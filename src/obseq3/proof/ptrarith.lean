import obseq3.proof.casts

/-!
# Pointer arithmetic as a read-then-store rvalue

`ptrOffset` compiles exactly like `copy` and the two integer-pointer
casts — lower the source place shared, put the result of ONE instruction
into a fresh register, store that register through the destination — so
it is an instance of `ReadRhsFamily` (proof/copy.lean) and reuses every
leaf, seam and fragment lemma they use. `readRhsShape_ptrOffset` holds by
`rfl`, which is the whole claim that it belongs to the family.

What differs is only the rvalue's own step:

* the delta is scaled to CELLS at compile time (`delta * blockSize σ`),
  so the machine instruction mentions no layout and the two sides' offset
  arithmetic is literally the same expression;
* the tag is PRESERVED — no mint, no expose — so the permission state
  after the step is the one the source read produced, on both machines;
* mirlite rejects a result below the allocation base, and the compiled
  `Rhs.PtrOffset` rejects the same thing, so the guard transports by
  matching `¬ (po + deltaCells < 0)` on the nose.

The source bounds guard mirlite carries (added 2026-09-14, the same one
the casts got) is what makes the read transportable: the compiled
instruction reads through the source register and errs OOB, so mirlite
must too.
-/

namespace obseq3.proof

variable {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
variable {ρa : AddrRenameMap} {ρt : TagRenameMap}
variable {s_mir s_mir' : mirlite.State MSB Γ}
variable {s_osea : oseair.State MSB}

open obseq3
open obseq3.compile
open obseq3.oseair (Instr Register Rhs Val)

/-- The mirlite step of a `ptrOffset` assignment does not see the
    difference between a source place and its flattening. -/
theorem stepStmt_assign_ptroffsetsrc_anyflatten
    {Γ : Ctx} {σ τ : LayoutTy} {M : PermissionModel}
    (s : mirlite.State M Γ) (dst : Place Γ (obseq.LayoutTy.PtrL τ))
    (src : Place Γ (obseq.LayoutTy.PtrL σ)) (delta : Int) :
    mirlite.stepStmt M s (.assign dst (.ptrOffset src delta))
      = mirlite.stepStmt M s (.assign dst (.ptrOffset (flattenPlace src) delta)) := by
  have h1 : ∀ st : mirlite.State M Γ,
      mirlite.resolvePlaceAcc M st (flattenPlace src)
        = mirlite.resolvePlaceAcc M st src :=
    fun st => resolvePlaceAcc_flatten src
  simp only [mirlite.stepStmt, mirlite.doAssign, mirlite.evalRExpr, h1]
/-- **The `ptrOffset` read package**, chain-class source: lower the
    source place, transport the pointer-cell read, execute the
    `Rhs.PtrOffset`. The value it leaves in the fresh register is the
    stored pointer shifted by the pre-scaled delta, with block, size and
    TAG untouched — so the pointer clause of `MemValSim` holds with the
    same witnesses the source cell's relation supplied. -/
theorem ptroffset_readpkg_lowered {σ τ : LayoutTy}
    {src : Place Γ (obseq.LayoutTy.PtrL σ)} (delta : Int)
    (compProg : oseair.Prog) (h_slower : LoweringSimAny compProg src) :
    ReadPkgLowered compProg (.ptrOffset (τ := τ) src delta) src
      (fun r => Rhs.PtrOffset r (delta * (blockSize σ : Int))) (fun _ => []) := by
  intro ρa ρt sM sA csA h_id_a h_wf_t h_tbd h_lbs h_prb h_sms h_alloc h_psim h_pc
    output h_eval
  simp only [mirlite.evalRExpr] at h_eval
  cases h_sres : mirlite.resolvePlaceAcc MSB sM src with
  | error e => rw [h_sres] at h_eval; simp at h_eval
  | ok pr =>
  obtain ⟨rs, permsS⟩ := pr
  rw [h_sres] at h_eval
  simp only at h_eval
  by_cases h_fit : rs.addr + 1 > rs.allocBase + rs.allocSize
  · rw [if_pos h_fit] at h_eval
    simp at h_eval
  · rw [if_neg h_fit] at h_eval
    cases h_read_src : MSB.read permsS rs.addr 1 rs.tag with
    | error e => rw [h_read_src] at h_eval; simp at h_eval
    | ok perms' =>
    rw [h_read_src] at h_eval
    simp only at h_eval
    cases h_cell : mirlite.Mem.find? sM.mem rs.addr with
    | none => rw [h_cell] at h_eval; simp at h_eval
    | some v =>
      cases v with
      | undef => rw [h_cell] at h_eval; simp at h_eval
      | word n => rw [h_cell] at h_eval; simp at h_eval
      | ptrVal pb po ps pt =>
      rw [h_cell] at h_eval
      simp only at h_eval
      by_cases h_neg : ((po : Int) + delta * (blockSize σ : Int)) < 0
      · rw [if_pos h_neg] at h_eval
        simp at h_eval
      · rw [if_neg h_neg] at h_eval
        injection h_eval with h_out
        subst h_out
        refine ⟨placeInputsMapped_of_localBindingSim_resolvePlace h_lbs
            (resolvePlace?_of_resolveAcc h_sres), ?_⟩
        intro sOut0 h_sval0 h_instS h_instD
        simp only [List.append_nil] at h_instD
        -- the source mother
        obtain ⟨sOut, n1, s_mid1, tres, h_sval, h_sclean, h_srun, h_spc, h_smem,
          h_spsim, h_snt1, h_snt2, h_slbs, h_sentry, h_srt, h_sle, h_srange,
          h_sbelow, h_sprm, h_sregmono, h_slabmono, -, -⟩ :=
          h_slower _ _ _ h_id_a h_wf_t RefKind.Shared csA sA
            rs permsS h_sres h_tbd h_lbs h_prb h_sms h_psim h_pc h_instS
        have h_sOut_eq : sOut = sOut0 := by
          rw [h_sval0] at h_sval
          exact (Except.ok.inj h_sval).symm
        subst h_sOut_eq
        have h_cancel := resolvedAddr_cancel h_sle
        -- the STORED pointer, on the target side
        obtain ⟨addr', value', h_ra', h_find_tgt, h_mvs⟩ := h_sms rs.addr _ h_cell
        have h_addr' : addr' = rs.addr := (h_id_a _ _ h_ra').symm
        subst h_addr'
        cases value' with
        | Undef => exact h_mvs.elim
        | Dat _ => exact h_mvs.elim
        | Ptr pb2 po2 ps2 pt2 =>
        obtain ⟨h_pb, h_po, h_ps, h_pt, h_prange⟩ := h_mvs
        have h_pb2 : pb2 = pb := (h_id_a _ _ h_pb).symm
        subst h_pb2
        subst h_po
        subst h_ps
        -- the READ: transport, then execute the offset
        obtain ⟨p2, h_read_tgt, h_psim2⟩ :=
          sb_read_respects_PermSim h_spsim h_wf_t h_srt h_read_src
        have h_code1 : compProg s_mid1.pc
            = some (Instr.Assgn (Register.R (CheckedCompilerM.run
                (placeToRegChecked RefKind.Shared src) csA).nextReg)
              (Rhs.PtrOffset sOut.result.reg (delta * (blockSize σ : Int)))) := by
          rw [h_spc]
          refine h_instD _ _ ?_ ?_
          · grind [emit]
          · simp only [csCleanup, h_sclean, List.append_nil]
            have h := emit_code_at_new
              { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA) with
                nextReg := (CheckedCompilerM.run
                  (placeToRegChecked RefKind.Shared src) csA).nextReg + 1 }
              [Instr.Assgn (Register.R (CheckedCompilerM.run
                  (placeToRegChecked RefKind.Shared src) csA).nextReg)
                (Rhs.PtrOffset sOut.result.reg (delta * (blockSize σ : Int)))]
              (k := 0) (by simp)
            simpa using h
        have h_lt : rs.addr - rs.allocBase < rs.allocSize := by
          have h1 : rs.addr + 1 ≤ rs.allocBase + rs.allocSize := Nat.not_lt.mp h_fit
          have h2 := h_sle
          grind
        have h_read2t : MSB.read s_mid1.perms
            (rs.allocBase + (rs.addr - rs.allocBase)) 1 tres = .ok p2 := by
          rw [h_cancel]
          exact h_read_tgt
        have h_cell_tgt : oseair.Mem.find? s_mid1.mem
            (rs.allocBase + (rs.addr - rs.allocBase))
            = some (Val.Ptr pb2 po2 ps2 pt2) := by
          rw [h_cancel, h_smem]
          exact h_find_tgt
        have h_run1 := runN_Assgn_PtrOffset_step compProg s_mid1
          (Register.R (CheckedCompilerM.run
            (placeToRegChecked RefKind.Shared src) csA).nextReg)
          sOut.result.reg (delta * (blockSize σ : Int))
          h_code1 h_sentry h_lt h_read2t h_cell_tgt h_neg
        -- the temporary is above every mapped register, and the offset
        -- touches nothing else
        have h_ins : LocalBindingSim ρa ρt sM.env
            { s_mid1 with
              perms := p2,
              reg := oseair.RegMap.insert s_mid1.reg
                (Register.R (CheckedCompilerM.run
                  (placeToRegChecked RefKind.Shared src) csA).nextReg)
                (obseq.TyVal.PTy,
                  [Val.Ptr pb2 ((po2 : Int) + delta * (blockSize σ : Int)).toNat ps2 pt2]),
              pc := s_mid1.pc + 1 } csA :=
          LocalBindingSim.insert_fresh_reg h_slbs h_prb h_sregmono rfl
        refine ⟨h_sclean, ρt, n1 + 1, _, perms',
          [Val.Ptr pb2 ((po2 : Int) + delta * (blockSize σ : Int)).toNat ps2 pt2],
          TagRenameIncr.refl ρt, h_wf_t,
          rfl, rfl, oseair_runN_trans h_srun h_run1,
          (by grind [emit]),
          (by grind [emit]),
          ?_,
          h_psim2,
          ?_, h_smem,
          (by rw [h_spc]; simp only [emit, List.append_nil, List.length_cons, List.length_nil]),
          RegMap.lookup_insert_self _ _ _,
          (by grind [emit]),
          ⟨⟨h_pb, rfl, rfl, h_pt, h_prange⟩, trivial⟩⟩
        · intro τ' loc' binding' h_env'
          obtain ⟨reg', base', tag', h_pi', h_entry', h_ra2', h_rt', h_nw', h_dom'⟩ :=
            h_ins loc' binding' h_env'
          refine ⟨reg', base', tag', ?_, h_entry', h_ra2', h_rt', h_nw', h_dom'⟩
          show getPlaceInfo _ loc'.idx.1 = _
          simp only [getPlaceInfo, emit]
          rw [h_sprm]
          exact h_pi'
        · show TagRenameBounded ρt perms'.NextTag p2.NextTag
          rw [sb_read_NextTag h_read_src, sb_read_NextTag h_read_tgt, h_snt1]
          exact TagRenameBounded.mono h_tbd (Nat.le_refl _) h_snt2

/-- **The `ptrOffset` read package**, projected source at a nonzero
    offset: the projection's `Borrow(Shared)`, the offset through it, and
    the `Die` that retires it. BRIDGE 1S supplies the borrow/read/die
    cancellation; unlike the two casts nothing touches the permissions
    between the read and the die, so the die applies unchanged. -/
theorem ptroffset_readpkg_projoffset {σ τ σs : LayoutTy} {B : Place Γ σs}
    {spath : PathTo σs (obseq.LayoutTy.PtrL σ)} (delta : Int)
    (compProg : oseair.Prog) (h_slower : LoweringSimAny compProg B) :
    ReadPkgProjOffset compProg (.ptrOffset (τ := τ) (.proj B spath) delta) B spath
      (fun r => Rhs.PtrOffset r (delta * (blockSize σ : Int))) (fun _ => []) := by
  intro ρa ρt sM sA csA h_id_a h_wf_t h_tbd h_lbs h_prb h_sms h_alloc h_psim h_pc
    output h_eval
  simp only [mirlite.evalRExpr] at h_eval
  cases h_sres : mirlite.resolvePlaceAcc MSB sM B with
  | error e =>
      rw [resolvePlaceAcc_proj_base_err h_sres] at h_eval
      simp at h_eval
  | ok pr =>
  obtain ⟨rs, permsS⟩ := pr
  rw [resolvePlaceAcc_proj_base_ok h_sres] at h_eval
  simp only [gt_iff_lt] at h_eval
  by_cases h_fit : rs.allocBase + rs.allocSize < rs.addr + PathTo.offset spath + 1
  · rw [if_pos h_fit] at h_eval
    simp at h_eval
  · rw [if_neg h_fit] at h_eval
    cases h_read_src : MSB.read permsS (rs.addr + PathTo.offset spath) 1 rs.tag with
    | error e => rw [h_read_src] at h_eval; simp at h_eval
    | ok perms' =>
    rw [h_read_src] at h_eval
    simp only at h_eval
    cases h_cell : mirlite.Mem.find? sM.mem (rs.addr + PathTo.offset spath) with
    | none => rw [h_cell] at h_eval; simp at h_eval
    | some v =>
      cases v with
      | undef => rw [h_cell] at h_eval; simp at h_eval
      | word n => rw [h_cell] at h_eval; simp at h_eval
      | ptrVal pb po ps pt =>
      rw [h_cell] at h_eval
      simp only at h_eval
      by_cases h_neg : ((po : Int) + delta * (blockSize σ : Int)) < 0
      · rw [if_pos h_neg] at h_eval
        simp at h_eval
      rw [if_neg h_neg] at h_eval
      injection h_eval with h_out
      subst h_out
      refine ⟨placeInputsMapped_of_localBindingSim_resolvePlace h_lbs
          (resolvePlace?_of_resolveAcc
            (resolvePlaceAcc_proj_base_ok (path := spath) h_sres)), ?_⟩
      intro sOut0 h_sval0 sOutP h_regP h_clP h_instS h_instCS
      simp only [List.append_nil] at h_instCS
      -- the source mother, on the chain BASE
      obtain ⟨sOut, n1, s_mid1, tres, h_sval, h_sclean, h_srun, h_spc, h_smem,
        h_spsim, h_snt1, h_snt2, h_slbs, h_sentry, h_srt, h_sle, h_srange,
        h_sbelow, h_sprm, h_sregmono, h_slabmono, -, -⟩ :=
        h_slower _ _ _ h_id_a h_wf_t RefKind.Shared csA sA
          rs permsS h_sres h_tbd h_lbs h_prb h_sms h_psim h_pc h_instS
      have h_cancelS := resolvedAddr_cancel h_sle
      have h_sOut_eq : sOut = sOut0 := by
        rw [h_sval0] at h_sval
        exact (Except.ok.inj h_sval).symm
      subst h_sOut_eq
      have h_bs : blockSize (obseq.LayoutTy.PtrL σ) = 1 := rfl
      -- code inclusion at the post-`Die` tower
      have h_instCS2 : CodeIncluded compProg (emit
        { (emit
        { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1 }
        [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)
          (borrowRhs RefKind.Shared (blockSize (obseq.LayoutTy.PtrL σ)) sOut.result.reg (pathOffset spath))]) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1 + 1 }
        [Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1))
            (Rhs.PtrOffset (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg) (delta * (blockSize σ : Int))),
          Instr.Die (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg) (blockSize (obseq.LayoutTy.PtrL σ))]) := by
        have h := h_instCS
        rw [h_regP, h_clP] at h
        simp only [csCleanup, h_sclean, List.nil_append, List.append_nil,
          List.reverse_cons, List.map_cons] at h
        csnorm at h ⊢
        exact h
      -- the STORED pointer, on the target side
      obtain ⟨addr', value', h_ra', h_find_tgt, h_mvs⟩ :=
        h_sms (rs.addr + PathTo.offset spath) _ h_cell
      have h_addr' : addr' = rs.addr + PathTo.offset spath := (h_id_a _ _ h_ra').symm
      subst h_addr'
      cases value' with
      | Undef => exact h_mvs.elim
      | Dat _ => exact h_mvs.elim
      | Ptr pb2 po2 ps2 pt2 =>
      obtain ⟨h_pb, h_po, h_ps, h_pt, h_prange⟩ := h_mvs
      have h_pb2 : pb2 = pb := (h_id_a _ _ h_pb).symm
      subst h_pb2
      subst h_po
      subst h_ps
      -- BRIDGE 1S: the borrow is taken, read through, and retired
      obtain ⟨p2, h_read_tgt, h_psim2⟩ :=
        sb_read_respects_PermSim h_spsim h_wf_t h_srt h_read_src
      have h_tbd2 : TagRenameBounded ρt permsS.NextTag s_mid1.perms.NextTag := by
        rw [h_snt1]
        exact TagRenameBounded.mono h_tbd (Nat.le_refl _) h_snt2
      obtain ⟨q1, q2, q3, h_ref_tgt, h_rd1, h_die1, h_psim2q, h_ntle⟩ :=
        bridge1S_of_read h_spsim h_wf_t h_tbd2 h_read_tgt h_psim2
      -- the three source instructions
      have h_code1 : compProg s_mid1.pc
          = some (Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)
              (borrowRhs RefKind.Shared (blockSize (obseq.LayoutTy.PtrL σ))
                sOut.result.reg (pathOffset spath))) := by
        rw [h_spc]
        refine h_instCS2 _ _ ?_ ?_
        · grind [emit]
        · rw [emit_code_lt_nextLabel _ _ (by
            grind [emit])]
          have h := emit_code_at_new
            { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1 }
            [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)
              (borrowRhs RefKind.Shared (blockSize (obseq.LayoutTy.PtrL σ))
                sOut.result.reg (pathOffset spath))]
            (k := 0) (by simp)
          simpa using h
      have h_code2 : compProg (s_mid1.pc + 1)
          = some (Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1))
              (Rhs.PtrOffset (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg) (delta * (blockSize σ : Int)))) := by
        rw [h_spc]
        refine h_instCS2 _ _ ?_ ?_
        · grind [emit]
        · have h := emit_code_at_new
            { (emit
        { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1 }
        [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)
          (borrowRhs RefKind.Shared (blockSize (obseq.LayoutTy.PtrL σ)) sOut.result.reg (pathOffset spath))]) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1 + 1 }
            [Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1))
                (Rhs.PtrOffset (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg) (delta * (blockSize σ : Int))),
              Instr.Die (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)
                (blockSize (obseq.LayoutTy.PtrL σ))]
            (k := 0) (by simp)
          simpa [emit] using h
      have h_code3 : compProg (s_mid1.pc + 1 + 1)
          = some (Instr.Die (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)
              (blockSize (obseq.LayoutTy.PtrL σ))) := by
        rw [h_spc]
        refine h_instCS2 _ _ ?_ ?_
        · grind [emit]
        · have h := emit_code_at_new
            { (emit
        { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1 }
        [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)
          (borrowRhs RefKind.Shared (blockSize (obseq.LayoutTy.PtrL σ)) sOut.result.reg (pathOffset spath))]) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1 + 1 }
            [Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1))
                (Rhs.PtrOffset (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg) (delta * (blockSize σ : Int))),
              Instr.Die (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)
                (blockSize (obseq.LayoutTy.PtrL σ))]
            (k := 1) (by simp)
          simpa [emit] using h
      -- execute Borrow, cast, Die
      have h_le1 : rs.allocBase + (rs.addr - rs.allocBase) + pathOffset spath
          + blockSize (obseq.LayoutTy.PtrL σ) ≤ rs.allocBase + rs.allocSize := by
        rw [h_cancelS, h_bs]
        have := Nat.not_lt.mp h_fit
        grind
      have h_ref_tgt' : MSB.ref s_mid1.perms
          (rs.allocBase + (rs.addr - rs.allocBase) + pathOffset spath)
          (blockSize (obseq.LayoutTy.PtrL σ)) tres RefKind.Shared false []
          = .ok (q1, s_mid1.perms.NextTag) := by
        rw [h_cancelS, h_bs]
        exact h_ref_tgt
      have h_run1 := runN_Assgn_Borrow_step compProg s_mid1
        (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg) sOut.result.reg RefKind.Shared false []
        (blockSize (obseq.LayoutTy.PtrL σ)) (pathOffset spath) h_code1 h_sentry
        h_le1 h_ref_tgt'
      have h_bentry : PtrRegisterEntry (oseair.RegMap.insert s_mid1.reg
          (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)
          (obseq.TyVal.PTy, [Val.Ptr rs.allocBase
            (rs.addr - rs.allocBase + pathOffset spath)
            rs.allocSize s_mid1.perms.NextTag]))
          (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg) rs.allocBase
          (rs.addr - rs.allocBase + pathOffset spath) rs.allocSize
          s_mid1.perms.NextTag :=
        RegMap.lookup_insert_self _ _ _
      have h_lt : rs.addr - rs.allocBase + pathOffset spath < rs.allocSize := by
        have h1 := Nat.not_lt.mp h_fit
        have h2 := h_sle
        grind
      have h_read2 : MSB.read q1
          (rs.allocBase + (rs.addr - rs.allocBase + pathOffset spath)) 1
          s_mid1.perms.NextTag = .ok q2 := by
        rw [← Nat.add_assoc, h_cancelS]
        exact h_rd1
      have h_cell_tgt : oseair.Mem.find? s_mid1.mem
          (rs.allocBase + (rs.addr - rs.allocBase + pathOffset spath))
          = some (Val.Ptr pb2 po2 ps2 pt2) := by
        rw [← Nat.add_assoc, h_cancelS, h_smem]
        exact h_find_tgt
      have h_run2 := runN_Assgn_PtrOffset_step compProg
        { s_mid1 with perms := q1, reg := oseair.RegMap.insert s_mid1.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg) (obseq.TyVal.PTy, [Val.Ptr rs.allocBase (rs.addr - rs.allocBase + pathOffset spath) rs.allocSize s_mid1.perms.NextTag]), pc := s_mid1.pc + 1 }
        (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1)) (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)
        (delta * (blockSize σ : Int))
        h_code2 h_bentry h_lt h_read2 h_cell_tgt h_neg
      have h_regbv : (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)
          ≠ (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1)) := by
        grind
      have h_bentry2 : oseair.RegMap.lookup
          (oseair.RegMap.insert (oseair.RegMap.insert s_mid1.reg
            (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)
            (obseq.TyVal.PTy, [Val.Ptr rs.allocBase
              (rs.addr - rs.allocBase + pathOffset spath)
              rs.allocSize s_mid1.perms.NextTag]))
            (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1))
            (obseq.TyVal.PTy, [Val.Ptr pb2 ((po2 : Int) + delta * (blockSize σ : Int)).toNat ps2 pt2]))
          (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)
          = some (obseq.TyVal.PTy, [Val.Ptr rs.allocBase
              (rs.addr - rs.allocBase + pathOffset spath)
              rs.allocSize s_mid1.perms.NextTag]) := by
        rw [RegMap.lookup_insert_ne _ h_regbv]
        exact h_bentry
      -- the exposure slides past the `Die`
      have h_die1' : MSB.die q2
          (rs.allocBase + (rs.addr - rs.allocBase + pathOffset spath))
          (blockSize (obseq.LayoutTy.PtrL σ)) s_mid1.perms.NextTag = .ok q3 := by
        rw [← Nat.add_assoc, h_cancelS, h_bs]
        exact h_die1
      have h_run3 := runN_Die_step compProg
        { s_mid1 with perms := q2, reg := oseair.RegMap.insert (oseair.RegMap.insert s_mid1.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg) (obseq.TyVal.PTy, [Val.Ptr rs.allocBase (rs.addr - rs.allocBase + pathOffset spath) rs.allocSize s_mid1.perms.NextTag])) (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1)) (obseq.TyVal.PTy, [Val.Ptr pb2 ((po2 : Int) + delta * (blockSize σ : Int)).toNat ps2 pt2]), pc := s_mid1.pc + 1 + 1 }
        (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg) (blockSize (obseq.LayoutTy.PtrL σ))
        h_code3 h_bentry2 h_die1'
      have h_psim3 : PermSim ρt perms' q3 := h_psim2q
      -- the post-`Die` binding simulation: both temporaries are fresh
      have h_lbsB : LocalBindingSim ρa ρt sM.env
          { s_mid1 with perms := q1, reg := oseair.RegMap.insert s_mid1.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg) (obseq.TyVal.PTy, [Val.Ptr rs.allocBase (rs.addr - rs.allocBase + pathOffset spath) rs.allocSize s_mid1.perms.NextTag]), pc := s_mid1.pc + 1 } csA :=
        LocalBindingSim.insert_fresh_reg h_slbs h_prb h_sregmono rfl
      have h_lbsV : LocalBindingSim ρa ρt sM.env
          { s_mid1 with perms := q3, reg := oseair.RegMap.insert (oseair.RegMap.insert s_mid1.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg) (obseq.TyVal.PTy, [Val.Ptr rs.allocBase (rs.addr - rs.allocBase + pathOffset spath) rs.allocSize s_mid1.perms.NextTag])) (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1)) (obseq.TyVal.PTy, [Val.Ptr pb2 ((po2 : Int) + delta * (blockSize σ : Int)).toNat ps2 pt2]), pc := s_mid1.pc + 1 + 1 + 1 } csA :=
        LocalBindingSim.insert_fresh_reg h_lbsB h_prb
          (Nat.le_trans h_sregmono (Nat.le_succ _)) rfl
      refine ⟨h_sclean, ρt, _, _, perms', [Val.Ptr pb2 ((po2 : Int) + delta * (blockSize σ : Int)).toNat ps2 pt2],
        TagRenameIncr.refl ρt, h_wf_t, rfl, rfl,
        oseair_runN_trans (oseair_runN_trans (oseair_runN_trans h_srun h_run1)
          h_run2) h_run3,
        (by grind [emit]),
        (by grind [emit]), ?_, h_psim3, ?_, h_smem,
        (by rw [h_spc]; simp only [emit, List.append_nil, List.length_cons, List.length_nil]),
        RegMap.lookup_insert_self _ _ _,
        (by grind [emit]),
        ⟨⟨h_pb, rfl, rfl, h_pt, h_prange⟩, trivial⟩⟩
      · intro τ' loc' binding' h_env'
        obtain ⟨reg', base', tag', h_pi', h_entry', h_ra2', h_rt', h_nw', h_dom'⟩ :=
          h_lbsV loc' binding' h_env'
        refine ⟨reg', base', tag', ?_, h_entry', h_ra2', h_rt', h_nw', h_dom'⟩
        show getPlaceInfo _ loc'.idx.1 = _
        simp only [getPlaceInfo, emit]
        rw [h_sprm]
        exact h_pi'
      · show TagRenameBounded ρt perms'.NextTag _
        rw [sb_read_NextTag h_read_src, h_snt1]
        refine TagRenameBounded.mono h_tbd (Nat.le_refl _) ?_
        refine Nat.le_trans h_snt2 ?_
        rw [← sb_read_NextTag h_read_tgt]
        exact h_ntle

/-- `ptrOffset` is a read-then-store family: it lowers its source place
    shared and emits one `Rhs.PtrOffset`, so every destination leaf, seam
    and fragment lemma serves it unchanged. The delta is fixed at the
    family, since it is part of the rvalue. -/
theorem ptrOffset_readRhsFamily {Γ : Ctx} {σ τ : LayoutTy} (delta : Int)
    (compProg : oseair.Prog) :
    ReadRhsFamily (Γ := Γ) compProg
      (fun src : Place Γ (obseq.LayoutTy.PtrL σ) =>
        RExpr.ptrOffset (τ := τ) src delta)
      (fun r => Rhs.PtrOffset r (delta * (blockSize σ : Int))) (fun _ => []) where
  shape := fun src => readRhsShape_ptrOffset src delta
  stepFlat := fun s dst src => stepStmt_assign_ptroffsetsrc_anyflatten s dst src delta
  pkgLowered := fun _ h => ptroffset_readpkg_lowered delta compProg h
  pkgProjOffset := fun _ _ h _ _ => ptroffset_readpkg_projoffset delta compProg h

/-- One `ptrOffset` statement, simulated. -/
theorem CompilerInv_step_ptrOffset
    {σ τ : LayoutTy}
    {dst : Place Γ (obseq.LayoutTy.PtrL τ)}
    {src : Place Γ (obseq.LayoutTy.PtrL σ)} {delta : Int}
    (compProg : oseair.Prog)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    (h_stmt : prog.get? s_mir.pc = some (.assign dst (.ptrOffset src delta)))
    (h_step : mirlite.stepStmt MSB s_mir (.assign dst (.ptrOffset src delta))
      = .ok s_mir') :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' :=
  CompilerInv_step_readrhs compProg (ptrOffset_readRhsFamily delta compProg) h_comp
    h_inv h_stmt h_step


/-! ## `ptrCast`: a one-cell copy at `PTy`

Since the cast lowers with a register temporary (compile.lean), its
compiled shape IS copy's at a pointer layout, so both read packages are
copy's with only the mirlite inversion changed — `blockSize (PtrL σ)` is
`1`, which is the literal the cast's own arm writes. -/

/-- **The `ptrCast` read package**, chain-class source. -/
theorem ptrcast_readpkg_lowered {σ τ : LayoutTy}
    {src : Place Γ (obseq.LayoutTy.PtrL σ)}
    (compProg : oseair.Prog) (h_slower : LoweringSimAny compProg src) :
    ReadPkgLowered compProg (.ptrCast (τ := τ) src) src
      (Rhs.Load (layoutToTyVal (obseq.LayoutTy.PtrL σ))) (fun _ => []) := by
  intro ρa ρt sM sA csA h_id_a h_wf_t h_tbd h_lbs h_prb h_sms h_alloc h_psim h_pc
    output h_eval
  simp only [mirlite.evalRExpr] at h_eval
  cases h_sres : mirlite.resolvePlaceAcc MSB sM src with
  | error e => rw [h_sres] at h_eval; simp at h_eval
  | ok pr =>
  obtain ⟨rs, permsS⟩ := pr
  rw [h_sres] at h_eval
  simp only at h_eval
  by_cases h_fit : rs.addr + 1 > rs.allocBase + rs.allocSize
  · rw [if_pos h_fit] at h_eval
    simp at h_eval
  · rw [if_neg h_fit] at h_eval
    cases h_read_src : MSB.read permsS rs.addr 1 rs.tag with
    | error e => rw [h_read_src] at h_eval; simp at h_eval
    | ok perms₂ =>
    rw [h_read_src] at h_eval
    injection h_eval with h_out
    subst h_out
    refine ⟨placeInputsMapped_of_localBindingSim_resolvePlace h_lbs
        (resolvePlace?_of_resolveAcc h_sres), ?_⟩
    intro sOut0 h_sval0 h_instS h_instD
    simp only [List.append_nil] at h_instD
    obtain ⟨h_sclean, n1, s_mid1, p2, h_runR, h_prmR, h_regmonoR, h_lbsR, h_psimR,
      h_tbdR, h_smem, h_spc, h_pcR, h_vbelow, h_rel⟩ :=
      copy_chainsrc_read compProg h_slower sM sA csA h_id_a h_wf_t h_tbd h_lbs h_prb
        h_sms h_psim h_pc h_sres h_fit h_read_src h_sval0 h_instS h_instD
    exact ⟨h_sclean, ρt, n1 + 1, _, perms₂, _, TagRenameIncr.refl ρt, h_wf_t, rfl,
      (by rw [oseair_readWordSeq_length]; rfl),
      h_runR, h_prmR, h_regmonoR, h_lbsR, h_psimR, h_tbdR, h_smem, h_pcR,
      RegMap.lookup_insert_self _ _ _, h_vbelow, h_rel⟩


/-- **The `ptrCast` read package**, projected source at a nonzero offset:
    the projection's `Borrow(Shared)`, the `Load` through it, and the
    `Die`. Copy's `copy_projsrc_offset_read` does all of it. -/
theorem ptrcast_readpkg_projoffset {σ τ σs : LayoutTy} {B : Place Γ σs}
    {spath : PathTo σs (obseq.LayoutTy.PtrL σ)}
    (compProg : oseair.Prog) (h_slower : LoweringSimAny compProg B) :
    ReadPkgProjOffset compProg (.ptrCast (τ := τ) (.proj B spath)) B spath
      (Rhs.Load (layoutToTyVal (obseq.LayoutTy.PtrL σ))) (fun _ => []) := by
  intro ρa ρt sM sA csA h_id_a h_wf_t h_tbd h_lbs h_prb h_sms h_alloc h_psim h_pc
    output h_eval
  simp only [mirlite.evalRExpr] at h_eval
  cases h_sres : mirlite.resolvePlaceAcc MSB sM B with
  | error e =>
      rw [resolvePlaceAcc_proj_base_err h_sres] at h_eval
      simp at h_eval
  | ok pr =>
  obtain ⟨rs, permsS⟩ := pr
  rw [resolvePlaceAcc_proj_base_ok h_sres] at h_eval
  simp only [gt_iff_lt] at h_eval
  by_cases h_fit : rs.allocBase + rs.allocSize < rs.addr + PathTo.offset spath + 1
  · rw [if_pos h_fit] at h_eval
    simp at h_eval
  · rw [if_neg h_fit] at h_eval
    cases h_read_src : MSB.read permsS (rs.addr + PathTo.offset spath) 1 rs.tag with
    | error e => rw [h_read_src] at h_eval; simp at h_eval
    | ok perms₂ =>
    rw [h_read_src] at h_eval
    injection h_eval with h_out
    subst h_out
    refine ⟨placeInputsMapped_of_localBindingSim_resolvePlace h_lbs
        (resolvePlace?_of_resolveAcc
          (resolvePlaceAcc_proj_base_ok (path := spath) h_sres)), ?_⟩
    intro sOut0 h_sval0 sOutP h_regP h_clP h_instS h_instCS
    simp only [List.append_nil] at h_instCS
    obtain ⟨h_sclean, n1, s_mid1, q3, h_runR, h_prmR, h_regmonoR, h_lbsR, h_psimR,
      h_tbdR, h_smem, h_spc, h_pcR, h_vbelow, h_rel⟩ :=
      copy_projsrc_offset_read compProg h_slower sM sA csA h_id_a h_wf_t h_tbd
        h_lbs h_prb h_sms h_psim h_pc h_sres h_fit h_read_src h_sval0 h_regP h_clP
        h_instS h_instCS
    exact ⟨h_sclean, ρt, n1, _, perms₂, _, TagRenameIncr.refl ρt, h_wf_t, rfl,
      (by rw [oseair_readWordSeq_length]; rfl),
      h_runR, h_prmR, h_regmonoR, h_lbsR, h_psimR, h_tbdR, h_smem, h_pcR,
      RegMap.lookup_insert_self _ _ _, h_vbelow, h_rel⟩

/-- The mirlite step of a `ptrCast` assignment does not see the difference
    between a source place and its flattening. -/
theorem stepStmt_assign_ptrcastsrc_anyflatten
    {Γ : Ctx} {σ τ : LayoutTy} {M : PermissionModel}
    (s : mirlite.State M Γ) (dst : Place Γ (obseq.LayoutTy.PtrL τ))
    (src : Place Γ (obseq.LayoutTy.PtrL σ)) :
    mirlite.stepStmt M s (.assign dst (.ptrCast src))
      = mirlite.stepStmt M s (.assign dst (.ptrCast (flattenPlace src))) := by
  have h1 : ∀ st : mirlite.State M Γ,
      mirlite.resolvePlaceAcc M st (flattenPlace src)
        = mirlite.resolvePlaceAcc M st src :=
    fun st => resolvePlaceAcc_flatten src
  simp only [mirlite.stepStmt, mirlite.doAssign, mirlite.evalRExpr, h1]

/-- `ptrCast` is a read-then-store family. -/
theorem ptrCast_readRhsFamily {Γ : Ctx} {σ τ : LayoutTy} (compProg : oseair.Prog) :
    ReadRhsFamily (Γ := Γ) compProg
      (fun src : Place Γ (obseq.LayoutTy.PtrL σ) => RExpr.ptrCast (τ := τ) src)
      (Rhs.Load (layoutToTyVal (obseq.LayoutTy.PtrL σ))) (fun _ => []) where
  shape := fun src => readRhsShape_ptrCast src
  stepFlat := fun s dst src => stepStmt_assign_ptrcastsrc_anyflatten s dst src
  pkgLowered := fun _ h => ptrcast_readpkg_lowered compProg h
  pkgProjOffset := fun _ _ h _ _ => ptrcast_readpkg_projoffset compProg h

/-- One `ptrCast` statement, simulated. -/
theorem CompilerInv_step_ptrCast
    {σ τ : LayoutTy}
    {dst : Place Γ (obseq.LayoutTy.PtrL τ)}
    {src : Place Γ (obseq.LayoutTy.PtrL σ)}
    (compProg : oseair.Prog)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    (h_stmt : prog.get? s_mir.pc = some (.assign dst (.ptrCast src)))
    (h_step : mirlite.stepStmt MSB s_mir (.assign dst (.ptrCast src))
      = .ok s_mir') :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' :=
  CompilerInv_step_readrhs compProg (ptrCast_readRhsFamily compProg) h_comp
    h_inv h_stmt h_step



/-! ## `refSlice`: the one read-then-store rvalue that MINTS

A slice retag reads the fat-pointer cell and then takes a fresh tag over
the REST of its allocation (`size - offset`), which is why the read
packages let the renaming grow.

It is also the one member with a non-empty `post`. `Rhs.BorrowRest` used
to do both halves in a single instruction, which forced a projected
source's `Borrow(Shared)` to stay live across the mint — and a `Mut`
retag whose range covers the fat pointer's own cell then popped it with
its write access, while a `Shared` or `Raw false` retag buried it. Either
way the cleanup `Die` no longer found its tag on top, and mirlite, which
has no projection borrow at all, ran clean: a real divergence, pinned by
`rs_mut_slice_retag_pops_projection_borrow`.

The lowering now splits (2026-09-16): `Load` the fat pointer through the
temporary, `Die` it while it is still on top, then mint with a
register-to-register `Rhs.RetagRest`. The read half is literally copy's,
so BRIDGE 1S collapses the bracket exactly as it does for `ptrCast`, and
the mint is a separate step that no borrow outlives. -/

/-- **The `refSlice` read package**, chain-class source. -/
theorem refslice_readpkg_lowered {σ τ : LayoutTy}
    {src : Place Γ (obseq.LayoutTy.PtrL σ)} (kind : RefKind) (prot : Bool)
    (compProg : oseair.Prog) (h_slower : LoweringSimAny compProg src) :
    ReadPkgLowered compProg (.refSlice (τ := τ) kind prot src) src
      (Rhs.Load (layoutToTyVal (obseq.LayoutTy.PtrL σ)))
      (fun tmp => [Instr.Assgn tmp (Rhs.RetagRest kind prot tmp)]) := by
  intro ρa ρt sM sA csA h_id_a h_wf_t h_tbd h_lbs h_prb h_sms h_alloc h_psim h_pc
    output h_eval
  simp only [mirlite.evalRExpr] at h_eval
  cases h_sres : mirlite.resolvePlaceAcc MSB sM src with
  | error e => rw [h_sres] at h_eval; simp at h_eval
  | ok pr =>
  obtain ⟨rs, permsS⟩ := pr
  rw [h_sres] at h_eval
  simp only at h_eval
  by_cases h_fit : rs.addr + 1 > rs.allocBase + rs.allocSize
  · rw [if_pos h_fit] at h_eval
    simp at h_eval
  · rw [if_neg h_fit] at h_eval
    cases h_read_src : MSB.read permsS rs.addr 1 rs.tag with
    | error e => rw [h_read_src] at h_eval; simp at h_eval
    | ok perms' =>
    rw [h_read_src] at h_eval
    simp only at h_eval
    cases h_cell : mirlite.Mem.find? sM.mem rs.addr with
    | none => rw [h_cell] at h_eval; simp at h_eval
    | some v =>
      cases v with
      | undef => rw [h_cell] at h_eval; simp at h_eval
      | word n => rw [h_cell] at h_eval; simp at h_eval
      | ptrVal pb po ps pt =>
      rw [h_cell] at h_eval
      simp only at h_eval
      cases h_ref_src : MSB.ref perms' (pb + po) (ps - po) pt kind prot [] with
      | error e => rw [h_ref_src] at h_eval; simp at h_eval
      | ok pr2 =>
        obtain ⟨perms'', newTag⟩ := pr2
        rw [h_ref_src] at h_eval
        injection h_eval with h_out
        subst h_out
        refine ⟨placeInputsMapped_of_localBindingSim_resolvePlace h_lbs
            (resolvePlace?_of_resolveAcc h_sres), ?_⟩
        intro sOut0 h_sval0 h_instS h_instD
        -- the source mother
        obtain ⟨sOut, n1, s_mid1, tres, h_sval, h_sclean, h_srun, h_spc, h_smem,
          h_spsim, h_snt1, h_snt2, h_slbs, h_sentry, h_srt, h_sle, h_srange,
          h_sbelow, h_sprm, h_sregmono, h_slabmono, -, -⟩ :=
          h_slower _ _ _ h_id_a h_wf_t RefKind.Shared csA sA
            rs permsS h_sres h_tbd h_lbs h_prb h_sms h_psim h_pc h_instS
        have h_sOut_eq : sOut = sOut0 := by
          rw [h_sval0] at h_sval
          exact (Except.ok.inj h_sval).symm
        subst h_sOut_eq
        have h_cancel := resolvedAddr_cancel h_sle
        -- the STORED pointer, on the target side
        obtain ⟨addr', value', h_ra', h_find_tgt, h_mvs⟩ := h_sms rs.addr _ h_cell
        have h_addr' : addr' = rs.addr := (h_id_a _ _ h_ra').symm
        subst h_addr'
        cases value' with
        | Undef => exact h_mvs.elim
        | Dat _ => exact h_mvs.elim
        | Ptr pb2 po2 ps2 pt2 =>
        obtain ⟨h_pb, h_po, h_ps, h_pt, h_prange⟩ := h_mvs
        have h_pb2 : pb2 = pb := (h_id_a _ _ h_pb).symm
        subst h_pb2
        subst h_po
        subst h_ps
        -- the READ transports, and BOTH emitted instructions are in the
        -- program: the `Load` at the fragment's first label, the mint at
        -- the second
        obtain ⟨p2, h_read_tgt, h_psim2⟩ :=
          sb_read_respects_PermSim h_spsim h_wf_t h_srt h_read_src
        have h_emit2 : ∀ (k : Nat) (instr : Instr), k < 2 →
            ([Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg) (Rhs.Load (layoutToTyVal (obseq.LayoutTy.PtrL σ)) sOut.result.reg),
              Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg) (Rhs.RetagRest kind prot (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg))]).get? k = some instr →
            compProg ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextLabel + k) = some instr := by
          intro k instr hk hget
          refine h_instD _ _ ?_ ?_
          · grind [emit]
          · simp only [csCleanup, h_sclean, List.nil_append, List.append_nil,
              List.cons_append]
            rw [emit_code_at_new _ _ (k := k) (by simpa using hk)]
            exact hget
        have h_code1 : compProg s_mid1.pc
            = some (Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg) (Rhs.Load (layoutToTyVal (obseq.LayoutTy.PtrL σ)) sOut.result.reg)) := by
          rw [h_spc]; exact h_emit2 0 _ (by omega) rfl
        have h_code2 : compProg (s_mid1.pc + 1)
            = some (Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg) (Rhs.RetagRest kind prot (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg))) := by
          rw [h_spc]; exact h_emit2 1 _ (by omega) rfl
        have h_lt : rs.addr - rs.allocBase < rs.allocSize := by
          have h1 : rs.addr + 1 ≤ rs.allocBase + rs.allocSize := Nat.not_lt.mp h_fit
          have h2 := h_sle
          grind
        have h_lt1 : (rs.addr - rs.allocBase) + obseq.typeSize (layoutToTyVal (obseq.LayoutTy.PtrL σ)) ≤ rs.allocSize := by
          show (rs.addr - rs.allocBase) + 1 ≤ rs.allocSize
          exact h_lt
        have h_read2t : MSB.read s_mid1.perms
            (rs.allocBase + (rs.addr - rs.allocBase)) (obseq.typeSize (layoutToTyVal (obseq.LayoutTy.PtrL σ))) tres
            = .ok p2 := by
          show MSB.read s_mid1.perms (rs.allocBase + (rs.addr - rs.allocBase)) 1 tres = _
          rw [h_cancel]
          exact h_read_tgt
        have h_cell_tgt : oseair.Mem.find? s_mid1.mem
            (rs.allocBase + (rs.addr - rs.allocBase))
            = some (Val.Ptr pb2 po2 ps2 pt2) := by
          rw [h_cancel, h_smem]
          exact h_find_tgt
        have h_seq : oseair.readWordSeq s_mid1.mem
            (rs.allocBase + (rs.addr - rs.allocBase)) (obseq.typeSize (layoutToTyVal (obseq.LayoutTy.PtrL σ)))
            = [Val.Ptr pb2 po2 ps2 pt2] := by
          show oseair.readWordSeq s_mid1.mem _ 1 = _
          simp [oseair.readWordSeq, h_cell_tgt]
        -- STEP 1: the Load, through the projection's temporary
        have h_run1 : oseair.runN MSB 1 s_mid1 compProg = oseair.Result.Ok
            { s_mid1 with
              perms := p2,
              reg := oseair.RegMap.insert s_mid1.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg)
                ((layoutToTyVal (obseq.LayoutTy.PtrL σ)), [Val.Ptr pb2 po2 ps2 pt2]),
              pc := s_mid1.pc + 1 } := by
          have h := runN_Assgn_Load_ptr_step compProg s_mid1 (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg)
            sOut.result.reg (layoutToTyVal (obseq.LayoutTy.PtrL σ)) h_code1 h_sentry h_lt1 h_read2t
          rwa [h_seq] at h
        -- the mint transports and EXTENDS the renaming
        have h_tbd_mid : TagRenameBounded ρt perms'.NextTag p2.NextTag := by
          rw [sb_read_NextTag h_read_src, sb_read_NextTag h_read_tgt, h_snt1]
          exact TagRenameBounded.mono h_tbd (Nat.le_refl _) h_snt2
        obtain ⟨q, h_ref_tgt, h_fresh_eq, h_incr_t, h_wf_t', h_tbd', h_psim'⟩ :=
          sb_ref_respects_PermSim h_psim2 h_wf_t h_tbd_mid h_pt h_ref_src
        subst h_fresh_eq
        -- STEP 2: the mint, register to register, the bracket already closed
        have h_run2 : oseair.runN MSB 1
            { s_mid1 with
              perms := p2,
              reg := oseair.RegMap.insert s_mid1.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg)
                ((layoutToTyVal (obseq.LayoutTy.PtrL σ)), [Val.Ptr pb2 po2 ps2 pt2]),
              pc := s_mid1.pc + 1 } compProg = oseair.Result.Ok
            { s_mid1 with
              perms := q,
              reg := oseair.RegMap.insert (oseair.RegMap.insert s_mid1.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg)
                  ((layoutToTyVal (obseq.LayoutTy.PtrL σ)), [Val.Ptr pb2 po2 ps2 pt2])) (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg)
                (obseq.TyVal.PTy, [Val.Ptr pb2 po2 ps2 p2.NextTag]),
              pc := s_mid1.pc + 1 + 1 } :=
          runN_Assgn_RetagRest_step compProg _ (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg) (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg) kind prot
            h_code2 (RegMap.lookup_insert_self _ _ _) h_ref_tgt
        -- the temporary is above every mapped register, twice over
        have h_ins : LocalBindingSim ρa ρt sM.env
            { s_mid1 with
              perms := q,
              reg := oseair.RegMap.insert (oseair.RegMap.insert s_mid1.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg)
                  ((layoutToTyVal (obseq.LayoutTy.PtrL σ)), [Val.Ptr pb2 po2 ps2 pt2])) (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg)
                (obseq.TyVal.PTy, [Val.Ptr pb2 po2 ps2 p2.NextTag]),
              pc := s_mid1.pc + 1 + 1 } csA :=
          LocalBindingSim.insert_fresh_reg
            (s := { s_mid1 with
              perms := p2,
              reg := oseair.RegMap.insert s_mid1.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg)
                ((layoutToTyVal (obseq.LayoutTy.PtrL σ)), [Val.Ptr pb2 po2 ps2 pt2]),
              pc := s_mid1.pc + 1 })
            (LocalBindingSim.insert_fresh_reg h_slbs h_prb h_sregmono rfl)
            h_prb h_sregmono rfl
        refine ⟨h_sclean, ρt.extend perms'.NextTag p2.NextTag, n1 + 1 + 1, _, perms'',
          [Val.Ptr pb2 po2 ps2 p2.NextTag],
          h_incr_t, h_wf_t',
          rfl, rfl, oseair_runN_trans (oseair_runN_trans h_srun h_run1) h_run2,
          (by grind [emit]),
          (by grind [emit]),
          ?_,
          h_psim',
          h_tbd', h_smem,
          (by rw [h_spc]; simp only [emit, List.length_append, List.length_cons,
            List.length_nil]),
          RegMap.lookup_insert_self _ _ _,
          (by grind [emit]),
          ⟨⟨h_pb, rfl, rfl, TagRenameMap.extend_self _ _ _, h_prange⟩, trivial⟩⟩
        · intro τ' loc' binding' h_env'
          obtain ⟨reg', base', tag', h_pi', h_entry', h_ra2', h_rt', h_nw', h_dom'⟩ :=
            (LocalBindingSim.rename_mono (AddrRenameIncr.refl ρa) h_incr_t h_ins)
              loc' binding' h_env'
          refine ⟨reg', base', tag', ?_, h_entry', h_ra2', h_rt', h_nw', h_dom'⟩
          show getPlaceInfo _ loc'.idx.1 = _
          simp only [getPlaceInfo, emit]
          rw [h_sprm]
          exact h_pi'

end obseq3.proof
