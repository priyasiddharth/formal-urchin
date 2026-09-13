import obseq3.proof.copy

/-!
# The pointer-integer casts as read-then-store rvalues

`exposeAddr` (ptr-to-int) and `fromExposed` (int-to-ptr) compile exactly
like `copy` — lower the source place shared, put the result of ONE
instruction into a fresh register, store that register through the
destination — so they are instances of `ReadRhsFamily` (proof/copy.lean)
and reuse every leaf, seam and fragment lemma copy uses.

What differs is the rvalue's own step, and that is all this file proves:
the two read packages per cast, and the family record built from them.
`exposeAddr` reads the pointer cell through the place's tag, exposes the
STORED pointer's tag, and yields that pointer's concrete address as a
word. The exposure is what makes it more than a `Load`: it grows the
`exposed` list, which `PermSim` relates positionally, so the transport is
`sb_expose_respects_PermSim`, and in the projected-source shape it has to
slide past the projection's `Die` (`sb_die_exposed_inert`).
-/

namespace obseq3.proof

variable {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
variable {ρa : AddrRenameMap} {ρt : TagRenameMap}
variable {s_mir s_mir' : mirlite.State MSB Γ}
variable {s_osea : oseair.State MSB}

open obseq3
open obseq3.compile
open obseq3.oseair (Instr Register Rhs Val)

/-- The mirlite step of an `exposeAddr` assignment does not see the
    difference between a source place and its flattening. -/
theorem stepStmt_assign_exposesrc_anyflatten
    {Γ : Ctx} {σ : LayoutTy} {M : PermissionModel}
    (s : mirlite.State M Γ) (dst : Place Γ obseq.LayoutTy.NatL)
    (src : Place Γ (obseq.LayoutTy.PtrL σ)) :
    mirlite.stepStmt M s (.assign dst (.exposeAddr src))
      = mirlite.stepStmt M s (.assign dst (.exposeAddr (flattenPlace src))) := by
  have h1 : ∀ st : mirlite.State M Γ,
      mirlite.resolvePlaceAcc M st (flattenPlace src)
        = mirlite.resolvePlaceAcc M st src :=
    fun st => resolvePlaceAcc_flatten src
  simp only [mirlite.stepStmt, mirlite.doAssign, mirlite.evalRExpr, h1]

/-- **The `exposeAddr` read package**, chain-class source: lower the
    source place, transport the pointer-cell read, execute the
    `Rhs.ExposeAddr`, and transport the exposure. The value it leaves in
    the fresh register is the stored pointer's concrete address, which the
    word clause of `MemValSim` relates by plain equality. -/
theorem expose_readpkg_lowered {σ : LayoutTy} {src : Place Γ (obseq.LayoutTy.PtrL σ)}
    (compProg : oseair.Prog) (h_slower : LoweringSimAny compProg src) :
    ReadPkgLowered compProg (.exposeAddr src) src Rhs.ExposeAddr := by
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
      -- the READ: transport, then execute the cast
      obtain ⟨p2, h_read_tgt, h_psim2⟩ :=
        sb_read_respects_PermSim h_spsim h_wf_t h_srt h_read_src
      have h_code1 : compProg s_mid1.pc
          = some (Instr.Assgn (Register.R (CheckedCompilerM.run
              (placeToRegChecked RefKind.Shared src) csA).nextReg)
            (Rhs.ExposeAddr sOut.result.reg)) := by
        rw [h_spc]
        refine h_instD _ _ ?_ ?_
        · simp only [csCleanup, h_sclean, List.append_nil, emit,
            List.length_cons, List.length_nil]
          omega
        · simp only [csCleanup, h_sclean, List.append_nil]
          have h := emit_code_at_new
            { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA) with
              nextReg := (CheckedCompilerM.run
                (placeToRegChecked RefKind.Shared src) csA).nextReg + 1 }
            [Instr.Assgn (Register.R (CheckedCompilerM.run
                (placeToRegChecked RefKind.Shared src) csA).nextReg)
              (Rhs.ExposeAddr sOut.result.reg)]
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
      have h_run1 := runN_Assgn_ExposeAddr_step compProg s_mid1
        (Register.R (CheckedCompilerM.run
          (placeToRegChecked RefKind.Shared src) csA).nextReg)
        sOut.result.reg h_code1 h_sentry h_lt h_read2t h_cell_tgt
      -- the post-cast binding simulation: the temporary is above every
      -- mapped register, and the exposure does not touch the registers
      have h_ins : LocalBindingSim ρa ρt sM.env
          { s_mid1 with
            perms := MSB.expose p2 pt2,
            reg := oseair.RegMap.insert s_mid1.reg
              (Register.R (CheckedCompilerM.run
                (placeToRegChecked RefKind.Shared src) csA).nextReg)
              (obseq.TyVal.NatTy, [Val.Dat (pb2 + po2)]),
            pc := s_mid1.pc + 1 } csA :=
        LocalBindingSim.insert_fresh_reg h_slbs h_prb h_sregmono rfl
      refine ⟨h_sclean, n1 + 1, _, MSB.expose perms' pt, [Val.Dat (pb2 + po2)],
        rfl, rfl, oseair_runN_trans h_srun h_run1,
        (by simp only [emit]; exact h_sprm),
        (by simp only [emit]; exact Nat.le_trans h_sregmono (Nat.le_succ _)),
        ?_,
        sb_expose_respects_PermSim h_psim2 h_wf_t h_pt,
        ?_, h_smem,
        (by rw [h_spc]; simp only [emit, List.length_cons, List.length_nil]),
        RegMap.lookup_insert_self _ _ _,
        (by show _ < _; simp only [emit]; omega),
        ⟨rfl, trivial⟩⟩
      · intro τ' loc' binding' h_env'
        obtain ⟨reg', base', tag', h_pi', h_entry', h_ra2', h_rt', h_nw', h_dom'⟩ :=
          h_ins loc' binding' h_env'
        refine ⟨reg', base', tag', ?_, h_entry', h_ra2', h_rt', h_nw', h_dom'⟩
        show getPlaceInfo _ loc'.idx.1 = _
        simp only [getPlaceInfo, emit]
        rw [h_sprm]
        exact h_pi'
      · show TagRenameBounded ρt (MSB.expose perms' pt).NextTag
          (MSB.expose p2 pt2).NextTag
        rw [show (MSB.expose perms' pt).NextTag = perms'.NextTag from
              sb_expose_NextTag _ _,
          show (MSB.expose p2 pt2).NextTag = p2.NextTag from sb_expose_NextTag _ _,
          sb_read_NextTag h_read_src, sb_read_NextTag h_read_tgt, h_snt1]
        exact TagRenameBounded.mono h_tbd (Nat.le_refl _) h_snt2

/-- **The `exposeAddr` read package**, projected source at a nonzero
    offset: the projection's `Borrow(Shared)`, the cast through it, and the
    `Die` that retires it. BRIDGE 1S supplies the borrow/read/die
    cancellation; the exposure the cast performs between the read and the
    die slides past the die by `sb_die_exposed_inert`. -/
theorem expose_readpkg_projoffset {σ σs : LayoutTy} {B : Place Γ σs}
    {spath : PathTo σs (obseq.LayoutTy.PtrL σ)}
    (compProg : oseair.Prog) (h_slower : LoweringSimAny compProg B)
    (h_np : ∀ (σ' : LayoutTy) (b : Place Γ σ') (q : PathTo σ' σs),
      B = b.proj q → False)
    (h_o : pathOffset spath ≠ 0) :
    ReadPkgProjOffset compProg (.exposeAddr (.proj B spath)) B spath
      Rhs.ExposeAddr := by
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
      injection h_eval with h_out
      subst h_out
      refine ⟨placeInputsMapped_of_localBindingSim_resolvePlace h_lbs
          (resolvePlace?_of_resolveAcc
            (resolvePlaceAcc_proj_base_ok (path := spath) h_sres)), ?_⟩
      intro sOut0 h_sval0 sOutP h_regP h_clP h_instS h_instCS
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
            (Rhs.ExposeAddr (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)),
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
        · simp only [emit, List.length_cons, List.length_nil]
          omega
        · rw [emit_code_lt_nextLabel _ _ (by
            simp only [emit, List.length_cons, List.length_nil]; omega)]
          have h := emit_code_at_new
            { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1 }
            [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)
              (borrowRhs RefKind.Shared (blockSize (obseq.LayoutTy.PtrL σ))
                sOut.result.reg (pathOffset spath))]
            (k := 0) (by simp)
          simpa using h
      have h_code2 : compProg (s_mid1.pc + 1)
          = some (Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1))
              (Rhs.ExposeAddr (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg))) := by
        rw [h_spc]
        refine h_instCS2 _ _ ?_ ?_
        · simp only [emit, List.length_cons, List.length_nil]
          omega
        · have h := emit_code_at_new
            { (emit
        { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1 }
        [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)
          (borrowRhs RefKind.Shared (blockSize (obseq.LayoutTy.PtrL σ)) sOut.result.reg (pathOffset spath))]) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1 + 1 }
            [Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1))
                (Rhs.ExposeAddr (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)),
              Instr.Die (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)
                (blockSize (obseq.LayoutTy.PtrL σ))]
            (k := 0) (by simp)
          simpa [emit] using h
      have h_code3 : compProg (s_mid1.pc + 1 + 1)
          = some (Instr.Die (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)
              (blockSize (obseq.LayoutTy.PtrL σ))) := by
        rw [h_spc]
        refine h_instCS2 _ _ ?_ ?_
        · simp only [emit, List.length_cons, List.length_nil]
          omega
        · have h := emit_code_at_new
            { (emit
        { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1 }
        [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)
          (borrowRhs RefKind.Shared (blockSize (obseq.LayoutTy.PtrL σ)) sOut.result.reg (pathOffset spath))]) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1 + 1 }
            [Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1))
                (Rhs.ExposeAddr (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)),
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
      have h_run2 := runN_Assgn_ExposeAddr_step compProg
        { s_mid1 with perms := q1, reg := oseair.RegMap.insert s_mid1.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg) (obseq.TyVal.PTy, [Val.Ptr rs.allocBase (rs.addr - rs.allocBase + pathOffset spath) rs.allocSize s_mid1.perms.NextTag]), pc := s_mid1.pc + 1 }
        (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1)) (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)
        h_code2 h_bentry h_lt h_read2 h_cell_tgt
      have h_regbv : (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)
          ≠ (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1)) := by
        intro h_eq
        injection h_eq with h_eq'
        omega
      have h_bentry2 : oseair.RegMap.lookup
          (oseair.RegMap.insert (oseair.RegMap.insert s_mid1.reg
            (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)
            (obseq.TyVal.PTy, [Val.Ptr rs.allocBase
              (rs.addr - rs.allocBase + pathOffset spath)
              rs.allocSize s_mid1.perms.NextTag]))
            (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1))
            (obseq.TyVal.NatTy, [Val.Dat (pb2 + po2)]))
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
      have h_die_exp : MSB.die (MSB.expose q2 pt2)
          (rs.allocBase + (rs.addr - rs.allocBase + pathOffset spath))
          (blockSize (obseq.LayoutTy.PtrL σ)) s_mid1.perms.NextTag
          = .ok (MSB.expose q3 pt2) :=
        sb_die_expose_comm h_die1'
      have h_run3 := runN_Die_step compProg
        { s_mid1 with perms := MSB.expose q2 pt2, reg := oseair.RegMap.insert (oseair.RegMap.insert s_mid1.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg) (obseq.TyVal.PTy, [Val.Ptr rs.allocBase (rs.addr - rs.allocBase + pathOffset spath) rs.allocSize s_mid1.perms.NextTag])) (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1)) (obseq.TyVal.NatTy, [Val.Dat (pb2 + po2)]), pc := s_mid1.pc + 1 + 1 }
        (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg) (blockSize (obseq.LayoutTy.PtrL σ))
        h_code3 h_bentry2 h_die_exp
      have h_psim3 : PermSim ρt (MSB.expose perms' pt) (MSB.expose q3 pt2) :=
        sb_expose_respects_PermSim h_psim2q h_wf_t h_pt
      -- the post-`Die` binding simulation: both temporaries are fresh
      have h_lbsB : LocalBindingSim ρa ρt sM.env
          { s_mid1 with perms := q1, reg := oseair.RegMap.insert s_mid1.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg) (obseq.TyVal.PTy, [Val.Ptr rs.allocBase (rs.addr - rs.allocBase + pathOffset spath) rs.allocSize s_mid1.perms.NextTag]), pc := s_mid1.pc + 1 } csA :=
        LocalBindingSim.insert_fresh_reg h_slbs h_prb h_sregmono rfl
      have h_lbsV : LocalBindingSim ρa ρt sM.env
          { s_mid1 with perms := MSB.expose q3 pt2, reg := oseair.RegMap.insert (oseair.RegMap.insert s_mid1.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg) (obseq.TyVal.PTy, [Val.Ptr rs.allocBase (rs.addr - rs.allocBase + pathOffset spath) rs.allocSize s_mid1.perms.NextTag])) (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1)) (obseq.TyVal.NatTy, [Val.Dat (pb2 + po2)]), pc := s_mid1.pc + 1 + 1 + 1 } csA :=
        LocalBindingSim.insert_fresh_reg h_lbsB h_prb
          (Nat.le_trans h_sregmono (Nat.le_succ _)) rfl
      refine ⟨h_sclean, _, _, MSB.expose perms' pt, [Val.Dat (pb2 + po2)], rfl, rfl,
        oseair_runN_trans (oseair_runN_trans (oseair_runN_trans h_srun h_run1)
          h_run2) h_run3,
        (by simp only [emit]; exact h_sprm),
        (by simp only [emit]; omega), ?_, h_psim3, ?_, h_smem,
        (by rw [h_spc]; simp only [emit, List.length_cons, List.length_nil]),
        RegMap.lookup_insert_self _ _ _,
        (by show _ < _; simp only [emit]; omega),
        ⟨rfl, trivial⟩⟩
      · intro τ' loc' binding' h_env'
        obtain ⟨reg', base', tag', h_pi', h_entry', h_ra2', h_rt', h_nw', h_dom'⟩ :=
          h_lbsV loc' binding' h_env'
        refine ⟨reg', base', tag', ?_, h_entry', h_ra2', h_rt', h_nw', h_dom'⟩
        show getPlaceInfo _ loc'.idx.1 = _
        simp only [getPlaceInfo, emit]
        rw [h_sprm]
        exact h_pi'
      · show TagRenameBounded ρt (MSB.expose perms' pt).NextTag _
        rw [show (MSB.expose perms' pt).NextTag = perms'.NextTag from
          sb_expose_NextTag _ _, sb_read_NextTag h_read_src, h_snt1]
        rw [show ((MSB.expose q3 pt2).NextTag) = q3.NextTag from
          sb_expose_NextTag _ _]
        refine TagRenameBounded.mono h_tbd (Nat.le_refl _) ?_
        refine Nat.le_trans h_snt2 ?_
        rw [← sb_read_NextTag h_read_tgt]
        exact h_ntle

/-- `exposeAddr` is a read-then-store family: it lowers its source place
    shared and emits one `Rhs.ExposeAddr`, so every copy leaf, seam and
    fragment lemma serves it unchanged. -/
theorem exposeAddr_readRhsFamily {Γ : Ctx} {σ : LayoutTy} (compProg : oseair.Prog) :
    ReadRhsFamily (Γ := Γ) compProg
      (fun src : Place Γ (obseq.LayoutTy.PtrL σ) => RExpr.exposeAddr src)
      Rhs.ExposeAddr where
  shape := fun src => readRhsShape_exposeAddr src
  stepFlat := fun s dst src => stepStmt_assign_exposesrc_anyflatten s dst src
  pkgLowered := fun _ h => expose_readpkg_lowered compProg h
  pkgProjOffset := fun _ _ h h_np h_o => expose_readpkg_projoffset compProg h h_np h_o

/-- One `exposeAddr` statement, simulated. -/
theorem CompilerInv_step_exposeAddr
    {σ : LayoutTy}
    {dst : Place Γ obseq.LayoutTy.NatL} {src : Place Γ (obseq.LayoutTy.PtrL σ)}
    (compProg : oseair.Prog)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    (h_stmt : prog.get? s_mir.pc = some (.assign dst (.exposeAddr src)))
    (h_step : mirlite.stepStmt MSB s_mir (.assign dst (.exposeAddr src))
      = .ok s_mir') :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' :=
  CompilerInv_step_readrhs compProg (exposeAddr_readRhsFamily compProg) h_comp
    h_inv h_stmt h_step

end obseq3.proof
