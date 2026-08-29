import obseq3.proof.common
import obseq3.proof.permsim_transport
import obseq3.proof.spine

namespace obseq3.proof

open obseq3
open obseq3.compile
open obseq3.oseair (Instr Register Rhs Val)

/-- The fragment of `dst := copy src` when BOTH places are mapped locals:
    a single `Memcpy`. The src lowering is a bare register read (no
    `Borrow`, no cleanup), so this leaf needs neither BRIDGE 1 nor any
    fresh register. -/
theorem compileStmt_copy_local_local_run
    {Γ : Ctx} {τ : LayoutTy}
    {dstLoc srcLoc : Local Γ τ}
    {cs : CompilerState} {dstReg srcReg : Register}
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = some (dstReg, τ))
    (h_src : getPlaceInfo cs srcLoc.idx.1 = some (srcReg, τ)) :
    CheckedCompilerM.run
        (compileStmtChecked
          (Stmt.assign (.local dstLoc) (.copy (.local srcLoc)))) cs
      = emit cs [Instr.Memcpy dstReg srcReg (obseq.layoutToTyVal τ)] := by
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_existing h_dst
  obtain ⟨h_prun, placeOut, h_pval, h_pres⟩ :=
    placeToRegChecked_local_existing (kind := RefKind.Shared) h_src
  simp [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked,
    h_run, h_val, h_prun, h_pval, h_pres]
  simp [CompilerM.run, CompilerM.value, emitM, cleanupInstrs, emit_nil]

/-- The copy statement lowers in this regime. -/
theorem compileStmt_copy_local_local_value
    {Γ : Ctx} {τ : LayoutTy}
    {dstLoc srcLoc : Local Γ τ}
    {cs : CompilerState} {dstReg srcReg : Register}
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = some (dstReg, τ))
    (h_src : getPlaceInfo cs srcLoc.idx.1 = some (srcReg, τ)) :
    ∃ so, CheckedCompilerM.value
      (compileStmtChecked
        (Stmt.assign (.local dstLoc) (.copy (.local srcLoc)))) cs
      = Except.ok so := by
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_existing h_dst
  obtain ⟨h_prun, placeOut, h_pval, h_pres⟩ :=
    placeToRegChecked_local_existing (kind := RefKind.Shared) h_src
  simp only [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
    h_run, h_pval]
  exact ⟨_, rfl⟩

/-- REGIME L→L, CLOSED 2026-08-28: `dst := copy src`, both bound locals.
    One `Memcpy`; its read/useMut pair is EXACTLY the source's two
    events (`M.read` of the src range in `evalRExpr .copy`, `useMut` of
    the dst range in `writeResolvedPlace`), transported by BRIDGE 3's
    read and write members. The copied VALUES are related pointwise by
    `readWordSeq_sim` — found source cells through `SourceMemSim`,
    source holes as undef-refines-anything — and `SourceMemSim` is
    re-established by BRIDGE 2's cell-by-cell write lemma. No tag is
    minted on either side and no register is written: both renames grow
    by `refl`. -/
theorem copy_local_local_simulation
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {τ : LayoutTy}
    {dstLoc srcLoc : Local Γ τ}
    {bD bS : mirlite.Binding}
    (compProg : oseair.Prog)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    (h_stmt : prog.get? s_mir.pc
      = some (.assign (.local dstLoc) (.copy (.local srcLoc))))
    (h_envD : mirlite.Env.lookup s_mir.env dstLoc = some bD)
    (h_envS : mirlite.Env.lookup s_mir.env srcLoc = some bS)
    (h_step : mirlite.stepStmt MSB s_mir
      (.assign (.local dstLoc) (.copy (.local srcLoc))) = .ok s_mir') :
    ∃ (s_osea' : oseair.State MSB) (n : Nat),
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa ρt s_mir' s_osea' := by
  obtain ⟨csPrefix, ⟨h_csAt, h_pc⟩, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_tbd,
    h_alloc, h_unmap, h_prb⟩ := h_inv
  obtain ⟨dstReg, baseD, tagD, h_piD, h_entryD, h_raD, h_rtD, h_nwD, h_domD⟩ :=
    h_lbs dstLoc bD h_envD
  obtain ⟨srcReg, baseS, tagS, h_piS, h_entryS, h_raS, h_rtS, h_nwS, h_domS⟩ :=
    h_lbs srcLoc bS h_envS
  have h_baseD : baseD = bD.addr := (h_id_a _ _ h_raD).symm
  subst h_baseD
  have h_baseS : baseS = bS.addr := (h_id_a _ _ h_raS).symm
  subst h_baseS
  -- §1 invert the source: read the src range, then write the dst range
  simp only [mirlite.stepStmt, mirlite.doAssign, mirlite.doAssignCont, mirlite.preparePlaceAssign,
    mirlite.resolvePlace?, h_envD, mirlite.resolvePlaceAcc, h_envS,
    mirlite.evalRExpr] at h_step
  rw [if_neg (Nat.lt_irrefl (bS.addr + blockSize τ))] at h_step
  cases h_read_src : MSB.read s_mir.perms bS.addr (blockSize τ) bS.tag with
  | error e => rw [h_read_src] at h_step; simp at h_step
  | ok perms' =>
    rw [h_read_src] at h_step
    simp only [h_envD] at h_step
    -- the overlapping-assignment check (post-rhs, Rust order): source
    -- success supplies the DISJOINTNESS the Memcpy check needs
    by_cases h_ov : bS.addr < bD.addr + blockSize τ ∧
        bD.addr < bS.addr + blockSize τ
    case pos => rw [if_pos h_ov] at h_step; simp at h_step
    rw [if_neg h_ov] at h_step
    -- §2 both events transported (BRIDGE 3 read + write members)
    obtain ⟨p2, h_read_tgt, h_psim2⟩ :=
      sb_read_respects_PermSim h_psim h_wf_t h_rtS h_nwS h_read_src
    have h_w := h_step
    simp only [mirlite.writeResolvedPlace] at h_w
    split at h_w
    · simp at h_w
    · rename_i h_nb
      split at h_w
      · rename_i perms'' h_useMut_src
        cases h_w
        have h_useMut_src' : MSB.useMut perms' bD.addr (blockSize τ) bD.tag
            = .ok perms'' := by
          grind
        obtain ⟨p3, h_useMut_tgt, h_psim3⟩ :=
          sb_write_respects_PermSim h_psim2 h_wf_t h_rtD h_nwD h_useMut_src'
        -- §3 the fragment and the Memcpy step
        have h_stmtRun := compileStmt_copy_local_local_run (cs := csPrefix)
          h_piD h_piS
        obtain ⟨stmtOut, h_stmtOut⟩ :=
          compileStmt_copy_local_local_value (cs := csPrefix) h_piD h_piS
        have h_code1 : compProg s_osea.pc
            = some (Instr.Memcpy dstReg srcReg (obseq.layoutToTyVal τ)) := by
          rw [h_pc]
          refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
          · rw [h_stmtRun]
            simp only [emit, List.length_cons, List.length_nil]
            omega
          · rw [h_stmtRun]
            have h := emit_code_at_new csPrefix
              [Instr.Memcpy dstReg srcReg (obseq.layoutToTyVal τ)] (k := 0) (by simp)
            simpa using h
        have h_ts : obseq.typeSize (obseq.layoutToTyVal τ) = blockSize τ := by
          simp [blockSize]
        have h_read_tgt' : MSB.read s_osea.perms (bS.addr + 0)
            (obseq.typeSize (obseq.layoutToTyVal τ)) tagS = .ok p2 := by
          rw [h_ts, Nat.add_zero]
          exact h_read_tgt
        have h_useMut_tgt' : MSB.useMut p2 (bD.addr + 0)
            (obseq.typeSize (obseq.layoutToTyVal τ)) tagD = .ok p3 := by
          rw [h_ts, Nat.add_zero]
          exact h_useMut_tgt
        have h_run1 := runN_Memcpy_step compProg s_osea dstReg srcReg
          (obseq.layoutToTyVal τ)
          h_code1 h_entryD h_entryS
          (by rw [h_ts, Nat.add_zero]; exact Nat.le_refl _)
          (by rw [h_ts, Nat.add_zero]; exact Nat.le_refl _)
          (by rw [h_ts]; simp only [Nat.add_zero]; grind)
          h_read_tgt' h_useMut_tgt'
        rw [h_ts] at h_run1
        simp only [Nat.add_zero] at h_run1
        -- §4 the copied values are pointwise related; memory sim rebuilt
        have h_rel : ListRel (MemValSim ρa ρt)
            (mirlite.readWordSeq s_mir.mem bS.addr (blockSize τ))
            (oseair.readWordSeq s_osea.mem bS.addr (blockSize τ)) :=
          readWordSeq_sim h_id_a h_sms (blockSize τ) bS.addr
        have h_dom : ∀ k,
            k < (mirlite.readWordSeq s_mir.mem bS.addr (blockSize τ)).length →
            ρa (bD.addr + k) = some (bD.addr + k) := by
          intro k hk
          obtain ⟨a', ha'⟩ := h_domD k (by simpa using hk)
          grind [IdentityOnDomain]
        have h_sms' : SourceMemSim ρa ρt
            (mirlite.writeWordSeq s_mir.mem bD.addr
              (mirlite.readWordSeq s_mir.mem bS.addr (blockSize τ)))
            (oseair.writeWordSeq s_osea.mem bD.addr
              (oseair.readWordSeq s_osea.mem bS.addr (blockSize τ))) :=
          SourceMemSim.writeWordSeq_extend h_id_a _ _ _ _ _ h_rel h_dom h_sms
        -- §5 rebuild the invariant (no rename growth, no register writes)
        refine ⟨_, 1, h_run1, ?_⟩
        refine ⟨CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.local dstLoc) (.copy (.local srcLoc)))) csPrefix,
          ⟨prefixCompileState_succ h_csAt h_stmt h_stmtOut, ?_⟩, ?_, h_sms', h_psim3,
          h_id_a, h_wf_t, ?_, ?_, ?_, ?_⟩
        · show s_osea.pc + 1 = _
          rw [h_pc, h_stmtRun]
          simp [emit]
        · intro τ' loc' binding' h_env'
          obtain ⟨reg', base', tag', h_pi', h_entry', h_ra', h_rt', h_nw', h_dom'⟩ :=
            h_lbs loc' binding' h_env'
          refine ⟨reg', base', tag', ?_, h_entry', h_ra', h_rt', h_nw', h_dom'⟩
          rw [h_stmtRun, getPlaceInfo_emit]
          exact h_pi'
        · show TagRenameBounded ρt perms''.NextTag p3.NextTag
          rw [sb_write_NextTag h_useMut_src', sb_read_NextTag h_read_src,
            sb_write_NextTag h_useMut_tgt, sb_read_NextTag h_read_tgt]
          exact h_tbd
        · simp only [AllocLockstep, mirlite_writeWordSeq_addrStart,
            oseair_writeWordSeq_addrStart]
          exact h_alloc
        · intro τ' loc' h_none
          rw [h_stmtRun, getPlaceInfo_emit]
          exact h_unmap loc' h_none
        · intro idx reg'' τ'' h_look
          rw [h_stmtRun] at h_look ⊢
          rw [getPlaceInfo_emit] at h_look
          refine RegisterBelow.mono ?_ (h_prb _ _ _ h_look)
          simp only [emit]
          exact Nat.le_refl _
      · simp at h_w

/-- The fragment of `dst := copy src.f` at ZERO offset, both roots
    mapped locals: still a single `Memcpy` — `placeToRegChecked` returns
    the base's own register for a zero-offset projection, so no Borrow
    is minted and no cleanup interleaves with the copy. -/
theorem compileStmt_copy_proj_zero_run
    {Γ : Ctx} {τ σb : LayoutTy}
    {dstLoc : Local Γ τ} {srcLoc : Local Γ σb}
    {f : PathTo σb τ}
    {cs : CompilerState} {dstReg srcReg : Register}
    (h_off : pathOffset f = 0)
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = some (dstReg, τ))
    (h_src : getPlaceInfo cs srcLoc.idx.1 = some (srcReg, σb)) :
    CheckedCompilerM.run
        (compileStmtChecked
          (Stmt.assign (.local dstLoc)
            (.copy (.proj (.local srcLoc) f)))) cs
      = emit cs [Instr.Memcpy dstReg srcReg (obseq.layoutToTyVal τ)] := by
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_existing h_dst
  obtain ⟨h_prun, placeOut, h_pval, h_pres⟩ :=
    placeToRegChecked_local_existing (kind := RefKind.Shared) h_src
  have h_proj_eq := placeToRegChecked_proj_root_eq (Γ := Γ)
    (kind := RefKind.Shared) (base := .local srcLoc) f
    (fun _ _ _ h => by cases h)
  simp only [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked, h_proj_eq,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
    h_run, h_val, h_prun, h_pval, h_off, dif_pos]
  simp [CompilerM.run, CompilerM.value, emitM, cleanupInstrs, h_pres, emit_nil]

/-- The zero-offset proj-src copy lowers. -/
theorem compileStmt_copy_proj_zero_value
    {Γ : Ctx} {τ σb : LayoutTy}
    {dstLoc : Local Γ τ} {srcLoc : Local Γ σb}
    {f : PathTo σb τ}
    {cs : CompilerState} {dstReg srcReg : Register}
    (h_off : pathOffset f = 0)
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = some (dstReg, τ))
    (h_src : getPlaceInfo cs srcLoc.idx.1 = some (srcReg, σb)) :
    ∃ so, CheckedCompilerM.value
      (compileStmtChecked
        (Stmt.assign (.local dstLoc)
          (.copy (.proj (.local srcLoc) f)))) cs
      = Except.ok so := by
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_existing h_dst
  obtain ⟨h_prun, placeOut, h_pval, h_pres⟩ :=
    placeToRegChecked_local_existing (kind := RefKind.Shared) h_src
  have h_proj_eq := placeToRegChecked_proj_root_eq (Γ := Γ)
    (kind := RefKind.Shared) (base := .local srcLoc) f
    (fun _ _ _ h => by cases h)
  simp only [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked, h_proj_eq,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
    h_run, h_prun, h_pval, h_off, dif_pos]
  exact ⟨_, rfl⟩

/-- REGIME P0→L, CLOSED 2026-08-28: `dst := copy src.f` at ZERO offset,
    both roots bound locals — regime L→L with a wider source allocation:
    the `Memcpy`'s source bounds check is discharged by TYPING
    (`PathTo.offset_add_size_le`: the field fits its layout), exactly as
    C0 widened regime A. The NONZERO-offset shape is NOT here: its
    fragment is `[Borrow(Shared); Memcpy; Die]`, and the `Memcpy`'s dst
    `useMut` sits BETWEEN the keystone's read and die — see the residual
    for the overlap countermodel. -/
theorem copy_proj_zero_simulation
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {τ σb : LayoutTy}
    {dstLoc : Local Γ τ} {srcLoc : Local Γ σb}
    {f : PathTo σb τ}
    {bD bS : mirlite.Binding}
    (compProg : oseair.Prog)
    (h_off : pathOffset f = 0)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    (h_stmt : prog.get? s_mir.pc
      = some (.assign (.local dstLoc) (.copy (.proj (.local srcLoc) f))))
    (h_envD : mirlite.Env.lookup s_mir.env dstLoc = some bD)
    (h_envS : mirlite.Env.lookup s_mir.env srcLoc = some bS)
    (h_step : mirlite.stepStmt MSB s_mir
      (.assign (.local dstLoc) (.copy (.proj (.local srcLoc) f))) = .ok s_mir') :
    ∃ (s_osea' : oseair.State MSB) (n : Nat),
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa ρt s_mir' s_osea' := by
  obtain ⟨csPrefix, ⟨h_csAt, h_pc⟩, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_tbd,
    h_alloc, h_unmap, h_prb⟩ := h_inv
  obtain ⟨dstReg, baseD, tagD, h_piD, h_entryD, h_raD, h_rtD, h_nwD, h_domD⟩ :=
    h_lbs dstLoc bD h_envD
  obtain ⟨srcReg, baseS, tagS, h_piS, h_entryS, h_raS, h_rtS, h_nwS, h_domS⟩ :=
    h_lbs srcLoc bS h_envS
  have h_baseD : baseD = bD.addr := (h_id_a _ _ h_raD).symm
  subst h_baseD
  have h_baseS : baseS = bS.addr := (h_id_a _ _ h_raS).symm
  subst h_baseS
  -- §1 invert the source: read the FIELD range, then write the dst range
  simp only [mirlite.stepStmt, mirlite.doAssign, mirlite.doAssignCont, mirlite.preparePlaceAssign,
    mirlite.resolvePlace?, h_envD, mirlite.resolvePlaceAcc, h_envS,
    mirlite.evalRExpr, h_off] at h_step
  rw [if_neg (Nat.not_lt.mpr (show bS.addr + 0 + blockSize τ
      ≤ bS.addr + blockSize σb by
    have h_fit := PathTo.offset_add_size_le f
    show bS.addr + 0 + layoutSize τ ≤ bS.addr + layoutSize σb
    have h_fit' : f.offset + layoutSize τ ≤ layoutSize σb := h_fit
    grind))] at h_step
  cases h_read_src : MSB.read s_mir.perms (bS.addr + 0) (blockSize τ) bS.tag with
  | error e => rw [h_read_src] at h_step; simp at h_step
  | ok perms' =>
    rw [h_read_src] at h_step
    simp only [h_envD] at h_step
    by_cases h_ov : bS.addr + 0 < bD.addr + blockSize τ ∧
        bD.addr < bS.addr + 0 + blockSize τ
    case pos => rw [if_pos h_ov] at h_step; simp at h_step
    rw [if_neg h_ov] at h_step
    -- §2 both events transported (BRIDGE 3 read + write members)
    obtain ⟨p2, h_read_tgt, h_psim2⟩ :=
      sb_read_respects_PermSim h_psim h_wf_t h_rtS h_nwS h_read_src
    have h_w := h_step
    simp only [mirlite.writeResolvedPlace] at h_w
    split at h_w
    · simp at h_w
    · rename_i h_nb
      split at h_w
      · rename_i perms'' h_useMut_src
        cases h_w
        have h_useMut_src' : MSB.useMut perms' bD.addr (blockSize τ) bD.tag
            = .ok perms'' := by
          grind
        obtain ⟨p3, h_useMut_tgt, h_psim3⟩ :=
          sb_write_respects_PermSim h_psim2 h_wf_t h_rtD h_nwD h_useMut_src'
        -- §3 the fragment and the Memcpy step
        have h_stmtRun := compileStmt_copy_proj_zero_run (cs := csPrefix)
          h_off h_piD h_piS
        obtain ⟨stmtOut, h_stmtOut⟩ :=
          compileStmt_copy_proj_zero_value (cs := csPrefix) h_off h_piD h_piS
        have h_code1 : compProg s_osea.pc
            = some (Instr.Memcpy dstReg srcReg (obseq.layoutToTyVal τ)) := by
          rw [h_pc]
          refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
          · rw [h_stmtRun]
            simp only [emit, List.length_cons, List.length_nil]
            omega
          · rw [h_stmtRun]
            have h := emit_code_at_new csPrefix
              [Instr.Memcpy dstReg srcReg (obseq.layoutToTyVal τ)] (k := 0) (by simp)
            simpa using h
        have h_ts : obseq.typeSize (obseq.layoutToTyVal τ) = blockSize τ := by
          simp [blockSize]
        have h_fit : blockSize τ ≤ blockSize σb := by
          have h := PathTo.offset_add_size_le f
          show layoutSize τ ≤ layoutSize σb
          grind
        have h_read_tgt' : MSB.read s_osea.perms (bS.addr + 0)
            (obseq.typeSize (obseq.layoutToTyVal τ)) tagS = .ok p2 := by
          rw [h_ts]
          exact h_read_tgt
        have h_useMut_tgt' : MSB.useMut p2 (bD.addr + 0)
            (obseq.typeSize (obseq.layoutToTyVal τ)) tagD = .ok p3 := by
          rw [h_ts, Nat.add_zero]
          exact h_useMut_tgt
        have h_run1 := runN_Memcpy_step compProg s_osea dstReg srcReg
          (obseq.layoutToTyVal τ)
          h_code1 h_entryD h_entryS
          (by rw [h_ts, Nat.add_zero]; exact Nat.le_refl _)
          (by rw [h_ts]; simpa using Nat.add_le_add_left h_fit bS.addr)
          (by rw [h_ts]; simp only [Nat.add_zero]; grind)
          h_read_tgt' h_useMut_tgt'
        rw [h_ts] at h_run1
        simp only [Nat.add_zero] at h_run1
        -- §4 the copied values are pointwise related; memory sim rebuilt
        have h_rel : ListRel (MemValSim ρa ρt)
            (mirlite.readWordSeq s_mir.mem bS.addr (blockSize τ))
            (oseair.readWordSeq s_osea.mem bS.addr (blockSize τ)) :=
          readWordSeq_sim h_id_a h_sms (blockSize τ) bS.addr
        have h_dom : ∀ k,
            k < (mirlite.readWordSeq s_mir.mem bS.addr (blockSize τ)).length →
            ρa (bD.addr + k) = some (bD.addr + k) := by
          intro k hk
          obtain ⟨a', ha'⟩ := h_domD k (by simpa using hk)
          grind [IdentityOnDomain]
        have h_sms' : SourceMemSim ρa ρt
            (mirlite.writeWordSeq s_mir.mem bD.addr
              (mirlite.readWordSeq s_mir.mem bS.addr (blockSize τ)))
            (oseair.writeWordSeq s_osea.mem bD.addr
              (oseair.readWordSeq s_osea.mem bS.addr (blockSize τ))) :=
          SourceMemSim.writeWordSeq_extend h_id_a _ _ _ _ _ h_rel h_dom h_sms
        -- §5 rebuild the invariant (no rename growth, no register writes)
        refine ⟨_, 1, h_run1, ?_⟩
        refine ⟨CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.local dstLoc)
              (.copy (.proj (.local srcLoc) f)))) csPrefix,
          ⟨prefixCompileState_succ h_csAt h_stmt h_stmtOut, ?_⟩, ?_, h_sms', h_psim3,
          h_id_a, h_wf_t, ?_, ?_, ?_, ?_⟩
        · show s_osea.pc + 1 = _
          rw [h_pc, h_stmtRun]
          simp [emit]
        · intro τ' loc' binding' h_env'
          obtain ⟨reg', base', tag', h_pi', h_entry', h_ra', h_rt', h_nw', h_dom'⟩ :=
            h_lbs loc' binding' h_env'
          refine ⟨reg', base', tag', ?_, h_entry', h_ra', h_rt', h_nw', h_dom'⟩
          rw [h_stmtRun, getPlaceInfo_emit]
          exact h_pi'
        · show TagRenameBounded ρt perms''.NextTag p3.NextTag
          rw [sb_write_NextTag h_useMut_src', sb_read_NextTag h_read_src,
            sb_write_NextTag h_useMut_tgt, sb_read_NextTag h_read_tgt]
          exact h_tbd
        · simp only [AllocLockstep, mirlite_writeWordSeq_addrStart,
            oseair_writeWordSeq_addrStart]
          exact h_alloc
        · intro τ' loc' h_none
          rw [h_stmtRun, getPlaceInfo_emit]
          exact h_unmap loc' h_none
        · intro idx reg'' τ'' h_look
          rw [h_stmtRun] at h_look ⊢
          rw [getPlaceInfo_emit] at h_look
          refine RegisterBelow.mono ?_ (h_prb _ _ _ h_look)
          simp only [emit]
          exact Nat.le_refl _
      · simp at h_w

/-- The fragment of `dst := copy src.f` at NONZERO offset, both roots
    mapped locals: `[Borrow(Shared); Memcpy; Die]` — the GEP borrow of
    the field, the copy through it, and its cleanup. -/
theorem compileStmt_copy_proj_offset_run
    {Γ : Ctx} {τ σb : LayoutTy}
    {dstLoc : Local Γ τ} {srcLoc : Local Γ σb}
    {f : PathTo σb τ}
    {cs : CompilerState} {dstReg srcReg : Register}
    (h_off : pathOffset f ≠ 0)
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = some (dstReg, τ))
    (h_src : getPlaceInfo cs srcLoc.idx.1 = some (srcReg, σb)) :
    CheckedCompilerM.run
        (compileStmtChecked
          (Stmt.assign (.local dstLoc)
            (.copy (.proj (.local srcLoc) f)))) cs
      = emit (emit (emit { cs with nextReg := cs.nextReg + 1 }
          [Instr.Assgn (Register.R cs.nextReg)
            (Rhs.Borrow RefKind.Shared false [] (blockSize τ) srcReg (pathOffset f))])
          [Instr.Memcpy dstReg (Register.R cs.nextReg) (obseq.layoutToTyVal τ)])
          [Instr.Die (Register.R cs.nextReg) (blockSize τ)] := by
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_existing h_dst
  obtain ⟨h_prun, placeOut, h_pval, h_pres⟩ :=
    placeToRegChecked_local_existing (kind := RefKind.Shared) h_src
  have h_proj_eq := placeToRegChecked_proj_root_eq (Γ := Γ)
    (kind := RefKind.Shared) (base := .local srcLoc) f
    (fun _ _ _ h => by cases h)
  simp only [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked,
    h_proj_eq,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
    h_run, h_val, h_prun, h_pval, h_off, dif_neg]
  simp [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM,
    cleanupInstrs, h_pres, emit_nil, borrowRhs]

/-- The nonzero-offset proj-src copy lowers. -/
theorem compileStmt_copy_proj_offset_value
    {Γ : Ctx} {τ σb : LayoutTy}
    {dstLoc : Local Γ τ} {srcLoc : Local Γ σb}
    {f : PathTo σb τ}
    {cs : CompilerState} {dstReg srcReg : Register}
    (h_off : pathOffset f ≠ 0)
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = some (dstReg, τ))
    (h_src : getPlaceInfo cs srcLoc.idx.1 = some (srcReg, σb)) :
    ∃ so, CheckedCompilerM.value
      (compileStmtChecked
        (Stmt.assign (.local dstLoc)
          (.copy (.proj (.local srcLoc) f)))) cs
      = Except.ok so := by
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_existing h_dst
  obtain ⟨h_prun, placeOut, h_pval, h_pres⟩ :=
    placeToRegChecked_local_existing (kind := RefKind.Shared) h_src
  have h_proj_eq := placeToRegChecked_proj_root_eq (Γ := Γ)
    (kind := RefKind.Shared) (base := .local srcLoc) f
    (fun _ _ _ h => by cases h)
  simp only [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked,
    h_proj_eq,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
    h_run, h_prun, h_pval, h_off, dif_neg]
  simp [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM,
    cleanupInstrs, emit_nil]

/-- REGIME P→L (nonzero offset), CLOSED 2026-08-28: `dst := copy src.f`
    with a real field offset, both roots bound locals. The fragment
    `[Borrow(Shared); Memcpy; Die]` interleaves the dst `useMut` (inside
    the atomic `Memcpy`) between BRIDGE 1S's phases; the proof composes
    - the overlap guard: source success supplies src/dst DISJOINTNESS,
    - BRIDGE 1S (`sb_ref_read_die_cancels`): ref;read;die ≡ parent read,
    - `sb_write_congr` + `sb_die_sb_write_comm`: the dst write slides
      between the keystone's phases by cell disjointness, up to `find?`
      (which is all the find?-quotient `PermSim` asks). -/
theorem copy_proj_offset_simulation
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {τ σb : LayoutTy}
    {dstLoc : Local Γ τ} {srcLoc : Local Γ σb}
    {f : PathTo σb τ}
    {bD bS : mirlite.Binding}
    (compProg : oseair.Prog)
    (h_off : pathOffset f ≠ 0)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    (h_stmt : prog.get? s_mir.pc
      = some (.assign (.local dstLoc) (.copy (.proj (.local srcLoc) f))))
    (h_envD : mirlite.Env.lookup s_mir.env dstLoc = some bD)
    (h_envS : mirlite.Env.lookup s_mir.env srcLoc = some bS)
    (h_step : mirlite.stepStmt MSB s_mir
      (.assign (.local dstLoc) (.copy (.proj (.local srcLoc) f))) = .ok s_mir') :
    ∃ (s_osea' : oseair.State MSB) (n : Nat),
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa ρt s_mir' s_osea' := by
  obtain ⟨csPrefix, ⟨h_csAt, h_pc⟩, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_tbd,
    h_alloc, h_unmap, h_prb⟩ := h_inv
  obtain ⟨dstReg, baseD, tagD, h_piD, h_entryD, h_raD, h_rtD, h_nwD, h_domD⟩ :=
    h_lbs dstLoc bD h_envD
  obtain ⟨srcReg, baseS, tagS, h_piS, h_entryS, h_raS, h_rtS, h_nwS, h_domS⟩ :=
    h_lbs srcLoc bS h_envS
  have h_baseD : baseD = bD.addr := (h_id_a _ _ h_raD).symm
  subst h_baseD
  have h_baseS : baseS = bS.addr := (h_id_a _ _ h_raS).symm
  subst h_baseS
  -- §1 invert the source: the overlap guard, then read + write
  simp only [mirlite.stepStmt, mirlite.doAssign, mirlite.doAssignCont,
    mirlite.preparePlaceAssign,
    mirlite.resolvePlace?, h_envD, mirlite.resolvePlaceAcc, h_envS,
    mirlite.evalRExpr] at h_step
  rw [if_neg (Nat.not_lt.mpr (show bS.addr + pathOffset f + blockSize τ
      ≤ bS.addr + blockSize σb by
    have h_fit := PathTo.offset_add_size_le f
    show bS.addr + pathOffset f + layoutSize τ ≤ bS.addr + layoutSize σb
    have h_fit' : f.offset + layoutSize τ ≤ layoutSize σb := h_fit
    grind))] at h_step
  cases h_read_src : MSB.read s_mir.perms (bS.addr + pathOffset f)
      (blockSize τ) bS.tag with
  | error e => rw [h_read_src] at h_step; simp at h_step
  | ok perms' =>
    rw [h_read_src] at h_step
    simp only [h_envD] at h_step
    by_cases h_ov : bS.addr + pathOffset f < bD.addr + blockSize τ ∧
        bD.addr < bS.addr + pathOffset f + blockSize τ
    case pos => rw [if_pos h_ov] at h_step; simp at h_step
    rw [if_neg h_ov] at h_step
    -- §2 the parent read + dst write transport (BRIDGE 3)
    obtain ⟨p2, h_read_tgt, h_psim2⟩ :=
      sb_read_respects_PermSim h_psim h_wf_t h_rtS h_nwS h_read_src
    have h_w := h_step
    simp only [mirlite.writeResolvedPlace] at h_w
    split at h_w
    · simp at h_w
    · rename_i h_nb
      split at h_w
      · rename_i perms'' h_useMut_src
        cases h_w
        have h_useMut_src' : MSB.useMut perms' bD.addr (blockSize τ) bD.tag
            = .ok perms'' := by
          grind
        obtain ⟨p3, h_useMut_tgt, h_psim3⟩ :=
          sb_write_respects_PermSim h_psim2 h_wf_t h_rtD h_nwD h_useMut_src'
        -- §3 BRIDGE 1S: the target's GEP borrow, its read, and its die
        obtain ⟨q1, h_ref_tgt⟩ := sb_ref_Shared_ok_of_sb_read_ok h_read_tgt
        have h_unprot := freshTag_not_protected h_psim h_tbd
        have h0 : wildcardTag < s_osea.perms.NextTag := (h_tbd _ _ h_wf_t.2).2
        have h_ntw : (s_osea.perms.NextTag == wildcardTag) = false := by grind
        obtain ⟨q2, q3, qAcc', h_rd1, h_die1, h_rd2, h_sm, h_exq, h_pfq, h_ntle⟩ :=
          sb_ref_read_die_cancels h_ntw h_unprot h_ref_tgt
        have h_qAcc : qAcc' = p2 := by
          grind
        subst h_qAcc
        -- §4 slide the dst write between the keystone's phases
        obtain ⟨p3q, h_wq3, h_p3q_sm, h_p3q_pf, h_p3q_ex, h_p3q_nt⟩ :=
          sb_write_congr h_sm h_pfq h_exq h_useMut_tgt
        have h_dis : ∀ j k, j < blockSize τ → k < blockSize τ →
            bS.addr + pathOffset f + j ≠ bD.addr + k := by
          intro j k hj hk h_eq
          refine h_ov ⟨?_, ?_⟩
          · calc bS.addr + pathOffset f
                ≤ bS.addr + pathOffset f + j := Nat.le_add_right _ _
              _ = bD.addr + k := h_eq
              _ < bD.addr + blockSize τ := Nat.add_lt_add_left hk _
          · calc bD.addr
                ≤ bD.addr + k := Nat.le_add_right _ _
              _ = bS.addr + pathOffset f + j := h_eq.symm
              _ < bS.addr + pathOffset f + blockSize τ := Nat.add_lt_add_left hj _
        obtain ⟨w, r', h_wq2, h_dwr, h_find_eq, h_r'_pf, h_r'_ex, h_r'_nt⟩ :=
          sb_die_sb_write_comm h_dis h_die1 h_wq3
        -- §5 the fragment and its three instructions
        have h_stmtRun := compileStmt_copy_proj_offset_run (cs := csPrefix)
          h_off h_piD h_piS
        obtain ⟨stmtOut, h_stmtOut⟩ :=
          compileStmt_copy_proj_offset_value (cs := csPrefix) h_off h_piD h_piS
        have h_len3 : ((emit (emit (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
            [Instr.Assgn (Register.R csPrefix.nextReg)
              (Rhs.Borrow RefKind.Shared false [] (blockSize τ) srcReg (pathOffset f))])
            [Instr.Memcpy dstReg (Register.R csPrefix.nextReg) (obseq.layoutToTyVal τ)])
            [Instr.Die (Register.R csPrefix.nextReg) (blockSize τ)])).nextLabel
            = csPrefix.nextLabel + 3 := by
          simp only [emit, List.length_cons, List.length_nil]
        have h_code1 : compProg s_osea.pc
            = some (Instr.Assgn (Register.R csPrefix.nextReg)
                (Rhs.Borrow RefKind.Shared false [] (blockSize τ) srcReg (pathOffset f))) := by
          rw [h_pc]
          refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
          · rw [h_stmtRun, h_len3]; omega
          · rw [h_stmtRun]
            rw [emit_code_lt_nextLabel _ _ (by
              simp only [emit, List.length_cons, List.length_nil]; omega)]
            rw [emit_code_lt_nextLabel _ _ (by
              simp only [emit, List.length_cons, List.length_nil]; omega)]
            have h := emit_code_at_new { csPrefix with nextReg := csPrefix.nextReg + 1 }
              [Instr.Assgn (Register.R csPrefix.nextReg)
                (Rhs.Borrow RefKind.Shared false [] (blockSize τ) srcReg (pathOffset f))]
              (k := 0) (by simp)
            simpa using h
        have h_code2 : compProg (s_osea.pc + 1)
            = some (Instr.Memcpy dstReg (Register.R csPrefix.nextReg)
                (obseq.layoutToTyVal τ)) := by
          rw [h_pc]
          refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
          · rw [h_stmtRun, h_len3]; omega
          · rw [h_stmtRun]
            rw [emit_code_lt_nextLabel _ _ (by
              simp only [emit, List.length_cons, List.length_nil]; omega)]
            have h := emit_code_at_new
              (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                [Instr.Assgn (Register.R csPrefix.nextReg)
                  (Rhs.Borrow RefKind.Shared false [] (blockSize τ) srcReg (pathOffset f))])
              [Instr.Memcpy dstReg (Register.R csPrefix.nextReg) (obseq.layoutToTyVal τ)]
              (k := 0) (by simp)
            simpa [emit] using h
        have h_code3 : compProg (s_osea.pc + 1 + 1)
            = some (Instr.Die (Register.R csPrefix.nextReg) (blockSize τ)) := by
          rw [h_pc]
          refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
          · rw [h_stmtRun, h_len3]; omega
          · rw [h_stmtRun]
            have h := emit_code_at_new
              (emit (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                [Instr.Assgn (Register.R csPrefix.nextReg)
                  (Rhs.Borrow RefKind.Shared false [] (blockSize τ) srcReg (pathOffset f))])
                [Instr.Memcpy dstReg (Register.R csPrefix.nextReg) (obseq.layoutToTyVal τ)])
              [Instr.Die (Register.R csPrefix.nextReg) (blockSize τ)]
              (k := 0) (by simp)
            simpa [emit] using h
        -- §6 execute: Borrow, Memcpy (read via fresh; the slid dst write), Die
        have h_fit : pathOffset f + blockSize τ ≤ blockSize σb :=
          PathTo.offset_add_size_le f
        have h_fit' : f.offset + layoutSize τ ≤ layoutSize σb := h_fit
        have h_ts : obseq.typeSize (obseq.layoutToTyVal τ) = blockSize τ := by
          simp [blockSize]
        have h_le1 : bS.addr + 0 + pathOffset f + blockSize τ
            ≤ bS.addr + blockSize σb := by
          show bS.addr + 0 + pathOffset f + layoutSize τ
            ≤ bS.addr + layoutSize σb
          grind
        have h_run1 := runN_Assgn_Borrow_step compProg s_osea
          (Register.R csPrefix.nextReg) srcReg RefKind.Shared false []
          (blockSize τ) (pathOffset f)
          h_code1 h_entryS h_le1 h_ref_tgt
        simp only [Nat.zero_add] at h_run1
        have h_regne : dstReg ≠ Register.R csPrefix.nextReg := by
          cases dstReg with
          | R n =>
              have h_lt := h_prb _ _ _ h_piD
              grind [RegisterBelow]
        have h_dentry : PtrRegisterEntry
            (oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
              (obseq.TyVal.PTy, [Val.Ptr bS.addr (pathOffset f)
                (blockSize σb) s_osea.perms.NextTag]))
            dstReg bD.addr 0 (blockSize τ) tagD := by
          show oseair.RegMap.lookup _ _ = _
          rw [RegMap.lookup_insert_ne _ h_regne]
          exact h_entryD
        have h_sentry : PtrRegisterEntry
            (oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
              (obseq.TyVal.PTy, [Val.Ptr bS.addr (pathOffset f)
                (blockSize σb) s_osea.perms.NextTag]))
            (Register.R csPrefix.nextReg) bS.addr (pathOffset f)
            (blockSize σb) s_osea.perms.NextTag :=
          RegMap.lookup_insert_self _ _ _
        have h_read2 : MSB.read q1 (bS.addr + pathOffset f)
            (obseq.typeSize (obseq.layoutToTyVal τ)) s_osea.perms.NextTag
            = .ok q2 := by
          rw [h_ts]
          exact h_rd1
        have h_useMut2 : MSB.useMut q2 (bD.addr + 0)
            (obseq.typeSize (obseq.layoutToTyVal τ)) tagD = .ok w := by
          rw [h_ts, Nat.add_zero]
          exact h_wq2
        have h_run2 := runN_Memcpy_step compProg
          { s_osea with
              perms := q1,
              reg := oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
                (obseq.TyVal.PTy, [Val.Ptr bS.addr (pathOffset f)
                  (blockSize σb) s_osea.perms.NextTag]),
              pc := s_osea.pc + 1 }
          dstReg (Register.R csPrefix.nextReg) (obseq.layoutToTyVal τ)
          h_code2 h_dentry h_sentry
          (by rw [h_ts, Nat.add_zero]; exact Nat.le_refl _)
          (by
            rw [h_ts]
            show bS.addr + pathOffset f + layoutSize τ
              ≤ bS.addr + layoutSize σb
            grind)
          (by
            rw [h_ts]
            intro hc
            simp only [Nat.add_zero] at hc
            exact h_ov ⟨hc.2, hc.1⟩)
          h_read2 h_useMut2
        rw [h_ts] at h_run2
        have h_die2 : MSB.die w (bS.addr + pathOffset f) (blockSize τ)
            s_osea.perms.NextTag = .ok r' := h_dwr
        have h_run3 := runN_Die_step compProg
          { s_osea with
              perms := w,
              reg := oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
                (obseq.TyVal.PTy, [Val.Ptr bS.addr (pathOffset f)
                  (blockSize σb) s_osea.perms.NextTag]),
              mem := oseair.writeWordSeq s_osea.mem bD.addr
                (oseair.readWordSeq s_osea.mem (bS.addr + pathOffset f)
                  (blockSize τ)),
              pc := s_osea.pc + 1 + 1 }
          (Register.R csPrefix.nextReg) (blockSize τ)
          h_code3 (RegMap.lookup_insert_self _ _ _) h_die2
        have h_runA := (oseair_runN_add 1 1 s_osea compProg _ h_run1).trans h_run2
        have h_run := (oseair_runN_add (1 + 1) 1 s_osea compProg _ h_runA).trans h_run3
        -- §7 memory: same values copied at the same addresses
        have h_rel : ListRel (MemValSim ρa ρt)
            (mirlite.readWordSeq s_mir.mem (bS.addr + pathOffset f) (blockSize τ))
            (oseair.readWordSeq s_osea.mem (bS.addr + pathOffset f) (blockSize τ)) :=
          readWordSeq_sim h_id_a h_sms (blockSize τ) (bS.addr + pathOffset f)
        have h_dom : ∀ k,
            k < (mirlite.readWordSeq s_mir.mem (bS.addr + pathOffset f)
              (blockSize τ)).length →
            ρa (bD.addr + k) = some (bD.addr + k) := by
          intro k hk
          obtain ⟨a', ha'⟩ := h_domD k (by simpa using hk)
          grind [IdentityOnDomain]
        have h_sms' : SourceMemSim ρa ρt
            (mirlite.writeWordSeq s_mir.mem bD.addr
              (mirlite.readWordSeq s_mir.mem (bS.addr + pathOffset f) (blockSize τ)))
            (oseair.writeWordSeq s_osea.mem bD.addr
              (oseair.readWordSeq s_osea.mem (bS.addr + pathOffset f) (blockSize τ))) :=
          SourceMemSim.writeWordSeq_extend h_id_a _ _ _ _ _ h_rel h_dom h_sms
        -- §8 the final permission relation, across the slide
        obtain ⟨hs, hp, he, hn⟩ := h_psim3
        have h_pf_final : r'.protFrames = p3.protFrames := by
          rw [h_r'_pf, h_p3q_pf, h_pfq, ← (sb_write_frames h_useMut_tgt).1]
        have h_ex_final : r'.exposed = p3.exposed := by
          rw [h_r'_ex, h_p3q_ex, h_exq, ← (sb_write_frames h_useMut_tgt).2]
        have h_nt_chain : s_osea.perms.NextTag ≤ r'.NextTag := by
          rw [h_r'_nt, h_p3q_nt, ← sb_read_NextTag h_read_tgt]
          exact h_ntle
        have h_psim_final : PermSim ρt perms'' r' := by
          refine ⟨?_, ?_, ?_, ?_⟩
          · exact StackMapSim.congr_right
              (fun a => by rw [h_find_eq a, h_p3q_sm]) hs
          · rw [h_pf_final]; exact hp
          · rw [h_ex_final]; exact he
          · refine Nat.le_trans hn ?_
            rw [sb_write_NextTag h_useMut_tgt, h_r'_nt, h_p3q_nt]
            exact h_ntle
        -- §9 rebuild the invariant
        refine ⟨_, 1 + 1 + 1, h_run, ?_⟩
        refine ⟨CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.local dstLoc)
              (.copy (.proj (.local srcLoc) f)))) csPrefix,
          ⟨prefixCompileState_succ h_csAt h_stmt h_stmtOut, ?_⟩, ?_, h_sms',
          h_psim_final, h_id_a, h_wf_t, ?_, ?_, ?_, ?_⟩
        · show s_osea.pc + 1 + 1 + 1 = _
          rw [h_pc, h_stmtRun, h_len3]
        · have h_lbs1 : LocalBindingSim ρa ρt s_mir.env
              { s_osea with
                  perms := r',
                  reg := oseair.RegMap.insert s_osea.reg
                    (Register.R csPrefix.nextReg)
                    (obseq.TyVal.PTy, [Val.Ptr bS.addr (pathOffset f)
                      (blockSize σb) s_osea.perms.NextTag]),
                  mem := oseair.writeWordSeq s_osea.mem bD.addr
                    (oseair.readWordSeq s_osea.mem (bS.addr + pathOffset f)
                      (blockSize τ)),
                  pc := s_osea.pc + 1 + 1 + 1 } csPrefix :=
            LocalBindingSim.insert_fresh_reg h_lbs h_prb (Nat.le_refl _) rfl
          intro τ' loc' binding' h_env'
          obtain ⟨reg', base', tag', h_pi', h_entry', h_ra', h_rt', h_nw', h_dom'⟩ :=
            h_lbs1 loc' binding' h_env'
          refine ⟨reg', base', tag', ?_, h_entry', h_ra', h_rt', h_nw', h_dom'⟩
          rw [h_stmtRun, getPlaceInfo_emit, getPlaceInfo_emit, getPlaceInfo_emit,
            getPlaceInfo_setNextReg]
          exact h_pi'
        · show TagRenameBounded ρt perms''.NextTag r'.NextTag
          rw [sb_write_NextTag h_useMut_src', sb_read_NextTag h_read_src]
          exact TagRenameBounded.mono h_tbd (Nat.le_refl _) h_nt_chain
        · simp only [AllocLockstep, mirlite_writeWordSeq_addrStart,
            oseair_writeWordSeq_addrStart]
          exact h_alloc
        · intro τ' loc' h_none
          rw [h_stmtRun, getPlaceInfo_emit, getPlaceInfo_emit, getPlaceInfo_emit,
            getPlaceInfo_setNextReg]
          exact h_unmap loc' h_none
        · intro idx reg'' τ'' h_look
          rw [h_stmtRun] at h_look ⊢
          rw [getPlaceInfo_emit, getPlaceInfo_emit, getPlaceInfo_emit,
            getPlaceInfo_setNextReg] at h_look
          refine RegisterBelow.mono ?_ (h_prb _ _ _ h_look)
          simp only [emit]
          omega
      · simp at h_w

/-- The fragment of `dst := copy *P` when `dst` is a mapped local and
    `P` lowers with no cleanup (a load spine): the pointer is loaded and
    the referent copied THROUGH THE LOADED TAG — `[P-code; Load;
    Memcpy]`. No Borrow and no Die: the deref place-lowering's result
    carries no cleanup, so nothing interleaves and no keystone is
    needed. -/
theorem compileStmt_copy_deref_run
    {Γ : Ctx} {τ : LayoutTy}
    {dstLoc : Local Γ τ}
    {P : Place Γ (obseq.LayoutTy.PtrL τ)}
    {cs : CompilerState} {dstReg : Register}
    {pOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared P)}
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = some (dstReg, τ))
    (h_pval : CheckedCompilerM.value (placeToRegChecked RefKind.Shared P) cs
      = Except.ok pOut)
    (h_pclean : pOut.result.cleanup = []) :
    CheckedCompilerM.run
        (compileStmtChecked
          (Stmt.assign (.local dstLoc) (.copy (.deref P)))) cs
      = emit (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) cs) with
            nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) cs).nextReg + 1 }
          [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) cs).nextReg)
            (Rhs.Load obseq.TyVal.PTy pOut.result.reg)])
          [Instr.Memcpy dstReg
            (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) cs).nextReg)
            (obseq.layoutToTyVal τ)] := by
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_existing h_dst
  have h_run' : (ensureLocalRegE dstLoc cs).snd.val = cs := h_run
  have h_deref_eq : placeToRegChecked (Γ := Γ) RefKind.Shared (.deref P)
      = (do
          let ptrOut ← placeToRegChecked RefKind.Shared P
          let ptrRes := ptrOut.result
          let loadedReg ← CheckedCompilerM.lift freshRegM
          let _ ← CheckedCompilerM.lift
            (emitM [Instr.Assgn loadedReg (Rhs.Load obseq.TyVal.PTy ptrRes.reg)])
          let _ ← CheckedCompilerM.lift (emitM (cleanupInstrs ptrRes.cleanup))
          pure {
            result := { reg := loadedReg, cleanup := [] },
            evidence := PlaceToRegEvidence.deref P ptrRes loadedReg ptrOut.evidence
          }) := by simp only [placeToRegChecked]
  simp [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked,
    h_deref_eq, h_run, h_run', h_val, h_pval]
  simp [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM,
    cleanupInstrs, h_pclean, emit_nil]

/-- The deref-src copy lowers. -/
theorem compileStmt_copy_deref_value
    {Γ : Ctx} {τ : LayoutTy}
    {dstLoc : Local Γ τ}
    {P : Place Γ (obseq.LayoutTy.PtrL τ)}
    {cs : CompilerState} {dstReg : Register}
    {pOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared P)}
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = some (dstReg, τ))
    (h_pval : CheckedCompilerM.value (placeToRegChecked RefKind.Shared P) cs
      = Except.ok pOut) :
    ∃ so, CheckedCompilerM.value
      (compileStmtChecked
        (Stmt.assign (.local dstLoc) (.copy (.deref P)))) cs
      = Except.ok so := by
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_existing h_dst
  have h_run' : (ensureLocalRegE dstLoc cs).snd.val = cs := h_run
  have h_deref_eq : placeToRegChecked (Γ := Γ) RefKind.Shared (.deref P)
      = (do
          let ptrOut ← placeToRegChecked RefKind.Shared P
          let ptrRes := ptrOut.result
          let loadedReg ← CheckedCompilerM.lift freshRegM
          let _ ← CheckedCompilerM.lift
            (emitM [Instr.Assgn loadedReg (Rhs.Load obseq.TyVal.PTy ptrRes.reg)])
          let _ ← CheckedCompilerM.lift (emitM (cleanupInstrs ptrRes.cleanup))
          pure {
            result := { reg := loadedReg, cleanup := [] },
            evidence := PlaceToRegEvidence.deref P ptrRes loadedReg ptrOut.evidence
          }) := by simp only [placeToRegChecked]
  simp only [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked,
    h_deref_eq,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
    h_run, h_pval]
  exact ⟨_, rfl⟩

/-- REGIME D→L, CLOSED 2026-08-29: `dst := copy *P` through a load
    spine, dst a bound local. Fragment `[P-code; Load; Memcpy]` — no
    Borrow, no Die, no keystone: the copy goes through the LOADED tag,
    exactly the source's wide read. The `Memcpy`'s source bound is
    supplied by the copy-range dereferenceability check (the read-side
    event fix, 2026-08-29) through `MemValSim`'s `o' = o ∧ s' = s`, and
    its nonoverlapping check by the overlap guard via
    `resolvePlace?_of_resolveAcc`. No tag is minted: both renames grow
    by `refl`. -/
theorem copy_deref_local_simulation
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {τ : LayoutTy}
    {dstLoc : Local Γ τ}
    {P : Place Γ (obseq.LayoutTy.PtrL τ)}
    {bD : mirlite.Binding}
    (compProg : oseair.Prog)
    (h_spine : LoadSpine P)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    (h_stmt : prog.get? s_mir.pc
      = some (.assign (.local dstLoc) (.copy (.deref P))))
    (h_envD : mirlite.Env.lookup s_mir.env dstLoc = some bD)
    (h_step : mirlite.stepStmt MSB s_mir
      (.assign (.local dstLoc) (.copy (.deref P))) = .ok s_mir') :
    ∃ (s_osea' : oseair.State MSB) (n : Nat),
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa ρt s_mir' s_osea' := by
  obtain ⟨csPrefix, ⟨h_csAt, h_pc⟩, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_tbd,
    h_alloc, h_unmap, h_prb⟩ := h_inv
  obtain ⟨dstReg, baseD, tagD, h_piD, h_entryD, h_raD, h_rtD, h_nwD, h_domD⟩ :=
    h_lbs dstLoc bD h_envD
  have h_baseD : baseD = bD.addr := (h_id_a _ _ h_raD).symm
  subst h_baseD
  -- §1 invert the source down to the loaded pointer and the wide read
  simp only [mirlite.stepStmt, mirlite.doAssign, mirlite.doAssignCont,
    mirlite.preparePlaceAssign,
    mirlite.resolvePlace?, h_envD, mirlite.resolvePlaceAcc,
    mirlite.evalRExpr] at h_step
  cases h_dres : mirlite.resolvePlaceAcc MSB s_mir P with
  | error e =>
      simp only [h_dres] at h_step
      simp at h_step
  | ok pr =>
  obtain ⟨pRes, permsP⟩ := pr
  simp only [h_dres] at h_step
  by_cases h_qb : pRes.addr < pRes.allocBase ∨
      pRes.addr ≥ pRes.allocBase + pRes.allocSize
  · rw [if_pos h_qb] at h_step
    simp at h_step
  · rw [if_neg h_qb] at h_step
    cases h_qread : MSB.read permsP pRes.addr 1 pRes.tag with
    | error e =>
        simp only [h_qread] at h_step
        simp at h_step
    | ok permsP' =>
    simp only [h_qread] at h_step
    cases h_qfind : mirlite.Mem.find? s_mir.mem pRes.addr with
    | none =>
        simp only [h_qfind] at h_step
        simp at h_step
    | some mv =>
    cases mv with
    | undef =>
        simp only [h_qfind] at h_step
        simp at h_step
    | word w0 =>
        simp only [h_qfind] at h_step
        simp at h_step
    | ptrVal b o sz t =>
    simp only [h_qfind] at h_step
    -- the copy-range dereferenceability check
    by_cases h_fit : b + o + blockSize τ > b + sz
    · rw [if_pos h_fit] at h_step
      simp at h_step
    · rw [if_neg h_fit] at h_step
      cases h_read2_src : MSB.read permsP' (b + o) (blockSize τ) t with
      | error e => rw [h_read2_src] at h_step; simp at h_step
      | ok perms₂ =>
      rw [h_read2_src] at h_step
      simp only [h_envD] at h_step
      -- reduce the overlap guard via the pure/access agreement at P
      rw [resolvePlace?_of_resolveAcc h_dres] at h_step
      simp only [h_qfind] at h_step
      by_cases h_ov : b + o < bD.addr + blockSize τ ∧
          bD.addr < b + o + blockSize τ
      · rw [if_pos h_ov] at h_step
        simp at h_step
      · rw [if_neg h_ov] at h_step
        -- §2 compiler-side scaffolding: the statement lowers
        have h_mapped : PlaceInputsMapped csPrefix P :=
          placeInputsMapped_of_resolveAcc h_lbs h_dres
        obtain ⟨pOut0, h_pval0⟩ := placeToRegChecked_ok_of_placeInputsMapped
          (cs := csPrefix) (kind := RefKind.Shared) (p := P) h_mapped
        obtain ⟨stmtOut, h_stmtOut⟩ :=
          compileStmt_copy_deref_value (cs := csPrefix) h_piD h_pval0
        have h_deref_eq : placeToRegChecked (Γ := Γ) RefKind.Shared (.deref P)
            = (do
                let ptrOut ← placeToRegChecked RefKind.Shared P
                let ptrRes := ptrOut.result
                let loadedReg ← CheckedCompilerM.lift freshRegM
                let _ ← CheckedCompilerM.lift
                  (emitM [Instr.Assgn loadedReg (Rhs.Load obseq.TyVal.PTy ptrRes.reg)])
                let _ ← CheckedCompilerM.lift (emitM (cleanupInstrs ptrRes.cleanup))
                pure {
                  result := { reg := loadedReg, cleanup := [] },
                  evidence := PlaceToRegEvidence.deref P ptrRes loadedReg ptrOut.evidence
                }) := by simp only [placeToRegChecked]
        have h_incr0 : StateIncr
            (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix)
            (CheckedCompilerM.run
              (placeToRegChecked RefKind.Shared (.deref P)) csPrefix) := by
          rw [h_deref_eq, CheckedCompilerM.run_bind]
          cases h : CheckedCompilerM.value (placeToRegChecked RefKind.Shared P) csPrefix with
          | ok a => exact CheckedCompilerM.incr _ _
          | error e => exact StateIncr.refl _
        have h_pre_bind : compileRExprPreChecked
              (RExpr.copy (Γ := Γ) (.deref P))
            = (do
                let srcOut ← placeToRegChecked RefKind.Shared (.deref P)
                let srcRes := srcOut.result
                pure ({
                  store := fun dstPtr =>
                    [Instr.Memcpy dstPtr srcRes.reg (obseq.layoutToTyVal τ)],
                  postCleanup := srcRes.cleanup,
                  ev := fun _ => RExprToEvidence.copy (.deref P) srcRes srcOut.evidence
                } : RhsPre Γ τ (RExpr.copy (.deref P)))) := rfl
        have h_pre_run : CheckedCompilerM.run
              (compileRExprPreChecked (RExpr.copy (Γ := Γ) (.deref P))) csPrefix
            = CheckedCompilerM.run
                (placeToRegChecked RefKind.Shared (.deref P)) csPrefix := by
          rw [h_pre_bind, CheckedCompilerM.run_bind]
          cases h : CheckedCompilerM.value
              (placeToRegChecked RefKind.Shared (.deref P)) csPrefix with
          | ok a => rfl
          | error e => rfl
        have h_rhs_bind : ∀ r : Register, compileRExprToChecked r
              (RExpr.copy (Γ := Γ) (.deref P))
            = (do
                let pre ← compileRExprPreChecked (RExpr.copy (Γ := Γ) (.deref P))
                let _ ← CheckedCompilerM.lift (emitM (pre.store r))
                let _ ← CheckedCompilerM.lift (emitM (cleanupInstrs pre.postCleanup))
                pure { result := (), evidence := pre.ev r }) := fun _ => rfl
        have h_incr1 : ∀ r : Register, StateIncr
            (CheckedCompilerM.run
              (placeToRegChecked RefKind.Shared (.deref P)) csPrefix)
            (CheckedCompilerM.run
              (compileRExprToChecked r (.copy (.deref P))) csPrefix) := by
          intro r
          rw [h_rhs_bind r, CheckedCompilerM.run_bind]
          cases h : CheckedCompilerM.value
              (compileRExprPreChecked (RExpr.copy (Γ := Γ) (.deref P))) csPrefix with
          | ok a => rw [h_pre_run] at *; exact CheckedCompilerM.incr _ _
          | error e => rw [h_pre_run] at *; exact StateIncr.refl _
        obtain ⟨h_erun, h_eval⟩ := ensureLocalRegE_existing h_piD
        have h_stmt_bind : compileStmtChecked
              (Stmt.assign (.local dstLoc) (.copy (.deref P)))
            = (do
                let dstOut ← CheckedCompilerM.lift (ensureLocalRegE dstLoc)
                let dstRes := dstOut.result
                let rhsOut ← compileRExprToChecked dstRes.reg (.copy (.deref P))
                pure {
                  result := (),
                  evidence := StmtEvidence.assignLocal dstLoc
                    (.copy (.deref P)) dstRes
                    dstOut.evidence rhsOut.evidence
                }) := rfl
        have h_incr2 : StateIncr
            (CheckedCompilerM.run
              (placeToRegChecked RefKind.Shared (.deref P)) csPrefix)
            (CheckedCompilerM.run
              (compileStmtChecked
                (Stmt.assign (.local dstLoc) (.copy (.deref P)))) csPrefix) := by
          rw [h_stmt_bind, CheckedCompilerM.run_bind]
          simp only [CheckedCompilerM.value_lift, CheckedCompilerM.run_lift, h_erun]
          rw [CheckedCompilerM.run_bind]
          split
          · simp only [CheckedCompilerM.run_pure]
            exact h_incr1 _
          · exact h_incr1 _
        have h_instP : ∀ q' instr,
            q' < (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextLabel →
            (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).code q'
              = some instr →
            compProg q' = some instr := by
          intro q' instr h_lt h_code
          have h_incrP := StateIncr.trans h_incr0 h_incr2
          refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
          · exact Nat.lt_of_lt_of_le h_lt h_incrP.nextLabel_le
          · rw [h_incrP.code_eq q' h_lt]
            exact h_code
        -- §3 the spine prelude
        obtain ⟨pOut, n1, s_mid, ptag, h_pval, h_pclean, h_prun, h_ppc, h_pmem, h_ppsim,
          h_pnt1, h_pnt2, h_plbs, h_pentry, h_prt, h_pnw, h_ple, h_prange, h_pbelow,
          h_pprm, h_pregmono, h_plabmono, -⟩ :=
          loadSpine_lowering_sim h_id_a h_wf_t h_spine RefKind.Shared csPrefix s_osea
            pRes permsP h_dres h_lbs h_prb h_sms h_psim h_pc h_instP
        have h_stmtRun := compileStmt_copy_deref_run (cs := csPrefix) (pOut := pOut)
          h_piD h_pval h_pclean
        have h_len2 : ((emit (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix) with
              nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg + 1 }
            [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg)
              (Rhs.Load obseq.TyVal.PTy pOut.result.reg)])
            [Instr.Memcpy dstReg
              (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg)
              (obseq.layoutToTyVal τ)])).nextLabel
            = (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextLabel + 2 := by
          simp only [emit, List.length_cons, List.length_nil]
        -- §4 the two instructions are in the program
        have h_code1 : compProg s_mid.pc
            = some (Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg)
                (Rhs.Load obseq.TyVal.PTy pOut.result.reg)) := by
          rw [h_ppc]
          refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
          · rw [h_stmtRun, h_len2]; omega
          · rw [h_stmtRun]
            rw [emit_code_lt_nextLabel _ _ (by
              simp only [emit, List.length_cons, List.length_nil]; omega)]
            have h := emit_code_at_new { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix) with
                nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg + 1 }
              [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg)
                (Rhs.Load obseq.TyVal.PTy pOut.result.reg)] (k := 0) (by simp)
            simpa using h
        have h_code2 : compProg (s_mid.pc + 1)
            = some (Instr.Memcpy dstReg
                (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg)
                (obseq.layoutToTyVal τ)) := by
          rw [h_ppc]
          refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
          · rw [h_stmtRun, h_len2]; omega
          · rw [h_stmtRun]
            have h := emit_code_at_new
              (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix) with
                  nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg + 1 }
                [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg)
                  (Rhs.Load obseq.TyVal.PTy pOut.result.reg)])
              [Instr.Memcpy dstReg
                (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg)
                (obseq.layoutToTyVal τ)]
              (k := 0) (by simp)
            simpa [emit] using h
        -- §5 execute the Load through the transported pointer-cell read
        obtain ⟨p2, h_read_tgt, h_psim2⟩ :=
          sb_read_respects_PermSim h_ppsim h_wf_t h_prt h_pnw h_qread
        have h_cancel : pRes.allocBase + (pRes.addr - pRes.allocBase) = pRes.addr := by
          grind
        have h_offP : pRes.addr - pRes.allocBase < pRes.allocSize := by grind
        have h_read_tgt' : MSB.read s_mid.perms
            (pRes.allocBase + (pRes.addr - pRes.allocBase)) 1 ptag = .ok p2 := by
          rw [h_cancel]; exact h_read_tgt
        have h_run1 := runN_Assgn_Load_ptr_step compProg s_mid
          (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg)
          pOut.result.reg obseq.TyVal.PTy
          h_code1 h_pentry h_offP h_read_tgt'
        obtain ⟨addr', value', h_ra', h_find_tgt, h_mvs⟩ := h_sms _ _ h_qfind
        have h_addr' : addr' = pRes.addr := (h_id_a _ _ h_ra').symm
        subst h_addr'
        cases value' with
        | Undef => exact h_mvs.elim
        | Dat _ => exact h_mvs.elim
        | Ptr b2 o2 s2 t2 =>
        obtain ⟨h_b, h_o, h_s, h_t, h_tnw, h_range⟩ := h_mvs
        have h_b2 : b2 = b := (h_id_a _ _ h_b).symm
        subst h_b2
        subst h_o
        subst h_s
        have h_rws : oseair.readWordSeq s_mid.mem
            (pRes.allocBase + (pRes.addr - pRes.allocBase))
            (obseq.typeSize obseq.TyVal.PTy) = [Val.Ptr b2 o2 s2 t2] := by
          rw [h_cancel]
          show oseair.readWordSeq s_mid.mem pRes.addr 1 = _
          rw [h_pmem]
          simp [oseair.readWordSeq, h_find_tgt]
        -- §6 transport the wide read and the dst write
        obtain ⟨p2w, h_read2_tgt, h_psim2w⟩ :=
          sb_read_respects_PermSim h_psim2 h_wf_t h_t h_tnw h_read2_src
        have h_w := h_step
        simp only [mirlite.writeResolvedPlace] at h_w
        split at h_w
        · simp at h_w
        · rename_i h_nb
          split at h_w
          · rename_i perms₃ h_useMut_src
            cases h_w
            have h_useMut_src' : MSB.useMut perms₂ bD.addr (blockSize τ) bD.tag
                = .ok perms₃ := by
              grind
            obtain ⟨dstReg2, baseD2, tagD2, h_piD2, h_entryD2, h_raD2, h_rtD2,
              h_nwD2, -⟩ := h_plbs dstLoc bD h_envD
            have h_dr2 : dstReg2 = dstReg := by grind
            have h_baseD2 : baseD2 = bD.addr := (h_id_a _ _ h_raD2).symm
            rw [h_dr2, h_baseD2] at h_entryD2
            obtain ⟨p3w, h_useMut_tgt, h_psim3w⟩ :=
              sb_write_respects_PermSim h_psim2w h_wf_t h_rtD2 h_nwD2 h_useMut_src'
            -- §7 execute the Memcpy
            have h_ts : obseq.typeSize (obseq.layoutToTyVal τ) = blockSize τ := by
              simp [blockSize]
            have h_regne : dstReg
                ≠ Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg := by
              cases dstReg with
              | R n =>
                  have h_lt := h_prb _ _ _ h_piD
                  grind [RegisterBelow]
            have h_dentry : PtrRegisterEntry
                (oseair.RegMap.insert s_mid.reg
                  (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg)
                  (obseq.TyVal.PTy, oseair.readWordSeq s_mid.mem
                    (pRes.allocBase + (pRes.addr - pRes.allocBase))
                    (obseq.typeSize obseq.TyVal.PTy)))
                dstReg bD.addr 0 (blockSize τ) tagD2 := by
              show oseair.RegMap.lookup _ _ = _
              rw [RegMap.lookup_insert_ne _ h_regne]
              exact h_entryD2
            have h_sentry : PtrRegisterEntry
                (oseair.RegMap.insert s_mid.reg
                  (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg)
                  (obseq.TyVal.PTy, oseair.readWordSeq s_mid.mem
                    (pRes.allocBase + (pRes.addr - pRes.allocBase))
                    (obseq.typeSize obseq.TyVal.PTy)))
                (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg)
                b2 o2 s2 t2 := by
              show oseair.RegMap.lookup _ _ = _
              rw [RegMap.lookup_insert_self, h_rws]
            have h_read2t : MSB.read p2 (b2 + o2)
                (obseq.typeSize (obseq.layoutToTyVal τ)) t2 = .ok p2w := by
              rw [h_ts]
              exact h_read2_tgt
            have h_useMut2t : MSB.useMut p2w (bD.addr + 0)
                (obseq.typeSize (obseq.layoutToTyVal τ)) tagD2 = .ok p3w := by
              rw [h_ts, Nat.add_zero]
              exact h_useMut_tgt
            have h_run2 := runN_Memcpy_step compProg
              { s_mid with
                  perms := p2,
                  reg := oseair.RegMap.insert s_mid.reg
                    (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg)
                    (obseq.TyVal.PTy, oseair.readWordSeq s_mid.mem
                      (pRes.allocBase + (pRes.addr - pRes.allocBase))
                      (obseq.typeSize obseq.TyVal.PTy)),
                  pc := s_mid.pc + 1 }
              dstReg
              (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg)
              (obseq.layoutToTyVal τ)
              h_code2 h_dentry h_sentry
              (by rw [h_ts, Nat.add_zero]; exact Nat.le_refl _)
              (by
                rw [h_ts]
                have h1 := Nat.not_lt.mp h_fit
                grind)
              (by
                rw [h_ts]
                intro hc
                simp only [Nat.add_zero] at hc
                exact h_ov ⟨hc.2, hc.1⟩)
              h_read2t h_useMut2t
            rw [h_ts] at h_run2
            have h_runA := (oseair_runN_add n1 1 s_osea compProg s_mid h_prun).trans h_run1
            have h_run := (oseair_runN_add (n1 + 1) 1 s_osea compProg _ h_runA).trans h_run2
            -- §8 memory: the same values copied at the same addresses
            have h_rel : ListRel (MemValSim ρa ρt)
                (mirlite.readWordSeq s_mir.mem (b2 + o2) (blockSize τ))
                (oseair.readWordSeq s_mid.mem (b2 + o2) (blockSize τ)) := by
              rw [h_pmem]
              exact readWordSeq_sim h_id_a h_sms (blockSize τ) (b2 + o2)
            have h_dom : ∀ k,
                k < (mirlite.readWordSeq s_mir.mem (b2 + o2) (blockSize τ)).length →
                ρa (bD.addr + k) = some (bD.addr + k) := by
              intro k hk
              obtain ⟨a', ha'⟩ := h_domD k (by simpa using hk)
              grind [IdentityOnDomain]
            have h_sms' : SourceMemSim ρa ρt
                (mirlite.writeWordSeq s_mir.mem bD.addr
                  (mirlite.readWordSeq s_mir.mem (b2 + o2) (blockSize τ)))
                (oseair.writeWordSeq s_mid.mem bD.addr
                  (oseair.readWordSeq s_mid.mem (b2 + o2) (blockSize τ))) :=
              SourceMemSim.writeWordSeq_extend h_id_a _ _ _ _ _ h_rel h_dom
                (by rw [h_pmem]; exact h_sms)
            -- §9 rebuild the invariant (no rename growth)
            refine ⟨_, n1 + 1 + 1, h_run, ?_⟩
            refine ⟨CheckedCompilerM.run
              (compileStmtChecked
                (Stmt.assign (.local dstLoc) (.copy (.deref P)))) csPrefix,
              ⟨prefixCompileState_succ h_csAt h_stmt h_stmtOut, ?_⟩, ?_, h_sms',
              h_psim3w, h_id_a, h_wf_t, ?_, ?_, ?_, ?_⟩
            · show s_mid.pc + 1 + 1 = _
              rw [h_ppc, h_stmtRun, h_len2]
            · have h_lbs1 : LocalBindingSim ρa ρt s_mir.env
                  { s_mid with
                      perms := p3w,
                      reg := oseair.RegMap.insert s_mid.reg
                        (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg)
                        (obseq.TyVal.PTy, oseair.readWordSeq s_mid.mem
                          (pRes.allocBase + (pRes.addr - pRes.allocBase))
                          (obseq.typeSize obseq.TyVal.PTy)),
                      mem := oseair.writeWordSeq s_mid.mem bD.addr
                        (oseair.readWordSeq s_mid.mem (b2 + o2) (blockSize τ)),
                      pc := s_mid.pc + 1 + 1 } csPrefix :=
                LocalBindingSim.insert_fresh_reg h_plbs h_prb h_pregmono rfl
              intro τ' loc' binding' h_env'
              obtain ⟨reg', base', tag', h_pi', h_entry', h_ra', h_rt', h_nw', h_dom'⟩ :=
                h_lbs1 loc' binding' h_env'
              refine ⟨reg', base', tag', ?_, h_entry', h_ra', h_rt', h_nw', h_dom'⟩
              rw [h_stmtRun, getPlaceInfo_emit, getPlaceInfo_emit,
                getPlaceInfo_setNextReg]
              show (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).placeRegMap.lookup loc'.idx.1 = _
              rw [h_pprm]
              exact h_pi'
            · show TagRenameBounded ρt perms₃.NextTag p3w.NextTag
              rw [sb_write_NextTag h_useMut_src', sb_read_NextTag h_read2_src,
                sb_read_NextTag h_qread, h_pnt1,
                sb_write_NextTag h_useMut_tgt, sb_read_NextTag h_read2_tgt,
                sb_read_NextTag h_read_tgt, h_pnt2]
              exact h_tbd
            · simp only [AllocLockstep, mirlite_writeWordSeq_addrStart,
                oseair_writeWordSeq_addrStart, h_pmem]
              exact h_alloc
            · intro τ' loc' h_none
              rw [h_stmtRun, getPlaceInfo_emit, getPlaceInfo_emit,
                getPlaceInfo_setNextReg]
              show (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).placeRegMap.lookup loc'.idx.1 = none
              rw [h_pprm]
              exact h_unmap loc' h_none
            · intro idx reg'' τ'' h_look
              rw [h_stmtRun] at h_look ⊢
              rw [getPlaceInfo_emit, getPlaceInfo_emit,
                getPlaceInfo_setNextReg] at h_look
              have h_cs : getPlaceInfo csPrefix idx = some (reg'', τ'') := by
                grind [getPlaceInfo]
              refine RegisterBelow.mono ?_ (h_prb _ _ _ h_cs)
              simp only [emit]
              exact Nat.le_trans h_pregmono (Nat.le_succ _)
          · simp at h_w

/-- RESIDUAL (sorried), NARROWED again 2026-08-29 (later): what remains
    of the copy leaf after L→L, P0→L, P→L (nonzero offset) AND D→L
    (deref src through a load spine, `copy_deref_local_simulation` —
    unlocked by the copy-range dereferenceability check) closed.
    - proj-of-proj srcs / proj-of-deref srcs: reassociation transfer
      and mixed chains, as elsewhere.
    - UNBOUND dst: the regime-B fresh-root composition (`allocateRoot`
      rebinding; `dst = src` aliasing lands in the overlap guard).
    - NON-LOCAL dst: post-lowering-order-fix the dst
      `Borrow(Mut); store; Die` is contiguous (BRIDGE 1 shape);
      composition work, not a blocker. -/
theorem copy_place_residual
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {τ : LayoutTy}
    {dst src : Place Γ τ}
    (compProg : oseair.Prog)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    (h_stmt : prog.get? s_mir.pc = some (.assign dst (.copy src)))
    (h_step : mirlite.stepStmt MSB s_mir (.assign dst (.copy src)) = .ok s_mir') :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' := by
  sorry

/-- LEAF SORRY 2 → DISPATCHER 2026-08-28: per-statement simulation for
    `.assign dst (.copy src)`, decomposed by the shapes of the two
    places. Regime L→L (both bound locals, any layout) is CLOSED by
    `copy_local_local_simulation`; the residual shapes are named. -/
theorem CompilerInv_step_copy
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {τ : LayoutTy}
    {dst src : Place Γ τ}
    (compProg : oseair.Prog)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    (h_stmt : prog.get? s_mir.pc = some (.assign dst (.copy src)))
    (h_step : mirlite.stepStmt MSB s_mir (.assign dst (.copy src)) = .ok s_mir') :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' := by
  cases dst with
  | «local» dstLoc =>
      cases src with
      | «local» srcLoc =>
          cases h_envD : mirlite.Env.lookup s_mir.env dstLoc with
          | some bD =>
              cases h_envS : mirlite.Env.lookup s_mir.env srcLoc with
              | some bS =>
                  obtain ⟨s_osea', n, h_run, h_inv'⟩ :=
                    copy_local_local_simulation compProg h_comp h_inv
                      h_stmt h_envD h_envS h_step
                  exact ⟨ρa, ρt, s_osea', n, AddrRenameIncr.refl ρa,
                    TagRenameIncr.refl ρt, h_run, h_inv'⟩
              | none =>
                  -- copy of an unbound local: the source errs at resolution
                  exfalso
                  simp [mirlite.stepStmt, mirlite.doAssign, mirlite.doAssignCont,
                    mirlite.preparePlaceAssign, mirlite.resolvePlace?, h_envD,
                    mirlite.resolvePlaceAcc, h_envS, mirlite.evalRExpr] at h_step
          | none =>
              -- fresh destination (regime-B composition; may alias src)
              exact copy_place_residual compProg h_comp h_inv h_stmt h_step
      | proj sbase ff =>
          cases sbase with
          | «local» srcLoc =>
              by_cases h_off : pathOffset ff = 0
              · cases h_envD : mirlite.Env.lookup s_mir.env dstLoc with
                | some bD =>
                    cases h_envS : mirlite.Env.lookup s_mir.env srcLoc with
                    | some bS =>
                        -- CLOSED: `dst := copy src.f` at zero offset
                        obtain ⟨s_osea', n, h_run, h_inv'⟩ :=
                          copy_proj_zero_simulation compProg h_off h_comp h_inv
                            h_stmt h_envD h_envS h_step
                        exact ⟨ρa, ρt, s_osea', n, AddrRenameIncr.refl ρa,
                          TagRenameIncr.refl ρt, h_run, h_inv'⟩
                    | none =>
                        exfalso
                        simp [mirlite.stepStmt, mirlite.doAssign, mirlite.doAssignCont,
                          mirlite.preparePlaceAssign, mirlite.resolvePlace?, h_envD,
                          mirlite.resolvePlaceAcc, h_envS,
                          mirlite.evalRExpr] at h_step
                | none =>
                    exact copy_place_residual compProg h_comp h_inv h_stmt h_step
              · cases h_envD : mirlite.Env.lookup s_mir.env dstLoc with
                | some bD =>
                    cases h_envS : mirlite.Env.lookup s_mir.env srcLoc with
                    | some bS =>
                        -- CLOSED: `dst := copy src.f` at nonzero offset
                        obtain ⟨s_osea', n, h_run, h_inv'⟩ :=
                          copy_proj_offset_simulation compProg h_off h_comp h_inv
                            h_stmt h_envD h_envS h_step
                        exact ⟨ρa, ρt, s_osea', n, AddrRenameIncr.refl ρa,
                          TagRenameIncr.refl ρt, h_run, h_inv'⟩
                    | none =>
                        exfalso
                        simp [mirlite.stepStmt, mirlite.doAssign,
                          mirlite.doAssignCont,
                          mirlite.preparePlaceAssign, mirlite.resolvePlace?, h_envD,
                          mirlite.resolvePlaceAcc, h_envS,
                          mirlite.evalRExpr] at h_step
                | none =>
                    exact copy_place_residual compProg h_comp h_inv h_stmt h_step
          | proj _ _ =>
              exact copy_place_residual compProg h_comp h_inv h_stmt h_step
          | deref _ =>
              exact copy_place_residual compProg h_comp h_inv h_stmt h_step
      | deref pp =>
          by_cases h_sp : LoadSpine pp
          · cases h_envD : mirlite.Env.lookup s_mir.env dstLoc with
            | some bD =>
                -- CLOSED: `dst := copy *p` through a load spine
                obtain ⟨s_osea', n, h_run, h_inv'⟩ :=
                  copy_deref_local_simulation compProg h_sp h_comp h_inv
                    h_stmt h_envD h_step
                exact ⟨ρa, ρt, s_osea', n, AddrRenameIncr.refl ρa,
                  TagRenameIncr.refl ρt, h_run, h_inv'⟩
            | none =>
                exact copy_place_residual compProg h_comp h_inv h_stmt h_step
          · exact copy_place_residual compProg h_comp h_inv h_stmt h_step
  | proj _ _ => exact copy_place_residual compProg h_comp h_inv h_stmt h_step
  | deref _ => exact copy_place_residual compProg h_comp h_inv h_stmt h_step

end obseq3.proof
