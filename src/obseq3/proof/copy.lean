import obseq3.proof.common
import obseq3.proof.permsim_transport

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
  simp [compileStmtChecked, compileRExprToChecked,
    h_run, h_val, h_prun, h_pval, h_pres]
  simp [CompilerM.run, CompilerM.value, emitM, cleanupInstrs]

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
  simp only [compileStmtChecked, compileRExprToChecked,
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
  simp only [mirlite.stepStmt, mirlite.doAssign, mirlite.preparePlaceAssign,
    mirlite.resolvePlace?, h_envD, mirlite.resolvePlaceAcc, h_envS,
    mirlite.evalRExpr] at h_step
  cases h_read_src : MSB.read s_mir.perms bS.addr (blockSize τ) bS.tag with
  | error e => rw [h_read_src] at h_step; simp at h_step
  | ok perms' =>
  rw [h_read_src] at h_step
  simp only at h_step
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
  simp only [compileStmtChecked, compileRExprToChecked, h_proj_eq,
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
  simp only [compileStmtChecked, compileRExprToChecked, h_proj_eq,
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
  simp only [mirlite.stepStmt, mirlite.doAssign, mirlite.preparePlaceAssign,
    mirlite.resolvePlace?, h_envD, mirlite.resolvePlaceAcc, h_envS,
    mirlite.evalRExpr, h_off] at h_step
  cases h_read_src : MSB.read s_mir.perms (bS.addr + 0) (blockSize τ) bS.tag with
  | error e => rw [h_read_src] at h_step; simp at h_step
  | ok perms' =>
  rw [h_read_src] at h_step
  simp only at h_step
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

/-- RESIDUAL (sorried), NARROWED 2026-08-28 (evening): what remains of
    the copy leaf after L→L and P0→L (zero-offset proj src) closed.
    - NONZERO-offset proj src: the fragment is
      `[Borrow(Shared); Memcpy; Die]`, and the `Memcpy` atomically does
      read-through-the-fresh-tag THEN the dst `useMut` — so the foreign
      dst op sits BETWEEN the BRIDGE-1S phases and the keystone does not
      apply as-is. This is not merely a missing proof pattern: in an
      invariant-JUNK state where two distinct locals' blocks overlap
      (`CompilerInv` carries no separation conjunct), a src-range stack
      `[.. tagD .. tagS(top)]` lets the source's read+useMut succeed
      while the target's dst `useMut` pops the fresh Shared before its
      `Die` (which demands the tag exactly on top) — target errs, leaf
      FALSE as stated. Closing it needs a SEPARATION invariant (distinct
      bound locals occupy disjoint blocks — a user/model decision; it
      would also unlock the non-local-dst commutations here and in
      ref/const_write), after which die↔useMut commute by cell
      disjointness and BRIDGE 1S applies.
    - deref src: spine composition (as D→L) plus the same interleaving
      for the trailing cleanup.
    - NON-LOCAL or UNBOUND dst: interleaved-keystone commutation /
      regime-B fresh-root composition (`dst = src` aliasing only in the
      unbound-dst branch, via `allocateRoot` rebinding). -/
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
                  simp [mirlite.stepStmt, mirlite.doAssign,
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
                        simp [mirlite.stepStmt, mirlite.doAssign,
                          mirlite.preparePlaceAssign, mirlite.resolvePlace?, h_envD,
                          mirlite.resolvePlaceAcc, h_envS,
                          mirlite.evalRExpr] at h_step
                | none =>
                    exact copy_place_residual compProg h_comp h_inv h_stmt h_step
              · exact copy_place_residual compProg h_comp h_inv h_stmt h_step
          | proj _ _ =>
              exact copy_place_residual compProg h_comp h_inv h_stmt h_step
          | deref _ =>
              exact copy_place_residual compProg h_comp h_inv h_stmt h_step
      | deref _ =>
          exact copy_place_residual compProg h_comp h_inv h_stmt h_step
  | proj _ _ => exact copy_place_residual compProg h_comp h_inv h_stmt h_step
  | deref _ => exact copy_place_residual compProg h_comp h_inv h_stmt h_step

end obseq3.proof
