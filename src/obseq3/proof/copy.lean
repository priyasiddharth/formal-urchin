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

/-- The fragment of `dst := copy *P` for a mapped local dst, stated
    over the OPAQUE run of the whole source place's lowering: the
    src-lowering code (whatever the chain emits — the mother lemma owns
    it), then one `Memcpy` through its result register. -/
theorem compileStmt_copy_derefchain_run
    {Γ : Ctx} {τ : LayoutTy}
    {dstLoc : Local Γ τ}
    {P : Place Γ (obseq.LayoutTy.PtrL τ)}
    {cs : CompilerState} {dstReg : Register}
    {sOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared (.deref P))}
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = some (dstReg, τ))
    (h_sval : CheckedCompilerM.value (placeToRegChecked RefKind.Shared (.deref P)) cs
      = Except.ok sOut)
    (h_sclean : sOut.result.cleanup = []) :
    CheckedCompilerM.run
        (compileStmtChecked
          (Stmt.assign (.local dstLoc) (.copy (.deref P)))) cs
      = emit (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (.deref P)) cs)
          [Instr.Memcpy dstReg sOut.result.reg (obseq.layoutToTyVal τ)] := by
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_existing h_dst
  have h_run' : (ensureLocalRegE dstLoc cs).snd.val = cs := h_run
  simp [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked,
    h_run, h_run', h_val, h_sval]
  simp [CompilerM.run, CompilerM.value, emitM, cleanupInstrs, h_sclean, emit_nil]

/-- The chain-src copy lowers. -/
theorem compileStmt_copy_derefchain_value
    {Γ : Ctx} {τ : LayoutTy}
    {dstLoc : Local Γ τ}
    {P : Place Γ (obseq.LayoutTy.PtrL τ)}
    {cs : CompilerState} {dstReg : Register}
    {sOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared (.deref P))}
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = some (dstReg, τ))
    (h_sval : CheckedCompilerM.value (placeToRegChecked RefKind.Shared (.deref P)) cs
      = Except.ok sOut) :
    ∃ so, CheckedCompilerM.value
      (compileStmtChecked
        (Stmt.assign (.local dstLoc) (.copy (.deref P)))) cs
      = Except.ok so := by
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_existing h_dst
  simp only [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
    h_run, h_sval]
  exact ⟨_, rfl⟩

/-! ## Flatten transfer for the copy-src shape -/

theorem compileRExprToChecked_copysrc_flatten_run
    {Γ : Ctx} {τ : LayoutTy} {P : Place Γ (obseq.LayoutTy.PtrL τ)}
    (r : Register) (cs : CompilerState) :
    CheckedCompilerM.run
        (compileRExprToChecked r (RExpr.copy (Γ := Γ) (.deref P))) cs
      = CheckedCompilerM.run
          (compileRExprToChecked r (RExpr.copy (.deref (flattenPlace P)))) cs := by
  obtain ⟨h_agr, h_agv⟩ :=
    placeToRegChecked_flatten_agree (Place.deref P) RefKind.Shared cs
  rw [show flattenPlace (Place.deref P) = Place.deref (flattenPlace P) from rfl]
    at h_agr h_agv
  simp only [compileRExprToChecked, compileRExprPreChecked,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure]
  cases hF : CheckedCompilerM.value
      (placeToRegChecked RefKind.Shared (Place.deref (flattenPlace P))) cs with
  | error eF =>
      cases hO : CheckedCompilerM.value
          (placeToRegChecked RefKind.Shared (Place.deref P)) cs with
      | error eO =>
          simp only [hF, hO]
          exact h_agr.symm
      | ok oO =>
          exfalso
          rw [hF, hO] at h_agv
          simp [Except.map] at h_agv
  | ok oF =>
      cases hO : CheckedCompilerM.value
          (placeToRegChecked RefKind.Shared (Place.deref P)) cs with
      | error eO =>
          exfalso
          rw [hF, hO] at h_agv
          simp [Except.map] at h_agv
      | ok oO =>
          have h_res : oF.result = oO.result := by
            rw [hF, hO] at h_agv
            simpa [Except.map] using h_agv
          simp only [hF, hO, h_res]
          rw [h_agr]

theorem compileRExprToChecked_copysrc_flatten_valunit
    {Γ : Ctx} {τ : LayoutTy} {P : Place Γ (obseq.LayoutTy.PtrL τ)}
    (r : Register) (cs : CompilerState) :
    (CheckedCompilerM.value
        (compileRExprToChecked r (RExpr.copy (Γ := Γ) (.deref P))) cs).map
      (fun _ => ())
      = (CheckedCompilerM.value
          (compileRExprToChecked r (RExpr.copy (.deref (flattenPlace P)))) cs).map
        (fun _ => ()) := by
  obtain ⟨h_agr, h_agv⟩ :=
    placeToRegChecked_flatten_agree (Place.deref P) RefKind.Shared cs
  rw [show flattenPlace (Place.deref P) = Place.deref (flattenPlace P) from rfl]
    at h_agr h_agv
  simp only [compileRExprToChecked, compileRExprPreChecked,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure]
  cases hF : CheckedCompilerM.value
      (placeToRegChecked RefKind.Shared (Place.deref (flattenPlace P))) cs with
  | error eF =>
      cases hO : CheckedCompilerM.value
          (placeToRegChecked RefKind.Shared (Place.deref P)) cs with
      | error eO =>
          have h_e : eF = eO := by
            rw [hF, hO] at h_agv
            simpa [Except.map] using h_agv
          subst h_e
          simp [hF, hO, Except.map]
      | ok oO =>
          exfalso
          rw [hF, hO] at h_agv
          simp [Except.map] at h_agv
  | ok oF =>
      cases hO : CheckedCompilerM.value
          (placeToRegChecked RefKind.Shared (Place.deref P)) cs with
      | error eO =>
          exfalso
          rw [hF, hO] at h_agv
          simp [Except.map] at h_agv
      | ok oO =>
          simp [hF, hO, Except.map]

theorem compileStmt_copy_derefsrc_flatten_run
    {Γ : Ctx} {τ : LayoutTy}
    {dstLoc : Local Γ τ} {P : Place Γ (obseq.LayoutTy.PtrL τ)}
    (cs : CompilerState) :
    CheckedCompilerM.run
        (compileStmtChecked
          (Stmt.assign (.local dstLoc) (.copy (.deref P)))) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.local dstLoc) (.copy (.deref (flattenPlace P))))) cs := by
  simp only [compileStmtChecked,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure]
  have h_run := compileRExprToChecked_copysrc_flatten_run (Γ := Γ) (P := P)
    ((ensureLocalRegE dstLoc).value cs).result.reg
    (CompilerM.run (ensureLocalRegE dstLoc) cs)
  have h_val := compileRExprToChecked_copysrc_flatten_valunit (Γ := Γ) (P := P)
    ((ensureLocalRegE dstLoc).value cs).result.reg
    (CompilerM.run (ensureLocalRegE dstLoc) cs)
  cases hO : CheckedCompilerM.value
      (compileRExprToChecked ((ensureLocalRegE dstLoc).value cs).result.reg
        (RExpr.copy (Γ := Γ) (.deref P)))
      (CompilerM.run (ensureLocalRegE dstLoc) cs) with
  | error eO =>
      cases hF : CheckedCompilerM.value
          (compileRExprToChecked ((ensureLocalRegE dstLoc).value cs).result.reg
            (RExpr.copy (.deref (flattenPlace P))))
          (CompilerM.run (ensureLocalRegE dstLoc) cs) with
      | error eF =>
          simp only [hO, hF]
          exact h_run
      | ok oF =>
          exfalso
          rw [hO, hF] at h_val
          simp [Except.map] at h_val
  | ok oO =>
      cases hF : CheckedCompilerM.value
          (compileRExprToChecked ((ensureLocalRegE dstLoc).value cs).result.reg
            (RExpr.copy (.deref (flattenPlace P))))
          (CompilerM.run (ensureLocalRegE dstLoc) cs) with
      | error eF =>
          exfalso
          rw [hO, hF] at h_val
          simp [Except.map] at h_val
      | ok oF =>
          simp only [hO, hF]
          exact h_run

theorem compileStmt_copy_derefsrc_flatten_value
    {Γ : Ctx} {τ : LayoutTy}
    {dstLoc : Local Γ τ} {P : Place Γ (obseq.LayoutTy.PtrL τ)}
    (cs : CompilerState) :
    ∀ so, CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.local dstLoc) (.copy (.deref (flattenPlace P))))) cs
      = Except.ok so →
    ∃ so', CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.local dstLoc) (.copy (.deref P)))) cs
      = Except.ok so' := by
  intro so h_so
  have h_val := compileRExprToChecked_copysrc_flatten_valunit (Γ := Γ) (P := P)
    ((ensureLocalRegE dstLoc).value cs).result.reg
    (CompilerM.run (ensureLocalRegE dstLoc) cs)
  simp only [compileStmtChecked,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure] at h_so ⊢
  cases hO : CheckedCompilerM.value
      (compileRExprToChecked ((ensureLocalRegE dstLoc).value cs).result.reg
        (RExpr.copy (Γ := Γ) (.deref P)))
      (CompilerM.run (ensureLocalRegE dstLoc) cs) with
  | error eO =>
      exfalso
      cases hF : CheckedCompilerM.value
          (compileRExprToChecked ((ensureLocalRegE dstLoc).value cs).result.reg
            (RExpr.copy (.deref (flattenPlace P))))
          (CompilerM.run (ensureLocalRegE dstLoc) cs) with
      | error eF =>
          rw [hF] at h_so
          simp at h_so
      | ok oF =>
          rw [hO, hF] at h_val
          simp [Except.map] at h_val
  | ok oO =>
      simp only [hO]
      exact ⟨_, rfl⟩

/-- REGIME D→L over full chains, COLLAPSED 2026-08-31 (originally
    closed 2026-08-29 for load spines): `dst := copy *P` for every src
    with `PtrChain (.deref P)` — spines, proj-topped pointer places
    (`x := copy *(s.f)`), interior projections at any depth. The mother
    lemma at `Shared` on the WHOLE source place performs the lowering
    including the final `Load`; the leaf adds one `Memcpy` whose source
    bound is the copy-range dereferenceability check and whose
    nonoverlapping check is the overlap guard via
    `resolvePlace?_of_resolveAcc`. No tag survives: renames grow by
    `refl`. -/
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
    (h_spine : PtrChain (Place.deref P))
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    {stmt0 : Stmt Γ}
    (h_stmt : prog.get? s_mir.pc = some stmt0)
    (h_run0 : ∀ cs, CheckedCompilerM.run (compileStmtChecked stmt0) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.local dstLoc) (.copy (.deref P)))) cs)
    (h_val0 : ∀ cs so, CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.local dstLoc) (.copy (.deref P)))) cs
        = Except.ok so →
      ∃ so', CheckedCompilerM.value (compileStmtChecked stmt0) cs
        = Except.ok so')
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
  -- §1 invert: prepare is a no-op (bound dst); the rhs resolves the
  -- whole src place ACC-style (kept OPAQUE for the mother lemma),
  -- checks the range, and wide-reads through the resolved tag
  simp only [mirlite.stepStmt, mirlite.doAssign] at h_step
  cases h_prep : mirlite.preparePlaceAssign MSB s_mir (Place.local dstLoc) with
  | err msg => rw [h_prep] at h_step; simp at h_step
  | ok s1 =>
  rw [h_prep] at h_step
  have h_s1 : s1 = s_mir := by
    simp only [mirlite.preparePlaceAssign, mirlite.resolvePlace?, h_envD] at h_prep
    grind
  rw [h_s1] at h_step
  simp only [mirlite.evalRExpr] at h_step
  cases h_dres : mirlite.resolvePlaceAcc MSB s_mir (Place.deref P) with
  | error e => rw [h_dres] at h_step; simp at h_step
  | ok pr =>
  obtain ⟨rs, permsP'⟩ := pr
  rw [h_dres] at h_step
  simp only at h_step
  by_cases h_fit : rs.addr + blockSize τ > rs.allocBase + rs.allocSize
  · rw [if_pos h_fit] at h_step
    simp at h_step
  · rw [if_neg h_fit] at h_step
    cases h_read_src : MSB.read permsP' rs.addr (blockSize τ) rs.tag with
    | error e => rw [h_read_src] at h_step; simp at h_step
    | ok perms₂ =>
    rw [h_read_src] at h_step
    simp only [mirlite.resolvePlaceAcc, h_envD] at h_step
    rw [resolvePlace?_of_resolveAcc h_dres] at h_step
    simp only at h_step
    by_cases h_ov : rs.addr < bD.addr + blockSize τ ∧
        bD.addr < rs.addr + blockSize τ
    · rw [if_pos h_ov] at h_step
      simp at h_step
    · rw [if_neg h_ov] at h_step
      -- §2 compiler scaffolding: mapped-ness, statement value,
      -- code-inclusion for the whole src-place lowering
      have h_mapped : PlaceInputsMapped csPrefix (Place.deref P) :=
        placeInputsMapped_of_localBindingSim_resolvePlace h_lbs
          (resolvePlace?_of_resolveAcc h_dres)
      obtain ⟨sOut0, h_sval0⟩ := placeToRegChecked_ok_of_placeInputsMapped
        (cs := csPrefix) (kind := RefKind.Shared) h_mapped
      obtain ⟨stmtOutC, h_stmtOutC⟩ :=
        compileStmt_copy_derefchain_value h_piD h_sval0
      obtain ⟨stmtOut, h_stmtOut⟩ := h_val0 csPrefix stmtOutC h_stmtOutC
      have h_incrS : StateIncr
          (CheckedCompilerM.run
            (placeToRegChecked RefKind.Shared (Place.deref P)) csPrefix)
          (CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix) := by
        rw [h_run0]
        obtain ⟨h_erun, h_eval⟩ := ensureLocalRegE_existing h_piD
        simp only [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked,
          CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
          CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
          CheckedCompilerM.run_pure, CheckedCompilerM.value_pure, h_erun, h_sval0]
        simp only [CompilerM.run, emitM]
        exact StateIncr.trans (emit_state_incr _ _) (emit_state_incr _ _)
      have h_instS : ∀ q' instr,
          q' < (CheckedCompilerM.run
            (placeToRegChecked RefKind.Shared (Place.deref P)) csPrefix).nextLabel →
          (CheckedCompilerM.run
            (placeToRegChecked RefKind.Shared (Place.deref P)) csPrefix).code q'
            = some instr →
          compProg q' = some instr := by
        intro q' instr h_lt h_code
        refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
        · exact Nat.lt_of_lt_of_le h_lt h_incrS.nextLabel_le
        · rw [h_incrS.code_eq q' h_lt]
          exact h_code
      -- §3 the mother lemma on the WHOLE src place (through the Load)
      obtain ⟨sOut, n1, s_mid, tres, h_sval, h_sclean, h_srun, h_spc, h_smem,
        h_spsim, h_snt1, h_snt2, h_slbs, h_sentry, h_srt, h_snw, h_sle, h_srange,
        h_sbelow, h_sprm, h_sregmono, h_slabmono, -, -⟩ :=
        ptrChain_lowering_sim h_id_a h_wf_t h_spine RefKind.Shared csPrefix s_osea
          rs permsP' h_dres h_tbd h_lbs h_prb h_sms h_psim h_pc h_instS
      have h_stmtRun := (h_run0 csPrefix).trans
        (compileStmt_copy_derefchain_run h_piD h_sval h_sclean)
      have h_cancel : rs.allocBase + (rs.addr - rs.allocBase) = rs.addr :=
        Nat.add_sub_cancel' h_sle
      -- §4 transports: the wide read through the resolved tag, then the
      -- dst write
      obtain ⟨p2w, h_read2_tgt, h_psim2w⟩ :=
        sb_read_respects_PermSim h_spsim h_wf_t h_srt h_snw h_read_src
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
            h_nwD2, -⟩ := h_slbs dstLoc bD h_envD
          have h_dr2 : dstReg2 = dstReg := by grind
          have h_baseD2 : baseD2 = bD.addr := (h_id_a _ _ h_raD2).symm
          rw [h_dr2, h_baseD2] at h_entryD2
          obtain ⟨p3w, h_useMut_tgt, h_psim3w⟩ :=
            sb_write_respects_PermSim h_psim2w h_wf_t h_rtD2 h_nwD2 h_useMut_src'
          -- §5 execute the Memcpy through the mother lemma's register
          have h_ts : obseq.typeSize (obseq.layoutToTyVal τ) = blockSize τ := by
            simp [blockSize]
          have h_code : compProg s_mid.pc
              = some (Instr.Memcpy dstReg sOut.result.reg (obseq.layoutToTyVal τ)) := by
            rw [h_spc]
            refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
            · rw [h_stmtRun]
              show _ < _ + 1
              exact Nat.lt_succ_self _
            · rw [h_stmtRun]
              have h := emit_code_at_new
                (CheckedCompilerM.run
                  (placeToRegChecked RefKind.Shared (Place.deref P)) csPrefix)
                [Instr.Memcpy dstReg sOut.result.reg (obseq.layoutToTyVal τ)]
                (k := 0) (by simp)
              simpa using h
          have h_read2t : MSB.read s_mid.perms
              (rs.allocBase + (rs.addr - rs.allocBase))
              (obseq.typeSize (obseq.layoutToTyVal τ)) tres = .ok p2w := by
            rw [h_ts, h_cancel]
            exact h_read2_tgt
          have h_useMut2t : MSB.useMut p2w (bD.addr + 0)
              (obseq.typeSize (obseq.layoutToTyVal τ)) tagD2 = .ok p3w := by
            rw [h_ts, Nat.add_zero]
            exact h_useMut_tgt
          have h_run2 := runN_Memcpy_step compProg s_mid
            dstReg sOut.result.reg (obseq.layoutToTyVal τ)
            h_code h_entryD2 h_sentry
            (by rw [h_ts, Nat.add_zero]; exact Nat.le_refl _)
            (by rw [h_ts]; grind)
            (by rw [h_ts]; grind)
            h_read2t h_useMut2t
          rw [h_ts, h_cancel] at h_run2
          simp only [Nat.add_zero] at h_run2
          have h_run := (oseair_runN_add n1 1 s_osea compProg s_mid h_srun).trans h_run2
          -- §6 memory: the same values copied at the same addresses
          have h_rel : ListRel (MemValSim ρa ρt)
              (mirlite.readWordSeq s_mir.mem rs.addr (blockSize τ))
              (oseair.readWordSeq s_mid.mem rs.addr (blockSize τ)) := by
            rw [h_smem]
            exact readWordSeq_sim h_id_a h_sms (blockSize τ) rs.addr
          have h_dom : ∀ k,
              k < (mirlite.readWordSeq s_mir.mem rs.addr (blockSize τ)).length →
              ρa (bD.addr + k) = some (bD.addr + k) := by
            intro k hk
            obtain ⟨a', ha'⟩ := h_domD k (by simpa using hk)
            grind [IdentityOnDomain]
          have h_sms' : SourceMemSim ρa ρt
              (mirlite.writeWordSeq s_mir.mem bD.addr
                (mirlite.readWordSeq s_mir.mem rs.addr (blockSize τ)))
              (oseair.writeWordSeq s_mid.mem bD.addr
                (oseair.readWordSeq s_mid.mem rs.addr (blockSize τ))) :=
            SourceMemSim.writeWordSeq_extend h_id_a _ _ _ _ _ h_rel h_dom
              (by rw [h_smem]; exact h_sms)
          -- §7 rebuild the invariant (no rename growth, no register writes)
          refine ⟨_, n1 + 1, h_run, ?_⟩
          refine ⟨CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix,
            ⟨prefixCompileState_succ h_csAt h_stmt h_stmtOut, ?_⟩, ?_, h_sms',
            h_psim3w, h_id_a, h_wf_t, ?_, ?_, ?_, ?_⟩
          · show s_mid.pc + 1 = _
            rw [h_spc, h_stmtRun]
            simp [emit]
          · intro τ' loc' binding' h_env'
            obtain ⟨reg', base', tag', h_pi', h_entry', h_ra', h_rt', h_nw', h_dom'⟩ :=
              h_slbs loc' binding' h_env'
            refine ⟨reg', base', tag', ?_, h_entry', h_ra', h_rt', h_nw', h_dom'⟩
            rw [h_stmtRun, getPlaceInfo_emit]
            show (CheckedCompilerM.run
              (placeToRegChecked RefKind.Shared (Place.deref P)) csPrefix).placeRegMap.lookup
                loc'.idx.1 = _
            rw [h_sprm]
            exact h_pi'
          · show TagRenameBounded ρt perms₃.NextTag p3w.NextTag
            rw [sb_write_NextTag h_useMut_src', sb_read_NextTag h_read_src, h_snt1,
              sb_write_NextTag h_useMut_tgt, sb_read_NextTag h_read2_tgt]
            exact TagRenameBounded.mono h_tbd (Nat.le_refl _) h_snt2
          · simp only [AllocLockstep, mirlite_writeWordSeq_addrStart,
              oseair_writeWordSeq_addrStart, h_smem]
            exact h_alloc
          · intro τ' loc' h_none
            rw [h_stmtRun, getPlaceInfo_emit]
            show (CheckedCompilerM.run
              (placeToRegChecked RefKind.Shared (Place.deref P)) csPrefix).placeRegMap.lookup
                loc'.idx.1 = none
            rw [h_sprm]
            exact h_unmap loc' h_none
          · intro idx reg'' τ'' h_look
            rw [h_stmtRun] at h_look ⊢
            rw [getPlaceInfo_emit] at h_look
            have h_prm2 : (CheckedCompilerM.run
                (placeToRegChecked RefKind.Shared (Place.deref P)) csPrefix).placeRegMap
                = csPrefix.placeRegMap := h_sprm
            have h_cs : getPlaceInfo csPrefix idx = some (reg'', τ'') := by
              show csPrefix.placeRegMap.lookup idx = _
              rw [← h_prm2]
              exact h_look
            refine RegisterBelow.mono ?_ (h_prb _ _ _ h_cs)
            simp only [emit]
            exact h_sregmono
        · simp at h_w

/-! ## Proj-topped sources over CHAIN bases: fragments over the opaque
    base lowering. `placeToRegChecked Shared (.proj B path)` runs B's
    code (the mother lemma owns it), then passes the register through
    at offset zero or mints a `Borrow(Shared)` otherwise; the statement
    adds the `Memcpy` and the cleanup `Die`. -/

theorem compileStmt_copy_projchain_zero_run
    {Γ : Ctx} {τ σb : LayoutTy}
    {dstLoc : Local Γ τ} {B : Place Γ σb} {path : PathTo σb τ}
    {cs : CompilerState} {dstReg : Register}
    {bOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared B)}
    (h_np : ∀ (σ' : LayoutTy) (b : Place Γ σ') (q : PathTo σ' σb), B = b.proj q → False)
    (h_off : pathOffset path = 0)
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = some (dstReg, τ))
    (h_bval : CheckedCompilerM.value (placeToRegChecked RefKind.Shared B) cs
      = Except.ok bOut)
    (h_bclean : bOut.result.cleanup = []) :
    CheckedCompilerM.run
        (compileStmtChecked
          (Stmt.assign (.local dstLoc) (.copy (.proj B path)))) cs
      = emit (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs)
          [Instr.Memcpy dstReg bOut.result.reg (obseq.layoutToTyVal τ)] := by
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_existing h_dst
  have h_run' : (ensureLocalRegE dstLoc cs).snd.val = cs := h_run
  have h_proj_eq := placeToRegChecked_proj_root_eq (Γ := Γ)
    (kind := RefKind.Shared) (base := B) path h_np
  simp only [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked,
    h_proj_eq,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
    h_run, h_run', h_val, h_bval, h_off, dif_pos]
  simp [CompilerM.run, CompilerM.value, emitM, cleanupInstrs, h_bclean, emit_nil]

theorem compileStmt_copy_projchain_zero_value
    {Γ : Ctx} {τ σb : LayoutTy}
    {dstLoc : Local Γ τ} {B : Place Γ σb} {path : PathTo σb τ}
    {cs : CompilerState} {dstReg : Register}
    {bOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared B)}
    (h_np : ∀ (σ' : LayoutTy) (b : Place Γ σ') (q : PathTo σ' σb), B = b.proj q → False)
    (h_off : pathOffset path = 0)
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = some (dstReg, τ))
    (h_bval : CheckedCompilerM.value (placeToRegChecked RefKind.Shared B) cs
      = Except.ok bOut) :
    ∃ so, CheckedCompilerM.value
      (compileStmtChecked
        (Stmt.assign (.local dstLoc) (.copy (.proj B path)))) cs
      = Except.ok so := by
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_existing h_dst
  have h_proj_eq := placeToRegChecked_proj_root_eq (Γ := Γ)
    (kind := RefKind.Shared) (base := B) path h_np
  simp only [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked,
    h_proj_eq,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
    h_run, h_bval, h_off, dif_pos]
  exact ⟨_, rfl⟩

theorem compileStmt_copy_projchain_offset_run
    {Γ : Ctx} {τ σb : LayoutTy}
    {dstLoc : Local Γ τ} {B : Place Γ σb} {path : PathTo σb τ}
    {cs : CompilerState} {dstReg : Register}
    {bOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared B)}
    (h_np : ∀ (σ' : LayoutTy) (b : Place Γ σ') (q : PathTo σ' σb), B = b.proj q → False)
    (h_off : pathOffset path ≠ 0)
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = some (dstReg, τ))
    (h_bval : CheckedCompilerM.value (placeToRegChecked RefKind.Shared B) cs
      = Except.ok bOut)
    (h_bclean : bOut.result.cleanup = []) :
    CheckedCompilerM.run
        (compileStmtChecked
          (Stmt.assign (.local dstLoc) (.copy (.proj B path)))) cs
      = emit (emit (emit
          { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs) with
              nextReg := (CheckedCompilerM.run
                (placeToRegChecked RefKind.Shared B) cs).nextReg + 1 }
          [Instr.Assgn (Register.R (CheckedCompilerM.run
              (placeToRegChecked RefKind.Shared B) cs).nextReg)
            (borrowRhs RefKind.Shared (blockSize τ) bOut.result.reg (pathOffset path))])
          [Instr.Memcpy dstReg (Register.R (CheckedCompilerM.run
              (placeToRegChecked RefKind.Shared B) cs).nextReg)
            (obseq.layoutToTyVal τ)])
          [Instr.Die (Register.R (CheckedCompilerM.run
              (placeToRegChecked RefKind.Shared B) cs).nextReg) (blockSize τ)] := by
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_existing h_dst
  have h_run' : (ensureLocalRegE dstLoc cs).snd.val = cs := h_run
  have h_proj_eq := placeToRegChecked_proj_root_eq (Γ := Γ)
    (kind := RefKind.Shared) (base := B) path h_np
  simp only [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked,
    h_proj_eq,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
    h_run, h_run', h_val, h_bval]
  simp [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM,
    cleanupInstrs, h_bclean, emit_nil, h_off, borrowRhs]

theorem compileStmt_copy_projchain_offset_value
    {Γ : Ctx} {τ σb : LayoutTy}
    {dstLoc : Local Γ τ} {B : Place Γ σb} {path : PathTo σb τ}
    {cs : CompilerState} {dstReg : Register}
    {bOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared B)}
    (h_np : ∀ (σ' : LayoutTy) (b : Place Γ σ') (q : PathTo σ' σb), B = b.proj q → False)
    (h_off : pathOffset path ≠ 0)
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = some (dstReg, τ))
    (h_bval : CheckedCompilerM.value (placeToRegChecked RefKind.Shared B) cs
      = Except.ok bOut) :
    ∃ so, CheckedCompilerM.value
      (compileStmtChecked
        (Stmt.assign (.local dstLoc) (.copy (.proj B path)))) cs
      = Except.ok so := by
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_existing h_dst
  have h_proj_eq := placeToRegChecked_proj_root_eq (Γ := Γ)
    (kind := RefKind.Shared) (base := B) path h_np
  simp only [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked,
    h_proj_eq,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
    h_run, h_bval, dif_neg h_off]
  exact ⟨_, rfl⟩

/-- REGIME P0→L over CHAIN bases, COLLAPSED 2026-09-03: `dst := copy
    B.f` at ZERO offset for ANY canonical chain base `B` — a bound
    local (the old P0→L), a deref chain (`y := copy (*p).f` at offset
    0), any depth. The projection passes the base register through, so
    this is the chain-src leaf with a `+ 0` on the resolution. -/
theorem copy_projchain_zero_simulation
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {τ σb : LayoutTy}
    {dstLoc : Local Γ τ} {B : Place Γ σb} {path : PathTo σb τ}
    {bD : mirlite.Binding}
    (compProg : oseair.Prog)
    (h_chain : PtrChain B)
    (h_off : pathOffset path = 0)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    {stmt0 : Stmt Γ}
    (h_stmt : prog.get? s_mir.pc = some stmt0)
    (h_run0 : ∀ cs, CheckedCompilerM.run (compileStmtChecked stmt0) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.local dstLoc) (.copy (.proj B path)))) cs)
    (h_val0 : ∀ cs so, CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.local dstLoc) (.copy (.proj B path)))) cs
        = Except.ok so →
      ∃ so', CheckedCompilerM.value (compileStmtChecked stmt0) cs
        = Except.ok so')
    (h_envD : mirlite.Env.lookup s_mir.env dstLoc = some bD)
    (h_step : mirlite.stepStmt MSB s_mir
      (.assign (.local dstLoc) (.copy (.proj B path))) = .ok s_mir') :
    ∃ (s_osea' : oseair.State MSB) (n : Nat),
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa ρt s_mir' s_osea' := by
  have h_np := h_chain.not_proj
  obtain ⟨csPrefix, ⟨h_csAt, h_pc⟩, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_tbd,
    h_alloc, h_unmap, h_prb⟩ := h_inv
  obtain ⟨dstReg, baseD, tagD, h_piD, h_entryD, h_raD, h_rtD, h_nwD, h_domD⟩ :=
    h_lbs dstLoc bD h_envD
  have h_baseD : baseD = bD.addr := (h_id_a _ _ h_raD).symm
  subst h_baseD
  -- §1 invert the source step, keeping the CHAIN's resolution opaque
  simp only [mirlite.stepStmt, mirlite.doAssign] at h_step
  cases h_prep : mirlite.preparePlaceAssign MSB s_mir (Place.local dstLoc) with
  | err msg => rw [h_prep] at h_step; simp at h_step
  | ok s1 =>
  rw [h_prep] at h_step
  have h_s1 : s1 = s_mir := by
    simp only [mirlite.preparePlaceAssign, mirlite.resolvePlace?, h_envD] at h_prep
    grind
  rw [h_s1] at h_step
  simp only [mirlite.evalRExpr] at h_step
  cases h_bres : mirlite.resolvePlaceAcc MSB s_mir B with
  | error e =>
      rw [resolvePlaceAcc_proj_base_err h_bres] at h_step
      simp at h_step
  | ok pr =>
  obtain ⟨rb, permsP'⟩ := pr
  rw [resolvePlaceAcc_proj_base_ok h_bres] at h_step
  -- at zero offset the projected resolution IS the chain's
  have h_o' : PathTo.offset path = 0 := h_off
  simp only [h_o', Nat.add_zero] at h_step
  by_cases h_fit : rb.addr + blockSize τ > rb.allocBase + rb.allocSize
  · rw [if_pos h_fit] at h_step
    simp at h_step
  · rw [if_neg h_fit] at h_step
    cases h_read_src : MSB.read permsP' rb.addr (blockSize τ) rb.tag with
    | error e => rw [h_read_src] at h_step; simp at h_step
    | ok perms₂ =>
    rw [h_read_src] at h_step
    simp only [mirlite.resolvePlaceAcc, h_envD] at h_step
    rw [resolvePlace?_of_resolveAcc
      (resolvePlaceAcc_proj_base_ok (path := path) h_bres)] at h_step
    simp only [h_o', Nat.add_zero] at h_step
    by_cases h_ov : rb.addr < bD.addr + blockSize τ ∧
        bD.addr < rb.addr + blockSize τ
    · rw [if_pos h_ov] at h_step
      simp at h_step
    · rw [if_neg h_ov] at h_step
      -- §2 compiler scaffolding
      have h_mapped : PlaceInputsMapped csPrefix (Place.proj B path) :=
        placeInputsMapped_of_localBindingSim_resolvePlace h_lbs
          (resolvePlace?_of_resolveAcc
            (resolvePlaceAcc_proj_base_ok (path := path) h_bres))
      have h_mappedB : PlaceInputsMapped csPrefix B := h_mapped
      obtain ⟨bOut0, h_bval0⟩ := placeToRegChecked_ok_of_placeInputsMapped
        (cs := csPrefix) (kind := RefKind.Shared) h_mappedB
      obtain ⟨stmtOutC, h_stmtOutC⟩ :=
        compileStmt_copy_projchain_zero_value h_np h_off h_piD h_bval0
      obtain ⟨stmtOut, h_stmtOut⟩ := h_val0 csPrefix stmtOutC h_stmtOutC
      have h_incrS : StateIncr
          (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix)
          (CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix) := by
        rw [h_run0]
        obtain ⟨h_erun, h_eval⟩ := ensureLocalRegE_existing h_piD
        have h_proj_eq := placeToRegChecked_proj_root_eq (Γ := Γ)
          (kind := RefKind.Shared) (base := B) path h_np
        simp only [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked,
          h_proj_eq,
          CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
          CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
          CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
          h_erun, h_bval0, h_off, dif_pos]
        simp only [CompilerM.run, emitM]
        exact StateIncr.trans (emit_state_incr _ _) (emit_state_incr _ _)
      have h_instS : ∀ q' instr,
          q' < (CheckedCompilerM.run
            (placeToRegChecked RefKind.Shared B) csPrefix).nextLabel →
          (CheckedCompilerM.run
            (placeToRegChecked RefKind.Shared B) csPrefix).code q' = some instr →
          compProg q' = some instr := by
        intro q' instr h_lt h_code
        refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
        · exact Nat.lt_of_lt_of_le h_lt h_incrS.nextLabel_le
        · rw [h_incrS.code_eq q' h_lt]
          exact h_code
      -- §3 the mother lemma on the chain BASE
      obtain ⟨sOut, n1, s_mid, tres, h_sval, h_sclean, h_srun, h_spc, h_smem,
        h_spsim, h_snt1, h_snt2, h_slbs, h_sentry, h_srt, h_snw, h_sle, h_srange,
        h_sbelow, h_sprm, h_sregmono, h_slabmono, -, -⟩ :=
        ptrChain_lowering_sim h_id_a h_wf_t h_chain RefKind.Shared csPrefix s_osea
          rb permsP' h_bres h_tbd h_lbs h_prb h_sms h_psim h_pc h_instS
      have h_stmtRun := (h_run0 csPrefix).trans
        (compileStmt_copy_projchain_zero_run h_np h_off h_piD h_sval h_sclean)
      have h_cancel : rb.allocBase + (rb.addr - rb.allocBase) = rb.addr :=
        Nat.add_sub_cancel' h_sle
      -- §4 transports
      obtain ⟨p2w, h_read2_tgt, h_psim2w⟩ :=
        sb_read_respects_PermSim h_spsim h_wf_t h_srt h_snw h_read_src
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
            h_nwD2, -⟩ := h_slbs dstLoc bD h_envD
          have h_dr2 : dstReg2 = dstReg := by grind
          have h_baseD2 : baseD2 = bD.addr := (h_id_a _ _ h_raD2).symm
          rw [h_dr2, h_baseD2] at h_entryD2
          obtain ⟨p3w, h_useMut_tgt, h_psim3w⟩ :=
            sb_write_respects_PermSim h_psim2w h_wf_t h_rtD2 h_nwD2 h_useMut_src'
          -- §5 the Memcpy through the base register
          have h_ts : obseq.typeSize (obseq.layoutToTyVal τ) = blockSize τ := by
            simp [blockSize]
          have h_code : compProg s_mid.pc
              = some (Instr.Memcpy dstReg sOut.result.reg (obseq.layoutToTyVal τ)) := by
            rw [h_spc]
            refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
            · rw [h_stmtRun]
              show _ < _ + 1
              exact Nat.lt_succ_self _
            · rw [h_stmtRun]
              have h := emit_code_at_new
                (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix)
                [Instr.Memcpy dstReg sOut.result.reg (obseq.layoutToTyVal τ)]
                (k := 0) (by simp)
              simpa using h
          have h_read2t : MSB.read s_mid.perms
              (rb.allocBase + (rb.addr - rb.allocBase))
              (obseq.typeSize (obseq.layoutToTyVal τ)) tres = .ok p2w := by
            rw [h_ts, h_cancel]
            exact h_read2_tgt
          have h_useMut2t : MSB.useMut p2w (bD.addr + 0)
              (obseq.typeSize (obseq.layoutToTyVal τ)) tagD2 = .ok p3w := by
            rw [h_ts, Nat.add_zero]
            exact h_useMut_tgt
          have h_run2 := runN_Memcpy_step compProg s_mid
            dstReg sOut.result.reg (obseq.layoutToTyVal τ)
            h_code h_entryD2 h_sentry
            (by rw [h_ts, Nat.add_zero]; exact Nat.le_refl _)
            (by rw [h_ts]; grind)
            (by rw [h_ts]; grind)
            h_read2t h_useMut2t
          rw [h_ts, h_cancel] at h_run2
          simp only [Nat.add_zero] at h_run2
          have h_run := (oseair_runN_add n1 1 s_osea compProg s_mid h_srun).trans h_run2
          -- §6 memory
          have h_rel : ListRel (MemValSim ρa ρt)
              (mirlite.readWordSeq s_mir.mem rb.addr (blockSize τ))
              (oseair.readWordSeq s_mid.mem rb.addr (blockSize τ)) := by
            rw [h_smem]
            exact readWordSeq_sim h_id_a h_sms (blockSize τ) rb.addr
          have h_dom : ∀ k,
              k < (mirlite.readWordSeq s_mir.mem rb.addr (blockSize τ)).length →
              ρa (bD.addr + k) = some (bD.addr + k) := by
            intro k hk
            obtain ⟨a', ha'⟩ := h_domD k (by simpa using hk)
            grind [IdentityOnDomain]
          have h_sms' : SourceMemSim ρa ρt
              (mirlite.writeWordSeq s_mir.mem bD.addr
                (mirlite.readWordSeq s_mir.mem rb.addr (blockSize τ)))
              (oseair.writeWordSeq s_mid.mem bD.addr
                (oseair.readWordSeq s_mid.mem rb.addr (blockSize τ))) :=
            SourceMemSim.writeWordSeq_extend h_id_a _ _ _ _ _ h_rel h_dom
              (by rw [h_smem]; exact h_sms)
          -- §7 rebuild the invariant
          refine ⟨_, n1 + 1, h_run, ?_⟩
          refine ⟨CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix,
            ⟨prefixCompileState_succ h_csAt h_stmt h_stmtOut, ?_⟩, ?_, h_sms',
            h_psim3w, h_id_a, h_wf_t, ?_, ?_, ?_, ?_⟩
          · show s_mid.pc + 1 = _
            rw [h_spc, h_stmtRun]
            simp [emit]
          · intro τ' loc' binding' h_env'
            obtain ⟨reg', base', tag', h_pi', h_entry', h_ra', h_rt', h_nw', h_dom'⟩ :=
              h_slbs loc' binding' h_env'
            refine ⟨reg', base', tag', ?_, h_entry', h_ra', h_rt', h_nw', h_dom'⟩
            rw [h_stmtRun, getPlaceInfo_emit]
            show (CheckedCompilerM.run
              (placeToRegChecked RefKind.Shared B) csPrefix).placeRegMap.lookup
                loc'.idx.1 = _
            rw [h_sprm]
            exact h_pi'
          · show TagRenameBounded ρt perms₃.NextTag p3w.NextTag
            rw [sb_write_NextTag h_useMut_src', sb_read_NextTag h_read_src, h_snt1,
              sb_write_NextTag h_useMut_tgt, sb_read_NextTag h_read2_tgt]
            exact TagRenameBounded.mono h_tbd (Nat.le_refl _) h_snt2
          · simp only [AllocLockstep, mirlite_writeWordSeq_addrStart,
              oseair_writeWordSeq_addrStart, h_smem]
            exact h_alloc
          · intro τ' loc' h_none
            rw [h_stmtRun, getPlaceInfo_emit]
            show (CheckedCompilerM.run
              (placeToRegChecked RefKind.Shared B) csPrefix).placeRegMap.lookup
                loc'.idx.1 = none
            rw [h_sprm]
            exact h_unmap loc' h_none
          · intro idx reg'' τ'' h_look
            rw [h_stmtRun] at h_look ⊢
            rw [getPlaceInfo_emit] at h_look
            have h_prm2 : (CheckedCompilerM.run
                (placeToRegChecked RefKind.Shared B) csPrefix).placeRegMap
                = csPrefix.placeRegMap := h_sprm
            have h_cs : getPlaceInfo csPrefix idx = some (reg'', τ'') := by
              show csPrefix.placeRegMap.lookup idx = _
              rw [← h_prm2]
              exact h_look
            refine RegisterBelow.mono ?_ (h_prb _ _ _ h_cs)
            simp only [emit]
            exact h_sregmono
        · simp at h_w

/-- REGIME P→L over CHAIN bases, COLLAPSED 2026-09-03: `dst := copy
    B.f` at NONZERO offset for ANY canonical chain base `B` — a bound
    local (the old P→L) or a deref chain (`y := copy (*p).f`). The
    mother lemma at `Shared` on `B` supplies the base register; the
    statement adds `[Borrow(Shared); Memcpy; Die]`, whose dst `useMut`
    (inside the atomic `Memcpy`) slides between BRIDGE 1S's phases by
    the overlap guard's disjointness. The `Borrow`'s bound is the
    SOURCE's own copy-range check, not typing. -/
theorem copy_projchain_offset_simulation
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {τ σb : LayoutTy}
    {dstLoc : Local Γ τ} {B : Place Γ σb} {path : PathTo σb τ}
    {bD : mirlite.Binding}
    (compProg : oseair.Prog)
    (h_chain : PtrChain B)
    (h_off : pathOffset path ≠ 0)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    {stmt0 : Stmt Γ}
    (h_stmt : prog.get? s_mir.pc = some stmt0)
    (h_run0 : ∀ cs, CheckedCompilerM.run (compileStmtChecked stmt0) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.local dstLoc) (.copy (.proj B path)))) cs)
    (h_val0 : ∀ cs so, CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.local dstLoc) (.copy (.proj B path)))) cs
        = Except.ok so →
      ∃ so', CheckedCompilerM.value (compileStmtChecked stmt0) cs
        = Except.ok so')
    (h_envD : mirlite.Env.lookup s_mir.env dstLoc = some bD)
    (h_step : mirlite.stepStmt MSB s_mir
      (.assign (.local dstLoc) (.copy (.proj B path))) = .ok s_mir') :
    ∃ (s_osea' : oseair.State MSB) (n : Nat),
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa ρt s_mir' s_osea' := by
  have h_np := h_chain.not_proj
  obtain ⟨csPrefix, ⟨h_csAt, h_pc⟩, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_tbd,
    h_alloc, h_unmap, h_prb⟩ := h_inv
  obtain ⟨dstReg, baseD, tagD, h_piD, h_entryD, h_raD, h_rtD, h_nwD, h_domD⟩ :=
    h_lbs dstLoc bD h_envD
  have h_baseD : baseD = bD.addr := (h_id_a _ _ h_raD).symm
  subst h_baseD
  -- §1 invert the source step, chain resolution opaque
  simp only [mirlite.stepStmt, mirlite.doAssign] at h_step
  cases h_prep : mirlite.preparePlaceAssign MSB s_mir (Place.local dstLoc) with
  | err msg => rw [h_prep] at h_step; simp at h_step
  | ok s1 =>
  rw [h_prep] at h_step
  have h_s1 : s1 = s_mir := by
    simp only [mirlite.preparePlaceAssign, mirlite.resolvePlace?, h_envD] at h_prep
    grind
  rw [h_s1] at h_step
  simp only [mirlite.evalRExpr] at h_step
  cases h_bres : mirlite.resolvePlaceAcc MSB s_mir B with
  | error e =>
      rw [resolvePlaceAcc_proj_base_err h_bres] at h_step
      simp at h_step
  | ok pr =>
  obtain ⟨rb, permsP'⟩ := pr
  rw [resolvePlaceAcc_proj_base_ok h_bres] at h_step
  simp only [gt_iff_lt] at h_step
  by_cases h_fit : rb.allocBase + rb.allocSize
      < rb.addr + PathTo.offset path + blockSize τ
  · rw [if_pos h_fit] at h_step
    simp at h_step
  · rw [if_neg h_fit] at h_step
    cases h_read_src : MSB.read permsP' (rb.addr + PathTo.offset path)
        (blockSize τ) rb.tag with
    | error e => rw [h_read_src] at h_step; simp at h_step
    | ok perms₂ =>
    rw [h_read_src] at h_step
    simp only [mirlite.resolvePlaceAcc, h_envD] at h_step
    have h_rp : mirlite.resolvePlace? s_mir (Place.proj B path)
        = some { addr := rb.addr + PathTo.offset path, tag := rb.tag,
                 allocBase := rb.allocBase, allocSize := rb.allocSize } :=
      resolvePlace?_of_resolveAcc (resolvePlaceAcc_proj_base_ok h_bres)
    rw [h_rp] at h_step
    dsimp only at h_step
    by_cases h_ov : rb.addr + PathTo.offset path < bD.addr + blockSize τ ∧
        bD.addr < rb.addr + PathTo.offset path + blockSize τ
    · rw [if_pos h_ov] at h_step
      simp at h_step
    · rw [if_neg h_ov] at h_step
      -- §2 compiler scaffolding
      have h_mapped : PlaceInputsMapped csPrefix (Place.proj B path) :=
        placeInputsMapped_of_localBindingSim_resolvePlace h_lbs
          (resolvePlace?_of_resolveAcc
            (resolvePlaceAcc_proj_base_ok (path := path) h_bres))
      have h_mappedB : PlaceInputsMapped csPrefix B := h_mapped
      obtain ⟨bOut0, h_bval0⟩ := placeToRegChecked_ok_of_placeInputsMapped
        (cs := csPrefix) (kind := RefKind.Shared) h_mappedB
      obtain ⟨stmtOutC, h_stmtOutC⟩ :=
        compileStmt_copy_projchain_offset_value h_np h_off h_piD h_bval0
      obtain ⟨stmtOut, h_stmtOut⟩ := h_val0 csPrefix stmtOutC h_stmtOutC
      have h_incrS : StateIncr
          (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix)
          (CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix) := by
        rw [h_run0]
        obtain ⟨h_erun, h_eval⟩ := ensureLocalRegE_existing h_piD
        have h_proj_eq := placeToRegChecked_proj_root_eq (Γ := Γ)
          (kind := RefKind.Shared) (base := B) path h_np
        simp only [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked,
          h_proj_eq,
          CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
          CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
          CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
          h_erun, h_bval0, dif_neg h_off]
        simp only [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM]
        exact StateIncr.trans (freshReg_state_incr _)
          (StateIncr.trans (emit_state_incr _ _)
            (StateIncr.trans (emit_state_incr _ _) (emit_state_incr _ _)))
      have h_instS : ∀ q' instr,
          q' < (CheckedCompilerM.run
            (placeToRegChecked RefKind.Shared B) csPrefix).nextLabel →
          (CheckedCompilerM.run
            (placeToRegChecked RefKind.Shared B) csPrefix).code q' = some instr →
          compProg q' = some instr := by
        intro q' instr h_lt h_code
        refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
        · exact Nat.lt_of_lt_of_le h_lt h_incrS.nextLabel_le
        · rw [h_incrS.code_eq q' h_lt]
          exact h_code
      -- §3 the mother lemma on the chain BASE
      obtain ⟨sOut, n1, s_mid, tres, h_sval, h_sclean, h_srun, h_spc, h_smem,
        h_spsim, h_snt1, h_snt2, h_slbs, h_sentry, h_srt, h_snw, h_sle, h_srange,
        h_sbelow, h_sprm, h_sregmono, h_slabmono, -, -⟩ :=
        ptrChain_lowering_sim h_id_a h_wf_t h_chain RefKind.Shared csPrefix s_osea
          rb permsP' h_bres h_tbd h_lbs h_prb h_sms h_psim h_pc h_instS
      have h_stmtRun := (h_run0 csPrefix).trans
        (compileStmt_copy_projchain_offset_run h_np h_off h_piD h_sval h_sclean)
      have h_cancel : rb.allocBase + (rb.addr - rb.allocBase) = rb.addr :=
        Nat.add_sub_cancel' h_sle
      -- §4 transports: the projected read, the dst write
      obtain ⟨p2, h_read_tgt, h_psim2⟩ :=
        sb_read_respects_PermSim h_spsim h_wf_t h_srt h_snw h_read_src
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
            h_nwD2, -⟩ := h_slbs dstLoc bD h_envD
          have h_dr2 : dstReg2 = dstReg := by grind
          have h_baseD2 : baseD2 = bD.addr := (h_id_a _ _ h_raD2).symm
          rw [h_dr2, h_baseD2] at h_entryD2
          obtain ⟨p3, h_useMut_tgt, h_psim3⟩ :=
            sb_write_respects_PermSim h_psim2 h_wf_t h_rtD2 h_nwD2 h_useMut_src'
          -- §5 BRIDGE 1S over the mother's register
          obtain ⟨q1, h_ref_tgt⟩ := sb_ref_Shared_ok_of_sb_read_ok h_read_tgt
          have h_tbd2 : TagRenameBounded ρt permsP'.NextTag s_mid.perms.NextTag := by
            rw [h_snt1]
            exact TagRenameBounded.mono h_tbd (Nat.le_refl _) h_snt2
          have h_unprot := freshTag_not_protected h_spsim h_tbd2
          have h0 : wildcardTag < s_mid.perms.NextTag := (h_tbd2 _ _ h_wf_t.2).2
          have h_ntw : (s_mid.perms.NextTag == wildcardTag) = false := by grind
          obtain ⟨q2, q3, qAcc', h_rd1, h_die1, h_rd2, h_sm, h_exq, h_pfq, h_ntle⟩ :=
            sb_ref_read_die_cancels h_ntw h_unprot h_ref_tgt
          have h_qAcc : qAcc' = p2 := by grind
          subst h_qAcc
          -- §6 slide the dst write between the keystone's phases
          obtain ⟨p3q, h_wq3, h_p3q_sm, h_p3q_pf, h_p3q_ex, h_p3q_nt⟩ :=
            sb_write_congr h_sm h_pfq h_exq h_useMut_tgt
          have h_dis : ∀ j k, j < blockSize τ → k < blockSize τ →
              rb.addr + PathTo.offset path + j ≠ bD.addr + k := by
            intro j k hj hk h_eq
            refine h_ov ⟨?_, ?_⟩
            · calc rb.addr + PathTo.offset path
                  ≤ rb.addr + PathTo.offset path + j := Nat.le_add_right _ _
                _ = bD.addr + k := h_eq
                _ < bD.addr + blockSize τ := Nat.add_lt_add_left hk _
            · calc bD.addr
                  ≤ bD.addr + k := Nat.le_add_right _ _
                _ = rb.addr + PathTo.offset path + j := h_eq.symm
                _ < rb.addr + PathTo.offset path + blockSize τ :=
                    Nat.add_lt_add_left hj _
          obtain ⟨w, r', h_wq2, h_dwr, h_find_eq, h_r'_pf, h_r'_ex, h_r'_nt⟩ :=
            sb_die_sb_write_comm h_dis h_die1 h_wq3
          -- §7 the three instructions after the base lowering
          have h_code1 : compProg s_mid.pc
              = some (Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg)
                  (borrowRhs RefKind.Shared (blockSize τ) sOut.result.reg
                    (pathOffset path))) := by
            rw [h_spc]
            refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
            · rw [h_stmtRun]
              simp only [emit, List.length_cons, List.length_nil]
              omega
            · rw [h_stmtRun]
              rw [emit_code_lt_nextLabel _ _ (by
                simp only [emit, List.length_cons, List.length_nil]; omega)]
              rw [emit_code_lt_nextLabel _ _ (by
                simp only [emit, List.length_cons, List.length_nil]; omega)]
              have h := emit_code_at_new { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg + 1 }
                [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg)
                  (borrowRhs RefKind.Shared (blockSize τ) sOut.result.reg
                    (pathOffset path))]
                (k := 0) (by simp)
              simpa using h
          have h_code2 : compProg (s_mid.pc + 1)
              = some (Instr.Memcpy dstReg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg)
                  (obseq.layoutToTyVal τ)) := by
            rw [h_spc]
            refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
            · rw [h_stmtRun]
              simp only [emit, List.length_cons, List.length_nil]
              omega
            · rw [h_stmtRun]
              rw [emit_code_lt_nextLabel _ _ (by
                simp only [emit, List.length_cons, List.length_nil]; omega)]
              have h := emit_code_at_new
                (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg + 1 }
                  [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg)
                    (borrowRhs RefKind.Shared (blockSize τ) sOut.result.reg
                      (pathOffset path))])
                [Instr.Memcpy dstReg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg) (obseq.layoutToTyVal τ)]
                (k := 0) (by simp)
              simpa [emit] using h
          have h_code3 : compProg (s_mid.pc + 1 + 1)
              = some (Instr.Die (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg) (blockSize τ)) := by
            rw [h_spc]
            refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
            · rw [h_stmtRun]
              simp only [emit, List.length_cons, List.length_nil]
              omega
            · rw [h_stmtRun]
              have h := emit_code_at_new
                (emit (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg + 1 }
                  [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg)
                    (borrowRhs RefKind.Shared (blockSize τ) sOut.result.reg
                      (pathOffset path))])
                  [Instr.Memcpy dstReg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg)
                    (obseq.layoutToTyVal τ)])
                [Instr.Die (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg) (blockSize τ)]
                (k := 0) (by simp)
              simpa [emit] using h
          -- §8 execute: Borrow, Memcpy, Die
          have h_ts : obseq.typeSize (obseq.layoutToTyVal τ) = blockSize τ := by
            simp [blockSize]
          have h_le1 : rb.allocBase + (rb.addr - rb.allocBase) + pathOffset path
              + blockSize τ ≤ rb.allocBase + rb.allocSize := by
            rw [h_cancel]
            have := Nat.not_lt.mp h_fit
            grind
          have h_ref_tgt' : MSB.ref s_mid.perms
              (rb.allocBase + (rb.addr - rb.allocBase) + pathOffset path)
              (blockSize τ) tres RefKind.Shared false []
              = .ok (q1, s_mid.perms.NextTag) := by
            rw [h_cancel]
            exact h_ref_tgt
          have h_run1 := runN_Assgn_Borrow_step compProg s_mid
            (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg) sOut.result.reg RefKind.Shared false []
            (blockSize τ) (pathOffset path)
            h_code1 h_sentry h_le1 h_ref_tgt'
          have h_regne : dstReg ≠ Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg := by
            cases dstReg with
            | R n =>
                have h_lt := h_prb _ _ _ h_piD
                have := h_sregmono
                grind [RegisterBelow]
          have h_dentry : PtrRegisterEntry
              (oseair.RegMap.insert s_mid.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg)
                (obseq.TyVal.PTy, [Val.Ptr rb.allocBase
                  (rb.addr - rb.allocBase + pathOffset path)
                  rb.allocSize s_mid.perms.NextTag]))
              dstReg bD.addr 0 (blockSize τ) tagD2 := by
            show oseair.RegMap.lookup _ _ = _
            rw [RegMap.lookup_insert_ne _ h_regne]
            exact h_entryD2
          have h_sentry2 : PtrRegisterEntry
              (oseair.RegMap.insert s_mid.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg)
                (obseq.TyVal.PTy, [Val.Ptr rb.allocBase
                  (rb.addr - rb.allocBase + pathOffset path)
                  rb.allocSize s_mid.perms.NextTag]))
              (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg) rb.allocBase
              (rb.addr - rb.allocBase + pathOffset path)
              rb.allocSize s_mid.perms.NextTag :=
            RegMap.lookup_insert_self _ _ _
          have h_read2 : MSB.read q1
              (rb.allocBase + (rb.addr - rb.allocBase + pathOffset path))
              (obseq.typeSize (obseq.layoutToTyVal τ)) s_mid.perms.NextTag
              = .ok q2 := by
            rw [h_ts, ← Nat.add_assoc, h_cancel]
            exact h_rd1
          have h_useMut2 : MSB.useMut q2 (bD.addr + 0)
              (obseq.typeSize (obseq.layoutToTyVal τ)) tagD2 = .ok w := by
            rw [h_ts, Nat.add_zero]
            exact h_wq2
          have h_run2 := runN_Memcpy_step compProg
            { s_mid with
                perms := q1,
                reg := oseair.RegMap.insert s_mid.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg)
                  (obseq.TyVal.PTy, [Val.Ptr rb.allocBase
                    (rb.addr - rb.allocBase + pathOffset path)
                    rb.allocSize s_mid.perms.NextTag]),
                pc := s_mid.pc + 1 }
            dstReg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg) (obseq.layoutToTyVal τ)
            h_code2 h_dentry h_sentry2
            (by rw [h_ts, Nat.add_zero]; exact Nat.le_refl _)
            (by
              rw [h_ts, ← Nat.add_assoc, h_cancel]
              have := Nat.not_lt.mp h_fit
              grind)
            (by
              rw [h_ts, ← Nat.add_assoc, h_cancel]
              intro hc
              simp only [Nat.add_zero] at hc
              exact h_ov ⟨hc.2, hc.1⟩)
            h_read2 h_useMut2
          rw [h_ts, ← Nat.add_assoc, h_cancel] at h_run2
          simp only [Nat.add_zero] at h_run2
          have h_die2 : MSB.die w
              (rb.allocBase + (rb.addr - rb.allocBase + pathOffset path))
              (blockSize τ) s_mid.perms.NextTag = .ok r' := by
            rw [← Nat.add_assoc, h_cancel]
            exact h_dwr
          have h_run3 := runN_Die_step compProg
            { s_mid with
                perms := w,
                reg := oseair.RegMap.insert s_mid.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg)
                  (obseq.TyVal.PTy, [Val.Ptr rb.allocBase
                    (rb.addr - rb.allocBase + pathOffset path)
                    rb.allocSize s_mid.perms.NextTag]),
                mem := oseair.writeWordSeq s_mid.mem bD.addr
                  (oseair.readWordSeq s_mid.mem (rb.addr + pathOffset path)
                    (blockSize τ)),
                pc := s_mid.pc + 1 + 1 }
            (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg) (blockSize τ)
            h_code3 (RegMap.lookup_insert_self _ _ _) h_die2
          have h_runA := (oseair_runN_add n1 1 s_osea compProg s_mid h_srun).trans h_run1
          have h_runB := (oseair_runN_add (n1 + 1) 1 s_osea compProg _ h_runA).trans h_run2
          have h_run := (oseair_runN_add (n1 + 1 + 1) 1 s_osea compProg _ h_runB).trans h_run3
          -- §9 memory
          have h_rel : ListRel (MemValSim ρa ρt)
              (mirlite.readWordSeq s_mir.mem (rb.addr + pathOffset path) (blockSize τ))
              (oseair.readWordSeq s_mid.mem (rb.addr + pathOffset path) (blockSize τ)) := by
            rw [h_smem]
            exact readWordSeq_sim h_id_a h_sms (blockSize τ) (rb.addr + pathOffset path)
          have h_dom : ∀ k,
              k < (mirlite.readWordSeq s_mir.mem (rb.addr + pathOffset path)
                (blockSize τ)).length →
              ρa (bD.addr + k) = some (bD.addr + k) := by
            intro k hk
            obtain ⟨a', ha'⟩ := h_domD k (by simpa using hk)
            grind [IdentityOnDomain]
          have h_sms' : SourceMemSim ρa ρt
              (mirlite.writeWordSeq s_mir.mem bD.addr
                (mirlite.readWordSeq s_mir.mem (rb.addr + pathOffset path)
                  (blockSize τ)))
              (oseair.writeWordSeq s_mid.mem bD.addr
                (oseair.readWordSeq s_mid.mem (rb.addr + pathOffset path)
                  (blockSize τ))) :=
            SourceMemSim.writeWordSeq_extend h_id_a _ _ _ _ _ h_rel h_dom
              (by rw [h_smem]; exact h_sms)
          -- §10 the final permission relation, across the slide
          obtain ⟨hs, hp, he, hn⟩ := h_psim3
          have h_pf_final : r'.protFrames = p3.protFrames := by
            rw [h_r'_pf, h_p3q_pf, h_pfq, ← (sb_write_frames h_useMut_tgt).1]
          have h_ex_final : r'.exposed = p3.exposed := by
            rw [h_r'_ex, h_p3q_ex, h_exq, ← (sb_write_frames h_useMut_tgt).2]
          have h_nt_chain : s_mid.perms.NextTag ≤ r'.NextTag := by
            rw [h_r'_nt, h_p3q_nt, ← sb_read_NextTag h_read_tgt]
            exact h_ntle
          have h_psim_final : PermSim ρt perms₃ r' := by
            refine ⟨?_, ?_, ?_, ?_⟩
            · exact StackMapSim.congr_right
                (fun a => by rw [h_find_eq a, h_p3q_sm]) hs
            · rw [h_pf_final]; exact hp
            · rw [h_ex_final]; exact he
            · refine Nat.le_trans hn ?_
              rw [sb_write_NextTag h_useMut_tgt, h_r'_nt, h_p3q_nt]
              exact h_ntle
          -- §11 rebuild the invariant
          refine ⟨_, n1 + 1 + 1 + 1, h_run, ?_⟩
          refine ⟨CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix,
            ⟨prefixCompileState_succ h_csAt h_stmt h_stmtOut, ?_⟩, ?_, h_sms',
            h_psim_final, h_id_a, h_wf_t, ?_, ?_, ?_, ?_⟩
          · show s_mid.pc + 1 + 1 + 1 = _
            rw [h_spc, h_stmtRun]
            simp [emit]
          · have h_lbs1 : LocalBindingSim ρa ρt s_mir.env
                { s_mid with
                    perms := r',
                    reg := oseair.RegMap.insert s_mid.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg)
                      (obseq.TyVal.PTy, [Val.Ptr rb.allocBase
                        (rb.addr - rb.allocBase + pathOffset path)
                        rb.allocSize s_mid.perms.NextTag]),
                    mem := oseair.writeWordSeq s_mid.mem bD.addr
                      (oseair.readWordSeq s_mid.mem (rb.addr + pathOffset path)
                        (blockSize τ)),
                    pc := s_mid.pc + 1 + 1 + 1 } csPrefix :=
              LocalBindingSim.insert_fresh_reg h_slbs h_prb h_sregmono rfl
            intro τ' loc' binding' h_env'
            obtain ⟨reg', base', tag', h_pi', h_entry', h_ra', h_rt', h_nw', h_dom'⟩ :=
              h_lbs1 loc' binding' h_env'
            refine ⟨reg', base', tag', ?_, h_entry', h_ra', h_rt', h_nw', h_dom'⟩
            rw [h_stmtRun, getPlaceInfo_emit, getPlaceInfo_emit, getPlaceInfo_emit,
              getPlaceInfo_setNextReg]
            show (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).placeRegMap.lookup loc'.idx.1 = _
            rw [h_sprm]
            exact h_pi'
          · show TagRenameBounded ρt perms₃.NextTag r'.NextTag
            rw [sb_write_NextTag h_useMut_src', sb_read_NextTag h_read_src, h_snt1]
            refine TagRenameBounded.mono h_tbd (Nat.le_refl _) ?_
            exact Nat.le_trans h_snt2 h_nt_chain
          · simp only [AllocLockstep, mirlite_writeWordSeq_addrStart,
              oseair_writeWordSeq_addrStart, h_smem]
            exact h_alloc
          · intro τ' loc' h_none
            rw [h_stmtRun, getPlaceInfo_emit, getPlaceInfo_emit, getPlaceInfo_emit,
              getPlaceInfo_setNextReg]
            show (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).placeRegMap.lookup loc'.idx.1 = none
            rw [h_sprm]
            exact h_unmap loc' h_none
          · intro idx reg'' τ'' h_look
            rw [h_stmtRun] at h_look ⊢
            rw [getPlaceInfo_emit, getPlaceInfo_emit, getPlaceInfo_emit,
              getPlaceInfo_setNextReg] at h_look
            have h_cs : getPlaceInfo csPrefix idx = some (reg'', τ'') := by
              show csPrefix.placeRegMap.lookup idx = _
              rw [← h_sprm]
              exact h_look
            refine RegisterBelow.mono ?_ (h_prb _ _ _ h_cs)
            simp only [emit]
            exact Nat.le_trans h_sregmono (Nat.le_succ _)
        · simp at h_w

/-! ## Flatten transfer for a copy source of ANY shape -/

theorem compileRExprToChecked_copysrc_anyflatten_run
    {Γ : Ctx} {τ : LayoutTy} (src : Place Γ τ)
    (r : Register) (cs : CompilerState) :
    CheckedCompilerM.run (compileRExprToChecked r (RExpr.copy src)) cs
      = CheckedCompilerM.run
          (compileRExprToChecked r (RExpr.copy (flattenPlace src))) cs := by
  obtain ⟨h_agr, h_agv⟩ := placeToRegChecked_flatten_agree src RefKind.Shared cs
  simp only [compileRExprToChecked, compileRExprPreChecked,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure]
  cases hF : CheckedCompilerM.value
      (placeToRegChecked RefKind.Shared (flattenPlace src)) cs with
  | error eF =>
      cases hO : CheckedCompilerM.value (placeToRegChecked RefKind.Shared src) cs with
      | error eO =>
          simp only [hF, hO]
          exact h_agr.symm
      | ok oO =>
          exfalso
          rw [hF, hO] at h_agv
          simp [Except.map] at h_agv
  | ok oF =>
      cases hO : CheckedCompilerM.value (placeToRegChecked RefKind.Shared src) cs with
      | error eO =>
          exfalso
          rw [hF, hO] at h_agv
          simp [Except.map] at h_agv
      | ok oO =>
          have h_res : oF.result = oO.result := by
            rw [hF, hO] at h_agv
            simpa [Except.map] using h_agv
          simp only [hF, hO, h_res]
          rw [h_agr]

theorem compileRExprToChecked_copysrc_anyflatten_valunit
    {Γ : Ctx} {τ : LayoutTy} (src : Place Γ τ)
    (r : Register) (cs : CompilerState) :
    (CheckedCompilerM.value (compileRExprToChecked r (RExpr.copy src)) cs).map
      (fun _ => ())
      = (CheckedCompilerM.value
          (compileRExprToChecked r (RExpr.copy (flattenPlace src))) cs).map
        (fun _ => ()) := by
  obtain ⟨h_agr, h_agv⟩ := placeToRegChecked_flatten_agree src RefKind.Shared cs
  simp only [compileRExprToChecked, compileRExprPreChecked,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure]
  cases hF : CheckedCompilerM.value
      (placeToRegChecked RefKind.Shared (flattenPlace src)) cs with
  | error eF =>
      cases hO : CheckedCompilerM.value (placeToRegChecked RefKind.Shared src) cs with
      | error eO =>
          have h_e : eF = eO := by
            rw [hF, hO] at h_agv
            simpa [Except.map] using h_agv
          subst h_e
          simp [hF, hO, Except.map]
      | ok oO =>
          exfalso
          rw [hF, hO] at h_agv
          simp [Except.map] at h_agv
  | ok oF =>
      cases hO : CheckedCompilerM.value (placeToRegChecked RefKind.Shared src) cs with
      | error eO =>
          exfalso
          rw [hF, hO] at h_agv
          simp [Except.map] at h_agv
      | ok oO =>
          simp [hF, hO, Except.map]

theorem compileStmt_copy_srcflatten_run
    {Γ : Ctx} {τ : LayoutTy} {dstLoc : Local Γ τ} (src : Place Γ τ)
    (cs : CompilerState) :
    CheckedCompilerM.run
        (compileStmtChecked (Stmt.assign (.local dstLoc) (.copy src))) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.local dstLoc) (.copy (flattenPlace src)))) cs := by
  simp only [compileStmtChecked,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure]
  have h_run := compileRExprToChecked_copysrc_anyflatten_run src
    ((ensureLocalRegE dstLoc).value cs).result.reg
    (CompilerM.run (ensureLocalRegE dstLoc) cs)
  have h_val := compileRExprToChecked_copysrc_anyflatten_valunit src
    ((ensureLocalRegE dstLoc).value cs).result.reg
    (CompilerM.run (ensureLocalRegE dstLoc) cs)
  cases hO : CheckedCompilerM.value
      (compileRExprToChecked ((ensureLocalRegE dstLoc).value cs).result.reg
        (RExpr.copy src))
      (CompilerM.run (ensureLocalRegE dstLoc) cs) with
  | error eO =>
      cases hF : CheckedCompilerM.value
          (compileRExprToChecked ((ensureLocalRegE dstLoc).value cs).result.reg
            (RExpr.copy (flattenPlace src)))
          (CompilerM.run (ensureLocalRegE dstLoc) cs) with
      | error eF =>
          simp only [hO, hF]
          exact h_run
      | ok oF =>
          exfalso
          rw [hO, hF] at h_val
          simp [Except.map] at h_val
  | ok oO =>
      cases hF : CheckedCompilerM.value
          (compileRExprToChecked ((ensureLocalRegE dstLoc).value cs).result.reg
            (RExpr.copy (flattenPlace src)))
          (CompilerM.run (ensureLocalRegE dstLoc) cs) with
      | error eF =>
          exfalso
          rw [hO, hF] at h_val
          simp [Except.map] at h_val
      | ok oF =>
          simp only [hO, hF]
          exact h_run

/-- Existential form: the dependent evidence type of the flattened
    statement's value is not transportable along the flattening
    equation, but its EXISTENTIAL is (the motive hides the type). -/
theorem compileStmt_copy_srcflatten_value
    {Γ : Ctx} {τ : LayoutTy} {dstLoc : Local Γ τ} (src : Place Γ τ)
    (cs : CompilerState)
    (h_ex : ∃ so, CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.local dstLoc) (.copy (flattenPlace src)))) cs
      = Except.ok so) :
    ∃ so', CheckedCompilerM.value
        (compileStmtChecked (Stmt.assign (.local dstLoc) (.copy src))) cs
      = Except.ok so' := by
  obtain ⟨so, h_so⟩ := h_ex
  have h_val := compileRExprToChecked_copysrc_anyflatten_valunit src
    ((ensureLocalRegE dstLoc).value cs).result.reg
    (CompilerM.run (ensureLocalRegE dstLoc) cs)
  simp only [compileStmtChecked,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure] at h_so ⊢
  cases hO : CheckedCompilerM.value
      (compileRExprToChecked ((ensureLocalRegE dstLoc).value cs).result.reg
        (RExpr.copy src))
      (CompilerM.run (ensureLocalRegE dstLoc) cs) with
  | error eO =>
      exfalso
      cases hF : CheckedCompilerM.value
          (compileRExprToChecked ((ensureLocalRegE dstLoc).value cs).result.reg
            (RExpr.copy (flattenPlace src)))
          (CompilerM.run (ensureLocalRegE dstLoc) cs) with
      | error eF =>
          rw [hF] at h_so
          simp at h_so
      | ok oF =>
          rw [hO, hF] at h_val
          simp [Except.map] at h_val
  | ok oO =>
      simp only [hO]
      exact ⟨_, rfl⟩

/-- RESIDUAL (sorried), NARROWED 2026-09-03: for a BOUND LOCAL dst
    every source shape is now closed — the deref-src arm by the chain
    leaf and the proj-src arm by the two collapsed proj-over-chain
    leaves (`copy_projchain_zero/offset_simulation`), both reached
    through the src flatten transfer, so `(*p).f`, `(s.f).g` and any
    mix normalize in. Remaining:
    - UNBOUND dst: the regime-B fresh-root composition (`allocateRoot`
      rebinding; `dst = src` aliasing lands in the overlap guard).
    - NON-LOCAL dst: the dst `Borrow(Mut); store; Die` is contiguous
      (BRIDGE 1 shape); composition work, not a blocker. -/
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
          cases h_envD : mirlite.Env.lookup s_mir.env dstLoc with
          | some bD =>
              -- FLATTEN the whole src: its normal form is ONE projection
              -- over a canonical chain, which the two collapsed leaves own
              obtain ⟨σ', Bc, path', h_flat, h_chain⟩ :=
                flatten_proj_chainish sbase ff
              rw [stepStmt_assign_copysrc_anyflatten, h_flat] at h_step
              have h_run0 : ∀ cs, CheckedCompilerM.run (compileStmtChecked
                  (Stmt.assign (.local dstLoc) (.copy (.proj sbase ff)))) cs
                  = CheckedCompilerM.run (compileStmtChecked
                      (Stmt.assign (.local dstLoc) (.copy (.proj Bc path')))) cs := by
                intro cs
                rw [compileStmt_copy_srcflatten_run (Place.proj sbase ff) cs, h_flat]
              have h_val0 : ∀ cs so, CheckedCompilerM.value (compileStmtChecked
                  (Stmt.assign (.local dstLoc) (.copy (.proj Bc path')))) cs
                  = Except.ok so →
                  ∃ so', CheckedCompilerM.value (compileStmtChecked
                    (Stmt.assign (.local dstLoc) (.copy (.proj sbase ff)))) cs
                    = Except.ok so' := by
                intro cs so h
                refine compileStmt_copy_srcflatten_value (Place.proj sbase ff) cs ?_
                rw [h_flat]
                exact ⟨so, h⟩
              by_cases h_off : pathOffset path' = 0
              · obtain ⟨s_osea', n, h_run, h_inv'⟩ :=
                  copy_projchain_zero_simulation compProg h_chain h_off h_comp h_inv
                    h_stmt h_run0 h_val0 h_envD h_step
                exact ⟨ρa, ρt, s_osea', n, AddrRenameIncr.refl ρa,
                  TagRenameIncr.refl ρt, h_run, h_inv'⟩
              · obtain ⟨s_osea', n, h_run, h_inv'⟩ :=
                  copy_projchain_offset_simulation compProg h_chain h_off h_comp h_inv
                    h_stmt h_run0 h_val0 h_envD h_step
                exact ⟨ρa, ρt, s_osea', n, AddrRenameIncr.refl ρa,
                  TagRenameIncr.refl ρt, h_run, h_inv'⟩
          | none =>
              exact copy_place_residual compProg h_comp h_inv h_stmt h_step
      | deref pp =>
          cases h_envD : mirlite.Env.lookup s_mir.env dstLoc with
          | some bD =>
              -- CLOSED: `dst := copy *chain` — flatten-normalized, TOTAL
              rw [stepStmt_assign_copysrc_flatten] at h_step
              obtain ⟨s_osea', n, h_run, h_inv'⟩ :=
                copy_deref_local_simulation (P := flattenPlace pp) compProg
                  (PtrChain_flatten_deref pp) h_comp h_inv h_stmt
                  (fun cs => compileStmt_copy_derefsrc_flatten_run cs)
                  (fun cs so h => compileStmt_copy_derefsrc_flatten_value cs so h)
                  h_envD h_step
              exact ⟨ρa, ρt, s_osea', n, AddrRenameIncr.refl ρa,
                TagRenameIncr.refl ρt, h_run, h_inv'⟩
          | none =>
              exact copy_place_residual compProg h_comp h_inv h_stmt h_step
  | proj _ _ => exact copy_place_residual compProg h_comp h_inv h_stmt h_step
  | deref _ => exact copy_place_residual compProg h_comp h_inv h_stmt h_step

end obseq3.proof
