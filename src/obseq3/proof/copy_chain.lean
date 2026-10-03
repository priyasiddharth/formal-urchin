import obseq3.proof.derefdst

/-!
# The copy package for any pointer-chain source

`dst := copy src` with `src` a local, a deref of a chain, or a deref of a
field of a chain: the source place's lowering (`ptrChain_lowering_simB`),
one `Load` at the source's layout into a fresh register, the `RStore` at
the destination's. Supersedes `copy_local_pkg` (a local is a chain).
-/

namespace obseq3.proof

open obseq3 obseq3.bytes obseq3.proof
open obseq3.mirlite (MemValue Binding Env PlaceRes)
open obseq3.oseair (Val Register)
open obseq3.compile

/-! ## Chains compile -/

/-- A chain whose root the source has bound compiles, leaves no cleanup,
    and does not touch the place map — compile-time facts, needed before
    any code is known to be in the program. -/
theorem ptrChain_compiles {Γ : Ctx} {L : mirlite.LayEnv Γ} {M : PermissionModel}
    {s : mirlite.State M Γ} {cs : CompilerState}
    (h_map : ∀ {τ : LayoutTy} (loc : Local Γ τ) (b : Binding), s.env.lookup loc = some b →
      ∃ reg layout, getPlaceInfo cs loc.idx.1 = some (reg, layout))
    {τ : LayoutTy} {p : Place Γ τ} (h_chain : PtrChain p) :
    ∀ (kind : RefKind) (r : PlaceRes × M.State), mirlite.resolvePlaceAcc M L s p = .ok r →
      ∃ out, CheckedCompilerM.value (placeToRegChecked L kind p) cs = .ok out ∧
        out.result.cleanup = [] ∧
        (CheckedCompilerM.run (placeToRegChecked L kind p) cs).placeRegMap = cs.placeRegMap := by
  induction h_chain with
  | base loc =>
      intro kind r h
      cases h_env : s.env.lookup loc with
      | none => simp [mirlite.resolvePlaceAcc, h_env] at h
      | some b =>
          obtain ⟨reg, layout, h_pi⟩ := h_map loc b h_env
          obtain ⟨h_run, out, h_val, h_res⟩ :=
            placeToRegChecked_local_existing (L := L) (kind := kind) h_pi
          exact ⟨out, h_val, by rw [h_res], by rw [h_run]⟩
  | deref h_q ih =>
      intro kind r h
      simp only [mirlite.resolvePlaceAcc] at h
      split at h
      · cases h
      rename_i rq h_rq
      obtain ⟨qOut, h_qval, h_qclean, h_qprm⟩ := ih RefKind.Shared _ h_rq
      obtain ⟨h_run, out, h_val, h_res⟩ := deref_lowering (kind := kind) h_qval
      refine ⟨out, h_val, by rw [h_res], ?_⟩
      rw [h_run, h_qclean]
      exact h_qprm
  | derefProj f h_b ih =>
      intro kind r h
      rename_i σb τ' b
      cases h_rb : mirlite.resolvePlaceAcc M L s b with
      | error e => simp [mirlite.resolvePlaceAcc, h_rb] at h
      | ok rb =>
      obtain ⟨bOut, h_bval, h_bclean, h_bprm⟩ := ih RefKind.Shared _ h_rb
      obtain ⟨hz, hnz⟩ := proj_lowering (kind := RefKind.Shared) f (PtrChain.not_proj h_b) h_bval
      by_cases h0 : pathOffset L b f = 0
      · obtain ⟨h_runP, outP, h_valP, h_resP⟩ := hz h0
        obtain ⟨h_run, out, h_val, h_res⟩ := deref_lowering (kind := kind) h_valP
        refine ⟨out, h_val, by rw [h_res], ?_⟩
        rw [h_run, h_resP, h_bclean, h_runP]
        exact h_bprm
      · obtain ⟨h_runP, outP, h_valP, h_resP⟩ := hnz h0
        obtain ⟨h_run, out, h_val, h_res⟩ := deref_lowering (kind := kind) h_valP
        refine ⟨out, h_val, by rw [h_res], ?_⟩
        rw [h_run, h_runP]
        exact h_bprm

/-! ## The read-then-store shape, for any lowered source -/

theorem readRhsPre_shape {Γ : Ctx} {L : mirlite.LayEnv Γ} {dstL : BLayout}
    {σ τ : LayoutTy} {rhs : RExpr Γ τ} {src : Place Γ σ} {mk : Register → oseair.Rhs}
    {ev : (srcRes : PtrResult) → PlaceToRegEvidence L RefKind.Shared src srcRes →
      (dstPtr : Register) → RExprToEvidence L dstPtr rhs}
    {cs : CompilerState}
    {sOut : ResultWithEvidence PtrResult (PlaceToRegEvidence L RefKind.Shared src)}
    (h_sval : CheckedCompilerM.value (placeToRegChecked L RefKind.Shared src) cs = .ok sOut)
    (h_sclean : sOut.result.cleanup = []) :
    CheckedCompilerM.run (readRhsPre L dstL rhs src mk (fun _ => []) ev) cs
      = emit (bumpReg (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared src) cs))
          [oseair.Instr.Assgn
            (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared src) cs).nextReg)
            (mk sOut.result.reg)] ∧
    ∃ pOut, CheckedCompilerM.value (readRhsPre L dstL rhs src mk (fun _ => []) ev) cs
        = Except.ok pOut ∧
      (∀ d, pOut.store d = [oseair.Instr.RStore dstL
        (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared src) cs).nextReg) d]) ∧
      pOut.postCleanup = [] := by
  simp only [readRhsPre, CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift, CheckedCompilerM.run_pure,
    CheckedCompilerM.value_pure, h_sval]
  refine ⟨?_, _, rfl, fun _ => rfl, rfl⟩
  simp only [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM, cleanupInstrs, h_sclean,
    List.reverse_nil, List.map_nil, List.append_nil]

/-! ## The package -/

theorem copy_chain_pkg {Γ : Ctx} {σ : LayoutTy} {compProg : oseair.Prog}
    {L : mirlite.LayEnv Γ} (hWF : PtrPlacesWF L) (dstL : BLayout) {src : Place Γ σ}
    (h_chain : PtrChain src) :
    ValuePkgB compProg L dstL (RExpr.copy src) := by
  intro ρt sM sA csA h_wf h_tbd h_lbs h_prb h_mem h_alloc h_psim h_pc _h_unmap output h_ev
  -- the source: resolve, check, read whole
  simp only [mirlite.evalRExpr, mirlite.evalCopy] at h_ev
  cases h_res : mirlite.resolvePlaceAcc MSB L sM src with
  | error e => simp [h_res] at h_ev
  | ok rr =>
  obtain ⟨resolved, permsR⟩ := rr
  simp only [h_res] at h_ev
  split at h_ev
  · cases h_ev
  rename_i h_free
  split at h_ev
  · cases h_ev
  rename_i h_bnd
  split at h_ev
  · cases h_ev
  rename_i permsR' hu
  split at h_ev
  · cases h_ev
  rename_i h_def
  simp only [mirlite.EvalResult.ok.injEq] at h_ev
  subst h_ev
  -- compile-time facts
  have h_map : ∀ {τ : LayoutTy} (loc : Local Γ τ) (b : Binding), sM.env.lookup loc = some b →
      ∃ reg layout, getPlaceInfo csA loc.idx.1 = some (reg, layout) := fun loc b h => by
    obtain ⟨r, t, hpi, -⟩ := h_lbs loc b h
    exact ⟨r, _, hpi⟩
  obtain ⟨sOut, h_sval, h_sclean, h_sprm⟩ :=
    ptrChain_compiles (L := L) h_map h_chain RefKind.Shared _ h_res
  have h_pre : compileRExprPreChecked L dstL (RExpr.copy src)
      = readRhsPre L dstL (RExpr.copy src) src (oseair.Rhs.Load (mirlite.placeLayout L src))
          (fun _ => []) (fun srcRes evd _ => RExprToEvidence.copy src srcRes evd) := rfl
  obtain ⟨h_run, pOut, h_val, h_store, h_post⟩ :=
    readRhsPre_shape (dstL := dstL) (rhs := RExpr.copy src)
      (mk := oseair.Rhs.Load (mirlite.placeLayout L src))
      (ev := fun srcRes evd _ => RExprToEvidence.copy src srcRes evd) h_sval h_sclean
  rw [h_pre]
  refine ⟨_, pOut, h_val, h_store, h_post, by rw [h_run]; exact h_sprm, fun h_code => ?_⟩
  rw [h_run] at h_code ⊢
  -- the source place's lowering
  have h_codeS : CodeIncludedB compProg
      (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared src) csA) :=
    h_code.mono ((bumpReg_state_incr' _).trans (emit_state_incr _ _))
  obtain ⟨sOut', n1, s1, tres, hS⟩ :=
    ptrChain_lowering_simB hWF h_wf h_chain RefKind.Shared csA sA resolved permsR h_res h_tbd
      h_lbs h_prb h_mem h_alloc h_psim h_pc h_codeS
  have h_same : sOut' = sOut := by
    have := hS.val
    rw [h_sval] at this
    exact (Except.ok.inj this).symm
  subst h_same
  obtain ⟨ext, h_entry⟩ := hS.entry
  have hA : resolved.allocBase + (resolved.addr - resolved.allocBase) = resolved.addr :=
    Nat.add_sub_cancel' hS.le
  -- the `Load`
  have h_instr : compProg s1.pc = some (oseair.Instr.Assgn
      (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared src) csA).nextReg)
      (oseair.Rhs.Load (mirlite.placeLayout L src) sOut'.result.reg)) := by
    rw [hS.pc]
    apply h_code
    · simp [emit]
    · simp [emit]
  have h_mem1 : ByteMemSim ρt sM.mem s1.mem := by rw [hS.mem]; exact h_mem
  have h_lock1 : ByteAllocLockstep sM.mem s1.mem := by rw [hS.mem]; exact h_alloc
  obtain ⟨pT', hu', hp'⟩ := sb_read_respects_PermSim hS.psim h_wf hS.rt hu
  have hrel := readL_sim h_wf h_mem1 resolved.addr (mirlite.placeLayout L src)
  obtain ⟨h_defT, h_relS⟩ := readL_rel hrel (by simpa using h_def)
  have h_freeT : s1.mem.isFreed resolved.allocBase = false := by
    simp only [bytes.Mem.isFreed, ← h_lock1.2.2] at h_free ⊢
    simpa using h_free
  let vals := (mirlite.readL s1.mem resolved.addr (mirlite.placeLayout L src)).map oseair.ofMem
  let sR : oseair.State MSB :=
    { s1 with
        perms := pT',
        reg := s1.reg.insert
          (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared src) csA).nextReg)
          vals,
        pc := s1.pc + 1 }
  have h_run1 : oseair.runN MSB 1 s1 compProg = .Ok sR := by
    simp only [PermissionModel.stackedBorrows] at hu'
    simp only [oseair.runN, oseair.step, h_instr, oseair.evalRhs, h_entry, hA, h_freeT,
      Bool.false_eq_true, if_false, h_bnd, PermissionModel.stackedBorrows, hu']
    simp only [h_defT, Bool.false_eq_true, if_false]
    rfl
  refine ⟨ρt, n1 + 1, sR, sM.mem, permsR', vals, TagRenameIncr.refl ρt, h_wf, rfl,
    runN_trans hS.run h_run1, ?_, ?_, hp', ?_, h_mem1, h_lock1, ?_, ?_, h_relS⟩
  · -- registers
    show csA.nextReg ≤ _ + 1
    exact Nat.le_trans hS.regmono (Nat.le_succ _)
  · -- bound locals: their registers are below the watermark, untouched
    refine LocalBindingSimB.prm_congr (h_lbs.of_frame h_prb fun r hr => ?_) ?_
    · have hne := RegisterBelow.ne_fresh (RegisterBelow.mono hS.regmono hr)
      show (s1.reg.insert _ _).lookup r = _
      rw [RegMap.lookup_insert_ne _ _ hne]
      exact hS.frame r hr
    · exact hS.prm
  · have h1 := sb_read_NextTag hu
    have h2 := sb_read_NextTag hu'
    simp only [PermissionModel.stackedBorrows] at h1 h2
    show TagRenameBounded ρt permsR'.NextTag pT'.NextTag
    rw [h1, h2, hS.srcNT]
    exact TagRenameBounded.mono h_tbd (Nat.le_refl _) hS.tgtNT
  · show s1.pc + 1 = _
    rw [hS.pc]; rfl
  · exact StoreStepB.rstore compProg _ _ dstL _ vals (RegMap.lookup_insert_self _ _ _)
      (show _ < _ + 1 by omega)

/-- `x := copy src`, `x` a bound local, `src` any pointer chain. -/
theorem copy_chain_local_sim {Γ : Ctx} {L : mirlite.LayEnv Γ} {ρt : TagRenameMap}
    {s_mir s_mir' : mirlite.State MSB Γ} {s_osea : oseair.State MSB}
    {τ : LayoutTy} {loc : Local Γ τ} {src : Place Γ τ} {b : Binding} {cs : CompilerState}
    (compProg : oseair.Prog) (hWF : PtrPlacesWF L) (h_chain : PtrChain src)
    (h_inv : InvAtB L ρt s_mir s_osea cs)
    (h_code : CodeIncludedB compProg
      (CheckedCompilerM.run (compileStmtChecked L (.assign (.local loc) (.copy src))) cs))
    (h_env : s_mir.env.lookup loc = some b)
    (h_step : mirlite.stepStmt MSB L s_mir (.assign (.local loc) (.copy src)) = .ok s_mir') :
    ∃ (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = .Ok s_osea' ∧
      InvAtB L ρt' s_mir' s_osea'
        (CheckedCompilerM.run (compileStmtChecked L (.assign (.local loc) (.copy src))) cs) :=
  storereg_local_simB compProg (copy_chain_pkg hWF _ h_chain) h_inv h_code h_env h_step

/-- `*P := copy src`: a pointer-chain destination, a pointer-chain source. -/
theorem copy_chain_chaindst_sim {Γ : Ctx} {L : mirlite.LayEnv Γ} {ρt : TagRenameMap}
    {s_mir s_mir' : mirlite.State MSB Γ} {s_osea : oseair.State MSB}
    {τ : LayoutTy} {P : Place Γ (LayoutTy.PtrL τ)} {src : Place Γ τ} {cs : CompilerState}
    (compProg : oseair.Prog) (hWF : PtrPlacesWF L)
    (h_dchain : PtrChain (.deref P)) (h_schain : PtrChain src)
    (h_inv : InvAtB L ρt s_mir s_osea cs)
    (h_code : CodeIncludedB compProg
      (CheckedCompilerM.run (compileStmtChecked L (.assign (.deref P) (.copy src))) cs))
    (h_step : mirlite.stepStmt MSB L s_mir (.assign (.deref P) (.copy src)) = .ok s_mir') :
    ∃ (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = .Ok s_osea' ∧
      InvAtB L ρt' s_mir' s_osea'
        (CheckedCompilerM.run (compileStmtChecked L (.assign (.deref P) (.copy src))) cs) :=
  storereg_chaindst_simB compProg hWF h_dchain (copy_chain_pkg hWF _ h_schain) h_inv h_code h_step

end obseq3.proof
