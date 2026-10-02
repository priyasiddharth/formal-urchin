import obseq3.byteproof.places

/-!
# Destination: a pointer chain

`*p := rhs`, `*(*p).f := rhs`, …: any destination that is a deref of a
pointer chain (`proof.PtrChain (.deref P)`), for any rvalue with a value
package. The byte analogue of the cell proof's
`storereg_chaindst_simulation`: the rvalue's code first (MIR's order),
then the destination's lowering (`ptrChain_lowering_simB`, at the
post-rvalue states), then the store through the lowered register.
-/

namespace obseq3.byteproof

open obseq3 obseq3.bytes obseq3.proof
open obseq3.mirlite (MemValue Binding Env PlaceRes)
open obseq3.oseair (Val Register)
open obseq3.compileB

/-! ## The compiled shape -/

/-- A destination the source resolves has a mapped root, so
    `ensurePlaceRoot` emits nothing. -/
theorem ensurePlaceRoot_noop {Γ : Ctx} {L : mirliteB.LayEnv Γ} {M : PermissionModel}
    {s : mirliteB.State M Γ} {cs : CompilerState}
    (h_map : ∀ {τ : LayoutTy} (loc : Local Γ τ) (b : Binding), s.env.lookup loc = some b →
      ∃ reg layout, getPlaceInfo cs loc.idx.1 = some (reg, layout)) :
    ∀ {τ : LayoutTy} (p : Place Γ τ) (r : PlaceRes),
      mirliteB.resolvePlace? M L s p = some r →
      CompilerM.run (ensurePlaceRoot L p) cs = cs := by
  intro τ p
  induction p with
  | «local» loc =>
      intro r h
      cases h_env : s.env.lookup loc with
      | none => simp [mirliteB.resolvePlace?, h_env] at h
      | some b =>
          obtain ⟨reg, layout, h_pi⟩ := h_map loc b h_env
          simp only [ensurePlaceRoot, CompilerM.run_bind, CompilerM.run_pure,
            ensureLocalRegE_existing (L := L) h_pi]
  | proj base path ih =>
      intro r h
      simp only [mirliteB.resolvePlace?] at h
      split at h
      · cases h
      · rename_i r' h'
        exact ih _ h'
  | deref q ih =>
      intro r h
      simp only [mirliteB.resolvePlace?] at h
      split at h
      · cases h
      · rename_i r' h'
        exact ih _ h'

/-- The destination's lowering only grows into the statement's run. -/
theorem assign_dst_incr {Γ : Ctx} {L : mirliteB.LayEnv Γ} {τ : LayoutTy}
    {dst : Place Γ τ} {rhs : RExpr Γ τ} {cs : CompilerState} {pOut : RhsPre L τ rhs}
    (h_root : CompilerM.run (ensurePlaceRoot L dst) cs = cs)
    (h_pval : CheckedCompilerM.value (compileRExprPreChecked L (mirliteB.placeLayout L dst) rhs) cs
      = .ok pOut) :
    StateIncr
      (CheckedCompilerM.run (placeToRegChecked L RefKind.Mut dst)
        (CheckedCompilerM.run (compileRExprPreChecked L (mirliteB.placeLayout L dst) rhs) cs))
      (CheckedCompilerM.run (compileStmtChecked L (.assign dst rhs)) cs) := by
  simp only [compileStmtChecked, compileAssignChecked, CheckedCompilerM.run_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift, h_root, h_pval]
  split
  · simp only [CheckedCompilerM.run_pure]
    exact ((emit_state_incr _ _).trans (emit_state_incr _ _)).trans (emit_state_incr _ _)
  · exact StateIncr.refl _

/-- `dst := rhs` for a destination whose lowering leaves no cleanup: the
    rvalue's code, the destination's, then the one store. -/
theorem compileStmt_storereg_dst {Γ : Ctx} {L : mirliteB.LayEnv Γ} {τ : LayoutTy}
    {dst : Place Γ τ} {rhs : RExpr Γ τ} {cs : CompilerState} {pOut : RhsPre L τ rhs}
    {mkStore : Register → oseairL.Instr}
    {dOut : ResultWithEvidence PtrResult (PlaceToRegEvidence L RefKind.Mut dst)}
    (h_root : CompilerM.run (ensurePlaceRoot L dst) cs = cs)
    (h_pval : CheckedCompilerM.value (compileRExprPreChecked L (mirliteB.placeLayout L dst) rhs) cs
      = .ok pOut)
    (h_store : ∀ d, pOut.store d = [mkStore d]) (h_post : pOut.postCleanup = [])
    (h_dval : CheckedCompilerM.value (placeToRegChecked L RefKind.Mut dst)
      (CheckedCompilerM.run (compileRExprPreChecked L (mirliteB.placeLayout L dst) rhs) cs)
      = .ok dOut)
    (h_dclean : dOut.result.cleanup = []) :
    CheckedCompilerM.run (compileStmtChecked L (.assign dst rhs)) cs
      = emit (CheckedCompilerM.run (placeToRegChecked L RefKind.Mut dst)
          (CheckedCompilerM.run (compileRExprPreChecked L (mirliteB.placeLayout L dst) rhs) cs))
          [mkStore dOut.result.reg] := by
  simp only [compileStmtChecked, compileAssignChecked, CheckedCompilerM.run_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, h_root, h_pval, h_dval, h_store, h_post, h_dclean]
  simp only [CompilerM.run, emitM, cleanupInstrs, List.reverse_nil, List.map_nil, emit_nil]

/-! ## The leaf -/

theorem LocalBindingSimB.prm_congr {Γ : Ctx} {L : mirliteB.LayEnv Γ} {ρt : TagRenameMap}
    {env : Env Γ} {s : oseairL.State MSB} {cs cs' : CompilerState}
    (h : LocalBindingSimB L ρt env s cs) (h_prm : cs'.placeRegMap = cs.placeRegMap) :
    LocalBindingSimB L ρt env s cs' := by
  intro τ loc b h_env
  obtain ⟨r, t, hpi, he, hrt, hnw⟩ := h loc b h_env
  refine ⟨r, t, ?_, he, hrt, hnw⟩
  show List.lookup _ _ = _
  rw [h_prm]; exact hpi

/-- The place-lowering contract: from any related states at which the
    source resolves `p`, the compiled lowering of `p` delivers `LoweredB`.
    Pointer chains meet it (`ptrChain_lowering_simB`), and so does a field
    of one at byte offset zero. -/
def LowersB {Γ : Ctx} (L : mirliteB.LayEnv Γ) (compProg : oseairL.Prog) {τ : LayoutTy}
    (p : Place Γ τ) : Prop :=
  ∀ (ρt : TagRenameMap) (sM : mirliteB.State MSB Γ) (kind : RefKind) (cs : CompilerState)
    (sA : oseairL.State MSB) (resolved : PlaceRes) (permsD : MSB.State),
    TagRenameWF ρt →
    mirliteB.resolvePlaceAcc MSB L sM p = .ok (resolved, permsD) →
    TagRenameBounded ρt sM.perms.NextTag sA.perms.NextTag →
    LocalBindingSimB L ρt sM.env sA cs →
    PlaceRegMapBoundB cs →
    ByteMemSim ρt sM.mem sA.mem →
    ByteAllocLockstep sM.mem sA.mem →
    PermSim ρt sM.perms sA.perms →
    sA.pc = cs.nextLabel →
    CodeIncludedB compProg (CheckedCompilerM.run (placeToRegChecked L kind p) cs) →
    ∃ placeOut n s' tres, LoweredB L ρt compProg kind p cs sM sA resolved permsD
      placeOut n s' tres

theorem ptrChain_lowers {Γ : Ctx} {L : mirliteB.LayEnv Γ} {compProg : oseairL.Prog}
    (hWF : PtrPlacesWF L) {τ : LayoutTy} {p : Place Γ τ} (h_chain : PtrChain p) :
    LowersB L compProg p :=
  fun _ _ kind cs sA resolved permsD hwf h_res =>
    ptrChain_lowering_simB hWF hwf h_chain kind cs sA resolved permsD h_res

/-- The destination leaf for ANY place whose lowering meets the
    place-lowering contract (`LowersB`) and whose assignment never
    allocates (`h_prepOK`), for any rvalue with a value package. -/
theorem storereg_lowered_simB {Γ : Ctx} {L : mirliteB.LayEnv Γ} {ρt : TagRenameMap}
    {s_mir s_mir' : mirliteB.State MSB Γ} {s_osea : oseairL.State MSB}
    {τ : LayoutTy} {dst : Place Γ τ} {rhs : RExpr Γ τ} {cs : CompilerState}
    (compProg : oseairL.Prog)
    (h_low : LowersB L compProg dst)
    (h_prepOK : ∀ s1, mirliteB.preparePlaceAssign MSB L s_mir dst = .ok s1 →
      s1 = s_mir ∧ ∃ r, mirliteB.resolvePlace? MSB L s_mir dst = some r)
    (h_pkg : ValuePkgB compProg L (mirliteB.placeLayout L dst) rhs)
    (h_inv : InvAtB L ρt s_mir s_osea cs)
    (h_code : CodeIncludedB compProg
      (CheckedCompilerM.run (compileStmtChecked L (.assign dst rhs)) cs))
    (h_step : mirliteB.stepStmt MSB L s_mir (.assign dst rhs) = .ok s_mir') :
    ∃ (ρt' : TagRenameMap) (s_osea' : oseairL.State MSB) (n : Nat),
      TagRenameIncr ρt ρt' ∧
      oseairL.runN MSB n s_osea compProg = .Ok s_osea' ∧
      InvAtB L ρt' s_mir' s_osea'
        (CheckedCompilerM.run (compileStmtChecked L (.assign dst rhs)) cs) := by
  -- §1 the source: the destination exists (a deref root is never allocated)
  simp only [mirliteB.stepStmt, mirliteB.doAssign] at h_step
  cases h_prep : mirliteB.preparePlaceAssign MSB L s_mir dst with
  | err msg => rw [h_prep] at h_step; cases h_step
  | ok s1 =>
  rw [h_prep] at h_step
  obtain ⟨rfl, rp, h_rp⟩ := h_prepOK s1 h_prep
  simp only at h_step
  split at h_step
  · cases h_step
  rename_i output h_eval
  -- §2 the rvalue, behind its package
  obtain ⟨mkStore, pOut, h_pval, h_storeR, h_postR, h_prmR, h_pkg'⟩ :=
    h_pkg ρt s1 s_osea cs h_inv.wf_t h_inv.tbd h_inv.lbs h_inv.prb h_inv.mem
      h_inv.alloc h_inv.psim h_inv.pc output h_eval
  -- the destination's access resolution, on the state the rvalue left
  split at h_step
  · cases h_step
  rename_i resolved permsD h_dres
  have h_root : CompilerM.run (ensurePlaceRoot L dst) cs = cs := by
    refine ensurePlaceRoot_noop (s := s1) (fun loc b h => ?_) _ _ h_rp
    obtain ⟨r, t, hpi, -⟩ := h_inv.lbs loc b h
    exact ⟨r, _, hpi⟩
  -- §3 code inclusion, from the statement's down to the rvalue's
  have h_codeD := h_code.mono (assign_dst_incr (rhs := rhs) h_root h_pval)
  have h_codePre := h_codeD.mono (CheckedCompilerM.incr (placeToRegChecked L RefKind.Mut dst)
    (CheckedCompilerM.run (compileRExprPreChecked L (mirliteB.placeLayout L dst) rhs) cs))
  obtain ⟨ρt', nR, sR, memO, perms₂, vals, h_incr_t, h_wf_t', h_ost, h_runR, h_regmono,
    h_lbsR, h_psimR, h_tbdR, h_memR, h_allocR, h_pcR, h_exec, h_valsRel⟩ := h_pkg' h_codePre
  rw [h_ost] at h_dres h_step
  have h_prbR : PlaceRegMapBoundB
      (CheckedCompilerM.run (compileRExprPreChecked L (mirliteB.placeLayout L dst) rhs) cs) :=
    fun idx r τ' h' => RegisterBelow.mono h_regmono (h_inv.prb idx r τ' (by
      show List.lookup _ _ = _
      rw [← h_prmR]; exact h'))
  -- §4 the destination's lowering, at the post-rvalue states
  obtain ⟨dOut, n2, s2, tres, hD⟩ :=
    h_low ρt' { s1 with mem := memO, perms := perms₂ } RefKind.Mut _ sR resolved permsD h_wf_t'
      h_dres h_tbdR h_lbsR h_prbR h_memR h_allocR h_psimR h_pcR h_codeD
  have h_shape := compileStmt_storereg_dst h_root h_pval h_storeR h_postR hD.val hD.clean
  rw [h_shape] at h_code ⊢
  -- §5 the store, on both sides
  simp only [mirliteB.writeResolvedPlace] at h_step
  split at h_step
  · cases h_step
  rename_i h_free
  split at h_step
  · cases h_step
  rename_i h_bnd
  split at h_step
  case h_2 => cases h_step
  rename_i permsW hu
  split at h_step
  case h_2 => cases h_step
  rename_i memW hw
  simp only [mirliteB.Result.ok.injEq] at h_step
  subst h_step
  obtain ⟨ext, h_dentry⟩ := hD.entry
  have hA : resolved.allocBase + (resolved.addr - resolved.allocBase) = resolved.addr :=
    Nat.add_sub_cancel' hD.le
  have h_mem2 : ByteMemSim ρt' memO s2.mem := by rw [hD.mem]; exact h_memR
  have h_lock2 : ByteAllocLockstep memO s2.mem := by rw [hD.mem]; exact h_allocR
  obtain ⟨pT', mT', hu', hw', hp', hm'⟩ :=
    store_step_sim h_wf_t' hD.psim h_mem2 hD.rt h_valsRel hu hw
  have h_freeT : s2.mem.isFreed resolved.allocBase = false := by
    simp only [bytes.Mem.isFreed, ← h_lock2.2.2] at h_free ⊢
    simpa using h_free
  have h_wtp : oseairL.writeThroughPtr MSB s2 dOut.result.reg
      (mirliteB.placeLayout L dst) vals "store"
      = .Ok { s2 with perms := pT', mem := mT', pc := s2.pc + 1 } := by
    simp only [PermissionModel.stackedBorrows] at hu'
    simp only [oseairL.writeThroughPtr, h_dentry, hA, h_freeT, Bool.false_eq_true, if_false,
      h_bnd, PermissionModel.stackedBorrows, hu', hw']
  have h_instr : compProg s2.pc = some (mkStore dOut.result.reg) := by
    rw [hD.pc]
    apply h_code
    · simp [emit]
    · simp [emit]
  have h_run1 := h_exec s2 _ dOut.result.reg hD.frame h_instr h_wtp
  refine ⟨ρt', _, nR + n2 + 1, h_incr_t, runN_trans (runN_trans h_runR hD.run) h_run1, ?_⟩
  obtain ⟨bufS, rfl⟩ := writeL_eq_write hw
  obtain ⟨bufT, rfl⟩ := writeL_eq_write hw'
  exact {
    pc := by simp [emit, hD.pc]
    lbs := LocalBindingSimB.prm_congr (h_lbsR.of_frame h_prbR hD.frame) hD.prm
    mem := hm'
    alloc := h_lock2.write _ _ _ _
    psim := hp'
    wf_t := h_wf_t'
    tbd := by
      have h1 := sb_write_NextTag hu
      have h2 := sb_write_NextTag hu'
      simp only [PermissionModel.stackedBorrows] at h1 h2
      show TagRenameBounded ρt' permsW.NextTag pT'.NextTag
      rw [h1, h2, hD.srcNT]
      exact TagRenameBounded.mono h_tbdR (Nat.le_refl _) hD.tgtNT
    unmap := fun loc' h' => by
      have : getPlaceInfo
          (CheckedCompilerM.run (placeToRegChecked L RefKind.Mut dst)
            (CheckedCompilerM.run (compileRExprPreChecked L (mirliteB.placeLayout L dst) rhs) cs))
          loc'.idx.1 = none := by
        show List.lookup _ _ = _
        rw [hD.prm, h_prmR]; exact h_inv.unmap loc' h'
      exact this
    prb := fun idx r τ' h' => by
      have : getPlaceInfo cs idx = some (r, τ') := by
        show List.lookup _ _ = _
        rw [← h_prmR, ← hD.prm]; exact h'
      exact RegisterBelow.mono (Nat.le_trans h_regmono hD.regmono) (h_inv.prb idx r τ' this)
  }

/-- The pointer-chain destination leaf (`proof/spine.lean`'s
    `storereg_chaindst_simulation`). -/
theorem storereg_chaindst_simB {Γ : Ctx} {L : mirliteB.LayEnv Γ} {ρt : TagRenameMap}
    {s_mir s_mir' : mirliteB.State MSB Γ} {s_osea : oseairL.State MSB}
    {τ : LayoutTy} {P : Place Γ (obseq.LayoutTy.PtrL τ)} {rhs : RExpr Γ τ} {cs : CompilerState}
    (compProg : oseairL.Prog) (hWF : PtrPlacesWF L)
    (h_chain : PtrChain (.deref P))
    (h_pkg : ValuePkgB compProg L (mirliteB.placeLayout L (.deref P)) rhs)
    (h_inv : InvAtB L ρt s_mir s_osea cs)
    (h_code : CodeIncludedB compProg
      (CheckedCompilerM.run (compileStmtChecked L (.assign (.deref P) rhs)) cs))
    (h_step : mirliteB.stepStmt MSB L s_mir (.assign (.deref P) rhs) = .ok s_mir') :
    ∃ (ρt' : TagRenameMap) (s_osea' : oseairL.State MSB) (n : Nat),
      TagRenameIncr ρt ρt' ∧
      oseairL.runN MSB n s_osea compProg = .Ok s_osea' ∧
      InvAtB L ρt' s_mir' s_osea'
        (CheckedCompilerM.run (compileStmtChecked L (.assign (.deref P) rhs)) cs) :=
  storereg_lowered_simB compProg (ptrChain_lowers hWF h_chain)
    (fun s1 h_prep => by
      simp only [mirliteB.preparePlaceAssign] at h_prep
      split at h_prep
      · rename_i r h_r
        exact ⟨(mirliteB.Result.ok.inj h_prep).symm, r, h_r⟩
      · simp [mirliteB.allocateRoot] at h_prep)
    h_pkg h_inv h_code h_step

end obseq3.byteproof
