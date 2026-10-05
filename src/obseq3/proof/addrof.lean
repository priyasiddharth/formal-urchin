import obseq3.proof.slice

/-!
# `addrOf`: a pointer to a local's place, with the local's own tag

`dst := addrOf(loc.path)`: the source builds the pointer from the local's
binding (its base and owning tag), the field's offset and size — no memory
or permission event. The compiled code moves the local's own pointer
register (`PlaceAddr`), which holds the same base and size with the
renamed tag (`LocalBindingSimB`): no borrow, so no route tag. The value
pair is related by that renaming.
-/

namespace obseq3.proof

open obseq3 obseq3.bytes obseq3.proof
open obseq3.mirlite (MemValue Binding Env PlaceRes)
open obseq3.oseair (Val Register)
open obseq3.compile

theorem addrOf_pkg {Γ : Ctx} {L : mirlite.LayEnv Γ} {compProg : oseair.Prog}
    (dstL : BLayout) {σ τ : LayoutTy} (loc : Local Γ σ) (path : PathTo σ τ) :
    ValuePkgB compProg L dstL (RExpr.addrOf loc path) := by
  intro ρt sM sA csA h_wf h_tbd h_lbs h_prb h_mem h_alloc h_psim h_pc h_unmap output h_ev
  -- the source: the binding, no event
  simp only [mirlite.evalRExpr] at h_ev
  split at h_ev
  · cases h_ev
  rename_i b h_b
  simp only [mirlite.EvalResult.ok.injEq] at h_ev
  subst h_ev
  obtain ⟨reg, tagT, h_pi, ⟨ext, h_reg⟩, h_tag, -⟩ := h_lbs loc b h_b
  obtain ⟨h_run0, placeOut, h_val0, h_res0⟩ :=
    placeToRegChecked_local_existing (L := L) (kind := RefKind.Shared) h_pi
  -- the rvalue's shape
  have h_pre : CheckedCompilerM.run (compileRExprPreChecked L dstL (RExpr.addrOf loc path)) csA
      = emit (bumpReg csA)
          [oseair.Instr.Assgn (Register.R csA.nextReg)
            (oseair.Rhs.PlaceAddr reg (pathOffsetB L (.local loc) path)
              (placeSizeB L (.proj (.local loc) path)))] := by
    simp only [compileRExprPreChecked, CheckedCompilerM.run_bind, h_val0, h_run0, h_res0,
      CheckedCompilerM.run_lift, CheckedCompilerM.value_lift, CheckedCompilerM.run_pure]
    rfl
  have h_preV : ∃ pOut, CheckedCompilerM.value
      (compileRExprPreChecked L dstL (RExpr.addrOf loc path)) csA = .ok pOut ∧
      (∀ d, pOut.store d = [oseair.Instr.RStore dstL (Register.R csA.nextReg) d]) ∧
      pOut.postCleanup = [] := by
    simp only [compileRExprPreChecked, CheckedCompilerM.value_bind, h_val0, h_run0,
      CheckedCompilerM.value_lift, CheckedCompilerM.run_lift, CheckedCompilerM.value_pure]
    exact ⟨_, rfl, fun _ => rfl, rfl⟩
  obtain ⟨pOut, h_pval, h_store, h_post⟩ := h_preV
  refine ⟨_, pOut, h_pval, h_store, h_post, by rw [h_pre]; rfl, fun h_code => ?_⟩
  rw [h_pre] at h_code ⊢
  have h_instr : compProg sA.pc = some (oseair.Instr.Assgn (Register.R csA.nextReg)
      (oseair.Rhs.PlaceAddr reg (pathOffsetB L (.local loc) path)
        (placeSizeB L (.proj (.local loc) path)))) := by
    rw [h_pc]
    apply h_code
    · simp [emit]
    · simp [emit]
  have h_run := runN_Assgn (vals := [Val.Ptr b.addr (0 + pathOffsetB L (.local loc) path)
      (placeSizeB L (.proj (.local loc) path)) (L loc.idx).sizeB tagT]) (s' := sA) h_instr
    (by simp only [oseair.evalRhs, h_reg])
  refine ⟨ρt, 1, _, sM.mem, sM.perms, [Val.Ptr b.addr (0 + pathOffsetB L (.local loc) path)
      (placeSizeB L (.proj (.local loc) path)) (L loc.idx).sizeB tagT],
    TagRenameIncr.refl ρt, h_wf, rfl, h_run,
    ?_, ?_, h_psim, h_tbd, h_mem, h_alloc, ?_, ?_, ?_⟩
  · show csA.nextReg ≤ csA.nextReg + 1
    omega
  · refine LocalBindingSimB.prm_congr (LocalBindingSimB.of_frame h_lbs h_prb
      fun r hr => ?_) rfl
    exact RegMap.lookup_insert_ne _ _ (RegisterBelow.ne_fresh hr)
  · show sA.pc + 1 = _
    rw [h_pc]; rfl
  · exact StoreStepB.rstore compProg _ _ dstL _ _ (RegMap.lookup_insert_self _ _ _)
      (show _ < _ + 1 by omega)
  · refine ⟨Or.inr ⟨by simp, ?_⟩, trivial⟩
    simp only [ValSim, oseair.Val.toMem, oseair.ofMem, MemValSim, idA, Nat.zero_add,
      pathOffsetB, placeSizeB]
    exact ⟨trivial, trivial, trivial, trivial, h_tag, fun _ _ => ⟨_, rfl⟩⟩

end obseq3.proof
