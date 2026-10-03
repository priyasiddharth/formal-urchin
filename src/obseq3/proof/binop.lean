import obseq3.proof.readsrc

/-!
# Arithmetic: the `binOp` package

`dst := a op b`: two copy-reads into registers (`readToReg_simB`, chained
through the invariant), then a register-only `BinOp` — no memory and no
permission event, with the same wrapping, flags and UB (`binOpUB`) on
both sides, since both machines call the same `evalBinOp`.
-/

namespace obseq3.proof

open obseq3 obseq3.bytes obseq3.proof
open obseq3.mirlite (MemValue Binding Env PlaceRes)
open obseq3.oseair (Val Register)
open obseq3.compile

theorem evalCopy_state {Γ : Ctx} {L : mirlite.LayEnv Γ} {sM : mirlite.State MSB Γ}
    {σ : LayoutTy} {p : Place Γ σ} {out : mirlite.EvalOutput MSB Γ}
    (h : mirlite.evalCopy MSB L sM p = .ok out) :
    out.state = { sM with perms := out.state.perms } := by
  simp only [mirlite.evalCopy] at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  · simp only [mirlite.EvalResult.ok.injEq] at h
    subst h
    rfl

theorem word_of_storeSim {ρt : TagRenameMap} {x : Nat} {vals : List Val}
    (h : ListRel (StoreSim ρt) [MemValue.word x] (vals.map oseair.Val.toMem)) :
    vals = [Val.Dat x] := by
  match vals, h with
  | [w], ⟨hs, _⟩ =>
      rcases hs with ⟨h1, -⟩ | ⟨-, hv⟩
      · cases h1
      · cases w with
        | Undef => simp [ValSim, MemValSim, oseair.Val.toMem, oseair.ofMem] at hv
        | Dat x' =>
            simp only [ValSim, MemValSim, oseair.Val.toMem, oseair.ofMem] at hv
            rw [hv]
        | Ptr _ _ _ _ _ => simp [ValSim, MemValSim, oseair.Val.toMem, oseair.ofMem] at hv
  | [], h => exact h.elim
  | _ :: _ :: _, ⟨_, h⟩ => exact h.elim

theorem binOp_pkg {Γ : Ctx} {L : mirlite.LayEnv Γ} {compProg : oseair.Prog}
    (hWF : PtrPlacesWF L) (dstL : BLayout) (op : BinOp)
    {ta tb tr : IntTy} {a : Place Γ (LayoutTy.IntL ta)} {b : Place Γ (LayoutTy.IntL tb)} (h_ca : ReadSrcB a) (h_cb : ReadSrcB b) :
    ValuePkgB compProg L dstL (RExpr.binOp (tr := tr) op a b) := by
  intro ρt sM sA csA h_wf h_tbd h_lbs h_prb h_mem h_alloc h_psim h_pc h_unmap output h_ev
  have h_inv0 : InvAtB L ρt sM sA csA := ⟨h_pc, h_lbs, h_mem, h_alloc, h_psim, h_wf, h_tbd,
    h_unmap, h_prb⟩
  -- the source: two reads, the operation
  simp only [mirlite.evalRExpr] at h_ev
  split at h_ev
  · cases h_ev
  rename_i out1 h_e1
  split at h_ev
  case h_2 => cases h_ev
  rename_i x h_x
  split at h_ev
  · cases h_ev
  rename_i out2 h_e2
  split at h_ev
  case h_2 => cases h_ev
  rename_i y h_y
  split at h_ev
  · cases h_ev
  rename_i h_ub
  simp only [mirlite.EvalResult.ok.injEq] at h_ev
  subst h_ev
  have h_st1 := evalCopy_state h_e1
  have h_st2 := evalCopy_state h_e2
  -- compile-time: both reads lower
  obtain ⟨h_valA, h_prmA, h_nrA⟩ := readToReg_factsR h_ca h_lbs h_e1
  have h_lbs1 : LocalBindingSimB L ρt out1.state.env sA (CheckedCompilerM.run (readToReg L a) csA) := by
    rw [h_st1]; exact LocalBindingSimB.prm_congr h_lbs h_prmA
  obtain ⟨h_valB, h_prmB0, -⟩ := readToReg_factsR h_cb h_lbs1 h_e2
  have h_prmB : (CheckedCompilerM.run (readToReg L b) (CheckedCompilerM.run (readToReg L a) csA)).placeRegMap
      = csA.placeRegMap := h_prmB0.trans h_prmA
  -- the rvalue's shape
  have h_pre : CheckedCompilerM.run (compileRExprPreChecked L dstL (RExpr.binOp (tr := tr) op a b)) csA
      = emit (bumpReg (CheckedCompilerM.run (readToReg L b) (CheckedCompilerM.run (readToReg L a) csA)))
          [oseair.Instr.Assgn
            (Register.R (CheckedCompilerM.run (readToReg L b)
              (CheckedCompilerM.run (readToReg L a) csA)).nextReg)
            (oseair.Rhs.BinOp op
              (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared a) csA).nextReg)
              (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared b)
                (CheckedCompilerM.run (readToReg L a) csA)).nextReg))] := by
    simp only [compileRExprPreChecked, CheckedCompilerM.run_bind,
      h_valA, h_valB, CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
      CheckedCompilerM.run_pure]
    rfl
  have h_preV : ∃ pOut, CheckedCompilerM.value
      (compileRExprPreChecked L dstL (RExpr.binOp (tr := tr) op a b)) csA = .ok pOut ∧
      (∀ d, pOut.store d = [oseair.Instr.RStore dstL
        (Register.R (CheckedCompilerM.run (readToReg L b)
          (CheckedCompilerM.run (readToReg L a) csA)).nextReg) d]) ∧
      pOut.postCleanup = [] := by
    simp only [compileRExprPreChecked, CheckedCompilerM.value_bind,
      h_valA, h_valB, CheckedCompilerM.value_lift, CheckedCompilerM.run_lift,
      CheckedCompilerM.value_pure]
    exact ⟨_, rfl, fun _ => rfl, rfl⟩
  obtain ⟨pOut, h_pval, h_store, h_post⟩ := h_preV
  refine ⟨_, pOut, h_pval, h_store, h_post, by rw [h_pre]; exact h_prmB, fun h_code => ?_⟩
  rw [h_pre] at h_code ⊢
  -- the two reads, chained
  have h_incrB := CheckedCompilerM.incr (readToReg L b) (CheckedCompilerM.run (readToReg L a) csA)
  have h_codeB : CodeIncludedB compProg
      (CheckedCompilerM.run (readToReg L b) (CheckedCompilerM.run (readToReg L a) csA)) :=
    h_code.mono ((bumpReg_state_incr' _).trans (emit_state_incr _ _))
  obtain ⟨n1, s1, vals1, h_run1, h_inv1, -, h_r1, -, h_rel1, h_rm1, -⟩ :=
    readToReg_simR hWF h_ca h_inv0 h_e1 (h_codeB.mono h_incrB)
  obtain ⟨n2, s2, vals2, h_run2, h_inv2, -, h_r2, -, h_rel2, -, h_fr2⟩ :=
    readToReg_simR hWF h_cb h_inv1 h_e2 h_codeB
  rw [h_x] at h_rel1
  rw [h_y] at h_rel2
  have hv1 := word_of_storeSim h_rel1
  have hv2 := word_of_storeSim h_rel2
  subst hv1 hv2
  have h_r1' : s2.reg.lookup
      (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared a) csA).nextReg)
      = some [Val.Dat x] := by
    rw [h_fr2 _ (by show _ < _; rw [h_nrA]; omega)]
    exact h_r1
  -- the operation
  have h_instr : compProg s2.pc = some (oseair.Instr.Assgn
      (Register.R (CheckedCompilerM.run (readToReg L b)
        (CheckedCompilerM.run (readToReg L a) csA)).nextReg)
      (oseair.Rhs.BinOp op
        (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared a) csA).nextReg)
        (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared b)
          (CheckedCompilerM.run (readToReg L a) csA)).nextReg))) := by
    rw [h_inv2.pc]
    apply h_code
    · simp [emit]
    · simp [emit]
  have h_ev3 : oseair.evalRhs MSB s2 (oseair.Rhs.BinOp op
        (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared a) csA).nextReg)
        (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared b)
          (CheckedCompilerM.run (readToReg L a) csA)).nextReg))
      = .Ok [Val.Dat (evalBinOp op x y)] s2 := by
    simp only [oseair.evalRhs, h_r1', h_r2, h_ub]
  have h_run3 := runN_Assgn h_instr h_ev3
  rw [h_st2, h_st1] at h_inv2
  simp only at h_inv2
  refine ⟨ρt, n1 + n2 + 1, _, sM.mem, out2.state.perms, [Val.Dat (evalBinOp op x y)],
    TagRenameIncr.refl ρt, h_wf, by rw [h_st2, h_st1], runN_trans (runN_trans h_run1 h_run2) h_run3,
    ?_, ?_, h_inv2.psim, h_inv2.tbd, h_inv2.mem, h_inv2.alloc, ?_, ?_,
    ⟨Or.inr ⟨by simp, rfl⟩, trivial⟩⟩
  · show csA.nextReg ≤ _ + 1
    have := h_incrB.nextReg_le
    have h_a := (CheckedCompilerM.incr (readToReg L a) csA).nextReg_le
    omega
  · refine LocalBindingSimB.prm_congr (LocalBindingSimB.of_frame h_inv2.lbs h_inv2.prb
      fun r hr => ?_) rfl
    have hne := RegisterBelow.ne_fresh hr
    exact RegMap.lookup_insert_ne _ _ hne
  · show s2.pc + 1 = _
    rw [h_inv2.pc]; rfl
  · exact StoreStepB.rstore compProg _ _ dstL _ _ (RegMap.lookup_insert_self _ _ _)
      (show _ < _ + 1 by omega)

end obseq3.proof
