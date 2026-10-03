import obseq3.byteproof.binop

/-!
# Slice metadata: `sliceLen`, `subSlice`

The `binOp` pattern with a pointer operand: copy-reads into registers
(`readToReg_simB`, chained), then a register-only `SliceLen` /
`SubSlice` computing the same extent arithmetic, in bytes, on both sides.
-/

namespace obseq3.byteproof

open obseq3 obseq3.bytes obseq3.proof
open obseq3.mirlite (MemValue Binding Env PlaceRes)
open obseq3.oseair (Val Register)
open obseq3.compileB

theorem ptr_of_storeSim {ρt : TagRenameMap} {b o e sz : Nat} {t : Tag} {vals : List Val}
    (h : ListRel (StoreSim ρt) [MemValue.ptrVal b o e sz t] (vals.map oseair.Val.toMem)) :
    ∃ t', vals = [Val.Ptr b o e sz t'] ∧ ρt t = some t' := by
  match vals, h with
  | [w], ⟨hs, _⟩ =>
      rcases hs with ⟨h1, -⟩ | ⟨-, hv⟩
      · cases h1
      · cases w with
        | Undef => simp [ValSim, MemValSim, oseair.Val.toMem, oseair.ofMem] at hv
        | Dat _ => simp [ValSim, MemValSim, oseair.Val.toMem, oseair.ofMem] at hv
        | Ptr b' o' e' s' t' =>
            simp only [ValSim, MemValSim, oseair.Val.toMem, oseair.ofMem, idA,
              Option.some.injEq] at hv
            obtain ⟨rfl, rfl, rfl, rfl, ht, -⟩ := hv
            exact ⟨t', rfl, ht⟩
  | [], h => exact h.elim
  | _ :: _ :: _, ⟨_, h⟩ => exact h.elim

theorem sliceLen_pkg {Γ : Ctx} {L : mirliteB.LayEnv Γ} {compProg : oseairL.Prog}
    (hWF : PtrPlacesWF L) (dstL : BLayout) {σ : LayoutTy}
    {src : Place Γ (LayoutTy.PtrL σ)} (h_c : ReadSrcB src) :
    ValuePkgB compProg L dstL (RExpr.sliceLen (t := tE) src) := by
  intro ρt sM sA csA h_wf h_tbd h_lbs h_prb h_mem h_alloc h_psim h_pc h_unmap output h_ev
  have h_inv0 : InvAtB L ρt sM sA csA := ⟨h_pc, h_lbs, h_mem, h_alloc, h_psim, h_wf, h_tbd,
    h_unmap, h_prb⟩
  simp only [mirliteB.evalRExpr] at h_ev
  split at h_ev
  · cases h_ev
  rename_i out1 h_e1
  split at h_ev
  case h_2 => cases h_ev
  rename_i pb po pe ps pt h_p
  simp only [mirliteB.EvalResult.ok.injEq] at h_ev
  subst h_ev
  have h_st1 := evalCopy_state h_e1
  obtain ⟨h_valA, h_prmA, -⟩ := readToReg_factsR h_c h_lbs h_e1
  have h_pre : CheckedCompilerM.run (compileRExprPreChecked L dstL (RExpr.sliceLen (t := tE) src)) csA
      = emit (bumpReg (CheckedCompilerM.run (readToReg L src) csA))
          [oseairL.Instr.Assgn (Register.R (CheckedCompilerM.run (readToReg L src) csA).nextReg)
            (oseairL.Rhs.SliceLen (mirliteB.pointeeLayout L src).size
              (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared src) csA).nextReg))] := by
    simp only [compileRExprPreChecked, CheckedCompilerM.run_bind, h_valA,
      CheckedCompilerM.run_lift, CheckedCompilerM.value_lift, CheckedCompilerM.run_pure]
    rfl
  have h_preV : ∃ pOut, CheckedCompilerM.value
      (compileRExprPreChecked L dstL (RExpr.sliceLen (t := tE) src)) csA = .ok pOut ∧
      (∀ d, pOut.store d = [oseairL.Instr.RStore dstL
        (Register.R (CheckedCompilerM.run (readToReg L src) csA).nextReg) d]) ∧
      pOut.postCleanup = [] := by
    simp only [compileRExprPreChecked, CheckedCompilerM.value_bind, h_valA,
      CheckedCompilerM.value_lift, CheckedCompilerM.run_lift, CheckedCompilerM.value_pure]
    exact ⟨_, rfl, fun _ => rfl, rfl⟩
  obtain ⟨pOut, h_pval, h_store, h_post⟩ := h_preV
  refine ⟨_, pOut, h_pval, h_store, h_post, by rw [h_pre]; exact h_prmA, fun h_code => ?_⟩
  rw [h_pre] at h_code ⊢
  obtain ⟨n1, s1, vals1, h_run1, h_inv1, -, h_r1, -, h_rel1, -, -⟩ :=
    readToReg_simR hWF h_c h_inv0 h_e1 (h_code.mono ((bumpReg_state_incr' _).trans (emit_state_incr _ _)))
  rw [h_p] at h_rel1
  obtain ⟨t', rfl, -⟩ := ptr_of_storeSim h_rel1
  have h_instr : compProg s1.pc = some (oseairL.Instr.Assgn
      (Register.R (CheckedCompilerM.run (readToReg L src) csA).nextReg)
      (oseairL.Rhs.SliceLen (mirliteB.pointeeLayout L src).size
        (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared src) csA).nextReg))) := by
    rw [h_inv1.pc]
    apply h_code
    · simp [emit]
    · simp [emit]
  have h_ev2 : oseairL.evalRhs MSB s1 (oseairL.Rhs.SliceLen (mirliteB.pointeeLayout L src).size
        (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared src) csA).nextReg))
      = .Ok [Val.Dat (pe / (mirliteB.pointeeLayout L src).size)] s1 := by
    simp only [oseairL.evalRhs, h_r1]
  have h_run2 := runN_Assgn h_instr h_ev2
  rw [h_st1] at h_inv1
  refine ⟨ρt, n1 + 1, _, sM.mem, out1.state.perms,
    [Val.Dat (pe / (mirliteB.pointeeLayout L src).size)],
    TagRenameIncr.refl ρt, h_wf, h_st1, runN_trans h_run1 h_run2,
    ?_, ?_, h_inv1.psim, h_inv1.tbd, h_inv1.mem, h_inv1.alloc, ?_, ?_,
    ⟨Or.inr ⟨by simp, rfl⟩, trivial⟩⟩
  · show csA.nextReg ≤ _ + 1
    have := (CheckedCompilerM.incr (readToReg L src) csA).nextReg_le
    omega
  · refine LocalBindingSimB.prm_congr (LocalBindingSimB.of_frame h_inv1.lbs h_inv1.prb
      fun r hr => ?_) rfl
    exact RegMap.lookup_insert_ne _ _ (RegisterBelow.ne_fresh hr)
  · show s1.pc + 1 = _
    rw [h_inv1.pc]; rfl
  · exact StoreStepB.rstore compProg _ _ dstL _ _ (RegMap.lookup_insert_self _ _ _)
      (show _ < _ + 1 by omega)

theorem subSlice_pkg {Γ : Ctx} {L : mirliteB.LayEnv Γ} {compProg : oseairL.Prog}
    (hWF : PtrPlacesWF L) (dstL : BLayout) {σ : LayoutTy}
    {src : Place Γ (LayoutTy.PtrL σ)} {tl th : IntTy} {lo : Place Γ (LayoutTy.IntL tl)} {hi : Place Γ (LayoutTy.IntL th)}
    (h_c : ReadSrcB src) (h_cl : ReadSrcB lo) (h_ch : ReadSrcB hi) :
    ValuePkgB compProg L dstL (RExpr.subSlice src lo hi) := by
  intro ρt sM sA csA h_wf h_tbd h_lbs h_prb h_mem h_alloc h_psim h_pc h_unmap output h_ev
  have h_inv0 : InvAtB L ρt sM sA csA := ⟨h_pc, h_lbs, h_mem, h_alloc, h_psim, h_wf, h_tbd,
    h_unmap, h_prb⟩
  -- the source: three reads, the narrowing
  simp only [mirliteB.evalRExpr] at h_ev
  split at h_ev
  · cases h_ev
  rename_i out1 h_e1
  split at h_ev
  case h_2 => cases h_ev
  rename_i pb po pe ps pt h_p
  split at h_ev
  · cases h_ev
  rename_i out2 h_e2
  split at h_ev
  case h_2 => cases h_ev
  rename_i l h_l
  split at h_ev
  · cases h_ev
  rename_i out3 h_e3
  split at h_ev
  case h_2 => cases h_ev
  rename_i h h_h
  split at h_ev
  · cases h_ev
  rename_i h_ok
  simp only [mirliteB.EvalResult.ok.injEq] at h_ev
  subst h_ev
  have h_st1 := evalCopy_state h_e1
  have h_st2 := evalCopy_state h_e2
  have h_st3 := evalCopy_state h_e3
  -- compile-time
  obtain ⟨h_val1, h_prm1, h_nr1⟩ := readToReg_factsR h_c h_lbs h_e1
  have h_lbs1 : LocalBindingSimB L ρt out1.state.env sA (CheckedCompilerM.run (readToReg L src) csA) := by
    rw [h_st1]; exact LocalBindingSimB.prm_congr h_lbs h_prm1
  obtain ⟨h_val2, h_p2, h_nr2⟩ := readToReg_factsR h_cl h_lbs1 h_e2
  have h_prm2 : (CheckedCompilerM.run (readToReg L lo)
      (CheckedCompilerM.run (readToReg L src) csA)).placeRegMap = csA.placeRegMap :=
    h_p2.trans h_prm1
  have h_lbs2 : LocalBindingSimB L ρt out2.state.env sA (CheckedCompilerM.run (readToReg L lo)
      (CheckedCompilerM.run (readToReg L src) csA)) := by
    rw [h_st2, h_st1]; exact LocalBindingSimB.prm_congr h_lbs h_prm2
  obtain ⟨h_val3, h_p3, -⟩ := readToReg_factsR h_ch h_lbs2 h_e3
  have h_prm3 : (CheckedCompilerM.run (readToReg L hi) (CheckedCompilerM.run (readToReg L lo)
      (CheckedCompilerM.run (readToReg L src) csA))).placeRegMap = csA.placeRegMap :=
    h_p3.trans h_prm2
  have h_pre : CheckedCompilerM.run (compileRExprPreChecked L dstL (RExpr.subSlice src lo hi)) csA
      = emit (bumpReg (CheckedCompilerM.run (readToReg L hi) (CheckedCompilerM.run (readToReg L lo)
          (CheckedCompilerM.run (readToReg L src) csA))))
          [oseairL.Instr.Assgn
            (Register.R (CheckedCompilerM.run (readToReg L hi) (CheckedCompilerM.run (readToReg L lo)
              (CheckedCompilerM.run (readToReg L src) csA))).nextReg)
            (oseairL.Rhs.SubSlice (mirliteB.pointeeLayout L src).size
              (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared src) csA).nextReg)
              (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared lo)
                (CheckedCompilerM.run (readToReg L src) csA)).nextReg)
              (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared hi)
                (CheckedCompilerM.run (readToReg L lo) (CheckedCompilerM.run (readToReg L src) csA))).nextReg))] := by
    simp only [compileRExprPreChecked, CheckedCompilerM.run_bind, h_val1, h_val2, h_val3,
      CheckedCompilerM.run_lift, CheckedCompilerM.value_lift, CheckedCompilerM.run_pure]
    rfl
  have h_preV : ∃ pOut, CheckedCompilerM.value
      (compileRExprPreChecked L dstL (RExpr.subSlice src lo hi)) csA = .ok pOut ∧
      (∀ d, pOut.store d = [oseairL.Instr.RStore dstL
        (Register.R (CheckedCompilerM.run (readToReg L hi) (CheckedCompilerM.run (readToReg L lo)
          (CheckedCompilerM.run (readToReg L src) csA))).nextReg) d]) ∧
      pOut.postCleanup = [] := by
    simp only [compileRExprPreChecked, CheckedCompilerM.value_bind, h_val1, h_val2, h_val3,
      CheckedCompilerM.value_lift, CheckedCompilerM.run_lift, CheckedCompilerM.value_pure]
    exact ⟨_, rfl, fun _ => rfl, rfl⟩
  obtain ⟨pOut, h_pval, h_store, h_post⟩ := h_preV
  refine ⟨_, pOut, h_pval, h_store, h_post, by rw [h_pre]; exact h_prm3, fun h_code => ?_⟩
  rw [h_pre] at h_code ⊢
  -- the three reads, chained
  have h_code3 := h_code.mono ((bumpReg_state_incr' _).trans (emit_state_incr _ _))
  have h_i3 := CheckedCompilerM.incr (readToReg L hi) (CheckedCompilerM.run (readToReg L lo)
    (CheckedCompilerM.run (readToReg L src) csA))
  have h_i2 := CheckedCompilerM.incr (readToReg L lo) (CheckedCompilerM.run (readToReg L src) csA)
  obtain ⟨n1, s1, vals1, h_r1, h_inv1, -, h_l1, -, h_rel1, -, -⟩ :=
    readToReg_simR hWF h_c h_inv0 h_e1 ((h_code3.mono h_i3).mono h_i2)
  obtain ⟨n2, s2, vals2, h_r2, h_inv2, -, h_l2, -, h_rel2, -, h_fr2⟩ :=
    readToReg_simR hWF h_cl h_inv1 h_e2 (h_code3.mono h_i3)
  obtain ⟨n3, s3, vals3, h_r3, h_inv3, -, h_l3, -, h_rel3, -, h_fr3⟩ :=
    readToReg_simR hWF h_ch h_inv2 h_e3 h_code3
  rw [h_p] at h_rel1
  rw [h_l] at h_rel2
  rw [h_h] at h_rel3
  obtain ⟨t', rfl, h_t⟩ := ptr_of_storeSim h_rel1
  have hv2 := word_of_storeSim h_rel2
  have hv3 := word_of_storeSim h_rel3
  subst hv2 hv3
  -- earlier registers survive later reads
  have hb1 : RegisterBelow (CheckedCompilerM.run (readToReg L src) csA).nextReg
      (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared src) csA).nextReg) := by
    show _ < _; rw [h_nr1]; omega
  have hb2 : RegisterBelow (CheckedCompilerM.run (readToReg L lo)
      (CheckedCompilerM.run (readToReg L src) csA)).nextReg
      (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared lo)
        (CheckedCompilerM.run (readToReg L src) csA)).nextReg) := by
    show _ < _; rw [h_nr2]; omega
  have h_l1' : s3.reg.lookup
      (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared src) csA).nextReg)
      = some [Val.Ptr pb po pe ps t'] := by
    rw [h_fr3 _ (RegisterBelow.mono h_i2.nextReg_le hb1), h_fr2 _ hb1]; exact h_l1
  have h_l2' : s3.reg.lookup
      (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared lo)
        (CheckedCompilerM.run (readToReg L src) csA)).nextReg) = some [Val.Dat l] := by
    rw [h_fr3 _ hb2]; exact h_l2
  -- the narrowing
  have h_instr : compProg s3.pc = some (oseairL.Instr.Assgn
      (Register.R (CheckedCompilerM.run (readToReg L hi) (CheckedCompilerM.run (readToReg L lo)
        (CheckedCompilerM.run (readToReg L src) csA))).nextReg)
      (oseairL.Rhs.SubSlice (mirliteB.pointeeLayout L src).size
        (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared src) csA).nextReg)
        (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared lo)
          (CheckedCompilerM.run (readToReg L src) csA)).nextReg)
        (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared hi)
          (CheckedCompilerM.run (readToReg L lo) (CheckedCompilerM.run (readToReg L src) csA))).nextReg))) := by
    rw [h_inv3.pc]
    apply h_code
    · simp [emit]
    · simp [emit]
  have h_ev4 := runN_Assgn (vals := [Val.Ptr pb (po + l * (mirliteB.pointeeLayout L src).size)
      ((h - l) * (mirliteB.pointeeLayout L src).size) ps t']) (s' := s3) h_instr
    (by simp only [oseairL.evalRhs, h_l1', h_l2', h_l3, h_ok, Bool.false_eq_true, if_false])
  rw [h_st3, h_st2, h_st1] at h_inv3
  simp only at h_inv3
  refine ⟨ρt, n1 + n2 + n3 + 1, _, sM.mem, out3.state.perms,
    [Val.Ptr pb (po + l * (mirliteB.pointeeLayout L src).size)
      ((h - l) * (mirliteB.pointeeLayout L src).size) ps t'],
    TagRenameIncr.refl ρt, h_wf, by rw [h_st3, h_st2, h_st1],
    runN_trans (runN_trans (runN_trans h_r1 h_r2) h_r3) h_ev4,
    ?_, ?_, h_inv3.psim, h_inv3.tbd, h_inv3.mem, h_inv3.alloc, ?_, ?_, ?_⟩
  · show csA.nextReg ≤ _ + 1
    have := (CheckedCompilerM.incr (readToReg L src) csA).nextReg_le
    have := h_i2.nextReg_le
    have := h_i3.nextReg_le
    omega
  · refine LocalBindingSimB.prm_congr (LocalBindingSimB.of_frame h_inv3.lbs h_inv3.prb
      fun r hr => ?_) rfl
    exact RegMap.lookup_insert_ne _ _ (RegisterBelow.ne_fresh hr)
  · show s3.pc + 1 = _
    rw [h_inv3.pc]; rfl
  · exact StoreStepB.rstore compProg _ _ dstL _ _ (RegMap.lookup_insert_self _ _ _)
      (show _ < _ + 1 by omega)
  · refine ⟨Or.inr ⟨by simp, ?_⟩, trivial⟩
    simp only [ValSim, oseair.Val.toMem, oseair.ofMem, MemValSim, idA]
    exact ⟨trivial, trivial, trivial, trivial, h_t, fun _ _ => ⟨_, rfl⟩⟩

end obseq3.byteproof
