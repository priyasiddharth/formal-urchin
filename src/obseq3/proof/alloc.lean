import obseq3.proof.slice

/-!
# Heap allocation: the `alloc` package

`dst := alloc[len]`, the length a constant or read from a place. Both
machines allocate `len × element` bytes in lockstep (same base) and own
them with `sb_own`, which mints a tag on each side and grows the tag
renaming (`sb_own_respects_PermSim`, as for a local's first assignment).
-/

namespace obseq3.proof

open obseq3 obseq3.bytes obseq3.proof
open obseq3.mirlite (MemValue Binding Env PlaceRes)
open obseq3.oseair (Val Register)
open obseq3.compile

theorem allocPtr_sim {ρt : TagRenameMap} (hwf : TagRenameWF ρt) {pS pS' : AccessPerms}
    {s : oseair.State MSB} {mS : bytes.Mem} {size align : Nat} {tag : Tag}
    (h_psim : PermSim ρt pS s.perms) (h_tbd : TagRenameBounded ρt pS.NextTag s.perms.NextTag)
    (h_mem : ByteMemSim ρt mS s.mem) (h_lock : ByteAllocLockstep mS s.mem)
    (h_own : sb_own pS (mS.allocate size (max 1 align)).1 size = .ok (pS', tag)) :
    ∃ tgt', oseair.allocPtr MSB s size align
        = .Ok [Val.Ptr (mS.allocate size (max 1 align)).1 0 size size s.perms.NextTag]
          { s with mem := (s.mem.allocate size (max 1 align)).2, perms := tgt' } ∧
      tag = pS.NextTag ∧
      TagRenameIncr ρt (ρt.extend pS.NextTag s.perms.NextTag) ∧
      TagRenameWF (ρt.extend pS.NextTag s.perms.NextTag) ∧
      TagRenameBounded (ρt.extend pS.NextTag s.perms.NextTag) pS'.NextTag tgt'.NextTag ∧
      PermSim (ρt.extend pS.NextTag s.perms.NextTag) pS' tgt' ∧
      ByteMemSim (ρt.extend pS.NextTag s.perms.NextTag) (mS.allocate size (max 1 align)).2
        (s.mem.allocate size (max 1 align)).2 ∧
      ByteAllocLockstep (mS.allocate size (max 1 align)).2 (s.mem.allocate size (max 1 align)).2 := by
  obtain ⟨h_base, h_memA, h_lockA⟩ := ByteMemSim.allocate h_mem h_lock size (max 1 align)
  obtain ⟨tgt', h_own_t, h_tag, h_incr, h_wf', h_tbd', h_psim'⟩ :=
    sb_own_respects_PermSim h_psim hwf h_tbd h_own
  refine ⟨tgt', ?_, h_tag, h_incr, h_wf', h_tbd', h_psim', ByteMemSim.rename_mono h_incr h_memA,
    h_lockA⟩
  simp only [oseair.allocPtr, h_base, PermissionModel.stackedBorrows, h_own_t]

theorem alloc_const_pkg {Γ : Ctx} {L : mirlite.LayEnv Γ} {compProg : oseair.Prog}
    (dstL : BLayout) {σ : LayoutTy} (n : Nat) :
    ValuePkgB compProg L dstL (RExpr.alloc (Γ := Γ) (τ := σ) (.const n)) := by
  intro ρt sM sA csA h_wf h_tbd h_lbs h_prb h_mem h_alloc h_psim h_pc h_unmap output h_ev
  -- the source: allocate and own
  simp only [mirlite.evalRExpr, mirlite.evalAllocLen] at h_ev
  split at h_ev
  · cases h_ev
  rename_i perms' tag h_own
  simp only [mirlite.EvalResult.ok.injEq] at h_ev
  subst h_ev
  have h_pre : CheckedCompilerM.run
      (compileRExprPreChecked L dstL (RExpr.alloc (Γ := Γ) (τ := σ) (.const n))) csA
      = emit (bumpReg csA) [oseair.Instr.Assgn (Register.R csA.nextReg)
          (oseair.Rhs.AllocN (mirlite.allocPointee dstL σ) n)] := by
    simp only [compileRExprPreChecked, compileAllocLenChecked, CheckedCompilerM.run_bind,
      CheckedCompilerM.value_bind, CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
      CheckedCompilerM.run_pure]
    rfl
  have h_preV : ∃ pOut, CheckedCompilerM.value
      (compileRExprPreChecked L dstL (RExpr.alloc (Γ := Γ) (τ := σ) (.const n))) csA = .ok pOut ∧
      (∀ d, pOut.store d = [oseair.Instr.RStore dstL (Register.R csA.nextReg) d]) ∧
      pOut.postCleanup = [] := by
    simp only [compileRExprPreChecked, compileAllocLenChecked, CheckedCompilerM.value_bind,
      CheckedCompilerM.run_bind, CheckedCompilerM.value_lift, CheckedCompilerM.run_lift,
      CheckedCompilerM.value_pure]
    exact ⟨_, rfl, fun _ => rfl, rfl⟩
  obtain ⟨pOut, h_pval, h_store, h_post⟩ := h_preV
  refine ⟨_, pOut, h_pval, h_store, h_post, by rw [h_pre]; rfl, fun h_code => ?_⟩
  rw [h_pre] at h_code ⊢
  obtain ⟨tgt', h_ap, h_tag, h_incr, h_wf', h_tbd', h_psim', h_mem', h_lock'⟩ :=
    allocPtr_sim h_wf h_psim h_tbd h_mem h_alloc h_own
  subst h_tag
  have h_instr : compProg sA.pc = some (oseair.Instr.Assgn (Register.R csA.nextReg)
      (oseair.Rhs.AllocN (mirlite.allocPointee dstL σ) n)) := by
    rw [h_pc]
    apply h_code
    · simp [emit]
    · simp [emit]
  have h_run1 := runN_Assgn (s' := { sA with
      mem := (sA.mem.allocate (n * (mirlite.allocPointee dstL σ).size)
        (max 1 (mirlite.allocPointee dstL σ).align)).2, perms := tgt' }) h_instr h_ap
  refine ⟨ρt.extend sM.perms.NextTag sA.perms.NextTag, 1, _,
    (sM.mem.allocate (n * (mirlite.allocPointee dstL σ).size)
      (max 1 (mirlite.allocPointee dstL σ).align)).2, perms',
    [Val.Ptr (sM.mem.allocate (n * (mirlite.allocPointee dstL σ).size)
      (max 1 (mirlite.allocPointee dstL σ).align)).1 0 (n * (mirlite.allocPointee dstL σ).size)
      (n * (mirlite.allocPointee dstL σ).size) sA.perms.NextTag], h_incr, h_wf', rfl,
    h_run1, ?_, ?_, h_psim', h_tbd', h_mem', h_lock', ?_, ?_, ?_⟩
  · show csA.nextReg ≤ csA.nextReg + 1
    omega
  · refine LocalBindingSimB.of_frame (LocalBindingSimB.rename_mono h_incr h_lbs) h_prb
      fun r hr => ?_
    exact RegMap.lookup_insert_ne _ _ (RegisterBelow.ne_fresh hr)
  · show sA.pc + 1 = _
    rw [h_pc]; rfl
  · exact StoreStepB.rstore compProg _ _ dstL _ _ (RegMap.lookup_insert_self _ _ _)
      (show csA.nextReg < csA.nextReg + 1 by omega)
  · refine ⟨Or.inr ⟨by simp, ?_⟩, trivial⟩
    simp only [ValSim, oseair.Val.toMem, oseair.ofMem, MemValSim, idA]
    exact ⟨trivial, trivial, trivial, trivial, TagRenameMap.extend_self _ _ _,
      fun _ _ => ⟨_, rfl⟩⟩

theorem evalAllocLen_fromPlace_inv {Γ : Ctx} {L : mirlite.LayEnv Γ} {sM s1 : mirlite.State MSB Γ}
    {p : Place Γ (LayoutTy.IntL tN)} {n : Nat}
    (h : mirlite.evalAllocLen MSB L sM (.fromPlace p) = .ok (n, s1)) :
    ∃ out, mirlite.evalCopy MSB L sM p = .ok out ∧ out.values = [.word n] ∧ s1 = out.state := by
  simp only [mirlite.evalAllocLen] at h
  split at h
  · cases h
  rename_i out h_out
  split at h
  · rename_i n' h_v
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨out, h_out, h_v, rfl⟩
  · cases h

theorem alloc_dyn_pkg {Γ : Ctx} {L : mirlite.LayEnv Γ} {compProg : oseair.Prog}
    (hWF : PtrPlacesWF L) (dstL : BLayout) {σ : LayoutTy}
    {p : Place Γ (LayoutTy.IntL tN)} (h_c : ReadSrcB p) :
    ValuePkgB compProg L dstL (RExpr.alloc (Γ := Γ) (τ := σ) (.fromPlace p)) := by
  intro ρt sM sA csA h_wf h_tbd h_lbs h_prb h_mem h_alloc h_psim h_pc h_unmap output h_ev
  have h_inv0 : InvAtB L ρt sM sA csA := ⟨h_pc, h_lbs, h_mem, h_alloc, h_psim, h_wf, h_tbd,
    h_unmap, h_prb⟩
  -- the source: read the length, allocate, own
  simp only [mirlite.evalRExpr] at h_ev
  cases h_al : mirlite.evalAllocLen MSB L sM (.fromPlace p) with
  | error e => rw [h_al] at h_ev; cases h_ev
  | ok ns =>
  obtain ⟨n, s1⟩ := ns
  rw [h_al] at h_ev
  simp only at h_ev
  split at h_ev
  · cases h_ev
  rename_i perms' tag h_own
  simp only [mirlite.EvalResult.ok.injEq] at h_ev
  subst h_ev
  obtain ⟨out1, h_e1, h_x, rfl⟩ := evalAllocLen_fromPlace_inv h_al
  have h_st1 := evalCopy_state h_e1
  -- compile-time
  obtain ⟨h_valA, h_prmA, -⟩ := readToReg_factsR h_c h_lbs h_e1
  have h_pre : CheckedCompilerM.run
      (compileRExprPreChecked L dstL (RExpr.alloc (Γ := Γ) (τ := σ) (.fromPlace p))) csA
      = emit (bumpReg (CheckedCompilerM.run (readToReg L p) csA))
          [oseair.Instr.Assgn (Register.R (CheckedCompilerM.run (readToReg L p) csA).nextReg)
            (oseair.Rhs.AllocDyn (mirlite.allocPointee dstL σ)
              (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared p) csA).nextReg))] := by
    simp only [compileRExprPreChecked, compileAllocLenChecked, guardRead, CheckedCompilerM.run_bind,
      CheckedCompilerM.value_bind, h_valA, CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
      CheckedCompilerM.run_pure]
    rfl
  have h_preV : ∃ pOut, CheckedCompilerM.value
      (compileRExprPreChecked L dstL (RExpr.alloc (Γ := Γ) (τ := σ) (.fromPlace p))) csA = .ok pOut ∧
      (∀ d, pOut.store d = [oseair.Instr.RStore dstL
        (Register.R (CheckedCompilerM.run (readToReg L p) csA).nextReg) d]) ∧
      pOut.postCleanup = [] := by
    simp only [compileRExprPreChecked, compileAllocLenChecked, guardRead,
      CheckedCompilerM.value_bind, CheckedCompilerM.run_bind, h_valA, CheckedCompilerM.value_lift,
      CheckedCompilerM.run_lift, CheckedCompilerM.value_pure]
    exact ⟨_, rfl, fun _ => rfl, rfl⟩
  obtain ⟨pOut, h_pval, h_store, h_post⟩ := h_preV
  refine ⟨_, pOut, h_pval, h_store, h_post, by rw [h_pre]; exact h_prmA, fun h_code => ?_⟩
  rw [h_pre] at h_code ⊢
  -- the read
  obtain ⟨n1, s1, vals1, h_run1, h_inv1, -, h_r1, -, h_rel1, -, -⟩ :=
    readToReg_simR hWF h_c h_inv0 h_e1 (h_code.mono ((bumpReg_state_incr' _).trans (emit_state_incr _ _)))
  rw [h_x] at h_rel1
  have hv1 := word_of_storeSim h_rel1
  subst hv1
  rw [h_st1] at h_inv1 h_own
  -- the allocation
  obtain ⟨tgt', h_ap, h_tag, h_incr, h_wf', h_tbd', h_psim', h_mem', h_lock'⟩ :=
    allocPtr_sim h_wf h_inv1.psim h_inv1.tbd h_inv1.mem h_inv1.alloc h_own
  subst h_tag
  have h_instr : compProg s1.pc = some (oseair.Instr.Assgn
      (Register.R (CheckedCompilerM.run (readToReg L p) csA).nextReg)
      (oseair.Rhs.AllocDyn (mirlite.allocPointee dstL σ)
        (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared p) csA).nextReg))) := by
    rw [h_inv1.pc]
    apply h_code
    · simp [emit]
    · simp [emit]
  have h_run2 := runN_Assgn (s' := { s1 with
      mem := (s1.mem.allocate (n * (mirlite.allocPointee dstL σ).size)
        (max 1 (mirlite.allocPointee dstL σ).align)).2, perms := tgt' }) h_instr
    (by simp only [oseair.evalRhs, h_r1]; exact h_ap)
  refine ⟨ρt.extend out1.state.perms.NextTag s1.perms.NextTag, n1 + 1, _,
    (sM.mem.allocate (n * (mirlite.allocPointee dstL σ).size)
      (max 1 (mirlite.allocPointee dstL σ).align)).2, perms',
    [Val.Ptr (sM.mem.allocate (n * (mirlite.allocPointee dstL σ).size)
      (max 1 (mirlite.allocPointee dstL σ).align)).1 0 (n * (mirlite.allocPointee dstL σ).size)
      (n * (mirlite.allocPointee dstL σ).size) s1.perms.NextTag], h_incr, h_wf',
    by rw [h_st1], runN_trans h_run1 h_run2, ?_, ?_, h_psim', h_tbd', h_mem', h_lock', ?_, ?_, ?_⟩
  · show csA.nextReg ≤ _ + 1
    have := (CheckedCompilerM.incr (readToReg L p) csA).nextReg_le
    omega
  · refine LocalBindingSimB.of_frame (LocalBindingSimB.rename_mono h_incr h_inv1.lbs) h_inv1.prb
      fun r hr => ?_
    exact RegMap.lookup_insert_ne _ _ (RegisterBelow.ne_fresh hr)
  · show s1.pc + 1 = _
    rw [h_inv1.pc]; rfl
  · exact StoreStepB.rstore compProg _ _ dstL _ _ (RegMap.lookup_insert_self _ _ _)
      (show _ < _ + 1 by omega)
  · refine ⟨Or.inr ⟨by simp, ?_⟩, trivial⟩
    simp only [ValSim, oseair.Val.toMem, oseair.ofMem, MemValSim, idA]
    rw [h_st1]
    exact ⟨rfl, trivial, trivial, trivial, TagRenameMap.extend_self _ _ _,
      fun _ _ => ⟨_, rfl⟩⟩

end obseq3.proof
