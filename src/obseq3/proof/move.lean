import obseq3.proof.ref

/-!
# The move package

`dst := move src`. Both machines retag the source `Mut` (a fresh tag),
read the value through it, and retire the tag — mirlite's `.move` does
the three Stacked Borrows events in a row, the compiled code is
`Borrow(Mut); Load; Die` through the borrow temporary. Each event
transports on its own (`sb_ref_respects_PermSim`, `sb_read_…`,
`sb_die_…`) under the renaming the retag grew, so no cancellation lemma
is needed. The borrow is the anchor contract of `ref.lean`.
-/

namespace obseq3.proof

open obseq3 obseq3.bytes obseq3.proof
open obseq3.mirlite (MemValue Binding Env PlaceRes)
open obseq3.oseair (Val Register)
open obseq3.compile

theorem code_borrow_load_die (ra : CompilerState) (i1 i2 i3 : oseair.Instr) :
    (emit (bumpReg (emit (bumpReg ra) [i1])) ([i2] ++ [i3])).code ra.nextLabel = some i1 ∧
    (emit (bumpReg (emit (bumpReg ra) [i1])) ([i2] ++ [i3])).code (ra.nextLabel + 1) = some i2 ∧
    (emit (bumpReg (emit (bumpReg ra) [i1])) ([i2] ++ [i3])).code (ra.nextLabel + 2) = some i3 ∧
    (emit (bumpReg (emit (bumpReg ra) [i1])) ([i2] ++ [i3])).nextLabel = ra.nextLabel + 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [emit]
  all_goals (repeat (first | rw [if_neg (by omega)] | rw [if_pos (by omega)])) <;> rfl

theorem move_pkg_core {Γ : Ctx} {L : mirlite.LayEnv Γ} {compProg : oseair.Prog}
    {σ τ : LayoutTy} {src : Place Γ τ} {a : Place Γ σ} {o : Nat}
    (h_shape : BorrowAnchorShape L src a o) (h_res : BorrowAnchorRes L src a o)
    (h_low : LowersB L compProg a) (h_comp : CompilesB L a) (dstL : BLayout) :
    ValuePkgB compProg L dstL (RExpr.move src) := by
  intro ρt sM sA csA h_wf h_tbd h_lbs h_prb h_mem h_alloc h_psim h_pc _h_unmap output h_ev
  -- the source: resolve, check, retag Mut, read through it, retire it
  simp only [mirlite.evalRExpr] at h_ev
  cases h_r : mirlite.resolvePlaceAcc MSB L sM src with
  | error e => simp [h_r] at h_ev
  | ok rr =>
  obtain ⟨resolved, permsR⟩ := rr
  simp only [h_r] at h_ev
  split at h_ev
  · cases h_ev
  rename_i h_free
  split at h_ev
  · cases h_ev
  rename_i h_bnd
  split at h_ev
  · cases h_ev
  rename_i permsM tmpTag h_ref
  split at h_ev
  · cases h_ev
  rename_i permsRd h_rd
  split at h_ev
  · cases h_ev
  rename_i perms' h_die
  split at h_ev
  · cases h_ev
  rename_i h_def
  simp only [mirlite.EvalResult.ok.injEq] at h_ev
  subst h_ev
  obtain ⟨⟨aRes, permsA⟩, h_ra, h_addr, h_tag, h_ab, h_as, h_pa⟩ := h_res sM _ h_r
  simp only at h_addr h_tag h_ab h_as h_pa
  subst h_pa
  -- compile-time facts
  have h_map : ∀ {τ' : LayoutTy} (loc : Local Γ τ') (b : Binding), sM.env.lookup loc = some b →
      ∃ reg layout, getPlaceInfo csA loc.idx.1 = some (reg, layout) := fun loc b h => by
    obtain ⟨r, t, hpi, -⟩ := h_lbs loc b h
    exact ⟨r, _, hpi⟩
  obtain ⟨aOut, h_aval, h_aclean, h_aprm⟩ := h_comp sM csA RefKind.Mut _ h_map h_ra
  obtain ⟨h_brun, bOut, h_bval, h_breg, h_bclean⟩ :=
    h_shape RefKind.Mut false [] csA aOut h_aval h_aclean
  have h_pre : CheckedCompilerM.run (compileRExprPreChecked L dstL (RExpr.move src)) csA
      = emit (bumpReg (emit (bumpReg (CheckedCompilerM.run (placeToRegChecked L RefKind.Mut a) csA))
          [oseair.Instr.Assgn
            (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Mut a) csA).nextReg)
            (oseair.Rhs.Borrow RefKind.Mut false [] (some (placeSize L src)) aOut.result.reg o)]))
          ([oseair.Instr.Assgn
            (Register.R ((CheckedCompilerM.run (placeToRegChecked L RefKind.Mut a) csA).nextReg + 1))
            (oseair.Rhs.Load (mirlite.placeLayout L src)
              (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Mut a) csA).nextReg))] ++
          [oseair.Instr.Die
            (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Mut a) csA).nextReg)
            (placeSize L src)]) := by
    simp only [compileRExprPreChecked, CheckedCompilerM.run_bind,
      h_bval, CheckedCompilerM.run_lift, CheckedCompilerM.value_lift, CheckedCompilerM.run_pure]
    rw [h_breg, h_bclean, h_brun]
    simp only [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM, cleanupInstrs,
      List.reverse_cons, List.reverse_nil, List.map_cons, List.map_nil, List.nil_append]
    rfl
  have h_preV : ∃ pOut, CheckedCompilerM.value
      (compileRExprPreChecked L dstL (RExpr.move src)) csA = .ok pOut ∧
      (∀ d, pOut.store d = [oseair.Instr.RStore dstL
        (Register.R ((CheckedCompilerM.run (placeToRegChecked L RefKind.Mut a) csA).nextReg + 1)) d]) ∧
      pOut.postCleanup = [] := by
    simp only [compileRExprPreChecked, CheckedCompilerM.value_bind, h_bval,
      CheckedCompilerM.value_lift, CheckedCompilerM.run_lift, CheckedCompilerM.value_pure]
    refine ⟨_, rfl, fun _ => ?_, rfl⟩
    rw [h_brun]; rfl
  obtain ⟨pOut, h_pval, h_store, h_post⟩ := h_preV
  refine ⟨_, pOut, h_pval, h_store, h_post, ?_, fun h_code => ?_⟩
  · rw [h_pre]; exact h_aprm
  rw [h_pre] at h_code ⊢
  -- the anchor's lowering
  obtain ⟨aOut', n1, s1, tres, hA⟩ :=
    h_low ρt sM RefKind.Mut csA sA aRes permsR h_wf h_ra h_tbd h_lbs h_prb h_mem h_alloc h_psim
      h_pc (h_code.mono (((bumpReg_state_incr' _).trans (emit_state_incr _ _)).trans
        ((bumpReg_state_incr' _).trans (emit_state_incr _ _))))
  have h_same : aOut' = aOut := by
    have := hA.val
    rw [h_aval] at this
    exact (Except.ok.inj this).symm
  subst h_same
  obtain ⟨ext, h_aentry⟩ := hA.entry
  have hB : aRes.allocBase + (aRes.addr - aRes.allocBase) = aRes.addr :=
    Nat.add_sub_cancel' hA.le
  have h_mem1 : ByteMemSim ρt sM.mem s1.mem := by rw [hA.mem]; exact h_mem
  have h_lock1 : ByteAllocLockstep sM.mem s1.mem := by rw [hA.mem]; exact h_alloc
  have h_freeT : s1.mem.isFreed aRes.allocBase = false := by
    rw [h_ab] at h_free
    simp only [bytes.Mem.isFreed, ← h_lock1.2.2] at h_free ⊢
    simpa using h_free
  have h_bnd' : aRes.addr + o + placeSize L src ≤ aRes.allocBase + aRes.allocSizeB := by
    rw [← h_addr, ← h_ab, ← h_as]; exact Nat.le_of_not_gt h_bnd
  -- the three events, transported
  have h_tbd1 : TagRenameBounded ρt permsR.NextTag s1.perms.NextTag := by
    rw [hA.srcNT]; exact TagRenameBounded.mono h_tbd (Nat.le_refl _) hA.tgtNT
  rw [h_addr, h_tag] at h_ref
  rw [h_addr] at h_rd h_die
  obtain ⟨q1, h_ref', h_fresh, h_incr, h_wf', h_tbd', h_psim1⟩ :=
    sb_ref_respects_PermSim hA.psim h_wf h_tbd1 hA.rt h_ref
  subst h_fresh
  have h_nt : (ρt.extend permsR.NextTag s1.perms.NextTag) permsR.NextTag
      = some s1.perms.NextTag := TagRenameMap.extend_self _ _ _
  obtain ⟨q2, h_rd', h_psim2⟩ := sb_read_respects_PermSim h_psim1 h_wf' h_nt h_rd
  obtain ⟨q3, h_die', h_psim3, h_nts, h_ntt⟩ := sb_die_respects_PermSim h_psim2 h_wf' h_nt h_die
  -- the values
  have hrel := readL_sim h_wf' (ByteMemSim.rename_mono h_incr h_mem1) (aRes.addr + o)
    (mirlite.placeLayout L src)
  obtain ⟨h_defT, h_relS⟩ := readL_rel hrel (by rw [h_addr] at h_def; simpa using h_def)
  -- the code
  have hct := code_borrow_load_die
    (CheckedCompilerM.run (placeToRegChecked L RefKind.Mut a) csA)
  have h_at : ∀ k i, k < 3 →
      (emit (bumpReg (emit (bumpReg (CheckedCompilerM.run (placeToRegChecked L RefKind.Mut a) csA))
        [oseair.Instr.Assgn
          (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Mut a) csA).nextReg)
          (oseair.Rhs.Borrow RefKind.Mut false [] (some (placeSize L src)) aOut'.result.reg o)]))
        ([oseair.Instr.Assgn
          (Register.R ((CheckedCompilerM.run (placeToRegChecked L RefKind.Mut a) csA).nextReg + 1))
          (oseair.Rhs.Load (mirlite.placeLayout L src)
            (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Mut a) csA).nextReg))] ++
        [oseair.Instr.Die
          (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Mut a) csA).nextReg)
          (placeSize L src)])).code (s1.pc + k) = some i →
      compProg (s1.pc + k) = some i := by
    intro k i hk hc
    refine h_code _ i ?_ hc
    rw [(hct _ _ _).2.2.2, hA.pc]; omega
  -- §1 Borrow
  have h1 := runN_Borrow (s := s1) (h_at 0 _ (by omega) (by rw [hA.pc]; exact (hct _ _ _).1))
    h_aentry h_freeT (by rw [hB]; exact h_bnd') (by rw [hB]; exact h_ref')
  -- §2 Load through the fresh tag
  let bTmp := Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Mut a) csA).nextReg
  let lTmp := Register.R ((CheckedCompilerM.run (placeToRegChecked L RefKind.Mut a) csA).nextReg + 1)
  let vals := (mirlite.readL s1.mem (aRes.addr + o) (mirlite.placeLayout L src)).map oseair.ofMem
  let S1 : oseair.State MSB :=
    { s1 with
        perms := q1,
        reg := s1.reg.insert bTmp
          [Val.Ptr aRes.allocBase (aRes.addr - aRes.allocBase + o) (placeSize L src)
            aRes.allocSizeB s1.perms.NextTag],
        pc := s1.pc + 1 }
  have hA' : aRes.allocBase + (aRes.addr - aRes.allocBase + o) = aRes.addr + o := by
    rw [← Nat.add_assoc, hB]
  have h2 : oseair.runN MSB 1 S1 compProg = .Ok
      { S1 with perms := q2, reg := S1.reg.insert lTmp vals, pc := S1.pc + 1 } := by
    have h_nb : ¬ (aRes.allocBase + (aRes.addr - aRes.allocBase + o)
        + (mirlite.placeLayout L src).size > aRes.allocBase + aRes.allocSizeB) := by
      rw [hA']; exact Nat.not_lt.mpr h_bnd'
    have h_instr := h_at 1 _ (by omega) (by rw [hA.pc]; exact (hct _ _ _).2.1)
    simp only [oseair.runN, oseair.step]
    rw [show S1.pc = s1.pc + 1 from rfl, h_instr]
    simp only [oseair.evalRhs, S1, bTmp, RegMap.lookup_insert_self, h_freeT, Bool.false_eq_true,
      if_false, h_nb, PermissionModel.stackedBorrows]
    rw [hA']
    simp only [h_rd', h_defT, Bool.false_eq_true, if_false]
    rfl
  -- §3 Die
  let S2 : oseair.State MSB :=
    { S1 with perms := q2, reg := S1.reg.insert lTmp vals, pc := S1.pc + 1 }
  have hne : bTmp ≠ lTmp := by simp [bTmp, lTmp]
  have h3 := runN_Die (s := S2) (h_at 2 _ (by omega) (by rw [hA.pc]; exact (hct _ _ _).2.2.1))
    (by
      show (S1.reg.insert lTmp vals).lookup bTmp = _
      rw [RegMap.lookup_insert_ne _ _ hne]
      exact RegMap.lookup_insert_self _ _ _)
    (by rw [hA']; exact h_die')
  refine ⟨ρt.extend permsR.NextTag s1.perms.NextTag, n1 + 1 + 1 + 1,
    { S2 with perms := q3, pc := S2.pc + 1 }, sM.mem, perms', vals, h_incr, h_wf', rfl,
    runN_trans (runN_trans (runN_trans hA.run h1) h2) h3, ?_, ?_, h_psim3, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show csA.nextReg ≤ _ + 1 + 1
    have := hA.regmono
    omega
  · refine LocalBindingSimB.prm_congr (LocalBindingSimB.of_frame
      (LocalBindingSimB.rename_mono h_incr h_lbs) h_prb fun r hr => ?_) hA.prm
    have hr' := RegisterBelow.mono hA.regmono hr
    have hne1 : r ≠ bTmp := RegisterBelow.ne_fresh hr'
    have hne2 : r ≠ lTmp := RegisterBelow.ne_fresh (RegisterBelow.mono (Nat.le_succ _) hr')
    show ((s1.reg.insert bTmp _).insert lTmp vals).lookup r = _
    rw [RegMap.lookup_insert_ne _ _ hne2, RegMap.lookup_insert_ne _ _ hne1]
    exact hA.frame r hr
  · show TagRenameBounded _ perms'.NextTag q3.NextTag
    rw [h_nts, h_ntt, sb_read_NextTag h_rd, sb_read_NextTag h_rd']
    exact h_tbd'
  · show ByteMemSim _ sM.mem s1.mem
    exact ByteMemSim.rename_mono h_incr h_mem1
  · exact h_lock1
  · show s1.pc + 1 + 1 + 1 = _
    rw [(hct _ _ _).2.2.2, hA.pc]
  · exact StoreStepB.rstore compProg _ _ dstL lTmp vals
      (by
        show ((S1.reg.insert lTmp vals)).lookup lTmp = _
        exact RegMap.lookup_insert_self _ _ _)
      (show _ < _ + 1 + 1 by omega)
  · rw [h_addr]; exact h_relS

/-! ## Instances -/

theorem move_local_pkg {Γ : Ctx} {L : mirlite.LayEnv Γ} {compProg : oseair.Prog}
    (hWF : PtrPlacesWF L) {τ : LayoutTy} (loc : Local Γ τ) (dstL : BLayout) :
    ValuePkgB compProg L dstL (RExpr.move (.local loc)) :=
  move_pkg_core (borrow_local_shape loc) (borrow_local_res loc)
    (ptrChain_lowers hWF (PtrChain.base loc)) (ptrChain_compilesB (PtrChain.base loc)) dstL

theorem move_deref_pkg {Γ : Ctx} {L : mirlite.LayEnv Γ} {compProg : oseair.Prog}
    (hWF : PtrPlacesWF L) {σ : LayoutTy} {q : Place Γ (LayoutTy.PtrL σ)}
    (h_chain : PtrChain (.deref q)) (dstL : BLayout) :
    ValuePkgB compProg L dstL (RExpr.move (.deref q)) :=
  move_pkg_core (borrow_deref_shape q) (borrow_deref_res q)
    (ptrChain_lowers hWF h_chain) (ptrChain_compilesB h_chain) dstL

theorem move_proj_pkg {Γ : Ctx} {L : mirlite.LayEnv Γ} {compProg : oseair.Prog}
    (hWF : PtrPlacesWF L) {ρ τ : LayoutTy} {b : Place Γ ρ} (f : PathTo ρ τ)
    (h_chain : PtrChain b) (dstL : BLayout) :
    ValuePkgB compProg L dstL (RExpr.move (.proj b f)) :=
  move_pkg_core (borrow_proj_shape f (PtrChain.not_proj h_chain)) (borrow_proj_res f)
    (ptrChain_lowers hWF h_chain) (ptrChain_compilesB h_chain) dstL

end obseq3.proof
