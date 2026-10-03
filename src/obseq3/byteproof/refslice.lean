import obseq3.byteproof.alloc

/-!
# Slice references: the `refSlice` package

`dst := &kind *src` for a fat pointer `src`: read the pointer (one leaf),
then retag its whole extent. Compiled as `Load` of the pointer leaf into
a temporary, the source's borrow retired, then `Borrow … none` on the
temporary (the post-mint split that keeps a projected source's borrow
bracket closed). The retag is `sb_ref_respects_PermSim`, growing the
renaming.
-/

namespace obseq3.byteproof

open obseq3 obseq3.bytes obseq3.proof
open obseq3.mirlite (MemValue Binding Env PlaceRes)
open obseq3.oseair (Val Register)
open obseq3.compileB

theorem readRhsPre_shape_post {Γ : Ctx} {L : mirliteB.LayEnv Γ} {dstL : BLayout}
    {σ τ : LayoutTy} {rhs : RExpr Γ τ} {src : Place Γ σ} {mk : Register → oseairL.Rhs}
    {post : Register → List oseairL.Instr}
    {ev : (srcRes : PtrResult) → PlaceToRegEvidence L RefKind.Shared src srcRes →
      (dstPtr : Register) → RExprToEvidence L dstPtr rhs}
    {cs : CompilerState}
    {sOut : ResultWithEvidence PtrResult (PlaceToRegEvidence L RefKind.Shared src)}
    (h_sval : CheckedCompilerM.value (placeToRegChecked L RefKind.Shared src) cs = .ok sOut)
    (h_sclean : sOut.result.cleanup = []) :
    CheckedCompilerM.run (readRhsPre L dstL rhs src mk post ev) cs
      = emit (bumpReg (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared src) cs))
          ([oseairL.Instr.Assgn
            (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared src) cs).nextReg)
            (mk sOut.result.reg)] ++
            post (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared src) cs).nextReg)) ∧
    ∃ pOut, CheckedCompilerM.value (readRhsPre L dstL rhs src mk post ev) cs = Except.ok pOut ∧
      (∀ d, pOut.store d = [oseairL.Instr.RStore dstL
        (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared src) cs).nextReg) d]) ∧
      pOut.postCleanup = [] := by
  simp only [readRhsPre, CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift, CheckedCompilerM.run_pure,
    CheckedCompilerM.value_pure, h_sval]
  refine ⟨?_, _, rfl, fun _ => rfl, rfl⟩
  simp only [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM, cleanupInstrs, h_sclean,
    List.reverse_nil, List.map_nil, List.append_nil]

theorem code_two (rb : CompilerState) (i1 i2 : oseairL.Instr) :
    (emit (bumpReg rb) ([i1] ++ [i2])).code rb.nextLabel = some i1 ∧
    (emit (bumpReg rb) ([i1] ++ [i2])).code (rb.nextLabel + 1) = some i2 ∧
    (emit (bumpReg rb) ([i1] ++ [i2])).nextLabel = rb.nextLabel + 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [emit]

theorem refSlice_core {Γ : Ctx} {L : mirliteB.LayEnv Γ} {compProg : oseairL.Prog}
    (dstL : BLayout) (kind : RefKind) (prot : Bool) {σ τ : LayoutTy}
    {src : Place Γ (obseq.LayoutTy.PtrL σ)} (h_low : LowersB L compProg src) (h_comp : CompilesB L src) :
    ValuePkgB compProg L dstL (RExpr.refSlice (τ := τ) kind prot src) := by
  intro ρt sM sA csA h_wf h_tbd h_lbs h_prb h_mem h_alloc h_psim h_pc h_unmap output h_ev
  -- the source: read the fat pointer, retag its extent
  simp only [mirliteB.evalRExpr] at h_ev
  split at h_ev
  · cases h_ev
  case h_3 => cases h_ev
  rename_i base offset extent size tag perms' h_rc
  split at h_ev
  · cases h_ev
  rename_i h_freeB
  split at h_ev
  · cases h_ev
  rename_i perms'' newTag h_ref
  simp only [mirliteB.EvalResult.ok.injEq] at h_ev
  subst h_ev
  obtain ⟨resolved, permsR, h_res, h_free, h_bnd, h_rd, h_v⟩ := readCell_inv h_rc
  -- compile-time
  have h_map : ∀ {τ' : LayoutTy} (loc : Local Γ τ') (b : Binding), sM.env.lookup loc = some b →
      ∃ reg layout, getPlaceInfo csA loc.idx.1 = some (reg, layout) := fun loc b h => by
    obtain ⟨r, t, hpi, -⟩ := h_lbs loc b h
    exact ⟨r, _, hpi⟩
  obtain ⟨sOut, h_sval, h_sclean, h_sprm⟩ :=
    h_comp sM csA RefKind.Shared _ h_map h_res
  have h_pre : compileRExprPreChecked L dstL (RExpr.refSlice (τ := τ) kind prot src)
      = readRhsPre L dstL (RExpr.refSlice (τ := τ) kind prot src) src
          (oseairL.Rhs.Load (leafLayout (mirliteB.leafKind (mirliteB.placeLayout L src))))
          (fun tmp => [oseairL.Instr.Assgn tmp (oseairL.Rhs.Borrow kind prot [] none tmp 0)])
          (fun srcRes evd _ => RExprToEvidence.refSlice kind prot src srcRes evd) := rfl
  obtain ⟨h_run, pOut, h_val, h_store, h_post⟩ :=
    readRhsPre_shape_post (dstL := dstL) (rhs := RExpr.refSlice (τ := τ) kind prot src)
      (mk := oseairL.Rhs.Load (leafLayout (mirliteB.leafKind (mirliteB.placeLayout L src))))
      (post := fun tmp => [oseairL.Instr.Assgn tmp (oseairL.Rhs.Borrow kind prot [] none tmp 0)])
      (ev := fun srcRes evd _ => RExprToEvidence.refSlice kind prot src srcRes evd) h_sval h_sclean
  rw [h_pre]
  refine ⟨_, pOut, h_val, h_store, h_post, by rw [h_run]; exact h_sprm, fun h_code => ?_⟩
  rw [h_run] at h_code ⊢
  -- the source place's lowering
  obtain ⟨sOut', n1, s1, tres, hS⟩ :=
    h_low ρt sM RefKind.Shared csA sA resolved permsR h_wf h_res h_tbd
      h_lbs h_prb h_mem h_alloc h_psim h_pc
      (h_code.mono ((bumpReg_state_incr' _).trans (emit_state_incr _ _)))
  have h_same : sOut' = sOut := by
    have := hS.val
    rw [h_sval] at this
    exact (Except.ok.inj this).symm
  subst h_same
  obtain ⟨ext, h_entry⟩ := hS.entry
  have h_mem1 : ByteMemSim ρt sM.mem s1.mem := by rw [hS.mem]; exact h_mem
  have h_lock1 : ByteAllocLockstep sM.mem s1.mem := by rw [hS.mem]; exact h_alloc
  have hcode := code_two (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared src) csA)
  -- §1 Load the fat pointer
  obtain ⟨p2, h_rd', h_psim2⟩ := sb_read_respects_PermSim hS.psim h_wf hS.rt h_rd
  have h_vs := decodeV_sim h_wf (mirliteB.leafKind (mirliteB.placeLayout L src))
    (h_mem1.read resolved.addr (mirliteB.leafKind (mirliteB.placeLayout L src)).size)
  rw [← h_v] at h_vs
  obtain ⟨t', h_w, h_t⟩ := valSim_ptr h_vs
  have hA : resolved.allocBase + (resolved.addr - resolved.allocBase) = resolved.addr :=
    Nat.add_sub_cancel' hS.le
  have h_freeT : s1.mem.isFreed resolved.allocBase = false := by
    simp only [bytes.Mem.isFreed, ← h_lock1.2.2] at h_free ⊢
    simpa using h_free
  let tmp := Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared src) csA).nextReg
  have h_i1 : compProg s1.pc = some (oseairL.Instr.Assgn tmp
      (oseairL.Rhs.Load (leafLayout (mirliteB.leafKind (mirliteB.placeLayout L src))) sOut'.result.reg)) := by
    rw [hS.pc]
    exact h_code _ _ (by rw [(hcode _ _).2.2]; omega) (hcode _ _).1
  have h_run1 := runN_Assgn (vals := [Val.Ptr base offset extent size t'])
    (s' := { s1 with perms := p2 }) h_i1
    (by
      simp only [PermissionModel.stackedBorrows] at h_rd'
      simp only [oseairL.evalRhs, h_entry, hA, h_freeT, Bool.false_eq_true, if_false,
        leafLayout_size, h_bnd, PermissionModel.stackedBorrows, h_rd', readL_leafLayout,
        List.map_cons, List.map_nil, h_w, oseairB.ofMem]
      rfl)
  -- §2 retag the extent through the temporary
  have h_tbd2 : TagRenameBounded ρt perms'.NextTag p2.NextTag := by
    rw [sb_read_NextTag h_rd, sb_read_NextTag h_rd', hS.srcNT]
    exact TagRenameBounded.mono h_tbd (Nat.le_refl _) hS.tgtNT
  obtain ⟨q, h_ref', h_fresh, h_incr, h_wf', h_tbd', h_psim'⟩ :=
    sb_ref_respects_PermSim h_psim2 h_wf h_tbd2 h_t h_ref
  subst h_fresh
  have h_freeB' : s1.mem.isFreed base = false := by
    simp only [bytes.Mem.isFreed, ← h_lock1.2.2] at h_freeB ⊢
    simpa using h_freeB
  have h_i2 : compProg (s1.pc + 1) = some (oseairL.Instr.Assgn tmp
      (oseairL.Rhs.Borrow kind prot [] none tmp 0)) := by
    rw [hS.pc]
    exact h_code _ _ (by rw [(hcode _ _).2.2]; omega) (hcode _ _).2.1
  let S1 : oseairL.State MSB :=
    { s1 with perms := p2, reg := s1.reg.insert tmp [Val.Ptr base offset extent size t'],
              pc := s1.pc + 1 }
  have h_run2 := runN_Assgn (s := S1) (vals := [Val.Ptr base (offset + 0) extent size p2.NextTag])
    (s' := { S1 with perms := q }) h_i2
    (by
      simp only [oseairL.evalRhs, S1, RegMap.lookup_insert_self, h_freeB', Bool.false_eq_true,
        if_false, Nat.add_zero, PermissionModel.stackedBorrows, h_ref'])
  refine ⟨ρt.extend perms'.NextTag p2.NextTag, n1 + 1 + 1, _, sM.mem, perms'',
    [Val.Ptr base (offset + 0) extent size p2.NextTag], h_incr, h_wf', rfl,
    runN_trans (runN_trans hS.run h_run1) h_run2, ?_, ?_, h_psim', h_tbd',
    ByteMemSim.rename_mono h_incr h_mem1, h_lock1, ?_, ?_, ?_⟩
  · show csA.nextReg ≤ _ + 1
    exact Nat.le_trans hS.regmono (Nat.le_succ _)
  · refine LocalBindingSimB.prm_congr (LocalBindingSimB.of_frame
      (LocalBindingSimB.rename_mono h_incr h_lbs) h_prb fun r hr => ?_) hS.prm
    have hne := RegisterBelow.ne_fresh (RegisterBelow.mono hS.regmono hr)
    show ((s1.reg.insert tmp _).insert tmp _).lookup r = _
    rw [RegMap.lookup_insert_ne _ _ hne, RegMap.lookup_insert_ne _ _ hne]
    exact hS.frame r hr
  · show s1.pc + 1 + 1 = _
    rw [(hcode _ _).2.2, hS.pc]
  · exact StoreStepB.rstore compProg _ _ dstL tmp _ (RegMap.lookup_insert_self _ _ _)
      (show _ < _ + 1 by omega)
  · refine ⟨Or.inr ⟨by simp, ?_⟩, trivial⟩
    simp only [ValSim, oseairB.Val.toMem, oseairB.ofMem, MemValSim, idA, Nat.add_zero]
    exact ⟨trivial, trivial, trivial, trivial, TagRenameMap.extend_self _ _ _,
      fun _ _ => ⟨_, rfl⟩⟩

theorem refSlice_pkg {Γ : Ctx} {L : mirliteB.LayEnv Γ} {compProg : oseairL.Prog}
    (hWF : PtrPlacesWF L) (dstL : BLayout) (kind : RefKind) (prot : Bool) {σ τ : LayoutTy}
    {src : Place Γ (obseq.LayoutTy.PtrL σ)} (h_chain : ChainB src) :
    ValuePkgB compProg L dstL (RExpr.refSlice (τ := τ) kind prot src) :=
  refSlice_core dstL kind prot (chainB_lowers hWF h_chain) (chainB_compilesB h_chain)

end obseq3.byteproof
