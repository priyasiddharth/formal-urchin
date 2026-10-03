import obseq3.byteproof.leaffield
import obseq3.byteproof.refslice

/-!
# `refSlice` with a field operand

`dst := &kind *b.f` for a fat-pointer field `b.f`. At offset zero and for
nested fields, `refSlice_core` applies through the lowering contract and
congruence. At a nonzero offset the compiled code is the one-leaf bracket
`Borrow(Shared); Load; Die` followed by the retag `Borrow … none` on the
loaded pointer: the bracket cancels to the source's read
(`sb_ref_read_die_cancels`, as in `leaf_pkg_projoff`), then the retag is
`sb_ref_respects_PermSim`, growing the renaming.
-/

namespace obseq3.byteproof

open obseq3 obseq3.bytes obseq3.proof
open obseq3.mirlite (MemValue Binding Env PlaceRes)
open obseq3.oseair (Val Register)
open obseq3.compileB

theorem readCell_what {Γ : Ctx} {L : mirliteB.LayEnv Γ} {sM : mirliteB.State MSB Γ}
    {σ : LayoutTy} {src : Place Γ σ} {w1 w2 : String} {x : MemValue × MSB.State}
    (h : mirliteB.readCell MSB L sM src w1 = .ok x) : mirliteB.readCell MSB L sM src w2 = .ok x := by
  obtain ⟨v, p⟩ := x
  obtain ⟨r, pR, h_r, h_f, h_b, h_rd, h_v⟩ := readCell_inv h
  simp only [mirliteB.readCell, h_r, h_f, h_b, h_v, if_false, Bool.false_eq_true]
  simp only [PermissionModel.stackedBorrows, h_rd]

theorem code_borrow_load_die_post (ra : CompilerState) (i1 i2 i3 i4 : oseairL.Instr) :
    (emit (bumpReg (emit (bumpReg ra) [i1])) ([i2] ++ [i3] ++ [i4])).code ra.nextLabel = some i1 ∧
    (emit (bumpReg (emit (bumpReg ra) [i1])) ([i2] ++ [i3] ++ [i4])).code (ra.nextLabel + 1)
      = some i2 ∧
    (emit (bumpReg (emit (bumpReg ra) [i1])) ([i2] ++ [i3] ++ [i4])).code (ra.nextLabel + 2)
      = some i3 ∧
    (emit (bumpReg (emit (bumpReg ra) [i1])) ([i2] ++ [i3] ++ [i4])).code (ra.nextLabel + 3)
      = some i4 ∧
    (emit (bumpReg (emit (bumpReg ra) [i1])) ([i2] ++ [i3] ++ [i4])).nextLabel = ra.nextLabel + 4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [emit]
  all_goals (repeat (first | rw [if_neg (by omega)] | rw [if_pos (by omega)])) <;> rfl

theorem refSlice_projoff {Γ : Ctx} {L : mirliteB.LayEnv Γ} {compProg : oseairL.Prog}
    (dstL : BLayout) (kind : RefKind) (prot : Bool) {ρ σ τ : LayoutTy} {b : Place Γ ρ}
    {f : PathTo ρ (obseq.LayoutTy.PtrL σ)}
    (h_np : ∀ (σ' : LayoutTy) (bb : Place Γ σ') (q : PathTo σ' ρ), b = bb.proj q → False)
    (h0 : pathOffset L b f ≠ 0) (hb : LowersB L compProg b) (hcb : CompilesB L b)
    (h_len : (mirliteB.leafKind (mirliteB.placeLayout L (.proj b f))).size = placeSize L (.proj b f)) :
    ValuePkgB compProg L dstL (RExpr.refSlice (τ := τ) kind prot (.proj b f)) := by
  intro ρt sM sA csA h_wf h_tbd h_lbs h_prb h_mem h_alloc h_psim h_pc _h_unmap output h_ev
  -- the source: read the fat pointer (as `ptrCast` would), retag its extent
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
  have h_evC : mirliteB.evalRExpr MSB L sM dstL (RExpr.ptrCast (τ := τ) (.proj b f)) =
      .ok { values := [.ptrVal base offset extent size tag], state := { sM with perms := perms' } } := by
    simp only [mirliteB.evalRExpr, readCell_what (w2 := "ptr-to-ptr cast") h_rc]
    rfl
  obtain ⟨resolved, permsR, h_res, h_free, h_bnd, h_rd, -⟩ := readCell_inv h_rc
  obtain ⟨⟨bRes, permsB⟩, h_rb, h_addr, h_tag, h_ab, h_as, h_pb⟩ :=
    borrow_proj_res (L := L) f sM _ h_res
  simp only at h_addr h_tag h_ab h_as h_pb
  subst h_pb
  -- compile-time
  let mk := oseairL.Rhs.Load (leafLayout (mirliteB.leafKind (mirliteB.placeLayout L (.proj b f))))
  let post := fun tmp => [oseairL.Instr.Assgn tmp (oseairL.Rhs.Borrow kind prot [] none tmp 0)]
  have h_pre : compileRExprPreChecked L dstL (RExpr.refSlice (τ := τ) kind prot (.proj b f))
      = readRhsPre L dstL (RExpr.refSlice (τ := τ) kind prot (.proj b f)) (.proj b f) mk post
          (fun srcRes evd _ => RExprToEvidence.refSlice kind prot _ srcRes evd) := rfl
  obtain ⟨bOut, h_bval, h_bclean, h_bprm⟩ := hcb sM csA RefKind.Shared _ (fun loc bnd h => by
    obtain ⟨r, t, hpi, -⟩ := h_lbs loc bnd h
    exact ⟨r, _, hpi⟩) h_rb
  obtain ⟨h_runP, outP, h_valP, h_resP⟩ :=
    (proj_lowering (kind := RefKind.Shared) f h_np h_bval).2 h0
  obtain ⟨h_run, pOut, h_val, h_store, h_post⟩ :=
    readRhsPre_shapeG (dstL := dstL) (rhs := RExpr.refSlice (τ := τ) kind prot (.proj b f)) (mk := mk)
      (post := post) (ev := fun srcRes evd _ => RExprToEvidence.refSlice kind prot _ srcRes evd) h_valP
  rw [h_resP, h_bclean, h_runP] at h_run
  simp only [List.nil_append, cleanupInstrs, List.reverse_cons, List.reverse_nil,
    List.map_cons, List.map_nil, post] at h_run
  rw [h_pre]
  refine ⟨_, pOut, h_val, h_store, h_post, ?_, fun h_code => ?_⟩
  · rw [h_run]; exact h_bprm
  rw [h_run] at h_code ⊢
  rw [h_runP] at h_store
  -- the base's lowering
  obtain ⟨bOut', n1, s1, tres, hB⟩ :=
    hb ρt sM RefKind.Shared csA sA bRes permsR h_wf h_rb h_tbd h_lbs h_prb h_mem h_alloc h_psim h_pc
      (h_code.mono (((bumpReg_state_incr' _).trans (emit_state_incr _ _)).trans
        ((bumpReg_state_incr' _).trans (emit_state_incr _ _))))
  have h_same : bOut' = bOut := by
    have := hB.val
    rw [h_bval] at this
    exact (Except.ok.inj this).symm
  subst h_same
  obtain ⟨ext, h_bentry⟩ := hB.entry
  have hA : bRes.allocBase + (bRes.addr - bRes.allocBase) = bRes.addr :=
    Nat.add_sub_cancel' hB.le
  have h_mem1 : ByteMemSim ρt sM.mem s1.mem := by rw [hB.mem]; exact h_mem
  have h_lock1 : ByteAllocLockstep sM.mem s1.mem := by rw [hB.mem]; exact h_alloc
  have h_freeT : s1.mem.isFreed bRes.allocBase = false := by
    rw [h_ab] at h_free
    simp only [bytes.Mem.isFreed, ← h_lock1.2.2] at h_free ⊢
    simpa using h_free
  have h_bnd' : bRes.addr + pathOffset L b f + placeSize L (.proj b f)
      ≤ bRes.allocBase + bRes.allocSize := by
    rw [← h_ab, ← h_as, ← h_len]
    have := Nat.le_of_not_gt h_bnd
    rw [h_addr] at this
    exact this
  -- the read, transported; the target's Shared retag; the cancellation
  have h_rd0 := h_rd
  rw [h_addr, h_tag, h_len] at h_rd0
  obtain ⟨p2, h_rd', h_psim2⟩ := sb_read_respects_PermSim hB.psim h_wf hB.rt h_rd0
  obtain ⟨q1, h_refS⟩ := sb_ref_Shared_ok_of_sb_read_ok h_rd'
  have h_tbd_mid : TagRenameBounded ρt permsR.NextTag s1.perms.NextTag := by
    rw [hB.srcNT]; exact TagRenameBounded.mono h_tbd (Nat.le_refl _) hB.tgtNT
  have h_unprot := freshTag_not_protected hB.psim h_tbd_mid
  have h0w : wildcardTag < s1.perms.NextTag := (h_tbd_mid _ _ h_wf.2).2
  have h_ntw : (s1.perms.NextTag == wildcardTag) = false := by
    simp only [beq_eq_false_iff_ne]; exact (Nat.ne_of_lt h0w).symm
  obtain ⟨q2, q3, sAcc, h_rd1, h_die1, h_rd2, h_sm, h_ex, h_pf, h_ntle, h_wk⟩ :=
    sb_ref_read_die_cancels h_ntw h_unprot h_refS
  have h_acc : sAcc = p2 := Except.ok.inj (h_rd2.symm.trans h_rd')
  subst h_acc
  -- the code
  have hct := code_borrow_load_die_post
    (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared b) csA)
  let tmp := Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared b) csA).nextReg
  let ld := Register.R ((CheckedCompilerM.run (placeToRegChecked L RefKind.Shared b) csA).nextReg + 1)
  have h_at : ∀ k i, k < 4 →
      (emit (bumpReg (emit (bumpReg (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared b) csA))
        [oseairL.Instr.Assgn tmp
          (borrowRhs RefKind.Shared (placeSize L (.proj b f)) bOut'.result.reg (pathOffset L b f))]))
        ([oseairL.Instr.Assgn ld (mk tmp)] ++ [oseairL.Instr.Die tmp (placeSize L (.proj b f))] ++
          [oseairL.Instr.Assgn ld (oseairL.Rhs.Borrow kind prot [] none ld 0)])).code
          (s1.pc + k) = some i →
      compProg (s1.pc + k) = some i := by
    intro k i hk hc
    refine h_code _ i ?_ hc
    rw [(hct _ _ _ _).2.2.2.2, hB.pc]; omega
  -- §1 Borrow
  have h1 := runN_Borrow (s := s1) (h_at 0 _ (by omega) (by rw [hB.pc]; exact (hct _ _ _ _).1))
    h_bentry h_freeT (by rw [hA]; exact h_bnd') (by rw [hA]; exact h_refS)
  -- §2 the Load, through the fresh tag
  let S1 : oseairL.State MSB :=
    { s1 with
        perms := q1,
        reg := s1.reg.insert tmp
          [Val.Ptr bRes.allocBase (bRes.addr - bRes.allocBase + pathOffset L b f)
            (placeSize L (.proj b f)) bRes.allocSize s1.perms.NextTag],
        pc := s1.pc + 1 }
  have h_le : resolved.allocBase ≤ resolved.addr := by
    rw [h_ab, h_addr]; exact Nat.le_trans hB.le (Nat.le_add_right _ _)
  have h_regS1 : S1.reg.lookup tmp = some [Val.Ptr resolved.allocBase
      (resolved.addr - resolved.allocBase) (placeSize L (.proj b f)) resolved.allocSize
      s1.perms.NextTag] := by
    rw [h_ab, h_as, h_addr]
    show (s1.reg.insert tmp _).lookup tmp = _
    rw [RegMap.lookup_insert_self, Nat.sub_add_comm hB.le]
  obtain ⟨vals, h_evT, h_rel⟩ := (ptrCast_ro (τ := τ) dstL (.proj b f)).target ρt sM S1 tmp resolved
    permsR _ _ _ q2 h_evC h_res h_wf h_mem1 h_lock1 h_regS1 h_le (by rw [h_len, h_addr]; exact h_rd1)
  obtain ⟨t', rfl, h_t⟩ := ptr_of_storeSim h_rel
  have h2 := runN_Assgn (h_at 1 _ (by omega) (by rw [hB.pc]; exact (hct _ _ _ _).2.1)) h_evT
  -- §3 Die
  let S2 : oseairL.State MSB :=
    { S1 with perms := q2, reg := S1.reg.insert ld [Val.Ptr base offset extent size t'],
              pc := S1.pc + 1 }
  have hne : tmp ≠ ld := by simp [tmp, ld]
  have h3 := runN_Die (s := S2) (h_at 2 _ (by omega) (by rw [hB.pc]; exact (hct _ _ _ _).2.2.1))
    (by
      show (S1.reg.insert ld _).lookup tmp = _
      rw [RegMap.lookup_insert_ne _ _ hne]
      exact RegMap.lookup_insert_self _ _ _)
    (by rw [← Nat.add_assoc, hA]; exact h_die1)
  -- §4 retag the extent through the loaded pointer
  have h_psim3 : PermSim ρt perms' q3 :=
    ⟨by rw [h_sm]; exact h_psim2.1, by rw [h_pf]; exact h_psim2.2.1,
      by rw [h_ex]; exact h_psim2.2.2.1, Nat.le_trans h_psim2.2.2.2.1 h_ntle,
      by rw [h_wk]; exact h_psim2.2.2.2.2⟩
  have h_tbd3 : TagRenameBounded ρt perms'.NextTag q3.NextTag := by
    rw [sb_read_NextTag h_rd, hB.srcNT]
    refine TagRenameBounded.mono h_tbd (Nat.le_refl _) (Nat.le_trans hB.tgtNT ?_)
    rw [← sb_read_NextTag h_rd']; exact h_ntle
  obtain ⟨q, h_ref', h_fresh, h_incr, h_wf', h_tbd', h_psim'⟩ :=
    sb_ref_respects_PermSim h_psim3 h_wf h_tbd3 h_t h_ref
  subst h_fresh
  have h_freeB' : s1.mem.isFreed base = false := by
    simp only [bytes.Mem.isFreed, ← h_lock1.2.2] at h_freeB ⊢
    simpa using h_freeB
  let S3 : oseairL.State MSB := { S2 with perms := q3, pc := S2.pc + 1 }
  have h4 := runN_Assgn (s := S3) (vals := [Val.Ptr base (offset + 0) extent size q3.NextTag])
    (s' := { S3 with perms := q })
    (h_at 3 _ (by omega) (by rw [hB.pc]; exact (hct _ _ _ _).2.2.2.1))
    (by
      simp only [oseairL.evalRhs, S3, S2, S1, RegMap.lookup_insert_self, h_freeB', Bool.false_eq_true,
        if_false, Nat.add_zero, PermissionModel.stackedBorrows, h_ref'])
  have h_frame : ∀ r, RegisterBelow csA.nextReg r →
      ((S3.reg).insert ld [Val.Ptr base (offset + 0) extent size q3.NextTag]).lookup r
        = sA.reg.lookup r := fun r hr => by
    have hr' := RegisterBelow.mono hB.regmono hr
    have hne1 : r ≠ tmp := RegisterBelow.ne_fresh hr'
    have hne2 : r ≠ ld := RegisterBelow.ne_fresh (RegisterBelow.mono (Nat.le_succ _) hr')
    show (((s1.reg.insert tmp _).insert ld _).insert ld _).lookup r = _
    rw [RegMap.lookup_insert_ne _ _ hne2, RegMap.lookup_insert_ne _ _ hne2,
      RegMap.lookup_insert_ne _ _ hne1]
    exact hB.frame r hr
  refine ⟨ρt.extend perms'.NextTag q3.NextTag, n1 + 1 + 1 + 1 + 1, _, sM.mem, perms'',
    [Val.Ptr base (offset + 0) extent size q3.NextTag], h_incr, h_wf', rfl,
    runN_trans (runN_trans (runN_trans (runN_trans hB.run h1) h2) h3) h4, ?_, ?_, h_psim', h_tbd',
    ByteMemSim.rename_mono h_incr h_mem1, h_lock1, ?_, ?_, ?_⟩
  · show csA.nextReg ≤ _ + 1 + 1
    have := hB.regmono
    omega
  · exact LocalBindingSimB.prm_congr (LocalBindingSimB.of_frame
      (LocalBindingSimB.rename_mono h_incr h_lbs) h_prb h_frame) hB.prm
  · show s1.pc + 1 + 1 + 1 + 1 = _
    rw [(hct _ _ _ _).2.2.2.2, hB.pc]
  · rw [h_runP]
    refine StoreStepB.rstore compProg _ _ dstL ld _ ?_ ?_
    · exact RegMap.lookup_insert_self _ _ _
    · show (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared b) csA).nextReg + 1
          < (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared b) csA).nextReg + 1 + 1
      omega
  · refine ⟨Or.inr ⟨by simp, ?_⟩, trivial⟩
    simp only [ValSim, oseairB.Val.toMem, oseairB.ofMem, MemValSim, idA, Nat.add_zero]
    exact ⟨trivial, trivial, trivial, trivial, TagRenameMap.extend_self _ _ _,
      fun _ _ => ⟨_, rfl⟩⟩

theorem refSlice_pkgL {Γ : Ctx} {L : mirliteB.LayEnv Γ} {compProg : oseairL.Prog}
    (hWF : PtrPlacesWF L) (hLeaf : LeafWF L) (dstL : BLayout) (kind : RefKind) (prot : Bool)
    {σ τ : LayoutTy} (src : Place Γ (obseq.LayoutTy.PtrL σ)) (h : LeafSrcB src) :
    ValuePkgB compProg L dstL (RExpr.refSlice (τ := τ) kind prot src) := by
  cases h with
  | chain hc => exact refSlice_pkg hWF dstL kind prot hc
  | field f hb =>
      rename_i ρ b
      have h_np := ChainB.not_proj hb
      by_cases h0 : pathOffset L b f = 0
      · exact refSlice_core dstL kind prot (proj_zero_lowers f h_np h0 (chainB_lowers hWF hb))
          (proj_zero_compiles f h_np h0 (chainB_compilesB hb))
      · exact refSlice_projoff dstL kind prot h_np h0 (chainB_lowers hWF hb) (chainB_compilesB hb)
          (hLeaf.1 _)
  | nested hn =>
      rename_i ρ' σ' b q p
      have ih := refSlice_pkgL (compProg := compProg) hWF hLeaf dstL kind prot (τ := τ)
        (.proj b (q.append p)) hn
      have h_as := readRhsPre_assoc (L := L) (dstL := dstL)
          (rhs1 := RExpr.refSlice (τ := τ) kind prot (.proj (.proj b q) p))
          (rhs2 := RExpr.refSlice (τ := τ) kind prot (.proj b (q.append p))) b q p
          (oseairL.Rhs.Load (leafLayout (mirliteB.leafKind (mirliteB.placeLayout L (.proj b (q.append p))))))
          (fun tmp => [oseairL.Instr.Assgn tmp (oseairL.Rhs.Borrow kind prot [] none tmp 0)])
          (fun srcRes evd _ => RExprToEvidence.refSlice kind prot _ srcRes evd)
          (fun srcRes evd _ => RExprToEvidence.refSlice kind prot _ srcRes evd)
      refine ValuePkgB.congr
        (fun sM => by simp only [mirliteB.evalRExpr, mirliteB.readCell, placeLayout_assoc,
          resolvePlaceAcc_assoc]) (fun cs => ?_) (fun cs => ?_) ih
      · have := (h_as cs).1
        simp only [compileRExprPreChecked, placeLayout_assoc] at this ⊢
        exact this
      · have := (h_as cs).2
        simp only [compileRExprPreChecked, placeLayout_assoc] at this ⊢
        exact this
termination_by src.depth
decreasing_by all_goals (subst_vars; simp_all [Place.depth]; try omega)

end obseq3.byteproof
