import obseq3.byteproof.readsrc

/-!
# One-leaf rvalues with a field operand

`ptrCast`, `ptrOffset` and `fromExposed` read ONE leaf of
their operand. When the operand is a field `b.f`:
- at byte offset zero (and for nested fields, after flattening) the field
  lowers as its base, so the chain skeletons apply through the lowering
  contract (`proj_nested_lowers`/`proj_nested_compiles` add nesting);
- at a nonzero offset the compiled read is `Borrow(Shared); op; Die`
  through the borrow temporary, and keystone's `sb_ref_read_die_cancels`
  closes it — provided the op reads exactly the field's bytes, which
  `LeafWF` (integer- and pointer-typed places have a one-leaf layout)
  guarantees. `refSlice` (a retag after the bracket) and `exposeAddr`
  (an exposure inside it) are in `refslicefield.lean`/`exposefield.lean`.
-/

namespace obseq3.byteproof

open obseq3 obseq3.bytes obseq3.proof
open obseq3.mirlite (MemValue Binding Env PlaceRes)
open obseq3.oseair (Val Register)
open obseq3.compileB

/-! ## Nested fields lower as the flattened field -/

theorem proj_nested_lowers {Γ : Ctx} {L : mirliteB.LayEnv Γ} {compProg : oseairL.Prog}
    {ρ σ τ : LayoutTy} {b : Place Γ ρ} {q : PathTo ρ σ} {p : PathTo σ τ}
    (h : LowersB L compProg (.proj b (q.append p))) : LowersB L compProg (.proj (.proj b q) p) := by
  intro ρt sM kind cs sA resolved permsD hwf h_res h_tbd h_lbs h_prb h_mem h_lock h_psim h_pc h_inc
  obtain ⟨h_run, h_val⟩ := placeToReg_assoc (L := L) kind b q p cs
  rw [resolvePlaceAcc_assoc] at h_res
  rw [h_run] at h_inc
  obtain ⟨o2, n, s', t, h2⟩ :=
    h ρt sM kind cs sA resolved permsD hwf h_res h_tbd h_lbs h_prb h_mem h_lock h_psim h_pc h_inc
  rw [h2.val] at h_val
  cases h_v1 : CheckedCompilerM.value (placeToRegChecked L kind (.proj (.proj b q) p)) cs with
  | error e => rw [h_v1] at h_val; cases h_val
  | ok o1 =>
      rw [h_v1] at h_val
      simp only [Except.map, Except.ok.injEq] at h_val
      exact ⟨o1, n, s', t, h2.congr h_v1 h_val h_run⟩

theorem proj_nested_compiles {Γ : Ctx} {L : mirliteB.LayEnv Γ}
    {ρ σ τ : LayoutTy} {b : Place Γ ρ} {q : PathTo ρ σ} {p : PathTo σ τ}
    (h : CompilesB L (.proj b (q.append p))) : CompilesB L (.proj (.proj b q) p) := by
  intro s cs kind r h_map h_res
  obtain ⟨h_run, h_val⟩ := placeToReg_assoc (L := L) kind b q p cs
  rw [resolvePlaceAcc_assoc] at h_res
  obtain ⟨o2, h_v2, h_c2, h_p2⟩ := h s cs kind r h_map h_res
  rw [h_v2] at h_val
  cases h_v1 : CheckedCompilerM.value (placeToRegChecked L kind (.proj (.proj b q) p)) cs with
  | error e => rw [h_v1] at h_val; cases h_val
  | ok o1 =>
      rw [h_v1] at h_val
      simp only [Except.map, Except.ok.injEq] at h_val
      exact ⟨o1, rfl, by rw [h_val]; exact h_c2, by rw [h_run]; exact h_p2⟩

/-! ## The one-leaf layout condition -/

/-- Integer- and pointer-typed places have a one-leaf layout: the leaf a
    one-leaf read decodes spans the whole place. -/
def LeafWF {Γ : Ctx} (L : mirliteB.LayEnv Γ) : Prop :=
  (∀ {σ : LayoutTy} (p : Place Γ (LayoutTy.PtrL σ)),
    (mirliteB.leafKind (mirliteB.placeLayout L p)).size = (mirliteB.placeLayout L p).size) ∧
  (∀ {t : IntTy} (p : Place Γ (LayoutTy.IntL t)),
    (mirliteB.leafKind (mirliteB.placeLayout L p)).size = (mirliteB.placeLayout L p).size)

/-! ## Read-only one-leaf ops -/

/-- An rvalue that reads one leaf through `src` and changes no permission
    beyond that read: its source evaluation is a checked read, and its
    target instruction, given the target read's outcome, yields related
    values. -/
structure ReadOnlyOpB {Γ : Ctx} (L : mirliteB.LayEnv Γ) (dstL : BLayout) {σ τ : LayoutTy}
    (rhs : RExpr Γ τ) (src : Place Γ σ) (mk : Register → oseairL.Rhs) : Prop where
  source : ∀ (sM : mirliteB.State MSB Γ) output,
    mirliteB.evalRExpr MSB L sM dstL rhs = .ok output →
    ∃ resolved permsR perms', mirliteB.resolvePlaceAcc MSB L sM src = .ok (resolved, permsR) ∧
      ¬ sM.mem.isFreed resolved.allocBase = true ∧
      ¬ (resolved.addr + (mirliteB.leafKind (mirliteB.placeLayout L src)).size
          > resolved.allocBase + resolved.allocSize) ∧
      sb_read permsR resolved.addr (mirliteB.leafKind (mirliteB.placeLayout L src)).size
        resolved.tag = .ok perms' ∧
      output.state = { sM with perms := perms' }
  target : ∀ (ρt : TagRenameMap) (sM : mirliteB.State MSB Γ) (s1 : oseairL.State MSB) (reg : Register)
      (resolved : PlaceRes) (permsR : MSB.State) (ext : Nat) (T : Tag) output (pmid : AccessPerms),
    mirliteB.evalRExpr MSB L sM dstL rhs = .ok output →
    mirliteB.resolvePlaceAcc MSB L sM src = .ok (resolved, permsR) →
    TagRenameWF ρt → ByteMemSim ρt sM.mem s1.mem → ByteAllocLockstep sM.mem s1.mem →
    s1.reg.lookup reg = some [Val.Ptr resolved.allocBase (resolved.addr - resolved.allocBase) ext
      resolved.allocSize T] →
    resolved.allocBase ≤ resolved.addr →
    sb_read s1.perms resolved.addr (mirliteB.leafKind (mirliteB.placeLayout L src)).size T = .ok pmid →
    ∃ vals, oseairL.evalRhs MSB s1 (mk reg) = .Ok vals { s1 with perms := pmid } ∧
      ListRel (StoreSim ρt) output.values (vals.map oseairB.Val.toMem)

/-- The target's one-leaf read, given the SB read's outcome. -/
theorem readCellThrough_ro {ρt : TagRenameMap} (hwf : TagRenameWF ρt)
    {s1 : oseairL.State MSB} {reg : Register} {resolved : PlaceRes} {ext : Nat} {T : Tag}
    {mS : bytes.Mem} {k : Scalar} {pmid : AccessPerms}
    (h_reg : s1.reg.lookup reg = some [Val.Ptr resolved.allocBase
      (resolved.addr - resolved.allocBase) ext resolved.allocSize T])
    (h_le : resolved.allocBase ≤ resolved.addr) (h_mem : ByteMemSim ρt mS s1.mem)
    (h_lock : ByteAllocLockstep mS s1.mem) (h_free : ¬ mS.isFreed resolved.allocBase = true)
    (h_bnd : ¬ (resolved.addr + k.size > resolved.allocBase + resolved.allocSize))
    (h_rd : sb_read s1.perms resolved.addr k.size T = .ok pmid) :
    oseairL.readCellThrough MSB s1 reg k
        = .ok (oseairB.ofMem (mirliteB.decodeV k (s1.mem.read resolved.addr k.size)), pmid) ∧
      ValSim ρt (mirliteB.decodeV k (mS.read resolved.addr k.size))
        (mirliteB.decodeV k (s1.mem.read resolved.addr k.size)) := by
  have hA : resolved.allocBase + (resolved.addr - resolved.allocBase) = resolved.addr :=
    Nat.add_sub_cancel' h_le
  have h_freeT : s1.mem.isFreed resolved.allocBase = false := by
    simp only [bytes.Mem.isFreed, ← h_lock.2.2] at h_free ⊢
    simpa using h_free
  refine ⟨?_, decodeV_sim hwf k (h_mem.read _ _)⟩
  simp only [oseairL.readCellThrough, h_reg, hA, h_freeT, Bool.false_eq_true, if_false, h_bnd,
    PermissionModel.stackedBorrows, h_rd]

theorem ptrOffset_ro {Γ : Ctx} {L : mirliteB.LayEnv Γ} (dstL : BLayout) {σ τ : LayoutTy}
    (src : Place Γ (LayoutTy.PtrL σ)) (delta : Int) :
    ReadOnlyOpB L dstL (RExpr.ptrOffset (τ := τ) src delta) src
      (fun r => oseairL.Rhs.PtrOffset (mirliteB.leafKind (mirliteB.placeLayout L src)) r
        (delta * ((mirliteB.pointeeLayout L src).size : Int))) where
  source sM output h := by
    simp only [mirliteB.evalRExpr] at h
    split at h
    · cases h
    · rename_i base offset e sz tag perms' h_rc
      split at h
      · cases h
      simp only [mirliteB.EvalResult.ok.injEq] at h
      subst h
      obtain ⟨r, p, h_r, h_free, h_bnd, h_rd, -⟩ := readCell_inv h_rc
      exact ⟨r, p, perms', h_r, h_free, h_bnd, h_rd, rfl⟩
    · cases h
  target ρt sM s1 reg resolved permsR ext T output pmid h h_res hwf h_mem h_lock h_reg h_le h_rdT := by
    simp only [mirliteB.evalRExpr] at h
    split at h
    · cases h
    · rename_i base offset e sz tag perms' h_rc
      split at h
      · cases h
      rename_i h_neg
      simp only [mirliteB.EvalResult.ok.injEq] at h
      subst h
      obtain ⟨r', p', h_r', h_free, h_bnd, h_rd, h_v⟩ := readCell_inv h_rc
      obtain ⟨rfl, rfl⟩ := resolve_eq h_res h_r'
      obtain ⟨h_rct, h_vs⟩ := readCellThrough_ro hwf h_reg h_le h_mem h_lock h_free h_bnd h_rdT
      rw [← h_v] at h_vs
      obtain ⟨t', h_w, h_t⟩ := valSim_ptr h_vs
      refine ⟨[Val.Ptr base (((offset : Int) + delta * ((mirliteB.pointeeLayout L src).size : Int)).toNat)
          e sz t'], ?_, ?_⟩
      · simp only [oseairL.evalRhs]
        rw [h_rct, h_w]
        simp only [oseairB.ofMem, h_neg, if_false]
      · refine ⟨Or.inr ⟨by simp, ?_⟩, trivial⟩
        simp only [ValSim, oseairB.Val.toMem, oseairB.ofMem, MemValSim, idA]
        exact ⟨trivial, trivial, trivial, trivial, h_t, fun _ _ => ⟨_, rfl⟩⟩
    · cases h

theorem fromExposed_ro {Γ : Ctx} {L : mirliteB.LayEnv Γ} (dstL : BLayout) {τ : LayoutTy}
    (src : Place Γ (LayoutTy.IntL tN)) :
    ReadOnlyOpB L dstL (RExpr.fromExposed (τ := τ) src) src
      (oseairL.Rhs.FromExposed (mirliteB.leafKind (mirliteB.placeLayout L src))) where
  source sM output h := by
    simp only [mirliteB.evalRExpr] at h
    split at h
    · cases h
    · rename_i n perms' h_rc
      simp only [mirliteB.EvalResult.ok.injEq] at h
      subst h
      obtain ⟨r, p, h_r, h_free, h_bnd, h_rd, -⟩ := readCell_inv h_rc
      exact ⟨r, p, perms', h_r, h_free, h_bnd, h_rd, rfl⟩
    · cases h
  target ρt sM s1 reg resolved permsR ext T output pmid h h_res hwf h_mem h_lock h_reg h_le h_rdT := by
    simp only [mirliteB.evalRExpr] at h
    split at h
    · cases h
    · rename_i n perms' h_rc
      simp only [mirliteB.EvalResult.ok.injEq] at h
      subst h
      obtain ⟨r', p', h_r', h_free, h_bnd, h_rd, h_v⟩ := readCell_inv h_rc
      obtain ⟨rfl, rfl⟩ := resolve_eq h_res h_r'
      obtain ⟨h_rct, h_vs⟩ := readCellThrough_ro hwf h_reg h_le h_mem h_lock h_free h_bnd h_rdT
      rw [← h_v] at h_vs
      have h_w := valSim_word h_vs
      have h_ao : s1.mem.allocOf n = sM.mem.allocOf n := by
        simp only [bytes.Mem.allocOf, h_lock.1]
      refine ⟨[Val.Ptr ((sM.mem.allocOf n).getD (n, 0)).1 (n - ((sM.mem.allocOf n).getD (n, 0)).1)
          (((sM.mem.allocOf n).getD (n, 0)).2 - (n - ((sM.mem.allocOf n).getD (n, 0)).1))
          ((sM.mem.allocOf n).getD (n, 0)).2 wildcardTag], ?_, ?_⟩
      · simp only [oseairL.evalRhs]
        rw [h_rct, h_w]
        simp only [oseairB.ofMem, h_ao]
      · refine ⟨Or.inr ⟨by simp, ?_⟩, trivial⟩
        simp only [ValSim, oseairB.Val.toMem, oseairB.ofMem, MemValSim, idA]
        exact ⟨trivial, trivial, trivial, trivial, hwf.2, fun _ _ => ⟨_, rfl⟩⟩
    · cases h

theorem ptrCast_ro {Γ : Ctx} {L : mirliteB.LayEnv Γ} (dstL : BLayout) {σ τ : LayoutTy}
    (src : Place Γ (LayoutTy.PtrL σ)) :
    ReadOnlyOpB L dstL (RExpr.ptrCast (τ := τ) src) src
      (oseairL.Rhs.Load (leafLayout (mirliteB.leafKind (mirliteB.placeLayout L src)))) where
  source sM output h := by
    simp only [mirliteB.evalRExpr] at h
    split at h
    · cases h
    · rename_i v perms' h_rc
      split at h
      · cases h
      simp only [mirliteB.EvalResult.ok.injEq] at h
      subst h
      obtain ⟨r, p, h_r, h_free, h_bnd, h_rd, -⟩ := readCell_inv h_rc
      exact ⟨r, p, perms', h_r, h_free, h_bnd, h_rd, rfl⟩
  target ρt sM s1 reg resolved permsR ext T output pmid h h_res hwf h_mem h_lock h_reg h_le h_rdT := by
    simp only [mirliteB.evalRExpr] at h
    split at h
    · cases h
    · rename_i v perms' h_rc
      split at h
      · cases h
      rename_i h_def
      simp only [mirliteB.EvalResult.ok.injEq] at h
      subst h
      obtain ⟨r', p', h_r', h_free, h_bnd, h_rd, h_v⟩ := readCell_inv h_rc
      obtain ⟨rfl, rfl⟩ := resolve_eq h_res h_r'
      have hv : v ≠ .undef := fun h' => h_def (by rw [h']; rfl)
      have h_vs := decodeV_sim hwf (mirliteB.leafKind (mirliteB.placeLayout L src))
        (h_mem.read resolved.addr (mirliteB.leafKind (mirliteB.placeLayout L src)).size)
      rw [← h_v] at h_vs
      obtain ⟨h_defT, h_relS⟩ := readL_rel (vs := [v])
        (ws := [mirliteB.decodeV (mirliteB.leafKind (mirliteB.placeLayout L src))
          (s1.mem.read resolved.addr (mirliteB.leafKind (mirliteB.placeLayout L src)).size)])
        (show ListRel _ [v] [_] from ⟨h_vs, trivial⟩)
        (by simp only [List.any_cons, List.any_nil, Bool.or_false]
            exact Bool.eq_false_iff.mpr h_def)
      have hA : resolved.allocBase + (resolved.addr - resolved.allocBase) = resolved.addr :=
        Nat.add_sub_cancel' h_le
      have h_freeT : s1.mem.isFreed resolved.allocBase = false := by
        simp only [bytes.Mem.isFreed, ← h_lock.2.2] at h_free ⊢
        simpa using h_free
      refine ⟨_, ?_, h_relS⟩
      simp only [oseairL.evalRhs, h_reg, hA, h_freeT, Bool.false_eq_true, if_false,
        leafLayout_size, h_bnd, PermissionModel.stackedBorrows, h_rdT, readL_leafLayout,
        List.map_cons, List.map_nil]
      have h_defT' : ([oseairB.ofMem (mirliteB.decodeV (mirliteB.leafKind (mirliteB.placeLayout L src))
          (s1.mem.read resolved.addr (mirliteB.leafKind (mirliteB.placeLayout L src)).size))].any
          fun v => v == Val.Undef) = false := h_defT
      rw [h_defT']
      rfl

/-! ## The bracket skeleton -/

theorem readRhsPre_shapeG {Γ : Ctx} {L : mirliteB.LayEnv Γ} {dstL : BLayout}
    {σ τ : LayoutTy} {rhs : RExpr Γ τ} {src : Place Γ σ} {mk : Register → oseairL.Rhs}
    {post : Register → List oseairL.Instr}
    {ev : (srcRes : PtrResult) → PlaceToRegEvidence L RefKind.Shared src srcRes →
      (dstPtr : Register) → RExprToEvidence L dstPtr rhs}
    {cs : CompilerState}
    {sOut : ResultWithEvidence PtrResult (PlaceToRegEvidence L RefKind.Shared src)}
    (h_sval : CheckedCompilerM.value (placeToRegChecked L RefKind.Shared src) cs = .ok sOut) :
    CheckedCompilerM.run (readRhsPre L dstL rhs src mk post ev) cs
      = emit (bumpReg (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared src) cs))
          ([oseairL.Instr.Assgn
            (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared src) cs).nextReg)
            (mk sOut.result.reg)] ++ cleanupInstrs sOut.result.cleanup ++
            post (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared src) cs).nextReg)) ∧
    ∃ pOut, CheckedCompilerM.value (readRhsPre L dstL rhs src mk post ev) cs = Except.ok pOut ∧
      (∀ d, pOut.store d = [oseairL.Instr.RStore dstL
        (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared src) cs).nextReg) d]) ∧
      pOut.postCleanup = [] := by
  simp only [readRhsPre, CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift, CheckedCompilerM.run_pure,
    CheckedCompilerM.value_pure, h_sval]
  exact ⟨rfl, _, rfl, fun _ => rfl, rfl⟩

theorem leaf_pkg_projoff {Γ : Ctx} {L : mirliteB.LayEnv Γ} {compProg : oseairL.Prog}
    {dstL : BLayout} {ρ τ τr : LayoutTy} {b : Place Γ ρ} {f : PathTo ρ τ} {rhs : RExpr Γ τr}
    {mk : Register → oseairL.Rhs}
    {ev : (srcRes : PtrResult) → PlaceToRegEvidence L RefKind.Shared (.proj b f) srcRes →
      (dstPtr : Register) → RExprToEvidence L dstPtr rhs}
    (h_np : ∀ (σ' : LayoutTy) (bb : Place Γ σ') (q : PathTo σ' ρ), b = bb.proj q → False)
    (h0 : pathOffset L b f ≠ 0) (hb : LowersB L compProg b) (hcb : CompilesB L b)
    (h_len : (mirliteB.leafKind (mirliteB.placeLayout L (.proj b f))).size = placeSize L (.proj b f))
    (h_op : ReadOnlyOpB L dstL rhs (.proj b f) mk)
    (h_pre : compileRExprPreChecked L dstL rhs = readRhsPre L dstL rhs (.proj b f) mk (fun _ => []) ev) :
    ValuePkgB compProg L dstL rhs := by
  intro ρt sM sA csA h_wf h_tbd h_lbs h_prb h_mem h_alloc h_psim h_pc _h_unmap output h_ev
  obtain ⟨resolved, permsR, perms', h_res, h_free, h_bnd, h_rd, h_ost⟩ := h_op.source sM output h_ev
  obtain ⟨⟨bRes, permsB⟩, h_rb, h_addr, h_tag, h_ab, h_as, h_pb⟩ :=
    borrow_proj_res (L := L) f sM _ h_res
  simp only at h_addr h_tag h_ab h_as h_pb
  subst h_pb
  -- compile-time
  obtain ⟨bOut, h_bval, h_bclean, h_bprm⟩ := hcb sM csA RefKind.Shared _ (fun loc bnd h => by
    obtain ⟨r, t, hpi, -⟩ := h_lbs loc bnd h
    exact ⟨r, _, hpi⟩) h_rb
  obtain ⟨h_runP, outP, h_valP, h_resP⟩ :=
    (proj_lowering (kind := RefKind.Shared) f h_np h_bval).2 h0
  obtain ⟨h_run, pOut, h_val, h_store, h_post⟩ :=
    readRhsPre_shapeG (dstL := dstL) (rhs := rhs) (mk := mk) (post := fun _ => []) (ev := ev) h_valP
  rw [h_resP, h_bclean, h_runP] at h_run
  simp only [List.nil_append, cleanupInstrs, List.reverse_cons, List.reverse_nil,
    List.map_cons, List.map_nil, List.append_nil] at h_run
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
  obtain ⟨q1, h_ref⟩ := sb_ref_Shared_ok_of_sb_read_ok h_rd'
  have h_tbd_mid : TagRenameBounded ρt permsR.NextTag s1.perms.NextTag := by
    rw [hB.srcNT]; exact TagRenameBounded.mono h_tbd (Nat.le_refl _) hB.tgtNT
  have h_unprot := freshTag_not_protected hB.psim h_tbd_mid
  have h0w : wildcardTag < s1.perms.NextTag := (h_tbd_mid _ _ h_wf.2).2
  have h_ntw : (s1.perms.NextTag == wildcardTag) = false := by
    simp only [beq_eq_false_iff_ne]; exact (Nat.ne_of_lt h0w).symm
  obtain ⟨q2, q3, sAcc, h_rd1, h_die1, h_rd2, h_sm, h_ex, h_pf, h_ntle, h_wk⟩ :=
    sb_ref_read_die_cancels h_ntw h_unprot h_ref
  have h_acc : sAcc = p2 := Except.ok.inj (h_rd2.symm.trans h_rd')
  subst h_acc
  -- the code
  have hct := code_borrow_load_die (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared b) csA)
  let tmp := Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared b) csA).nextReg
  let ld := Register.R ((CheckedCompilerM.run (placeToRegChecked L RefKind.Shared b) csA).nextReg + 1)
  have h_at : ∀ k i, k < 3 →
      (emit (bumpReg (emit (bumpReg (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared b) csA))
        [oseairL.Instr.Assgn tmp
          (borrowRhs RefKind.Shared (placeSize L (.proj b f)) bOut'.result.reg (pathOffset L b f))]))
        ([oseairL.Instr.Assgn ld (mk tmp)] ++ [oseairL.Instr.Die tmp (placeSize L (.proj b f))])).code
          (s1.pc + k) = some i →
      compProg (s1.pc + k) = some i := by
    intro k i hk hc
    refine h_code _ i ?_ hc
    rw [(hct _ _ _).2.2.2, hB.pc]; omega
  -- §1 Borrow
  have h1 := runN_Borrow (s := s1) (h_at 0 _ (by omega) (by rw [hB.pc]; exact (hct _ _ _).1))
    h_bentry h_freeT (by rw [hA]; exact h_bnd') (by rw [hA]; exact h_ref)
  -- §2 the op, through the fresh tag
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
  obtain ⟨vals, h_evT, h_rel⟩ := h_op.target ρt sM S1 tmp resolved permsR _ _ output q2 h_ev h_res h_wf
    h_mem1 h_lock1 h_regS1 h_le (by rw [h_len, h_addr]; exact h_rd1)
  have h2 := runN_Assgn (h_at 1 _ (by omega) (by rw [hB.pc]; exact (hct _ _ _).2.1)) h_evT
  -- §3 Die
  let S2 : oseairL.State MSB := { S1 with perms := q2, reg := S1.reg.insert ld vals, pc := S1.pc + 1 }
  have hne : tmp ≠ ld := by simp [tmp, ld]
  have h3 := runN_Die (s := S2) (h_at 2 _ (by omega) (by rw [hB.pc]; exact (hct _ _ _).2.2.1))
    (by
      show (S1.reg.insert ld vals).lookup tmp = _
      rw [RegMap.lookup_insert_ne _ _ hne]
      exact RegMap.lookup_insert_self _ _ _)
    (by rw [← Nat.add_assoc, hA]; exact h_die1)
  have h_frame : ∀ r, RegisterBelow csA.nextReg r → (S2.reg).lookup r = sA.reg.lookup r :=
    fun r hr => by
      have hr' := RegisterBelow.mono hB.regmono hr
      have hne1 : r ≠ tmp := RegisterBelow.ne_fresh hr'
      have hne2 : r ≠ ld := RegisterBelow.ne_fresh (RegisterBelow.mono (Nat.le_succ _) hr')
      show ((s1.reg.insert tmp _).insert ld vals).lookup r = _
      rw [RegMap.lookup_insert_ne _ _ hne2, RegMap.lookup_insert_ne _ _ hne1]
      exact hB.frame r hr
  refine ⟨ρt, n1 + 1 + 1 + 1, { S2 with perms := q3, pc := S2.pc + 1 }, sM.mem, perms', vals,
    TagRenameIncr.refl ρt, h_wf, h_ost,
    runN_trans (runN_trans (runN_trans hB.run h1) h2) h3, ?_, ?_, ?_, ?_, h_mem1, h_lock1, ?_, ?_,
    h_rel⟩
  · show csA.nextReg ≤ _ + 1 + 1
    have := hB.regmono
    omega
  · exact LocalBindingSimB.prm_congr (LocalBindingSimB.of_frame h_lbs h_prb h_frame) hB.prm
  · exact ⟨by rw [h_sm]; exact h_psim2.1, by rw [h_pf]; exact h_psim2.2.1,
      by rw [h_ex]; exact h_psim2.2.2.1, Nat.le_trans h_psim2.2.2.2.1 h_ntle,
      by rw [h_wk]; exact h_psim2.2.2.2.2⟩
  · show TagRenameBounded ρt perms'.NextTag q3.NextTag
    rw [sb_read_NextTag h_rd, hB.srcNT]
    refine TagRenameBounded.mono h_tbd (Nat.le_refl _) (Nat.le_trans hB.tgtNT ?_)
    rw [← sb_read_NextTag h_rd']; exact h_ntle
  · show s1.pc + 1 + 1 + 1 = _
    rw [(hct _ _ _).2.2.2, hB.pc]
  · rw [h_runP]
    refine StoreStepB.rstore compProg _ _ dstL ld vals ?_ ?_
    · show (S1.reg.insert ld vals).lookup ld = _
      exact RegMap.lookup_insert_self _ _ _
    · show (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared b) csA).nextReg + 1
          < (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared b) csA).nextReg + 1 + 1
      omega

/-! ## Nested fields: congruence -/

theorem ValuePkgB.congr {Γ : Ctx} {L : mirliteB.LayEnv Γ} {compProg : oseairL.Prog}
    {dstL : BLayout} {τ : LayoutTy} {r1 r2 : RExpr Γ τ}
    (h_eval : ∀ sM, mirliteB.evalRExpr MSB L sM dstL r1 = mirliteB.evalRExpr MSB L sM dstL r2)
    (h_run : ∀ cs, CheckedCompilerM.run (compileRExprPreChecked L dstL r1) cs
      = CheckedCompilerM.run (compileRExprPreChecked L dstL r2) cs)
    (h_val : ∀ cs p2, CheckedCompilerM.value (compileRExprPreChecked L dstL r2) cs = .ok p2 →
      ∃ p1, CheckedCompilerM.value (compileRExprPreChecked L dstL r1) cs = .ok p1 ∧
        (∀ d, p1.store d = p2.store d) ∧ p1.postCleanup = p2.postCleanup)
    (h : ValuePkgB compProg L dstL r2) : ValuePkgB compProg L dstL r1 := by
  intro ρt sM sA csA h_wf h_tbd h_lbs h_prb h_mem h_alloc h_psim h_pc h_unmap output h_ev
  rw [h_eval] at h_ev
  obtain ⟨mkStore, p2, h_v2, h_st2, h_po2, h_prm2, h_rest⟩ :=
    h ρt sM sA csA h_wf h_tbd h_lbs h_prb h_mem h_alloc h_psim h_pc h_unmap output h_ev
  obtain ⟨p1, h_v1, h_st, h_po⟩ := h_val csA p2 h_v2
  refine ⟨mkStore, p1, h_v1, fun d => (h_st d).trans (h_st2 d), h_po.trans h_po2,
    by rw [h_run]; exact h_prm2, fun hc => ?_⟩
  rw [h_run] at hc ⊢
  exact h_rest hc



theorem readRhsPre_assoc {Γ : Ctx} {L : mirliteB.LayEnv Γ} {dstL : BLayout} {ρ σ τ τr : LayoutTy}
    {rhs1 rhs2 : RExpr Γ τr} (b : Place Γ ρ) (q : PathTo ρ σ) (p : PathTo σ τ)
    (mk : Register → oseairL.Rhs) (post : Register → List oseairL.Instr)
    (ev1 : (srcRes : PtrResult) → PlaceToRegEvidence L RefKind.Shared (.proj (.proj b q) p) srcRes →
      (dstPtr : Register) → RExprToEvidence L dstPtr rhs1)
    (ev2 : (srcRes : PtrResult) → PlaceToRegEvidence L RefKind.Shared (.proj b (q.append p)) srcRes →
      (dstPtr : Register) → RExprToEvidence L dstPtr rhs2) (cs : CompilerState) :
    CheckedCompilerM.run (readRhsPre L dstL rhs1 (.proj (.proj b q) p) mk post ev1) cs
      = CheckedCompilerM.run (readRhsPre L dstL rhs2 (.proj b (q.append p)) mk post ev2) cs ∧
    ∀ p2, CheckedCompilerM.value (readRhsPre L dstL rhs2 (.proj b (q.append p)) mk post ev2) cs = .ok p2 →
      ∃ p1, CheckedCompilerM.value (readRhsPre L dstL rhs1 (.proj (.proj b q) p) mk post ev1) cs = .ok p1 ∧
        (∀ d, p1.store d = p2.store d) ∧ p1.postCleanup = p2.postCleanup := by
  obtain ⟨h_run, h_val⟩ := placeToReg_assoc (L := L) RefKind.Shared b q p cs
  cases h1 : CheckedCompilerM.value (placeToRegChecked L RefKind.Shared (.proj (.proj b q) p)) cs with
  | ok o1 =>
      cases h2 : CheckedCompilerM.value (placeToRegChecked L RefKind.Shared (.proj b (q.append p))) cs with
      | ok o2 =>
          rw [h1, h2] at h_val
          simp only [Except.map, Except.ok.injEq] at h_val
          obtain ⟨r1, p1, v1, s1, c1⟩ := readRhsPre_shapeG (dstL := dstL) (rhs := rhs1) (mk := mk)
            (post := post) (ev := ev1) h1
          obtain ⟨r2, p2, v2, s2, c2⟩ := readRhsPre_shapeG (dstL := dstL) (rhs := rhs2) (mk := mk)
            (post := post) (ev := ev2) h2
          rw [r1, r2, h_run, h_val]
          refine ⟨rfl, fun p2' h2' => ?_⟩
          rw [v2] at h2'
          cases h2'
          exact ⟨p1, v1, fun d => by rw [s1, s2, h_run], by rw [c1, c2]⟩
      | error e => rw [h1, h2] at h_val; simp [Except.map] at h_val
  | error e =>
      cases h2 : CheckedCompilerM.value (placeToRegChecked L RefKind.Shared (.proj b (q.append p))) cs with
      | ok o2 => rw [h1, h2] at h_val; simp [Except.map] at h_val
      | error e' =>
          rw [h1, h2] at h_val
          simp only [Except.map, Except.error.injEq] at h_val
          subst h_val
          simp only [readRhsPre, CheckedCompilerM.run_bind, CheckedCompilerM.value_bind, h1, h2, h_run]
          exact ⟨by first | rfl | trivial, fun p2 h => by cases h⟩

/-! ## Operands: a chain, a field of one, a nested field -/

inductive LeafSrcB {Γ : Ctx} : {τ : LayoutTy} → Place Γ τ → Prop
  | chain {τ : LayoutTy} {p : Place Γ τ} : ChainB p → LeafSrcB p
  | field {ρ τ : LayoutTy} {b : Place Γ ρ} (f : PathTo ρ τ) : ChainB b → LeafSrcB (.proj b f)
  | nested {ρ σ τ : LayoutTy} {b : Place Γ ρ} {q : PathTo ρ σ} {p : PathTo σ τ} :
      LeafSrcB (.proj b (q.append p)) → LeafSrcB (.proj (.proj b q) p)

theorem ptrCast_pkgL {Γ : Ctx} {L : mirliteB.LayEnv Γ} {compProg : oseairL.Prog}
    (hWF : PtrPlacesWF L) (hLeaf : LeafWF L) (dstL : BLayout) {σ τ : LayoutTy}
    (src : Place Γ (LayoutTy.PtrL σ)) (h : LeafSrcB src) :
    ValuePkgB compProg L dstL (RExpr.ptrCast (τ := τ) src) := by
  cases h with
  | chain hc => exact ptrCast_pkg hWF dstL hc
  | field f hb =>
      rename_i ρ b
      have h_np := ChainB.not_proj hb
      by_cases h0 : pathOffset L b f = 0
      · exact leaf_pkg_core (ev := fun srcRes evd _ => RExprToEvidence.ptrCast _ srcRes evd)
          (proj_zero_lowers f h_np h0 (chainB_lowers hWF hb))
          (proj_zero_compiles f h_np h0 (chainB_compilesB hb)) (ptrCast_leafop dstL _) rfl
      · exact leaf_pkg_projoff (ev := fun srcRes evd _ => RExprToEvidence.ptrCast _ srcRes evd)
          h_np h0 (chainB_lowers hWF hb) (chainB_compilesB hb) (hLeaf.1 _) (ptrCast_ro dstL _) rfl
  | nested hn =>
      rename_i ρ' σ' b q p
      have ih := ptrCast_pkgL (compProg := compProg) hWF hLeaf dstL (τ := τ) (.proj b (q.append p)) hn
      refine ValuePkgB.congr
        (fun sM => by simp only [mirliteB.evalRExpr, mirliteB.readCell, placeLayout_assoc,
          resolvePlaceAcc_assoc]) (fun cs => ?_) (fun cs => ?_) ih
      · have := (readRhsPre_assoc (L := L) (dstL := dstL)
          (rhs1 := RExpr.ptrCast (τ := τ) (.proj (.proj b q) p))
          (rhs2 := RExpr.ptrCast (τ := τ) (.proj b (q.append p))) b q p
          (oseairL.Rhs.Load (leafLayout (mirliteB.leafKind (mirliteB.placeLayout L (.proj b (q.append p))))))
          (fun _ => []) (fun srcRes evd _ => RExprToEvidence.ptrCast _ srcRes evd)
          (fun srcRes evd _ => RExprToEvidence.ptrCast _ srcRes evd) cs).1
        simp only [compileRExprPreChecked, placeLayout_assoc]
        exact this
      · have := (readRhsPre_assoc (L := L) (dstL := dstL)
          (rhs1 := RExpr.ptrCast (τ := τ) (.proj (.proj b q) p))
          (rhs2 := RExpr.ptrCast (τ := τ) (.proj b (q.append p))) b q p
          (oseairL.Rhs.Load (leafLayout (mirliteB.leafKind (mirliteB.placeLayout L (.proj b (q.append p))))))
          (fun _ => []) (fun srcRes evd _ => RExprToEvidence.ptrCast _ srcRes evd)
          (fun srcRes evd _ => RExprToEvidence.ptrCast _ srcRes evd) cs).2
        simp only [compileRExprPreChecked, placeLayout_assoc]
        exact this
termination_by src.depth
decreasing_by all_goals (subst_vars; simp_all [Place.depth]; try omega)

theorem ptrOffset_pkgL {Γ : Ctx} {L : mirliteB.LayEnv Γ} {compProg : oseairL.Prog}
    (hWF : PtrPlacesWF L) (hLeaf : LeafWF L) (dstL : BLayout) {σ τ : LayoutTy}
    (src : Place Γ (LayoutTy.PtrL σ)) (h : LeafSrcB src) (delta : Int) :
    ValuePkgB compProg L dstL (RExpr.ptrOffset (τ := τ) src delta) := by
  cases h with
  | chain hc => exact ptrOffset_pkg hWF dstL hc delta
  | field f hb =>
      rename_i ρ b
      have h_np := ChainB.not_proj hb
      by_cases h0 : pathOffset L b f = 0
      · exact leaf_pkg_core (ev := fun srcRes evd _ => RExprToEvidence.ptrOffset _ delta srcRes evd)
          (proj_zero_lowers f h_np h0 (chainB_lowers hWF hb))
          (proj_zero_compiles f h_np h0 (chainB_compilesB hb)) (ptrOffset_leafop dstL _ delta) rfl
      · exact leaf_pkg_projoff (ev := fun srcRes evd _ => RExprToEvidence.ptrOffset _ delta srcRes evd)
          h_np h0 (chainB_lowers hWF hb) (chainB_compilesB hb) (hLeaf.1 _) (ptrOffset_ro dstL _ delta) rfl
  | nested hn =>
      rename_i ρ' σ' b q p
      have ih := ptrOffset_pkgL (compProg := compProg) hWF hLeaf dstL (τ := τ) (.proj b (q.append p)) hn delta
      have h_as := readRhsPre_assoc (L := L) (dstL := dstL)
          (rhs1 := RExpr.ptrOffset (τ := τ) (.proj (.proj b q) p) delta)
          (rhs2 := RExpr.ptrOffset (τ := τ) (.proj b (q.append p)) delta) b q p
          (fun r => oseairL.Rhs.PtrOffset (mirliteB.leafKind (mirliteB.placeLayout L (.proj b (q.append p)))) r
            (delta * ((mirliteB.pointeeLayout L (.proj b (q.append p))).size : Int)))
          (fun _ => []) (fun srcRes evd _ => RExprToEvidence.ptrOffset _ delta srcRes evd)
          (fun srcRes evd _ => RExprToEvidence.ptrOffset _ delta srcRes evd)
      refine ValuePkgB.congr
        (fun sM => by simp only [mirliteB.evalRExpr, mirliteB.readCell, placeLayout_assoc,
          resolvePlaceAcc_assoc, mirliteB.pointeeLayout]) (fun cs => ?_) (fun cs => ?_) ih
      · have := (h_as cs).1
        simp only [compileRExprPreChecked, mirliteB.pointeeLayout, placeLayout_assoc] at this ⊢
        exact this
      · have := (h_as cs).2
        simp only [compileRExprPreChecked, mirliteB.pointeeLayout, placeLayout_assoc] at this ⊢
        exact this
termination_by src.depth
decreasing_by all_goals (subst_vars; simp_all [Place.depth]; try omega)

theorem fromExposed_pkgL {Γ : Ctx} {L : mirliteB.LayEnv Γ} {compProg : oseairL.Prog}
    (hWF : PtrPlacesWF L) (hLeaf : LeafWF L) (dstL : BLayout) {τ : LayoutTy}
    (src : Place Γ (LayoutTy.IntL tN)) (h : LeafSrcB src) :
    ValuePkgB compProg L dstL (RExpr.fromExposed (τ := τ) src) := by
  cases h with
  | chain hc => exact fromExposed_pkg hWF dstL hc
  | field f hb =>
      rename_i ρ b
      have h_np := ChainB.not_proj hb
      by_cases h0 : pathOffset L b f = 0
      · exact leaf_pkg_core (ev := fun srcRes evd _ => RExprToEvidence.fromExposed _ srcRes evd)
          (proj_zero_lowers f h_np h0 (chainB_lowers hWF hb))
          (proj_zero_compiles f h_np h0 (chainB_compilesB hb)) (fromExposed_leafop dstL _) rfl
      · exact leaf_pkg_projoff (ev := fun srcRes evd _ => RExprToEvidence.fromExposed _ srcRes evd)
          h_np h0 (chainB_lowers hWF hb) (chainB_compilesB hb) (hLeaf.2 _) (fromExposed_ro dstL _) rfl
  | nested hn =>
      rename_i ρ' σ' b q p
      have ih := fromExposed_pkgL (compProg := compProg) hWF hLeaf dstL (τ := τ) (.proj b (q.append p)) hn
      have h_as := readRhsPre_assoc (L := L) (dstL := dstL)
          (rhs1 := RExpr.fromExposed (τ := τ) (.proj (.proj b q) p))
          (rhs2 := RExpr.fromExposed (τ := τ) (.proj b (q.append p))) b q p
          (oseairL.Rhs.FromExposed (mirliteB.leafKind (mirliteB.placeLayout L (.proj b (q.append p)))))
          (fun _ => []) (fun srcRes evd _ => RExprToEvidence.fromExposed _ srcRes evd)
          (fun srcRes evd _ => RExprToEvidence.fromExposed _ srcRes evd)
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
