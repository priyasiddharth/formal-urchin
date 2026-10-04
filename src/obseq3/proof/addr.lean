import obseq3.proof.leaffield

/-!
# `addr`: a pointer's bytes read as an integer

`dst := p.addr()` (or a pointer-to-integer `transmute`) reads the pointer
place's bytes and decodes them at integer type: the address, with the
provenance stripped and nothing exposed. The compiled code is one `Load`
of those bytes at integer layout, which decodes them the same way, so the
op is read-only and `ro_pkgL` covers every operand shape.
-/

namespace obseq3.proof

open obseq3 obseq3.bytes obseq3.proof
open obseq3.mirlite (MemValue Binding Env PlaceRes)
open obseq3.oseair (Val Register)
open obseq3.compile

theorem readCellAs_inv {Γ : Ctx} {L : mirlite.LayEnv Γ} {sM : mirlite.State MSB Γ}
    {σ : LayoutTy} {src : Place Γ σ} {k : Scalar} {what : String} {v : MemValue}
    {perms' : MSB.State}
    (h : mirlite.readCellAs MSB L sM src k what = .ok (v, perms')) :
    ∃ resolved permsR, mirlite.resolvePlaceAcc MSB L sM src = .ok (resolved, permsR) ∧
      ¬ sM.mem.isFreed resolved.allocBase = true ∧
      ¬ (resolved.addr + k.sizeB > resolved.allocBase + resolved.allocSizeB) ∧
      sb_read permsR resolved.addr k.sizeB resolved.tag = .ok perms' ∧
      v = mirlite.decodeV k (sM.mem.read resolved.addr k.sizeB) := by
  simp only [mirlite.readCellAs] at h
  cases h_r : mirlite.resolvePlaceAcc MSB L sM src with
  | error e => simp [h_r] at h
  | ok rr =>
  obtain ⟨resolved, permsR⟩ := rr
  simp only [h_r] at h
  split at h
  · cases h
  rename_i h_free
  split at h
  · cases h
  rename_i h_bnd
  split at h
  · cases h
  rename_i p hp
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨resolved, permsR, rfl, h_free, h_bnd, hp, rfl⟩

theorem scalar_int_sizeB (nB : Nat) : (Scalar.int nB).sizeB = nB := rfl

theorem readL_int (m : bytes.Mem) (a nB : Nat) :
    mirlite.readL m a (.int nB) = [mirlite.decodeV (.int nB) (m.read a nB)] :=
  readL_leafLayout m a (.int nB)

theorem addr_leafop {Γ : Ctx} {L : mirlite.LayEnv Γ} (dstL : BLayout) {σ : LayoutTy}
    (src : Place Γ (LayoutTy.PtrL σ)) :
    LeafOpB L dstL (RExpr.addr (t := tE) src) src
      (oseair.Rhs.Load (.int (mirlite.leafKind (mirlite.placeLayout L src)).sizeB)) where
  resolves sM output h := by
    simp only [mirlite.evalRExpr] at h
    split at h
    · cases h
    · rename_i h_rc
      obtain ⟨r, p, h_r, -⟩ := readCellAs_inv h_rc
      exact ⟨_, h_r⟩
  step ρt sM s1 reg resolved permsR ext tres output h h_res hwf h_tbd h_psim h_mem h_lock
      h_reg h_rt h_le := by
    simp only [mirlite.evalRExpr] at h
    split at h
    · cases h
    · rename_i v perms' h_rc
      split at h
      · cases h
      rename_i h_def
      simp only [mirlite.EvalResult.ok.injEq] at h
      subst h
      obtain ⟨r', p', h_r', h_free, h_bnd, h_rd, h_v⟩ := readCellAs_inv h_rc
      simp only [scalar_int_sizeB] at h_v h_bnd h_rd
      obtain ⟨rfl, rfl⟩ := resolve_eq h_res h_r'
      obtain ⟨p2, h_rd', h_psim2⟩ := sb_read_respects_PermSim h_psim hwf h_rt h_rd
      have h_vs := decodeV_sim hwf (.int (mirlite.leafKind (mirlite.placeLayout L src)).sizeB)
        (h_mem.read resolved.addr (mirlite.leafKind (mirlite.placeLayout L src)).sizeB)
      rw [← h_v] at h_vs
      obtain ⟨h_defT, h_relS⟩ := readL_rel (vs := [v])
        (ws := [mirlite.decodeV (.int (mirlite.leafKind (mirlite.placeLayout L src)).sizeB)
          (s1.mem.read resolved.addr (mirlite.leafKind (mirlite.placeLayout L src)).sizeB)])
        (show ListRel _ [v] [_] from ⟨h_vs, trivial⟩)
        (by simp only [List.any_cons, List.any_nil, Bool.or_false]
            exact Bool.eq_false_iff.mpr h_def)
      have hA : resolved.allocBase + (resolved.addr - resolved.allocBase) = resolved.addr :=
        Nat.add_sub_cancel' h_le
      have h_freeT : s1.mem.isFreed resolved.allocBase = false := by
        simp only [bytes.Mem.isFreed, ← h_lock.2.2] at h_free ⊢
        simpa using h_free
      refine ⟨_, p2, perms', ?_, rfl, h_psim2, ?_, h_relS⟩
      · simp only [oseair.evalRhs, h_reg, hA, h_freeT, Bool.false_eq_true, if_false,
          BLayout.sizeB, h_bnd, PermissionModel.stackedBorrows, h_rd', readL_int,
          List.map_cons, List.map_nil]
        have h_defT' : ([oseair.ofMem (mirlite.decodeV
            (.int (mirlite.leafKind (mirlite.placeLayout L src)).sizeB)
            (s1.mem.read resolved.addr (mirlite.leafKind (mirlite.placeLayout L src)).sizeB))].any
            fun v => v == Val.Undef) = false := h_defT
        rw [h_defT']
        rfl
      · rw [sb_read_NextTag h_rd, sb_read_NextTag h_rd']; exact h_tbd

theorem addr_ro {Γ : Ctx} {L : mirlite.LayEnv Γ} (dstL : BLayout) {σ : LayoutTy}
    (src : Place Γ (LayoutTy.PtrL σ)) :
    ReadOnlyOpB L dstL (RExpr.addr (t := tE) src) src
      (oseair.Rhs.Load (.int (mirlite.leafKind (mirlite.placeLayout L src)).sizeB)) where
  source sM output h := by
    simp only [mirlite.evalRExpr] at h
    split at h
    · cases h
    · rename_i v perms' h_rc
      split at h
      · cases h
      simp only [mirlite.EvalResult.ok.injEq] at h
      subst h
      obtain ⟨r, p, h_r, h_free, h_bnd, h_rd, -⟩ := readCellAs_inv h_rc
      exact ⟨r, p, perms', h_r, h_free, h_bnd, h_rd, rfl⟩
  target ρt sM s1 reg resolved permsR ext T output pmid h h_res hwf h_mem h_lock h_reg h_le h_rdT := by
    simp only [mirlite.evalRExpr] at h
    split at h
    · cases h
    · rename_i v perms' h_rc
      split at h
      · cases h
      rename_i h_def
      simp only [mirlite.EvalResult.ok.injEq] at h
      subst h
      obtain ⟨r', p', h_r', h_free, h_bnd, h_rd, h_v⟩ := readCellAs_inv h_rc
      simp only [scalar_int_sizeB] at h_v h_bnd h_rd
      obtain ⟨rfl, rfl⟩ := resolve_eq h_res h_r'
      have h_vs := decodeV_sim hwf (.int (mirlite.leafKind (mirlite.placeLayout L src)).sizeB)
        (h_mem.read resolved.addr (mirlite.leafKind (mirlite.placeLayout L src)).sizeB)
      rw [← h_v] at h_vs
      obtain ⟨h_defT, h_relS⟩ := readL_rel (vs := [v])
        (ws := [mirlite.decodeV (.int (mirlite.leafKind (mirlite.placeLayout L src)).sizeB)
          (s1.mem.read resolved.addr (mirlite.leafKind (mirlite.placeLayout L src)).sizeB)])
        (show ListRel _ [v] [_] from ⟨h_vs, trivial⟩)
        (by simp only [List.any_cons, List.any_nil, Bool.or_false]
            exact Bool.eq_false_iff.mpr h_def)
      have hA : resolved.allocBase + (resolved.addr - resolved.allocBase) = resolved.addr :=
        Nat.add_sub_cancel' h_le
      have h_freeT : s1.mem.isFreed resolved.allocBase = false := by
        simp only [bytes.Mem.isFreed, ← h_lock.2.2] at h_free ⊢
        simpa using h_free
      refine ⟨_, ?_, h_relS⟩
      simp only [oseair.evalRhs, h_reg, hA, h_freeT, Bool.false_eq_true, if_false,
        BLayout.sizeB, h_bnd, PermissionModel.stackedBorrows, h_rdT, readL_int,
        List.map_cons, List.map_nil]
      have h_defT' : ([oseair.ofMem (mirlite.decodeV
          (.int (mirlite.leafKind (mirlite.placeLayout L src)).sizeB)
          (s1.mem.read resolved.addr (mirlite.leafKind (mirlite.placeLayout L src)).sizeB))].any
          fun v => v == Val.Undef) = false := h_defT
      rw [h_defT']
      rfl

theorem addr_pkgL {Γ : Ctx} {L : mirlite.LayEnv Γ} {compProg : oseair.Prog}
    (hWF : PtrPlacesWF L) (hLeaf : LeafWF L) (dstL : BLayout) {σ : LayoutTy}
    (src : Place Γ (LayoutTy.PtrL σ)) (h : LeafSrcB src) :
    ValuePkgB compProg L dstL (RExpr.addr (t := tE) src) :=
  ro_pkgL (fun p => RExpr.addr (t := tE) p)
    (fun p => oseair.Rhs.Load (.int (mirlite.leafKind (mirlite.placeLayout L p)).sizeB))
    (fun p srcRes evd _ => RExprToEvidence.addr p srcRes evd) (fun _ => rfl)
    (fun _ _ _ => by simp only [placeLayout_assoc])
    (fun _ _ _ _ => by simp only [mirlite.evalRExpr, mirlite.readCellAs, placeLayout_assoc,
      resolvePlaceAcc_assoc])
    (fun p => addr_leafop dstL p) (fun p => addr_ro dstL p) hWF (fun p => hLeaf.1 p) src h

end obseq3.proof
