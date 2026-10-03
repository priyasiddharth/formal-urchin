import obseq3.proof.leaffield
import obseq3.proof.refslice

/-!
# `refSlice` with a field operand

`dst := &kind *b.f` for a fat-pointer field `b.f`. At offset zero and for
nested fields, `refSlice_core` applies through the lowering contract and
congruence. At a nonzero offset the compiled code is the one-leaf bracket
`Borrow(Shared); Load; Die` followed by the retag `Borrow … none` on the
loaded pointer: `projoff_bracket` with a plain read, then the retag by
`sb_ref_respects_PermSim`, growing the renaming.
-/

namespace obseq3.proof

open obseq3 obseq3.bytes obseq3.proof
open obseq3.mirlite (MemValue Binding Env PlaceRes)
open obseq3.oseair (Val Register)
open obseq3.compile

theorem readCell_what {Γ : Ctx} {L : mirlite.LayEnv Γ} {sM : mirlite.State MSB Γ}
    {σ : LayoutTy} {src : Place Γ σ} {w1 w2 : String} {x : MemValue × MSB.State}
    (h : mirlite.readCell MSB L sM src w1 = .ok x) : mirlite.readCell MSB L sM src w2 = .ok x := by
  obtain ⟨v, p⟩ := x
  obtain ⟨r, pR, h_r, h_f, h_b, h_rd, h_v⟩ := readCell_inv h
  simp only [mirlite.readCell, h_r, h_f, h_b, h_v, if_false, Bool.false_eq_true]
  simp only [PermissionModel.stackedBorrows, h_rd]

/-- The instruction after a fragment: emitting one more instruction puts it
    at the shorter emission's next label. -/
theorem emit_snoc_code (cs : CompilerState) (l : List oseair.Instr) (i : oseair.Instr) :
    (emit cs (l ++ [i])).code (emit cs l).nextLabel = some i ∧
    (emit cs (l ++ [i])).nextLabel = (emit cs l).nextLabel + 1 := by
  refine ⟨?_, by simp [emit]; omega⟩
  have := emit_code_at_new cs (l ++ [i]) (k := l.length) (by simp)
  simp only [emit] at this ⊢
  rw [this]; simp

theorem refSlice_projoff {Γ : Ctx} {L : mirlite.LayEnv Γ} {compProg : oseair.Prog}
    (dstL : BLayout) (kind : RefKind) (prot : Bool) {ρ σ τ : LayoutTy} {b : Place Γ ρ}
    {f : PathTo ρ (LayoutTy.PtrL σ)}
    (h_np : ∀ (σ' : LayoutTy) (bb : Place Γ σ') (q : PathTo σ' ρ), b = bb.proj q → False)
    (h0 : pathOffset L b f ≠ 0) (hb : LowersB L compProg b) (hcb : CompilesB L b)
    (h_len : (mirlite.leafKind (mirlite.placeLayout L (.proj b f))).size = placeSize L (.proj b f)) :
    ValuePkgB compProg L dstL (RExpr.refSlice (τ := τ) kind prot (.proj b f)) := by
  intro ρt sM sA csA h_wf h_tbd h_lbs h_prb h_mem h_alloc h_psim h_pc _h_unmap output h_ev
  -- the source: read the fat pointer (as `ptrCast` would), retag its extent
  simp only [mirlite.evalRExpr] at h_ev
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
  simp only [mirlite.EvalResult.ok.injEq] at h_ev
  subst h_ev
  have h_evC : mirlite.evalRExpr MSB L sM dstL (RExpr.ptrCast (τ := τ) (.proj b f)) =
      .ok { values := [.ptrVal base offset extent size tag], state := { sM with perms := perms' } } := by
    simp only [mirlite.evalRExpr, readCell_what (w2 := "ptr-to-ptr cast") h_rc]
    rfl
  obtain ⟨resolved, permsR, h_res, h_free, h_bnd, h_rd, -⟩ := readCell_inv h_rc
  -- compile-time
  let mk := oseair.Rhs.Load (leafLayout (mirlite.leafKind (mirlite.placeLayout L (.proj b f))))
  let post := fun tmp => [oseair.Instr.Assgn tmp (oseair.Rhs.Borrow kind prot [] none tmp 0)]
  let ev := fun (srcRes : PtrResult) (evd : PlaceToRegEvidence L RefKind.Shared (.proj b f) srcRes)
    (dstPtr : Register) => RExprToEvidence.refSlice (dstPtr := dstPtr) (τ := τ) kind prot (.proj b f) srcRes evd
  have h_pre : compileRExprPreChecked L dstL (RExpr.refSlice (τ := τ) kind prot (.proj b f))
      = readRhsPre L dstL (RExpr.refSlice (τ := τ) kind prot (.proj b f)) (.proj b f) mk post ev := rfl
  obtain ⟨outP, h_valP, h_len1, h_prmP⟩ := projoff_compile h_np h0 hcb h_lbs h_res
  obtain ⟨h_run, pOut, h_val, h_store, h_post⟩ :=
    readRhsPre_shapeG (dstL := dstL) (rhs := RExpr.refSlice (τ := τ) kind prot (.proj b f)) (mk := mk)
      (post := post) (ev := ev) h_valP
  obtain ⟨h_run0, -⟩ :=
    readRhsPre_shapeG (dstL := dstL) (rhs := RExpr.refSlice (τ := τ) kind prot (.proj b f)) (mk := mk)
      (post := fun _ => []) (ev := ev) h_valP
  have h_prmR : (CheckedCompilerM.run (readRhsPre L dstL (RExpr.refSlice (τ := τ) kind prot
      (.proj b f)) (.proj b f) mk post ev) csA).placeRegMap = csA.placeRegMap := by
    rw [h_run]; exact h_prmP
  rw [h_pre]
  refine ⟨_, pOut, h_val, h_store, h_post, h_prmR, fun h_code => ?_⟩
  -- the bracket: a plain read of the pointer leaf
  obtain ⟨n, s3, q3, vals, g, h_runT, h_pc3, h_mem3, h_g, h_ps, h_tb, h_ld, h_fr, h_nr,
      rfl, t', rfl, h_t⟩ :=
    projoff_bracket (P := fun vals g => g = id ∧ ∃ t',
        vals = [Val.Ptr base offset extent size t'] ∧ ρt tag = some t')
      h_np h0 hb hcb h_len h_wf h_tbd h_lbs h_prb h_mem h_alloc h_psim h_pc h_res h_free h_bnd h_rd
      (fun S1 reg ext T pmid hm hl hr hle hrd => by
        obtain ⟨vals, h_ev', h_rel⟩ := (ptrCast_ro (τ := τ) dstL (.proj b f)).target ρt sM S1 reg
          resolved permsR ext T _ pmid h_evC h_res h_wf hm hl hr hle hrd
        obtain ⟨t', rfl, h_t⟩ := ptr_of_storeSim h_rel
        exact ⟨_, id, h_ev', fun _ _ _ _ _ h => h, rfl, t', rfl, h_t⟩)
      h_code
  -- §4 retag the extent through the loaded pointer
  obtain ⟨q, h_ref', h_fresh, h_incr, h_wf', h_tbd', h_psim'⟩ :=
    sb_ref_respects_PermSim h_ps h_wf h_tb h_t h_ref
  subst h_fresh
  have h_freeB' : s3.mem.isFreed base = false := by
    rw [h_mem3]
    simp only [bytes.Mem.isFreed, ← h_alloc.2.2] at h_freeB ⊢
    simpa using h_freeB
  let ld := Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared (.proj b f)) csA).nextReg
  have h_shape : CheckedCompilerM.run (readRhsPre L dstL (RExpr.refSlice (τ := τ) kind prot (.proj b f))
      (.proj b f) mk post ev) csA
      = emit (bumpReg (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared (.proj b f)) csA))
          (([oseair.Instr.Assgn ld (mk outP.result.reg)] ++ cleanupInstrs outP.result.cleanup)
            ++ [oseair.Instr.Assgn ld (oseair.Rhs.Borrow kind prot [] none ld 0)]) := by
    rw [h_run]
  have h_shape0 : CheckedCompilerM.run (readRhsPre L dstL (RExpr.refSlice (τ := τ) kind prot (.proj b f))
      (.proj b f) mk (fun _ => []) ev) csA
      = emit (bumpReg (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared (.proj b f)) csA))
          ([oseair.Instr.Assgn ld (mk outP.result.reg)] ++ cleanupInstrs outP.result.cleanup) := by
    rw [h_run0]; simp only [List.append_nil]; rfl
  have hcs := emit_snoc_code (bumpReg (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared
    (.proj b f)) csA)) ([oseair.Instr.Assgn ld (mk outP.result.reg)] ++ cleanupInstrs outP.result.cleanup)
    (oseair.Instr.Assgn ld (oseair.Rhs.Borrow kind prot [] none ld 0))
  have h_i4 : compProg s3.pc = some (oseair.Instr.Assgn ld (oseair.Rhs.Borrow kind prot [] none ld 0)) := by
    rw [h_shape] at h_code
    refine h_code _ _ ?_ ?_
    · rw [h_pc3, h_shape0, hcs.2]; omega
    · rw [h_pc3, h_shape0]; exact hcs.1
  have h4 := runN_Assgn (s := s3) (vals := [Val.Ptr base (offset + 0) extent size q3.NextTag])
    (s' := { s3 with perms := q }) h_i4
    (by
      simp only [oseair.evalRhs, ld, h_ld, h_freeB', Bool.false_eq_true, if_false, Nat.add_zero,
        PermissionModel.stackedBorrows, h_g, id, h_ref'])
  refine ⟨ρt.extend perms'.NextTag q3.NextTag, n + 1, _, sM.mem, perms'',
    [Val.Ptr base (offset + 0) extent size q3.NextTag], h_incr, h_wf', rfl,
    runN_trans h_runT h4, ?_, ?_, h_psim', h_tbd',
    ByteMemSim.rename_mono h_incr (by rw [h_mem3]; exact h_mem), by rw [h_mem3]; exact h_alloc,
    ?_, ?_, ?_⟩
  · rw [h_shape]; show csA.nextReg ≤ _ + 1; omega
  · refine LocalBindingSimB.prm_congr (LocalBindingSimB.of_frame
      (LocalBindingSimB.rename_mono h_incr h_lbs) h_prb fun r hr => ?_) h_prmR
    have hne : r ≠ ld := RegisterBelow.ne_fresh (RegisterBelow.mono h_nr hr)
    show (s3.reg.insert ld _).lookup r = _
    rw [RegMap.lookup_insert_ne _ _ hne]
    exact h_fr r hr
  · show s3.pc + 1 = _
    rw [h_pc3, h_shape, h_shape0, hcs.2]
  · rw [h_shape]
    exact StoreStepB.rstore compProg _ _ dstL ld _ (RegMap.lookup_insert_self _ _ _)
      (show _ < _ + 1 by omega)
  · refine ⟨Or.inr ⟨by simp, ?_⟩, trivial⟩
    simp only [ValSim, oseair.Val.toMem, oseair.ofMem, MemValSim, idA, Nat.add_zero]
    exact ⟨trivial, trivial, trivial, trivial, TagRenameMap.extend_self _ _ _,
      fun _ _ => ⟨_, rfl⟩⟩

theorem refSlice_pkgL {Γ : Ctx} {L : mirlite.LayEnv Γ} {compProg : oseair.Prog}
    (hWF : PtrPlacesWF L) (hLeaf : LeafWF L) (dstL : BLayout) (kind : RefKind) (prot : Bool)
    {σ τ : LayoutTy} (src : Place Γ (LayoutTy.PtrL σ)) (h : LeafSrcB src) :
    ValuePkgB compProg L dstL (RExpr.refSlice (τ := τ) kind prot src) :=
  leaf_pkgL (fun p => RExpr.refSlice (τ := τ) kind prot p)
    (fun p => oseair.Rhs.Load (leafLayout (mirlite.leafKind (mirlite.placeLayout L p))))
    (fun tmp => [oseair.Instr.Assgn tmp (oseair.Rhs.Borrow kind prot [] none tmp 0)])
    (fun p srcRes evd _ => RExprToEvidence.refSlice kind prot p srcRes evd) (fun _ => rfl)
    (fun _ _ _ => by simp only [placeLayout_assoc])
    (fun _ _ _ _ => by simp only [mirlite.evalRExpr, mirlite.readCell, placeLayout_assoc,
      resolvePlaceAcc_assoc])
    (fun _ hl hc => refSlice_core dstL kind prot hl hc)
    (fun _ _ h_np h0 hl hc h_l => refSlice_projoff dstL kind prot h_np h0 hl hc h_l) hWF
    (fun p => hLeaf.1 p) src h

end obseq3.proof
