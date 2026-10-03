import obseq3.proof.leaffield

/-!
# `exposeAddr` with a field operand

`dst := b.f as usize` for a pointer field `b.f`. At offset zero and for
nested fields the chain skeleton applies through the lowering contract
and congruence. At a nonzero offset the compiled code is the bracket
`Borrow(Shared); ExposeAddr; Die`: the exposure sits between the read and
the `Die`, and moves past it by `sb_die_expose_comm` (a `die` never reads
the exposed set): `projoff_bracket` with the exposure as its permission
transform.
-/

namespace obseq3.proof

open obseq3 obseq3.bytes obseq3.proof
open obseq3.mirlite (MemValue Binding Env PlaceRes)
open obseq3.oseair (Val Register)
open obseq3.compile

theorem exposeAddr_projoff {Γ : Ctx} {L : mirlite.LayEnv Γ} {compProg : oseair.Prog}
    (dstL : BLayout) {ρ σ : LayoutTy} {b : Place Γ ρ} {f : PathTo ρ (LayoutTy.PtrL σ)}
    (h_np : ∀ (σ' : LayoutTy) (bb : Place Γ σ') (q : PathTo σ' ρ), b = bb.proj q → False)
    (h0 : pathOffset L b f ≠ 0) (hb : LowersB L compProg b) (hcb : CompilesB L b)
    (h_len : (mirlite.leafKind (mirlite.placeLayout L (.proj b f))).size = placeSize L (.proj b f)) :
    ValuePkgB compProg L dstL (RExpr.exposeAddr (t := tE) (.proj b f)) := by
  intro ρt sM sA csA h_wf h_tbd h_lbs h_prb h_mem h_alloc h_psim h_pc _h_unmap output h_ev
  -- the source: read the pointer, expose its tag
  simp only [mirlite.evalRExpr] at h_ev
  split at h_ev
  · cases h_ev
  case h_3 => cases h_ev
  rename_i base offset extent size tag perms' h_rc
  simp only [mirlite.EvalResult.ok.injEq] at h_ev
  subst h_ev
  obtain ⟨resolved, permsR, h_res, h_free, h_bnd, h_rd, h_v⟩ := readCell_inv h_rc
  let mk := oseair.Rhs.ExposeAddr (mirlite.leafKind (mirlite.placeLayout L (.proj b f)))
  have h_pre : compileRExprPreChecked L dstL (RExpr.exposeAddr (t := tE) (.proj b f))
      = readRhsPre L dstL (RExpr.exposeAddr (t := tE) (.proj b f)) (.proj b f) mk (fun _ => [])
          (fun srcRes evd _ => RExprToEvidence.exposeAddr _ srcRes evd) := rfl
  -- compile-time
  obtain ⟨outP, h_valP, -, h_prmP⟩ := projoff_compile h_np h0 hcb h_lbs h_res
  obtain ⟨h_run, pOut, h_val, h_store, h_post⟩ :=
    readRhsPre_shapeG (dstL := dstL) (rhs := RExpr.exposeAddr (t := tE) (.proj b f)) (mk := mk)
      (post := fun _ => []) (ev := fun srcRes evd _ => RExprToEvidence.exposeAddr _ srcRes evd) h_valP
  have h_prmR : (CheckedCompilerM.run (readRhsPre L dstL (RExpr.exposeAddr (t := tE) (.proj b f))
      (.proj b f) mk (fun _ => []) (fun srcRes evd _ => RExprToEvidence.exposeAddr _ srcRes evd))
      csA).placeRegMap = csA.placeRegMap := by rw [h_run]; exact h_prmP
  rw [h_pre]
  refine ⟨_, pOut, h_val, h_store, h_post, h_prmR, fun h_code => ?_⟩
  -- the bracket, with the exposure inside it
  obtain ⟨n, s3, q3, vals, g, h_runT, h_pc3, h_mem3, h_g, h_ps, h_tb, h_ld, h_fr, h_nr,
      t', rfl, rfl, h_t⟩ :=
    projoff_bracket (P := fun vals g => ∃ t', g = (fun p => sb_expose p t') ∧
        vals = [Val.Dat (base + offset)] ∧ ρt tag = some t')
      h_np h0 hb hcb h_len h_wf h_tbd h_lbs h_prb h_mem h_alloc h_psim h_pc h_res h_free h_bnd h_rd
      (fun S1 reg ext T pmid hm hl hr hle hrd => by
        obtain ⟨h_rct, h_vs⟩ := readCellThrough_ro h_wf hr hle hm hl h_free h_bnd hrd
        rw [← h_v] at h_vs
        obtain ⟨t', h_w, h_t⟩ := valSim_ptr h_vs
        refine ⟨[Val.Dat (base + offset)], fun p => sb_expose p t', ?_,
          fun _ _ _ _ _ h => sb_die_expose_comm h, t', rfl, rfl, h_t⟩
        simp only [mk, oseair.evalRhs]
        rw [h_rct, h_w]
        rfl)
      h_code
  refine ⟨ρt, n, s3, sM.mem, sb_expose perms' tag, [Val.Dat (base + offset)],
    TagRenameIncr.refl ρt, h_wf, rfl, h_runT, ?_, ?_, ?_, ?_, by rw [h_mem3]; exact h_mem,
    by rw [h_mem3]; exact h_alloc, h_pc3, ?_, ⟨Or.inr ⟨by simp, rfl⟩, trivial⟩⟩
  · rw [h_run]; show csA.nextReg ≤ _ + 1; omega
  · exact LocalBindingSimB.prm_congr (LocalBindingSimB.of_frame h_lbs h_prb h_fr) h_prmR
  · rw [h_g]; exact sb_expose_respects_PermSim h_ps h_wf h_t
  · rw [h_g]
    show TagRenameBounded ρt (sb_expose perms' tag).NextTag (sb_expose q3 t').NextTag
    rw [sb_expose_NextTag, sb_expose_NextTag]; exact h_tb
  · rw [h_run]
    exact StoreStepB.rstore compProg _ _ dstL _ _ h_ld (show _ < _ + 1 by omega)

theorem exposeAddr_pkgL {Γ : Ctx} {L : mirlite.LayEnv Γ} {compProg : oseair.Prog}
    (hWF : PtrPlacesWF L) (hLeaf : LeafWF L) (dstL : BLayout) {σ : LayoutTy}
    (src : Place Γ (LayoutTy.PtrL σ)) (h : LeafSrcB src) :
    ValuePkgB compProg L dstL (RExpr.exposeAddr (t := tE) src) :=
  leaf_pkgL (fun p => RExpr.exposeAddr (t := tE) p)
    (fun p => oseair.Rhs.ExposeAddr (mirlite.leafKind (mirlite.placeLayout L p))) (fun _ => [])
    (fun p srcRes evd _ => RExprToEvidence.exposeAddr p srcRes evd) (fun _ => rfl)
    (fun _ _ _ => by simp only [placeLayout_assoc])
    (fun _ _ _ _ => by simp only [mirlite.evalRExpr, mirlite.readCell, placeLayout_assoc,
      resolvePlaceAcc_assoc])
    (fun p hl hc => leaf_pkg_core (ev := fun srcRes evd _ => RExprToEvidence.exposeAddr p srcRes evd)
      hl hc (exposeAddr_leafop dstL p) rfl)
    (fun _ _ h_np h0 hl hc h_l => exposeAddr_projoff dstL h_np h0 hl hc h_l) hWF
    (fun p => hLeaf.1 p) src h

end obseq3.proof
