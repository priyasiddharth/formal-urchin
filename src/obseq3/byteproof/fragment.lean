import obseq3.byteproof.program
import obseq3.byteproof.leaffield
import obseq3.byteproof.refslicefield
import obseq3.byteproof.exposefield
import obseq3.byteproof.const_write

/-!
# The proved fragment

Which statements the byte-level proof covers, as predicates, and the
lemma turning each into a `StmtSimB` — so `compileB_correct_fragment` is
the program theorem for every program in the fragment. The predicates
turn out to be total (`coverage.lean`): every statement is in the
fragment.
-/

namespace obseq3.byteproof

open obseq3 obseq3.bytes obseq3.proof
open obseq3.mirlite (MemValue Binding Env PlaceRes)
open obseq3.oseair (Val Register)
open obseq3.compileB

/-- Places that can be borrowed (`ref`, `move`): a local, a deref chain,
    a field of a chain. -/
inductive BorrowSrcB {Γ : Ctx} : {τ : LayoutTy} → Place Γ τ → Prop
  | local {τ : LayoutTy} (loc : Local Γ τ) : BorrowSrcB (.local loc)
  | deref {σ : LayoutTy} {q : Place Γ (LayoutTy.PtrL σ)} :
      ChainB (.deref q) → BorrowSrcB (.deref q)
  | field {ρ τ : LayoutTy} {b : Place Γ ρ} (f : PathTo ρ τ) : ChainB b → BorrowSrcB (.proj b f)
  | nested {ρ σ τ : LayoutTy} {b : Place Γ ρ} {q : PathTo ρ σ} {p : PathTo σ τ} :
      BorrowSrcB (.proj b (q.append p)) → BorrowSrcB (.proj (.proj b q) p)

/-! ## Congruences for nested projections -/

theorem ref_assoc_pre {Γ : Ctx} {L : mirliteB.LayEnv Γ} {dstL : BLayout} {ρ σ τ : LayoutTy}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (b : Place Γ ρ) (q : PathTo ρ σ) (p : PathTo σ τ) (cs : CompilerState) :
    CheckedCompilerM.run (compileRExprPreChecked L dstL (RExpr.ref kind prot mask (.proj (.proj b q) p))) cs
      = CheckedCompilerM.run
          (compileRExprPreChecked L dstL (RExpr.ref kind prot mask (.proj b (q.append p)))) cs ∧
    ∀ p2, CheckedCompilerM.value
        (compileRExprPreChecked L dstL (RExpr.ref kind prot mask (.proj b (q.append p)))) cs = .ok p2 →
      ∃ p1, CheckedCompilerM.value
          (compileRExprPreChecked L dstL (RExpr.ref kind prot mask (.proj (.proj b q) p))) cs = .ok p1 ∧
        (∀ d, p1.store d = p2.store d) ∧ p1.postCleanup = p2.postCleanup := by
  obtain ⟨h_run, h_val⟩ := placeToBorrowReg_assoc (L := L) kind prot
    (mirliteB.maskBytes (mirliteB.placeLayout L (.proj b (q.append p))) mask) b q p cs
  simp only [compileRExprPreChecked, CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    placeLayout_assoc, CheckedCompilerM.run_pure, CheckedCompilerM.value_pure]
  rw [h_run]
  revert h_val
  cases CheckedCompilerM.value (placeToBorrowRegChecked L kind prot
      (mirliteB.maskBytes (mirliteB.placeLayout L (.proj b (q.append p))) mask) (.proj (.proj b q) p)) cs <;>
    cases CheckedCompilerM.value (placeToBorrowRegChecked L kind prot
      (mirliteB.maskBytes (mirliteB.placeLayout L (.proj b (q.append p))) mask) (.proj b (q.append p))) cs <;>
    intro h_val <;> simp only [Except.map, Except.ok.injEq, Except.error.injEq, reduceCtorEq] at h_val
  all_goals first
    | (refine ⟨rfl, fun p2 h2 => ?_⟩; cases h2; done)
    | (refine ⟨rfl, fun p2 h2 => ?_⟩
       simp only [Except.ok.injEq] at h2
       subst h2
       refine ⟨_, rfl, fun d => ?_, rfl⟩
       simp [h_val])

theorem move_assoc_pre {Γ : Ctx} {L : mirliteB.LayEnv Γ} {dstL : BLayout} {ρ σ τ : LayoutTy}
    (b : Place Γ ρ) (q : PathTo ρ σ) (p : PathTo σ τ) (cs : CompilerState) :
    CheckedCompilerM.run (compileRExprPreChecked L dstL (RExpr.move (.proj (.proj b q) p))) cs
      = CheckedCompilerM.run (compileRExprPreChecked L dstL (RExpr.move (.proj b (q.append p)))) cs ∧
    ∀ p2, CheckedCompilerM.value
        (compileRExprPreChecked L dstL (RExpr.move (.proj b (q.append p)))) cs = .ok p2 →
      ∃ p1, CheckedCompilerM.value
          (compileRExprPreChecked L dstL (RExpr.move (.proj (.proj b q) p))) cs = .ok p1 ∧
        (∀ d, p1.store d = p2.store d) ∧ p1.postCleanup = p2.postCleanup := by
  obtain ⟨h_run, h_val⟩ := placeToBorrowReg_assoc (L := L) RefKind.Mut false [] b q p cs
  simp only [compileRExprPreChecked, CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    placeLayout_assoc, CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure]
  rw [h_run]
  revert h_val
  cases CheckedCompilerM.value (placeToBorrowRegChecked L RefKind.Mut false [] (.proj (.proj b q) p)) cs <;>
    cases CheckedCompilerM.value (placeToBorrowRegChecked L RefKind.Mut false [] (.proj b (q.append p))) cs <;>
    intro h_val <;> simp only [Except.map, Except.ok.injEq, Except.error.injEq, reduceCtorEq] at h_val
  all_goals first
    | (refine ⟨rfl, fun p2 h2 => ?_⟩; cases h2; done)
    | (refine ⟨by simp only [h_val], fun p2 h2 => ?_⟩
       simp only [Except.ok.injEq] at h2
       subst h2
       refine ⟨_, rfl, fun d => ?_, rfl⟩
       simp)

theorem BorrowSrcB.ref_pkg {Γ : Ctx} {L : mirliteB.LayEnv Γ} {compProg : oseairL.Prog}
    (hWF : PtrPlacesWF L) (dstL : BLayout) (kind : RefKind) (prot : Bool) (mask : List Bool)
    {τ : LayoutTy} {src : Place Γ τ} (h : BorrowSrcB src) :
    ValuePkgB compProg L dstL (RExpr.ref kind prot mask src) := by
  induction h with
  | «local» loc => exact ref_local_pkg hWF loc dstL kind prot mask
  | deref hc =>
      exact ref_pkg_core (borrow_deref_shape _) (borrow_deref_res _)
        (chainB_lowers hWF hc) (chainB_compilesB hc) dstL kind prot mask
  | field f hc =>
      exact ref_pkg_core (borrow_proj_shape f (ChainB.not_proj hc)) (borrow_proj_res f)
        (chainB_lowers hWF hc) (chainB_compilesB hc) dstL kind prot mask
  | nested _ ih =>
      rename_i b q p _
      exact ValuePkgB.congr
        (fun sM => by simp only [mirliteB.evalRExpr, placeLayout_assoc, resolvePlaceAcc_assoc])
        (fun cs => (ref_assoc_pre kind prot mask b q p cs).1)
        (fun cs => (ref_assoc_pre kind prot mask b q p cs).2) ih

theorem BorrowSrcB.move_pkg {Γ : Ctx} {L : mirliteB.LayEnv Γ} {compProg : oseairL.Prog}
    (hWF : PtrPlacesWF L) (dstL : BLayout) {τ : LayoutTy} {src : Place Γ τ} (h : BorrowSrcB src) :
    ValuePkgB compProg L dstL (RExpr.move src) := by
  induction h with
  | «local» loc => exact move_local_pkg hWF loc dstL
  | deref hc =>
      exact move_pkg_core (borrow_deref_shape _) (borrow_deref_res _)
        (chainB_lowers hWF hc) (chainB_compilesB hc) dstL
  | field f hc =>
      exact move_pkg_core (borrow_proj_shape f (ChainB.not_proj hc)) (borrow_proj_res f)
        (chainB_lowers hWF hc) (chainB_compilesB hc) dstL
  | nested _ ih =>
      rename_i b q p _
      exact ValuePkgB.congr
        (fun sM => by simp only [mirliteB.evalRExpr, placeLayout_assoc, resolvePlaceAcc_assoc])
        (fun cs => (move_assoc_pre b q p cs).1)
        (fun cs => (move_assoc_pre b q p cs).2) ih

theorem StmtSimB.congr {Γ : Ctx} {L : mirliteB.LayEnv Γ} {compProg : oseairL.Prog}
    {s1 s2 : Stmt Γ}
    (h_run : ∀ cs, CheckedCompilerM.run (compileStmtChecked L s1) cs
      = CheckedCompilerM.run (compileStmtChecked L s2) cs)
    (h_step : ∀ s, mirliteB.stepStmt MSB L s s1 = mirliteB.stepStmt MSB L s s2)
    (h : StmtSimB L compProg s2) : StmtSimB L compProg s1 := by
  intro ρt s_mir s_mir' s_osea cs h_inv h_code h_st
  rw [h_run] at h_code ⊢
  rw [h_step] at h_st
  exact h ρt s_mir s_mir' s_osea cs h_inv h_code h_st

/-- The rvalues covered, with their operand shapes. -/
inductive RhsB {Γ : Ctx} : {τ : LayoutTy} → RExpr Γ τ → Prop
  | constInit {t : IntTy} (v : Word) : RhsB (.constInit (t := t) v)
  | uninit {τ : LayoutTy} : RhsB (τ := τ) .uninit
  | copy {τ : LayoutTy} {src : Place Γ τ} : ReadSrcB src → RhsB (.copy src)
  | move {τ : LayoutTy} {src : Place Γ τ} : BorrowSrcB src → RhsB (.move src)
  | ref {τ : LayoutTy} {src : Place Γ τ} (kind : RefKind) (prot : Bool) (mask : List Bool) :
      BorrowSrcB src → RhsB (.ref kind prot mask src)
  | ptrCast {σ τ : LayoutTy} {src : Place Γ (LayoutTy.PtrL σ)} :
      LeafSrcB src → RhsB (.ptrCast (τ := τ) src)
  | ptrOffset {σ τ : LayoutTy} {src : Place Γ (LayoutTy.PtrL σ)} (delta : Int) :
      LeafSrcB src → RhsB (.ptrOffset (τ := τ) src delta)
  | refSlice {σ τ : LayoutTy} {src : Place Γ (LayoutTy.PtrL σ)} (kind : RefKind)
      (prot : Bool) : LeafSrcB src → RhsB (.refSlice (τ := τ) kind prot src)
  | exposeAddr {σ : LayoutTy} {t : IntTy} {src : Place Γ (LayoutTy.PtrL σ)} :
      LeafSrcB src → RhsB (.exposeAddr (t := t) src)
  | fromExposed {τ : LayoutTy} {t : IntTy} {src : Place Γ (LayoutTy.IntL t)} :
      LeafSrcB src → RhsB (.fromExposed (τ := τ) src)
  | sliceLen {σ : LayoutTy} {t : IntTy} {src : Place Γ (LayoutTy.PtrL σ)} :
      ReadSrcB src → RhsB (.sliceLen (t := t) src)
  | subSlice {σ : LayoutTy} {src : Place Γ (LayoutTy.PtrL σ)}
      {tl th : IntTy} {lo : Place Γ (LayoutTy.IntL tl)} {hi : Place Γ (LayoutTy.IntL th)} :
      ReadSrcB src → ReadSrcB lo → ReadSrcB hi → RhsB (.subSlice src lo hi)
  | allocConst {τ : LayoutTy} (n : Nat) : RhsB (.alloc (τ := τ) (.const n))
  | allocDyn {τ : LayoutTy} {t : IntTy} {p : Place Γ (LayoutTy.IntL t)} :
      ReadSrcB p → RhsB (.alloc (τ := τ) (.fromPlace p))
  | binOp (op : BinOp) {ta tb tr : IntTy} {a : Place Γ (LayoutTy.IntL ta)}
      {b : Place Γ (LayoutTy.IntL tb)} :
      ReadSrcB a → ReadSrcB b → RhsB (.binOp (tr := tr) op a b)

theorem RhsB.pkg {Γ : Ctx} {L : mirliteB.LayEnv Γ} {compProg : oseairL.Prog}
    (hWF : PtrPlacesWF L) (hLeaf : LeafWF L) {τ : LayoutTy} {rhs : RExpr Γ τ} (h : RhsB rhs)
    (dstL : BLayout) :
    ValuePkgB compProg L dstL rhs := by
  cases h with
  | constInit v => exact constInit_pkg dstL v
  | uninit => exact uninit_pkg dstL
  | copy h => exact copy_pkgR hWF dstL h
  | move h => exact h.move_pkg hWF dstL
  | ref kind prot mask h => exact h.ref_pkg hWF dstL kind prot mask
  | ptrCast h => exact ptrCast_pkgL hWF hLeaf dstL _ h
  | ptrOffset delta h => exact ptrOffset_pkgL hWF hLeaf dstL _ h delta
  | refSlice kind prot h => exact refSlice_pkgL hWF hLeaf dstL kind prot _ h
  | exposeAddr h => exact exposeAddr_pkgL hWF hLeaf dstL _ h
  | fromExposed h => exact fromExposed_pkgL hWF hLeaf dstL _ h
  | sliceLen h => exact sliceLen_pkg hWF dstL h
  | subSlice h1 h2 h3 => exact subSlice_pkg hWF dstL h1 h2 h3
  | allocConst n => exact alloc_const_pkg dstL n
  | allocDyn h => exact alloc_dyn_pkg hWF dstL h
  | binOp op ha hb => exact binOp_pkg hWF dstL op ha hb

/-- The destinations covered. -/
inductive DstB {Γ : Ctx} : {τ : LayoutTy} → Place Γ τ → Prop
  | local {τ : LayoutTy} (loc : Local Γ τ) : DstB (.local loc)
  | deref {τ : LayoutTy} {P : Place Γ (LayoutTy.PtrL τ)} :
      ChainB (.deref P) → DstB (.deref P)
  | projLocal {ρ τ : LayoutTy} (loc : Local Γ ρ) (f : PathTo ρ τ) : DstB (.proj (.local loc) f)
  | projDeref {ρ τ : LayoutTy} {P : Place Γ (LayoutTy.PtrL ρ)} (f : PathTo ρ τ) :
      ChainB (.deref P) → DstB (.proj (.deref P) f)

/-- The statements covered. -/
inductive StmtB0 {Γ : Ctx} : Stmt Γ → Prop
  | assign {τ : LayoutTy} {dst : Place Γ τ} {rhs : RExpr Γ τ} :
      DstB dst → RhsB rhs → StmtB0 (.assign dst rhs)
  | pushProtectors : StmtB0 .pushProtectors
  | popProtectors : StmtB0 .popProtectors
  | dealloc {σ : LayoutTy} {dst : Place Γ (LayoutTy.PtrL σ)} :
      ReadSrcB dst → StmtB0 (.dealloc dst)
  /-- `x.f.g := rhs` is `x.(f ++ g) := rhs` on both machines. -/
  | nested {ρ σ τ : LayoutTy} {b : Place Γ ρ} {q : PathTo ρ σ} {p : PathTo σ τ} {rhs : RExpr Γ τ} :
      StmtB0 (.assign (.proj b (q.append p)) rhs) → StmtB0 (.assign (.proj (.proj b q) p) rhs)

theorem StmtB0.sim {Γ : Ctx} {L : mirliteB.LayEnv Γ} {compProg : oseairL.Prog}
    (hWF : PtrPlacesWF L) (hLeaf : LeafWF L) {stmt : Stmt Γ} (h : StmtB0 stmt) :
    StmtSimB L compProg stmt := by
  induction h with
  | nested _ ih =>
      rename_i b q p rhs _
      exact StmtSimB.congr (fun cs => compileStmt_assign_assoc b q p rhs cs)
        (fun s => stepStmt_assign_assoc b q p rhs s) ih
  | assign hd hr =>
      intro ρt s_mir s_mir' s_osea cs h_inv h_code h_step
      cases hd with
      | «local» loc =>
          cases h_env : s_mir.env.lookup loc with
          | none =>
              exact storereg_localfresh_simB compProg (hr.pkg hWF hLeaf _) h_inv h_code h_env h_step
          | some b =>
              exact storereg_local_simB compProg (hr.pkg hWF hLeaf _) h_inv h_code h_env h_step
      | deref hc =>
          exact storereg_lowered_simB compProg (chainB_lowers hWF hc)
            (fun s1 h_prep => by
              simp only [mirliteB.preparePlaceAssign] at h_prep
              split at h_prep
              · rename_i r h_r
                exact ⟨(mirliteB.Result.ok.inj h_prep).symm, r, h_r⟩
              · simp [mirliteB.allocateRoot] at h_prep)
            (hr.pkg hWF hLeaf _) h_inv h_code h_step
      | projLocal loc f =>
          cases h_env : s_mir.env.lookup loc with
          | none =>
              exact storereg_projlocalfresh_simB compProg hWF (hr.pkg hWF hLeaf _) h_inv h_code h_env
                h_step
          | some b =>
              exact storereg_projlocal_simB compProg hWF h_env (hr.pkg hWF hLeaf _) h_inv h_code h_step
      | projDeref f hc =>
          exact storereg_proj_simB compProg (fun _ _ _ h => by cases h) (chainB_lowers hWF hc)
            (fun s1 h_prep => by
              simp only [mirliteB.preparePlaceAssign] at h_prep
              split at h_prep
              · rename_i r h_r
                exact ⟨(mirliteB.Result.ok.inj h_prep).symm, r, h_r⟩
              · simp [mirliteB.allocateRoot] at h_prep)
            (hr.pkg hWF hLeaf _) h_inv h_code h_step
  | pushProtectors =>
      intro ρt s_mir s_mir' s_osea cs h_inv h_code h_step
      exact pushProt_simB compProg h_inv h_code h_step
  | popProtectors =>
      intro ρt s_mir s_mir' s_osea cs h_inv h_code h_step
      exact popProt_simB compProg h_inv h_code h_step
  | dealloc hd =>
      intro ρt s_mir s_mir' s_osea cs h_inv h_code h_step
      exact dealloc_simB compProg hWF hd h_inv h_code h_step

end obseq3.byteproof
