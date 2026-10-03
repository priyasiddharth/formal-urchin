import obseq3.byteproof.program
import obseq3.byteproof.const_write

/-!
# The proved fragment

Which statements the byte-level proof covers, as predicates, and the
lemma turning each into a `StmtSimB` — so `compileB_correct_fragment` is
the program theorem for every program in the fragment. Not yet covered:
`assignIf`, nested projections (`x.f.g`), derefs of non-chain places, and
the one-leaf rvalues / `refSlice` with a FIELD operand.
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
  | deref {σ : LayoutTy} {q : Place Γ (obseq.LayoutTy.PtrL σ)} :
      PtrChain (.deref q) → BorrowSrcB (.deref q)
  | field {ρ τ : LayoutTy} {b : Place Γ ρ} (f : PathTo ρ τ) : PtrChain b → BorrowSrcB (.proj b f)
  | nested {ρ σ τ : LayoutTy} {b : Place Γ ρ} {q : PathTo ρ σ} {p : PathTo σ τ} :
      BorrowSrcB (.proj b (q.append p)) → BorrowSrcB (.proj (.proj b q) p)

/-! ## Congruences for nested projections -/

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
  | deref hc => exact ref_deref_pkg hWF hc dstL kind prot mask
  | field f hc => exact ref_proj_pkg hWF f hc dstL kind prot mask
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
  | deref hc => exact move_deref_pkg hWF hc dstL
  | field f hc => exact move_proj_pkg hWF f hc dstL
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
  | constInit (v : Word) : RhsB (.constInit v)
  | uninit {τ : LayoutTy} : RhsB (τ := τ) .uninit
  | copy {τ : LayoutTy} {src : Place Γ τ} : ReadSrcB src → RhsB (.copy src)
  | move {τ : LayoutTy} {src : Place Γ τ} : BorrowSrcB src → RhsB (.move src)
  | ref {τ : LayoutTy} {src : Place Γ τ} (kind : RefKind) (prot : Bool) (mask : List Bool) :
      BorrowSrcB src → RhsB (.ref kind prot mask src)
  | ptrCast {σ τ : LayoutTy} {src : Place Γ (obseq.LayoutTy.PtrL σ)} :
      PtrChain src → RhsB (.ptrCast (τ := τ) src)
  | ptrOffset {σ τ : LayoutTy} {src : Place Γ (obseq.LayoutTy.PtrL σ)} (delta : Int) :
      PtrChain src → RhsB (.ptrOffset (τ := τ) src delta)
  | refSlice {σ τ : LayoutTy} {src : Place Γ (obseq.LayoutTy.PtrL σ)} (kind : RefKind)
      (prot : Bool) : PtrChain src → RhsB (.refSlice (τ := τ) kind prot src)
  | exposeAddr {σ : LayoutTy} {src : Place Γ (obseq.LayoutTy.PtrL σ)} :
      PtrChain src → RhsB (.exposeAddr src)
  | fromExposed {τ : LayoutTy} {src : Place Γ obseq.LayoutTy.NatL} :
      PtrChain src → RhsB (.fromExposed (τ := τ) src)
  | sliceLen {σ : LayoutTy} {src : Place Γ (obseq.LayoutTy.PtrL σ)} :
      ReadSrcB src → RhsB (.sliceLen src)
  | subSlice {σ : LayoutTy} {src : Place Γ (obseq.LayoutTy.PtrL σ)}
      {lo hi : Place Γ obseq.LayoutTy.NatL} :
      ReadSrcB src → ReadSrcB lo → ReadSrcB hi → RhsB (.subSlice src lo hi)
  | allocConst {τ : LayoutTy} (n : Nat) : RhsB (.alloc (τ := τ) (.const n))
  | allocDyn {τ : LayoutTy} {p : Place Γ obseq.LayoutTy.NatL} :
      ReadSrcB p → RhsB (.alloc (τ := τ) (.fromPlace p))
  | binOp (op : BinOp) {a b : Place Γ obseq.LayoutTy.NatL} :
      ReadSrcB a → ReadSrcB b → RhsB (.binOp op a b)

theorem RhsB.pkg {Γ : Ctx} {L : mirliteB.LayEnv Γ} {compProg : oseairL.Prog}
    (hWF : PtrPlacesWF L) {τ : LayoutTy} {rhs : RExpr Γ τ} (h : RhsB rhs) (dstL : BLayout) :
    ValuePkgB compProg L dstL rhs := by
  cases h with
  | constInit v => exact constInit_pkg dstL v
  | uninit => exact uninit_pkg dstL
  | copy h => exact copy_pkgR hWF dstL h
  | move h => exact h.move_pkg hWF dstL
  | ref kind prot mask h => exact h.ref_pkg hWF dstL kind prot mask
  | ptrCast h => exact ptrCast_pkg hWF dstL h
  | ptrOffset delta h => exact ptrOffset_pkg hWF dstL h delta
  | refSlice kind prot h => exact refSlice_pkg hWF dstL kind prot h
  | exposeAddr h => exact exposeAddr_pkg hWF dstL h
  | fromExposed h => exact fromExposed_pkg hWF dstL h
  | sliceLen h => exact sliceLen_pkg hWF dstL h
  | subSlice h1 h2 h3 => exact subSlice_pkg hWF dstL h1 h2 h3
  | allocConst n => exact alloc_const_pkg dstL n
  | allocDyn h => exact alloc_dyn_pkg hWF dstL h
  | binOp op ha hb => exact binOp_pkg hWF dstL op ha hb

/-- The destinations covered. -/
inductive DstB {Γ : Ctx} : {τ : LayoutTy} → Place Γ τ → Prop
  | local {τ : LayoutTy} (loc : Local Γ τ) : DstB (.local loc)
  | deref {τ : LayoutTy} {P : Place Γ (obseq.LayoutTy.PtrL τ)} :
      PtrChain (.deref P) → DstB (.deref P)
  | projLocal {ρ τ : LayoutTy} (loc : Local Γ ρ) (f : PathTo ρ τ) : DstB (.proj (.local loc) f)
  | projDeref {ρ τ : LayoutTy} {P : Place Γ (obseq.LayoutTy.PtrL ρ)} (f : PathTo ρ τ) :
      PtrChain (.deref P) → DstB (.proj (.deref P) f)

/-- The statements covered. -/
inductive StmtB {Γ : Ctx} : Stmt Γ → Prop
  | assign {τ : LayoutTy} {dst : Place Γ τ} {rhs : RExpr Γ τ} :
      DstB dst → RhsB rhs → StmtB (.assign dst rhs)
  | pushProtectors : StmtB .pushProtectors
  | popProtectors : StmtB .popProtectors
  | dealloc {σ : LayoutTy} {dst : Place Γ (obseq.LayoutTy.PtrL σ)} :
      ReadSrcB dst → StmtB (.dealloc dst)
  /-- `x.f.g := rhs` is `x.(f ++ g) := rhs` on both machines. -/
  | nested {ρ σ τ : LayoutTy} {b : Place Γ ρ} {q : PathTo ρ σ} {p : PathTo σ τ} {rhs : RExpr Γ τ} :
      StmtB (.assign (.proj b (q.append p)) rhs) → StmtB (.assign (.proj (.proj b q) p) rhs)

theorem StmtB.sim {Γ : Ctx} {L : mirliteB.LayEnv Γ} {compProg : oseairL.Prog}
    (hWF : PtrPlacesWF L) {stmt : Stmt Γ} (h : StmtB stmt) : StmtSimB L compProg stmt := by
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
              exact storereg_localfresh_simB compProg (hr.pkg hWF _) h_inv h_code h_env h_step
          | some b =>
              exact storereg_local_simB compProg (hr.pkg hWF _) h_inv h_code h_env h_step
      | deref hc =>
          exact storereg_chaindst_simB compProg hWF hc (hr.pkg hWF _) h_inv h_code h_step
      | projLocal loc f =>
          cases h_env : s_mir.env.lookup loc with
          | none =>
              exact storereg_projlocalfresh_simB compProg hWF (hr.pkg hWF _) h_inv h_code h_env
                h_step
          | some b =>
              exact storereg_projlocal_simB compProg hWF h_env (hr.pkg hWF _) h_inv h_code h_step
      | projDeref f hc =>
          exact storereg_projchain_simB compProg hWF hc (hr.pkg hWF _) h_inv h_code h_step
  | pushProtectors =>
      intro ρt s_mir s_mir' s_osea cs h_inv h_code h_step
      exact pushProt_simB compProg h_inv h_code h_step
  | popProtectors =>
      intro ρt s_mir s_mir' s_osea cs h_inv h_code h_step
      exact popProt_simB compProg h_inv h_code h_step
  | dealloc hd =>
      intro ρt s_mir s_mir' s_osea cs h_inv h_code h_step
      exact dealloc_simB compProg hWF hd h_inv h_code h_step

/-- **Byte-level compiler correctness, for the proved fragment.** If every
    pointer-typed place has a pointer-sized layout, `prog` compiles, and
    every non-halt statement of `prog` is in the fragment, then every
    successful source run from the initial state is matched by a
    successful target run from the initial state, the two related by the
    byte invariant at the statement-prefix compile state. -/
theorem compileB_correct_fragment {Γ : Ctx} (L : mirliteB.LayEnv Γ) (hWF : PtrPlacesWF L)
    (prog : Prog Γ) (compProg : oseairL.Prog) (h_comp : compileProg L prog = .ok compProg)
    (h_frag : ∀ stmt, stmt ∈ prog → stmt ≠ .halt → StmtB stmt)
    (n : Nat) {s_mir' : mirliteB.State MSB Γ}
    (h_run : mirliteB.runN MSB L n (mirliteB.State.initial MSB Γ) prog = .ok s_mir') :
    ∃ (ρt : TagRenameMap) (s_osea' : oseairL.State MSB) (m : Nat),
      oseairL.runN MSB m (oseairL.State.initial MSB) compProg = .Ok s_osea' ∧
      InvAtB L ρt s_mir' s_osea' (csAtB L (initialState Γ) prog s_mir'.pc) :=
  compileB_correct L prog compProg h_comp
    (fun stmt h_mem h_nh => (h_frag stmt h_mem h_nh).sim hWF) n h_run

end obseq3.byteproof
