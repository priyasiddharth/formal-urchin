import obseq3.byteproof.spine

/-!
# The byte-level constant stores — A step 2

`x := const v` and `x := uninit`: both lower to ONE `CStore` at the
destination's byte layout and emit nothing before it, so their value
packages are immediate — no target step, the values in the instruction.
With the destination leaves of `spine.lean` they give the byte
`constInit`/`uninit` steps (bound-local destination so far).
-/

namespace obseq3.byteproof

open obseq3 obseq3.bytes obseq3.proof
open obseq3.mirlite (MemValue Binding Env)
open obseq3.oseair (Val Register)
open obseq3.compileB

/-- A pure constant store's package: no code before the `CStore`, the
    target state unchanged, the values in the instruction. -/
theorem pureCStore_pkg {Γ : Ctx} {τ : LayoutTy} {compProg : oseairL.Prog}
    {L : mirliteB.LayEnv Γ} {dstL : BLayout} {rhs : RExpr Γ τ}
    (vs : List MemValue) (ws : List Val)
    (h_pre : ∀ cs, CheckedCompilerM.run (compileRExprPreChecked L dstL rhs) cs = cs ∧
      ∃ pre, CheckedCompilerM.value (compileRExprPreChecked L dstL rhs) cs = Except.ok pre ∧
        (∀ r, pre.store r = [oseairL.Instr.CStore dstL ws r]) ∧ pre.postCleanup = [])
    (h_eval : ∀ (sM : mirliteB.State MSB Γ) output,
      mirliteB.evalRExpr MSB L sM dstL rhs = .ok output → output = ⟨vs, sM⟩)
    (h_rel : ∀ ρt, ListRel (StoreSim ρt) vs (ws.map oseair.Val.toMem)) :
    ValuePkgB compProg L dstL rhs := by
  intro ρt sM sA csA h_wf h_tbd h_lbs _ h_mem h_alloc h_psim h_pc _h_unmap output h_ev
  obtain ⟨h_run, pre, h_val, h_store, h_post⟩ := h_pre csA
  have h_out := h_eval sM output h_ev
  subst h_out
  refine ⟨_, pre, h_val, h_store, h_post, by rw [h_run], fun _ => ?_⟩
  rw [h_run]
  exact ⟨ρt, 0, sA, sM.mem, sM.perms, ws, TagRenameIncr.refl ρt, h_wf, rfl,
    rfl, Nat.le_refl _, h_lbs, h_psim, h_tbd, h_mem, h_alloc, h_pc,
    StoreStepB.cstore compProg sA _ dstL ws, h_rel ρt⟩

theorem constInit_pkg {Γ : Ctx} {compProg : oseairL.Prog} {L : mirliteB.LayEnv Γ}
    (dstL : BLayout) (v : Word) :
    ValuePkgB compProg L dstL (RExpr.constInit (Γ := Γ) (t := tE) v) :=
  pureCStore_pkg [MemValue.word v] [Val.Dat v]
    (fun _ => ⟨rfl, _, rfl, fun _ => rfl, rfl⟩)
    (fun sM output h => by
      simp only [mirliteB.evalRExpr, mirliteB.EvalResult.ok.injEq] at h
      exact h.symm)
    (fun _ => ⟨Or.inr ⟨by simp, rfl⟩, trivial⟩)

theorem uninit_pkg {Γ : Ctx} {τ : LayoutTy} {compProg : oseairL.Prog} {L : mirliteB.LayEnv Γ}
    (dstL : BLayout) :
    ValuePkgB compProg L dstL (RExpr.uninit (Γ := Γ) (τ := τ)) :=
  pureCStore_pkg (List.replicate dstL.leaves.length MemValue.undef)
    (List.replicate dstL.leaves.length Val.Undef)
    (fun _ => ⟨rfl, _, rfl, fun _ => rfl, rfl⟩)
    (fun sM output h => by
      simp only [mirliteB.evalRExpr, mirliteB.EvalResult.ok.injEq] at h
      exact h.symm)
    (fun _ => by
      rw [List.map_replicate]
      exact ListRel.replicate (R := StoreSim _) (a := MemValue.undef)
        (b := oseair.Val.toMem Val.Undef) (Or.inl ⟨rfl, rfl⟩) _)

/-- `x := const v`, `x` a bound local. -/
theorem constWrite_local_sim {Γ : Ctx} {L : mirliteB.LayEnv Γ} {ρt : TagRenameMap}
    {s_mir s_mir' : mirliteB.State MSB Γ} {s_osea : oseairL.State MSB}
    {loc : Local Γ (LayoutTy.IntL tN)} {b : Binding} {v : Word} {cs : CompilerState}
    (compProg : oseairL.Prog)
    (h_inv : InvAtB L ρt s_mir s_osea cs)
    (h_code : CodeIncludedB compProg
      (CheckedCompilerM.run (compileStmtChecked L (.assign (.local loc) (.constInit v))) cs))
    (h_env : s_mir.env.lookup loc = some b)
    (h_step : mirliteB.stepStmt MSB L s_mir (.assign (.local loc) (.constInit v)) = .ok s_mir') :
    ∃ (ρt' : TagRenameMap) (s_osea' : oseairL.State MSB) (n : Nat),
      TagRenameIncr ρt ρt' ∧
      oseairL.runN MSB n s_osea compProg = .Ok s_osea' ∧
      InvAtB L ρt' s_mir' s_osea'
        (CheckedCompilerM.run (compileStmtChecked L (.assign (.local loc) (.constInit v))) cs) :=
  storereg_local_simB compProg (constInit_pkg _ v) h_inv h_code h_env h_step

/-- `x := uninit`, `x` a bound local, at any layout. -/
theorem uninit_local_sim {Γ : Ctx} {L : mirliteB.LayEnv Γ} {ρt : TagRenameMap}
    {s_mir s_mir' : mirliteB.State MSB Γ} {s_osea : oseairL.State MSB}
    {τ : LayoutTy} {loc : Local Γ τ} {b : Binding} {cs : CompilerState}
    (compProg : oseairL.Prog)
    (h_inv : InvAtB L ρt s_mir s_osea cs)
    (h_code : CodeIncludedB compProg
      (CheckedCompilerM.run (compileStmtChecked L (.assign (.local loc) .uninit)) cs))
    (h_env : s_mir.env.lookup loc = some b)
    (h_step : mirliteB.stepStmt MSB L s_mir (.assign (.local loc) .uninit) = .ok s_mir') :
    ∃ (ρt' : TagRenameMap) (s_osea' : oseairL.State MSB) (n : Nat),
      TagRenameIncr ρt ρt' ∧
      oseairL.runN MSB n s_osea compProg = .Ok s_osea' ∧
      InvAtB L ρt' s_mir' s_osea'
        (CheckedCompilerM.run (compileStmtChecked L (.assign (.local loc) .uninit)) cs) :=
  storereg_local_simB compProg (uninit_pkg _) h_inv h_code h_env h_step

end obseq3.byteproof
