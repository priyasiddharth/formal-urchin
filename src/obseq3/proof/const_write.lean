import obseq3.proof.common
import obseq3.proof.permsim_transport
import obseq3.proof.spine

/-!
Per-statement simulation for `.assign dst (.constInit v)` — port of
`obseq2/proof/const_write.lean`. The evidence lemma, the delegation
structure, REGIME A (bound local) and REGIME D1 (deref of a bound
pointer local) are fully proved; the residual regimes (B fresh local,
C projection, D2 proj-pointer place, D3 nested deref) are the audited
sorries — see the audit in `proof/compiler.lean`.
-/

namespace obseq3.proof

/-! ### Ambient binders

    The data every simulation leaf and fragment-transfer lemma
    quantifies over. These are IMPLICIT and every leaf's conclusion
    mentions them, so Lean includes them automatically — no `include` is
    needed, and because they were already the leading binders the
    explicit argument order is unchanged.

    A theorem that binds its own `{Γ : Ctx}` shadows these cleanly and
    picks up none of them. -/
variable {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
variable {ρa : AddrRenameMap} {ρt : TagRenameMap}
variable {s_mir s_mir' : mirlite.State MSB Γ}
variable {s_osea : oseair.State MSB}


open obseq3
open obseq3.compile
open obseq3.oseair (Instr Register Rhs Val)


/-! ## §F What a constant-store rvalue supplies

    Every leaf below needs the same kind of fact about the rvalue: at
    each destination shape, the statement lowers to the destination's
    own code plus one `CStore` of a fixed value list, and it lowers at
    all. A variable `rhs` never REDUCES, but these facts do not need it
    to — they need only `PureCStore rhs`, and `pureCStore_frags` builds
    the whole bundle from that one witness. Each rvalue's instance is
    therefore a single line. -/

structure ConstStoreFrags {Γ : Ctx} {τ : LayoutTy}
    (rhs : RExpr Γ τ) (vs' : List Val) : Prop where
  /-- bound local: one `CStore` through the local's register -/
  localRun : ∀ (loc : Local Γ τ) (cs : CompilerState) (reg : Register),
    getPlaceInfo cs loc.idx.1 = some (reg, τ) →
    CheckedCompilerM.run (compileStmtChecked (Stmt.assign (.local loc) rhs)) cs
      = emit cs [Instr.CStore (layoutToTyVal τ) vs' reg]
  localVal : ∀ (loc : Local Γ τ) (cs : CompilerState), ∃ so,
    CheckedCompilerM.value (compileStmtChecked (Stmt.assign (.local loc) rhs)) cs
      = Except.ok so
  /-- fresh local: root `Alloc`, then the `CStore` -/
  localFreshRun : ∀ (loc : Local Γ τ) (cs : CompilerState),
    getPlaceInfo cs loc.idx.1 = none →
    CheckedCompilerM.run (compileStmtChecked (Stmt.assign (.local loc) rhs)) cs
      = emit (setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 }
            [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal τ))])
          loc.idx.1 (Register.R cs.nextReg, τ))
        [Instr.CStore (layoutToTyVal τ) vs' (Register.R cs.nextReg)]
  /-- projection off a bound local, ZERO offset -/
  projZeroRun : ∀ {σ : LayoutTy} (loc : Local Γ σ) (path : PathTo σ τ)
    (cs : CompilerState) (reg : Register),
    pathOffset path = 0 →
    getPlaceInfo cs loc.idx.1 = some (reg, σ) →
    CheckedCompilerM.run
        (compileStmtChecked (Stmt.assign (.proj (.local loc) path) rhs)) cs
      = emit cs [Instr.CStore (layoutToTyVal τ) vs' reg]
  /-- projection off a bound local, NONZERO offset: `Borrow; CStore; Die` -/
  projOffsetRun : ∀ {σ : LayoutTy} (loc : Local Γ σ) (path : PathTo σ τ)
    (cs : CompilerState) (reg : Register),
    pathOffset path ≠ 0 →
    getPlaceInfo cs loc.idx.1 = some (reg, σ) →
    CheckedCompilerM.run
        (compileStmtChecked (Stmt.assign (.proj (.local loc) path) rhs)) cs
      = emit (emit (emit { cs with nextReg := cs.nextReg + 1 }
            [Instr.Assgn (Register.R cs.nextReg)
              (borrowRhs RefKind.Mut (blockSize τ) reg (pathOffset path))])
            [Instr.CStore (layoutToTyVal τ) vs' (Register.R cs.nextReg)])
            [Instr.Die (Register.R cs.nextReg) (blockSize τ)]
  projLocalVal : ∀ {σ : LayoutTy} (loc : Local Γ σ) (path : PathTo σ τ)
    (cs : CompilerState) (reg : Register),
    getPlaceInfo cs loc.idx.1 = some (reg, σ) →
    ∃ so, CheckedCompilerM.value
      (compileStmtChecked (Stmt.assign (.proj (.local loc) path) rhs)) cs
        = Except.ok so
  /-- projection off an UNBOUND local root -/
  projFreshVal : ∀ {σ : LayoutTy} (loc : Local Γ σ) (path : PathTo σ τ)
    (cs : CompilerState), getPlaceInfo cs loc.idx.1 = none →
    ∃ so, CheckedCompilerM.value
      (compileStmtChecked (Stmt.assign (.proj (.local loc) path) rhs)) cs
        = Except.ok so
  projFreshZeroRun : ∀ {σ : LayoutTy} (loc : Local Γ σ) (path : PathTo σ τ)
    (cs : CompilerState), pathOffset path = 0 →
    getPlaceInfo cs loc.idx.1 = none →
    CheckedCompilerM.run
        (compileStmtChecked (Stmt.assign (.proj (.local loc) path) rhs)) cs
      = emit (setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 }
            [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
          loc.idx.1 (Register.R cs.nextReg, σ))
        [Instr.CStore (layoutToTyVal τ) vs' (Register.R cs.nextReg)]
  projFreshOffsetRun : ∀ {σ : LayoutTy} (loc : Local Γ σ) (path : PathTo σ τ)
    (cs : CompilerState), pathOffset path ≠ 0 →
    getPlaceInfo cs loc.idx.1 = none →
    CheckedCompilerM.run
        (compileStmtChecked (Stmt.assign (.proj (.local loc) path) rhs)) cs
      = emit (emit (emit
            { (setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 }
                [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
              loc.idx.1 (Register.R cs.nextReg, σ)) with
                nextReg := cs.nextReg + 1 + 1 }
            [Instr.Assgn (Register.R (cs.nextReg + 1))
              (borrowRhs RefKind.Mut (blockSize τ) (Register.R cs.nextReg)
                (pathOffset path))])
            [Instr.CStore (layoutToTyVal τ) vs' (Register.R (cs.nextReg + 1))])
            [Instr.Die (Register.R (cs.nextReg + 1)) (blockSize τ)]
  /-- projection over a DEREF base -/
  projDerefZeroVal : ∀ {σ : LayoutTy} (Q : Place Γ (obseq.LayoutTy.PtrL σ))
    (path : PathTo σ τ) (cs : CompilerState)
    {dOut : ResultWithEvidence PtrResult
      (PlaceToRegEvidence RefKind.Mut (Place.deref Q))},
    pathOffset path = 0 →
    CompilerM.run (ensurePlaceRoot (Place.proj (Place.deref Q) path)) cs = cs →
    CheckedCompilerM.value (placeToRegChecked RefKind.Mut (Place.deref Q)) cs
      = Except.ok dOut →
    ∃ so, CheckedCompilerM.value
      (compileStmtChecked (Stmt.assign (.proj (.deref Q) path) rhs)) cs
        = Except.ok so
  projDerefOffsetVal : ∀ {σ : LayoutTy} (Q : Place Γ (obseq.LayoutTy.PtrL σ))
    (path : PathTo σ τ) (cs : CompilerState)
    {dOut : ResultWithEvidence PtrResult
      (PlaceToRegEvidence RefKind.Mut (Place.deref Q))},
    pathOffset path ≠ 0 →
    CompilerM.run (ensurePlaceRoot (Place.proj (Place.deref Q) path)) cs = cs →
    CheckedCompilerM.value (placeToRegChecked RefKind.Mut (Place.deref Q)) cs
      = Except.ok dOut →
    ∃ so, CheckedCompilerM.value
      (compileStmtChecked (Stmt.assign (.proj (.deref Q) path) rhs)) cs
        = Except.ok so
  projDerefZeroRun : ∀ {σ : LayoutTy} (Q : Place Γ (obseq.LayoutTy.PtrL σ))
    (path : PathTo σ τ) (cs : CompilerState)
    {dOut : ResultWithEvidence PtrResult
      (PlaceToRegEvidence RefKind.Mut (Place.deref Q))},
    pathOffset path = 0 →
    CompilerM.run (ensurePlaceRoot (Place.proj (Place.deref Q) path)) cs = cs →
    CheckedCompilerM.value (placeToRegChecked RefKind.Mut (Place.deref Q)) cs
      = Except.ok dOut →
    dOut.result.cleanup = [] →
    CheckedCompilerM.run
        (compileStmtChecked (Stmt.assign (.proj (.deref Q) path) rhs)) cs
      = emit (CheckedCompilerM.run
          (placeToRegChecked RefKind.Mut (Place.deref Q)) cs)
        [Instr.CStore (layoutToTyVal τ) vs' dOut.result.reg]
  projDerefOffsetRun : ∀ {σ : LayoutTy} (Q : Place Γ (obseq.LayoutTy.PtrL σ))
    (path : PathTo σ τ) (cs : CompilerState)
    {dOut : ResultWithEvidence PtrResult
      (PlaceToRegEvidence RefKind.Mut (Place.deref Q))},
    pathOffset path ≠ 0 →
    CompilerM.run (ensurePlaceRoot (Place.proj (Place.deref Q) path)) cs = cs →
    CheckedCompilerM.value (placeToRegChecked RefKind.Mut (Place.deref Q)) cs
      = Except.ok dOut →
    dOut.result.cleanup = [] →
    CheckedCompilerM.run
        (compileStmtChecked (Stmt.assign (.proj (.deref Q) path) rhs)) cs
      = emit (emit (emit
          { (CheckedCompilerM.run
              (placeToRegChecked RefKind.Mut (Place.deref Q)) cs) with
              nextReg := (CheckedCompilerM.run
                (placeToRegChecked RefKind.Mut (Place.deref Q)) cs).nextReg + 1 }
          [Instr.Assgn (Register.R (CheckedCompilerM.run
              (placeToRegChecked RefKind.Mut (Place.deref Q)) cs).nextReg)
            (borrowRhs RefKind.Mut (blockSize τ) dOut.result.reg (pathOffset path))])
          [Instr.CStore (layoutToTyVal τ) vs'
            (Register.R (CheckedCompilerM.run
              (placeToRegChecked RefKind.Mut (Place.deref Q)) cs).nextReg)])
          [Instr.Die (Register.R (CheckedCompilerM.run
            (placeToRegChecked RefKind.Mut (Place.deref Q)) cs).nextReg)
            (blockSize τ)]
  projDerefIncr : ∀ {σ : LayoutTy} (Q : Place Γ (obseq.LayoutTy.PtrL σ))
    (path : PathTo σ τ) (cs : CompilerState),
    CompilerM.run (ensurePlaceRoot (Place.proj (Place.deref Q) path)) cs = cs →
    StateIncr
      (CheckedCompilerM.run (placeToRegChecked RefKind.Mut
        (.proj (.deref Q) path)) cs)
      (CheckedCompilerM.run
        (compileStmtChecked (Stmt.assign (.proj (.deref Q) path) rhs)) cs)
  /-- a DEREF destination -/
  derefVal : ∀ (Q : Place Γ (obseq.LayoutTy.PtrL τ)) (cs : CompilerState)
    {dOut : ResultWithEvidence PtrResult
      (PlaceToRegEvidence RefKind.Mut (Place.deref Q))},
    CompilerM.run (ensurePlaceRoot (Place.deref Q)) cs = cs →
    CheckedCompilerM.value (placeToRegChecked RefKind.Mut (Place.deref Q)) cs
      = Except.ok dOut →
    ∃ so, CheckedCompilerM.value
      (compileStmtChecked (Stmt.assign (.deref Q) rhs)) cs = Except.ok so
  derefRun : ∀ (Q : Place Γ (obseq.LayoutTy.PtrL τ)) (cs : CompilerState)
    {dOut : ResultWithEvidence PtrResult
      (PlaceToRegEvidence RefKind.Mut (Place.deref Q))},
    CompilerM.run (ensurePlaceRoot (Place.deref Q)) cs = cs →
    CheckedCompilerM.value (placeToRegChecked RefKind.Mut (Place.deref Q)) cs
      = Except.ok dOut →
    dOut.result.cleanup = [] →
    CheckedCompilerM.run (compileStmtChecked (Stmt.assign (.deref Q) rhs)) cs
      = emit (CheckedCompilerM.run
          (placeToRegChecked RefKind.Mut (Place.deref Q)) cs)
        [Instr.CStore (layoutToTyVal τ) vs' dOut.result.reg]
  /-- the statement lowers whenever the destination's own lowering does
      — the shape `const_store_stmt_evidence` needs, at each non-local
      destination constructor -/
  projAnyVal : ∀ {σ : LayoutTy} (base : Place Γ σ) (path : PathTo σ τ)
    (cs : CompilerState)
    {dstOut : ResultWithEvidence PtrResult
      (PlaceToRegEvidence RefKind.Mut (Place.proj base path))},
    CheckedCompilerM.value (placeToRegChecked RefKind.Mut (Place.proj base path))
      (CompilerM.run (ensurePlaceRoot (Place.proj base path)) cs) = Except.ok dstOut →
    ∃ so, CheckedCompilerM.value
      (compileStmtChecked (Stmt.assign (.proj base path) rhs)) cs = Except.ok so
  derefAnyVal : ∀ (Q : Place Γ (obseq.LayoutTy.PtrL τ)) (cs : CompilerState)
    {dstOut : ResultWithEvidence PtrResult
      (PlaceToRegEvidence RefKind.Mut (Place.deref Q))},
    CheckedCompilerM.value (placeToRegChecked RefKind.Mut (Place.deref Q))
      (CompilerM.run (ensurePlaceRoot (Place.deref Q)) cs) = Except.ok dstOut →
    ∃ so, CheckedCompilerM.value
      (compileStmtChecked (Stmt.assign (.deref Q) rhs)) cs = Except.ok so
  derefIncr : ∀ (Q : Place Γ (obseq.LayoutTy.PtrL τ)) (cs : CompilerState),
    CompilerM.run (ensurePlaceRoot (Place.deref Q)) cs = cs →
    StateIncr
      (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (.deref Q)) cs)
      (CheckedCompilerM.run (compileStmtChecked (Stmt.assign (.deref Q) rhs)) cs)


/-! ## §A' The CONSTANT-STORE fragment, generic in the rvalue

    `constInit` and `uninit` differ only in the value list they store:
    both evaluate WITHOUT touching the source state, both lower to a
    single `CStore` with no rhs pre-phase instructions, and both leave
    the destination's own lowering to run from the prefix state. The
    leaves below are therefore stated over an arbitrary rhs, an
    arbitrary destination layout, and a source/target value pair related
    cell-by-cell by `MemValSim`; each rvalue supplies the pair.

    `constInit` gives `[word v]` / `[Val.Dat v]` at `NatL` (width one);
    `uninit` gives `replicate (blockSize τ) undef` /
    `replicate (blockSize τ) Val.Undef` at ANY `τ`, whose `ListRel` is
    free because `MemValSim`'s first clause is `| .undef, _ => True`. -/



/-- Two equally long runs of undef refine each other cell-by-cell. -/
theorem ListRel_replicate_undef (ρa : AddrRenameMap) (ρt : TagRenameMap)
    (n : Nat) (v : Val) :
    ListRel (MemValSim ρa ρt) (List.replicate n mirlite.MemValue.undef)
      (List.replicate n v) := by
  induction n with
  | zero => trivial
  | succ n ih =>
      rw [List.replicate_succ, List.replicate_succ]
      exact ⟨trivial, ih⟩

/-- `blockSize` IS the compiled type's cell count. -/
theorem blockSize_eq_typeSize (τ : LayoutTy) :
    blockSize τ = obseq.typeSize (layoutToTyVal τ) := by
  simp [blockSize]

/-! ## §F' The constant stores as value packages

    A `PureCStore` rvalue emits no code at all: its whole contribution is
    the one `CStore` in its `store` field. So its value package is the
    invariant handed straight back, with `nR = 0` and the target state
    untouched — and `StoreStep.cstore` for the store, which needs no
    register to survive anything. That is the entire distance between
    `constInit`/`uninit` and the destination leaves that copy, the casts
    and ref already share. -/

theorem ValuePkg.of_pureCStore {τ : LayoutTy} {rhs : RExpr Γ τ}
    {ty : obseq.TyVal} {vs' : List Val}
    (compProg : oseair.Prog)
    (h_pure : PureCStore rhs ty vs')
    (h_size : vs'.length = obseq.typeSize ty)
    (h_len : vs'.length = blockSize τ)
    (h_ev : ∀ (ρa : AddrRenameMap) (ρt : TagRenameMap)
      (sM : mirlite.State MSB Γ) (output : mirlite.EvalOutput MSB Γ τ),
      mirlite.evalRExpr MSB sM rhs = .ok output →
      output.state = sM ∧ ListRel (MemValSim ρa ρt) output.values vs') :
    ValuePkg compProg rhs := by
  intro ρa ρt sM sA csA h_id_a h_wf_t h_tbd h_lbs h_prb h_sms h_alloc h_psim h_pc
    output h_evalo
  obtain ⟨h_run, pre, h_pval, h_store, h_post⟩ := h_pure csA
  obtain ⟨h_ost, h_rel⟩ := h_ev ρa ρt sM output h_evalo
  refine ⟨fun d => Instr.CStore ty vs' d, pre, h_pval, h_store, h_post,
    by rw [h_run], ?_⟩
  intro _
  exact ⟨ρt, 0, sA, sM.perms, vs', TagRenameIncr.refl ρt, h_wf_t,
    by rw [h_ost], h_len, rfl,
    by rw [h_run], by rw [h_run]; exact Nat.le_refl _,
    by rw [h_run]; exact h_lbs,
    h_psim, h_tbd, rfl, by rw [h_run]; exact h_pc,
    by rw [h_run]; exact StoreStep.cstore compProg sA _ ty vs' h_size,
    h_rel⟩

theorem constInit_valuePkg {Γ : Ctx} (v : Word) (compProg : oseair.Prog) :
    ValuePkg compProg (RExpr.constInit (Γ := Γ) v) :=
  ValuePkg.of_pureCStore compProg (constInit_pureCStore v) rfl rfl
    (fun _ _ _ _ h => by
      simp only [mirlite.evalRExpr] at h
      injection h with h
      subst h
      exact ⟨rfl, ⟨rfl, trivial⟩⟩)

theorem uninit_valuePkg {Γ : Ctx} (τ : LayoutTy) (compProg : oseair.Prog) :
    ValuePkg compProg (RExpr.uninit (Γ := Γ) (τ := τ)) :=
  ValuePkg.of_pureCStore compProg (uninit_pureCStore τ)
    (by rw [List.length_replicate, blockSize_eq_typeSize])
    (List.length_replicate)
    (fun ρa ρt _ _ h => by
      simp only [mirlite.evalRExpr] at h
      injection h with h
      subst h
      exact ⟨rfl, ListRel_replicate_undef ρa ρt _ _⟩)

































/-! ## Flatten transfer for regime D: every deref dst normalizes into
    the chain grammar, so the chain leaf serves ALL of them. -/






/-- The per-statement simulation for a CONSTANT-STORE rvalue. Since
    2026-09-14 it is the same case split on the destination that copy,
    the casts and ref use: the rvalue contributes only its value package,
    and a constant store's package is `StoreStep.cstore` over a
    `PureCStore` witness. -/
theorem CompilerInv_step_constStore
    {τ : LayoutTy} {dst : Place Γ τ} {rhs : RExpr Γ τ}
    (compProg : oseair.Prog)
    (h_pkg : ValuePkg compProg rhs)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    (h_stmt : prog.get? s_mir.pc = some (.assign dst rhs))
    (h_step : mirlite.stepStmt MSB s_mir (.assign dst rhs) = .ok s_mir') :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' := by
  cases dst with
  | «local» loc =>
      cases h_envD : mirlite.Env.lookup s_mir.env loc with
      | some bD =>
          obtain ⟨ρt', s_osea', n, h_incr, h_run, h_inv'⟩ :=
            storereg_local_simulation compProg h_pkg h_comp h_inv h_stmt
              (fun _ => rfl) (fun _ so h => ⟨so, h⟩) h_envD h_step
          exact ⟨ρa, ρt', s_osea', n, AddrRenameIncr.refl ρa, h_incr, h_run, h_inv'⟩
      | none =>
          exact storereg_localfresh_simulation compProg h_pkg h_comp h_inv h_stmt
            (fun _ => rfl) (fun _ so h => ⟨so, h⟩) h_envD h_step
  | proj base path =>
      exact storereg_projdst_recursion compProg h_pkg h_comp h_inv h_stmt
        (fun _ => rfl) (fun _ so h => ⟨so, h⟩) h_step
  | deref P =>
      rw [stepStmt_assign_dstderef_flatten] at h_step
      obtain ⟨ρt', s_osea', n, h_incr, h_run, h_inv'⟩ :=
        storereg_chaindst_simulation (P := flattenPlace P) compProg h_pkg
          (PtrChain_flatten_deref P) h_comp h_inv h_stmt
          (fun cs => compileStmt_assign_derefdst_flatten_run _ cs)
          (fun cs so h => compileStmt_assign_derefdst_flatten_value _ cs so h)
          h_step
      exact ⟨ρa, ρt', s_osea', n, AddrRenameIncr.refl ρa, h_incr, h_run, h_inv'⟩

/-- The `constInit` instance of the constant-store step. -/
theorem CompilerInv_step_constWrite
    {dst : Place Γ obseq.LayoutTy.NatL}
    (compProg : oseair.Prog)
    (v : Word)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    (h_stmt : prog.get? s_mir.pc = some (.assign dst (.constInit v)))
    (h_step : mirlite.stepStmt MSB s_mir (.assign dst (.constInit v)) = .ok s_mir') :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' :=
  CompilerInv_step_constStore compProg (constInit_valuePkg v compProg)
    h_comp h_inv h_stmt h_step

/-- The `uninit` instance: an undef-fill of ANY destination place at ANY
    layout type. -/
theorem CompilerInv_step_uninit
    {τ : LayoutTy} {dst : Place Γ τ}
    (compProg : oseair.Prog)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    (h_stmt : prog.get? s_mir.pc = some (.assign dst .uninit))
    (h_step : mirlite.stepStmt MSB s_mir (.assign dst .uninit) = .ok s_mir') :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' :=
  CompilerInv_step_constStore compProg (uninit_valuePkg τ compProg)
    h_comp h_inv h_stmt h_step

end obseq3.proof
