import obseq3.proof.spine

/-!
# Nested projections: `(b.q).p` is `b.(q ++ p)`

The compiler reassociates nested projections (one borrow at the composed
offset, `compile.lean`); here the source is shown to agree:
the composed path has the same byte layout and byte offset, so the
place's layout, its access resolution and its pure resolution coincide.
On the compiler side, the reassociation arm's run and result ARE the
flattened place's.
-/

namespace obseq3.proof

open obseq3 obseq3.bytes obseq3.proof
open obseq3.mirlite (MemValue Binding Env PlaceRes)
open obseq3.oseair (Val Register)
open obseq3.compile

theorem PathTo.indices_append {a b c : LayoutTy} (q : PathTo a b) (p : PathTo b c) :
    (q.append p).indices = q.indices ++ p.indices := by
  induction q with
  | nil => rfl
  | field idx tail ih => simp [PathTo.append, PathTo.indices, ih]

theorem fieldLayout_nontup {lay : BLayout} (h : ∀ fs os sz al, lay ≠ .tup fs os sz al) :
    ∀ ys, mirlite.fieldLayout lay ys = lay
  | [] => rfl
  | _ :: _ => by
      cases lay with
      | tup fs os sz al => exact absurd rfl (h fs os sz al)
      | int n => rfl
      | ptr q => rfl

theorem fieldOffset_nontup {lay : BLayout} (h : ∀ fs os sz al, lay ≠ .tup fs os sz al) :
    ∀ ys, mirlite.fieldOffsetB lay ys = 0
  | [] => rfl
  | _ :: _ => by
      cases lay with
      | tup fs os sz al => exact absurd rfl (h fs os sz al)
      | int n => rfl
      | ptr q => rfl

theorem fieldLayout_append : ∀ (lay : BLayout) (xs ys : List Nat),
    mirlite.fieldLayout lay (xs ++ ys)
      = mirlite.fieldLayout (mirlite.fieldLayout lay xs) ys
  | _, [], _ => rfl
  | .tup fs os sz al, i :: is, ys => by
      simp only [List.cons_append, mirlite.fieldLayout]
      exact fieldLayout_append _ is ys
  | .int n, i :: is, ys => by
      simp only [List.cons_append, mirlite.fieldLayout]
      exact (fieldLayout_nontup (by simp) ys).symm
  | .ptr q, i :: is, ys => by
      simp only [List.cons_append, mirlite.fieldLayout]
      exact (fieldLayout_nontup (by simp) ys).symm

theorem fieldOffset_append : ∀ (lay : BLayout) (xs ys : List Nat),
    mirlite.fieldOffsetB lay (xs ++ ys)
      = mirlite.fieldOffsetB lay xs + mirlite.fieldOffsetB (mirlite.fieldLayout lay xs) ys
  | _, [], _ => by simp [mirlite.fieldOffsetB, mirlite.fieldLayout]
  | .tup fs os sz al, i :: is, ys => by
      simp only [List.cons_append, mirlite.fieldOffsetB, mirlite.fieldLayout]
      rw [fieldOffset_append _ is ys]
      omega
  | .int n, i :: is, ys => by
      simp only [List.cons_append, mirlite.fieldOffsetB, mirlite.fieldLayout]
      rw [fieldOffset_nontup (by simp) ys]
  | .ptr q, i :: is, ys => by
      simp only [List.cons_append, mirlite.fieldOffsetB, mirlite.fieldLayout]
      rw [fieldOffset_nontup (by simp) ys]

theorem placeLayout_assoc {Γ : Ctx} (L : mirlite.LayEnv Γ) {ρ σ τ : LayoutTy}
    (b : Place Γ ρ) (q : PathTo ρ σ) (p : PathTo σ τ) :
    mirlite.placeLayout L (.proj (.proj b q) p) = mirlite.placeLayout L (.proj b (q.append p)) := by
  simp only [mirlite.placeLayout, PathTo.indices_append, fieldLayout_append]

theorem resolvePlaceAcc_assoc {Γ : Ctx} {L : mirlite.LayEnv Γ} {M : PermissionModel}
    (s : mirlite.State M Γ) {ρ σ τ : LayoutTy} (b : Place Γ ρ) (q : PathTo ρ σ)
    (p : PathTo σ τ) :
    mirlite.resolvePlaceAcc M L s (.proj (.proj b q) p)
      = mirlite.resolvePlaceAcc M L s (.proj b (q.append p)) := by
  simp only [mirlite.resolvePlaceAcc]
  cases mirlite.resolvePlaceAcc M L s b with
  | error e => rfl
  | ok r =>
      obtain ⟨res, perms⟩ := r
      simp only [mirlite.placeLayout, PathTo.indices_append, fieldOffset_append, Nat.add_assoc]

theorem resolvePlace?_assoc {Γ : Ctx} {L : mirlite.LayEnv Γ} {M : PermissionModel}
    (s : mirlite.State M Γ) {ρ σ τ : LayoutTy} (b : Place Γ ρ) (q : PathTo ρ σ)
    (p : PathTo σ τ) :
    mirlite.resolvePlace? M L s (.proj (.proj b q) p)
      = mirlite.resolvePlace? M L s (.proj b (q.append p)) := by
  simp only [mirlite.resolvePlace?]
  cases mirlite.resolvePlace? M L s b with
  | none => rfl
  | some res =>
      simp only [mirlite.placeLayout, PathTo.indices_append, fieldOffset_append, Nat.add_assoc]

/-! ## The compiler side -/

theorem placeToReg_assoc {Γ : Ctx} {L : mirlite.LayEnv Γ} {ρ σ τ : LayoutTy} (kind : RefKind)
    (b : Place Γ ρ) (q : PathTo ρ σ) (p : PathTo σ τ) (cs : CompilerState) :
    CheckedCompilerM.run (placeToRegChecked L kind (.proj (.proj b q) p)) cs
      = CheckedCompilerM.run (placeToRegChecked L kind (.proj b (q.append p))) cs ∧
    (CheckedCompilerM.value (placeToRegChecked L kind (.proj (.proj b q) p)) cs).map (·.result)
      = (CheckedCompilerM.value (placeToRegChecked L kind (.proj b (q.append p))) cs).map
          (·.result) := by
  have h : placeToRegChecked L kind (.proj (.proj b q) p)
      = (do
          let out ← placeToRegChecked L kind (.proj b (q.append p))
          pure {
            result := out.result,
            evidence := PlaceToRegEvidence.projAssoc b q p out.result out.evidence
          }) := by simp only [placeToRegChecked]
  rw [h]
  simp only [CheckedCompilerM.run_bind, CheckedCompilerM.value_bind]
  cases CheckedCompilerM.value (placeToRegChecked L kind (.proj b (q.append p))) cs <;>
    exact ⟨rfl, rfl⟩

theorem placeToBorrowReg_assoc {Γ : Ctx} {L : mirlite.LayEnv Γ} {ρ σ τ : LayoutTy}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (b : Place Γ ρ) (q : PathTo ρ σ) (p : PathTo σ τ) (cs : CompilerState) :
    CheckedCompilerM.run (placeToBorrowRegChecked L kind prot mask (.proj (.proj b q) p)) cs
      = CheckedCompilerM.run (placeToBorrowRegChecked L kind prot mask (.proj b (q.append p))) cs ∧
    (CheckedCompilerM.value (placeToBorrowRegChecked L kind prot mask (.proj (.proj b q) p)) cs).map
        (·.result)
      = (CheckedCompilerM.value
          (placeToBorrowRegChecked L kind prot mask (.proj b (q.append p))) cs).map (·.result) := by
  have h : placeToBorrowRegChecked L kind prot mask (.proj (.proj b q) p)
      = (do
          let out ← placeToBorrowRegChecked L kind prot mask (.proj b (q.append p))
          pure {
            result := out.result,
            evidence := PlaceToBorrowRegEvidence.projAssoc b q p out.result out.evidence
          }) := by simp only [placeToBorrowRegChecked]
  rw [h]
  simp only [CheckedCompilerM.run_bind, CheckedCompilerM.value_bind]
  cases CheckedCompilerM.value (placeToBorrowRegChecked L kind prot mask (.proj b (q.append p))) cs
    <;> exact ⟨rfl, rfl⟩

theorem compileStmt_assign_assoc {Γ : Ctx} {L : mirlite.LayEnv Γ} {ρ σ τ : LayoutTy}
    (b : Place Γ ρ) (q : PathTo ρ σ) (p : PathTo σ τ) (rhs : RExpr Γ τ) (cs : CompilerState) :
    CheckedCompilerM.run (compileStmtChecked L (.assign (.proj (.proj b q) p) rhs)) cs
      = CheckedCompilerM.run (compileStmtChecked L (.assign (.proj b (q.append p)) rhs)) cs := by
  simp only [compileStmtChecked, compileAssignChecked, CheckedCompilerM.run_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift, ensurePlaceRoot, placeLayout_assoc]
  split
  · generalize CheckedCompilerM.run (compileRExprPreChecked L
        (mirlite.placeLayout L (.proj b (q.append p))) rhs) (CompilerM.run (ensurePlaceRoot L b) cs) = c
    obtain ⟨h_run, h_val⟩ := placeToReg_assoc (L := L) RefKind.Mut b q p c
    rw [h_run]
    revert h_val
    cases CheckedCompilerM.value (placeToRegChecked L RefKind.Mut (.proj (.proj b q) p)) c <;>
      cases CheckedCompilerM.value (placeToRegChecked L RefKind.Mut (.proj b (q.append p))) c <;>
      intro h_val <;> simp only [Except.map, Except.ok.injEq, reduceCtorEq] at h_val
    · rfl
    · simp only [CheckedCompilerM.run_pure, h_val]
  · rfl

theorem stepStmt_assign_assoc {Γ : Ctx} {L : mirlite.LayEnv Γ} {ρ σ τ : LayoutTy}
    (b : Place Γ ρ) (q : PathTo ρ σ) (p : PathTo σ τ) (rhs : RExpr Γ τ)
    (s : mirlite.State MSB Γ) :
    mirlite.stepStmt MSB L s (.assign (.proj (.proj b q) p) rhs)
      = mirlite.stepStmt MSB L s (.assign (.proj b (q.append p)) rhs) := by
  simp only [mirlite.stepStmt, mirlite.doAssign, mirlite.preparePlaceAssign,
    placeLayout_assoc, resolvePlace?_assoc, resolvePlaceAcc_assoc, mirlite.allocateRoot]

end obseq3.proof
