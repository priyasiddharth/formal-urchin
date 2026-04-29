import obseq2.context

namespace obseq2

/-- A path through layout type `src` that reaches a sub-layout of type `dst`.
    Represented as a sequence of tuple field projections. -/
inductive PathTo : LayoutTy → LayoutTy → Type where
| nil : PathTo τ τ
| field {tys : List LayoutTy} (idx : Fin tys.length) :
    PathTo (tys.get idx) τ → PathTo (obseq.LayoutTy.TupL tys) τ

namespace PathTo

/-- Extract the sequence of field indices from a path, in order from outermost to innermost. -/
def indices : PathTo src dst → List Nat
  | .nil => []
  | .field idx tail => idx.1 :: indices tail

end PathTo

/-- A place (addressable memory location) of layout type `τ` in context `Γ`.
    Corresponds to an lvalue: either a local variable, a field projection, or a
    dereference of a pointer-typed place (following Rust MIR's design where Deref
    is a place projection, not a separate expression). -/
inductive Place (Γ : Ctx) : LayoutTy → Type where
| local : Local Γ τ → Place Γ τ
| proj  : Place Γ σ → PathTo σ τ → Place Γ τ
| deref : Place Γ (obseq.LayoutTy.PtrL τ) → Place Γ τ

namespace Place

/-- Collect all field indices needed to reach this place from its root local variable.
    For deref places the static path resets — the dynamic pointer target has its own path. -/
def pathIndices : Place Γ τ → List Nat
  | .local _ => []
  | .proj base path => base.pathIndices ++ path.indices
  | .deref _ => []

end Place

/-- A right-hand-side expression of layout type `τ` in context `Γ`. -/
inductive RExpr (Γ : Ctx) : LayoutTy → Type where
| constInit : Word → RExpr Γ obseq.LayoutTy.NatL
| copy : Place Γ τ → RExpr Γ τ
| ref : RefKind → Place Γ τ → RExpr Γ (obseq.LayoutTy.PtrL τ)

/-- A statement in context `Γ`. -/
inductive Stmt (Γ : Ctx) : Type where
| assign : Place Γ τ → RExpr Γ τ → Stmt Γ
| halt : Stmt Γ

/-- A sequential program: a list of statements in context `Γ`. -/
abbrev Prog (Γ : Ctx) := List (Stmt Γ)

/-- Assign the value at `src` into `dst` by copying. -/
def copyAssign (dst src : Place Γ τ) : Stmt Γ :=
  .assign dst (.copy src)

/-- Assign a reference of the given kind to `src` into `dst`. -/
def refAssign (dst : Place Γ (obseq.LayoutTy.PtrL τ)) (kind : RefKind) (src : Place Γ τ) : Stmt Γ :=
  .assign dst (.ref kind src)

/-- Assign the value at the dereferenced place `src` into `dst`.
    `src` is a pointer-typed place; `Place.deref src` is the pointee place. -/
def derefAssign (dst : Place Γ τ) (src : Place Γ (obseq.LayoutTy.PtrL τ)) : Stmt Γ :=
  .assign dst (.copy (.deref src))

end obseq2
