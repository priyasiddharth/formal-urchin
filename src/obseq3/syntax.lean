import obseq3.context

namespace obseq3

/-- A path through layout type `src` that reaches a sub-layout of type `dst`.
    Represented as a sequence of tuple field projections. -/
inductive PathTo : LayoutTy → LayoutTy → Type where
| nil : PathTo τ τ
| field {tys : List LayoutTy} (idx : Fin tys.length) :
    PathTo (tys.get idx) τ → PathTo (obseq.LayoutTy.TupL tys) τ

namespace PathTo

def indices : PathTo src dst → List Nat
  | .nil => []
  | .field idx tail => idx.1 :: indices tail

def offset : PathTo src dst → Nat
  | .nil => 0
  | .field (tys := tys) idx tail =>
      layoutSizeList (tys.take idx.1) + offset tail

end PathTo

/-- A place of layout type `τ` in context `Γ` (as in obseq2: local, field
    projection, or deref-as-place-projection). -/
inductive Place (Γ : Ctx) : LayoutTy → Type where
| local : Local Γ τ → Place Γ τ
| proj  : Place Γ σ → PathTo σ τ → Place Γ τ
| deref : Place Γ (obseq.LayoutTy.PtrL τ) → Place Γ τ

/-- A right-hand-side expression of layout type `τ` in context `Γ`.
    `ref`'s `Bool` marks a *protected* (function-entry) retag and its
    `List Bool` is the UnsafeCell freeze mask (true = interior-mutable
    cell); `uninit` fills the destination with undef (used to
    materialize hoisted statics and other uninitialized allocations). -/
inductive RExpr (Γ : Ctx) : LayoutTy → Type where
| constInit : Word → RExpr Γ obseq.LayoutTy.NatL
| copy : Place Γ τ → RExpr Γ τ
| ref : RefKind → Bool → List Bool → Place Γ τ → RExpr Γ (obseq.LayoutTy.PtrL τ)
| ptrCast : Place Γ (obseq.LayoutTy.PtrL σ) → RExpr Γ (obseq.LayoutTy.PtrL τ)
| ptrOffset : Place Γ (obseq.LayoutTy.PtrL σ) → Int → RExpr Γ (obseq.LayoutTy.PtrL τ)
| refSlice : RefKind → Bool → Place Γ (obseq.LayoutTy.PtrL σ) → RExpr Γ (obseq.LayoutTy.PtrL τ)
| exposeAddr : Place Γ (obseq.LayoutTy.PtrL σ) → RExpr Γ obseq.LayoutTy.NatL
| fromExposed : Place Γ obseq.LayoutTy.NatL → RExpr Γ (obseq.LayoutTy.PtrL τ)
| uninit : RExpr Γ τ

/-- Allocation length for `Stmt.alloc`: a static count or a runtime word
    read from a place (e.g. a `Layout` size). The allocation covers
    `n * blockSize τ` cells for a `PtrL τ` destination. -/
inductive AllocLen (Γ : Ctx) : Type where
| const : Nat → AllocLen Γ
| fromPlace : Place Γ obseq.LayoutTy.NatL → AllocLen Γ

/-- A statement in context `Γ`.
    - `pushProtectors`/`popProtectors` bracket an inlined call's protector
      frame (Miri's fn-entry protectors).
    - `alloc`/`dealloc` model heap allocation (`Box::new`, `std::alloc`).
    - `assignIf` runs the assignment only when the word at `discr` equals
      `val` — used for variant-conditional seam retags of enum payloads. -/
inductive Stmt (Γ : Ctx) : Type where
| assign : Place Γ τ → RExpr Γ τ → Stmt Γ
| assignIf : Place Γ obseq.LayoutTy.NatL → Word → Place Γ τ → RExpr Γ τ → Stmt Γ
| alloc : Place Γ (obseq.LayoutTy.PtrL τ) → AllocLen Γ → Stmt Γ
| dealloc : Place Γ (obseq.LayoutTy.PtrL τ) → Stmt Γ
| pushProtectors : Stmt Γ
| popProtectors : Stmt Γ
| halt : Stmt Γ

/-- A sequential program: a list of statements in context `Γ`. -/
abbrev Prog (Γ : Ctx) := List (Stmt Γ)

end obseq3
