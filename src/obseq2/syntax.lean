import obseq2.context

namespace obseq2

inductive PathTo : LayoutTy → LayoutTy → Type where
| nil : PathTo τ τ
| field {tys : List LayoutTy} (idx : Fin tys.length) :
    PathTo (tys.get idx) τ → PathTo (obseq.LayoutTy.TupL tys) τ

namespace PathTo

def indices : PathTo src dst → List Nat
  | .nil => []
  | .field idx tail => idx.1 :: indices tail

end PathTo

inductive Place (Γ : Ctx) : LayoutTy → Type where
| local : Local Γ τ → Place Γ τ
| proj : Place Γ σ → PathTo σ τ → Place Γ τ

namespace Place

def pathIndices : Place Γ τ → List Nat
  | .local _ => []
  | .proj base path => base.pathIndices ++ path.indices

end Place

inductive RExpr (Γ : Ctx) : LayoutTy → Type where
| constInit : Word → RExpr Γ obseq.LayoutTy.NatL
| copy : Place Γ τ → RExpr Γ τ
| ref : RefKind → Place Γ τ → RExpr Γ (obseq.LayoutTy.PtrL τ)
| deref : Place Γ (obseq.LayoutTy.PtrL τ) → RExpr Γ τ

inductive Stmt (Γ : Ctx) : Type where
| assign : Place Γ τ → RExpr Γ τ → Stmt Γ
| halt : Stmt Γ

abbrev Prog (Γ : Ctx) := List (Stmt Γ)

def copyAssign (dst src : Place Γ τ) : Stmt Γ :=
  .assign dst (.copy src)

def refAssign (dst : Place Γ (obseq.LayoutTy.PtrL τ)) (kind : RefKind) (src : Place Γ τ) : Stmt Γ :=
  .assign dst (.ref kind src)

def derefAssign (dst : Place Γ τ) (src : Place Γ (obseq.LayoutTy.PtrL τ)) : Stmt Γ :=
  .assign dst (.deref src)

end obseq2
