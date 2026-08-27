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

/-- Path composition. `PathTo` is a cons-chain, so `s.1.1`'s two
    single-field paths compose into one — which is what lets the compiler
    flatten nested projections into a SINGLE field-sized borrow instead of
    retagging every intermediate place (the nested-projection divergence,
    `local/nested_proj_borrow`, 2026-08-27). -/
def append : PathTo src mid → PathTo mid dst → PathTo src dst
  | .nil, p => p
  | .field idx tail, p => .field idx (append tail p)

@[simp] theorem offset_append (q : PathTo src mid) (p : PathTo mid dst) :
    offset (append q p) = offset q + offset p := by
  induction q with
  | nil => simp [append, offset]
  | field idx tail ih => simp [append, offset, ih]; omega

/-- A field's range fits inside its layout: the path's offset plus the
    target's size stays within the source's size. This is the TYPING fact
    that discharges the target `Borrow`'s bounds check when a reference to
    a projected field is minted — the source's `sb_ref` has no bounds
    check of its own, so nothing semantic supplies it. -/
theorem offset_add_size_le : (p : PathTo src dst) →
    offset p + layoutSize dst ≤ layoutSize src
  | .nil => by simp [offset]
  | .field (tys := tys) idx tail => by
      have ih := offset_add_size_le tail
      have h_split : layoutSizeList (tys.take idx.1) + layoutSize (tys.get idx)
          ≤ layoutSizeList tys := by
        clear ih tail
        obtain ⟨i, h_i⟩ := idx
        induction tys generalizing i with
        | nil => cases h_i
        | cons ty rest ihs =>
            cases i with
            | zero => simp [layoutSizeList, obseq.layoutSizeList]
            | succ j =>
                have h_j : j < rest.length := Nat.lt_of_succ_lt_succ h_i
                have := ihs j h_j
                simp only [List.take_succ_cons, List.get_cons_succ]
                show layoutSizeList (ty :: rest.take j) + _ ≤ layoutSizeList (ty :: rest)
                simp only [layoutSizeList, obseq.layoutSizeList] at this ⊢
                omega
      calc offset (.field idx tail) + layoutSize dst
          = layoutSizeList (tys.take idx.1) + (offset tail + layoutSize dst) := by
            simp [offset, Nat.add_assoc]
        _ ≤ layoutSizeList (tys.take idx.1) + layoutSize (tys.get idx) :=
            Nat.add_le_add_left ih _
        _ ≤ layoutSizeList tys := h_split
        _ = layoutSize (obseq.LayoutTy.TupL tys) := rfl

end PathTo

/-- A place of layout type `τ` in context `Γ` (as in obseq2: local, field
    projection, or deref-as-place-projection). -/
inductive Place (Γ : Ctx) : LayoutTy → Type where
| local : Local Γ τ → Place Γ τ
| proj  : Place Γ σ → PathTo σ τ → Place Γ τ
| deref : Place Γ (obseq.LayoutTy.PtrL τ) → Place Γ τ

/-- Constructor count — the termination measure for place lowering, which
    reassociates `.proj (.proj b q) p` to `.proj b (q.append p)`:
    reassociation shortens the place by one constructor whatever the
    paths' sizes, which `sizeOf` does not see cleanly. -/
def Place.depth : Place Γ τ → Nat
  | .local _ => 1
  | .proj b _ => b.depth + 1
  | .deref p => p.depth + 1

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
