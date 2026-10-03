import obseq3.context

namespace obseq3

/-- A path through layout type `src` that reaches a sub-layout of type `dst`.
    Represented as a sequence of tuple field projections. -/
inductive PathTo : LayoutTy → LayoutTy → Type where
| nil : PathTo τ τ
| field {tys : List LayoutTy} (idx : Fin tys.length) :
    PathTo (tys.get idx) τ → PathTo (LayoutTy.TupL tys) τ

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
            | zero => simp [layoutSizeList, layoutSizeList]
            | succ j =>
                have h_j : j < rest.length := Nat.lt_of_succ_lt_succ h_i
                have := ihs j h_j
                simp only [List.take_succ_cons, List.get_cons_succ]
                show layoutSizeList (ty :: rest.take j) + _ ≤ layoutSizeList (ty :: rest)
                simp only [layoutSizeList, layoutSizeList] at this ⊢
                omega
      calc offset (.field idx tail) + layoutSize dst
          = layoutSizeList (tys.take idx.1) + (offset tail + layoutSize dst) := by
            simp [offset, Nat.add_assoc]
        _ ≤ layoutSizeList (tys.take idx.1) + layoutSize (tys.get idx) :=
            Nat.add_le_add_left ih _
        _ ≤ layoutSizeList tys := h_split
        _ = layoutSize (LayoutTy.TupL tys) := rfl

end PathTo

/-- A place of layout type `τ` in context `Γ` (as in obseq2: local, field
    projection, or deref-as-place-projection). -/
inductive Place (Γ : Ctx) : LayoutTy → Type where
| local : Local Γ τ → Place Γ τ
| proj  : Place Γ σ → PathTo σ τ → Place Γ τ
| deref : Place Γ (LayoutTy.PtrL τ) → Place Γ τ

/-- Constructor count — the termination measure for place lowering, which
    reassociates `.proj (.proj b q) p` to `.proj b (q.append p)`:
    reassociation shortens the place by one constructor whatever the
    paths' sizes, which `sizeOf` does not see cleanly. -/
def Place.depth : Place Γ τ → Nat
  | .local _ => 1
  | .proj b _ => b.depth + 1
  | .deref p => p.depth + 1

/-- Allocation length for the `alloc` rvalue: a static count or a runtime
    word read from a place (e.g. a `Layout` size). The allocation covers
    `n * blockSize τ` cells for a `PtrL τ` result. -/
inductive AllocLen (Γ : Ctx) : Type where
| const : Nat → AllocLen Γ
| fromPlace {t : IntTy} : Place Γ (LayoutTy.IntL t) → AllocLen Γ

/-- A right-hand-side expression of layout type `τ` in context `Γ`.
    `ref`'s `Bool` marks a *protected* (function-entry) retag and its
    `List Bool` is the UnsafeCell freeze mask (true = interior-mutable
    cell); `uninit` fills the destination with undef (used to
    materialize hoisted statics and other uninitialized allocations);
    `binOp op a b` reads the two word places as `copy` does (the second
    in the state the first read left) and stores `evalBinOp op` of them;
    `sliceLen p` reads the fat pointer in `p` the same way and stores its
    LENGTH IN ELEMENTS — the extent the pointer claims divided by the
    element's block size (the slice metadata Miri carries beside the
    address); `subSlice p lo hi` reads the same three places and stores
    the pointer NARROWED to elements `lo..hi` — same allocation, same
    tag, offset moved by `lo` elements and extent cut to `hi − lo`. It
    is pure pointer arithmetic: no retag (the `&mut s[lo..hi]` that
    surrounds it is a separate `refSlice`) and no memory event beyond
    the three reads. -/
inductive RExpr (Γ : Ctx) : LayoutTy → Type where
| constInit {t : IntTy} : Word → RExpr Γ (LayoutTy.IntL t)
| copy : Place Γ τ → RExpr Γ τ
| move : Place Γ τ → RExpr Γ τ
| ref : RefKind → Bool → List Bool → Place Γ τ → RExpr Γ (LayoutTy.PtrL τ)
| ptrCast : Place Γ (LayoutTy.PtrL σ) → RExpr Γ (LayoutTy.PtrL τ)
| ptrOffset : Place Γ (LayoutTy.PtrL σ) → Int → RExpr Γ (LayoutTy.PtrL τ)
| refSlice : RefKind → Bool → Place Γ (LayoutTy.PtrL σ) → RExpr Γ (LayoutTy.PtrL τ)
| sliceLen {t : IntTy} : Place Γ (LayoutTy.PtrL σ) → RExpr Γ (LayoutTy.IntL t)
| subSlice {tl th : IntTy} : Place Γ (LayoutTy.PtrL σ) → Place Γ (LayoutTy.IntL tl)
    → Place Γ (LayoutTy.IntL th) → RExpr Γ (LayoutTy.PtrL σ)
| exposeAddr {t : IntTy} : Place Γ (LayoutTy.PtrL σ) → RExpr Γ (LayoutTy.IntL t)
| fromExposed {t : IntTy} : Place Γ (LayoutTy.IntL t) → RExpr Γ (LayoutTy.PtrL τ)
| uninit : RExpr Γ τ
| alloc : AllocLen Γ → RExpr Γ (LayoutTy.PtrL τ)
| binOp {ta tb tr : IntTy} : BinOp → Place Γ (LayoutTy.IntL ta) → Place Γ (LayoutTy.IntL tb)
    → RExpr Γ (LayoutTy.IntL tr)

/-- A statement in context `Γ`.
    - `pushProtectors`/`popProtectors` bracket an inlined call's protector
      frame (Miri's fn-entry protectors).
    - `dealloc` frees a heap block (`std::alloc::dealloc`); allocation is
      the `alloc` RVALUE (`Box::new`, `std::alloc::alloc` — a call, so its
      destination is written after it, 2026-09-21).
    - `assignIf` runs the assignment only when the word at `discr` equals
      `val` — used for variant-conditional seam retags of enum payloads. -/
inductive Stmt (Γ : Ctx) : Type where
| assign : Place Γ τ → RExpr Γ τ → Stmt Γ
| assignIf {t : IntTy} : Place Γ (LayoutTy.IntL t) → Word → Place Γ τ → RExpr Γ τ → Stmt Γ
| dealloc : Place Γ (LayoutTy.PtrL τ) → Stmt Γ
| pushProtectors : Stmt Γ
| popProtectors : Stmt Γ
| halt : Stmt Γ

/-- A sequential program: a list of statements in context `Γ`. -/
abbrev Prog (Γ : Ctx) := List (Stmt Γ)

end obseq3
