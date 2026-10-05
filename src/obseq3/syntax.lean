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

/-- Path composition. `PathTo` is a cons-chain, so `s.1.1`'s two
    single-field paths compose into one — which is what lets the compiler
    flatten nested projections into a SINGLE field-sized borrow instead of
    retagging every intermediate place (the nested-projection divergence,
    `local/nested_proj_borrow`, 2026-08-27). -/
def append : PathTo src mid → PathTo mid dst → PathTo src dst
  | .nil, p => p
  | .field idx tail, p => .field idx (append tail p)

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
    `n * |β|` bytes, `β` the result pointer's pointee layout
    (`mirlite.allocPointee`): `n` bytes for a `*mut u8`. -/
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
/-- `ptrOffset p delta inbounds`: `p` moved by `delta` pointees. `inbounds`
    (`add`/`offset`, not `wrapping_*`) makes a move out of the allocation
    UB, as Miri's in-bounds pointer arithmetic (`bytes.Mem.offsetPtr`). -/
| ptrOffset : Place Γ (LayoutTy.PtrL σ) → Int → Bool → RExpr Γ (LayoutTy.PtrL τ)
/-- `ptrOffsetBy p i inbounds`: `p` moved by the value of the integer place
    `i` (in pointees, read when the program runs, at `i`'s type): the
    run-time `ptrOffset`. Both places are copy-read, as `subSlice`'s. -/
| ptrOffsetBy {t : IntTy} : Place Γ (LayoutTy.PtrL σ) → Place Γ (LayoutTy.IntL t) → Bool →
    RExpr Γ (LayoutTy.PtrL τ)
/-- `addrOf loc path`: a raw pointer to the place `loc.path` carrying the
    local's OWN tag — no retag, no memory or permission event, as Miri's
    place projection (`a[i]`, `(*p).f`'s base). The loader uses it only where
    Rust makes no reference: never for `&`/`&raw`, which are retags (`ref`).
    Rooted at a local, so the pointer is exactly the place's provenance. -/
| addrOf : Local Γ σ → PathTo σ τ → RExpr Γ (LayoutTy.PtrL τ)
| refSlice : RefKind → Bool → Place Γ (LayoutTy.PtrL σ) → RExpr Γ (LayoutTy.PtrL τ)
| sliceLen {t : IntTy} : Place Γ (LayoutTy.PtrL σ) → RExpr Γ (LayoutTy.IntL t)
| subSlice {tl th : IntTy} : Place Γ (LayoutTy.PtrL σ) → Place Γ (LayoutTy.IntL tl)
    → Place Γ (LayoutTy.IntL th) → RExpr Γ (LayoutTy.PtrL σ)
| exposeAddr {t : IntTy} : Place Γ (LayoutTy.PtrL σ) → RExpr Γ (LayoutTy.IntL t)
/-- The pointer's bytes read at integer type (`ptr.addr()`, a pointer-to-integer
    `transmute`): the address, provenance stripped, nothing exposed. -/
| addr {t : IntTy} : Place Γ (LayoutTy.PtrL σ) → RExpr Γ (LayoutTy.IntL t)
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
