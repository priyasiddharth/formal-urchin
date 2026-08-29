# The last copy class is an event-ORDER mismatch (durable note)

`copy_place_residual`'s remaining class — a NON-LOCAL destination,
`(*p).f := copy src` — was described in earlier docstrings as
"composition work, not a blocker". That assessment is WRONG, and this
note records why, so no future increment starts on the false premise.

## The mismatch
Both machines perform the same events; the ORDER differs.

- mirlite `doAssign` (rhs-first since 2026-08-30, Rust's documented
  order): prepare dst root → `evalRExpr` (src resolution + the copy's
  RANGE READ) → dst resolution (each deref level READS its pointer
  cell) → overlap guard → write.
- compiled (`compileStmtChecked`'s general assign arm): src lowering
  (address only) → dst lowering (the pointer-cell Loads) → `Memcpy`,
  which performs the range read AND the write → cleanups.

So the copy's range read sits BEFORE the dst's pointer-cell reads on the
source and AFTER them on the target.

## Why it matters
SB reads do not commute. A read through tag `t` pops Unique items above
`t` in each cell's stack. At a shared cell with `t₂` a Unique above
`t₁`, `read t₁; read t₂` traps (the first pops `t₂`) while
`read t₂; read t₁` succeeds. The direction that hurts us is the mirror
image: the source succeeds and the target traps, which is exactly a
missed refinement — so a proof of this class cannot just transport the
two reads independently.

## Why the class is nevertheless TRUE
The two reads can only interact at a shared cell: a dst-chain pointer
cell lying inside the source's τ-sized range. Within CoreProg (no
`ptrCast`, no `exposeAddr`) a cell holds a pointer only where the layout
puts one, so such a cell is a `PtrL σ` field of τ — making σ a strict
subterm of τ. The chain then continues from σ, through projections and
derefs (both subterm steps), to a `PtrL τ` it dereferences — making τ a
subterm of σ. `LayoutTy` is an inductive tree, so both cannot hold. The
ranges are disjoint BY TYPING, and cell-wise disjoint reads commute.

## What closing it would cost
Two options, both decisions for the human:
1. **Invariant strengthening.** Carry memory well-typedness in
   `CompilerInv`: every `ptrVal` cell sits at a `PtrL`-typed offset of
   its allocation. Then derive the disjointness above and add a
   read-read commutation lemma to the keystone layer.
2. **Compiler change.** Materialize the copy's source into a temporary
   before the dst lowering, so both orders coincide. Cheaper for the
   proof; changes emitted code (and needs a temp buffer for arbitrary
   layouts, i.e. more than a register).

Note that `const_write` and `ref` do NOT have this problem: `constInit`
raises no source event, and `ref`'s retag IS emitted in the pre-phase,
so its order already matches.
