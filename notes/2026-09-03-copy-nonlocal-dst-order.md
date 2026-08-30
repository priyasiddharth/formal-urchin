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

## The divergence is REAL — witness (2026-09-03, executable)

`notes/2026-09-03-copy-order-witness.lean` runs the differential harness
on

```
x  := 5
p  := &mut x
q  := &mut p          -- q points at the cell holding p
q2 := &mut *q         -- Unique reborrow of THAT cell, tag above q's
r  := ptrCast q2      -- same cell, viewed as *mut Nat, carrying q2's tag
**q := copy *r
```

and reports **source `.ok`, target `.ub` at the copy**. The copy's range
read and the destination chain's pointer-cell read land on the SAME cell
(p's storage) through different tags:

- mirlite: read through `t(q2)` (top of the stack) succeeds; THEN the
  chain reads through `t(q)`, popping the Unique `t(q2)` above it. Fine.
- compiled: the chain's read through `t(q)` runs FIRST and pops
  `t(q2)`; the `Memcpy`'s read through `t(q2)` then finds no such tag
  and traps.

`ptrCast` is outside CoreProg, so the CLOSED theorem is unaffected — but
the compiler and the semantics both support it today, so this is a live
miscompilation for programs the frontier work will eventually cover.

## What rustc does (checked, not recalled)

`rustc -Zunpretty=mir` on `unsafe fn g(s: &mut (usize, *mut usize), v: *const usize) { *s.1 = *v; }`
(rustc 1.91.0) gives

```
bb2: {
    _3 = (*_2);                                  // the source read, into a TEMP
    _4 = deref_copy ((*_1).1: *mut usize);       // THEN the destination chain
    ...
}
bb1: { (*_4) = move _3; }                        // then the store
```

So rustc materializes the copied value into a temporary and reads it
BEFORE evaluating the destination place. mirlite's rhs-first order is
faithful to that; OUR COMPILER is the outlier.

## Why the class is nevertheless TRUE inside CoreProg
The two reads can only interact at a shared cell: a dst-chain pointer
cell lying inside the source's τ-sized range. Within CoreProg (no
`ptrCast`, no `exposeAddr`) a cell holds a pointer only where the layout
puts one, so such a cell is a `PtrL σ` field of τ — making σ a strict
subterm of τ. The chain then continues from σ, through projections and
derefs (both subterm steps), to a `PtrL τ` it dereferences — making τ a
subterm of σ. `LayoutTy` is an inductive tree, so both cannot hold. The
ranges are disjoint BY TYPING, and cell-wise disjoint reads commute.

## What closing it would cost
Two options, both decisions for the human — but the witness above tilts
the choice:
1. **Compiler change (now the recommended one).** Materialize the copy's
   source into a temporary before the dst lowering, exactly as rustc
   does. Fixes the live `ptrCast` divergence, makes the orders coincide
   so the CoreProg proof needs no commutation argument at all, and is
   the faithful shape. Cost: oseair needs a temp BUFFER for arbitrary
   layouts (a register holds one word), so this is an `Alloc`-and-two-
   `Memcpy`s lowering or a new instruction — emitted code changes for
   every copy.
2. **Invariant strengthening only.** Carry memory well-typedness in
   `CompilerInv` (every `ptrVal` cell sits at a `PtrL`-typed offset of
   its allocation), derive the disjointness above, and add a read-read
   commutation lemma. Closes the CoreProg class without touching the
   compiler — but leaves the `ptrCast` divergence in place for the
   frontier.

Note that `const_write` and `ref` do NOT have this problem: `constInit`
raises no source event, and `ref`'s retag IS emitted in the pre-phase,
so its order already matches.
