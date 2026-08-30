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

## Confirmed against the real toolchain (Miri, rustc 1.91.0 nightly)

Both claims were RUN, not inferred:

1. The witness shape, transliterated to Rust, executes CLEAN under Miri
   with Stacked Borrows:
   ```rust
   let mut x: usize = 5;
   let mut p: *mut usize = &mut x;
   let q: *mut *mut usize = &mut p;
   unsafe {
       let q2: *mut *mut usize = &mut *q;    // Unique reborrow of p's cell
       let r: *mut usize = q2 as *mut usize; // same cell, viewed as usize
       **q = *r;
   }
   ```
   `cargo +nightly miri run` prints and exits 0. Its MIR is
   ```
   _11 = (*_9);                  // the source read, into a temp
   _27 = deref_copy (*_4);       // THEN the destination chain's pointer read
   (*_27) = move _11;
   ```
   So Miri accepts exactly the program our compiled code traps on: this
   is bad codegen against Rust, not only against mirlite.

2. The EXACT overlap `*p = *p` (same address, same length) also runs
   clean under Miri, and its MIR is `_5 = (*_2); (*_2) = move _5`.

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

## The same missing temp ALSO makes our copy stricter than Rust

Separate symptom, same cause. mirlite's `doAssign` rejects a copy whose
source and destination ranges overlap ("copy of overlapping ranges"),
and oseair's `Memcpy` carries a nonoverlapping precondition; d35 pins
`x := copy x` as UB on both machines. But rustc's temporary makes an
overlapping assignment WELL-DEFINED — `_3 = (*_2); (*_1) = move _3`
reads before it writes. So our model is stricter than Rust on this
program. That is sound for the refinement (we only relate
source-successful runs) but it is a fidelity gap, and introducing the
temp would close it: the overlap guard could then go away entirely.

NOT the same thing as the witness above. In that witness the source
range (the cell holding `p`) and the destination range (the cell
holding `x`) are DISJOINT — the guard correctly does not fire, and the
source runs clean. The collision there is between the source range and
a pointer cell the destination chain reads on its way, which no overlap
guard covers.

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
