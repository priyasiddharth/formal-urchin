# OSEA-v3: SkipIf — the first (forward-only) branch (matched 71)

[OBS 2026-08-15] `assignIf` compiles: `Instr.SkipIf discrPtr val skip`
is the target's first control-flow instruction, and the `Prog = Nat →
Option Instr` code-map design (chosen 2026-04-28 for exactly this)
absorbed it without touching stepWith's shape. Differential:
**matched 71 | mismatch 0 | skipped 5** (was 68/0/8) — all 3 enum tests
agree. Remaining: ptrCast 3 · ptrOffset 2.

Design points:

[FACT] SkipIf is an event-free memory peek: mirlite's assignIf reads
the discriminant with a raw `mem.find?`, NOT an SB read, so SkipIf
does the same (register → addr → find?; non-word → the same error).
On mismatch `pc += 1 + skip`; forward-only, statically bounded, so the
fuel bound (`emittedLabels + 2`) and stmt-range attribution are
untouched — the assignIf statement's contiguous `[start,end)` range
covers SkipIf plus the guarded block, so guard-true body UB attributes
to the assignIf statement (d18 pins this).

[FACT] The skip count is measured by a **dry-run compilation**
(`emitSkipIfAround`): compile the guarded block from the current
state, take the nextLabel delta, emit SkipIf, compile again for real.
Sound because both runs start from the same nextReg/placeRegMap and
instructions carry only registers and *relative* skips — content is
start-label-independent. A failing body rejects the statement without
emitting.

[FACT] The skip must suppress the block's *SB events*, not just its
store — mirlite's guard-false path never evaluates the rhs. d17 pins
it: a guarded write to a mutably-borrowed field leaves the borrow
alive when skipped; executing the block's Borrow would have popped it.

[HYP → latent asymmetry, recorded not fixed] A **fresh local** first
assigned inside a guard-false assignIf: mirlite would allocate it on a
later assignment (preparePlaceAssign), but the compiler's placeRegMap
statically maps it at the guarded Alloc, which the skip jumped over —
a later unconditional assign would RStore into a never-assigned
register (target UB) where mirlite allocates and proceeds. Not
reachable from the corpus: seam assignIf destinations are enum payload
fields whose root is always pre-assigned by aggregate desugar. The
differential harness will catch it if it ever surfaces.

New tests (29/29 — count now derived from allTests): golden g11
(SkipIf 1 3 over Borrow/CStore/Die), d16 guard-true, d17 skip
suppresses events, d18 guard-true body UB at the assignIf stmt.

**References:** 2026-08-15-osea-exposed-provenance.md, dev-log
2026-04-28 (code-map representation), loose-ends/parked.md (assignIf
bullet marked done).
