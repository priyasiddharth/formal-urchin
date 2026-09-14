# `ptrCast` was the last Memcpy caller — check for outlier lowerings first

Load this when an rvalue does not fit the shared destination leaves, or
before building proof infrastructure to accommodate an instruction.

[FACT, 2026-09-14] **The rule that found it.** When an rvalue resists the
shared architecture, ask whether its LOWERING is an outlier before asking
what machinery would accept it. `ptrCast` emitted
`Memcpy dstPtr srcReg PTy` while every other read-then-store rvalue
emitted `Load` into a register temporary and then `RStore`. That was not
a design choice about casts; it was a leftover.
→ supersedes ptrcast-is-a-memcpy-not-a-store.md

[FACT, 2026-09-14] **It was a live divergence, not just an inconvenience.**
`.copy` stopped lowering to `Memcpy` on 2026-08-29 (the d34 event-order
fix), and mirlite dropped its overlapping-assignment guard on 2026-08-30
with the reason recorded in `doAssign`: rustc reads through a temporary
(`_3 = (*_2); (*_1) = move _3`), Miri runs `*p = *p` clean, "the compiler
now materializes the same temporary (a register), so both machines are
read-then-write and the guard has nothing left to protect." `ptrCast`
kept the Memcpy, so it kept the overlap REJECTION that mirlite had given
up:

    p = p as *mut U     mirlite: ok        oseair: "Memcpy overlapping ranges"

No executed witness covered it — `g5_compiler_total` writes exactly that
statement but only checks that the compiler accepts the program — so
neither the differential suite nor the ULLBC corpus could see it.
→ src/obseq3/mirlite_semantics.lean, `doAssign`, the 2026-08-30 comment
→ src/obseq3/compile_tests.lean:119

[FACT, 2026-09-14] **The fix was the lowering, and the proof followed.**
With the register temporary materialized, `readRhsShape_ptrCast` holds by
`rfl` — the cast IS copy's compiled shape at a pointer layout — so both
read packages are copy's with only the mirlite inversion changed, and
each delegates to `copy_chainsrc_read` / `copy_projsrc_offset_read`
unaltered. Ninety lines, no new seam, no new store abstraction.
`ptrOffset` went in the same day and the same way, at 400 lines, because
its instruction (`Rhs.PtrOffset`) needed its own step lemma and packages.

## Why this matters

`compile_correct` now covers every rvalue but `refSlice`. More durably:
two of the three excluded rvalues turned out to be excluded for reasons
that dissolved on inspection, and the one real obstacle was an
inconsistency in the COMPILER that the proof effort surfaced. That is the
argument for admitting the remaining fragment rather than assuming the
frontier is where it looks.

## See also

- ptrcast-is-a-memcpy-not-a-store.md
- one-leaf-per-destination-shape.md
- ptroffset-defers-ub-to-the-use.md
