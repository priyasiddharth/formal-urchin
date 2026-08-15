# OSEA-v3: refSlice lands — FULL SUITE DIFFERENTIAL (76/76, 0 mismatch)

[OBS 2026-08-15] `Rhs.BorrowRest (kind, prot, srcPtr)` — the runtime-
length slice retag — was the last uncompiled construct. Differential:
**matched 76 | mismatch 0 | skipped 0**. Every conformance test that
passes under mirlite now compiles to OSEA-IR and produces the same
verdict, with every UB attributed to the same source statement. The
compiler is TOTAL on obseq3's statement/rvalue surface (g5 now
witnesses totality — a program using every construct family compiles —
replacing the retired unsupported-witness test).

[FACT] BorrowRest reads the fat pointer cell (1 cell, place's tag),
takes `len := size - offset` from the STORED value at runtime, and
calls `M.ref (base+offset) len tag kind prot []` — mirlite's
`.refSlice` verbatim, mask always empty for slice data. It is the only
Borrow whose length is not compiler-static, which is exactly why it
could not reuse `Rhs.Borrow`.

[OBS 2026-08-15] Milestone summary — eight increments in two days,
each landing with zero differential mismatches on first run:
v3 IR+compiler core (25) → protector frames (53) → uninit (56) →
heap alloc/dealloc (63) → exposed provenance (68) → SkipIf (71) →
ptrCast/ptrOffset (75) → refSlice (76/76). Three constructs needed no
new instruction (uninit, ptrCast, const-alloc); the risk register's
three GEP hazards never fired; the harness caught zero divergences —
which is itself evidence that matching mirlite's event ORDER
statement-by-statement (root-alloc first, reads inside instructions,
Die only for minted tags) was the right compilation discipline.

New tests (36/36): golden g13 (BorrowRest with kind/prot), d22 (Mut
slice retag over runtime len 2, write + owner read back), d23 (the
fnentry_invalidation2 mechanism: the slice retag's write access pops a
shared ref above the raw; using it is UB at the same stmt).

**References:** 2026-08-15-osea-ptr-ops.md, loose-ends/parked.md
("OSEA-v3 remaining increments" — section CLOSED), conformance/README.md.
