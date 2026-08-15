# OSEA-v3: protector frames (matched 25 → 53, mismatch 0)

[OBS 2026-08-15] Same-day follow-up to the v3 compiler landing:
`Instr.PushProt`/`PopProt` in oseair (calling `M.pushFrame` /
`M.popFrame`, error on pop propagating as target UB) and direct
emission from `Stmt.pushProtectors`/`popProtectors`. The protected
seam-retag borrows already carried `prot` into `Rhs.Borrow` — only the
frame bracketing was missing, which is why this increment is ~20 lines.

Differential suite: **matched 53 | mismatch 0 | skipped 23** (was
25/0/51). Every inlined-call test whose body is otherwise core now runs
through the compiler and agrees with mirlite — including the protector
UB tests, attributed to the same source statement. New unit tests:
golden g6 (Push/Pop bracket a protected Borrow), d7 (owner write while
protected = UB at same stmt on both machines), d8 (after PopProt the
same write is ok).

[OBS 2026-08-15] `assignIf` (3 tests) surfaced from behind
pushProtectors in the skip histogram — enum tests were double-blocked.
Remaining skips: alloc 6 · uninit 6 · exposeAddr 5 · assignIf 3 ·
ptrCast 2 · ptrOffset 1.

**References:** 2026-08-15-osea-v3-compiler-landed.md,
loose-ends/parked.md ("OSEA-v3 remaining increments" — first item
marked done).
