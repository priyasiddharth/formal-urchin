# OSEA-v3: uninit compiles with no new instruction (matched 56)

[OBS 2026-08-15] `RExpr.uninit` (statics hoisting's materializer) now
compiles: `CStore (layoutToTyVal τ) (replicate (blockSize τ) Val.Undef)`.
No new instruction — CStore already stores arbitrary `Val` lists through
a useMut write, which is exactly mirlite's undef-fill event
(`replicate blockSize undef` + `finishPlaceAssign` useMut). Golden g7
pins the shape; d9 runs the statics shape (uninit → overwrite → copy)
and a partially-initialized tuple whose undef cell flows through Memcpy
without a verdict.

Differential: **matched 56 | mismatch 0 | skipped 20** (was 53/0/23).
uninit was the first blocker in only 3 of its 6 tests — the histogram
reshuffled to alloc 7 · exposeAddr 5 · assignIf 3 · ptrCast 3 ·
ptrOffset 2. Unit tests 16/16.

[FACT] Undef cells are verdict-inert on both machines: reads/copies of
undef are permission events only (SB doesn't inspect values), so a
partially-initialized aggregate copies identically. Only value-directed
operations (fromExposed's address read, assignIf's discriminant,
AllocLen) reject undef — none of which uninit feeds in the compiled set.

**References:** 2026-08-15-osea-protector-frames.md,
loose-ends/parked.md (uninit bullet marked done).
