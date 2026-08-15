# OSEA-v3: exposed provenance (matched 68, 89% differential)

[OBS 2026-08-15] `Rhs.ExposeAddr` / `Rhs.FromExposed` landed as a pair
(the 5 blocked tests use both), with the allocs table + `resolveAddr`
finally ported into `oseair.Mem` (the deferred piece dealloc didn't
need). Differential: **matched 68 | mismatch 0 | skipped 8** (was
63/0/13). Remaining: assignIf 3 · ptrCast 3 · ptrOffset 2.

[FACT] Both are Rhs forms mirroring mirlite's rvalues exactly:
- `ExposeAddr srcPtr`: SB-read the pointer cell via the *place's* tag,
  expose the *stored* pointer's tag (`M.expose`), yield
  `Dat (base+off)` — the two-tags-two-roles split (place tag for the
  read, stored tag for the expose) is where a careless port would go
  wrong.
- `FromExposed srcPtr`: SB-read the integer cell, `resolveAddr` it to
  its containing allocation, yield `Ptr base off size wildcardTag`.
  Wildcard *resolution* lives in the permission model (topmost exposed
  granting item at access time), so the machine needs no new logic at
  use sites — a wildcard CStore/Memcpy just calls `M.useMut` with tag 0.

[FACT] `allocate` now records `(base, size)` in `Mem.allocs` for every
allocation (locals and heap — mirlite does the same via its single
`allocate`), which is what makes both machines resolve the same integer
to the same allocation. `removeRange` leaves `allocs` intact, exactly as
mirlite: a resolved-but-dead allocation fails at the perms level.

New tests (25/25): golden g10 (ExposeAddr reads the place, RStores the
numeric address), d14 (full round trip: expose → fromExposed → wildcard
write → owner read, ok), d15 (owner write pops the exposed raw before
the wildcard write — no exposed granting item, UB at the same stmt).
g5's unsupported witness moved to ptrCast.

**References:** 2026-08-15-osea-heap.md, loose-ends/parked.md
(exposeAddr/fromExposed bullet marked done),
durable/sb-conformance-claim.md (wildcard determinization).
