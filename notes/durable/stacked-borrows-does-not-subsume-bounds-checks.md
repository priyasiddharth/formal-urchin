# Stacked borrows does not subsume bounds checks

Load this when reasoning about write safety, `writeThroughPtr` /
`writeResolvedPlace` error branches, or a proposal to drop a bounds
side-condition "because SB catches it".

[FACT] Stacked borrows is a per-address permission model ("does tag T
have permission at address A?"), orthogonal to allocation bounds ("is
A within allocation B?"). An OOB write landing in another *live*
allocation passes SB if the tag is valid there; an in-bounds write
through an expired borrow passes the bounds check. Both checks are
needed. → obseq2-comparison.md 2026-04-25

[FACT] Both sides check the same end-of-write bounds predicate — the
entire write range must fit in the allocation:
- mirlite `writeResolvedPlace`: errors when
  `dst.addr + values.length > dst.allocBase + dst.allocSize`
  (`PlaceRes` carries `allocBase`/`allocSize` for exactly this)
- oseair `writeThroughPtr`: errors when `addr + vals.length > base + size`
For well-typed programs `PathTo` guarantees the bound statically and
the check never fires; it exists for future raw pointer arithmetic,
and matching predicates on both sides is what preserves simulation.

[FACT] Two v1-invisible target bugs were fixed alongside (2026-04-25):
`RStore`/`CStore` ignored their `ty` field (now validated:
`srcTy == ty`, `vals.length == typeSize ty`), and the original bounds
check tested only the write start, not the end. Both were invisible in
v1 because its proofs never constrained the relevant variables.

## Why this matters

The source non-OOB hypothesis (from `writeResolvedPlace`'s ok-branch)
is what `writeThroughPtr_sim` transports to the target — the shared
predicate shape is load-bearing for the simulation, not just a safety
nicety. And it's a live example of proofs mirroring semantics bugs:
an unconstrained variable in a lemma statement can hide a real defect.

## See also

- writethroughptr-sim-is-place-kind-agnostic.md
