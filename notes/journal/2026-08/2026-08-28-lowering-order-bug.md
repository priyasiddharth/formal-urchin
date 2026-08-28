# 2026-08-28 (night) — d34: a REACHABLE divergence — the lowering-order bug

## The finding
`d34_deref_dst_temp_killed_by_rhs_spine` (compile_tests): the first
divergence pinned on a REACHABLE state — a genuine compiler bug, not
an invariant gap. All raw-pointer steps, both machines' semantics
defined:

    t : (u64, *mut u64);  x : u64
    t.1 := &raw mut x;  p := &raw mut t;  w := &raw mut t.1
    (*p).1 := &mut **w        -- source .ok, target .ub 5

Source: resolution reads cell a+1 via t_w (raw read), retags x, writes
a+1 through t_p — raws survive foreign reads; succeeds. Target: the
dst lowering mints its temporary Borrow(Mut) on a+1 BEFORE the rhs
runs; the rhs spine's legitimate Load of a+1 (a pointer cell on its
own path) and the fresh Unique kill each other (order depends on SRW
grouping); the fragment errs. Verified by execution on first run —
the differential harness returned exactly (.ok, .ub 5).

## Why no invariant or event fix can help
Both machines' behaviors are DEFINED here; simulation must preserve
the source's success. The bug is the compiler's op order: the dst
temporary straddles rhs evaluation. The fix is the lowering order MIR
itself uses — evaluate the rhs to a temporary FIRST, then lower the
dst and store (`tmp = rhs; dst = move tmp`) — so no dst borrow is
live while rhs code runs. Model/compiler decision: PARKED for the
user. When it lands, d34's docstring says to flip it to
`expectDiff .ok`, and the non-local-dst residuals lose their
interleaving obstacle entirely (the keystone phases become adjacent
again), leaving only the separation-invariant question for
proj-vs-proj overlap.

## Taxonomy after this (the three divergence classes)
1. junk-state gaps, event-fixable (retag bound — FIXED 2026-08-28).
2. junk-state gaps, invariant-fixable (d33 overlap — separation
   conjunct, parked).
3. reachable divergences = compiler bugs (d34 — lowering order,
   parked).
