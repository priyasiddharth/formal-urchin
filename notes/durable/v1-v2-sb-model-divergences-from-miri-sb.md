# v1/v2 SB model divergences from Miri's Stacked Borrows

Recorded 2026-08-14 during the SB-conformance audit (repo @ 52ec1e0).
These describe v1 (`src/obseq/sb.lean`) and v2 (which reuses it via
`src/obseq2/permission.lean`). obseq3 is planned to fix the first two —
see plans/sb_conformance_obseq3.md; this note stays durable as a
statement about v1/v2, which are frozen.

[FACT] Raw pointers are never writable — there is no SharedReadOnly vs
SharedReadWrite distinction. `sb_use_mb` grants writes only to
`Own`/`MutRef` and rejects `RawPtr` (src/obseq/sb.lean:596-600). So the
canonical Miri pattern `&mut x as *mut T` followed by a write through
the raw is UB in this model but legal under real SB.

[FACT] `sb_ref` with a `Raw` kind performs a *mutable* parent access
(`sb_use_mb`) unconditionally (src/obseq/sb.lean:783), so even
`&x as *const T` off a shared reference is UB here. Real SB does a read
access for const raws.

[FACT] Borrow stacks exist only at allocation base addresses. `sb_own`
is called exactly once per allocation, at the base (call sites:
src/obseq/mirlite.lean:350, src/obseq/oseair.lean:173,
src/obseq2/oseair.lean:145). Any SB access at `base + k`, `k > 0`
(i.e. any tuple-field access past field 0) fails with "address not
found". Miri keeps a stack per byte. Related: accesses are performed
once per *place*, not per covered cell (`writeResolvedPlace` calls
`M.useMut` once at the base then writes `blockSize τ` cells,
src/obseq2/mirlite_semantics.lean:154).

[FACT] The SB-enforcing semantics (obseq v1, obseq2) have zero
executable tests. All executable tests live in `src/interp/`
(test_mirlight.lean, test_oseairlight.lean, test_compile.lean), and
`grep -rn 'sb_' src/interp/` is empty — interp threads `AccessPerms`
through but only ever calls `freshTag`. See also
[[v1-obseq-is-axiom-backed-check-before-citing]].

[FACT] Also absent from the model (out of scope for obseq3 by
decision, listed for the conformance claim's exclusions): protectors
(no function boundaries exist at all), two-phase borrows, UnsafeCell/
interior-mutability retagging, deallocation (bump allocator never
frees), int↔ptr casts/exposed provenance, SRW adjacent-item grouping.
