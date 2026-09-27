# 2026-09-27 — survey of the 39 unsupported conformance entries

[OBS] Four read-only agents charon-compiled every unsupported source
and ran the loader on it (scratch manifests, nothing committed). The
per-test feature list is in parked.md, MASTER INVENTORY § A′.

Headlines:
- [OBS] illegal_read5 and track_caller already pass on the raw source;
  their manifest reasons ("Rc", "closures") are stale. Six more flip with
  a prep alone, and 2phase::two_phase1 passes as a split-out.
- [OBS] Three loader/tooling bugs: `Cell::get` is caught by the
  `UnsafeCell::get` shim; enum-variant field projections drop the
  variant (cell 0 = discriminant); `miri_cert.py` `last_segment`
  returns "" for turbofish frames.
- [HYP, source-backed] `containsRef (.structT _) = false` rests on
  fnentry_invalidation2, which passes `&mut Thing` and so says nothing
  about by-value struct fields; newtype_retagging tests exactly that
  retag. Flipping it is the only change the two newtype tests need.
- [OBS] `[(); usize::MAX]` hangs the loader; the loop visit budget
  rejects certified loops beyond a few iterations.

## See also
loose-ends/parked.md (§ A′)

## Later: Tier 0 landed

[OBS] Ten entries flipped with preps only: illegal_read5, track_caller
(raw source), illegal_read3 (union → `*const i32`),
mut_exclusive_violation2 (NonNull → raw), mixed_cell_deallocate
(alloc for Box), box-cell-alias (trailing `val.get()` dropped),
issue-miri-2389 and write_does_not_invalidate_all_aliases (`.cast` →
`as`), and two 2phase split-outs (two_phase1; two_phase_overlapping2
with a local `AddAssign` trait). Each prep got a certificate from the
pinned Miri, and every fail entry's expected line is Miri's own
(16, 10, 18, 17, 18, 11). Corpus 109/0/31, osea 109 matched,
certificates 35 entries / 47 checked (27 static, 20 runtime) / 0
unchecked; units 18/18, 129/129. No Lean change.

[OBS] box-cell-alias's expected line moved 9 → 11: the prep gained two
header lines. drop_in_place_protector's heavy prep was NOT taken; it
waits for the drop_in_place shim (§ A′ q).
