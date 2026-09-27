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
