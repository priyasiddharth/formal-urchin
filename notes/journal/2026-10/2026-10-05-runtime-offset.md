# 2026-10-05 — Array guard and run-time pointer offsets

## Context

[OBS] Probing the 18 unsupported Miri entries (loader only, one artifact
at a time with `ulimit -v 4 GB` / `timeout 20`) found that
zst-field-retagging-terminates exhausts memory. `[(); usize::MAX]` is
expanded element by element, in the type (`parseTy`'s `Array` case) and in
`Repeat` (`List.replicate n`). Miri keeps arrays symbolic: the layout is
(count, stride, size), and its retag walk skips values with nothing to
retag. That probe was also what made the background run get killed for low
memory on 2026-10-04.

## Decisions (user: "do 1 and 2")

[DEC] 1. Guard: arrays and array repeats with more than `maxArrayLen`
(4096) elements are unsupported. The test is now rejected at once.

[DEC] 2. A run-time `ptrOffset` instead of an array type in mirlite:
- source `RExpr.ptrOffsetBy p i inbounds` (`i` an integer place);
- target `Rhs.PtrOffsetBy t elemSizeB rp ri inbounds`;
- both copy-read the two places into registers (subSlice's pattern)
  and call the shared `bytes.Mem.offsetPtr` with `t.toInt w · stride`.
Proof: `ptrOffsetBy_pkg` (slice.lean, adapted from `subSlice_pkg`). The
check transports by `offsetPtr_congr` and the lockstep freed lists, plus
the program-counter case, `RhsB`, and coverage. It built on the first
try; 782 declarations, 3 axioms, 0 sorries.

[OBS] Correction to my own plan: lowering a run-time `a[i]` on a LOCAL
array as "pointer to a[0], move by i" is wrong. Taking the pointer needs
a `&raw` retag, an access Miri does not perform (Miri's index is a place
projection), so it would pop shared borrows of the array (false UB).
Where a pointer already exists there is no retag, and that is what
ships:
- `ptr.add(i)`/`offset(i)`/`wrapping_*` with a place count always use
  `ptrOffsetBy`, even when the tracker knows the value: a tracked
  constant is a bit pattern, and `ptrOffsetBy` reads it at its (maybe
  signed) type;
- slice data `(*s)[i]` with an unknown `i` goes through
  `ptrOffsetBy s i` (MIR's own bounds assert precedes it).
The local-array case stays unsupported; the options are in parked item y.

[OBS] Results:
- buggy_split_at_mut passes (`ptr.add(mid)`).
- New Miri-verified witnesses: ptr_add_runtime_{ok,oob} and
  slice_index_runtime_{ok,other_elem,popped}. other_elem was meant as a
  UB witness, but Miri said ok: the raw write hit element 0 and the read
  element 2, and stacks are per byte. It is kept as an ok witness and
  _popped writes the same element (UB at the read).
- The stale manifest reasons for interior_mutability, smallvec,
  unknown-bottom-gc, zst-field-retagging-terminates and
  box-custom-alloc-aliasing were replaced by the probed blockers.
- Units 33 + 141; corpus 182/0/0/18 of 200; --osea 182; --layouts 182.
