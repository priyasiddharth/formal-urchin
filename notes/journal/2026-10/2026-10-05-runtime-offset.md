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

## Later: run-time index into an array by dispatch (parked y, option 1)

[DEC] (user) Option 1: `dispatchRuntimeIndex` (emit.lean). A statement
whose destination or value has `a[i]`, with `i` unknown, becomes
`assignIf i k (dst := rv)[i := k]` for each `k < N`.
- Each guard reads `i`. Miri reads it once, and re-reading with the same
  tag changes no stack.
- Only the matching branch performs its accesses.
- No pointer and no retag, as with Miri's place projection.
- MIR's bounds assert precedes the dispatch, and the certificate checks
  it at run time.
- Covered: copy/move/constant values and `&a[i]` (also through a
  pointer, `(*p)[i]`), for types without references.
- The tracker forgets the array (destination) or the destination value.
[OBS] The user asked why not a binOp on pointers. Arithmetic was never
the gap (`ptrOffsetBy` is pointer-plus-integer). The gap is the first
pointer to a local, which only a retag makes in mirlite.
[OBS] Witnesses, all Miri-verified:
- array_index_runtime_ok;
- keeps_shared: ok; a `&raw mut` retag would pop the shared borrow, so
  this would be a false UB under the rejected lowering;
- ref_popped: UB;
- ref_other_elem: ok, per-byte stacks.
The first versions of ref_popped/_other_elem failed rustc's borrow check
and were rewritten through a raw pointer.
Corpus 186/0/0/18 of 204; no proof change.

## Later: option 2, `addrOf` — and a correction

[OBS] CORRECTION, superseding the "Correction to my own plan" above and
the keeps_shared remark: a `&raw mut` retag is NOT an access in Miri. In
`from_ref_ty`, `RawPtr Mut` gives SharedReadWrite with `access: None`, and
`grant` inserts it right above the parent's granting item, so it pops
nothing. Indexing a local array through `&raw mut a` would therefore not
have been a false UB; it would only add a stack item Miri does not create.
The model agrees: compiler test d120, planned as a "pops the shared
borrow" contrast, came out ok on both machines, and it now pins this
rule. The user's question "why do we need 2" got a wrong answer from me
on this point (the arithmetic part of that answer stands).

[DEC] (user) Option 2 anyway, being the faithful lowering (no extra item).
- `RExpr.addrOf loc path` (local-rooted only, so the result is exactly
  the place's provenance): `ptrVal base (offset of path) (field size)
  (local size) (owning tag)`, no event.
- Target `Rhs.PlaceAddr reg offB extB`: moves the pointer value in the
  local's own register. No borrow, so no route tag.
- Proof `addrOf_pkg` (proof/addrof.lean, new file): `LocalBindingSimB`
  gives the register `Ptr base 0 _ size tag'` with ρt(owning) = tag', and
  `placeToRegChecked_local_existing` the code shape. 784 declarations,
  3 axioms, 0 sorries.
- Compiler tests d118 (write/read through it), d119 (a read keeps a
  shared borrow), d120 (pins a raw mut retag as no access), d121 (a
  write through it pops the shared borrow: UB at the same statement on
  both machines).
- Loader `arrayElemPlace`: a local-rooted `a[i]` (no dereference before
  the index) is `t := addrOf(a.0); t := ptrOffsetBy t i; (*t)…`. The
  dispatch stays for `(*p)[i]`.
- Local witnesses array_index_runtime_refs_{ok,popped}: arrays of
  references, which the dispatch rejected. In _popped, Miri reports UB at
  the retag of the loaded reference (line 12), and the model agrees.
- Corpus 188/0/0/18 of 206; units 33 + 145.

## Later: the dispatch is gone

[DEC] The user asked whether `assignIf` is still needed once branches have
certificates. Inventory of the loader's uses: certificate checks, enum-seam
retags, `format!` assumptions, and the run-time array dispatch. The last
was a lowering choice, not a need: `(*p)[i]` is Miri's place projection
through `p`'s own tag, the same shape as slice data.

[OBS] `arrayElemPlace` now covers `(*q)[i]`: `t := copy q` at type
`*mut Elem` (a tag-preserving `ptrCast` at elaboration), `t := ptrOffsetBy
t i`, place `(*t)…`. `dispatchRuntimeIndex` deleted; a run-time index the
lowering cannot reach (`(*p).f[i]`) is now `unsupported`. Both `(*p)[i]`
witnesses (`array_index_runtime_ref_popped`, `_ref_other_elem`) still
pass with Miri's line and reason; the dump shows `ptrOffsetBy`, no
`assignIf`. Corpus 188/0/0/18 of 206, `--osea` 188, `--layouts` 188, units
33 + 149. No proof change (the loader is outside the proof).
