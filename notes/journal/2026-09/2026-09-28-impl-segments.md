# 2026-09-28 — Impl blocks are path segments (survey items b, d)

[OBS] The loader named a function by its `Ident` segments only, dropping
Charon's `Impl` elements, so `Cell::get` and `UnsafeCell::get` were both
`core::cell::get` and `Cell::get` ran the raw-reborrow shim ("dst NatL vs
rhs PtrL"). A survey of all 140 artifacts found the same collapse for
`core::cell::new` (Cell / RefCell / UnsafeCell), `core::cell::deref`
(`<Ref as Deref>` / `<RefMut as Deref>`) and `get_mut`.

[FACT] Now `nameSegs` renders an inherent impl as its self type's head
(`Cell`, `*mut T`, `[T]`, `[T; N]`, `i32`) and a trait impl as
`<Self as Trait>`. Every shim literal was rewritten from a data-derived
old→new table (a Python copy of the rule over every artifact); where one
old literal covered several functions with the same semantics, the shim
lists each (`Cell|UnsafeCell|RefCell::new`, `Cell|RefCell::replace`,
`*::get_mut`, both `deref`s). New: a `Cell::get` shim (masked shared
reborrow, then a read — `Cell::set`'s shape with a read), and
`Cell::get(&C) -> T` feeds the cell-pointee prescan.

[OBS] The old `core::slice::index::get_unchecked{,_mut}` literals matched
nothing: the real functions are inherent, `core::slice::[T]::get_unchecked`.
They now point there; a usize index is still rejected ("slice index by
nat"), so only range calls take the sub-slice shim.

[OBS] Behaviour check: the pre-change binary (scratch worktree at HEAD)
and the new one produce IDENTICAL `--dump` output for all 140 entries.

[OBS] Unlocked: box-cell-alias runs its upstream body (`val.get()` and
`assert_eq!` restored; only the annotation strip remains);
interior_mutability::two_phase split out and passes with one runtime
certificate check. That needed `miri_cert.py` to accept
`<std::cell::Cell<i32> as main::Thing>::do_the_thing` as a user frame
(it rejected any path containing `std::`), plus bug d's trailing-`::`
fix. Corpus 110/0/31, osea 110, certificates 36 entries / 48 checked;
live: Miri 110/110, 0 drift.

## See also
2026-09-27-unsupported-survey.md, loose-ends/parked.md § A′ b/d
