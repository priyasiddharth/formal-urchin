# 2026-10-09 — RefCell::borrow's value pointer is SharedReadWrite (no fix needed)

## Context
The user asked to "fix the frozen &T for borrow's value pointer" (the
2026-10-08 [DEC] said Miri's guard pointer is a frozen `&T` and the
model's a masked shared reborrow) and to add a local test that fails
without the fix.

## Finding
[FACT] std at the pinned toolchain (`library/core/src/cell.rs`):
`try_borrow` stores `NonNull::new_unchecked(self.value.get())`;
`UnsafeCell::get` is `self as *const UnsafeCell<T> as *const T as *mut
T`. So the guard's pointer is RAW, carrying the tag of a shared reborrow
of an `UnsafeCell<T>`: SharedReadWrite over the whole value. The freeze
(Freeze `T`) happens at `Ref::deref` (`NonNull::as_ref`), and again at
the caller's retag of the returned `&T`. The model's masked shared
reborrow of `cell T` is exactly SharedReadWrite. The 2026-10-08 premise
was wrong; there is nothing to fix.
[OBS] Probes against the pinned Miri, all agreeing with the model
before any change: a deref'd `&T` popped by a later `borrow_mut` (UB at
the read), a write through `&*g as *mut` (UB: read-only item), two live
guards (ok), and the two witnesses below.
[OBS] Mutation: freezing the guard pointer (masking the reborrow by `T`
instead of `cell T`) makes `local/refcell_guard_ptr_survives_sibling_write_ok`
a false positive ("retag failed ... tag does not exist", line 13, where
Miri says ok); the rest of the corpus stays 202 + that one. So the change
asked for would have been a regression no earlier test caught.
[OBS] Mutation: making the shim's `deref` SharedReadWrite changes
nothing anywhere: the `&u32` a deref yields is retagged again by the
caller (`&*g`, or the call result's retag), frozen either way. The
shim's own freeze is not observable.

## What changed
- `local/refcell_guard_ptr_survives_sibling_write_ok` (ok): a raw
  pointer to the value from `&rc` (offset 8, after the flag) writes while
  a `Ref` is alive; the guard's SRW pointer survives, `*g` reads 2.
- `local/refcell_deref_frozen_popped_ub` (ub, line 14): the same write
  pops the frozen `&u32` from `&*g`; the read through it is UB, same
  reason as Miri.
- conformance/README.md says why the shared reborrow is SRW; counts
  220 / 203 in CLAUDE.md and the paper.

## Numbers
[OBS] Corpus 203 / 0 / 0 / 17 of 220; reasons 106 as Miri + 2 known; --osea 203 (1008 Dies); --layouts 203; live.py: all 220 Miri verdicts equal the manifest, no drift; audit 3 axioms, 0 sorries, 1234 declarations.
