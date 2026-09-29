# 2026-09-29 — Fn pointers through moved arguments (survey item e)

[OBS] Fn pointers are tracked statically (`LowerSt.fnPtrs`: local ↦ fun
id; `.fnRef` writes a placeholder 0 and records the target; `.callDyn`
inlines the recorded target). `emitAssign` propagated the entry on
`.use (.copy|.move p)`, but a moved call argument is bound by
`emitSeamBind` with mirlite's own `.move p` rvalue, whose branch pushed
the assignment only — so `inner(x, f)` left `f` untracked in the callee.

[FACT] Fix: `propagateFnPtr st src dst` (whole-local → whole-local), used
by both branches. No mirlite/oseair/proof change.

[OBS] New entries, all three failing on the pre-fix binary with
"indirect call with unknown target" and passing now:
- local/fn_ptr_moved_arg (Miri ok);
- fail/both_borrows/deallocate_against_protector1 — prep: closure →
  `fn free_it`, `Box::leak(Box::new(0))` → `alloc` + store,
  `drop(Box::from_raw(raw))` → `dealloc` (Box drop is item p). Miri and
  model: UB line 19, "deallocating while item … is strongly protected".
- fail/both_borrows/deallocate_against_protector2 — prep: the same plus
  `.cast()` → `as`, `Layout::new::<i32>()` → `from_size_align_unchecked`.
  Miri and model: UB line 21, the tag derived from the zero-sized `x` does
  not exist for the i32's cells.
Upstream both raise the error inside std (`error-in-other-file`); with
`dealloc` called directly the span lands in the test, so the lines pin.

[OBS] All 141 existing entries lower byte-identically to the pre-fix
binary. Corpus 115/0/29, osea 115; live Miri 115/115, 0 drift.

## See also
2026-09-28-enum-payload-read.md, loose-ends/parked.md § A′ e
