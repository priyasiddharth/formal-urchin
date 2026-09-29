# 2026-09-29 — `Box::into_raw` shim

[FACT] std (pinned toolchain, alloc/src/boxed.rs:1434):
`let mut b = ManuallyDrop::new(b); (&mut **b) as *mut T`, written so SB
sees a retag. Under SB: the fn-entry Unique retag of the Box argument, the
`&mut **b` Unique reborrow, the raw retag (the result). `boxIntoRaw` in
stdlite.lean emits exactly those three; the argument's protector is
omitted (it ends at return; the only accesses meanwhile are reborrows of
its own tag).

[OBS] Witnesses (Miri-checked): local/box_into_raw_ok (ok) and
local/box_into_raw_pops_prior_raw — `r = &mut *b as *mut i32` taken
before `into_raw(b)`, written after: UB line 13, "tag does not exist",
model identical. A copy-only shim would say ok there, so the witness pins
the fn-entry retag. mixed_cell_deallocate's `Box::new` + `into_raw` +
`transmute` restored (only the `Layout::new` → `for_value` rewrite left);
still UB line 18, read-only item does not grant dealloc.

[OBS] Old binary: all three "call to bodyless function into_raw"; the
other 144 entries lower byte-identically. Corpus 118/0/29, osea 118; live
Miri 118/118, 0 drift. The unsupported tests that also call into_raw
(newtype_*, unsafe_cell_deallocate) still need Box drop glue (item p) /
closures / item m.

## See also
2026-09-29-stdlite-module.md, 2026-09-29-box-pointee-inference.md
