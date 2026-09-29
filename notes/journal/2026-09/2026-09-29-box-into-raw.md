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

## Later: `Box::leak`

[FACT] std: `let (ptr, alloc) = Box::into_raw_with_allocator(b);
mem::forget(alloc); &mut *ptr`, with `into_raw_with_allocator` doing
`&raw mut **b` — fn-entry Unique retags, the raw retag, a Unique reborrow:
`boxIntoRaw` then `&mut *`, which is what `boxLeak` emits. Layers beyond
that (the caller's retag of the returned `&mut`) derive from the shim's own
tags and cannot touch another pointer.

[OBS] local/box_leak_ok (ok; frees via from_raw so Miri's leak check is
quiet) and local/box_leak_pops_prior_raw (UB line 11, as Miri). The two
deallocate_against_protector preps run upstream `Box::leak(Box::new(..))`
again; lines 19/21 unchanged. Old binary: all four "call to bodyless
function leak"; 145 others byte-identical. Corpus 120/0/29, osea 120, live
120/120, 0 drift.

## Later: `<*T>::cast`, `cast_mut`, `cast_const` (survey item a)

[FACT] std: `self as _` — a raw-to-raw cast, no retag; raw arguments are
not retagged at fn entry. `ptrCast` emits a plain copy at the destination
type (ptrCast at elaboration). Witness local/ptr_cast_keeps_tag: casting a
pointer after its tag was popped is fine when unused. [OBS] Made the shim
retag instead (`&raw mut *p`) as a check: the witness then fails with a
false positive at line 14, the cast — so it pins the no-retag property.

[OBS] Upstream `.cast` restored in issue-miri-2389,
write_does_not_invalidate_all_aliases and deallocate_against_protector2
(line 21 kept). Old binary: all four "call to bodyless function cast";
146 others byte-identical. Corpus 121/0/29, osea 121, live 121/121, 0
drift.

## See also
2026-09-29-stdlite-module.md, 2026-09-29-box-pointee-inference.md
