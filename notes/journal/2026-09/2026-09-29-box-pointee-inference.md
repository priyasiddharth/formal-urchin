# 2026-09-29 — Box pointee inference from constructors (survey item f)

[OBS] With `--monomorphize`, Charon emits each `Box<T>` as its own type
decl of kind `"Opaque"` with empty generics (e.g. box_cell_alias decl 0,
`alloc::boxed::Box`), so `T` is not in the type. `collectBoxPointees`
recovered it only from a `Deref` projection whose base is Box-typed; a Box
never written `*b` stayed "Box with uninferred pointee" and the test was
rejected. The pointee ends up as `UTy.boxT T` and, in mirlite, as the
layout index of `PtrL τ` — Box itself does not exist in the syntax.

[FACT] Now also: `Box::new(v: T) -> Box`, `Box::from_raw(p: *mut T) ->
Box`, `Box::into_raw(b) -> *mut T`, `Box::leak(b) -> &mut T` (first use
wins; `boxDeclId`, `ptrPointeeJson`). The prescan needs fun paths, so
`parseCrate` computes `funPaths` before it.

[OBS] Witness local/box_never_derefed fails on the pre-fix binary ("type
Box with uninferred pointee (local _1 used at line 10)") and passes now;
all 144 existing entries lower byte-identically.

[OBS] Unlocks nothing alone: unprepped mixed_cell_deallocate and the
unsafe_cell_deallocate scenario both now stop at "call to bodyless
function into_raw" — item j's `Box::into_raw` shim is next for them.

Corpus 116/0/29, osea 116; live Miri 116/116, 0 drift.

## See also
2026-09-29-fn-ptr-moved-arg.md, loose-ends/parked.md § A′ f, j
