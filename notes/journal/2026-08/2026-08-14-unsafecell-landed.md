# UnsafeCell / interior mutability landed — 36/75, zero divergences

[OBS 2026-08-14] Fourth increment: interior mutability. Suite:
pass 47 | fail 0 | xfail 0 | xpass 0 | unsupported 63; fail tests 36/75
verdict-conformant (32 line-accurate), 11 pass scenarios. New:
interior_mut1 (ub@13, miri's line), illegal_read7 (ub@17),
mixed_mutability_static (ub@16, frozen-vs-cell field split), pass
cell_inside_struct and interior_mutability::unsafe_cell_invalidate.

[FACT] Freeze-mask design: shared AND raw-const retags take a
type-derived per-cell mask (true = inside UnsafeCell); masked cells get
a SharedReadWrite item inserted above the granting item with NO access,
unmasked cells freeze (read access + Ref/RawConst push). The mask is
computed by the loader from `UPlace.ty` at elaboration
(conformance.freezeMask) and carried on `RExpr.ref` — LayoutTy itself
stays cell-agnostic, so obseq.types is untouched. `&mut` retags ignore
the mask (Unique everywhere), matching Miri.

[FACT] Protection is WEAK on SharedReadWrite items: Miri allows popping
and even deallocating protected SRW items (pass test
unsafe_cell_invalidate — "writing to y invalidates x, but that is
okay"); only protected Unique/frozen items make a pop UB
(invalidate_against_protector1/2 still fail correctly).
Implementation: obseq3.firstProtected skips `RawPtr true` items.

[FACT] UnsafeCell/Cell decls are Opaque in charon output and their
`new`/`get` are bodyless. Pointees are inferred from call sites
(`new(v) -> C` gives C ↦ ty(v); `get(&C) -> *mut T` gives C ↦ T), with
a one-word fallback; `Atomic*` maps to a one-word cell by name. Shims:
cell `new` = identity (layout-transparent), cell `get` = a masked
shared reborrow of the pointee (exactly Miri's mechanics: the retag
happens at the &self boundary), `ptr::read` = a deref read.

[FACT] Pointer type-punning casts (`p as *mut U` with a different
pointee layout) are tag-preserving one-cell reinterprets — new
`RExpr.ptrCast`, produced by the elaborator when a pointer copy's
source and destination layouts disagree.
