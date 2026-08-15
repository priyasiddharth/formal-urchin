# OSEA-v3: ptrCast + ptrOffset (matched 75/76 — one refSlice test left)

[OBS 2026-08-15] Both pointer rvalues landed. Differential:
**matched 75 | mismatch 0 | skipped 1** (was 71/0/5). The single
remaining skip is `fail/stacked_borrows/fnentry_invalidation2`, whose
lowering contains a `refSlice` (the as_mut_ptr entry retag) — the last
uncompiled construct.

[FACT] `ptrCast` needed NO new instruction: mirlite's semantics is a
tag-preserving one-cell copy with an SB read, which is exactly
`Memcpy dst src PTy` (read 1 via src tag, useMut 1 via dst tag). Third
construct compiled by reusing an existing instruction (uninit → CStore
of Undef, const alloc → AllocN, now ptrCast → Memcpy) — evidence that
the v2-inherited instruction set plus the v3 additions spans the
source surface economically.

[FACT] `Rhs.PtrOffset (srcPtr) (deltaCells : Int)` carries the delta
**pre-scaled to cells** by the compiler (`delta * blockSize σ`, σ the
source pointee — the compiler knows it statically, same pattern as
`Die`'s length). Runtime: read the pointer cell via the place's tag,
shift the STORED pointer's offset, preserve its tag; negative-past-base
errs ("pointer offset before the allocation base") as mirlite does.
Golden g12 pins the scaling: `.ptrOffset r 1` on a `*mut (u64,u64)`
emits `PtrOffset _ 2`.

New tests (33/33): g12, d19 (cast keeps raw provenance through a write),
d20 (the `(&raw mut tup) as *mut u64` + `.add(1)` idiom — cast to
element type, offset one cell, write via the whole-range raw tag),
d21 (offset before base, UB at the same stmt).

**References:** 2026-08-15-osea-skipif.md, loose-ends/parked.md
(ptrCast/ptrOffset marked done; refSlice is the sole remaining bullet).
