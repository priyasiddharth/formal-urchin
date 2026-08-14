# Enums + heap alloc/dealloc landed — 33/75, still zero divergences

[OBS 2026-08-14] Third increment of the day: enums (Option) and heap
allocation/deallocation (Box, std::alloc). Suite:
pass 42 | fail 0 | xfail 0 | xpass 0 | unsupported 67; fail tests 33/75
verdict-conformant (29 line-accurate), verified from the manifest (see
[[2026-08-14-count-correction]]).

[FACT] Enum encoding: monomorphized enum decls lower to
`TupL (NatL :: mergedPayload)` — a discriminant word plus the
prefix-merged payload cells of all variants (variants must be
prefix-compatible, Option-style; else unsupported). Variant aggregates
desugar to a discriminant write + payload-field writes. The seam-retag
of an enum-typed value copies the discriminant and retags each payload
ref under `Stmt.assignIf` — a runtime discriminant guard — so a None
value never triggers a spurious retag. pass_invalid_shr_option fails
exactly through that guarded retag, at Miri's line.

[FACT] Miri retags reference-typed values LOADED through a pointer
indirection (that is precisely what load_invalid_mut/shr test: the
error is "retag", not "read access"). Loader rule: `dst := copy p`
where `p` contains a deref and the loaded type contains refs →
emitSeamCopy (unprotected). Plain ref copies without deref stay
tag-preserving.

[FACT] Box and Layout are Opaque in monomorphized charon output; the
Box pointee is inferred from deref-projection use sites (the projection
node's own `ty` is the pointee) in a prescan, and Box maps to a mutable
raw pointer — Miri's "implicit raw" reading, minus the Unique box
retag (noted divergence; box_exclusive_violation1 agrees regardless).
Layout maps to its size word; `from_size_align_unchecked` is shimmed to
pass the size through, so `alloc(layout)` reads a runtime size.

[FACT] sb_dealloc (src/obseq3/sb.lean): per cell, the deallocating tag
must exist (miri phrase: "deallocation through tag N: that tag does not
exist in the borrow stack") and grant writes; ANY protected item in the
stack blocks deallocation; the stack is then removed, so dangling
accesses fail with "no borrow stack" (the bump allocator never reuses
addresses). Freed memory cells are dropped from the map.
