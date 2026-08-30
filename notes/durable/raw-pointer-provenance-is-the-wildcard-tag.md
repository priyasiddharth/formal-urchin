# Raw pointers: the LOCAL has a unique tag, the VALUE may be the wildcard

Load this when a lemma's `(tag == wildcardTag) = false` side condition
looks gratuitous, or when reasoning about `exposeAddr`/`fromExposed`.

[FACT, 2026-08-30] **Two tags, routinely conflated.**
1. *The local's storage tag.* A local of pointer layout `PtrL τ` is
   allocated like any other: `allocateBase` → `own` → `freshTag`. So the
   VARIABLE `p` has a unique tag governing accesses to the pointer-sized
   cell that holds the pointer. `LocalBindingSim` carries it as
   `binding.tag`, always with `(binding.tag == wildcardTag) = false`,
   which holds structurally — `freshTag` starts at 1 and
   `wildcardTag = 0` (src/obseq3/sb.lean:149), so no minted tag collides.
2. *The tag inside the pointer VALUE.* That belongs to the referent's
   borrow stack and depends on how the pointer was produced: `.ref`
   mints a fresh unique tag and pushes it; `ptrCast`/`ptrOffset` carry
   the existing one along; `refSlice` mints; and `fromExposed`
   (int-to-ptr) produces `wildcardTag` — deliberately NOT unique
   (src/obseq3/mirlite_semantics.lean, `.fromExposed` arm).

[FACT, 2026-08-30] **Wildcard resolution is per-cell and optimistic.**
An access through tag 0 is not looked up in the stack:
`readCellContent`/`writeCellContent` test `tag == wildcardTag` and call
`resolveWildcardIn exposed stack`, which scans the cell's stack top-down
for the topmost item whose tag is in the `exposed` set AND grants the
access, then proceeds as if that tag had been used (Miri's optimistic
wildcard resolution). `exposed` grows via `sb_expose` on a ptr-to-int
cast (`exposeAddr` reads the pointer and exposes ITS tag; exposing the
wildcard is a no-op). No exposed tag grants it ⇒ UB.
→ src/obseq3/sb.lean:169, 226, 265, 327

[FACT, 2026-08-30] **Why the transport lemmas demand non-wildcard.**
`sb_read/write/ref_respects_PermSim` and the mother lemma's
`ρt resolved.tag = some tres` + `(resolved.tag == wildcardTag) = false`
conjuncts move ONE SPECIFIC tag across ρt. A wildcard access has no
specific tag to move — its outcome depends on the whole stack plus the
exposed set. That is why `PermSim` carries an `exposed` component (so
wildcard resolution would agree on both machines) and why
`TagRenameBounded` asserts `wildcardTag < NextTag` on both sides: the
wildcard is a reserved constant BELOW every mintable tag, never
something the allocator hands out.

[OPEN] The wildcard-producing statements (`exposeAddr`, `fromExposed`,
`ptrCast`, `ptrOffset`, `refSlice`) are modeled and conformance-tested
but sit OUTSIDE `CoreProg`: the closed correctness theorem covers
assign/const/copy/ref. Their simulation leaves are frontier-B work, and
a wildcard leaf will need a genuinely different argument from the
tag-transport one (resolution against `exposed`, not renaming).

## See also

- v1-v2-sb-model-divergences-from-miri-sb.md
- sb-conformance-claim.md
