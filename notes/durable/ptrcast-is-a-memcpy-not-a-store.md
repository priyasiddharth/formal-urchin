# `ptrCast` is a Memcpy, which is why it is still outside the theorem

Load this when asking why `ptrCast` (and `ptrOffset`, `refSlice`) are
excluded from `CoreRhs` although they are implemented and tested, or
when scoping the work to admit them.

[FACT, 2026-09-14] **What it is.** A tag-PRESERVING pointer type-punning
cast — Rust's `p as *mut U`. Typed
`ptrCast : Place Γ (PtrL σ) → RExpr Γ (PtrL τ)` (src/obseq3/syntax.lean:99):
the pointee layout changes, nothing else does. mirlite reads ONE cell
through the source place's own tag and hands the cell straight back
(`mirlite_semantics.lean:262`): `resolvePlaceAcc`, then
`M.read permsR resolved.addr 1 resolved.tag`, then
`readWordSeq mem resolved.addr 1`. So the provenance in the pointer VALUE
rides along unchanged — contrast `.ref`, which mints, and `fromExposed`,
which produces `wildcardTag` (see
[[raw-pointer-provenance-is-the-wildcard-tag]]). The SB event is one
read at the source, and no write to the pointer's own storage cell.

[FACT, 2026-09-14] **What it compiles to.** ONE instruction, and it is
neither of the two stores every admitted rvalue uses
(`compile.lean:625`):

    placeToRegChecked Shared src
    Memcpy dstPtr srcReg PTy        -- the whole rvalue's `store` field
    (postCleanup := srcRes.cleanup) -- NOT [] — the source borrow is retired after

`Memcpy` (`oseair.lean:384`) reads both registers as pointers, checks
BOTH ranges in bounds, rejects overlap ("Memcpy models a NONOVERLAPPING
copy", mirroring mirlite's overlapping-assignment guard), then does
`M.read` at the source, `M.useMut` at the destination, and copies the
cells.

[FACT, 2026-09-14] **Why that blocks the shared leaves.** Since
2026-09-14 every destination leaf is stated over
`StoreStep compProg sR bound mkStore vals` — see
[[valuepkg-one-leaf-per-destination]] if that note exists, else
spine.lean's `ValuePkg`. Three things do not fit:
1. `vals` is fixed BEFORE the store runs (a register's contents, or the
   instruction's own list). Memcpy's values are `readWordSeq` at the
   SOURCE at execution time, so they are not available when the package
   is built.
2. `StoreStep` reduces the instruction to `writeThroughPtr`, which
   performs one `useMut`. Memcpy performs a `read` at the source AND a
   `useMut` at the destination — two SB events in one instruction, and
   the read is the rvalue's, not the destination's.
3. `postCleanup` is non-empty, where `ValuePkg` demands `[]`; the source
   place's borrow is retired after the store, not before it.
Admitting `ptrCast` therefore means a second store abstraction (values
produced by a source-side read, two permission events), not a third
`StoreStep` instance. That is a strictly bigger change than the one that
admitted the constant stores.

[FACT, 2026-09-14] **It is exercised, just not proven.** Compiler-witness
corpus: `d19 ptrCast roundtrip` (cast a `&raw mut`, write through the
cast pointer, read the original back), `d20 cast_then_offset_into_pair`,
and `d59`. All differential — both machines must agree on the verdict.
So the gap is in the THEOREM's scope, not in the implementation or its
testing; `compiler.lean`'s scope list says the same under (a).

→ src/obseq3/syntax.lean:99, mirlite_semantics.lean:262,
  compile.lean:521/625, oseair.lean:117/384,
  proof/common.lean `CoreRhs`
