# `ptrCast` is a Memcpy, which is why it is still outside the theorem

Load this when asking why `ptrCast` is excluded from `CoreRhs` although
it is implemented and tested, or when scoping the work to admit it.

[FACT, 2026-09-14] **What it is.** A tag-PRESERVING pointer type-punning
cast — Rust's `p as *mut U`. The pointee layout changes and nothing else
does.
→ src/obseq3/syntax.lean:99

    | ptrCast : Place Γ (obseq.LayoutTy.PtrL σ) → RExpr Γ (obseq.LayoutTy.PtrL τ)

mirlite reads ONE cell through the source place's own tag and hands the
cell straight back, so the provenance inside the pointer VALUE rides
along unchanged — contrast `.ref`, which mints, and `fromExposed`, which
produces `wildcardTag`.
→ src/obseq3/mirlite_semantics.lean:262

    | .ptrCast src =>
        match resolvePlaceAcc M state src with
        | .ok (resolved, permsR) =>
            match M.read permsR resolved.addr 1 resolved.tag with
            | .ok perms' => .ok { values := readWordSeq …  resolved.addr 1, … }

[FACT, 2026-09-14] **What it compiles to.** One instruction, and it is
neither of the two stores every admitted rvalue uses.
→ src/obseq3/compile.lean:625

    let srcOut ← placeToRegChecked RefKind.Shared src
    pure { store := fun dstPtr => [Instr.Memcpy dstPtr srcRes.reg obseq.TyVal.PTy],
           postCleanup := srcRes.cleanup, … }

`Memcpy` reads both registers as pointers, bounds-checks BOTH ranges,
rejects overlap (it "models a NONOVERLAPPING copy", mirroring mirlite's
overlapping-assignment guard), then does `M.read` at the source,
`M.useMut` at the destination, and copies the cells.
→ src/obseq3/oseair.lean:384

[FACT, 2026-09-14] **Why that blocks the shared leaves.** Every
destination leaf is stated over `StoreStep compProg sR bound mkStore
vals` (see one-leaf-per-destination-shape.md). Three things do not fit:

1. `vals` is fixed BEFORE the store runs — a register's contents, or the
   instruction's own list. Memcpy's values are `readWordSeq` at the
   SOURCE at execution time, so they are not available when the package
   is built.
2. `StoreStep` reduces the instruction to `writeThroughPtr`, one
   `useMut`. Memcpy performs a `read` at the source AND a `useMut` at the
   destination — two SB events in one instruction, and the read is the
   rvalue's, not the destination's.
3. `postCleanup` is `srcRes.cleanup`, where `ValuePkg` demands `[]`: the
   source place's borrow is retired AFTER the store.

So admitting `ptrCast` means a second store abstraction — values produced
by a source-side read, two permission events — not a third `StoreStep`
instance.

[FACT, 2026-09-14] **It is exercised, just not proven.** Compiler-witness
corpus: `d19 ptrCast roundtrip` (cast a `&raw mut`, write through the
cast pointer, read the original back), `d20 cast_then_offset_into_pair`,
`d59`. All differential — both machines must agree on the verdict. The
gap is in the THEOREM's scope, not in the implementation or its testing.
→ src/obseq3/compile_tests.lean:525, 538, 1338
→ src/obseq3/proof/compiler.lean, scope list item (a)

## Why this matters

`ptrCast`, `ptrOffset` and `refSlice` are the three rvalues left outside
`compile_correct`. This note says the obstacle for the first one is
structural rather than incidental, and names its shape, so nobody
re-attempts it expecting the constant-store collapse to repeat.

## See also

- one-leaf-per-destination-shape.md
- raw-pointer-provenance-is-the-wildcard-tag.md
- stacked-borrows-does-not-subsume-bounds-checks.md
