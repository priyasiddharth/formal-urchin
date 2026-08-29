# 2026-09-03 (later) — Regime B-proj: the second sorry dies

## What happened
`const_write_proj_nonlocal_residual` is DELETED — whitelist 3 → 2.
Its last class (unbound roots) closed as
`const_write_proj_fresh_simulation`: `s.f := v` with `s` unbound, any
offset. Source: `preparePlaceAssign` → `allocateRoot` → `allocateBase`
allocates the σ-sized root and binds it. Compiled: `ensurePlaceRoot`'s
`ensureLocalRegE` fresh arm emits the root `Alloc` + placeRegMap entry,
then the C0/C1 shapes over the fresh register:
`[Alloc; CStore]` at offset 0, `[Alloc; Borrow(Mut); CStore; Die]`
(BRIDGE 1) otherwise.

## The new piece: block-wide ρa extension
The bare-local regime B extended ρa by ONE identity pair — enough for
`blockSize NatL = 1`. A projected dst's root is a TUPLE:
`LocalBindingSim`'s block-domain conjunct quantifies over every
`k < blockSize σ`, and the nonzero-offset write itself lands at
`base + offset`. New machinery (common.lean):
`AddrRenameMap.extendIdRange ρa base n` (identity over `[base, base+n)`)
with `AddrRenameIncr.extendIdRange` / `IdentityOnDomain.extendIdRange`
(no freshness side conditions — same argument as `extend_id`) and
`extendIdRange_mem`. ρt still extends by the single minted root tag.

## Shapes
- Fragments `compileStmt_proj_fresh_zero_run` /
  `compileStmt_proj_fresh_offset_run` / `compileStmt_proj_fresh_value`:
  `ensureLocalRegE_fresh` + `placeToRegChecked_local_existing` at the
  post-`setPlaceInfo` state + the proj-root equation. (The offset run
  needed a trailing `rfl` — the emit tower's `nextReg` projections
  differ only definitionally.)
- Leaf: fresh-local regime B's §1–§3 skeleton (own on both machines,
  `sb_own_respects_PermSim`, lockstep base address) at `blockSize σ`;
  the Borrow's bound comes from TYPING (`PathTo.offset_add_size_le` —
  `h_fit : offset + 1 ≤ blockSize σ`), the write transported under the
  EXTENDED renames, BRIDGE 1 through the fresh tag over the fresh
  block. Both endgames built clean on first submission — the crib
  discipline (fresh-local §§ + the collapsed C-deref endgame) pays.

## Witness
d54: `s.1 := 9` as s's FIRST touch (fresh root, NONZERO offset — the
Alloc must size the whole tuple), then `s.0`, `t.0` (fresh, zero),
copies out. Teeth: undersized the root Alloc
(`Rhs.Alloc NatTy` instead of `layoutToTyVal τ`, both occurrences in
`ensureLocalRegE`) → d54 fails with target UB (the field-1 Borrow
falls out of the 1-cell block); restored. 67/67.

## State
Full build green; 17/17 + 67/67; corpus 82/0/123; audit exact at TWO
sorries: `copy_place_residual`, `ref_place_residual`. Next: copy's
remaining classes (proj-topped srcs over non-local bases, unbound dst,
non-local dst) and ref's (proj-topped dsts over non-local bases,
non-local srcs under non-local dsts, unbound roots).
