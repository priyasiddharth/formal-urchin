# 2026-09-03 (fourth) — copy: one source leaf, and fresh destinations

## What happened
Two steps on `copy_place_residual`.

1. **L→L retired.** `copy_deref_local_simulation` generalized from a
   `.deref P` source to ANY `src` with `PtrChain src`, becoming
   `copy_chainsrc_local_simulation`. A bound local source is
   `PtrChain.base`, so the old two-mapped-locals leaf and its fragments
   (210 lines) were deleted; the dispatcher's local-src arm passes
   `(fun _ => rfl)` / `(fun _ so h => ⟨so, h⟩)` as its stmt0 transfer.
2. **Regime B for copy.** `copy_fresh_chainsrc_simulation`:
   `dst := copy src` where the destination local is UNBOUND. The source
   allocates and binds the destination BEFORE reading the source, and
   `ensureLocalRegE` emits the matching root `Alloc`; the mother lemma
   is then called at the POST-allocation states (compiler state
   `setPlaceInfo (emit … [Alloc]) …`, machine state after the Alloc
   step) under both EXTENDED renames, and one `Memcpy` finishes.

## New machinery
- `AddrRenameMap.extendBlock ρa base n` = `extend base base` then
  `extendIdRange base n`. A ZERO-SIZED destination has an empty block,
  so `extendIdRange` alone leaves its base unmapped — but the binding
  still needs `ρa base = some base`. `const_write`'s regime-B-proj leaf
  did not hit this because a projection to a `NatL` leaf proves the root
  is non-empty; a copy destination can be any layout.
- `mirlite_readWordSeq_congr`: `readWordSeq` observes memory only
  through `find?`, so allocation (which bumps `addrStart`/`allocs`)
  does not change what it reads.

## Potholes (new)
- **Keep the post-allocation state ABSTRACT.** Writing the allocated
  state as a record literal inside a `cases` scrutinee hits the
  multiline record-`with` parse failure. Instead, do NOT `subst` the
  allocation equation: keep `s1` and derive `s1.env`, `s1.perms`,
  `s1.pc`, `s1.mem.addrStart` and `find? s1.mem = find? s_mir.mem` as
  small bridging `have`s. Every downstream lemma then takes `s1`.
- **`show … .placeRegMap.lookup …` blocks `getPlaceInfo_setPlaceInfo_ne`**
  (the `show` unfolds `getPlaceInfo`, so the rewrite finds no match).
  Introduce one `h_gp : ∀ i, getPlaceInfo (run … cs1) i = getPlaceInfo cs1 i`
  right after the mother call and rewrite with it in every bullet.
- A whole-file `str.replace` on a common tactic block can hit the WRONG
  leaf (two leaves shared the same `intro τ' loc' h_none` opening); the
  stray edit compiled as a type error 1500 lines away from where it was
  made. Anchor replacements on text unique to the target proof.

## Witness
d57: `t := copy s` and `y := copy (*p).0` into freshly-allocated locals,
plus a chain-source read. Teeth: undersize the fresh-local `Alloc` to
one cell → target traps where the source does not. 70/70.

## State
Full build green; 17/17 + 70/70; corpus 82/0/123; audit exact at 2.
copy's remaining classes: unbound dst with a PROJ-TOPPED src (needs the
same Alloc composition with the projection endgames) and NON-LOCAL dst.
