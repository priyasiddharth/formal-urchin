# 2026-08-29 (cont. 3) — Ref's first non-local destination: L→P0

## What closed
`ref_local_projzero_simulation`: `dst.g := &src`, both roots bound,
`g` at offset 0 — the first NON-LOCAL DESTINATION regime outside
const_write. The projection returns the dst base register, so the
fragment is L→L's `[Borrow; RStore]` and the proof is L→L with a wider
resolved destination ({addr := bD.addr + 0, allocSize := blockSize σ}),
exactly the C0-widens-A pattern. d40 covers it differentially,
including a later write THROUGH the stored field reference (53/53).

## The one structural novelty (MIR order in fragment lemmas)
The dst lowering runs AFTER the rhs pre-phase, so the fragment lemma's
base-register facts must be taken at the POST-BorrowS compiler state,
not at `cs` — `placeToRegChecked_local_existing` instantiated at
`emit {cs with nextReg+1} [BorrowS]` via getPlaceInfo_emit/setNextReg.
First build failed exactly there (the value at `cs` didn't match the
goal's state); the pattern will recur in every non-local-dst fragment
lemma.

## Potholes
- `omega` on `bD.addr + 0 - bD.addr = 0` — Word projection blindness;
  `Nat.sub_self` by defeq instead.
- grind + `layoutSize (PtrL τ)` opacity — feed `= 1 := rfl`.

## Next in the class
The NONZERO field dst: `[BorrowS(src); BorrowM(dst field); RStore;
Die]` — BRIDGE 1 around the store composed with the rhs retag's ρt
extension (two target mints, one source mint). Then the dst flattening
recursion (stmt0 triples, as const_write) and deref dsts.

## State
All targets green; units 17/17 + 53/53; suite 82/123; axiom audit
exact; audit at 4.
