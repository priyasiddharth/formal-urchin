# 2026-08-29 (fifth) — copy: unbound destinations, every source shape

## What happened
`copy_place_residual` narrowed to ONE class. Two new leaves close an
unbound destination whose source is proj-topped:
`copy_fresh_projchain_zero_simulation` (`Alloc; Memcpy`) and
`copy_fresh_projchain_offset_simulation`
(`Alloc; Borrow(Shared); Memcpy; Die`). With the chain-source leaf from
the previous increment, a fresh local destination now accepts every
source spelling, routed by the src flatten transfer.

## Shape
Both leaves are assemblies of two working proofs:
- PREFIX from `copy_fresh_chainsrc_simulation`: invert
  `preparePlaceAssign` into the abstract post-allocation state `s1`,
  extend both renames (`extendBlock` for ρa), execute the root `Alloc`,
  then call the mother lemma at (post-Alloc compiler state, post-Alloc
  machine state) under the extended renames.
- ENDGAME from the corresponding bound-dst leaf: the projection's own
  instructions, with the destination register being the root `Alloc`'s
  and the destination binding read out of the mother lemma's
  `LocalBindingSim` at the fresh local.
The zero-offset leaf was produced by a mechanical transform of the
chain-src leaf; the nonzero one by splicing the offset endgame onto the
same prefix.

## Potholes (new)
- `emit_state_incr` in TERM position with `_` placeholders elaborates
  fine, but the same chain written with `refine … ?_` fails to
  synthesize `s2`/`instrs` — the expected type is only known once the
  whole chain is assembled. Keep these chains term-mode.
- Register distinctness (`R csPrefix.nextReg ≠ R (run … ).nextReg`) is
  NOT a `grind` fact: the monotonicity hypothesis mentions the emit
  tower's `nextReg` projections. Restate the bound as an explicit
  `have` (with `simp only [setPlaceInfo, emit]`), then
  `intro`/`injection`/`omega`.

## Witness
d58: `x := copy s.0` (zero offset) and `y := copy s.1` (nonzero) into
destinations the statements themselves allocate. Teeth: point the
`Memcpy` at the destination register → both diverge with target UB.
71/71.

## State
Full build green; 17/17 + 71/71; corpus 82/0/123; audit exact at 2.
copy's LAST class: NON-LOCAL destinations (`(*p).f := copy s`), where
the compiled order is src-lowering, dst-lowering, `Memcpy`, then BOTH
cleanups — two place lowerings composed, plus two `Die`s.
