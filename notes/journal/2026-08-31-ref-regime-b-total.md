# ref regime B is total: the mother lemma at a post-Alloc state

Date: 2026-08-31
Tags: obseq3, ref, regime-B, spine, mother-lemma

## [FACT] all four unbound-root sites are closed

`ref_fresh_derefsrc_simulation` proves `dst := &kind *chain` with
`dst`'s root UNBOUND, the last of the four. `ref_place_residual`'s
remaining classes no longer include unbound destination roots.

## [FACT] the shape of the crossing

The previous three leaves crossed the fresh-root axis with an extra
INSTRUCTION (an interior borrow, or nothing at all). This one crosses
it with the SPINE: `ptrChain_lowering_sim` has to be applied at the
post-`Alloc` compiler state

```
csA = setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 }
        [Assgn (R cs.nextReg) (Alloc (layoutToTyVal (PtrL τ)))])
        cs.idx (R cs.nextReg, PtrL τ)
```

and the post-`Alloc` oseair state, under the ALREADY-extended ρa and
ρt. So its whole hypothesis bundle is re-established MID-PROOF:
`LocalBindingSim`, `PlaceRegMapBound`, `SourceMemSim`, `PermSim`, the
pc agreement, the instruction transfer. Every other fresh-root leaf
only ever needed those at the very end.

That sounded expensive and was not, because `copy`'s
`copy_projlocal_fresh_zero_simulation` had already solved exactly this
problem — its source lowering also runs after the root allocation. Its
`h_prb1` and `h_lbs1` blocks transferred almost verbatim (rename `loc`
to `dstLoc`, `σ` to `PtrL τ`). The lesson generalises: when a new leaf
needs an invariant at an UNUSUAL point in the statement, look for
another statement form that already had to pass through that point,
not for a leaf of the same statement form.

## [OBS] `simp only [emit]` splits the atom when the state is an argument

The compiled state `csA` contains an `emit`, and it appears as an
ARGUMENT to `CheckedCompilerM.run`. Putting `emit` in a `simp only` set
then unfolds it in both positions but at different rates, so `omega`
sees two unrelated atoms for what is one term:

```
d := (run (placeToRegChecked ...) (setPlaceInfo (emit { ... } [...]) ...)).nextLabel
f := (run (placeToRegChecked ...) (setPlaceInfo { ... unfolded ... } ...)).nextLabel
```

Fix: use the PROJECTION lemmas — `emit_nextLabel`, `setPlaceInfo_nextLabel`,
`emit_nextReg`, `setPlaceInfo_nextReg` (csnorm's set) — which rewrite
`(emit cs l).nextLabel` without touching `emit` inside the run's
argument. Three `omega` failures became zero.

This is the general rule behind csnorm, now with a second symptom: not
only do record-update spellings fail to match, but unfolding a
definition that also occurs inside an opaque argument silently creates
a second atom.

## [OBS] subst direction is not the one you wrote

`subst h_deq` on `h_deq : dOut = dOut0` eliminated `dOut0`, not `dOut`
— Lean picks the variable it can eliminate, which here was the one
introduced EARLIER. Four downstream references to `dOut0.result.reg`
had to become `dOut.result.reg`. Read the traced state rather than
predicting which name survives.

Also: `LocalBindingSim.insert_fresh_reg`'s final `rfl` argument cannot
infer the target oseair state on its own; the `have` needs a full type
ascription naming that state.

## [FACT] d79's teeth

`s := &mut y` held live across `t := &mut *r`. Reborrowing through `r`
touches only `x`, so `*s := 8` afterwards is defined. Point the
reborrow at `*s` instead and it becomes a CHILD of `s`, which the later
write through `s` pops — `*t := 9` then reads a popped tag. Control run
reports `ub` at statement 6.

## state

Build green; 17/17 + 92/92; audit exact at ONE sorry. Residual call
sites 9 -> 8. `ref_place_residual`'s remaining classes: non-local srcs
under non-local dsts, non-spine deref srcs, proj-of-proj srcs.
