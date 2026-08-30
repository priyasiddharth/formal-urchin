# 2026-08-29 — Ref's deref dst closed (`*P := &src`); grind audit of the delta

## What closed
`ref_derefdst_local_simulation`: `*P := &kind src` for any all-deref
LoadSpine P (so `**q := &x` etc. too), src a bound local. Fragment
`[Borrow(src); spine Loads; Load; RStore]` — MIR order puts the rhs
Borrow FIRST, which is exactly why the rhs-first doAssign swap was the
prerequisite. Dispatcher deref-dst arm wired (local src + spine;
everything else falls to the residual, which is narrowed to projected
deref dsts / non-spine derefs / non-local srcs). d43 exercises it
end-to-end (store the ref through a loaded pointer, then write through
it via a double deref); teeth: swapping the RStore operands breaks the
suite.

## The new lemma muscle
`loadSpine_lowering_sim` gained a REGISTER-FRAME conjunct (appended,
so consumers just add `-` or a name to their obtain): the spine writes
only fresh registers ≥ cs.nextReg, so any register below survives.
That is what carries the borrow temp `R csPrefix.nextReg` across the
spine to the final RStore. Base case `fun _ _ => rfl`; step case one
`lookup_insert_ne` off the ih.

## Composition notes (what the leaf actually does)
prepare = identity on a resolvable deref root (const_write's h_pre
pattern); rhs retag transported FIRST (`sb_ref_respects_PermSim`,
extending ρt by the mint pair); the spine prelude instantiated at the
POST-retag source state and post-Borrow target state under the
extended rename (PlaceInputsMapped at cs1 via
`resolvePlace?_of_resolveAcc h_dres` + the cs1 LocalBindingSim — NOT
via defeq from csPrefix, which is stuck on a variable place); Load =
sb_read transport + MemValSim inversion; RStore = BRIDGE 2
(`writeThroughPtr_sim`) through the loaded tag, bounds from the source
write check via `o' = o ∧ s' = s`.

## Potholes hit (all catalogued ones)
- subst roulette: `subst h_s1` (s1 = s_mir) ate s_mir; use `rw at`.
- atom-splitting: `simp only [emit] at h_le` split the run-argument
  atom from the goal's spelling — defeq-RESTATE the hypothesis at the
  goal's spelling instead of unfolding.
- h_pprm's rhs is cs1.placeRegMap (emit-form); a `show`-reduced goal
  at csPrefix.placeRegMap can't be rewritten by it — defeq-restate
  h_pprm at csPrefix first.
- `cases h : value ...` for StateIncr — unnecessary; `split` +
  `CheckedCompilerM.incr _ _` per arm is the whole proof.

## grind audit (user-requested, delta since 09d5472)
10 sites collapsed:
- copy.lean: h_qAcc (rw+injection+exact → grind), h_cs (show+rw+exact
  → grind [getPlaceInfo]).
- const_write.lean: 2× h_osz Nat-chains → grind; 3× h_qAcc C-deref
  twins (the carry-over the LAST audit flagged) → grind; the
  1144-line Nat.not_lt chain → grind.
- ref.lean: h_qAcc → grind; h_offlt's simpa-have deleted (bare grind).
1 rejection: const_write's h_cs (grind [getPlaceInfo] fails there —
its placeRegMap chain routes through an extra state; kept manual).
Left as-is: the spelling-workaround `show` chains (blockSize/
layoutSize) and cases-before-`RegisterBelow` — those ARE the known
grind-pothole workarounds; keystone's inline `(by omega)` side
conditions are already minimal.

## State
All targets green; units 17/17 + 56/56 (d43 new); suite 82/123
(0 fail); axiom audit exact; audit at 4. Next: `(*p).f := &x`
(projected deref dsts) or copy's non-local dst arms.
