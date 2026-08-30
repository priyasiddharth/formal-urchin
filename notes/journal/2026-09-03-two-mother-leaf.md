# 2026-09-03 (ninth) — the two-mother leaf: non-local destinations

## What happened
`copy_chaindst_chainsrc_simulation` closes `*Q := copy src` for a
canonical-chain destination AND source — the first leaf in the
development that composes TWO mother-lemma calls.

Order (identical on both machines, which is only true since the
temp-assignment lowering): source lowering → the READ (`Load` into a
fresh register) → destination lowering → the write (`RStore`).

## The three things that made it work
1. **The register frame.** The temporary holding the copied value must
   survive the destination lowering. That is exactly the mother lemma's
   register-frame conjunct (`∀ r, RegisterBelow cs.nextReg r → lookup
   preserved`), instantiated at the temp — which is below the second
   mother's starting `nextReg` by construction.
2. **`PtrChain.placeToRegChecked_placeRegMap`** (spine.lean): a chain's
   lowering never touches `placeRegMap`. The mother produces this as an
   OUTPUT, but the second lowering needs it as an INPUT (to transfer
   `PlaceInputsMapped` past the first lowering, before any mother has
   run). Induction on the CHAIN, not the place — the chain grammar has
   no proj-of-proj, so it is structural.
3. **The value fragment stated over the GENERAL cleanup.** The
   statement's value is needed before the mother tells us the source
   cleanup is empty, so `compileStmt_copy_chaindst_value` quantifies
   over `sOut.result.cleanup` while the run fragment (used after) takes
   `h_sclean`.

## Potholes (new)
- `StateIncr` chains over an emit tower do not elaborate with `_`
  placeholders: the intermediate states are metavariables until the
  outer type is known. Pin every state, or use a helper with explicit
  arguments (`emit_tower_incr₃`). Note the tower here is TWO emits, not
  three — `emit_nil` collapses the empty post-cleanup.
- `List.map (fun x => Instr.Die x.fst x.snd)` needs its binder ANNOTATED
  (`fun (x : Register × Nat) => …`) when written by hand, or the pattern
  carries metavariables and will not match the goal.
- The two code-inclusion facts are at DIFFERENT states: labels below the
  post-`Load` state (for the `Load` itself) and labels below the
  destination run (for its own instructions). They need separate
  `StateIncr`s; one does not imply the other.

## Grind pass
Condensed the tag-bound chain, the register-bound chain, and the
address-domain proof (4 explicit `Nat.le_trans`/rewrite steps → `grind`
with the pieces in scope). Leaf: 601 → 596 lines.

## Witness
d60 `*p := copy y` and `*p := copy *q`. Teeth: pointing the `RStore` at
the SOURCE register makes the target write through a Shared borrow →
target UB where the source is fine. (A duplicated store does NOT bite —
writing the same values twice through the same tag is behaviourally
identical, which is worth remembering when choosing an inverse edit.)

## State
Full build green; 17/17 + 73/73; corpus 82/0/123; audit exact at 2.
`copy_place_residual` now names only: deref destinations that need
FLATTENING first (the compiled transfer for this statement shape is
unwritten — mechanical), and PROJECTED destinations.

## Addendum — the deref-dst flatten transfer (same day)
`compileStmt_copy_derefdst_srcflatten_run/_value` and
`..._dstflatten_run/_value` complete the arm: the dispatcher flattens
the source, then the destination, then calls the two-mother leaf, so
every deref-destination spelling whose flattened source is a chain is
covered (d61: `*(s.f.g) := copy y` and the copy back out).

The lesson that cost the iterations: do NOT attempt both flattenings in
one lemma. The nested case split leaves the two sides' states spelled
differently at every branch, and the alignment rewrites stop firing.
Two single-split lemmas compose cleanly — for the source step the
destination lowering is literally the same place at equal states (so the
ok/ok case closes by `simp only [hO, hF, h_sres, h_sagr]`), and for the
destination step the source pre-phase is untouched.

Second lesson: pick ONE spelling of the post-`Load` state per proof and
stay in it. Unfolding `CompilerM.run`/`emitM` rewrites the state to
`(ensurePlaceRoot _ cs).snd.val`-flavoured terms, and every later `cases`
scrutinee must match that, or the match never reduces and the closers
report "no progress".
