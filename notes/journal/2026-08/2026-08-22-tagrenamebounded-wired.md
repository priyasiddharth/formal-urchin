# `TagRenameBounded` is an invariant conjunct: the `sb_ref` member is now applicable

[FACT] `CompilerInv` (proof/common.lean) carries an eighth conjunct,
`TagRenameBounded ρt s_mir.perms.NextTag s_osea.perms.NextTag`. This is the
hypothesis every consumer of `sb_ref_respects_PermSim` needs, so the member
went from "proved" to "usable at a leaf" in one increment. Audit unchanged
at 5 sorries — no leaf was closed, but three of them lost their last
machinery blocker.

[FACT] Re-establishing the conjunct at the closed sites cost essentially
nothing, and the reason is worth stating as the general principle: the
bound only moves when a counter moves, and the three access ops do not
move counters. `sb_write_NextTag`, `sb_read_NextTag`, `sb_die_NextTag`
(permsim_transport.lean) each fall straight out of `foldCells_ok_inv` —
the fold's result is `{ ap with StackMap := … }`, so `NextTag` is
syntactically the old one. Regime A and the deref spine then discharge
their new obligation by rewriting the bound through those equalities and
handing back the incoming `h_tbd` unchanged.

[FACT] `loadSpine_lowering_sim` (proof/spine.lean) gained two conjuncts of
the same kind — `permsD.NextTag = s_mir.perms.NextTag` and
`s_osea'.perms.NextTag = s_osea.perms.NextTag`. The spine performs only
reads on both machines, so both are provable, and without them a consumer
cannot carry the bound across a spine of unknown depth (the induction is
where the counters would otherwise become opaque). Base case: two `rfl`s.
Step case: the IH's equality composed with `sb_read_NextTag` on each side.

[OBS 2026-08-22] The wiring touched exactly four proof obligations —
two `CompilerInv` construction sites (regime A, regime D spine) and the
two spine cases — plus three destructuring patterns. That is a smaller
blast radius than the conjunct count suggests, and the reason is that
`CompilerInv` is built in only two places today; the delegating theorems
pass it through. Expect the same cheapness for the lockstep-allocation
conjunct that regime B still needs.

[HYP] The `sb_own` member will reuse this increment wholesale.
`sb_own` mints exactly as `sb_ref` does (`freshTag`, then a fold that only
touches `StackMap`), so `TagRenameWF.extend`/`TagRenameIncr.extend`/
`TagRenameBounded.extend` should apply verbatim and the member should cost
a fraction of `sb_ref`'s — its per-cell op is `ownCell`, with no kind
analysis, no mask and no protector tail. If that holds, regime B's
remaining blocker is only the lockstep-allocation conjunct.

Validation: units 15/15 + 38/38, suite pass 77 | fail 0 (117),
differential matched 77 | mismatch 0 | skipped 0, obseq2 green. No model
files changed this increment (proof layer only). The closed leaves stay
axiom-clean: `const_write_local_existing_simulation`,
`const_write_deref_spine_simulation` and `loadSpine_lowering_sim` all
report only propext / Classical.choice / Quot.sound.

**References:** proof/compiler.lean (audit),
2026-08-22-sb-ref-transport.md, loose-ends/parked.md → "obseq3 proof
closure".
