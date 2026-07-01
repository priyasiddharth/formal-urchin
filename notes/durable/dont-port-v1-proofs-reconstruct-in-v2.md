# Don't port v1 proofs — reconstruct natively from v2 primitives

Load this when tempted to reuse `src/obseq/proof/` code for an obseq2
lemma.

[FACT] Verdict of the 2026-06-17 planning session: v1's
`existing_write_simulation` (src/obseq/proof/state_helpers.lean:2929)
is dominated by machinery v2 was designed to delete. Only the
seven-step phase skeleton transfers — and that is already encoded in
common.lean's factoring. Lift the *plan*, write the *script* against
v2 primitives.
→ obseq2-comparison.md, 2026-06-17 entry ("Reconstruct-not-Port")

| Concern | v1 approach (don't port) | v2 native (use this) |
|---|---|---|
| Fragment placement | list-slice lemmas, `StartsAt` lists | code-map `simp` + `compileProgFrom_code_eq_compileStmt` |
| State monotonicity | `*_state_incr` lemma family | `CompilerM.incr` witness |
| Type consistency | large explicit obligations | free (intrinsic typing) |
| Invariant | `StateSim` + `TargetNonInterference` | single 9-conjunct `CompilerInv` |
| Execution | `StepStar` | `runN n` + `oseair_runN_add` |
| Pointer-in-register | `place_runtime_sim` hypothesis | `PlaceRegReady` (packages the `useMut` witness) |

## Why this matters

A line-by-line port re-derives v1's scaffolding shape and then fights
every v2 abstraction to map it back. v1 stays useful only as a
phase-structure reference (its `existing_write_simulation` *is* the
seven-step shape, buried under type-tracking v2 removed).

## See also

- rho-maps-are-identity-on-domain.md
