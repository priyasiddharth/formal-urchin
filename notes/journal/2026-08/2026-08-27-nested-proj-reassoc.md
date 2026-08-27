# Nested projections reassociate: the divergence fixed at its root

[FACT] `placeToRegChecked` and `placeToBorrowRegChecked` now REASSOCIATE
projection chains: `.proj (.proj b q) p` compiles as
`.proj b (q.append p)` (new `PathTo.append`, offset additive by
`offset_append`). A nested projection therefore emits ONE `Borrow` —
anchored at the chain root, at the composed offset, with the FINAL
field's `blockSize` — instead of retagging every intermediate place. GEP
remains a borrow, exactly as the user specified; it just spans the
accessed field. This closes `local/nested_proj_borrow`: differential
matched 81 | mismatch 0, corpus and all 39 unit tests unchanged.

[FACT] The elaborator was the reason nesting arose at all:
`elabPlaceAux` emits one `.proj` per field with a singleton path
(`.field i .nil`), so every multi-field access is proj-of-proj. The fix
went into the COMPILER, not the elaborator, because the correctness
theorem quantifies over all core programs — an elaborator fix would have
left the theorem false for hand-written nested-proj programs.

[FACT] Termination: reassociation is not structural (the composed place
is not a subterm), so both lowering functions became well-founded, with
`Place.depth` (constructor count) as the measure — reassociation shortens
the place by one constructor whatever the paths' sizes, which `sizeOf`
does not see cleanly (the auto-generated `sizeOf` on the dependent
`PathTo.field` defeated `omega`).

[EMP] (Lean 4.28) the REAL cost of a def going structural → well-founded
is the loss of definitional unfolding, and it is bounded and mechanical:
- every `:= rfl` closed-form of the function breaks; `by simp only [f]`
  (the generated equation lemmas) replaces it — 6 sites here;
- equations for a match arm whose pattern OVERLAPS an earlier arm become
  conditional: the generic-proj equation now carries "base is not a
  proj". `placeToRegChecked_proj_root_eq` packages it (proved by `cases`
  on the base, one arm each); the two run lemmas gained the hypothesis
  and their `.local`-based consumers discharge it with `fun _ _ _ h => by
  cases h` (`Place.noConfusion` unapplied does NOT elaborate to False —
  it is the curried noConfusionType);
- structural inductions over the argument break where the new arm
  recurses on a non-subterm; the generated FUNCTIONAL induction principle
  (`f.induct`, targets in motive order — here `τ, kind, p`) is the
  drop-in replacement, and its case3 hands you exactly the
  not-a-proj hypothesis the conditional equation needs. Two proofs
  converted (`placeToRegChecked_emits_preserves_mem`, the totality
  lemma); the deref case's IH arrives pre-instantiated at `Shared`.

[FACT] d26 (`compile_tests`) pins the fix in-repo, and its teeth are
verified the standard way: with the reassociation arms reverted it fails
with `target ub 5, source ok` — the exact divergence. The suite witness
alone would not run under `--unit`.

[FACT] Consequence for the audit: `const_write_proj_nonlocal_residual`
and `const_write_deref_nonspine_simulation` are TRUE again (they were
FALSE for six hours). Nested-local-rooted bases no longer reach the
general arm at all; the only shapes left in those residuals are
DEREF-rooted, provable by `loadSpine_lowering_sim` composed with the C1
pattern, plus a mirlite resolution-composition lemma (`resolvePlaceAcc`
offsets add) for the reassociation cases.

Validation: units 15/15 + 39/39 (d26 new), suite pass 81 | fail 0 |
unsupported 41 (122), differential matched 81 | mismatch 0 | skipped 0,
all targets build, axioms unchanged (spot-checked C1, spine, ref L→L,
totality).

**References:** compile.lean (reassoc arms), syntax.lean
(`PathTo.append`, `Place.depth`), 2026-08-27-regime-c-closed.md,
conformance/local/nested_proj_borrow.rs.
