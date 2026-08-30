# 2026-08-29 — flattenPlace; the FIRST residual dies (4 → 3 sorries)

## What closed
`const_write_deref_deep_residual` is DELETED, along with its nonspine
dispatcher. Regime D (`*P := v`) is TOTAL: every deref dst — any
mixture of stars and fields, proj-of-proj spellings included
(`*(s.f.g) := v`, d50) — routes through the chain leaf. The axiom
whitelist dropped to THREE sorries; `scripts/audit_axioms.sh` confirms.

## The machinery
- `flattenPlace` / `projInto` (spine.lean): recursive reassociation of
  every nested projection. KEY THEOREM `flatten_chainish`: a flattened
  place is a chain or ONE projection over a chain — so a flattened
  DEREF place is ALWAYS a chain (`PtrChain_flatten_deref`). The chain
  grammar is not a fragment; it is a normal form for the whole place
  language.
- Source congruences: resolvePlaceAcc/resolvePlace?/allocateRoot/
  preparePlaceAssign/ensurePlaceRoot are flatten-invariant (structural
  inductions over the existing proj_assoc trio; PathTo.append_assoc
  new).
- `placeToRegChecked_flatten_agree`: the compiled lowering agrees with
  the flattening — run EQUAL, value's RESULT component equal (the
  evidence differs by reassociation wrappers, so the value equality is
  stated through `Except.map (·.result)`). Well-founded on
  `Place.depth` (the assoc step strictly drops it); the proj-of-proj
  case rewrites through `projInto_projInto` + the assoc-arm equation,
  the deref/proj-over-deref cases align the two values by four-way
  case split.
- Statement transfer (`compileStmt_derefdst_flatten_run/_value`) rides
  the stmt0-threading the chain leaf ALREADY had — the canonical
  statement is now the flattened one, and the dispatcher's identity
  transfers became flatten transfers. The stmt0 pattern was built for
  program-vs-canonical gaps; this is its purest use yet.

## Potholes
- The agree facts must be instantiated at the POST-ensure compiler
  state (the dst lowering runs there), and the final simp must NOT
  unfold CompilerM.run (the .snd.val respelling splits the run atom).
- `flattenPlace (pp.deref)` vs `(flattenPlace pp).deref`: defeq but
  not syntactic — normalize hypotheses with a `show ... from rfl`
  rewrite before any rw.
- decreasing_by needs `try omega` (some goals close under simp alone).

## State
All targets green; units 17/17 + 63/63; corpus 82/123 (0 fail); audit
at THREE: ref_place_residual, copy_place_residual,
const_write_proj_nonlocal_residual. Next: the same flatten transfer
for the proj-dst C-deref gates and copy/ref dispatchers (cheap now),
then unbound roots (regime-B) to kill const_write_proj_nonlocal.
