# 2026-08-30 — Ref's dst-flattening recursion

## What closed
`ref_proj_dst_simulation`: nested projection DESTINATIONS of any depth
for ref statements — `s.f.g := &x` etc. The const_write recipe ported
in three moves:
1. stmt0-generalized the two field-dst leaves (same mechanical
   surgery: transfer triple in, fragment-run composed, refine witness
   `run stmt0`).
2. `stepStmt_assign_proj_assoc` (spine.lean): the SOURCE cannot tell
   the spellings apart at the whole-STEP level — `doAssign` consults
   the dst only through prepare/resolveAcc, both already proven to
   compose. Three-line proof. This is cleaner than const_write's
   recursion (which pre-destructured the source facts): ref's threads
   the raw `h_step` through one rewrite per level.
3. The compiled transfer lemmas moved const_write.lean → common.lean
   (they were always rhs-generic; ref.lean doesn't import
   const_write).
The dispatcher's whole proj-dst arm collapsed to ONE call with
identity transfers. `ref_place_residual`'s h_stmt loosened to stmt0
(sorry-side, no cost).

## Pattern status
The statement-transfer recursion is now a reusable recipe: leaves
stmt0-generalized + one source step-transfer + one compiled
run/value-transfer + a base-induction. copy's dispatcher can take it
identically when its non-local dst arms open.

## State
All targets green; units 17/17 + 55/55 (d42: nested-field ref store +
write through it); suite 82/123; axiom audit exact; audit at 4.
