# 2026-08-31 — The chain-dst leaf; D-spine and proj-top SUBSUMED

## What closed
`const_write_deref_chain_simulation`: `*P := v` for every dst that is
a `PtrChain (.deref P)` — all-deref spines, proj-topped pointer places
over chain bases (`*((*q).f) := v`, d46), interior projections at any
depth. ~200 lines. RETIRED as subsumed: const_write_deref_spine_simulation,
const_write_deref_proj_simulation, compileStmt_deref_run,
compileStmt_deref_proj_run (~750 lines net deletion). The nonspine
dispatcher collapsed to three arms (local absurd / residual /
residual); the D-dispatcher gates `PtrChain (.deref ptrPlace)`.

## The subsumption process
Documented as a durable note —
[[chain-leaves-gate-on-the-whole-place]] — in four steps: (1) the
pending-cleanup audit showed the cleanup list is ≤ 1 entry by the
lowering's own discipline; (2) the derefProj induction case FORCED
type-generalizing the mother lemma to all layouts (a proj base is a
struct-typed deref); (3) that generalization made the lemma
instantiable at the statement's WHOLE dst, whose chain-hood is
definitionally the union of the two leaf classes, with the lemma
absorbing the final Load; (4) the planned "generalize the depth-1
leaf's base" surgery dissolved — the leaf's endgame already lived in
the lemma's last induction case.

## New pieces
compileStmt_derefdst_run/_value (one CStore over the opaque
Mut-lowering run); the leaf (mother lemma at Mut on the dst →
sb_write transport → writeThroughPtr_sim → runN_CStore_step →
invariant rebuild; TagRenameBounded via mono over the weakened ≤).
Pothole notes: the h_incrS split-arm needed emit_state_incr chaining
(CheckedCompilerM.incr doesn't fit a reduced emitM chain); grind
needed Nat.add_sub_cancel' spelled out (the sub-identity gap).
A span-splice with end < start duplicated a block — caught by
count-asserts, excised; anchor-order asserts added to the recipe.

## State
All targets green; units 17/17 + 59/59 (d44 `*(*(s.f)) := v`, d45 ref
sibling, d46 `*((*q).f) := v`); corpus 82/123 (0 fail); axiom audit
exact at the same 4 residuals. const_write's deep residual is down to
proj-of-proj normalization + unbound roots.
