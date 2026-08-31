# ref regime B-proj: a field reference into an unbound root

Date: 2026-08-31
Tags: obseq3, ref, regime-B, unbound-root, projection

## [FACT] the offset rule composes with regime B unchanged

`ref_fresh_projsrc_simulation` proves `dst := &kind s.f` when `dst`'s
root is UNBOUND. It is `ref_fresh_dst_simulation` under exactly the
substitutions recorded in 2026-08-31-ref-derefdst-projsrc.md — the
projection costs only the `Borrow`'s offset operand, and the
allocation half is untouched. Fragment is still three instructions:
`Alloc; Borrow; RStore`.

Both compiled fragments (`compileStmt_ref_fresh_projsrc_run/_value`)
went through first try, as did every substitution in the leaf except
two mechanical ones (below). This is now two data points that ref's
proj-source rule transfers across regimes for free; the [HYP] that a
`BorrowSim` package would pay for itself is looking weaker, since the
substitution is cheap enough that packaging may not beat copying.

## [OBS] index-disjointness needs a different argument for proj sources

`ref_dst_src_idx_ne` proves `srcLoc.idx ≠ dstLoc.idx` from TYPES:
`dstLoc : Local Γ (PtrL τ)` and `srcLoc : Local Γ τ` cannot share an
index because `τ ≠ PtrL τ`. With a projected source the types are
`PtrL τ` and `σb`, which CAN coincide as far as the binders say.

Two replacements, and both are needed — they are used in different
branches:

1. Inside the leaf, where `h_envD : lookup = none` and
   `h_envS : lookup = some bS`: `Env.lookup env loc` is literally
   `env loc.idx`, so equal indices give `none = some bS`. Type-free,
   three lines.
2. In the dispatcher's none/none branch, where BOTH lookups are `none`
   and no semantic contradiction exists: back to types.
   `ref_proj_dst_src_idx_ne` assumes the indices agree, gets
   `σb = PtrL τ`, substitutes, and does `cases f`. Both `PathTo`
   constructors fail to unify — `.nil` would need `τ = PtrL τ` and
   `.field` needs a `TupL` — so `cases f` closes the goal with zero
   remaining cases and no lemma about layouts at all.

That second one is worth remembering as a technique: an impossible
INDEXED family is often refuted by `cases` alone, because the
constructor indices do the work that an explicit disequality lemma
would otherwise have to.

## [OBS] a Lean packaging trap

Inserting the new theorem directly above `ref_place_residual` put it
between the residual's docstring and its `theorem` line — two
consecutive docstrings, which is a parse error at the SECOND one
("unexpected token '/--'"). Insert above the docstring, not above the
`theorem` keyword. Anchoring on `theorem <name>` is the natural thing
to script and it is wrong whenever the target is documented.

Also: `Option.noConfusion h` on `h : none = some x` does not elaborate
without a motive here; `simp at h` closes it.

## [FACT] d76's teeth

Same construction as d75: `r := &mut s.0` held live across
`t := &mut s.1`, then `*r := 9`. Disjoint field ranges mean a correct
borrow leaves `r` alone. Control run with the source retargeted to
`s.0` reports `ub` at statement 4.

## state

Build green; 17/17 + 89/89; audit exact at ONE sorry. Residual call
sites 12 -> 11. Three unbound-root sites left: a deref source under a
fresh destination, and projected destinations over an unbound root at
zero and at nonzero offset (the latter two are regime B-proj for the
DESTINATION, the analogue of `const_write_proj_fresh_simulation`).
