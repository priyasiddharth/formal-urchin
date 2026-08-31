# [FACT] ref_place_residual: the eight sites, and one class that never existed

Tags: obseq3, ref, residual, site-map

`obseq3.proof.ref_place_residual` is the ONLY `sorry` left in
`src/obseq3` (verified 2026-08-31 by `grep -rn sorry src/obseq3` and by
`scripts/audit_axioms.sh`). It has EIGHT call sites, in four classes.

## the map

Enumerated by walking the `cases` arms enclosing each
`exact ref_place_residual` in `src/obseq3/proof/ref.lean`.

| class | statement shape | sites |
|---|---|---|
| 1 | non-local src under a PROJECTED dst over a local base — `t.g := &s.f`, `t.g := &*p` | 2 |
| 2 | PROJECTED dst over a DEREF base — `(*p).g := &_`, any src | 1 |
| 3 | PROJ-TOPPED src whose base is not a local — `&(s.f).h`, `&(*p).f`, under a local or a deref dst | 4 |
| 4 | DEREF src under a DEREF dst — `*chain := &*chain'` | 1 |

## [FACT] "non-spine deref sources" is not a class

Earlier docstrings (and the commits of 2026-08-31 that copied them)
listed "non-spine deref srcs" among the remaining work. There is no
such thing:

```lean
theorem PtrChain_flatten_deref {Γ : Ctx} {τ : LayoutTy}
    (p : Place Γ (obseq.LayoutTy.PtrL τ)) :
    PtrChain (Place.deref (flattenPlace p))     -- spine.lean:420
```

holds for an ARBITRARY `p`. Flattening normalizes any deref place into
the `PtrChain` grammar, so every deref source is a spine and the mother
lemma always applies to it. The residual's deref-source sites (classes
1 and 4) are blocked by their DESTINATIONS, not by their sources.

Corrected in `ref_place_residual`'s docstring and in the SORRY AUDIT
block of `obseq3/proof/compiler.lean`.

## [HYP] what the classes are likely to cost

- Class 3's `(s.f).h` half looks like a src-flattening transfer away
  from the already-closed proj-over-local leaves — the ref analogue of
  `compileStmt_assign_derefdst_flatten_run`, generalized over the src
  rather than the rhs. Cheap if it goes through.
- Class 2 is the one the dst-flattening recursion structurally cannot
  reach: flattening keeps the `deref`, so `(*p).g` never becomes a
  projection over a local. It needs the spine mother lemma on the
  DESTINATION side, which no ref leaf does yet.
- Classes 1, 4 and the `(*p).f` half of 3 all pair a spine-lowered src
  with a non-local dst, i.e. two mother-lemma applications in one
  statement. `copy` already does that (its two-mother skeleton), so
  that is the donor to look at, not another ref leaf.
