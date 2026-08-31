# ref: a chain source under a projected destination

Date: 2026-08-31
Tags: obseq3, ref, spine, projected-destination

## [FACT] class 1 splits by how many mother lemmas a statement needs

The residual's class 1 — a deref-rooted SOURCE under a destination that
is not a plain local — looked uniform. It is not. A PROJECTED
destination over a LOCAL base has NO SPINE: at zero offset its lowering
IS the root register, at nonzero offset it is one `Borrow` from that
register. So

  `t.g := &kind *p`   and   `t.g := &kind (*p).f`

need only ONE mother lemma, the source's. Only the two DEREF-destination
sites (`*chain := &kind *chain'`, `*chain := &kind (*p).f`) need two.

That halves the class, and the half that needs one mother lemma is the
same offset substitution used seven times now.

## [FACT] what landed

- `placeToRegChecked_deref_cleanup` — a deref lowering leaves no
  cleanup. Standalone, because the compiled fragment mentions the
  source's cleanup and so needs the fact BEFORE the mother lemma can be
  invoked. `PtrChain.placeToRegChecked_placeRegMap` already existed for
  exactly the same reason and is the model.
- `compileStmt_ref_projzero_derefsrc_run/_value` — the compiled side,
  taking `h_dclean` and `h_prm` as hypotheses so it can be applied
  before the mother lemma.
- `ref_projzero_derefsrc_simulation` — `dst.g := &kind (*p).f` with
  both roots bound and `pathOffset g = 0`.

All four compiled first try.

## [OBS] the plain deref source is the `f = .nil` instance, but not
## syntactically

`placeToBorrowRegChecked kind prot mask (.deref P)` and
`... (.proj (.deref P) .nil)` emit the SAME code — the deref arm lowers
`P` at `Shared`, `Load`s, and borrows at 0; the proj arm lowers
`.deref P` (same thing) and borrows at `pathOffset .nil = 0`. But they
are different TERMS, so one leaf cannot serve both without a
normalization step that the compiler does not itself perform.

That is why `t.g := &kind *p` (residual site in
`ref_proj_dst_simulation`) still needs its own statement even though the
code is identical.

## state

Build green; 17/17 + 99/99; audit exact at ONE sorry. Residual sites
still 5 — the leaf is landed but NOT wired, because wiring one quadrant
of a 2x2 (destination offset x root bound/fresh) would split one
residual arm into three and fragment the map for no coverage gain. The
remaining three quadrants are the next increment.

## what remains, precisely

| shape | leaves needed |
|---|---|
| `t.g := &kind (*p).f`, dst offset 0, root bound | LANDED |
| same, root fresh | σ-sized root Alloc + extendBlock, as `ref_projzero_fresh_*` |
| same, dst offset nonzero (bound and fresh) | BRIDGE 1 on the destination |
| `t.g := &kind *p` (all four) | same again with the source spelled `.deref P` |
| `*chain := &kind *chain'`, `*chain := &kind (*p).f` | TWO mother lemmas — copy's two-mother skeleton |
