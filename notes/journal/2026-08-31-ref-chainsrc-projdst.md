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

## progress on the four quadrants (later the same day)

| quadrant | state |
|---|---|
| dst offset 0, root BOUND | `ref_projzero_derefsrc_simulation` |
| dst offset 0, root FRESH | `ref_projzero_fresh_derefsrc_simulation` |
| dst offset ≠ 0, root BOUND | fragment only |
| dst offset ≠ 0, root FRESH | not started |

All THREE compiled fragments went through first try
(`compileStmt_ref_projzero_derefsrc_*`,
`compileStmt_ref_projzero_fresh_derefsrc_*`,
`compileStmt_ref_projoffset_derefsrc_*`). Both zero-offset LEAVES also
landed, the fresh one needing three corrections beyond the substitution,
all from the destination resolving at `addrStart + pathOffset g` rather
than `addrStart`: the `writeThroughPtr_sim` resolved record, its
`allocBase ≤ addr` argument (`Nat.le_add_right`, not `Nat.le_refl`), and
the destination register entry's offset.

## [FACT] why the nonzero leaves are not a substitution

The zero-offset leaf's destination phase is one `RStore` through the
root register. The nonzero one is FOUR steps — interior `Borrow(Mut)`,
`RStore`, `Die`, and BRIDGE 1 collapsing the triple — and the mirlite
write inversion has to move BEFORE the execution steps to supply
`q1`/`q2`/`q3`. That is the same assembly as
`ref_projoffset_fresh_simulation`: splice
`ref_projzero_derefsrc_simulation`'s §1-§5 with
`ref_projoffset_projsrc_simulation`'s §3 and §6-§10, re-spelling
`s_osea` → `s_mid`, `csPrefix.nextReg` → the post-spine
`(run (placeToRegChecked kind (Place.deref P)) csPrefix).nextReg`, and
the source pointer `Val.Ptr bS.addr (pathOffset f) (blockSize σb)` →
`Val.Ptr resolved.allocBase (resolved.addr - resolved.allocBase + pathOffset f) resolved.allocSize`.
Code-fact peels go 3/2/1/0 for the four instructions after the spine.

## [HYP] a DESTINATION-side package would collapse all four quadrants

The four quadrants differ only in how the destination place lowers —
root register, root register plus an interior borrow, and whether the
root was allocated first. Everything downstream (the store, BRIDGE 2,
the invariant rebuild) is uniform. That is exactly the shape
`LoweringSim` captured for SOURCES in copy: name the destination
lowering's conclusion and take it as a hypothesis, and one leaf covers
every destination shape that can produce one.

It was not built because the source-side package was judged not to pay
(2026-08-31, journal ...-lowering-sim-package.md) — but that judgement
was about SOURCES, where each shape needed its own extraction. For
destinations the four shapes already exist as four proved leaves, so
the package could be READ OFF them rather than invented. Worth doing
before the two-mother sites, which will otherwise need the same four
quadrants again.
