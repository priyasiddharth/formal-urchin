# ref_place_residual — RETIRED 2026-08-31

The residual is CLOSED and the theorem DELETED. obseq3 has no sorries:
`obseq3.proof.compile_correct` rests on `propext`, `Classical.choice`
and `Quot.sound` alone, and `scripts/axiom_whitelist.txt` no longer
lists `sorryAx`. Its reappearance is a REGRESSION, not a drift.

This file is kept as the record of how the site map shrank, because the
counting discipline it enforced is reusable.

## [FACT] sites are not the metric; classes are

The count went 12 -> 11 -> 10 -> 9 -> 8 -> 6 -> **8** -> 6 -> 5 -> 4 ->
2 -> 1 -> 0. It rose once, when one coarse residual arm split into
three narrow ones — coverage grew while the number went up. Track the
CLASS TABLE (which statement shapes are open), not the call-site count.

## [FACT] the closing order, and what each step actually cost

| shape | closed by | note |
|---|---|---|
| unbound destination roots (4 sites) | `ref_fresh_*`, `ref_proj{zero,offset}_fresh_*` | regime B-proj; `extendBlock`, not a single cell |
| nested projection sources | the four flattening recursions | the compiler already reassociates; the transfer is a congruence, not a new leaf |
| `t.g := &kind (*p).f` | four quadrants + `ref_proj_src_projdst_simulation` | a projected destination over a LOCAL base has NO spine, so one mother suffices |
| `t.g := &kind *p` | the nil-projection eta | pure spelling: `flattenPlace` never makes an empty projection |
| `*chain := &kind (*p).f` | `ref_derefdst_derefprojsrc_simulation` | TWO mothers; 453 lines, first try |
| `(*p).g := &kind _` | `ref_proj{zero,offset}_derefdst_chainsrc_simulation` | two mothers AND BRIDGE 1 |

## [FACT] the two structural facts that made the endgame cheap

1. **Empty cleanups collapse the bookkeeping.** When both lowerings
   return `cleanup = []`, no `Die` is emitted (no BRIDGE 1) AND the
   statement's whole emitted shape is known before either mother runs,
   so each code-inclusion obligation is ONE `StateIncr` step off
   `h_stmtRun`. copy's two-mother leaves, whose source lowering leaves
   a cleanup, need fifty-line `StateIncr` towers instead.
2. **A leaf rarely needs a place's constructor.** It needs the
   definitional unfolding. Take that as a hypothesis
   (`placeToBorrowRegChecked_proj_root_eq`, side condition
   `PtrChain.not_proj`) and the leaf becomes generic in the source,
   halving the leaf count. `ptrChain_lowering_sim` already covers a
   LOCAL place at zero execution steps, so "local vs chain" is not a
   real axis either.

## [OBS] the destination-side package does NOT collapse the quadrants

Considered and rejected 2026-08-31. `LoweringSim` — the named
conclusion of `ptrChain_lowering_sim` — demands
`placeOut.result.cleanup = []`, and `placeToRegChecked`'s projection arm
at NONZERO offset returns `baseRes.cleanup ++ [(tmpReg, blockSize τ)]`.
So the package covers exactly the ZERO-offset cases, which were already
cheap. Check the `cleanup = []` conjunct before proposing a package for
any lowering that mints a temporary.

## [FACT] `.proj (.deref p) g` is not a `PtrChain`

`derefProj` is `.deref (.proj b f)`, not `.proj (.deref b) f`, and
`PtrChain.not_proj` forbids a top-level projection. A projected
destination over a deref base therefore needs its BASE lowered by the
mother and its offset handled by the leaf. See
journal/2026-08-31-ref-last-site.md.
