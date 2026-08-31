# ref_place_residual: the inventory, and why copy's shortcut does not transfer

[OBS 2026-08-31] With copy closed, `ref_place_residual` is the only
sorry. It has ELEVEN call sites, and they group into three families.
Read off `src/obseq3/proof/ref.lean` directly, not off the docstring,
which lags.

**(A) Unbound destination roots — 4 sites.** A projected dst over an
unbound local base at zero offset and at nonzero offset (inside
`ref_proj_dst_simulation`); a local dst unbound with a proj source; a
local dst unbound with a deref source.

**(B) Non-local SOURCES — 6 sites.** Under a projected dst over a local
base: proj src, deref src. Under a local dst: proj-of-proj src,
proj-over-deref src. Under a deref dst: proj src, deref src.

**(C) Projected destination over a DEREF base — 1 site**, any source.

The closed set is the complement: LOCAL sources under every
destination, and non-local sources only under a LOCAL destination.

## Why copy's package trick does not transfer for free

[FACT] For copy, `LoweringSim` was cheap because
`ptrChain_lowering_sim` ALREADY existed as a standalone source lemma —
naming its conclusion was the whole move. ref has no such lemma: every
leaf inlines its own source phase, so factoring one out means
EXTRACTING ~150-300 lines from three different leaves and proving the
package for each source shape.

[FACT] The payoff would be larger, though, and the shape is favourable.
`placeToBorrowRegChecked` (compile.lean:449) ends the SAME way in all
three arms — a `Borrow` into a fresh register with cleanup
`[(tmpReg, blockSize τ)]` — differing only in what precedes it and in
the borrow's offset. So a `BorrowSim`-style package with a ONE-ENTRY
cleanup is uniform across local, proj and deref sources, and would
unlock all six family-(B) sites at once. Note the contrast with copy,
where the package's promise was `cleanup = []` and the nonzero-offset
projection broke it; here a non-empty cleanup is the norm, so the
package should be stated with the cleanup rather than against it.

**Recommendation:** do family (B) via the package once two or three
concrete leaves exist to extract from, not before — the extraction is
easier when there is more than one instance to generalize over.

## This increment

The compiled side of the first concrete leaf:
`compileStmt_ref_derefdst_projsrc_run/_value`, for
`*P := &kind s.f` over a bound local `s`. The proj arm of
`placeToBorrowRegChecked` differs from its local arm ONLY in the
borrow's offset, so both fragments are the deref-dst pair with
`pathOffset f` in place of `0`; both compiled first try.

**Validation:** build green; 17/17 + 87/87; audit exact at ONE sorry.
