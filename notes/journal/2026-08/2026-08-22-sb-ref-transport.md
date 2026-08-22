# The `sb_ref` transport member lands: ρt can now grow

[FACT] `sb_ref_respects_PermSim` (proof/permsim_transport.lean) is proved:
a successful source retag is matched by a target retag through the renamed
parent tag, and the results are `PermSim`-related under **ρt extended at
the fresh pair**. This completes the BRIDGE 3 transport family — the three
non-minting ops (`sb_write` 2026-08-18, `sb_read`/`sb_die` 2026-08-19) plus
the one minting op. It is the single blocker named by 3 of the audit's 5
remaining sorries (`const_write_proj_simulation`,
`const_write_deref_nonspine_simulation`, `CompilerInv_step_ref`).

[FACT] The enabling fact is `TagRenameBounded ρt nS nT` (common.lean):
every mapped pair is below both counters. This is the **tag half** of the
strengthened WF the audit has been naming since regime C (the register half
landed 2026-08-21 as `PlaceRegMapBound`). It does exactly two jobs, and
both are needed: the RANGE bound puts the target's fresh tag outside ρt's
range, which is what keeps the extension injective; the DOMAIN bound gives
`ρt srcFresh = none`, which is what makes it an extension rather than an
overwrite. `TagRenameWF.extend`/`TagRenameIncr.extend`/
`TagRenameBounded.extend` package this; each is one `grind` call once the
bound is stated. Wildcard survives for free — `wildcardTag = 0` and
`NextTag ≥ 1`, so the fresh tag is never the wildcard.

[FACT] Two behavior-preserving model factorings were needed first, both in
the `readCellContent` tradition: `insertAboveContent` out of
`insertAboveCell`, and `refCellOp` out of `sb_ref`. The second is the
interesting one — `sb_ref`'s per-cell action was an inline
`match kind with ...` producing lambdas, which cannot be reasoned about
under a `RefKind` variable without case-splitting the whole proof. Naming
it lets `refCellContent`/`refCellStep` (proof-side) collapse all five
variants to one stack-to-stack function, so the SAME `foldCellsIdx`
inversion/construction pair the other members use applies here, and the
kind analysis is confined to two small lemmas
(`refCellOp_content_form`, `refCellContent_transport`).

[FACT] `foldCellsIdx_ok_of_cells` (keystone.lean) is the construction
counterpart of `foldCellsIdx_ok_inv`, which existed alone since the
keystone. The index-carrying fold now has both directions, as the
index-free one already did.

[OPEN] `CompilerInv` does not yet carry `TagRenameBounded`. Until it does,
the member cannot be applied at a leaf: every consumer needs the bound as a
hypothesis. Next increment: add it as an eighth conjunct and re-establish
it at each construction site — trivial for the closed regimes (`sb_write`/
`sb_read` do not move `NextTag`, so the bound is literally unchanged) and
supplied at minting sites by the member's own conclusion. See
loose-ends/parked.md → "obseq3 proof closure".

[EMP] (Lean 4.28) three potholes, all about matcher identity and where
terms are reachable:
- Two textually identical `match`es at different sites are NOT defeq
  (the 2026-08-19 note again), so `sb_ref_unfold` as a hand-written match
  equal to `sb_ref`'s `do`-block could not be closed by `rfl` even after
  `simp only` made both sides display identically. Factoring the model
  (above) dissolved the lemma entirely — the right fix for this pothole is
  usually to stop restating the term.
- `cases h : SB.find? ...` does NOT substitute into a subterm that sits
  under a matcher's minor premise, because there the occurrence is a
  BOUND variable, not the term. Resolve the cell FIRST and carry `h_find`
  in every rewrite set; then the inner content result is a genuine
  subterm and can be case-split.
- `rw` on `tgt.protFrames` fails ("motive is not type correct") when the
  goal also mentions a `choose` term whose type depends on it. Generalize
  the per-cell results to an opaque `W'` via `obtain` before the rewrite.
- `reduceIte` does not fire on `if false = true then _ else _` arising
  from a `Bool.not_eq_true` rewrite; `if_pos`/`if_neg` applied to the
  `by_cases` hypothesis do, and `split <;> rfl` handles the cases where
  both branches agree.

Validation: units 15/15 + 38/38, suite pass 77 | fail 0 (117),
differential matched 77 | mismatch 0 | skipped 0, obseq2 green. Audit
stays at 5 sorries (this is machinery, not a leaf), and
`#print axioms sb_ref_respects_PermSim` shows only propext /
Classical.choice / Quot.sound.

**References:** proof/compiler.lean (audit), 2026-08-19-read-die-transports.md,
2026-08-21-regime-d3-spine.md.
