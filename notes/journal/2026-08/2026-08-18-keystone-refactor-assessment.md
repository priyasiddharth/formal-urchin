# Keystone proof refactor: what's reusable, when to extract

[OBS 2026-08-18] Assessment (user asked; not yet acted on) of whether
`sb_ref_use_die_cancels`'s proof (proof/keystone.lean) should be split
into smaller lemmas, and which parts the remaining 7 audited sorries
can reuse.

**Already generic as-is** (bottom ~60% of the file): the `SB` assoc-list
lemmas (`find?_set_self/_ne`, `set_set`, filter idempotence), the whole
`setChain`/`chain` theory (normal form, override/collapse, `find?`,
nodup keys), and the two fold characterizations `foldCellsIdx_ok_inv` /
`foldCells_ok_of_cells`. Every range-based SB op (read, write, die,
dealloc, own, ref) is a fold of a content-driven cell rewrite, so any
future lemma about any of them wants those two.

**Worth extracting from the ~250-line monolith**, by payoff:
1. Per-op characterization wrappers — `sb_write_ok_inv` /
   `sb_write_of_cells`, `sb_die_of_cells`, and `sb_ref_mut_inv` (the
   monolith's whole first half: mint + fold inversion + per-cell choose
   extraction + field equalities). Each use currently re-fights the
   `h_op` discharge and the `{s with NextTag+1}.StackMap` projection
   normalization inline; wrappers fight both once. Consumers: BRIDGE 3
   (write characterization on both machines), leaf 3 (`ref` — needs the
   inversion again plus per-kind siblings), leaf 2 (`copy` — needs a
   not-yet-written `sb_read` analog whose pattern these set).
2. [HYP] A new generic `foldCells_respects` — two folds over
   ListRel-related stack maps with pointwise-related contents produce
   related setChains. This plus one content-transport fact per op
   (`writeCellContent` respects `StackSim` under a renamed tag) is
   essentially all of BRIDGE 3, turning "half-day per op" into "one
   content lemma per op + instantiation". Largest single payoff.
3. Keep in place: the three-phase collapse and the top-of-stack content
   facts — specific to the compiler's Borrow/use/Die pattern, no other
   consumer, and it is the keystone's readable core.

**Cost/risk:** low; the development-time fragilities (elaboration-order
`op :=` forcing, matcher mismatches) get MORE robust once the op is
fixed in a lemma statement instead of inferred at a use site.

**Recommendation:** extract on demand, not as a standalone pass — do
the `sb_write` wrappers + `foldCells_respects` as the first step of
closing BRIDGE 3, and pull `sb_ref_mut_inv` out when leaf 3 starts, so
every extracted lemma has a consumer (matches the repo's increment
style). Extra reason to name `sb_ref_mut_inv` early: the keystone's two
side conditions (fresh tag ≠ wildcard, not protected) will be
discharged from the planned WF invariant, and a named inversion is the
natural seam to thread it through.

**References:** 2026-08-15-keystone-closed.md, proof/compiler.lean
(audit, closing order 4→5→7→1→2→6→3), loose-ends/parked.md
("obseq3 proof closure").
