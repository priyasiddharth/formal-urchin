# Flatten transfers: ONE place per lemma, never both at once

[FACT, 2026-09-03] When a statement lowers TWO places (a non-local
destination with a place-valued rhs — `*Q := copy src`), write the
flatten transfer as TWO single-split lemmas that compose, never as one
lemma that flattens both places.

**Why the combined form fails.** Each half of a transfer is proved by
casing on a `placeToRegChecked … value` (4 cases: ok/ok, ok/error,
error/ok, error/error, three of which are contradictions from
`placeToRegChecked_flatten_agree`'s `Except.map (·.result)` equality).
Flattening two places means NESTING those splits. In the inner split
the two sides' compiler states have already been rewritten by the outer
one — differently on each branch — so the alignment rewrites
(`h_sagr`, `h_sres`) no longer match syntactically and every closer
reports "simp made no progress" or "did not find an occurrence".

**The decomposition that works** (copy.lean, deref-dst):

1. `compileStmt_copy_derefdst_srcflatten_run/_value` — flatten only the
   SOURCE. The destination lowering is then literally the same place at
   equal states, so the ok/ok case closes by
   `simp only [hO, hF, h_sres, h_sagr]` with nothing left to align.
2. `compileStmt_copy_derefdst_dstflatten_run/_value` — flatten only the
   DESTINATION. The source pre-phase is untouched, so its `cases` is a
   pass-through.

The dispatcher composes them with `.trans` (run) and by nesting the
existential (value). See [[flatten-transfer-explained]] for what a
transfer is; this note is about how to SHAPE one when two places are in
play.

**Companion discipline — one state spelling per proof.** Unfolding
`CompilerM.run`/`emitM` (needed to see the post-`Load` state as
`emit { … } [Load …]`) rewrites it into
`(ensurePlaceRoot _ cs).snd.val`-flavoured terms. Every later `cases`
scrutinee must be written in THAT spelling; a scrutinee in the folded
spelling does not reduce the match, and the branch closers then fail
with "no progress" rather than with an obvious type error. Decide the
spelling at the top of the proof and stay in it.

Related: [[chain-leaves-gate-on-the-whole-place]] (what the leaf gates
on), [[flatten-transfer-explained]] (what a transfer is and why the
source half is free).
