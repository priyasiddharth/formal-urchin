# `csnorm`: a normal form for compiler states

[FACT, 2026-08-30] The same compiled `CompilerState` is reachable by
several definitionally-equal spellings — `emit`, `setPlaceInfo` and
`freshReg` all build record updates, so a hypothesis may hold
`(emit s l).nextReg` where the goal says `s.nextReg`. `rw` and
`simp only [h]` need a SYNTACTIC match, so the two never meet, and the
failure reads "did not find an occurrence" rather than "your spellings
differ".

`csnorm` (common.lean) is eight `rfl` projection lemmas plus a tactic
macro. It pushes counters and maps down to the underlying state, so a
state is identified by what it DOES rather than by how it was written:

    emit_nextReg / emit_nextLabel / emit_placeRegMap
    setPlaceInfo_nextReg / _nextLabel / _code
    freshReg_fst / freshReg_snd

Use it on BOTH sides of the boundary — `csnorm at h ⊢` — so hypothesis
and goal normalize together.

**Measured effect.** In `copy_projdst_zero_projsrc_offset_simulation`
the three `StateIncr` towers had needed two auxiliary hypotheses whose
statements were the destination state pasted verbatim out of a
`trace_state` dump — 3188 and 3148 characters. With `csnorm` both are
gone:

    have h_d0 := h_dval0
    csnorm at h_d0 ⊢
    simp only [h_d0]

Nine lines of pasted spelling deleted, the leaf still compiles, and the
towers no longer depend on which normal form the surrounding `simp`
happened to produce.

**Why it is NOT global `@[simp]`.** That would change the normal form
inside every existing leaf, several of which are written against the
current one. `csnorm` is opt-in and applied deliberately at boundaries.
(It is a tactic macro rather than a `register_simp_attr` set only
because that command needs `import Lean`, which this project does not
take.)

**Where it does NOT help.** It normalizes SPELLINGS, not content.
`cleanupInstrs sOut.result.cleanup` versus `[Die …]` differ by
`h_sclean`, a proof — no projection lemma can bridge that, so those
boundaries still need an explicit rewrite before `csnorm` can finish
the job. And `grind` is the wrong tool for the whole family: these are
hypotheses failing to match, not goals failing to close, and the terms
run to thousands of characters.

Related: [[transport-compiled-states-by-defeq]] — the complementary
move when only ONE hypothesis has to cross a boundary. Prefer `csnorm`
when both sides can be normalized; prefer defeq transport when the
target spelling is fixed by someone else's statement.
