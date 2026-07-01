# Where design knowledge lives — document map

Load this when looking for prior reasoning before re-deriving a design
question. Grep these files before answering "why is X this way".

[FACT] `obseq2-comparison.md` (repo root, committed) is the dev log,
newest-first. Entry index:
- 2026-06-17 — const_write plan: reconstruct-not-port, identity-on-domain
  conjunct, regime A/B split, conditional `runN_cleanupInstrs`
- 2026-04-30 — CompCert `Block × Z` memory model evaluated and REJECTED
- 2026-04-30 — labels vs runtime PCs (`FragmentInstalledAtLabel` /
  `FragInstalled` split, `s.pc = baseLabel` bridge)
- 2026-04-30 — `StateIncr`/`CompilerM` monad (kills `*_state_incr` lemmas)
- 2026-04-28 — code map `Prog = Nat → Option Instr` (kills list-slice
  placement; chosen over an 8th "slice" conjunct)
- 2026-04-25 — bounds semantics, two target-semantics bugs fixed, WF-layer
  plan (never built — see the 2026-06-17 session correction), SB ≠ bounds
- 2026-04-22 — initial v2 design: intrinsic typing, `Ctx`/`Place`/`PathTo`,
  `MemValue.placeTag` trade-offs, what's standard vs novel

[FACT] `paper.md` (repo root, committed d3fa01e) is a draft paper about
**v1** (obseq): the four-stage template (compiled_eq → mirlite_step_inv →
osea_run_ok → StateSim reconstruction), RefOp/DrefOp case studies, and a
comparison table vs CompCert/Velus/Vellvm/CertiCoq/RustBelt/SB. Its §7
mechanization-status claims describe v1 debt — see
v1-obseq-is-axiom-backed-check-before-citing.md.

[FACT] `src/obseq/obseq2.md` is the original v2 plan (typed MIR AST,
bundled FrameInv/footprint non-interference, permission model as a
module, phased delivery, "no new axioms without review", explicit
preference of CompCert-style footprints over Iris).

[FACT] `references/related_work.md` annotates 17 PDFs in
`references/papers/` (CompCert, Velus line, Vellvm, CertiCoq line,
Compositional CompCert, RustBelt, Stacked Borrows), each with a
why-relevant line. Still missing: Paraskevopoulou & Grover,
"Compiling with Continuations, Correctly" (OOPSLA 2021).

[FACT] `ARISTOTLE_SUMMARY.md` + `README.md`: the repo was edited by
Aristotle (Harmonic). Convention: credit Aristotle-authored work in
commits with `Co-authored-by: Aristotle (Harmonic)
<aristotle-harmonic@harmonic.fun>`.

[HYP] `plans/state_helpers_refactor.md` (v1 `state_sim_alloc` helper
extraction) is likely obsolete: v1 is frozen as reference-only, and
Aristotle's simplification run already did overlapping cleanup.
`plans/osea_symbolic_exec.md` is v1-era but its idea is alive — see
loose-ends/parked.md "OSEA symbolic-execution tactic".
