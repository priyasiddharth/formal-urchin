# formal-urchin2

Lean 4 formalization: obseq2 compiler-correctness proofs
(mirlite → oseair). v2 lives in `src/obseq2/`; `src/obseq/` is the v1
reference implementation.

notes at: notes/

- Validation builds: bare `lake build` builds only the DEFAULT target
  (Core), which EXCLUDES the obseq3 proof lib — use
  `lake build Core Obseq3 Obseq3Proof Conformance` (or rely on
  `scripts/audit_axioms.sh`, which builds Obseq3Proof).
- Axiom/sorry audit: `scripts/audit_axioms.sh` machine-checks that the
  two roots (`obseq3.proof.compile_correct` and
  `compile_correct_from_initial`) rest only on the whitelisted axioms
  and EXACTLY the audited sorries (pinned in
  `scripts/axiom_whitelist.txt`; the audit fails on drift in either
  direction). Run it as part of validation before every
  commit that touches proofs; update the pin in the same commit that
  closes or adds a residual. obseq3 is currently sorry-FREE, so the
  `[sorries]` block is empty and `sorryAx` reappearing is a regression,
  not drift.
- Test suites — there are FOUR, and `--unit` runs only the first two:

      ./.lake/build/bin/sb_conformance --unit
        # obseq3 tests           17/17   (mirlite SB semantics)
        # obseq3 compiler tests  104/104 (compiler witness corpus)

      ./.lake/build/bin/sb_conformance \
        --manifest conformance/manifest.json --charon-dir conformance/charon
        # ULLBC corpus, Charon artifacts vs Miri verdicts
        # 82 pass / 0 fail / 41 unsupported (123 total)

      ...same, plus --osea
        # differential: compile each program and require the SAME verdict
        # from both machines. 82 matched / 0 mismatch / 0 skipped

  Run all four before committing, not just `--unit`. The last two need
  no Charon binary — they read the committed JSON under
  `conformance/charon/`.
- `notes/` is the agent-maintained research notebook (better-than-fish
  conventions — see notes/CLAUDE.md). Start sessions by reading the
  last entry in notes/sessions.md. That file is always chronological,
  oldest first; append new entries at the end.
- The human-facing dev log is `obseq2-comparison.md` (newest-first
  dated entries).
