# formal-urchin2

Lean 4 formalization: compiler correctness for mirlite → OSEA-IR on
byte-addressed memory with Stacked Borrows (`src/obseq3/`: semantics
`mirlite.lean`, target `oseair.lean`, compiler `compile.lean`, proof
`proof/`). `src/obseq2/` and `src/obseq/` are the v2 and v1 reference
implementations. The cell model was retired on 2026-10-03.

notes at: notes/

- Validation builds: bare `lake build` builds only the DEFAULT target
  (Core), which EXCLUDES the obseq3 proof lib — use
  `lake build Core Obseq3 Obseq3Proof Conformance` (or rely on
  `scripts/audit_axioms.sh`, which builds Obseq3Proof).
- Axiom/sorry audit: `scripts/audit_axioms.sh` machine-checks that the
  roots (`obseq3.proof.compile_correct_agrees`, `compile_correct_uniform`,
  `compile_correct_all`, `die_elision`, `compiled_die_elision_iff`,
  `compiled_die_elision`, `compile_correct_noDie_all`) rest only on the
  whitelisted axioms
  and EXACTLY the audited sorries (pinned in
  `scripts/axiom_whitelist.txt`; the audit fails on drift in either
  direction). Run it as part of validation before every
  commit that touches proofs; update the pin in the same commit that
  closes or adds a residual. obseq3 is currently sorry-FREE, so the
  `[sorries]` block is empty and `sorryAx` reappearing is a regression,
  not drift. `lake env lean scripts/proof_axioms.lean` checks EVERY
  declaration under `obseq3.proof` the same way.
- Test suites — there are FOUR, and `--unit` runs only the first two:

      ./.lake/build/bin/sb_conformance --unit
        # obseq3 tests           33/33   (mirlite SB semantics on bytes)
        # obseq3 compiler tests  146/146 (compiler witness corpus; the
        #   differential ones also run on OSEA-IR_B, Die elided, and
        #   pass the route-bracket check)

      ./.lake/build/bin/sb_conformance \
        --manifest conformance/manifest.json --charon-dir conformance/charon
        # ULLBC corpus, Charon artifacts vs Miri verdicts
        # 198 pass / 0 fail / 0 xfail / 17 unsupported (215 total)

      ...same, plus --osea
        # differential: compile each program and require the SAME verdict
        # from both machines, and the same OSEA-IR verdict with Die
        # elided (OSEA-IR_B), and that the compiled code passes the
        # route-bracket check (`oseair.routeOK`, the hypothesis of
        # `compiled_die_elision_iff`). 198 matched / 0 mismatch /
        # 0 skipped / 0 OSEA-IR_B mismatch / 0 route-bracket issues

      ...same, with --layouts instead
        # the loader's byte layouts have their types' shape (the proof's
        # layout hypothesis): 198 agree / 0 disagree

  The validation build above does NOT relink this binary: run
  `lake build sb_conformance` after touching a test file, or `--unit`
  silently reports the old count. Run all of them before committing, not just `--unit`. The last three need
  no Charon binary — they read the committed JSON under
  `conformance/charon/`.
- `notes/` is the agent-maintained research notebook (better-than-fish
  conventions — see notes/CLAUDE.md). Start sessions by reading the
  last entry in notes/sessions.md. That file is always chronological,
  oldest first; append new entries at the end.
- The paper is `pldi27/mirlite-oseair-correctness.typ` (Typst; build line
  in its header). Its running example is executed, not hand-computed:
  `notes/2026-09-18-paper-running-example.lean` prints every state, and
  witnesses `g14`/`d92` pin the listing. Change them together.
- The human-facing dev log is `obseq2-comparison.md` (newest-first
  dated entries).
