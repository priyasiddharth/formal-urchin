# formal-urchin2

Lean 4 formalization: obseq2 compiler-correctness proofs
(mirlite → oseair). v2 lives in `src/obseq2/`; `src/obseq/` is the v1
reference implementation.

notes at: notes/

- Axiom/sorry audit: `scripts/audit_axioms.sh` machine-checks that the
  main theorem (`obseq3.proof.compile_correct`) rests only on the
  whitelisted axioms and EXACTLY the audited sorries (pinned in
  `scripts/axiom_audit.lean`). Run it as part of validation before every
  commit that touches proofs; update the pin in the same commit that
  closes or adds a residual.
- `notes/` is the agent-maintained research notebook (better-than-fish
  conventions — see notes/CLAUDE.md). Start sessions by reading the
  latest entry in notes/sessions.md.
- The human-facing dev log is `obseq2-comparison.md` (newest-first
  dated entries).
