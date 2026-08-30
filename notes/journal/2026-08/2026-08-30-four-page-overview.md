# Four-page MIRLite → OSEA-IR overview

[OBS] Drafted `mirlite-oseair-correctness.typ`, a four-page artifact overview
organized as one page each for MIRLite semantics, OSEA-IR semantics, the
compiler, and the compiler-correctness proof.

## Narrative decision

The same closed proof-core case runs through all four pages:
`tuple.field := 42` at a nonzero field offset. MIRLite performs a direct
field write through the parent tag; the compiler emits
`Borrow(Mut); CStore; Die`; the correctness page closes the semantic gap with
`sb_ref_use_die_cancels`. This keeps the overview focused on the artifact's
distinctive issue—target-only permission events—rather than becoming four
independent definition summaries.

## Scope discipline

- The document describes live `obseq3`; `paper.md` supplied only the older
  four-stage proof-exposition pattern.
- The executable compiler's full syntax is distinguished from the theorem's
  `CoreProg` scope.
- `compile_correct` is described as successful-run forward simulation, not
  backward simulation or error preservation.
- The status box names the exact audited residuals in
  `scripts/axiom_whitelist.txt`: `copy_place_residual` and
  `ref_place_residual`. The document does not claim an axiom-free proof.

## Verification

[EMP] Verified against repository commit `614daff` using a temporary Typst
0.15.1 binary. `mirlite-oseair-correctness.typ` compiled without errors to
`mirlite-oseair-correctness.pdf`; a PNG render and visual inspection confirmed
exactly four A4 pages, one topic per page, with no overflow.

The pre-existing modification to `src/obseq3/proof/copy.lean` was not touched.
