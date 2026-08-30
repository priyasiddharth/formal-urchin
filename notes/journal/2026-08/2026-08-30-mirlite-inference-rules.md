# MIRLite inference-rule expansion

[OBS] Expanded `mirlite-oseair-correctness.typ` from four to six A4 pages.
The original overview, OSEA-IR, compiler, and compiler-correctness pages
remain intact; two pages now give a derived inference-rule presentation of
MIRLite's executable semantics.

## Rule selection

The place-resolution page introduces the access judgment and the successful
branches corresponding to `resolvePlaceAcc`:

- `ACC-LOCAL` retrieves the allocation address and tag from the environment;
- `ACC-PROJ` adds the typed path offset while preserving tag and bounds;
- `ACC-DEREF` bounds-checks and reads the pointer cell, threads the resulting
  permission state, and switches to the stored pointer's provenance.

It separately describes pure `resolvePlace?`, which performs raw lookup
without a bounds or permission event. The evaluation page gives `E-CONST`,
`E-COPY`, `E-REF`, `WRITE`, and `S-ASSIGN`, exposing the exact order in
`doAssign`: prepare the destination root, complete RHS evaluation, resolve the
destination for access, then write.

## Presentation boundary

[FACT] These are derived rules for successful branches of the executable Lean
definitions, not a second inductive semantics. Errors correspond to failed
premises. The distinction matters especially for dereference: access
resolution performs the permission-model `read`, while pure resolution does
not. The rules retain the running nonzero-field assignment so the source's
parent-tag write can be compared directly with the compiler's
`Borrow(Mut); CStore; Die` fragment.

## Verification

[EMP] Verified against repository commit `d4bd4f2` with Typst 0.15.1.
`mirlite-oseair-correctness.typ` compiles without errors to
`mirlite-oseair-correctness.pdf`; a six-page PNG render was inspected at
110 PPI. All six A4 pages are self-contained, with no overflow or unintended
page break.

The pre-existing modification to `src/obseq3/proof/copy.lean` was not touched.
