# OSEA-IR and compiler rule expansion

[SUPERSEDED → `2026-08-31-semantic-narrative-rewrite.md`] The paper was
subsequently rewritten around language syntax, operational/translation
semantics, and a single end-to-end example. This entry records the earlier
rule-catalog presentation.

[OBS] Expanded `mirlite-oseair-correctness.typ` from seven to eleven PLDI-format
pages. The new material gives derived rules for the successful branches of the
OSEA-IR executable semantics and compiler, then relates the compiler's local
projection reassociation to the proof layer's total `flattenPlace` normalizer.

## OSEA-IR rules

The right-hand-side judgment now includes `T-LOAD`, `T-BORROW`, and `T-ALLOC`.
They expose full-range bounds checks, permission events, memory reads, fresh-tag
creation, retained pointer base/extent, and allocation ownership. The target
small-step judgment includes `I-ASSGN`, the common `T-WRITE` subrule,
`I-RSTORE`, `I-CSTORE`, and `I-DIE`. The accompanying text records the distinct
type/length checks for the two stores and the fixed-point behavior of halt and
missing-code states under `runNWith`.

[FACT] These are a paper presentation of the successful branches of
`evalRhsWith`, `writeThroughPtr`, `stepWith`, and `runNWith`; they are not a
second inductive semantics. Failed premises correspond to the executable
functions returning an error.

## Compiler rules and flattening

The place-lowering judgment adds `C-LOCAL`, `C-PROJ-ASSOC`, `C-PROJ-0`,
`C-PROJ-OFF`, and `C-DEREF`. It makes three implementation details explicit:
zero-offset projections reuse the base register; nonzero projections emit one
final-width internal borrow plus a cleanup obligation; and dereference loads a
stored pointer after retiring temporaries used to reach its pointer cell.
Cleanup is LIFO because `cleanupInstrs` reverses its list before mapping `Die`.

The paper includes the Lean-shaped `projInto` and `flattenPlace` definitions
from `src/obseq3/proof/spine.lean`. Direct compiler recursion reassociates one
nested projection at a time; the proof layer packages the same behavior as a
total normalization. Fusion is semantic rather than cosmetic: compiling
`s.1.0` through a borrow of the whole intermediate `s.1` may invalidate a
sibling borrow such as `s.1.1`, whereas the fused path emits one borrow at the
composed offset and final field width. The cited development proves access
resolution, assignment preparation, and checked lowering agree before and
after flattening.

The RHS/compiler judgment adds `C-CONST`, `C-COPY`, `C-REF`, and `C-ASSIGN`.
In particular, `C-COPY` materializes the entire source before destination
lowering, and `C-ASSIGN` displays the full order: prepare root, emit the RHS
pre-phase, lower destination, store, retire RHS temporaries, then retire
destination temporaries.

## Verification

[EMP] Verified against repository commit `0c4c89d` with Typst 0.15.1 and
`faithful-acmart` 0.1.0. The PDF compiles without warnings and contains eleven
single-column pages, below PLDI 2026's twenty-page main-text limit. All eleven
pages were rendered at 110 PPI and visually inspected; rule boxes stay intact,
equations remain within the text block, and no heading is stranded.

`scripts/audit_axioms.sh` also passes. The audit rooted at
`obseq3.proof.compile_correct` reports exactly one sorry root,
`obseq3.proof.ref_place_residual`, matching the paper's mechanization-status
paragraph. Concurrent proof edits were not modified.
