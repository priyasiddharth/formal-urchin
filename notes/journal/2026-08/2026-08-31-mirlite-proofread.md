# MIRLite semantic proofreading

[CORRECTION] Reworked the MIRLite section after identifying two fundamental
notation errors: `τ` was used without being introduced, and retag kind `k` was
incorrectly restricted to shared and mutable references.

## Typed syntax

The paper now explicitly declares `σ` and `τ` as layout metavariables and
defines the layout grammar and cell-size function. It explains that pointers
occupy one cell while retaining a statically significant pointee layout. A
context is an ordered list of layouts, and locals, projections, dereferences,
expressions, and assignments are presented through typed judgments rather than
an untyped grammar.

The retag-kind grammar now contains shared, mutable, raw-const, raw-mut, and
two-phase kinds. Reference formation is written neutrally as
`ref(k,c,m,p)`, since ampersand notation is misleading for raw pointers. The
protector flag `c` and interior-mutability mask `m` appear in the expression
syntax and in both source and target permission transitions. Internal compiler
borrows are shown with their actual unprotected, empty-mask parameters.

## Operational semantics

The source state description now distinguishes the partial local environment,
cell map, bump-allocation metadata, allocation ranges, and abstract permission
state. The text states that displayed judgments are successful branches and
enumerates their principal error cases. Assignment preparation now describes
the existing-root, fresh-local, and illegal-dereference-root cases.

An explicit constant transition and program-level halt/fixed-point behavior
were added. Assignment is decomposed through a `write` relation so the final
state retains allocator/environment changes from preparation and all effects
of RHS evaluation, instead of reconstructing a state from unexplained primed
components.

## Running derivation

The example now fixes the context, typed local, address-indexed memory cells,
and owning-tag assumption. It defines paths `q₁` and `q₀`, gives their source
and destination layouts and offsets, distinguishes nested projection from
appended-path syntax, and derives each resolution step:

```text
x          ↦ res(100, tx, 100, 3)
x.q1       ↦ res(101, tx, 100, 3)
(x.q1).q0  ↦ res(101, tx, 100, 3)
```

The final assignment transition updates address 101 in the actual memory map
and leaves sibling address 102 untouched.

## Verification

[EMP] Verified against repository commit `4913cf6` with Typst 0.15.1. The
paper compiles without warnings to ten PLDI-format pages. All pages were
rendered at 110 PPI and visually checked; corrected longer notation does not
overlap, and tables remain with their headers. The axiom audit passes with the
same single admitted reference-assignment root. Concurrent proof edits were
not modified.
