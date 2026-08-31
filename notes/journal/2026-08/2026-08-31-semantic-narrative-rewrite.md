# Syntax–semantics–example paper rewrite

[DECISION] Replaced the rule-catalog presentation of
`mirlite-oseair-correctness.typ` with a semantic narrative. Every major part
now introduces the notation it consumes, states an operational or translation
relation, and instantiates that relation on the same running program. Lean
theorem and helper names were removed from the exposition; file paths remain
only as mechanization pointers.

## Running example

The shared example is `x.1.0 := 42` for
`x : (Nat, (Nat, Nat))`, initially stored as `[5, 7, 9]` at base address 100.
The composed projection has offset one and final width one. MIRLite therefore
resolves address 101, uses the source owning tag directly, and produces
`[5, 42, 9]` in one source step.

The compiler flattens `(x.1).0` to one projection with the appended path and
emits:

```text
r_f := borrow_mut r_x offset 1 length 1
store_nat 42 through r_f
die r_f length 1
```

OSEA-IR execution is presented as a concrete three-state trace: `ref` creates
a fresh field tag, `useMut` writes through it, and `die` retires it. The
correctness section then relates the source and target entry/final states via
address and tag renamings. It explicitly identifies the permission
cancellation argument and explains why a width-two intermediate borrow would
incorrectly touch sibling field `x.1.1`.

## Structural changes

- MIRLite now has a grammar for layouts, places, expressions, and statements;
  an access-resolution judgment; expression and assignment transitions; and
  the complete source execution of the example.
- OSEA-IR now has a value/RHS/instruction grammar, target state and small-step
  judgments, the range and permission behavior of its memory operations, and
  the exact target trace.
- The compiler now has explicit place, expression, and statement translation
  judgments. Projection flattening is tied to path offset composition and the
  running derivation rather than to proof-library names.
- Correctness now defines the address/tag maps and each component of the state
  relation before stating local and whole-run simulation. The running example
  demonstrates how memory and permission components are re-established.
- A final case table covers copy through dereference, an escaping reference,
  and allocation of an unbound destination using the same vocabulary.

## Verification

[EMP] Verified against repository commit `c195aa0` with Typst 0.15.1 and
`faithful-acmart` 0.1.0. The document compiles without warnings to nine
single-column PLDI-format pages. All nine pages were rendered at 110 PPI and
visually inspected after correcting grammar separators and a wrapped
projection side condition. No rule, equation, table, or code fragment crosses
the text boundary.

`scripts/audit_axioms.sh` passes and reports exactly one admitted root in a
reference-assignment case, matching the prose without exposing its internal
declaration name. Concurrent proof edits were not modified.
