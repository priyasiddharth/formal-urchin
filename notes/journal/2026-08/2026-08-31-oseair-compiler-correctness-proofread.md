# OSEA-IR, compiler, and correctness semantic proofreading

[SUPERSEDES the OSEA-IR/compiler/correctness portions of
`2026-08-31-semantic-narrative-rewrite.md` and
`2026-08-31-oseair-compiler-rules.md`. The MIRLite proofreading entry remains
current.]

## Purpose

Reworked the remaining paper sections to the same standard as the corrected
MIRLite section: every metavariable is introduced, syntax is separated from
runtime representation, judgments state executable behavior, and the running
example determines a complete source/target/compiler/correctness derivation.
The resulting paper is exactly twenty PLDI-review-format pages.

## OSEA-IR corrections

[CORRECTION] Distinguished source `LayoutTy` from target `TyVal`. Registers
carry an erased runtime type and a value-cell list; every pointer layout erases
to `PTy`, while tuples erase recursively and sizes are preserved. The running
register for `x` is therefore typed `PTy`, not by the source pointer layout.
Target memory cells are written as `dat(n)`, pointers, or `undef` rather than
as bare source words.

[CORRECTION] Presented the actual RHS and instruction surface and the
successful branches of `evalRhsWith`/`stepWith`. Load checks both ends of its
complete runtime-type range. Borrow checks its upper bound and admits a
zero-length one-past borrow. Stores separately check source runtime type or
constant length before the common write-through-pointer operation. `die`
does not perform the allocation-range check previously claimed; it delegates
admissibility to the permission model.

Added the remaining allocation, provenance, pointer-offset, slice-retag,
copy, deallocation, conditional, and protector behavior, plus an error
classification that records when permission events have already occurred.
The target example now fixes three permission premises and derives exact
states `T0 → T1 → T2 → T3`, including PC, register, memory, and permission
changes.

## Compiler corrections

[CORRECTION] Replaced the fictitious “returned instruction list” judgment with
a state-delta presentation. Compiler state is `(nextReg, nextLabel, code,
localMap)`; the emitted interval is read from the final code map between the
old and new label counters. Monotone state growth preserves old labels and
local-map entries.

The section now distinguishes root establishment, ordinary place lowering,
and escaping-borrow lowering. It explains offset-zero reuse, final-width
projection borrows, pointer loads for dereference, LIFO cleanup, and why a
loaded source pointer must not be died. The supplied `projInto`/
`flattenPlace` code is typed and tied to path composition; flattening stops at
dereference and prevents the erroneous two-cell intermediate borrow in
`x.1.0`.

RHS lowering is presented as pre-destination work plus a deferred store. The
core constant/copy/reference cases and all executable non-core cases now give
concrete OSEA sequences. Statement lowering records the distinct ordering for
ordinary assignment, allocation, deallocation, conditionals, and protector
frames. Program-prefix compilation defines target label alignment. The
running derivation starts with an explicit compiler state and derives fresh
register/label counters and the exact three emitted instructions.

## Correctness corrections

[CORRECTION] The simulation no longer suggests that compiler state changes
during target execution. Both local and whole-program statements keep the
original compiler state and source program fixed; only the partial address and
tag relations extend. Address renaming is identity on its domain because the
bump allocators are synchronized. Tag renaming is genuinely injective rather
than identity because internal target borrows advance the target tag counter.

The statement-boundary invariant now lists all ten mechanized conjuncts:
prefix/PC alignment, bound-local simulation, forward memory simulation,
permission simulation, address identity, tag-map shape, tag bounds, allocator
lockstep, unbound-local agreement, and local-register freshness. Permission
simulation is explained at item, stack, address-map, protector-frame, exposed
list, and counter levels. The paper also constructs the canonical empty
initial relation and states the observable word, pointer, local, permission,
and control consequences of a final invariant.

The step theorem covers successful core constants, copies, and references for
all defined borrow kinds and arbitrary protector/mask parameters. The
whole-program theorem is explicitly forward simulation only. A table records
the semantic obligations still needed to extend the theorem to each
executable non-core form.

## Verification

[EMP] Built `mirlite-oseair-correctness.typ` with Typst 0.15.1 and
`faithful-acmart` 0.1.0 into an exactly twenty-page PLDI review PDF. All pages
were rasterized and visually checked through the rewrite; rule boxes and
tables fit, the widened expression table no longer crosses a column boundary,
and the final page contains an end-to-end synthesis rather than an orphaned
status fragment.

`scripts/audit_axioms.sh` passes its whitelist at repository commit
`ddc35d1`. Rooting the audit at the whole-program correctness result reports
one admitted root, the residual reference-assignment case. The paper states
that limitation precisely. Concurrent changes to `CLAUDE.md` and the proof
development were not modified.
