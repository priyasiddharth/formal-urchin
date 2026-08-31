# what `compile_correct` actually says (and does not)

Written 2026-08-31, after the last sorry closed. The point of this file
is to keep "obseq3 is proven" from being read wider than it is.

## [FACT] the theorem, unconditional form

`obseq3.proof.compile_correct_from_initial` (proof/compiler.lean §Z):

    CoreProg prog →
    compileProg prog = ok compProg →
    mirlite.runN MSB n (mirlite.State.initial MSB Γ) prog = ok s_mir' →
    ∃ ρa' ρt' s_osea' m,
      oseair.runN MSB m (oseair.State.initial MSB) compProg = Ok s_osea' ∧
      CompilerInv (initialState Γ) prog ρa' ρt' s_mir' s_osea'

No invariant hypothesis: `CompilerInv_initial` discharges the base case
at the real entry states. Both this and `compile_correct` are audited
roots of `scripts/audit_axioms.sh`. Axioms: `propext`,
`Classical.choice`, `Quot.sound`. No `sorryAx`.

The observable content is inside `CompilerInv`: `SourceMemSim` at
ρa-renamed addresses and `PermSim` at ρt-renamed tags, plus the
label/binding/allocator agreements that make the induction go.

## [FACT] the initial rename maps are NOT both empty

ρa is empty — nothing is allocated at entry. ρt is NOT: `TagRenameWF`
demands `ρt wildcardTag = some wildcardTag` of every rename map,
because int-to-ptr pointers carry the wildcard on BOTH machines and
`MemValSim` needs it fixed. So the initial ρt is the singleton
`wildcardTag ↦ wildcardTag`. That also satisfies `TagRenameBounded`,
since `wildcardTag = 0` and both machines start at `NextTag = 1`.

If a future change makes the wildcard a nonzero tag, or moves either
machine's initial `NextTag`, `CompilerInv_initial`'s last bullet is
where it breaks.

## [FACT] two scope limits, neither of them a hole in the proof

**1. The `CoreProg` gate.** `CoreStmt` admits only `halt` and
`assign dst rhs` with `CoreRhs rhs`, and `CoreRhs` admits only
`constInit`, `copy`, `ref`. Excluded: `assignIf`, `alloc`, `dealloc`,
`pushProtectors`, `popProtectors`, and the rvalues `uninit`,
`ptrCast`, `ptrOffset`, `refSlice`, `exposeAddr`, `fromExposed`. They
are implemented and exercised by the conformance corpus; the theorem
discharges them with `absurd h_stmt_core`.

Note the OTHER axis is total: within the fragment, `dst` and `src` are
ARBITRARY places — any nesting of local/proj/deref, bound or unbound
roots, any offset. That is what the four residuals were quantifying
over, and it is what closed.

**2. The direction.** This is forward simulation of SUCCESSFUL source
runs. It says nothing about what the target does when the source has
UB. Nothing in Lean rules out a compiler that turns a UB source
program into a clean target run.

That direction is covered only EMPIRICALLY, by the `expectDiff` corpus
(103 witnesses), which compares VERDICTS — ok / ub-at-statement-k /
stuck — not values. This is exactly why every witness needs TEETH: a
witness that passes for both machines without ever inducing UB tests
the forward direction twice and the backward direction not at all.

## [OBS] the honest one-line summary

"Three rvalues over every place shape, forward, from entry, sorry-free
— with UB-preservation tested rather than proven."
