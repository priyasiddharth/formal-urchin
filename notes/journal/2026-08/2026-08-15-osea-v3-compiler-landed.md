# OSEA-IR v3 + compiler + differential oracle landed

[OBS 2026-08-15] `src/obseq3/oseair.lean` (target IR) and
`src/obseq3/compile.lean` (mirlite→OSEA compiler, proof-core subset:
constInit/copy/ref/halt) landed, plus a `--osea` differential mode in the
conformance harness. First numbers, zero-iteration clean:

- unit: 13/13 mirlite + 11/11 compiler (5 golden incl. prot/mask in
  `Borrow`, 6 differential incl. 2 negatives UB-matched at the exact
  source statement);
- suite: **osea: matched 25 | mismatch 0 | skipped 51** on the 76
  passing tests; mirlite outcomes unchanged (pass 76 | fail 0).
  14 of the 25 matches are fail-tests — target UB attributed via the
  compiler's per-statement label ranges to the SAME source statement
  miri flags. Matched set includes raw-pointer tests (two_raw,
  raw_tracking, mut_raw_mut2), interior-mutability (refcell_basic,
  cell_inside_struct) and SRW-group tests (disable_mut_does_not_merge_srw,
  shared_rw_borrows_are_weak1/2).

## Design deltas vs the v2 target/compiler

[FACT] `oseair.State` is parameterized by `obseq3.PermissionModel`
(field `perms : M.State`), symmetric with mirlite v3 — a future
`CompilerInv` can state `s_osea.perms = s_mir.perms` verbatim at
`stackedBorrows`. All permission calls are range-based.

[FACT] One `Rhs.Borrow (kind) (prot) (mask) (len) (base) (offset)`
replaces v2's BorOffset/MutBorOffset/CopyOffset; `RExpr.ref`'s own
prot/mask land verbatim in the instruction (faithful by construction —
golden g2 witnesses it). Internal place-lowering borrows are only ever
Shared/Mut with `prot := false, mask := []`. `Die (reg) (len)` carries
the borrow's static length.

[FACT] **Deref lowering does NOT die the loaded pointer register**
(v2 did). The loaded tag was read from memory, not minted by the
compiler; under v3 per-cell stacks, dying it would pop the source
program's own reference out of the stacks. Golden g3 pins this.

[FACT] `ensurePlaceRoot` in `compileStmtChecked .assign`: the root
local of a projected destination is allocated before the rhs compiles,
mirroring mirlite's `preparePlaceAssign`/`allocateRoot`. Without it,
every aggregate-desugared program (`_x.0 := …` before `_x` exists)
would be rejected as `missingLocal`. Alloc order matches mirlite
(dst root before rhs), so both machines' bump allocators mint identical
addresses; tag *values* still drift (compiler mints extra borrow tags),
which only the future `CompilerInv` tag-rename ρt cares about.

[FACT] `runNWith` stops when pc doesn't advance (Halt/off-end) instead
of idling fuel away — lets the harness distinguish completion from fuel
exhaustion. The `@[simp]` runN lemmas carry the same shape.

## The GEP risk register — how it resolved

The plan named three risk spots for target-performs-more-SB-events;
none produced a mismatch in 25 compiled tests:

- (a) deref `Load` reads pointer cells the source never SB-reads: the
  read uses the pointer local's *own* tag, which only disables MutRefs
  *above* Own — invisible unless the pointer cell itself is mutably
  borrowed. No witness in the compiled set; [HYP] a `&mut &mut T`
  chain test would exercise it once nested derefs compile.
- (b) mask-less internal borrows on cell data: internal borrows are
  push-top Shared/Mut, pushed and died with no intervening foreign
  access. refcell_basic and cell_inside_struct matched.
- (c) Die × SRW-group adjacency for Raw temps: **vacuous** — compiler
  temps are never Raw (Raw borrows only arise from `RExpr.ref`, are
  RStored as values, and their cleanup entries are dropped, as v2's
  `.ref` case already did). Only Shared/Mut push-top temps die.

## Skip histogram → next instructions

31 pushProtectors (every inlined-call test) · 6 alloc · 6 uninit
(statics hoisting) · 5 exposeAddr · 2 ptrCast · 1 ptrOffset. Parked
with per-item instruction designs in loose-ends/parked.md ("OSEA-v3
remaining increments"). pushProtectors alone unlocks ~31 tests.

**References:** obseq2-comparison.md dev-log 2026-08-15,
loose-ends/parked.md, src/obseq3/{oseair,compile,compile_tests}.lean,
src/conformance/{harness,main}.lean (`--osea`).
