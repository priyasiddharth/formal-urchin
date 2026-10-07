# 2026-10-07 — `check`, then no `assignIf`/`SkipIf`

## Context
The user asked for a check statement and then the removal of `assignIf`
and `SkipIf`. Design agreed: `check p ∈ V` / `∉ V` reads `p` exactly as
`copy` does (a real SB read — the peek was removed from `assignIf` on
2026-09-17 for good reason) and continues iff membership agrees;
otherwise the run is STUCK — in the paper no rule applies (as for UB), in
Lean `.err`/`Result.Err`. Never a non-moving `Ok` (that would make `runN`
succeed and the theorems apply to a failed check).

## Stage 1: add `check`
[OBS] mirlite `Stmt.check discr vals member`; OSEA-IR `Instr.Check r vals
member` (register compare, no memory, no permissions); compiler: `guardRead`
then `Check`. Proofs: `check_simB` (proof/check.lean, ~70 lines: the read
via `readToReg_simR`, one `Check` step, `InvAtB.retarget`); `StmtB.check`,
`StmtB.all`; `step_msim`/`step_back` cases (no permission change);
`compileStmt_spec` case (route brackets). Loader: `LStmt.check`; the
certificate checks (`emitCheckEq`, `emitCheckNotIn`) and the `format!`
assumption are now single `check`s on their sentinel lines (the
`uninit`/`assignIf`/`copy` construction is gone). A corrupted variant still
gives "certificate rejected"; `--osea` matches the failure. Witnesses
d122 (passes), d123 (fails at stmt 1 on all three machines).
Units 33 + 151; corpus 190/0/0/18; audit 1270 declarations.

## Stage 2: enum seams without guards
[OBS] `emitSeamCopy`'s enum case now retags only the variant the value
holds: the certificate's recorded fn-entry variant, else the discriminant
the lowering knows STATICALLY (`constOfPlace` of the discriminant slot),
and emits `check discr ∈ [v]` either way; with neither the seam is
`unsupported`. The four programs that still used guarded retags (3 return
seams, pass_invalid_shr_option) all had a statically known variant
(`Some(..)` built in plain sight; as_ref's arm follows the certificate).
Corpus 190/0/0/18 unchanged; the loader emits NO `assignIf` anywhere (97
`check`s).

## Stage 3: delete `assignIf` and `SkipIf`
[OBS] Gone from mirlite (`Stmt.assignIf`), OSEA-IR (`Instr.SkipIf`), the
compiler (`emitSkipIfAround`, `reserveLabel`, `patchLabel`,
`StateIncr.patchLabel`; `StateIncr.code_none` stays, the route proof uses
it), the loader (`LStmt.assignIf`), brackets.lean (`skipLandsIn`, the jump
check). OSEA-IR is straight-line: no instruction moves the pc by more
than one.
[OBS] Proofs shrank: assignif.lean deleted (its `InvAtB.retarget`/`src_pc`
moved to check.lean); prmpres.lean deleted too — `PrmPres` existed only
for `assignIf`'s not-taken arm (nothing else used it). `IsBracket.nojump`,
`Seg.noskip`, `StmtOK.skips`, `Code.skips`, `Code.cons_skip`,
`Code.append_guard`, `skipIfAround_ok/err`, `Emits.skip` and the
`assignIf` arm of `compileStmt_spec` deleted. 50 proof files (was 52),
~19,100 lines (was ~19,950), 1236 declarations (was 1270), 3 axioms,
0 sorries.
[OBS] Tests: d16/d17/d18 (assignIf taken/skipped/body UB), the guarded
fresh-root probe and its golden g12 deleted — they tested `assignIf`
itself. g11 is now a golden for `check` (`Load; Check`). Tests that used
`assignIf` as a value probe (d98, d100, d101 sliceLen, d102, d105) now
`check` the value; strictly stronger, since a false guard silently
passed and a false check is stuck (d100 now pins 3-5 at u64 =
2^64-2). Units 33 + 146; corpus 190/0/0/18 of 208; `--osea` 190 matched,
B mismatch 0, 779 Dies route-checked; `--layouts` 190.
[DEC] `StmtSimBc` (simulation that may use compile success) was first
kept, then removed at the user's request: it existed for `assignIf`'s
body. Every leaf is a plain `StmtSimB` again, `StmtSimB.toC` is gone,
and `stmt_in_prog` no longer returns the statement's compile success.
The step theorem (paper `thm:step`) no longer assumes the statement
compiles. 1234 declarations.
Paper: grammar rows and rule `exec-check` replace `assignIf`/`skipIf`;
the lowering table's `check` row; the "guarded assignment" prose is a
paragraph on `check`; error classes list a failed check; counts updated.

