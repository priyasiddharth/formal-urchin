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
