# 2026-08-29 (third) — copy's proj-sources collapse onto the chain base

## What happened
`copy_place_residual` narrowed to DST-shape classes only: for a bound
local dst, every source spelling is now closed. Two collapsed leaves
replace the old bound-local-base pair, and a src flatten transfer feeds
them everything else.

- `copy_projchain_zero_simulation` / `copy_projchain_offset_simulation`:
  src `.proj B path` gated `PtrChain B`. The mother lemma at `Shared`
  on `B` supplies the base register; zero offset adds one `Memcpy`,
  nonzero adds `[Borrow(Shared); Memcpy; Die]`.
- Fragments `compileStmt_copy_projchain_zero/offset_run/_value` over the
  opaque `run (placeToRegChecked Shared B)`.
- Src flatten transfer: `stepStmt_assign_copysrc_anyflatten` (source,
  src-generic), `compileRExprToChecked_copysrc_anyflatten_run/_valunit`
  + `compileStmt_copy_srcflatten_run/_value` (compiled, src-generic
  because the dst is constructor-headed `.local`), and
  `flatten_proj_chainish` (a flattened projection is ALWAYS one
  projection over a chain — the `.inr` half of `flatten_chainish` with
  the impossible half discharged).
- DELETED: `copy_proj_zero_simulation`, `copy_proj_offset_simulation`
  and their four fragments — 617 lines, subsumed.

## Potholes (new)
- **`set` is a Mathlib tactic** and this project has no Mathlib: a
  `set x := e with h` reads as "unknown tactic". Spell the term out or
  use `have h : e = e := rfl`.
- **Dependent evidence types do not transport along a flattening
  equation.** `compileStmtChecked (assign dst (copy p))`'s value type
  mentions `p`, so `rw [h_flat]` on a hypothesis `value … = ok so`
  fails. Fix: state the value transfer with an EXISTENTIAL hypothesis
  (`(∃ so, value (flattened) = ok so) → ∃ so', value (orig) = ok so'`)
  — the existential hides the dependent type, so the motive is fine.
  The run transfer needs no such care (it returns a CompilerState).
- **Record-update projections block `rw [if_pos/if_neg]`.** After
  `resolvePlaceAcc_proj_base_ok`, the source's guards read
  `{rb with addr := …}.addr < …`; `rw` on a spelled-out condition finds
  no match. Fixes used: `simp only [gt_iff_lt] at h_step` (any real
  rewrite normalizes the projections), or a `have h_rp : resolvePlace? …
  = some {explicit fields}` + `rw` + `dsimp only`.

## Witnesses
d55 `x := copy (*p).0` / `y := copy (*p).1` (proj over a pointer chain,
both offsets); d56 `x := copy s.1.0` / `s.1.1` (proj-of-proj, flatten
load-bearing). Teeth: pointed the `Memcpy` at the dst register instead
of the source (`Instr.Memcpy dstPtr dstPtr`) → both fail with target-UB
verdicts; restored. 69/69.

## State
Full build green; 17/17 + 69/69; corpus 82/0/123; audit exact at 2.
copy's remaining classes: UNBOUND dst (regime-B composition, now
straightforward after `const_write_proj_fresh_simulation` and
`extendIdRange`) and NON-LOCAL dst (`Borrow(Mut); Memcpy; Die`).
