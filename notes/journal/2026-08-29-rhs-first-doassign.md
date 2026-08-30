# 2026-08-29 — mirlite doAssign goes rhs-first (SEMANTICS CHANGE, flagged)

## What changed
`mirlite.doAssign` now evaluates in Rust's documented assignment
order: prepare the dst root, **evaluate the rhs**, THEN resolve the
dst place (on `output.state`), then the copy-overlap guard, then
`writeResolvedPlace` on `{output.state with perms := permsD}`. The
old dst-resolve-then-rhs order lived in `doAssignCont` (def retained,
no longer referenced).

This is the SOURCE-side completion of the d34 lowering-order arc: the
compiler's assign arm was moved to MIR order (rhs pre-phase → dst
lowering → store) on 2026-08-28; the source still resolved the dst
first. The orders only diverge when the dst has a deref spine AND the
rhs raises events — a rhs retag can pop a tag a later dst-spine read
needs (and vice versa). That divergence is exactly what blocks ref's
deref-dst leaves, hence the swap now.

## Why it is safe / faithful
- Rust's reference documents rhs-before-place evaluation for
  assignment; Miri follows it. The old order was OURS, not Rust's.
- No corpus program distinguishes the orders: conformance stayed
  82 pass | 0 fail | 41 unsupported of 123 across the swap.
- Units 17/17 + 55/55 unchanged; axiom audit exact at the same 4
  residuals.

## Proof fallout (the repair sweep)
~28 errors across ref/copy/const_write, all mechanical:
- ref.lean: 6× `simp only [h_envD] at h_step` before `have h_w :=`
  (dst resolution now sits above the write in the term); F→L instead
  needs `simp only [hD1]` — its dst is unbound, resolution runs on
  the SET env, so the prepared-binding fact discharges the match, not
  `h_envD`. Both-unbound dispatcher exfalso re-simped.
- copy.lean leaves (L→L, P0→L, P→L): the overlap-guard `by_cases
  h_ov` moves AFTER the read inversion + a `simp only [h_envD]`
  reduction of the dst match; `case pos =>` inline keeps the §2
  remainder's indentation. D→L: `h_fit` (range check, rhs-side) now
  precedes `h_ov` (guard, post-rhs); dead branches collapse from
  `split<;>first` to plain `simp` (rhs error now kills the whole
  term before any dst structure exists).
- const_write.lean caller: reduce `mirlite.evalRExpr` in the same
  simp as `h_prep` so the resolveAcc match surfaces at `s_pre`
  (constInit's rhs is stateless, `output.state = s_pre`).

## State
All targets green; units 17/17 + 55/55; suite 82/123 (0 fail);
axiom audit exact; audit at 4. Deref dsts for ref are now unblocked.
