# 2026-08-28 — Regime D→L closed: `dst := &kind *p` through a load spine

## What closed
`ref_deref_local_simulation` (proof/ref.lean): a reference through a
LOADED pointer, stored into a bound local, `P` any load spine (any
deref depth). Fragment `[P-code; Load; Borrow(kind, offset 0); RStore]`.
Dispatcher `CompilerInv_step_ref`'s `| deref pp =>` src arm now splits
on `LoadSpine pp` and dst boundness; only non-spine/unbound shapes fall
to `ref_place_residual`. Audit stays at 4 (strictly narrower).

## The proof, by provenance
A composition of two existing texts with ONE new idea:
- spine prelude + source inversion: `const_write_proj_deref_simulation`
  (loadSpine_lowering_sim, sb_read transport for the Load, MemValSim
  extraction of the loaded `Ptr b2 o2 s2 t2`).
- endgame: `ref_proj_local_simulation` (sb_ref transport minting the
  fresh pair into `ρt.extend`, BRIDGE 2 `writeThroughPtr_sim` for the
  RStore into the dst binding).
- the NEW idea (the point of the whole event-fix arc): the target
  `Borrow`'s bound `b2 + o2 + 0 + blockSize τ ≤ b2 + s2` comes from the
  SOURCE's retag-dereferenceability check — `by_cases` on the event
  check in `h_step`, failure contradicts source success, success is
  the bound in source names, and `MemValSim`'s `o' = o ∧ s' = s`
  makes those names the target names. One `grind`.
- the stored values pair up as
  `ptrVal b2 (b2+o2-b2) s2 permsP'.NextTag` ~ `Ptr b2 (o2+0) s2
  p2.NextTag` under the extended ρt (`extend_self` + the loaded
  pointer's own range conjunct for the domain field).

## New potholes met (all previously catalogued, all bit anyway)
- `subst h_dr2` (dstReg2 = dstReg) ate `dstReg` — rewrote at the
  hypotheses instead (`rw [h_dr2, h_baseD2] at h_entryD2`).
- `LocalBindingSim.rename_mono` without type ascription eta-expanded;
  ascribing the full type fixed it.
- `omega` blind to `Word`: `b2+o2+0+blockτ ≤ b2+s2` from
  `¬(b2+o2+blockτ > b2+s2)` — omega fails, `grind` closes.
- `RegMap.lookup_insert_ne`'s hypothesis is `k' ≠ k` (looked-up ≠
  inserted) — no `Ne.symm`.
- the dependent-motive rewrite: `(ensureLocalRegE …).value.result.reg`
  cannot be rewritten to `dstReg` under the evidence binder (evidence
  TYPE depends on the reg). Dodged: state `h_incr1` for ∀ registers and
  `split` on the match instead of `cases` on a named scrutinee.

## grind audit (user-requested pass)
New theorem refactored: h_cancel, h_offP, h_le2 (the event bound),
h_dr2, h_nw_new, h_regne1/2 all close by `grind` (two `have`s deleted
outright). The C-deref twin still carries the manual chains — left
as-is, candidate for a later sweep.

## State
Suite 82/123 (0 fail), differential 82/0/0, units 16/16 + 44/44.
Axioms of the leaf: propext, Classical.choice, Quot.sound.
`CompilerInv_step_ref` still sees sorryAx only via `ref_place_residual`.
