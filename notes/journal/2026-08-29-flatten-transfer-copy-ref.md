# 2026-08-29 — Flatten transfer across copy/ref; all deref arms TOTAL

## What closed
The flatten transfer (see [[flatten-transfer-explained]]) applied to
the three remaining deref dispatch arms:
- copy deref-src (`y := copy *place`, any spelling) — TOTAL for bound
  dsts;
- ref deref-src (`q := &kind *place`) — TOTAL for bound dsts;
- ref deref-dst (`*place := &kind src`) — TOTAL for bound srcs.
`y := copy *(s.f.g)` and `q := &mut *(s.f.g)` (proj-of-proj src
spellings) leave the residuals — d51 pins both.

## The pieces
- Three SOURCE statement congruences (spine.lean):
  `stepStmt_assign_dstderef_flatten` (rhs-generic!),
  `stepStmt_assign_copysrc_flatten`, `stepStmt_assign_refsrc_flatten` —
  each a simp over doAssign/evalRExpr with the ∀-state flatten
  equations as rewrite rules.
- stmt0 surgery on the three collapsed leaves (the known recipe: the
  triple in, h_stmtRun := (h_run0 _).trans canonical, value via h_val0,
  csAt witness at run(stmt0)).
- COMPILED statement pairs per shape. The recurring proof shape: bind
  simp; case ONCE on shared segments (ensure, the src-local pre); at
  the diverging dst/src lowering, 4-way case aligned by
  `placeToRegChecked_flatten_agree` (instantiated at the right
  intermediate state); errors align by the map-equation, oks by the
  result-equation; close with `rw [h_agr]`. The ref-src pair goes
  through the borrow-deref arm — both sides share their prefix, so the
  alignment is the INNER agree at `Shared P`, not at the deref.
- A rhs-level "valunit" lemma (`(value …).map (fun _ => ())` equality)
  turned out to be the right currency for statement-level ok/error
  alignment when the payload types differ.

## State
All targets green; units 17/17 + 64/64; corpus 82/123 (0 fail); audit
exact at 3. Copy's residual: proj-topped srcs over non-local bases,
unbound dst, non-local dst. Ref's: proj-topped dsts over non-local
bases, non-local srcs under non-local dsts, unbound roots. Next:
regime-B unbound roots (const_write_proj_nonlocal's last classes) or
the C-deref collapse+flatten for the proj-dst gates.
