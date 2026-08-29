# 2026-09-03 — C-deref collapse: the proj-dst deref arm goes total

## What happened
The two C-deref leaves (`const_write_proj_deref_zero_simulation`,
`const_write_proj_deref_simulation`, dst `.proj (.deref P) path`) were
COLLAPSED onto `ptrChain_lowering_sim` at `Mut (.deref P)`, regated
from `PtrChain P` to `PtrChain (.deref P)` (the WHOLE pointer place —
so proj-interior chains like `*((*q).f)` now route in). Then the
proj-dst dispatcher's deref arm was made TOTAL with a flatten transfer,
retiring the residual's non-chain class. Only unbound roots remain in
`const_write_proj_nonlocal_residual`.

## Shapes
- New fragment pair `compileStmt_proj_deref_zero_run/_value` and
  `compileStmt_proj_deref_run/_value`: stated over the OPAQUE
  `run (placeToRegChecked Mut (.deref P))` (via
  `placeToRegChecked_proj_root_eq` + `dif_pos/neg`), exactly like the
  chain-dst fragments. Zero-offset = one `emit [CStore]`; nonzero =
  `emit³ [Borrow(Mut); CStore; Die]` over a fresh tmp register.
- Zero leaf: resolveAcc opened ONE proj layer with the new
  `resolvePlaceAcc_proj_base_ok/_err` helpers (chain resolution stays
  opaque for the mother); the projected resolution
  `{rd with addr := rd.addr + offset}` η-collapses to `rd` at offset 0
  (`simp [h_o']` after coercing `pathOffset = PathTo.offset`); endgame
  = chain-dst leaf verbatim.
- Nonzero leaf: mother at Mut gives the loaded register + entry;
  endgame is depth-1 BRIDGE 1 (`sb_ref_Mut_ok_of_sb_write_ok` →
  `sb_ref_use_die_cancels`) with the Borrow bound from the source
  WRITE's own bounds check, ONE fresh register (vs two pre-collapse:
  the mother swallowed the Load).
- Dispatcher: `PtrChain_flatten_deref pp` supplies the gate for
  `flattenPlace (.deref pp)` outright;
  `compileStmt_const_projderef_flatten_run/_value` (compiled side) +
  the flatten congruences (source side) transfer everything.

## Potholes (new entries)
- **omega is blind to `Word`-flavored hypotheses.** `h_dle :
  rd.allocBase ≤ rd.addr` (a mother-lemma conjunct) is IGNORED by
  omega — its ≤ carries the `Word` abbrev as the type argument and
  omega's syntactic Nat check refuses it; goals stated the same way
  get no constraints at all. Everything the OLD leaves proved here
  went through grind or a `Nat.*` lemma (which re-unifies the type
  args to `Nat`) — that was load-bearing, not style. Fixes:
  `Nat.sub_add_comm h_dle`, `Nat.not_lt.mp h_nb` + `simpa`, grind.
- **`pathOffset` vs `PathTo.offset` are distinct atoms** to
  omega/grind (reducible abbrev, never unfolded). Normalize the
  endgame's spellings to ONE of them; a bridging `rfl` hypothesis does
  NOT help (omega drops it as trivial after whnf).
- **A fully dst-generic compiled flatten transfer is impossible as
  stated**: `compileStmtChecked (assign dst rhs)` is STUCK for a
  variable dst (the match's earlier `.local` arm) — state transfer
  pairs at a constructor-headed dst (here `.proj (.deref pp) path`).

## Witnesses
d52 `(**q).0 := v` / `(**q).1 := v` (depth-2 chain under a projection,
both offsets); d53 `(*(s.f.g)).1 := v` (proj-of-proj pointer base —
the flatten transfer is load-bearing). Teeth: broke the proj-arm
Borrow offset (`offset + 1`) → both fail with target-UB verdicts;
restored. 66/66.

## State
Full build green; 17/17 + 66/66; corpus 82 pass / 0 fail / 123; audit
exact at 3 sorries (residual narrowed, not yet closed — whitelist
unchanged). Next: regime-B unbound roots (allocateRoot + fresh-block
C0/C1 endgames) → residual to zero, whitelist 3 → 2.
