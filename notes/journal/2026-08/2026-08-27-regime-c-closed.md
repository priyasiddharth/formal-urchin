# Regime C closed: BRIDGE 1 finally does work

[FACT] `const_write_proj_simulation` is proved for a bound-local base,
split by the projection's OFFSET — which is what decides the lowering's
shape, not the base's type. C0 (offset zero): `placeToRegChecked` returns
the base's own register, so the fragment is a bare `CStore` and the proof
is regime A with a wider `allocSize` (a projected place's bounds come
from the BASE's layout, not from `NatL`). C1 (nonzero): the compiler
mints an internal `Borrow(Mut)` into a temp and records a `Die` that the
assign arm emits after the store — `Borrow; CStore; Die`.

[FACT] C1 is the FIRST closed regime whose target mints a tag, uses it,
and kills it, and therefore the first consumer of BRIDGE 1
(`sb_ref_use_die_cancels`, proved 2026-08-15). Twelve days and eleven
closed regimes later, the keystone finally carries weight. What it gives
is exactly what is needed: the triple's net effect on the stacks equals
the bare parent write the SOURCE performs, so `PermSim` transfers from
BRIDGE 3's result by rewriting three component equalities
(`StackMap`/`protFrames`/`exposed`) and composing the `NextTag ≤`.

[FACT] Both of BRIDGE 1's side conditions turned out to be DERIVABLE from
the invariant rather than assumable, which is the day's real result:
- `sb_ref_Mut_ok_of_sb_write_ok` — BRIDGE 1 takes the retag's SUCCESS as
  a hypothesis, and on the target nothing supplies it: the source
  performs a bare write, so there is no retag to transport. But a mutable
  retag is per cell `writeCell` then `pushCell`, and a push onto the
  stack the write just produced cannot fail — so write-success implies
  retag-success. Proved by feeding `foldCells_ok_inv`'s per-cell data
  straight into `foldCellsIdx_ok_of_cells`, i.e. entirely out of
  machinery that already existed.
- `freshTag_not_protected` — `h_unprot` says the freshly minted tag is
  not already protected. Every tag in a target protector frame came
  through ρt (`PermSim`'s `TagListSim` component), and
  `TagRenameBounded` puts ρt's whole range strictly below the counter,
  so the tag being minted AT the counter cannot be in a frame. Third
  time the bound has paid for itself beyond the case it was introduced
  for.

[OBS 2026-08-27] Pattern worth naming: every BRIDGE has needed a
companion "…succeeds when…" lemma on the target side, because the
bridges are stated as transports of a SUCCESSFUL source event and the
target sometimes performs an event the source does not. `sb_ref` was the
first (its own member handles it), and this is the second. Expect the
same for copy's `Memcpy`.

[EMP] (Lean 4.28) `0 + x` is NOT defeq to `x` for `Nat` (addition
recurses on the second argument), so a register entry holding
`bo + offset = 0 + offset` will not unify with a resolved place's
`addr - allocBase = offset`. `Nat.add_zero` is defeq; `Nat.zero_add` is a
theorem. Hoist the equation as a `have` and `rw` it rather than hoping.

[EMP] (Lean 4.28) `omega` again failed on a `Word`-typed goal
(`binding.addr + off + 1 ≤ binding.addr + size`); `Nat.add_assoc` +
`Nat.le_of_add_le_add_left` closes it. Same pothole as 2026-08-23 — this
is now the third occurrence, so: on any goal whose atoms are `Word`
projections, reach for the `Nat` lemma FIRST.

[OPEN] The residual narrowed rather than vanished:
`const_write_proj_nonlocal_residual` (base is itself a proj or a deref).
There the base's lowering emits code and carries its own cleanup, so the
fragment is not three instructions and the `Die` sequence is a LIST —
`runN_cleanupInstrs` exists for that, and composing it with BRIDGE 1 per
level is the work owed.

Validation: units 15/15 + 38/38, suite pass 80 | fail 0 | unsupported 41
(121), differential matched 80 | mismatch 0 | skipped 0, all targets
build. Audit stays at 4. Axioms: propext / Classical.choice / Quot.sound
throughout (`freshTag_not_protected` needs only propext / Quot.sound).

**References:** proof/compiler.lean (audit), proof/keystone.lean
(BRIDGE 1), 2026-08-22-tagrenamebounded-wired.md.
