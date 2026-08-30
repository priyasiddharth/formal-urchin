# Projected copy destinations: recursion + a zero-offset leaf

[OBS 2026-09-03] `(*p).0 := copy y` — a PROJECTED destination — is now
closed at zero offset, and the whole projected-destination arm has a
recursive dispatcher instead of a flat residual.

**What landed** (`src/obseq3/proof/copy.lean`, `common.lean`,
`spine.lean`):

- `copy_projdst_zero_chainsrc_simulation` — the two-mother leaf with the
  destination read one projection layer deep. Only three things change
  from `copy_chaindst_chainsrc_simulation`: the destination resolution
  is opened with `resolvePlaceAcc_proj_base_ok` and collapsed by
  `{rd with addr := rd.addr + 0} = rd`; the compiled fragments become
  the proj-dst pair; and the write is at layout `τ` while the register
  points at a `σb` block — which `writeThroughPtr_sim` already tolerates
  (it is layout-generic; the bound comes from the source write's own
  check). Note the two layouts genuinely differ, so this could NOT be
  reduced to the chain leaf by rewriting places: `*P : Place Γ σb` and
  `(*P).f : Place Γ τ` are different types.
- `copy_projdst_simulation` — recursion on the destination's BASE place,
  mirroring `const_write_proj_simulation`. Nested projections peel with
  `compileStmt_assign_proj_assoc_run/_value` and the new
  `stepStmt_assign_dst_proj_assoc`; a deref base at zero offset hits the
  leaf; a local base or a nonzero offset falls to the residual.
- Four `compileStmt_copy_projderefdst_{src,dst}flatten_{run,value}`
  transfers — a pure textual lift of the deref-dst four, with the dst
  place wrapped in the projection. They compiled unchanged, which is the
  strongest evidence yet that the ONE-PLACE-PER-LEMMA shape (see
  durable/flatten-one-place-at-a-time.md) is the reusable one.
- `copy_place_residual` now carries the stmt0 transfer triple, so the
  recursion can fall back to it mid-flight. Same sorry, more general
  statement; the pin is unchanged at 2.

**The pothole worth remembering.** [OBS] Unfolding the projection layer
(`placeToRegChecked_proj_root_eq`) inside a `StateIncr` proof turns the
destination's compiler state into a `match … with | ok a => … | error a
=> …` whose branches are IDENTICAL — and none of the emit-tower lemmas
match a match. The fix was NOT to case-split but to add two small
bridges in `common.lean`:

    placeToRegChecked_proj_zero_run   : run (proj base path) cs = run base cs
    placeToRegChecked_proj_zero_value : value base cs = ok o →
                                        value (proj base path) cs = ok ⟨o.result, …⟩

With the run bridge the projection stays OPAQUE in the tower proofs and
one `rw` converts the state to the base spelling, after which the chain
leaf's tactic text applies verbatim. Both bridges proved in three lines.
General shape: when a wrapper is state-neutral, prove the state equation
and rewrite; do not unfold the wrapper.

**Teeth.** The obvious mutation (make the zero-offset shortcut fire on
the wrong condition) is rejected at TYPE-CHECK, not by a witness: the
`PlaceToRegEvidence.projZero` constructor demands `pathOffset path = 0`,
so the shortcut cannot be mis-taken. d62 pins the behaviour end to end
(`(*p).0 := copy y` then the read-back agrees on both machines).

**Validation:** full build green; 17/17 + 75/75; corpus 82 pass / 0 fail
/ 123; `scripts/audit_axioms.sh` exact at 2 sorries.
