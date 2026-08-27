# Ref regime F→L closed: the first statement that extends ρt twice

[FACT] `ref_fresh_dst_simulation` (proof/ref.lean) is proved: `&src`
stored into an UNBOUND local. mirlite's prepare allocates the
destination, so the fragment is three instructions — `Alloc; Borrow;
RStore` — and BOTH renames grow. Audit 5 → 4. `CompilerInv_step_ref`
now has one residual left (proj/deref places).

[FACT] It is the first statement in which ρt extends TWICE: `sb_own`
mints the destination's root tag, then `sb_ref` mints the reference tag.
The chain works with no new machinery because each minting member
RETURNS the `TagRenameBounded` at the intermediate counters that the next
one TAKES as a hypothesis. That is the payoff for making the bound an
invariant conjunct (2026-08-22) rather than a per-leaf side condition —
the design was chosen for `sb_ref` alone and composed for free here.
`TagRenameIncr.trans` glues the two extensions into the single
`TagRenameIncr ρt ρt''` the theorem must produce.

[FACT] ρa extends once, at the identity pair, and needs no freshness side
condition — `IdentityOnDomain` supplies it (the 2026-08-22 asymmetry
again). But unlike regime B, here the extension must be TRANSPORTED into
facts that were established before it: `doAssign` resolves the SOURCE
against the POST-allocation state, so the source local's `ρa`-facts
(`h_raS`, and the block-domain conjunct `h_domS`) cross the destination's
allocation. `AddrRenameIncr` + the `.choose`/`.choose_spec` pattern
handles it; nothing new was needed.

[FACT] Two new structural lemmas, both of independent use:
- `prepare_lookup_ne` — preparing one local's assignment leaves every
  OTHER local's binding alone (either the destination was bound and the
  state is unchanged, or `Env.set` touched only its own index). Needed
  twice: once in the regime, once in the dispatcher's doubly-unbound
  branch.
- `layout_ne_ptrL` / `ref_dst_src_idx_ne` — a `PtrL τ`-typed destination
  and a `τ`-typed source are NECESSARILY distinct locals. `Local` carries
  `Γ.get idx = τ`, so equal indices would force `τ = PtrL τ`, refuted by
  `congrArg sizeOf`. Without this the dispatcher cannot rule out the
  case where the destination allocation binds the source.

[EMP] (Lean 4.28) `grind` proves the `Env.set` case splits and the
register-distinctness goals, but NOT `τ ≠ PtrL τ`: its equivalence-class
reasoning sees `{τ, τ.PtrL}` as one class and has no occurs check. Plain
`simp` on `congrArg sizeOf h` closes it in one step (the `omega` I
reached for first was surplus — `simp` already discharges the
`sizeOf` arithmetic). Rule of thumb: `grind` for case analysis and
congruence, `sizeOf` + `simp` for structural impossibility.

[EMP] (Lean 4.28) two potholes, both about elaboration order:
- A `by`-block argument whose goal mentions still-unassigned implicits
  reports the goal with metavariables and fails opaquely. Hoist it to a
  `have` with the type written out, or pin the state argument
  explicitly — `runN_Assgn_Borrow_step` needed BOTH here.
- `{ X with nextReg := n }` elaborates to a `have __src := X; { … }`
  binding, so `getPlaceInfo` of it is not syntactically
  `getPlaceInfo (setPlaceInfo …)` and `rw` misses. A one-line `rfl`
  lemma (`getPlaceInfo_setNextReg`) restores the rewrite chain — the
  same fix as `getPlaceInfo_emit` on 2026-08-22.

[OBS 2026-08-23] The fragment closed-form was wrong on the first
attempt: I omitted the `nextReg` bump that `freshRegM` performs between
the `Alloc` and the `Borrow`, so the RHS named register
`R (cs.nextReg + 1)` in a state whose counter was still `cs.nextReg + 1`.
The final `simp` reduced the goal to `False` rather than erroring at the
mismatch — worth knowing as a signature: *a closed-form lemma whose
residual goal is `False` means the stated form is wrong, not that a
rewrite is missing.*

Validation: units 15/15 + 38/38, suite pass 80 | fail 0 | unsupported 41
(121), differential matched 80 | mismatch 0 | skipped 0, all targets
build. `#print axioms ref_fresh_dst_simulation`: propext /
Classical.choice / Quot.sound.

**References:** proof/compiler.lean (audit),
2026-08-22-ref-ll-closed.md, 2026-08-22-tagrenamebounded-wired.md,
2026-08-22-regime-b-closed.md.
