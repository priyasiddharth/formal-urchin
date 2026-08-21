# Regime D1 closed: `*p := v` simulates end-to-end (deref-read change pays off same-day)

[FACT] `const_write_deref_local_simulation` (proof/const_write.lean) is
proved: a constant write through a dereferenced BOUND pointer local —
the canonical deref write, the shape of every current witness — is
simulated by its `Load; CStore` fragment with `CompilerInv`
re-established. The proof is exactly the shape predicted this morning
when the deref-read change landed: the target `Load`'s SB read is the
read mirlite's `resolvePlaceAcc` now performs, transported by
`sb_read_respects_PermSim`; the loaded value is the ρ-renamed stored
pointer by `MemValSim` inversion; the `CStore` is BRIDGE 2 + the
`sb_write` transport. No SB-env-coherence invariant, as diagnosed.

[FACT] Two invariant extensions were needed after all (the morning's
"existing machinery only" claim was over-optimistic, corrected in the
audit):
- **`PlaceRegMapBound`** — new `CompilerInv` conjunct: every register in
  `placeRegMap` is `< nextReg`. The `Load` writes a FRESH register, and
  `LocalBindingSim` preservation needs it clear of bound locals'
  registers. This is the register half of the long-planned strengthened
  `CompilerStateWF` — regime C's blocker list shrinks accordingly.
- **strengthened `MemValSim` (ptrVal case)** — stored pointer tags are
  non-wildcard (core programs cannot mint wildcard pointers) and the
  referent range is in ρa's domain. Supplies BRIDGE 3's non-wildcard
  hypothesis and BRIDGE 2's `h_dom` for writes THROUGH loaded pointers.

[FACT] Proof obligations refactored into reusable lemmas (the point of
doing D1 carefully — D2/D3, regime C, copy and ref all consume these):
- `runN_Assgn_Load_ptr_step` (§F) — one-step execution of a pointer
  `Load`; reused per level of the D3 spine and by copy's loads.
- `resolvePlaceAcc_deref_local_inversion` (§F) — destructures mirlite's
  deref resolution into read-success + ptrVal-content + resolved-fields.
- `LocalBindingSim.insert_fresh_reg` (§F) — binding sim survives writing
  any register ≥ nextReg; the consumer of `PlaceRegMapBound`.
- `RegMap.lookup_insert_self`/`_ne` + a `LawfulBEq Register` instance
  (§F) — register-file update algebra (none existed).
- `placeToRegChecked_local_existing` (§D) — run/value pair for lowering
  a mapped local, stepping OVER the dependent match that blocks simp.
- `emit_nil` (§E) — `emit cs [] = cs`; collapses the no-op cleanup
  emits every non-local lowering produces.
- `compileStmt_deref_local_run` (const_write) — the fragment closed
  form `emit (emit {cs, nextReg+1} [Load]) [CStore]`.

[FACT] Regime D is now delegated by pointer-place shape: D1 (local,
CLOSED; fresh-local vacuous — `preparePlaceAssign` cannot allocate under
a deref), D2 (proj pointer place — blocked on the `sb_ref` transport,
same as regime C), D3 (nested deref — mechanical spine induction over
the D1 pieces, no new SB lemmas). Audit count 5 → 6 sorries (D split
into two named residuals), but the frontier moved: every closed shape is
end-to-end, and D2's blocker MERGED with C's.

Validation: units 14/14 + 37/37, suite pass 77 | fail 0 (117),
differential matched 77 | mismatch 0 | skipped 0, obseq2 green.

[EMP] (Lean 4.28) potholes hit: `set` is Mathlib-only — name
intermediate states by inlining the literal and letting defeq do the
rest; derived `BEq` instances don't unfold by instance name but DO
iota-reduce on constructor forms (`show (n == m) = ...` works);
`subst` on `obtain`-produced equalities again eliminated the unprimed
side (write downstream script against the primed names).
