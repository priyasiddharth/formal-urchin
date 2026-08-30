# Gate leaves on the WHOLE place the mother lemma can swallow

[FACT, 2026-08-29] `const_write_deref_chain_simulation` subsumed BOTH
the D-spine leaf (`*spine := v`, ~300 lines) and the depth-1 proj-top
leaf (`*(s.f) := v`, ~400 lines + two fragment lemmas) — net deletion
of ~750 lines for one ~200-line leaf. The process that got there, in
the order it actually happened:

1. **Pending-cleanup audit of the lowering** (planning, not proving):
   `placeToRegChecked` reassociates proj-of-proj away, only the
   nonzero-proj arm emits a `Borrow`+cleanup entry, and the deref arm
   DISCHARGES the accumulated cleanup right after its `Load`. So a
   proj's base is always cleanup-free and the pending list is ≤ 1 —
   every interior projection is a CONTIGUOUS `Borrow(Shared); Load;
   Die` triple, i.e. exactly BRIDGE 1S's statement shape. The dreaded
   "list of deferred Dies" never exists.

2. **Forced type-generalization.** Writing the mother lemma's
   `derefProj` case forced dropping the `Place Γ (PtrL τ)` restriction
   to `Place Γ τ` for ANY τ: in `(*q).f` the proj's base `*q` is a
   STRUCT-typed deref, so the induction hypothesis must speak about
   non-pointer-typed places. This felt like a chore; it was the pivot.

3. **The wiring insight** (only visible after 2): once the lemma is
   typed at any layout, it can be instantiated at the statement's
   WHOLE dst, not merely at the pointer place under the deref. And
   `PtrChain (.deref P)` holds iff P is a chain (`.deref` ctor) OR
   `P = .proj b f` with b a chain (`.derefProj` ctor) — definitionally
   the UNION of the D-spine class and the proj-top class. Called at
   `kind := Mut` on the dst, the lemma performs the entire dst
   lowering INCLUDING the final `Load`; the leaf is left with one
   `CStore` + BRIDGE 2 + the invariant rebuild.

4. **Consequence for the planned surgery:** the plan said "generalize
   the depth-1 leaf's base from a code-free local to a chain via a
   mother-lemma call". That surgery was never performed — the
   depth-1 leaf's ENTIRE Borrow/Load/Die endgame already lives inside
   the mother lemma's `derefProj` case, so the leaf itself became
   redundant, not just its base-handling section.

**How to apply** (the reusable heuristic): when a leaf's structure is
"lower a place, then one event through its result", check whether the
place-lowering mother lemma can be instantiated ON THE BIGGER PLACE —
an induction's last case IS the leaf's endgame. Gate dispatchers on
the largest place the lemma swallows (`PtrChain (.deref p)`, not
`PtrChain p`). Candidates: copy's D→L leaf and ref's deref-src/dst
leaves still call the lemma on the INNER pointer place and hand-run
the final Load — each could shrink the same way when next touched.

**Consumers/refs:** const_write.lean (chain-dst leaf + dispatcher),
spine.lean (`PtrChain`, `ptrChain_lowering_sim`),
journal 2026-08-29-ptrchain-mother-lemma.md,
journal 2026-08-29-chain-dst-subsumption.md.
