# 2026-08-29 — The collapse travels: copy D→L and ref deref-dst

## What closed
Both leaves re-founded on the whole-place mother lemma, per the
[[chain-leaves-gate-on-the-whole-place]] heuristic:
- `copy_deref_local_simulation`: `dst := copy *P` for every
  `PtrChain (.deref P)` — closes `y := copy *(s.f)` (d47) and every
  interior-proj chain. ~170 lines replace ~430 (leaf + two fragment
  lemmas). New fragments `compileStmt_copy_derefchain_run/_value`
  (one `Memcpy` over the opaque src-lowering run).
- `ref_derefdst_local_simulation`: `*P := &src` for every
  `PtrChain (.deref P)` — closes `*(t.f) := &x` (d48). The mother
  lemma runs at `Mut` on the WHOLE dst from the post-Borrow state
  under the extended rename; its register-frame conjunct carries the
  borrow temp across the entire dst lowering. §§7–8 (spine call +
  hand-run Load + find inversion) deleted.
Dispatchers regated `PtrChain pp` → `PtrChain (.deref pp)`.

## Technique notes (grind per user instruction)
- Keeping the src/dst resolution OPAQUE for the mother lemma while
  reducing a sibling `.local` resolution needed
  `resolvePlaceAcc_local` (a 3-line targeted equation) — putting
  `mirlite.resolvePlaceAcc` in the simp set unfolds ALL exposed
  applications, including the one the lemma wants whole.
- `rw [h_dres]` needs a `simp only at` iota before if/match rewrites
  land at the rs-spelling.
- The pre-phase of copy is NOT pure: h_incrS's value-matches collapse
  with the already-obtained `h_sval0` in the simp set, then a chain of
  `emit_state_incr` — no split needed.
- geometry/bounds side goals (h_fit negation, h_lt, h_dom identity)
  all fell to grind, with `Nat.add_sub_cancel'` spelled out once (the
  known sub-identity gap).
- A dead `h_regne1` fell out: with no post-lemma register insert, the
  RStore's two operand lookups are independent facts — no
  insert-distinctness needed at all.

## State
All targets green; units 17/17 + 61/61; corpus 82/123 (0 fail);
axiom audit exact at 4. Residual docstrings narrowed: copy's chain
srcs and ref's deref-dst chains are out. Left for the leaves' family:
ref deref-src collapse (wants the borrow-deref bind equation),
proj-TOPPED srcs/dsts over non-local bases, proj-of-proj
normalization, unbound roots.
