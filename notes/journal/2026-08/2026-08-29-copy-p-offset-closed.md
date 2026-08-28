# 2026-08-29 — Copy P→L (nonzero offset) closed: the quotient + the slide

## What closed
`copy_proj_offset_simulation`: `dst := copy src.f` at a real field
offset, both roots bound. Fragment `[Borrow(Shared); Memcpy; Die]` —
the shape that was FALSE before the overlap guard and UNSTATABLE
before the PermSim quotient. Dispatcher wired (both `pathOffset`
branches now closed); d36 covers it differentially (49/49). Audit
stays at 4; leaf axioms propext/Classical.choice/Quot.sound
(#print axioms; note: lean_verify can serve STALE axiom reports right
after a rebuild — cross-check with #print axioms).

## The two new pieces of machinery
1. **find?-quotient PermSim** (route (a) of the fork): `StackMapSim`
   relates stack maps per ADDRESS, not per list position. Surgery was
   astonishingly contained: the transports consume through
   `SB.find?_transport` and rebuild through `setChain_chain_respects`,
   so swapping both to find?-level (and `SB.set_respects` becoming a
   two-case find? argument — SHORTER than the old ListRel.filter
   proof) left every leaf untouched. Zero downstream breakage.
2. **Disjoint-range commutation** (keystone.lean):
   `sb_die_sb_write_comm` — die-then-write becomes write-then-die with
   a find?-identical result — via foldCells_ok_inv/of_cells and
   setChain_find?_not_mem/chain_key_not_mem; `sb_write_congr` moves
   the transported dst write from the keystone's parent-read state to
   the post-die state (equal observation fields, own NextTag).

## The proof's shape
overlap guard ⇒ disjointness; BRIDGE 1S (ref;read;die ≡ parent read);
`sb_write_congr` re-bases the dst write; `sb_die_sb_write_comm` slides
the die past it; `StackMapSim.congr_right` absorbs the representation
difference. Everything else is the standard leaf plumbing.

## Potholes met
- grind atom-splitting across SPELLINGS: `pathOffset f` vs `f.offset`,
  `blockSize` vs `layoutSize` coexist after simp partially unfolds
  abbrevs — grind treats them as distinct atoms and fails. Fixes:
  defeq-restate the typing fact in the unfolded spelling
  (`h_fit' : f.offset + layoutSize τ ≤ ... := h_fit`), or hand-write
  the interval arithmetic as calc chains.
- `0 + x` is not defeq to `x` (again): normalize run-lemma states with
  `simp only [Nat.zero_add]` at the FIRST run fact so the whole chain
  stays in one spelling.
- python splice: a mid-script assert aborts BEFORE the write — the
  earlier edits in the same script are silently lost. One replacement
  per script, or write incrementally.
- `foldCells_ok_of_cells` needs `(op := ...)` pinned explicitly (the
  conclusion alone leaves it a metavariable); content-form h_op
  obligations need `show`-beta before `rw [..._content_form]`, and
  under-binder rewrites need `simp only`, not `rw`.

## State
All targets 0 errors; units 16/16 + 49/49; suite 82/123 (0 fail);
axiom audit exact (4 pinned sorries unchanged).
