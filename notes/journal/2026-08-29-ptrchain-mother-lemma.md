# 2026-08-29 — The blocker falls: `ptrChain_lowering_sim` (pending-cleanup spine)

## What closed
The deep-chain blocker's core. `PtrChain` (spine.lean): canonical
pointer chains — local | deref of chain | deref of (ONE proj over a
chain); projs only under derefs, never stacked (reassociation keeps
that canonical). `ptrChain_lowering_sim` generalizes the retired
`loadSpine_lowering_sim` with exactly three interface changes:
- +hypothesis `TagRenameBounded ρt s_mir… s_osea…` (feeds BRIDGE 1S's
  side conditions per level);
- target-counter conjunct weakened `=` → `≤` (interior mints die but
  the counter stays);
- everything else VERBATIM — `cleanup = []`, mem untouched, and
  `PermSim ρt permsD s_osea'.perms` at the UNextended rename, because
  the interior tags die and BRIDGE 1S's stack/exposed/protFrames
  equalities transport the cancelled state.
The new `derefProj` case is the depth-1 leaf's endgame replayed inside
the induction: ih on the base chain, this level's source deref check +
pointer-cell read, `sb_read_respects_PermSim` → supplier →
`sb_ref_read_die_cancels`, run Borrow/Load/Die, PermSim rebuilt from
the BRIDGE equalities (the const_write §1105 expression, verbatim).
The zero-offset sub-case is the plain deref step with a shifted-by-0
address. Base case's range conjunct now comes from LocalBindingSim's
block-domain fact (the `k < 1` shortcut died with the PtrL-type
restriction — the lemma is now stated at ANY place type, which is what
lets a struct-typed `.deref q` sit under a proj).

## Migration
Five consumers swapped in one pass: pass `h_spine.toPtrChain` + h_tbd;
the seven h_pnt2 equality-rewrites became `TagRenameBounded.mono …
h_pnt2` closers (one site had already half-converted to mono — its hA
became a ≤ and the final `rw [hA]` a `Nat.le_trans`). First build
green. Old lemma deleted; `LoadSpine` retained (leaf signatures and
dispatchers still gate on it until the wiring increment).

## Potholes hit (all catalogued, plus one new)
- record-`with` layout: `{ s with field := x,` with fields CONTINUING
  on later lines fails to parse (newline field-separation); fields
  must start on lines after `with`. Same for a dite-record inside a
  `have` TYPE ascription — sidestep by using the library equation
  (`placeToRegChecked_proj_root_eq`) UNascribed.
- simp refuses the dependent evidence argument → `rfl` closes (defeq).
- LocalBindingSim eta on `exact` even THROUGH an ascribed `have` —
  intro-then-apply (`intro τ loc b h; exact h_lbs2 loc b h`).
- subst ate p2 in favor of qAcc' (roulette, again).
- nested `insert_fresh_reg` needs the middle state pinned by its own
  ascribed `have` (metavar state can't be inverted from `rfl`).

## What this unblocks (the wiring increment, next)
- `const_write_deref_deep_residual`'s chain class: nonspine
  dispatchers re-gated on PtrChain; depth-1 proj-top leaves
  generalized to chain bases (mother-lemma call replaces "base is a
  code-free local").
- copy D→L / ref deref-src / ref deref-dst automatically cover deeper
  mixed chains once their dispatchers test PtrChain instead of
  LoadSpine.
- Left: proj-of-proj normalization inside chains, unbound roots,
  non-local srcs.

## State
All targets green; units 17/17 + 56/56; corpus 82/123 (0 fail); axiom
audit exact at the same 4 residuals (coverage widens only at wiring).
