# 2026-09-01 — Three-for-three: ref deref-src collapses; the base-fact conjunct

## What closed
`ref_deref_local_simulation` re-founded on the whole-place mother
lemma: `dst := &kind *P` for every `PtrChain (.deref P)` — closes
`q := &mut *(s.f)` (d49) and every interior-proj chain source. All
three deref leaves (copy src, ref dst, ref src) now stand on
`ptrChain_lowering_sim`; no leaf hand-runs a `Load` anymore.

## The two techniques this leaf added
1. The borrow-deref fragment WITHOUT a standalone bind lemma: the
   borrow arm shares its prefix with the place-lowering deref arm, so
   `compileStmt_ref_deref_run` is proved by ONE case split on the
   INNER value (`cases h_x : value (Shared P) cs`): the error arm
   contradicts the deref-level ok-ness, the ok arm computes both
   sides concretely and `cases h_dval` substitutes dOut away.
   Corollary discovered en route: the STATEMENT run lemma needs only
   the dst-lowering's VALUE (ok-ness), not its cleanup — so
   `h_stmtRun` is available BEFORE the mother lemma and the
   code-inclusion argument needs no StateIncr dance at all (`exact
   h_code` closes the inner layer by defeq).
2. NEW mother-lemma conjunct: `ρa resolved.allocBase = some
   resolved.allocBase`. The stored-pointer MemValSim base component
   needs it, and `h_drange` cannot supply it when the referent is
   zero-sized (`&mut ()` through a chain — allocSize can be 0). All
   three induction cases had it on hand (the local's h_ra; the loaded
   value's MemValSim base, twice); appended after the register-frame
   conjunct, consumers add a `-`.

## Potholes (recurring)
subst roulette again (h_deq direction flipped so dOut' dies, not
dOut); the error arms of the case-split needed an explicit
`simp at h_dval` closer.

## State
All targets green; units 17/17 + 62/62 (d49); corpus 82/123 (0 fail);
axiom audit exact at 4. Deref-leaf family DONE. Next classes:
proj-topped srcs/dsts over non-local bases (`(*p).f := &x`,
`y := copy (*p).f`), proj-of-proj normalization, unbound roots.
