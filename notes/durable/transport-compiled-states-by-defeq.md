# Compiled states: transport by DEFEQ, never by `rw`

[FACT, 2026-08-30] When a lemma's hypothesis and the goal both mention
the same compiled `CompilerState` but you wrote it one way and the
elaborator produced another, do NOT try to make the spellings match.
Transport the hypothesis across the difference with a type ascription
and let defeq do the work.

    -- h_d comes from `split`; its state is the elaborator's spelling
    have h_d' : CheckedCompilerM.value (placeToRegChecked kind Q)
        <the spelling in MY statement> = Except.ok o := h_d
    have h_oeq : dOut = o := Except.ok.inj (h_dval.symm.trans h_d')

and finish any residual shape difference in the goal with a trailing
`rfl`.

**Why the spellings diverge, unavoidably.** Three independent sources:

- `{ X with f := v }` in a *hypothesis* elaborates to
  `let __src := X; { f := v, g := __src.g, … }`, but the *goal* carries
  the flat field-by-field literal.
- `simp only [… emitM …]` normalizes a state to
  `emit { nextReg := (emit … [..]).nextReg + 1, … } [..]`, i.e. with
  projections OUT of an inner `emit`, whereas a hand-written statement
  naturally says `cs.nextReg + 1 + 1`.
- `cleanupInstrs` produces `[a] ++ [b]` where a hand-written list says
  `[a, b]`.

All three are definitional equalities and none is a rewrite `rw` can
find. Chasing them by adding `List.cons_append`, `emit` projection
lemmas, etc. to a simp set works only until the next lemma and makes
the proof text depend on simp's normal form.

**Corollary — the same trick sizes `StateIncr` chains.** A chain of
`StateIncr.trans (emit_state_incr _ _) …` more than about three steps
long leaves the intermediate instruction lists as metavariables, and
the unifier must then reconcile a partially-applied `emit` tower with a
record literal. It fails ("application type mismatch") or times out in
`isDefEq`. Split the chain at a state you can NAME, prove the prefix as
a ground term, and compose: two ground-vs-ground defeq checks instead
of one metavariable-laden unification.

Related: [[flatten-one-place-at-a-time]] (companion discipline — one
state spelling per proof, which this note does NOT replace: keep the
spelling stable *within* a proof, and use defeq transport only at the
boundary where a hypothesis meets a differently-elaborated goal).

## Addendum 2026-08-30 — prefer `csnorm` when you control both sides

[[csnorm-a-normal-form-for-compiler-states]] normalizes the spellings
outright, which is strictly better than transporting when both the
hypothesis and the goal are yours to rewrite. Defeq transport remains
the move when the target spelling is fixed by someone else's statement
(a fragment's `h_dval`, a mother lemma's `cs` argument), and it is still
what makes `have h' : <my spelling> := h` legal in the first place.
