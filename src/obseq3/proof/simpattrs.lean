import Lean

/-!
Simp-set registrations for the obseq3 proofs.

A simp attribute cannot be APPLIED in the file that registers it, so the
registration has to sit upstream of every use. This file exists only to
hold those declarations; the lemmas themselves are tagged in
`obseq3/proof/common.lean`.

* `csMonad` — the six `CheckedCompilerM` run/value projections
  (`run_bind`/`value_bind`, `run_lift`/`value_lift`,
  `run_pure`/`value_pure`). They are already global `@[simp]`, but every
  fragment proof uses `simp only`, which excludes the default set, so
  each of the 205 call sites listed all six by hand.
* `csRun` — the `CompilerM` plumbing a fragment lemma unfolds to reach
  the emitted instruction list (`CompilerM.run`/`value`, `emitM`,
  `freshReg`/`freshRegM`). 142 sites listed all five.
* `csCompile` — the two compiler entry points a fragment lemma unfolds
  before anything else (`compileStmtChecked`, `compileRExprPreChecked`).
  162 sites listed both.

* `mirPrep` / `mirAlloc` — the mirlite side of an assignment: resolving
  the destination place, and (for an unbound root) the allocation path.

* `csCleanup` — normalising an empty cleanup list to no instructions
  (`cleanupInstrs` with `List.map_nil` / `List.reverse_nil`). The two
  `List` lemmas are core `@[simp]`; as with `csMonad` they are listed by
  hand only because these proofs use `simp only`.
-/

register_simp_attr csMonad
register_simp_attr csRun
register_simp_attr csCompile
register_simp_attr mirPrep
register_simp_attr mirAlloc
register_simp_attr csCleanup
