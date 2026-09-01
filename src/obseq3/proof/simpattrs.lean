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
-/

register_simp_attr csMonad
register_simp_attr csRun
