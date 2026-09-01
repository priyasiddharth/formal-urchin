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
-/

register_simp_attr csMonad
