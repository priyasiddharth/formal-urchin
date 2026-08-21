# The ref leaf's core regime: the first ρt-growing statement simulation

[FACT] `ref_local_local_existing_simulation` (proof/ref.lean, commit
0d47351) proves `dl = &sl` end-to-end for two bound one-cell locals —
the first statement whose simulation GROWS ρt. Shape: the compiled
fragment is `Assgn tmp (Borrow kind prot mask len srcReg 0)` then
`RStore PTy tmp dstReg`; the borrow is matched by mirlite's `M.ref` via
`sb_ref_respects_PermSim` (which extends ρt at the fresh pair), the
store by BRIDGE 2 + `sb_write_respects_PermSim` fired at the EXTENDED
map, and the invariant is rebuilt with every relation transported along
`TagRenameIncr`. Axiom check: propext / Classical.choice / Quot.sound
only. `CompilerInv_step_ref` now delegates, leaving four named residual
regimes (REF-FRESH-DST, REF-NONLOCAL-DST, REF-NONLOCAL-SRC,
REF-WIDE-SRC).

[FACT] `TagRenameBound ρt s_mir.perms.NextTag s_osea.perms.NextTag` is
now a `CompilerInv` conjunct (commit 2ca77da) — the injectivity guard
the ref transport consumes. Preservation is cheap and total: `sb_write`
/`sb_read`/`sb_die` never touch a counter (`foldCells_NextTag` + the
three wrappers, plus `resolvePlaceAcc_NextTag` for the source's
resolution reads), and the ref transport returns the bound
re-established at the bumped counters. The spine mother lemma's
conclusion gained the matching target-counter equation.

[FACT] **Root fix — the opaque-BEq trap.** `deriving BEq` on the NESTED
inductives `TyVal`/`LayoutTy` (both carry a `List` payload) compiles to
a `partial`, i.e. OPAQUE, function: `#print obseq.instBEqTyVal.beq`
shows `opaque`. Consequence: `ty != ty` is irreducible — `rfl`,
`decide`, `decide +kernel`, `simp`, and `unfold` all fail (only
`native_decide` "works", via compiled code). Since oseair's
`Instr.RStore` guards on `srcTy != ty`, NO proof about a register store
could get past the type check; every prior proof happened to use
`CStore` (whose guard is a `Nat` length comparison) and so never hit it.
Both instances are now hand-written structurally in obseq/types.lean
with `beq_self`/`bne_self` simp lemmas. Behavior-neutral: interp tests
pass, conformance 77/117 pass 0 fail, differential 77/0/0.

[EMP] (Lean 4.28, verified against 0d47351) new potholes:
- Record-update syntax is column-sensitive in a way that produces
  baffling errors ("unexpected identifier; expected '}'", "Fields
  missing: …"): when `{ s with` is followed by fields on later lines,
  every field must start to the RIGHT of the `{`. Putting the first
  field on the `{ s with perms := …,` line and continuing at a lesser
  column breaks it. Safe shape: `{ s with` newline, fields indented.
- A failed elaboration LATER in a tactic block can make an EARLIER
  `omega` fail with a nonsense counterexample (atoms from unrelated
  hypotheses) — metavariable leakage. Do not trust an omega failure
  whose reported atoms do not appear in the goal; fix the downstream
  error first and re-check.
- `omega` still failed on `a + 0 + 0 < a + 1` in this context even
  after the downstream fixes, where the same goal is closed by
  `exact Nat.lt_succ_self _` (and by omega in a standalone file).
  Prefer the term proof for these trivial `Nat` steps.

[FACT] grind's role, as scoped by the 2026-08-21 assessment: every new
small lemma this session was closed by it — `TagRenameBound.mono`,
`TagRenameWF.extend`, `TagRenameBound.extend*`, `foldCells_NextTag`'s
per-cell obligations (`grind [writeCell.eq_def]`, `[readCell.eq_def]`),
the `resolvePlaceAcc` local case, and the fresh-tag non-wildcardness
side condition (`grind [wildcardTag]`). The big assemblies stayed
manual, exactly as predicted.
