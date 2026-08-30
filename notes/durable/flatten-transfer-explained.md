# What a "flatten transfer" is

[FACT, 2026-09-01] A *flatten transfer* is the lemma pair that lets a
simulation proof about the FLATTENED spelling of a statement stand in
for the statement the program actually contains.

**The concrete instance** (d50): the program says

    *(s.f.g) := 9        -- dst = .deref (.proj (.proj s f) g)

The chain leaf only speaks the canonical spelling where consecutive
fields compose:

    *(s.(f.g)) := 9      -- dst = .deref (.proj s (f.append g))

Same behavior, different syntax tree. The transfer has two halves,
one per machine:

- **Source half** — the interpreter cannot tell the spellings apart:
  `resolvePlaceAcc_flatten`, `resolvePlace?_flatten`,
  `preparePlaceAssign_flatten` (spine.lean) are equalities, so the
  leaf's source hypotheses are obtained from the program's actual step
  by rewriting.
- **Compiled half** — the compiler cannot either:
  `placeToRegChecked_flatten_agree` gives run-equality (identical
  instructions, registers, compiler state) and result-equality (via
  `Except.map (·.result)` — only the evidence wrappers differ);
  lifted per statement shape, e.g. `compileStmt_derefdst_flatten_run`.

**The plumbing** is the stmt0 threading the leaves already carry: a
leaf takes "the program's statement `stmt0` + a proof its compilation
EQUALS my canonical statement's." Dispatchers used to pass identity
transfers (`fun _ => rfl`); with flattening the canonical statement is
the flattened one and the transfers are the flatten lemmas. The leaf
never knows the difference.

**Why it kills residuals**: pre-transfer, a proj-of-proj spelling
failed the `PtrChain` gate and fell into a sorried fallback. The
dispatcher now normalizes FIRST, and `PtrChain_flatten_deref` says a
flattened deref place is ALWAYS a chain — so the failing case is
unreachable and the fallback gets DELETED (how
`const_write_deref_deep_residual` died, 4 → 3 sorries).

**How to apply**: to extend to a new statement shape (copy src, ref
src/dst), only the statement-level run/value pair is new — the
place-level machinery is shared. Pattern: instantiate
`placeToRegChecked_flatten_agree` at the POST-ensure compiler state,
never unfold `CompilerM.run` in the closing simp (atom split), and
normalize `flattenPlace (p.deref)` ↔ `(flattenPlace p).deref`
spellings with a `show ... from rfl` rewrite first.

**Refs**: [[chain-leaves-gate-on-the-whole-place]],
journal 2026-09-01-first-residual-dies.md, spine.lean (flattenPlace,
flatten_chainish, PtrChain_flatten_deref),
const_write.lean (compileStmt_derefdst_flatten_run/_value).

When a statement lowers TWO places, shape the transfer per
[[flatten-one-place-at-a-time]] — one place per lemma, composed.
