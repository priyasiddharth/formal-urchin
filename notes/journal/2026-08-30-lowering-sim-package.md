# The source lowering becomes a package; half the last class falls out

[OBS 2026-08-30] A PROJ-TOPPED source at ZERO offset under a PROJECTED
destination is closed (d70/d71) — not by a new leaf, but by naming the
mother lemma's conclusion and gating the existing leaves on it. See
[[lowering-sim-as-a-package]] for the durable statement.

**What landed** (`spine.lean`, `copy.lean`):

- `LoweringSim ρa ρt s_mir compProg p` — the twenty-conjunct conclusion
  of `ptrChain_lowering_sim`, named; and `LoweringSimAny compProg p`,
  its rename-polymorphic form. The regime-B leaves need the polymorphic
  one: they run the source lowering at EXTENDED renames and a
  post-allocation state, which a package fixed at `ρa, ρt, s_mir`
  cannot serve. That was the one thing the first draft got wrong.
- `PtrChain.loweringSimAny` (two lines) and `LoweringSimAny.projZero`
  (~35 lines, compiled first try).
- `projZero_placeRegMap` — the companion fact, needed BEFORE the package
  may be invoked and therefore not derivable from it.
- Four leaves refactored to take `(h_slower, h_sprm0)` in place of
  `PtrChain src`: `copy_projdst_zero/offset_chainsrc_simulation` and
  `copy_projlocal_fresh_zero/offset_simulation`. Three edits each — the
  hypothesis, one `placeToRegChecked_placeRegMap` use, one
  `ptrChain_lowering_sim` call.
- The dispatcher's proj-dst arm now splits with `flatten_chainish`
  instead of `by_cases PtrChain`, and feeds the projZero package when
  the flattened source is a projection at zero offset.

**Why this was the right shape.** The parked recipe said to generalize
the projsrc leaves and splice BRIDGE 1S with BRIDGE 1 — two ~650-line
leaves. That is the correct recipe for the NONZERO-offset half, but at
zero offset the source projection is state-neutral and cleanup-free, so
there is nothing to splice: the existing leaves already do the whole
job once they stop asking for a chain. Checking WHY a hypothesis is
there, before writing the proof it seems to demand, has now paid twice
in two sessions (the other was the `.deref P` spelling).

## What remains — and the boundary that decides it

[FACT] A package must promise `placeOut.result.cleanup = []`. At
nonzero offset the source projection emits a `Borrow(Shared)` and
leaves a cleanup `Die`, so it cannot supply a package, and the extra
instruction plus its BRIDGE 1S cancellation belong to the consumer.
So the remaining half — proj-topped source at NONZERO offset under a
projected destination, at either destination offset — still needs two
real leaves. The enabling step is to generalize
`compileStmt_copy_projdst_zero/offset_run` from `h_sclean :
sOut.result.cleanup = []` to the general
`[Load] ++ cleanupInstrs sOut.result.cleanup` shape their `_value`
twins already use; then each leaf is
`copy_projdst_{zero,offset}_chainsrc_simulation` with
`copy_chaindst_projsrc_offset_simulation`'s BRIDGE 1S block spliced in
where the bare `Load` is.

**Validation:** full build green; 17/17 + 84/84; corpus 82 pass / 0 fail
/ 123, osea matched 82; audit exact at 2 sorries, `[axioms]` untouched.
