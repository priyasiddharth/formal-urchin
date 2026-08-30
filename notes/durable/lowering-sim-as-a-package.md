# Name the mother lemma's conclusion; gate leaves on the PACKAGE

[FACT, 2026-08-30] A copy leaf's only use of `PtrChain src` is to call
`ptrChain_lowering_sim` and consume its twenty conjuncts. Naming that
conclusion — `LoweringSim ρa ρt s_mir compProg p`, and its
rename-polymorphic form `LoweringSimAny compProg p` — lets a leaf take
the PACKAGE as a hypothesis instead of the chain predicate, and then
ANY source shape that can produce a package plugs in unchanged.

    theorem PtrChain.loweringSimAny  : PtrChain p → LoweringSimAny compProg p
    theorem LoweringSimAny.projZero  : (B not proj) → pathOffset spath = 0 →
                                       LoweringSimAny compProg B →
                                       LoweringSimAny compProg (.proj B spath)

`projZero` is ~35 lines: at zero offset the projection contributes a
`+ 0` on the resolved address (which collapses) and a `pure` on the
compiled side (which `placeToRegChecked_proj_zero_run/_value` make
invisible), so every conjunct transports by one rewrite.

**What this bought.** Four leaves — the two projected-destination
leaves and the two regime-B fresh-root leaves — accept a zero-offset
proj-topped source with NO change beyond swapping one hypothesis. The
alternative, which the parked note had prescribed, was writing two more
~650-line leaves.

**The companion fact.** A leaf needs
`(run (placeToRegChecked kind src) cs).placeRegMap = cs.placeRegMap`
BEFORE it may invoke the package (it feeds the value fragment, which
feeds the code-inclusion hypothesis, which the package demands). So it
cannot come out of the package — it is a second hypothesis,
`h_sprm0`, supplied by `PtrChain.placeToRegChecked_placeRegMap` or by
`projZero_placeRegMap`.

**Where it stops.** At NONZERO offset the source projection emits a
`Borrow` and leaves a cleanup `Die`, so `placeOut.result.cleanup = []`
— a conjunct of the package — is FALSE, and the extra instruction plus
its BRIDGE 1S cancellation are the consumer's business, not the
lowering's. That case still needs a real leaf. The package boundary is
exactly "lowerings that emit no cleanup".

Related: [[chain-leaves-gate-on-the-whole-place]] (what a leaf gates
on), [[transport-compiled-states-by-defeq]] (the spelling discipline
these refactors lean on).
