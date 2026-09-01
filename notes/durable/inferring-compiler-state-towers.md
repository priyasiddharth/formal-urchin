# Inferring compiler-state towers by instance resolution

**Status:** durable. Landed 2026-09-01 (`6ac292f`, `4b58a27`).

A compiled statement's state is a *tower*: `emit`s interleaved with
`setNextReg` and `setPlaceInfo` over some base state. Two whole classes
of proof obligation are "walk that tower", and both were being done by
hand at ~150 sites each.

## The trick

Make the walk an instance-resolution problem, with the *answer* as an
`outParam`:

```lean
class EmitTower (cs : CompilerState) (base : Nat)
    (instrs : outParam (List Instr)) : Prop where
  out : EmittedAt cs base instrs
```

with one instance per tower constructor (`emit` peels and appends,
`setNextReg`/`setPlaceInfo` pass through, `nil` bottoms out). Resolution
runs outside-in on the state — which is an input — and assembles the
list on the way back out.

This works only because **`emit` and `setPlaceInfo` are plain `def`s**.
Their heads survive instance resolution, so the four instances never
overlap. Making either `@[reducible]` would break it.

## Where `nil` stops is the whole design

`emitTower_nil` fires at the first state that is not one of the three
recognised updates. In a leaf that calls the mother lemma
(`ptrChain_lowering_sim`), that state is
`CheckedCompilerM.run (placeToRegChecked …) csPrefix`.

So the inferred base is the mother's output `nextLabel` — which is
exactly what the `h_dpc`/`h_spc` the mother hands back already say — and
instruction indices come out **group-local**. That is the convention the
hand-written `h_code` blocks were already using, so `instrAt 0,1,2`
lines up with no arithmetic and every `h_q` is `rfl`.

A site is now:

```lean
have hFrag :=
  (CodeIncluded.of_stmt h_comp h_csAt h_stmt h_stmtOut).fragmentOf
    h_stmtRun h_dpc
have h_code1 : compProg s_mid.pc = some … := hFrag.instrAt 0 rfl rfl
```

The fragment's type is left to inference. A 3-instruction leaf went
59 → 15 lines.

## What does NOT need a class

`getPlaceInfo_emit` and `getPlaceInfo_setNextReg` are `rfl`, so chasing
the *place map* through a tower is pure defeq — `exact h_unmap loc' h`
closes it with no rewriting at all. Do not build machinery for it.

But do not sweep the existing `rw [getPlaceInfo_emit, …]` chains away
either: measured across 146 sites it buys only 95 lines (most chains are
one line), and ~20 of them are followed by a `rw` that *depends* on the
peeling having happened — dropping the chain leaves the later rewrite
with no redex to find.

## The exception the sweep cannot handle

The `h_code0` convention: the root `Alloc` of a **fresh destination** is
emitted *before* the mother lemma runs, so the whole-statement fragment
starts after it and cannot locate it. Those 10 sites stay hand-written.

See also [[transport-compiled-states-by-defeq]].
