# ref: the source-flattening transfer

Date: 2026-08-31
Tags: obseq3, ref, flattening, congruence, probe

## [FACT] the compiler already does it

`placeToBorrowRegChecked` (compile.lean:464) carries an explicit
reassociating arm for `.proj (.proj b q) p`, recursing on
`.proj b (q.append p)`, with the comment "`&mut s.1.0` must not route
through a wide Mut borrow of `s.1`". So the source-flattening transfer
is a theorem about code the compiler was already written to emit.

## [OBS] the probe that saved a wrong lemma

Before writing anything I reasoned that the transfer might be FALSE:
`placeToBorrowRegChecked (.proj b f)` lowers `b` with
`placeToRegChecked`, which for a projected `b` at nonzero offset emits
its own interior `Borrow` — so `&(s.f).h` looked like it should emit
two borrows where `&s.(f++h)` emits one.

A ten-line `#eval` probe settled it: for `(s.1).1` (offsets 2, 1) and
for `((s.1).1).1` (offsets 4, 2, 1), both spellings emit ONE `Borrow`,
at the summed offset (3, then 7), with the same result register and the
same cleanup. The reassociating arm fires before `placeToRegChecked` is
ever reached.

Cost: one scratch file and one `lake env lean` run, against a lemma
that would not have been provable. Worth doing whenever the compiled
shapes are in doubt — `.nextLabel` alone detects a difference in
instruction count, and `repr (... .code 0)` the actual instruction.

## [FACT] the congruence, and why a rewrite cannot work

The natural proof of the reassociation transfer rewrites the source
place inside
`CheckedCompilerM.value (compileStmtChecked (.assign dst (.ref .. src)))`.
Lean rejects it: "motive is not type correct". The value's type is
`Except String (ResultWithEvidence Unit (fun _ => StmtEvidence stmt))`,
so the result TYPE mentions the statement; changing the place changes
the type of the value being produced.

The fix is to factor every statement-level transfer through a
CONGRUENCE whose hypotheses are the two agreement facts about the
BORROW lowering:

```lean
compileStmt_ref_src_congr_local_run
  (h_agr : run (placeToBorrowRegChecked kind prot mask src1) cs' =
           run (placeToBorrowRegChecked kind prot mask src2) cs')
  (h_agv : (value ... src1 cs').map (·.result) = (value ... src2 cs').map (·.result))
```

Both the flatten transfer and the one-layer reassociation are then
one-line instantiations, and neither ever rewrites a `Place` underneath
`compileStmtChecked`. Reach for this shape whenever a transfer concerns
a subterm of an evidence-carrying compiled statement.

## [FACT] what closed

`ref_proj_src_local_simulation` mirrors `ref_proj_dst_simulation`
exactly — `induction sbase`, reassociate one layer per step on both
machines, base cases into the closed proj-over-local leaves
(`ref_proj_local_simulation` bound, `ref_fresh_projsrc_simulation`
fresh), `deref` to the residual. Both base leaves had to be
stmt0-threaded first, the same mechanical three-line change as before.

Residual sites 8 -> 7.

## state

Build green; 17/17 + 93/93; audit exact at ONE sorry. Pinned by d80
(`t := &mut s.1.0` spelled as a projection over a projection, with a
live disjoint borrow as teeth; control reports `ub`).

## [FACT] extending to a deref destination (same day)

`ref_proj_src_deref_simulation` reuses ALL the source-side theory
unchanged. The only new pieces are the congruence at the other base
state (`CompilerM.run (ensurePlaceRoot (Place.deref P)) cs` instead of
`(ensureLocalRegE dstLoc).run cs`), its two reassociation
instantiations, and the recursion skeleton — whose base case
additionally flattens the DESTINATION chain and composes both transfers
into the threaded `stmt0`.

So the recursion is parameterized by destination shape, and the source
theory is written once. A projected-destination instance would close
the two remaining class-1 sites the same way.

The one asymmetry: the deref congruence's VALUE direction needs a case
split the local one does not. With a local destination the compilation
cannot fail after the borrow lowering succeeds, so `exact ⟨_, rfl⟩`
closes it; with a deref destination `placeToRegChecked Mut (.deref P)`
can still fail, so its success has to be read off the hypothesis first.

Residual sites 7 -> 6; classes 4 -> 3. Pinned by d81.
