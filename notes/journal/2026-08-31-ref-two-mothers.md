# the two-mother leaf: `*D := &kind (*P).f`

Closed 2026-08-31. A chain SOURCE under a chain DESTINATION — the one
ref shape needing two `ptrChain_lowering_sim` applications in a single
statement. 453 lines, and it went through FIRST TRY.

## [FACT] the order is forced, and it is Rust's

`doAssign` runs the rhs before the destination resolution (mirlite), and
`compileStmtChecked`'s non-local arm runs `compileRExprPreChecked`
before `placeToRegChecked Mut dst`. So:

1. MOTHER 1 lowers the SOURCE chain at `kind` from the prefix state.
   `placeToRegChecked`'s deref arm ignores its `kind` and recurses at
   `Shared`, which is why the same mother serves every `kind`.
2. one `Borrow kind prot mask (blockSize τ) sOut.reg (pathOffset f)`
   mints the reference; `sb_ref_respects_PermSim` transports it and
   EXTENDS ρt.
3. MOTHER 2 lowers the DESTINATION chain at `Mut` — from the
   post-`Borrow` state, under the extended ρt, with the mother's
   register-frame conjunct carrying the borrow temp across.
4. one `RStore` (BRIDGE 2, `writeThroughPtr_sim`) writes the reference
   through the loaded destination tag.

## [OBS] the empty cleanups are what made it cheap

Both `placeToRegChecked (.deref _)` calls return `cleanup := []`
(`placeToRegChecked_deref_cleanup`). Two consequences:

- No `Die` is emitted anywhere in the statement, so BRIDGE 1 is not
  needed — unlike every projected-destination leaf.
- The whole compiled shape is known BEFORE either mother lemma runs:
  `compileStmt_ref_derefdst_derefprojsrc_run` needs only the two VALUES
  (available from `placeToRegChecked_ok_of_placeInputsMapped` on the two
  `PlaceInputsMapped` facts) plus the destination's empty cleanup. With
  `h_stmtRun` in hand up front, each of the three code-inclusion
  obligations — source lowering, the `Borrow`'s state, destination
  lowering — is ONE `StateIncr` step off it.

  copy's two-mother leaves build those same three obligations with
  hand-assembled `StateIncr` towers spanning fifty lines each, because
  copy's source lowering leaves a cleanup and its run lemma therefore
  cannot be stated before the mother. If a future two-mother shape has
  empty cleanups, get `h_stmtRun` first — it collapses the bookkeeping.

## [FACT] both chains must be flattened at the call site

`ref_proj_src_deref_simulation`'s `| deref pp =>` arm carries no spine
hypothesis for either place, so it flattens both: the destination with
`stepStmt_assign_dstderef_flatten` +
`compileStmt_assign_derefdst_flatten_run/_value`, the source with
`stepStmt_assign_refsrc_anyflatten` +
`compileStmt_ref_srcflatten_deref_run/_value` (added here, the third
instantiation of the deref-destination congruence). Both spines are then
`PtrChain_flatten_deref`.

## what is left

ONE site: `(*p).g := &kind _`, a projected destination over a deref
base. Same two-mother architecture, but the projection at nonzero offset
ALSO mints an interior `Borrow(Mut)` whose `Die` BRIDGE 1 must collapse
— the conjunction this leaf was spared. Donors:
`ref_derefdst_derefprojsrc_simulation` for the two mothers,
`ref_proj{zero,offset}_derefsrc_simulation` for the projection.

Witness d89, teeth confirmed (ub at statement 8 when the source is
retargeted to the field `r` holds).
