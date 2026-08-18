# All common.lean sorries closed: bridges 2 and 3 + the §E glue (audit 7 → 4)

[OBS 2026-08-18] Three closures in one increment; only the four
leaf-side sorries remain (const_write ×2, copy, ref).

**§E glue** (`placeToRegChecked_emits_preserves_mem`): the earlier
combinator-unification failure dissolved once the binds got explicit
`(m := ...)` arguments and the local case used `simp only + split`
(the same shape §D's proved lemmas already used). Fully mechanical, as
predicted.

**BRIDGE 2** (`writeThroughPtr_sim`, common §G): exactly as scoped in
the "will it use the discussed lemmas" assessment — no fold/setChain
machinery needed, because `SourceMemSim` is pointwise (unlike PermSim's
raw-list comparison). New pieces: `ListRel.length_eq`,
`SourceMemSim.write_extend` (single cell, the obseq2 proof's core), and
`SourceMemSim.writeWordSeq_extend` (paired-list induction). The main
proof destructures `writeResolvedPlace`, transports the bounds check
through `ListRel.length_eq` (no omega — Word), and reads the target
`useMut` off `PlaceRegReady`. Statement generalized over the
`invalidMsg` so RStore call sites can reuse it.

**BRIDGE 3** (`sb_write_respects_PermSim`, new
`proof/permsim_transport.lean`, ~560 lines): the transport family from
the refactor assessment, built exactly as planned there:
- generic `ListRel` transports (append/reverse/take/takeWhile/filter/
  find?_none, all pred-transport parameterized);
- `TagRenameWF.beq_eq` — the injectivity+functionality → beq-equality
  workhorse; `ItemSim.tag_rel/grantsWrite_eq/isSrw_eq` (constructor
  preservation doing the real work — `Item.isSrw` was named in sb.lean
  precisely so these could be stated, replacing an anonymous lambda);
- `contains`/`isProtectedIn`/`firstProtectedIn` transports;
- `splitStack_some_transport` (paired-stack recursion);
- `writeCellContent_transport` — the meaty one; the SRW-grouping case
  transports `reverse ∘ takeWhile isSrw` and the length-arithmetic
  `take`, which is exactly why `ItemSim` was designed
  constructor-preserving: grouping structure transports for free;
- relational `SB.set`/`setChain` respects-lemmas + the keystone's new
  `foldCells_ok_inv`/`writeCell_content_form` (the extract-on-demand
  wrappers, now real).

[FACT] Scope: bridge 3 assumes the acting tag is non-wildcard.
Justified for the proof core — `fromExposed` is not a core rvalue, so
core programs cannot mint wildcard pointers; `resolveWildcardIn`
transport is deferred with the non-core constructs.

[EMP] (Lean 4.28) two more recurring potholes for the collection:
`subst`/`obtain ⟨rfl,…⟩` on `x' = x` with both sides local eliminates
an unpredictable side — rewrite the goal with `h.1` instead when later
script references a name; and `Nat.eq_of_beq_eq_true` does not unify
against `==` on Nat-abbrevs (`Tag`) — use the `LawfulBEq` generic
`eq_of_beq`.

**References:** proof/compiler.lean audit (remaining order 4→1→2→3),
2026-08-18-keystone-refactor-assessment.md (the plan this executed),
2026-08-15-keystone-closed.md.
