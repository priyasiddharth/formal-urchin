# Keystone closed: sb_ref_use_die_cancels is a theorem (audit 8 → 7)

[FACT] BRIDGE 1 is proved (`src/obseq3/proof/keystone.lean`, ~560 lines,
zero sorries): for a Mut retag, `sb_ref` then a write through the fresh
tag then `sb_die` yields exactly the `StackMap`/`exposed`/`protFrames`
of the bare parent `sb_write`, with only `NextTag ≤` — the fact that
justifies the compiler's Borrow/use/Die place-lowering scheme and that
obseq2's const_write sorry silently depended on. Two side conditions,
both invariants of reachable states (the future WF conjunct): the fresh
tag is not the wildcard and not protected.

## Proof architecture (the reusable part)

[FACT] Every per-cell SB op involved is a content-driven rewrite of its
own cell: `StackMap.set a v` with `v` a function of `find? a` and the
constant `(protFrames, exposed)`. This was made literal by a
behavior-preserving `sb.lean` refactor (suite re-verified identical):
`writeCellContent`/`dieCellContent` factored out of `writeCell`/`sb_die`,
`resolveWildcardIn`/`firstProtectedIn`/`isProtectedIn` taking the field
values, and `sb_ref`'s nested `let rec go` promoted to a top-level
`foldCellsIdx` (nested let-recs are unaddressable in proofs).

[FACT] Fold normal form: a fold of such ops over the distinct cells
`[addr, addr+len)` equals a `setChain` (left-to-right `SB.set`s) of
per-cell entries (`foldCellsIdx_ok_inv` — inversion with the entries
extracted via `Exists.choose`; `foldCells_ok_of_cells` — construction).
Because `SB.set` is move-to-front, `setChain`s only collapse under the
explicit normal form `entries.reverse ++ filter (keys ∉) original`
(`setChain_normal`, keys nodup) — pointwise equality is NOT enough since
`PermSim` compares raw stack-map lists. `setChain_override` (same key
sequence ⇒ last chain wins, same layout) then collapses the target's
three phases (ref-fold, write-through-top, die) onto the source's single
write phase entry-for-entry: the ref phase writes `MutRef t' :: wⱼ`, the
write-through-top phase rewrites it unchanged
(`writeCellContent_top_mutref` — the fresh Unique is top, so the pop-set
is empty), the die phase pops back to `wⱼ` (`dieCellContent_top`).

## Lean potholes worth remembering

[EMP] (Lean 4.28, this repo) `omega` does NOT see through the `Word`/
`Tag` abbrevs of Nat — goals like `addr + j ≠ addr + i` or
`s.NextTag ≤ s.NextTag + 1` fail with "no usable constraints"; use
`Nat.add_left_cancel`/`Nat.le_succ` term proofs. Pure-Nat-typed index
goals are fine.
[EMP] Do-blocks of the shape `let x ← e; pure (f x)` compile to
`Functor.map`, not `bind` — hypothesis destructuring must simp
`[Functor.map, Except.map]`.
[EMP] `cases h : scrutinee` on a match whose patterns REBIND the same
name leaves the inner occurrence untouched (shadowing) — rewrite the
scrutinee by equation (`simp only [h]`) instead of substituting.
[EMP] Lemma-application arguments elaborate before later arguments
unify the head's implicit `op` — pass `(op := ...)` explicitly when a
`fun ...` proof argument needs the op concrete.
[EMP] `induction h : e generalizing x` silently loses the measure
equation in this setup; self-recursive theorems with
`termination_by len - i` are the robust pattern for interval folds.

**References:** proof/compiler.lean (audit updated: 7 sorries, closing
order 4→5→7→1→2→6→3), 2026-08-15-obseq3-proof-skeleton.md.
