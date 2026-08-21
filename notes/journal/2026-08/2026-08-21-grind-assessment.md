# grind assessment for permsim_transport-style proofs

[EMP] (Lean 4.28, trialed against d0d5719 on copies of real lemmas)
`grind` collapses this file's SMALL AND MID case-bash/logic/arith
lemmas to one-liners, but not the large transport assemblies:

PASSES (with size of the manual original):
- `TagRenameWF.beq_eq` (22 lines → `grind [TagRenameWF]`)
- `TagRenameWF.extend` (~25 lines → `grind [TagRenameWF, TagRenameBound,
  TagRenameMap.extend]`) — including the injectivity/arith reasoning
- `TagRenameBound.extend` / `.extend_incr` (arith + case split, 1-liners)
- `refCellContent_none_error` (13 lines → `grind [refCellContent.eq_def]`,
  no manual `cases kind` needed)
- `ItemSim.mono`, `ItemSim.grantsWrite_eq`, `ItemSim.disable_map` after
  `cases i <;> cases i'`
- induction LEAVES: `ListRel.append`, `TagListSim.contains_eq` (grind
  does not do induction; `induction … <;> grind [ListRel, …]` works)

KEY TRICK: for defs pattern-matching on a Bool inside a constructor
(`Item.grantsWrite`, `Item.poppedByRead`, `refCellContent`'s Raw arm),
pass `foo.eq_def` instead of `foo` — grind then sees the match term and
case-splits it; with plain `foo` it gets conditional equations and
stalls on the un-split Bool.

FAILS (keep manual):
- monadic bind/pure unfolding goals (the `sb_ref_unfold` h_tail shape):
  grind does not reduce do-desugared `bind`/record-eta even with
  `[bind, Except.bind, pure, Except.pure]`
- ∃-witness transport assemblies (`insertAboveContent_transport` given
  `splitStack_some_transport` in the lemma list): grind will not
  instantiate the helper and build the witness chain
- (untried, surely out of scope) the fold characterizations and the
  choose-based top-level members

COST: ~1.1s per grind call here (vs ms for the manual simp/cases) —
irrelevant per lemma, noticeable only if applied to dozens.

Verdict: worth using in NEW proofs for the small-lemma tier (tag/beq/
bound algebra, constructor case-bashes, induction leaves); refactoring
the existing green file is optional churn — the wins are in future
files (copy/ref leaves will need many small helper lemmas of exactly
the shapes grind closes).
