# sb_ref transport closed: the ρt-growing BRIDGE 3 member

[FACT] `sb_ref_respects_PermSim` (permsim_transport.lean, commit
d0d5719) completes the BRIDGE 3 transport family — write/read/die/ref
are all theorems now. The ref member is the only ρt-GROWING one: both
machines mint their own fresh tag (counters only satisfy `≤`, so the
values differ), and the results are `PermSim`-related under
`TagRenameMap.extend ρt src.NextTag tgt.NextTag`. Injectivity of the
extension needs the new `TagRenameBound ρt nS nT` predicate (every
mapped pair strictly below both counters); the lemma consumes it at the
current counters and RETURNS it re-established at the bumped ones, so
consumers can thread it as an invariant. Also returned: `TagRenameWF`
of the extension, `TagRenameIncr`, and both NextTag bump equations.

[FACT] Proof architecture: `sb_ref` is `foldCellsIdx` (per-cell op sees
its index, for the freeze mask), so keystone gained
`foldCellsIdx_ok_of_cells`, the forward mate of the existing inversion.
The per-kind cell op is lifted to `refCellOp` with an Option-consuming
content form `refCellContent` (Mut = write+push; Shared/Raw-false =
masked insertAbove | read+push; Raw-true = insertAbove; TwoPhase =
read+insertAbove), plus `insertAboveContent(_transport)` at the stack
level — the wildcard branch is eliminated up front by the non-wildcard
side condition, so the content function needs no exposed set. The
whole per-cell transport runs directly at the EXTENDED map (via
`PermSim.rename_mono` up front), so the fresh item's `ItemSim` is just
`extend_self` and no per-cell mono step is needed.

[EMP] (Lean 4.28, verified against d0d5719) potholes from this proof:
- `simp only [h]` where `h : f args = .ok u` can report "no progress"
  on goals where the same `rw [h]` succeeds (scrutinee under a compiled
  matcher application). Reach for `rw` first when rewriting a match
  scrutinee by an equation.
- `Exists.choose`-terms poison rewrite motives: any goal containing
  `(h_pkg j).choose` cannot be rewritten at terms occurring in
  `h_pkg`'s TYPE (e.g. `tgt.protFrames`) — "motive is not type
  correct". Two working antidotes: (a) split fold hypotheses into
  separate find?/content functions so callers pass lambdas checked by
  defeq instead of rewriting (`foldCellsIdx_ok_of_cells` takes V and W);
  (b) repackage the choose-built function through an `∃ W'', … ∧ …`
  obtain, making it opaque before any goal rewriting.
- Record-update syntax is line-sensitive: a field value starting on the
  line AFTER `f :=` at a column ≤ the field name breaks the parser
  ("unexpected identifier; expected '}'"). Keep `f := value-head` on
  one line, or nest `{ { x with a := … } with b := … }`.
- `cases h : e` substitutes `e`'s occurrences in the goal — after
  `cases h_pfT : tgt.protFrames with | cons …`, a match on the record's
  protFrames reduces DEFINITIONALLY and the conjunct closes by `rfl`;
  no goal rewriting needed at all.
- `Except.noConfusion h` at `h : .error _ = .ok _` hits universe-mvar
  trouble as a bare `exact`; `simp at h` (reduceCtorEq) is the robust
  spelling. `omega` also won't split an `∧`-goal of two linear facts.

[FACT] Consumer contract for the remaining sorries (audit now in
compiler.lean): obligations 2/3/5 lost their transport blocker; what
remains is (a) carrying `TagRenameBound ρt s_mir.perms.NextTag
s_osea.ap.NextTag` as a `CompilerInv` conjunct — it holds at init (ρt
maps only the wildcard, tag 0, and counters start at 1) and every
transport member preserves it — and (b) the per-leaf composition
(fragment execution + invariant rebuild, `MemValSim` transported along
`TagRenameIncr`).

Validated: full `lake build` green; suite pass 77 | fail 0 (117);
differential `--osea` matched 77 | mismatch 0 | skipped 0.
