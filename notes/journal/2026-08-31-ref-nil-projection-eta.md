# the nil-projection eta: `*P` and `(*P).nil`

[FACT] `flattenPlace` never introduces an empty projection — `projInto b
.nil` is `.proj b .nil`, and flattening a `.deref` produces
`.deref (flattenPlace p)`, never a projection. So flattening CANNOT
relate the two spellings of a deref source, and the leaves that take a
`.proj (.deref P) f` source could not be reached from a `src = .deref P`
site. That is the whole reason `t.g := &kind *p` was a separate residual
site from `t.g := &kind (*p).f`.

[FACT] They are nonetheless the same place on both machines.

Source side: `resolvePlaceAcc` of `.proj p path` adds `PathTo.offset
path` to the resolved address, and `PathTo.offset .nil` is `0`, so
`resolvePlaceAcc_nil` is a two-line case split. The `.ref` rhs sees its
source ONLY through `resolvePlaceAcc` (mirlite_semantics.lean), so
`stepStmt_assign_refsrc_nil` follows by the same three-line recipe as
`stepStmt_assign_refsrc_anyflatten`.

Compiled side: `placeToBorrowRegChecked`'s projection arm calls
`placeToRegChecked kind base`, and for `base = .deref P` that arm
IGNORES `kind` and recurses with `RefKind.Shared`, emits the `Load` and
the pointer cleanup, and returns `cleanup := []`. The projection arm
then mints one `Borrow` at `pathOffset .nil = 0` with cleanup
`[] ++ [(tmp, blockSize τ)]`. The deref arm of
`placeToBorrowRegChecked` emits exactly that sequence directly. Same
instructions, same register counter, same result — so
`placeToBorrowRegChecked_nil_agree` is one `simp` after a case split on
the shared prefix `CheckedCompilerM.value (placeToRegChecked
RefKind.Shared P) cs`.

[OBS] The case split is the whole proof. Without it `simp` leaves a goal
whose two sides are a `match` over that prefix, nested differently — the
projection arm scrutinizes the deref's RESULT while the deref arm
scrutinizes the pointer's. `Except.map` must also be in the simp set:
the two sides' `Except` carry different evidence types, so the value
halves are not closed by `rfl` until `map` is unfolded.

[OBS] The eta pays twice, and differently.

- Under a PROJECTED destination it CLOSES `t.g := &kind *p`: the site
  routes into `ref_proj_src_projdst_simulation` with `sbase := .deref pp`
  and `f := .nil`, and lands in the four quadrants closed earlier today.
- Under a DEREF destination it MERGES rather than closes:
  `*chain := &kind *chain'` becomes `*chain := &kind (*chain').nil`,
  which is the OTHER residual site. Two sites become one, and closing
  the two-mother leaf will now close both spellings at once.

Residual sites 4 -> 2. Witness d88 covers the closure at the hardest
quadrant (unbound root, nonzero destination offset); its teeth retarget
the source from `*q` to `(*p).0`, which pops the live `r` and makes
statement 7 ub on both machines.
