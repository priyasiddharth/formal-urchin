# A stale `.Ref` item is unobservable — which is why the suites could not
# have caught the weak `die`

Load this when a change is justified by a PROOF obligation rather than by
behaviour, or when asking whether the differential suite can vouch for a
Stacked Borrows change.

[FACT, 2026-09-14] **The situation.** With `die` merely a no-op when its
tag is not on top (the first version of the 2026-09-14 change), a
`Shared` or `Raw false` mint inside a projection's bracket leaves the
temporary BURIED — a read disables rather than removes, so the mint
pushes above it:

    target   Ref n :: Ref tmp :: r(X)
    mirlite  Ref n ::            r(X)

[FACT, 2026-09-14] **No access can tell the two apart.** `Item.Ref tmp`
is a frozen shared item for a tag nothing holds any more, and every way
the model inspects a stack is closed to it:

1. **Reads below it.** `readCellContent` takes
   `hit = above.filter (·.poppedByRead)`, and `poppedByRead` is true only
   for `MutRef`. `.Ref` is not in `hit`, and the disable-map leaves it
   unchanged. → src/obseq3/sb.lean, `readCellContent`
2. **Writes below it.** Everything above the granting item is discarded,
   the stale item with it. Same result either way.
3. **The SharedReadWrite run.** `grp = above.reverse.takeWhile isSrw`,
   and `isSrw` holds only of `RawPtr true`. A `.Ref` can neither lengthen
   nor shorten a run.
4. **Protectors.** This WOULD be observable — an extra entry in `rest`
   makes `firstProtectedIn` fire, so a write mirlite accepts would be UB
   on the target. It cannot happen: the projection's borrow is
   `Rhs.Borrow kind false []` (`borrowRhs`, compile.lean:331), `prot` is
   `false`, and `sb_ref` registers a tag in a protector frame only when
   `prot` is set.
5. **Wildcard resolution.** Also WOULD be observable — `resolveWildcardIn`
   scans top-down for an exposed granting tag, so a stale exposed item
   would win over the one below it. It cannot happen either: `exposed`
   grows only through `sb_expose`, which exposes the tag inside a pointer
   VALUE being cast to an integer, and a projection temporary lives in a
   register and never reaches memory.

[FACT, 2026-09-14] **So the weak `die` passed all four suites**, and no
verdict test could ever have failed. What it broke is `PermSim`:
`StackSim` is `ListRel ItemSim` over the WHOLE stack, so an extra element
is unrelatable and the simulation step for `Shared` and `Raw false` mints
does not typecheck. The strengthening to "remove the tag wherever it
sits" is driven by that obligation alone.

## Why this matters

This is the uncomfortable shape of change: correct, necessary, and
invisible to every test. The differential corpus cannot vouch for it, so
the proof is the only witness — which is an argument for widening
`CoreRhs`, since the unproved fragment has no such witness at all. See
one-leaf-per-destination-shape.md.

[OPEN] The argument above is a case analysis over the five ways the model
inspects a stack, not a theorem. The airtight form is: *an
`Item.Ref t` at ANY position, for a `t` that is unprotected, unexposed and
not the pivot, does not change what an access computes.* The three
content lemmas in keystone.lean prove exactly this for the LEADING
position (`readCellContent_cons_ref`, `insertAboveContent_cons_ref`,
`writeCellContent_cons_ref`); the general-position version needs an
induction on the prefix. See loose-ends/parked.md.

[OPEN] Scope. The five paths above are the PROVED fragment. `dealloc` is
not traced; if it inspects stack shape, a stale item could surface there.
It is outside `CoreStmt` so the theorem is unaffected, but it is where to
look first if the counterexample is ever hunted properly.

## See also

- die-is-permissive-when-not-on-top.md
- refslice-projsrc-mut-pops-the-projection-borrow.md
- one-leaf-per-destination-shape.md
