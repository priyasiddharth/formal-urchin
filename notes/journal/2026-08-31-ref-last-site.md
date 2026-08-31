# the last site: `(*p).g := &kind _`, and zero sorries

Closed 2026-08-31. `obseq3.proof.compile_correct` now rests on
`propext`, `Classical.choice` and `Quot.sound` alone;
`scripts/axiom_whitelist.txt` no longer lists `sorryAx`.

## [FACT] the destination is a chain, but `PtrChain` cannot say so

`.proj (.deref pp) g` is NOT a `PtrChain` — the grammar's `derefProj`
constructor is `.deref (.proj b f)`, a deref whose POINTER PLACE is a
projection, and `PtrChain.not_proj` says a chain never carries a
projection at the TOP. So the mother lemma does not apply to the
destination directly; it applies to the base `.deref pp`, and the
field offset is the leaf's own business. Two leaves, split on
`pathOffset g`:

- ZERO: `placeToRegChecked`'s projection arm returns `baseRes`
  unchanged, cleanup and all, so the destination supplies the
  `LoweringSim` PACKAGE via `LoweringSim.projZero` and the whole leaf
  is the two-mother assembly with the destination place respelled.
- NONZERO: the arm mints its OWN interior `Borrow(Mut)` at the field
  offset and retires it with a `Die`, neither of which mirlite
  performs. `sb_ref_use_die_cancels` (BRIDGE 1) collapses the triple to
  the parent's single `useMut`. This is the only leaf in obseq3 where
  two mother lemmas and BRIDGE 1 all appear in one statement.

## [FACT] one source-generic leaf beats four leaves

The dispatcher arm reaches this site with a GENERIC `src`, so the
naive shape was 2 (destination offset) x 2 (source local/deref) = four
leaves. Two facts collapse the source axis:

1. `ptrChain_lowering_sim` already covers a LOCAL source — `PtrChain`'s
   `base` constructor — with `n = 0` execution steps. A local source
   needs no special leaf, only the same mother at zero cost.
2. The only thing the leaf needs from the source's CONSTRUCTOR is the
   `placeToBorrowRegChecked` unfolding for `.proj sbase f`, and that is
   available from "sbase is not a projection" alone —
   `placeToBorrowRegChecked_proj_root_eq`, the borrow mirror of
   `placeToRegChecked_proj_root_eq`, whose side condition is exactly
   `PtrChain.not_proj`.

So both leaves take `PtrChain sbase` plus that unfolding as a
hypothesis and are generic in the source. The dispatcher then does the
case split ONCE, with `flatten_chainish`, and needs no source-shaped
leaves of its own.

**Rule:** before splitting a leaf on a place's constructor, check
whether the constructor is needed for anything but a definitional
unfolding. If not, take the unfolding as a hypothesis and pass
`PtrChain.not_proj` at the call site.

## [OBS] the wiring needs BOTH flattenings and the nil eta

`ref_proj_dst_simulation`'s `| deref pp =>` arm carries no spine
hypothesis for either place, so the arm flattens both:

- destination, `stepStmt_assign_dstflatten` +
  `compileStmt_assign_projderefdst_flatten_run/_value` (the deref-dst
  transfer generalized to a projection over a deref, by pure textual
  substitution — the proof never mentioned the destination's shape
  beyond `ensurePlaceRoot_flatten` and `placeToRegChecked_flatten_agree`);
- source, `stepStmt_assign_refsrc_anyflatten` +
  `compileStmt_ref_srcflatten_proj_run/_value`.

Then `flatten_chainish` splits the flattened source into "already a
chain" and "one projection over a chain". The first branch needs the
nil eta at a GENERAL chain base, which is why
`placeToBorrowRegChecked_nil_agree_local` had to join the deref form:
the local arm and the zero-offset projection arm emit the same
`Borrow`, and `placeToRegChecked_local_cleanup` supplies the `[]` that
makes their results equal.

## [OBS] the dependent match under `placeToRegChecked`'s local arm

`simp [placeToRegChecked, h]` does NOT reduce the local arm even with
`h : getPlaceInfo cs loc.idx = none` in hand: the arm is
`match h_lookup : getPlaceInfo cs loc.idx.1 with ...`, a DEPENDENT
match whose motive mentions the equation, so simp cannot rewrite under
it. The idiom that works is the one
`placeToRegChecked_local_existing` uses: `simp only [CheckedCompilerM.value,
CompilerM.value, placeToRegChecked]` then `split`. Recorded because the
first two attempts at `placeToBorrowRegChecked_nil_agree_local` both
died here.

## [OBS] a python `.index` on an under-indented needle can edit the wrong theorem

Reordering two `have`s inside a 650-line leaf, `s.index("      have h_regne2 :")`
matched INSIDE a more deeply indented line in a different theorem 14000
lines earlier, and the paired `.index` for the end marker then spanned
a huge region. `git diff --stat` showed the damage was four inserted
lines, not a deletion, but only by luck.

**Rule:** when editing one occurrence inside a known theorem, slice the
file to that theorem FIRST (`s.index(theorem_header)` .. next header)
and search within the slice. Never search the whole file for an
indentation-sensitive needle.
