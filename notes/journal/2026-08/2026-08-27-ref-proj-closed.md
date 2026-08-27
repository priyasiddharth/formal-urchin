# Ref regime P→L closed; the deref-source blocker is a model gap

[FACT] `ref_proj_local_simulation`: `dst := &kind s.f` — any kind, any
offset (no zero/nonzero split: `placeToBorrowRegChecked`'s proj arm
always emits the borrow), any mask, both roots bound. The fragment is
L→L's two instructions with the field's offset in the `Borrow`.
`ref_place_residual` narrowed accordingly; audit stays 4.

[FACT] The `Borrow` bounds check is discharged by PURE TYPING:
`PathTo.offset_add_size_le` (syntax.lean) — a field's offset plus its
size fits its layout's size. This is the only closed regime whose bounds
obligation has NO semantic source: mirlite's `.ref` checks nothing, and
unlike the write regimes there is no `writeResolvedPlace` bounds check to
mirror. Also the first place `omega` worked directly in a while — every
atom was a genuine `Nat` (`layoutSizeList`), no `Word` projections.

[FACT] The stored pointer for `&s.f` covers the WHOLE base allocation
(mirlite stores `resolved.allocBase/allocSize`, not the field's range) —
provenance-style, matching the target's `Val.Ptr base (off) size`. The
`MemValSim` range obligation is therefore over the FULL block, and
`LocalBindingSim`'s block-domain conjunct (added for L→L) supplies it
directly. Second consumer; the conjunct is earning its keep.

[FACT] The DEREF-source shape (`L := &kind *p`) is blocked on a genuine
MODEL GAP, found by attempting it: the target `Borrow`'s check needs
`offset + blockSize τ ≤ size` for a LOADED pointer; `MemValSim` is
untyped (cells carry no pointee type, so no "well-sized for its use
type" fact can even be stated there); and mirlite's `.ref` has no bounds
check to transport. Miri DOES require a retag's range to be
dereferenceable — so mirlite is arguably MISSING a check, the same
finding-shape as the 2026-08-21 deref-read gap. Likely fix, if chosen:
add `resolved.addr + blockSize τ ≤ resolved.allocBase + allocSize` to
mirlite's `.ref` (and `.refSlice`?) — then source success implies the
target check via `MemValSim`'s `o' = o ∧ s' = s`. Model decision;
parked.

[FACT] The NON-LOCAL-destination shapes have a different blocker: the
dst `Borrow(Mut); …; Die` INTERLEAVES with the src retag (dst is lowered
before the rhs), so BRIDGE 1's three phases are separated by a foreign
op and need a commutation argument — a genuinely new proof pattern (the
ops act on provably disjoint cells: a cell holding `PtrL τ` cannot lie
inside a `τ`-typed source range, by finiteness of layouts — but proving
THAT is its own lemma).

Validation: units 15/15 + 42/42, suite pass 82 | fail 0 (123),
differential matched 82 | mismatch 0. `ref_proj_local_simulation`
axiom-clean; `offset_add_size_le` needs only propext/Quot.sound.

**References:** proof/compiler.lean (audit), syntax.lean,
2026-08-22-ref-ll-closed.md, loose-ends/parked.md.
