# `refSlice` at a projected source: a `Mut` retag pops the projection's borrow

[SUPERSEDED 2026-09-16 → split-the-mint-out-of-the-bracket.md]
[SUPERSEDED 2026-09-14 → die-is-permissive-when-not-on-top.md, itself reverted]
The DIVERGENCE described here is fixed. The user's call: make `Die` a
no-op when its tag is no longer on top, rather than change the lowering
or the source model. `Die` retires compiler scaffolding and has no Rust
counterpart, so when an intervening access has already popped the
temporary there is nothing left to retire. Both machines now run the
witness clean, and its test flipped from pinning `ub 3` to
`expectDiff … .ok`.

**Why I was misled:** I read the strict "must be on top" check as part of
the Stacked Borrows model and looked for ways to avoid tripping it — a
lowering change or a source-model change, both large. It was a
self-check on the compiler's own bracketing, and the two options I
weighed were both more invasive than deleting it.

What survives: the diagnosis (a minting rvalue holds a cell-borrow across
its mint), the witness, and the `Raw`/`Shared` vs `Mut` asymmetry — and,
after the 2026-09-16 revert, the [OPEN] block's premise that the fix must
be an ISA or lowering change. It was right; the 2026-09-14 line above,
which called it wrong, is the part that did not hold. The fix taken is
neither (a) nor (b) below but a third option: SPLIT `BorrowRest` so the
mint leaves the bracket, keeping every borrow where it is.

One correction to the analysis below: "`Raw` and `Shared` retags do not
diverge … inserted directly ABOVE THE GRANTING ITEM" is true only of
`Raw true`, the kind actually probed. `Shared` and `Raw false` CONS on
top of a read that merely disables, so they BURY the temporary — a
different failure, invisible to any verdict test. See
split-the-mint-out-of-the-bracket.md.

Load this for the diagnosis and the witness; load
split-the-mint-out-of-the-bracket.md for the resolution.

[FACT, 2026-09-14] **`refSlice`'s lowering is NOT an outlier.** It lowers
its source place shared and emits one `Rhs.BorrowRest`, so
`readRhsShape_refSlice` holds by `rfl` and it is a read-then-store member
like copy, the two integer-pointer casts, `ptrOffset` and `ptrCast`. The
machine step (`runN_Assgn_BorrowRest_step`) and the chain-class read
package are proved. It is the ONLY member that mints, which is why
`ReadPkgLowered`/`ReadPkgProjOffset` were generalised to let the tag
renaming grow.
→ src/obseq3/compile.lean, the `.refSlice` arm
→ src/obseq3/proof/ptrarith.lean

[FACT, 2026-09-14] **What blocks it is a compiler bug.** A projected
source at NONZERO offset lowers to `Borrow(Shared)` at the field offset,
the instruction, then a cleanup `Die`. So the projection's borrow is
alive across the mint. A `Mut` slice retag performs a WRITE access
through the LOADED pointer's tag; if that pointer's range covers the cell
it is itself stored in, the write pops everything above the granting item
— the projection borrow included — and `dieCellContent` then fails,
because it requires its tag to be on TOP:

    | item :: below => if item.tag == tag then … else .error "top of stack is …"

mirlite has no projection borrow at all, so it runs clean.
→ src/obseq3/sb.lean, `dieCellContent`

[FACT, 2026-09-14] **Minimal witness, and it is pinned.**

    (t.0) = 1
    p     = &raw mut t                       -- tag grants over the whole block
    (*p).1 = ptrCast p                       -- park it in t.1, writing THROUGH p
    q     = refSlice Mut ((*p).1)            -- range covers t.1's own cell

    mirlite: ok      oseair: ub at the last statement

`rs_known_divergence_projsrc_mut` (compile_tests.lean) asserts exactly
this, with teeth — flipping the expectation makes it fail, verified — so
fixing the lowering breaks the test loudly.

[FACT, 2026-09-14] **`Raw` and `Shared` retags do not diverge.** They
access for READ, which does not pop shared items, and the new item is
inserted directly ABOVE THE GRANTING ITEM rather than on top — so the
projection borrow stays on top and the `Die` succeeds. Probed both ways:
`Raw true` runs `ok`/`ok`, `Mut` runs `ok`/`ub`. The bug is narrow.

[OPEN] The fix is an ISA or lowering change, not a proof. A minting
rvalue must not hold a cell-borrow across its mint, which means either
(a) an offset operand on `Rhs.BorrowRest` so a projected source needs no
borrow — mirroring what `Rhs.Borrow` already does for `ref`, or (b)
generalising `readRhsPre`'s `mk` to take the projection offset, which
would let copy, the casts, `ptrOffset` and `ptrCast` all drop their
`Borrow`/`Die` at projected sources and retire BRIDGE 1S with them. (b)
is the bigger prize and the bigger change. See loose-ends/parked.md.

## Why this matters

`refSlice` is the last rvalue outside `compile_correct`, and it is
outside for a reason that a proof cannot fix. Do not spend effort on
`pkgProjOffset` for it: the package is FALSE as the compiler stands.

## See also

- ptrcast-was-the-last-memcpy-caller.md
- one-leaf-per-destination-shape.md
- stacked-borrows-does-not-subsume-bounds-checks.md
