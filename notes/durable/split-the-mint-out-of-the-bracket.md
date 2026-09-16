# Split the mint out of the bracket, don't weaken `die`

Load this before touching `dieCellContent`, before adding a minting
rvalue, or when a `Borrow; use; Die` bracket will not collapse.

[FACT, 2026-09-16] **A projected place lowering emits a bracket, and
nothing that MINTS may run inside it.** `placeToRegChecked` at a nonzero
field offset emits `Borrow(Shared) base +off -> t`, the rvalue's
instruction, then `Die t`. The bracket collapses — BRIDGE 1S,
`sb_ref_read_die_cancels` — only because the temporary `t` is still on
TOP of every covered cell's stack when the `Die` runs. An access THROUGH
`t` leaves it there. A mint through some other tag does not:

    Mut         write pops everything above the parent   -> t GONE
    Shared      read DISABLES, then the item is CONSED   -> t BURIED
    Raw false   same                                     -> t BURIED
    Raw true    insertAbove, below t                     -> t on top

Only `Raw true` survives, which is why probing with it (2026-09-14)
wrongly suggested the problem was narrow.
→ src/obseq3/sb.lean, `refContent`; src/obseq3/proof/keystone.lean

[FACT, 2026-09-16] **The fix is in the LOWERING: give the rvalue a slot
after the cleanup.** `readRhsPre` (compile.lean, shared by all six
read-then-store rvalues) takes a `post : Register → List Instr` emitted
AFTER `cleanupInstrs`. Five members pass `fun _ => []`; `refSlice`
passes its mint. `Rhs.BorrowRest` — deref the cell and retag, one
instruction — became `Rhs.Load` + `Rhs.RetagRest`, the second taking the
loaded value from a register. Same three accesses, same order, same as
mirlite's `.refSlice`; only the `Die` moved earlier.
→ src/obseq3/compile.lean, `readRhsPre` and the `.refSlice` arm

[FACT, 2026-09-16] **The alternative — a permissive `die` — cost more
than it saved, and was reverted.** Removing the tag wherever it sits
makes the collapse unconditional, but turns `dieCellContent` from a
head match into a recursive search, so every lemma about it inducts.
Measured: +60 lines in sb.lean and +472 in keystone.lean
(`refContent_die_cons`, `refFold_die_comm` and twelve supporting
lemmas), against +12 for the new `Rhs` arm and +35 for its step lemma.
The user's call, and the arithmetic backs it.

**Why I was misled:** I argued the permissive die was worth it because
future minting rvalues would inherit the collapse for free. There are
none — `refSlice` was the last rvalue outside `CoreRhs`, and `ref`, the
only other minting rvalue, already avoids the problem with an offset
operand on `Rhs.Borrow`. A generality argument with an empty population.

[FACT, 2026-09-16] **`Rhs.Borrow` is still the only instruction in
oseair that forms a pointer offset**, and every place lowering goes
through it (compile.lean 430, 457, 476, 490). `Rhs.PtrOffset` appears
once, for the source-level `ptrOffset` rvalue. `RetagRest` adds no
arithmetic: it retags `(pb + po, ps - po)` off a loaded value. GEP is
still a borrow — the 2026-08-27 decision survives the change untouched,
which the options that move the ACCESS (`readRhsPre`'s `mk` taking the
offset; `PtrOffset` in `placeToRegChecked`) would not.

## Why this matters

`compile_correct` now covers every rvalue. The bracket discipline is
what keeps a future one cheap: put the mint in `post`, not in the
instruction the bracket wraps.

## See also

- die-is-permissive-when-not-on-top.md  (SUPERSEDED by this)
- refslice-projsrc-mut-pops-the-projection-borrow.md  (the diagnosis)
- one-leaf-per-destination-shape.md
