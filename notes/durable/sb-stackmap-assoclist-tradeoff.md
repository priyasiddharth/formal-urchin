# StackMap as move-to-front AssocList — the recorded trade-off vs a canonical map

Load this when a proof needs REPRESENTATIONAL equality of `StackMap`s (not
just extensional), when `PermSim`'s positional key-order invariant bites,
or if a refactor of `SB` is ever on the table.

[FACT] `SB = List (Word × BorrowStack)` with `SB.set` move-to-front
(`(addr, v) :: filter (≠ addr)`, sb.lean). Consequence: the list's key
ORDER is a function of the access HISTORY, not of the contents — equal
contents do not give equal lists.

[FACT] Two places paid for that, both in the compiler-correctness proofs:
1. BRIDGE 1 (`sb_ref_use_die_cancels`, keystone.lean) concludes
   `s3.StackMap = sAcc.StackMap` — representational equality between the
   `Borrow; use; Die` history and the bare-parent-write history. That
   required the `setChain` normal-form theory (`setChain_normal`,
   `setChain_override`, ~150 lines) whose sole purpose is pinning
   move-to-front down: both histories normalize to the same list.
2. `PermSim` is POSITIONAL (`CellSim` demands `a' = a` at the same list
   index), so it silently carries "both machines' maps have identical key
   order". Every compiler-inserted op sequence (the target's internal
   Borrow/Die pairs) therefore owes a proof that it restores the EXACT
   list, not just its meaning — the keystone family is that proof for the
   sequences emitted so far, and any NEW compiler-inserted sequence
   inherits the obligation.

[FACT] What a canonical representation would change: with sorted-by-
address entries (or any canonical map), semantic equality = structural
equality; obligation class (1) largely evaporates and (2) becomes a
non-fact. What it would NOT change: the fold machinery
(`foldCells_ok_inv`/`_of_cells`, `chain`/`setChain`, the `*CellContent`
functions) is about the FOLD, not the list — it survives any
representation. The costs: a sorted list threads a sortedness invariant
through every op and lemma (we know what conjunct-threading costs);
`Std.TreeMap` outsources that but moves the fold characterizations onto
its lemma API, against this project's thin-dependency stance (`ListRel`
exists to avoid Mathlib).

[FACT] The Miri-faithful representation, if a refactor ever happens, is a
DENSE PER-ALLOCATION ARRAY: Miri keeps, per allocation, a Vec of per-byte
stacks indexed by offset. The analogue (`allocId ⇀ Array BorrowStack`) is
canonical by construction (no insertion order exists), O(1) at an offset,
and makes `sb_dealloc` a whole-allocation drop instead of a key filter.
Preferable to a sorted list on a redo. The switch is well-localized:
`SB.find?`/`SB.set` + the keystone normal-form section; nothing above the
`*CellContent` layer moves.

[OBS 2026-08-27] Verdict at current scale: a wash — ~150 lines paid once,
in one file, and the positional invariant has held. The balance flips if
(a) more compiler-inserted op sequences appear, each owing a
list-restoration proof, or (b) programs grow enough for O(n) `find?` to
matter. Neither is true today; do not refactor speculatively (see
[[dont-port-v1-proofs-reconstruct-in-v2]] for the precedent on
reconstruction costs).

**References:** src/obseq3/sb.lean (`SB.set`), proof/keystone.lean
(`setChain_normal`, BRIDGE 1), proof/common.lean (`PermSim`, `CellSim`),
journal/2026-08/2026-08-22-sb-ref-transport.md (the transport family
built on the fold-is-a-map view).
