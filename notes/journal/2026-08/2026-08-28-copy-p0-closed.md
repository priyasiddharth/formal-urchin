# 2026-08-28 (late) — Copy P0→L closed; the nonzero-offset countermodel

## What closed
`copy_proj_zero_simulation`: `dst := copy src.f` at ZERO offset, both
roots bound. `placeToRegChecked` returns the base register for a
zero-offset projection, so the fragment is the same single `Memcpy` as
L→L with the source bounds check discharged by TYPING
(`PathTo.offset_add_size_le` + `h_off`), exactly C0's widening of
regime A. Dispatcher wired (`by_cases pathOffset ff = 0`); d32 covers
it differentially (45/45). Audit stays at 4; axiom audit green.

## What did NOT close, and why it CANNOT as stated
Nonzero offset lowers to `[Borrow(Shared); Memcpy; Die]`. Memcpy is
ATOMIC: read-through-the-fresh-tag, then the dst `useMut`, in one
instruction — so the foreign dst op lands BETWEEN BRIDGE 1S's read and
die. That is not just a missing lemma:

**Countermodel.** `CompilerInv` has no separation conjunct, so a junk
state may give two distinct bound locals overlapping blocks. Put
`[.. tagD .. tagS(top)]` on an overlap cell: the source's field read
(via tagS) and dst write (via tagD) both succeed, but the target's dst
`useMut` pops the fresh Shared minted by the Borrow, and `die` —
which demands its tag EXACTLY on top (`dieCellContent`) — errs. Target
UB where the source succeeded: the nonzero-offset leaf is FALSE
without a separation invariant. (Same-local aliasing is impossible —
a `PathTo τ τ` would need τ to contain itself — this is strictly a
junk-state artifact, like the pre-event-fix retag gap, but this time
the fix must be INVARIANT-side: separation is a property of reachable
states, not of any typed event.)

## The proposed fix (user decision, parked)
A separation conjunct: distinct bound locals occupy disjoint
`[addr, addr + blockSize)` blocks (likely alongside
`addr + blockSize ≤ watermark`). Cost: re-establish per leaf — trivial
(`exact h_sep`) everywhere env is unchanged; real work only in
alloc/fresh-dst regimes. Payoff: die↔useMut commute by cell
disjointness, unlocking nonzero-offset copy AND the non-local-dst
interleaved-keystone residuals in ref/const_write — the single
biggest remaining blocker class.

## State
Suite 82/123 (0 fail), differential 83/0/0 (d32 new), units 16/16 +
45/45. Leaf axioms: propext, Classical.choice, Quot.sound.

## Addendum: the countermodel is now a TEST (d33)
`d33_overlap_junk_copy_diverges` (compile_tests) pins the divergence
state-level, t16-style but on BOTH machines: forged overlap (y re-bound
inside tup's block), cell 1 stack `[Ref 4, MutRef 3, Own 1]`,
tup.tag := 4, y.tag := 3. Source `y := copy tup.1` succeeds; the
hand-written compiled fragment `[Borrow(Shared); Memcpy; Die]` runs
2 steps ok and errs at the Die with "sb-die". Teeth: un-forging the
overlap (y at its own block) makes the target SUCCEED and the test
throw — which is simultaneously the demonstration that a separation
invariant is exactly what the leaf is missing. Units 46/46.
(Process scars, again: ran the teeth against a stale olean the first
time — always rebuild before `lake env lean --run`; and a hasty
`git checkout <file>` destroyed the uncommitted test — reconstructed
from the session patch. Also a splice bug: `add` ending in the anchor
AND replacing with add+anchor doubles the anchor.)
