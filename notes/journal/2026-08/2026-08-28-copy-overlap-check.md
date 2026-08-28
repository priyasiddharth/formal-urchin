# 2026-08-28 (night, cont. 3) — The overlap event check: d33 retired

## What changed (both machines, symmetric — user-approved)
- mirlite `doAssign`: for a `.copy` rhs, the resolved src range and the
  resolved dst range must not overlap, else UB ("copy of overlapping
  ranges"). Checked with the ACCESS-FREE resolver (`resolvePlace?`) so
  no SB event is duplicated. Implementation: `doAssignCont` split —
  the guard exists ONLY in the `.copy` branch, so every other rhs
  reduces to the exact old shape (zero repair for non-copy proofs...
  after the first attempt's `let overlapUB : Bool` leaked an
  `if false` wrapper into every ref inversion — the match-per-branch
  form is the right one).
- oseair `Memcpy`: nonoverlapping check (`dAddr < sAddr+sz ∧ sAddr <
  dAddr+sz → Err`) — Memcpy models LLVM memcpy / Miri's assignment
  lowering, so this is faithful, and it makes the two machines AGREE
  on overlap instead of source-only UB.

## Why this is the retag fix's sibling
Source success at the guard SUPPLIES the disjointness the target
fragment needs: the `Memcpy`'s own check discharges from it directly
(both copy leaves now pass an `h_disj` to `runN_Memcpy_step`), and the
`[Borrow(Shared); Memcpy; Die]` interleaving concern dissolves — die
and the dst useMut act on provably disjoint cells. d33's countermodel
is RETIRED: both machines now refuse the forged overlap copy (test
updated to pin exactly that, teeth on both sides verified by
transiently disabling each check). d35 pins the REACHABLE case
differentially: `x := copy x` is `.ub 1` on both machines.

## Consequences for the residuals
With this + the lowering-order fix, NO copy/ref/const_write residual
shape has a standing countermodel. The separation-invariant parked
entry is DEMOTED (both its consumers dissolved). Remaining residual
work is composition: disjoint-range commutation (foldCells locality)
+ BRIDGE 1S for nonzero-offset copy, spine composition, regime-B.

## Faithfulness note
Exact self-assignment `x = x` is UB here (any overlap). rustc's MIR
builder materializes rhs operands through temps in the cases users
write, and Miri's `copy_op` uses nonoverlapping copies — pinned
Miri-side verification stays on the parked list with the other local
witnesses.

## Process scar (the same one, again)
A `git checkout -- <file>` during teeth restored the last COMMIT and
destroyed the uncommitted semantics edits; reconstructed from the
session patch. Rule upgraded: during teeth-verification, revert by
INVERSE EDIT (the paired python splice), never by git checkout, unless
the fix under test is already committed.

## State
All targets green; suite 82/123 (0 fail — the Miri-pinned corpus is
unchanged, confirming reachable behavior is preserved); units 16/16 +
48/48; axiom audit exact; audit stays at 4 sorries.
