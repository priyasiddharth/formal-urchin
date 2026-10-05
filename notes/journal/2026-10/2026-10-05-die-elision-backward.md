# 2026-10-05 — Die elision, backward: same verdict on compiled code

## Context
`die_elision` is OK(A) ⇒ OK(B). The user asked for the other direction
(UB in OSEA-IR ⇒ UB in OSEA-IR_B), equivalently OK(B) ⇒ OK(A). False for
arbitrary OSEA-IR (w1–w3). For compiled code it needs two COMPILER
properties: every `Die` succeeds, and nothing acts through a died tag.
Neither involves the source program (an earlier answer of mine said it
did; corrected).

## The compiler check
[OBS] Reading compile.lean: `Die`s come only from `cleanupInstrs`, and
every cleanup list is a singleton in practice — `projOffset`'s base and
`placeToBorrowRegChecked`'s base are never `.proj` (nested projections
are reassociated first), so their cleanup is `[]`. `.ref` never dies its
borrow (postCleanup `[]`); `addrOf` uses the local's own register. Hence
the expected shape of every bracket:

    r := Borrow k false [] (some n) base off   -- k ∈ Mut/BoxMut/Shared/Raw false
    one access THROUGH r                        -- Load/ExposeAddr/FromExposed/PtrOffset, RStore/CStore at r
    Die r n

and `r` (a fresh register) appears nowhere else. `SkipIf` jumps over a
whole compiled assignment, never into a bracket.

[OBS] `oseair.bracketIssues` (src/obseq3/brackets.lean) checks exactly
that, per program, decidably. Wired into `expectDiff` (all compiled
witnesses) and `--osea` (all compiled corpus programs; new status
`brackets`, fails the suite). Result: 0 issues; the corpus has 771 `Die`s,
all checked. Sanity: the checker rejects w1/w3's shapes and a reuse of a
bracket register, accepts a good bracket.

## Plan from here
1. General lemma: a program whose brackets check out reaches the same
   verdict on OSEA-IR and OSEA-IR_B (OK(B) ⇒ OK(A) at each step).
2. Compiled code passes the check: either prove it for `compile.lean`, or
   keep it as a per-program decidable hypothesis (as `LocalsAgree`).
