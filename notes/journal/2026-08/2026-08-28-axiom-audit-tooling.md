# 2026-08-28 — Machine-checked axiom/sorry audit

## What
`scripts/axiom_audit.lean` + `scripts/audit_axioms.sh`: elaborating the
script audits `obseq3.proof.compile_correct` (extensible root list) and
FAILS elaboration — nonzero exit — on any drift:
1. transitive axiom closure (via `Lean.collectAxioms`, which already
   walks the full dependency tree, so `#print axioms`-style transitivity
   is inherited) must be ⊆ {propext, Classical.choice, Quot.sound,
   sorryAx};
2. the set of SORRY ROOTS — reachable declarations whose own body
   mentions `sorryAx`, found by a hand-rolled DFS over
   type+value used-constants — must EXACTLY equal the pinned list of
   audited residuals (currently the 4). New sorry → fail; closed sorry
   still pinned → fail, forcing the pin to move in the same commit.

## Design decision (user's call)
Root at the MAIN THEOREM, not a sweep over all project declarations:
the guarantee that matters is what `compile_correct` rests on, its
closure covers every consumed lemma, and unreachable declarations are
by definition irrelevant to the statement. Simpler and cheaper.

## Why the DFS on top of collectAxioms
`collectAxioms` says WHICH axioms are used, not WHERE `sorryAx` enters.
The DFS records the declarations that reference `sorryAx` directly —
the residuals themselves, not their consumers — which is what the pin
compares against.

## Teeth (all three verified, restored after)
- drop `sorryAx` from the whitelist → "axioms outside the whitelist".
- un-pin `copy_place_residual` → "UNAUDITED sorries reachable".
- pin a ghost (`ref_local_local_simulation`) → "pinned sorries no longer
  present". (First attempt at this teeth-check was a silent no-op edit —
  the un-asserted replace missed; the assert-every-splice rule caught it
  on redo. Also: `cmd | tail; echo $?` reports tail's status — pipe
  exit-code pothole.)
- also catches: `native_decide` (`ofReduceBool`), project-local `axiom`
  declarations, anything a dependency smuggles in.

## Wiring
CLAUDE.md: run `scripts/audit_axioms.sh` in validation before every
proof-touching commit; move the pin in the commit that closes/adds a
residual. Script needs `import Lean` (project modules don't pull the
meta API).

## Addendum (same night): whitelist externalized
Per user request the pin moved out of the script into
`scripts/axiom_whitelist.txt` (`[axioms]` / `[sorries]` sections, `#`
comments), and the comparison is now EXACT in both directions for both
sections — a stale whitelisted axiom that is no longer used also fails,
keeping the file an honest record. Teeth re-verified on the file:
removed `sorryAx` line → rogue-axiom failure; added a ghost sorry line
→ stale-pin failure. (Lean 4.28 note: `String.trim` is deprecated →
`trimAscii.toString`.)
