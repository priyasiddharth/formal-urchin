# 2026-08-28 (night, cont.) — The lowering-order fix lands

## What changed (compile.lean)
`compileRExprToChecked` split into phases: `compileRExprPreChecked`
emits ALL rhs source-side code (loads, borrows, temp Assgns, pre-store
cleanups) and returns an `RhsPre` — the store instructions as a
function of the eventual dst register, the post-store cleanups (a
copy's src borrow must survive its own Memcpy), and the evidence
factory `(dstPtr : Register) → RExprToEvidence dstPtr expr`.
`compileRExprToChecked` is now the uniform composition pre;store;
postCleanup — its emitted stream is UNCHANGED for every rhs.

`compileStmtChecked`'s assign-PLACE arm (and the `compileAssignChecked`
twin) now use MIR's order: **rhs pre-phase first, then the destination
lowering, then the store** — no dst temporary `Borrow` is live while
rhs code runs. The assign-LOCAL arm is untouched. For code-free rhs
(constInit/uninit) the assign-place stream is byte-identical, so every
closed const_write regime kept its closed-form statement.

## d34 flips
The pin fired on first post-fix run (target `.ok`); d34 is now an
`expectDiff .ok` agreement test with reversion teeth (flipping the arm
order back reproduces `.ub 5` — verified).

## Proof fallout: shockingly small
The state-function monad's DEFINITIONAL monad laws kept most `rfl`
bind-equations alive; simp-based fragment proofs needed only
`compileRExprPreChecked`/`cleanupInstrs`/`emit_nil` added to their
lists. Real edits: `emit_nil` relocated earlier in common.lean; one
dead empty-range `if` layer discharged by funext+if_neg (F→L);
`ref_deref_local_simulation`'s `h_rhs_bind` restated against the
uniform new definition (with an `h_pre_run` framing equation).

## New potholes
- **`lake build` bare builds only the DEFAULT target (Core), which
  excludes Obseq3Proof** — my "full build: 0 errors" sweeps were
  vacuous until the axiom-audit wrapper (which builds Obseq3Proof)
  caught the breakage. Validate with explicit targets:
  `lake build Core Obseq3 Obseq3Proof Conformance`.
- An interior `emit s []` (the postCleanup of a code-free rhs) blocks
  emit-chain rfl; `emit_nil` in the closing simp handles it, EXCEPT
  when an earlier simp already unfolded `emit` — then the dead
  empty-range `if` needs funext + `if_neg (by omega)`.

## State
All targets build; suite 82/123 (0 fail); units 16/16 + 47/47
(differential now includes d34 as agreement); axiom audit exact;
audit stays at 4 sorries. The interleaved-keystone obstacle is GONE
from the non-local-dst residual class — what remains there is the
separation/overlap analysis only.
