# 2026-08-28 — Copy L→L closed; the bidirectional-relation scare dissolves

## What closed
`copy_local_local_simulation` (proof/copy.lean): `dst := copy src`,
both bound locals, any layout. Fragment: ONE `Memcpy` — the src
lowering for a mapped local is a bare register read, so no Borrow, no
Die, no fresh register, no rename growth. `CompilerInv_step_copy` is
now a proved dispatcher; `copy_place_residual` names the rest. Audit
stays at 4.

## The predicted blocker that wasn't
The audit predicted a "bidirectional memory relation": target-side
junk at source-absent cells would break `SourceMemSim` after the copy
(source dst cell becomes explicit `.undef`, target dst cell copies the
junk, `MemValSim .undef (Dat v)` was False). The fix is NOT a new
invariant conjunct (which would tax every closed write site) but a
WEAKENING: `MemValSim`'s undef row is now `| .undef, _ => True` —
undef refines anything, the textbook forward-simulation reading. It is
sound because every source operation that OBSERVES a word errs on
undef (branch reads, alloc-length reads, pointer loads demand their
constructor), so those cases carry no simulation obligation. All
`h_mvs.elim` consumers case on SOURCE ptrVal rows — untouched. Whole
project rebuilt green with zero proof edits.

## New machinery
- `readWordSeq_sim` (common.lean): pointwise `ListRel (MemValSim)`
  between `mirlite.readWordSeq` and `oseair.readWordSeq` over the same
  range, from `SourceMemSim` + `IdentityOnDomain` alone; source holes
  ride the weakened undef row. The read half of the copy bridge.
- `runN_Memcpy_step` (common.lean): one-step Memcpy execution —
  entries, bounds (a Bool `||` condition: `if_neg` via
  `Bool.or_eq_true/decide_eq_true_eq/not_or`), read then useMut, memory
  written with the read sequence, registers untouched.
- `SourceMemSim.writeWordSeq_extend` (existing, BRIDGE 2's core) closes
  the write half directly — `writeThroughPtr_sim` itself was not needed
  since Memcpy inlines its own useMut+write.

## Events line up exactly
mirlite `.copy` = `M.read` src range (evalRExpr) + `useMut` dst range
(writeResolvedPlace). oseair `Memcpy` = the same two, same order, same
lengths (`typeSize (layoutToTyVal τ) = blockSize τ`). BRIDGE 3's read
and write members transport them 1:1; NextTags frame through both.

## Potholes (catalogued ones, met again)
- `subst` roulette in `readWordSeq_sim` (addr eliminated) → rw at the
  hypothesis instead.
- `IdentityOnDomain` gives `a = b` from `ρa a = some b`; the h_dom
  rewrite needed `← h_e` (and then `grind [IdentityOnDomain]` made the
  point moot).

## State
Suite 82/123 (0 fail), differential 82/0/0 (d6_tuple_copy covers the
closed regime differentially), units 16/16 + 44/44. Leaf axioms:
propext, Classical.choice, Quot.sound.
