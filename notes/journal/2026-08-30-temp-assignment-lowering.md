# 2026-08-30 (seventh) — the temp-assignment lowering (COMPILER + SEMANTICS CHANGE)

Approved by the human after the divergence witness and the rustc/Miri
evidence. Three coordinated changes plus the proof repair.

## 1. Compiler: copy materializes the value in a REGISTER
`compileRExprPreChecked`'s `.copy` arm now lowers the source place,
emits `tmp := Load τ srcReg` (THE READ) followed by the source
cleanup, and defers only `RStore τ tmp dstPtr` to the store phase.
Previously the whole read+write was one `Memcpy` emitted AFTER the
destination lowering, which put the read after the destination chain's
own pointer reads — observable under Stacked Borrows (d59).

The temp is a REGISTER, not an allocation: oseair registers hold
`(TyVal, List Val)` and `Rhs.Load ty` reads `typeSize ty` words. This
matters — a heap temp would bump only the target's watermark and break
`AllocLockstep`, hence identity-`ρa`. (That was the human's objection,
and it is why the register route is the right one.)

## 2. ISA: `Rhs.Load` bounds-checks its whole width
Was `addr < base || addr >= base + size` — sound only because `Load`
was used exclusively at `PTy` (one word). Now
`addr + typeSize ty > base + size` errs, matching `writeThroughPtr`.

## 3. Semantics: overlapping assignment is ALLOWED
mirlite's `doAssign` no longer rejects an overlapping copy. rustc reads
into a temporary (`_5 = (*_2); (*_2) = move _5`) and Miri runs `*p = *p`
clean, so the old guard was stricter than Rust; it existed only to
match the nonoverlapping `Memcpy`. d35 flips from UB to ok, and d33's
forged countermodel now SUCCEEDS on both machines (its `Die` precedes
the write, which is the whole point).

## Proof repair (copy.lean, all six leaves)
Every leaf's fragment and endgame moved from one `runN_Memcpy_step` to
`runN_Assgn_Load_ptr_step` + `runN_RStore_step`, with one extra fresh
register threaded through the `LocalBindingSim`/`RegisterBelow`
bullets. The nonzero-offset leaves got SIMPLER: the cleanup `Die` now
sits between the read and the write, so BRIDGE 1S's `Borrow; read; die`
is contiguous and `sb_die_sb_write_comm` (the slide) is no longer
needed at all — the destination write simply follows the parent read.
Also deleted: every leaf's inversion of the (now absent) overlap guard.

New helpers in common.lean: `oseair_readWordSeq_length`,
`mirlite_readWordSeq_length`.

## Validation
Full build; 17/17 + 72/72 (d59 is the new regression pin); corpus
82 pass / 0 fail / 123; audit exact at 2. The witness
notes/2026-08-30-copy-order-witness.lean now passes (both machines ok).

## State
`copy_place_residual`'s last class (non-local destination) is now
ordinary composition work: two place lowerings and two cleanups in one
leaf. No commutation argument, no invariant strengthening needed.
