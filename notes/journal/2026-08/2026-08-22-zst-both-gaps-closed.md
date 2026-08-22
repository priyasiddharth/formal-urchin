# Both ZST gaps closed; the StorageLive hypothesis refuted by rustc

[FACT] The OSEA target's `Rhs.Borrow` bounds check is now the range form
`addr + len > base + size` (oseair.lean), replacing `addr ≥ base + size`.
This is Miri's actual requirement — the retagged range must be
dereferenceable — and it is the same form `writeThroughPtr` already used.
For `len = 0` it admits a one-past-the-end address, which is exactly what
makes `&()` legal. It is STRICTER for multi-cell retags (it requires the
whole range in bounds, not just the first cell), and the differential did
not move: matched 78 | mismatch 0 | skipped 0. So no currently-accepted
program retags past its allocation — which is what well-typed places
guarantee, and the suite now checks.

[FACT] Proof side, the side condition was load-bearing only for the old
check: `runN_Assgn_Borrow_step` now takes `b + bo + offset + len ≤ b + sz`
(discharged by `Nat.le_refl` in the L→L regime, where offset = 0 and
len = blockSize τ), `ref_local_local_simulation` lost `h_nz`, and
`ref_zst_residual` is DELETED — closed by removing its cause, not by
proving it. Audit 6 → 5. This is the second time today a proof
obligation was discharged by aligning a machine with Miri rather than by
a proof (the first was the `BEq TyVal` instance); both were found by
attempting a leaf.

[FACT] `local/zst_ref` now PASSES end to end: source ok (loader fix,
earlier today) AND target ok (this fix), differential matched. Suite
pass 78 | fail 0 (119 total with the new probe).

[SUPERSEDED → this entry] The [HYP] in
2026-08-22-zst-loader-gap-fixed.md — that dropping `StorageLive/Dead` and
allocating at first assignment could be exposed by a borrow-before-write
— is REFUTED for the supported fragment, by rustc rather than by the
model. `let x: u64; let p = &raw const x;` is E0381: the borrow checker
forbids taking the address of an uninitialized local. The only legal form
is `MaybeUninit::uninit()`, a bodyless call on a UNION type, and unions
are outside the lowering's surface. So without unions, every local is
written before it is borrowed, and first-assignment allocation is sound
BY CONSTRUCTION. Why I was misled: I reasoned from Miri's allocation
model (`StorageLive` allocates) without checking what Rust lets you
write; the gap between "what Miri would do" and "what rustc admits" is
the whole point of the witness discipline, and here it cut the other way.
The probe is registered `unsupported: unions` so it lights up if unions
land.

[OBS 2026-08-22] Process note on the three home-grown witnesses this
week: each one was written to probe ONE claim and each one found
something adjacent — the deref-read witness found the `resolvePlaceAcc`
change, the ZST witness found a loader gap in front of its target, the
StorageLive probe found a rustc guarantee that replaces a model argument.
Promote to durable when it recurs once more: *a witness is worth writing
even when the hypothesis is wrong, because the pipeline answers a
different question than the one asked.*

[FACT] Second ZST witness added the same day, `local/zst_tail_field`:
a ZST field at a struct tail, where `addr = base + size` with
`base ≠ addr` and `size = 1`. `zst_ref` alone was NOT enough coverage for
the check change — there the ZST stands alone, so `base = addr` and
`size = 0` and one-past-the-end holds degenerately; only the tail-field
case exercises the boundary at a nonzero offset. Both witnesses were
shown to have teeth by restoring the old point check and observing two
INDEPENDENT mismatches (labels 5 and 6): a passing test proves nothing
about a check change unless it is also shown to fail without it.
Promote if this recurs: *when a fix relaxes a predicate, add the witness
that distinguishes the degenerate case from the general one, and verify
by reverting.*

[OBS 2026-08-22] A third ZST witness, `local/zst_interior_field`, was
added and its first version was WRONG about why it was worth having. The
claim was that it "pins the third position an empty range can occupy";
the teeth probe refuted that — an interior address is genuinely in
bounds, so the old point check `addr ≥ base + size` accepts it too, and
it mismatched under neither check. Only `zst_ref` and `zst_tail_field`
are boundary regression tests. The witness was restructured to earn its
place differently: because a ZST occupies no cell, `(u64, (), u64)` puts
`s.1` and `s.2` at the SAME offset, so keeping a `&mut s.2` live across
the `&mut s.1` retag catches a retag that wrongly used length 1 — a
different bug class (wrong length) from the boundary one (wrong
comparison). Lesson, and the reason the probe is worth running every
time: *a test whose failure mode you cannot name is a passenger.*

Validation: suite pass 80 | fail 0 | unsupported 41 (121), differential
matched 80 | mismatch 0 | skipped 0, units 15/15 + 38/38, all targets
build. `ref_local_local_simulation` axioms: propext / Classical.choice /
Quot.sound.

**References:** conformance/local/zst_ref.rs,
conformance/local/unassigned_local_addr.rs,
2026-08-22-zst-loader-gap-fixed.md (superseded HYP), proof/compiler.lean.
