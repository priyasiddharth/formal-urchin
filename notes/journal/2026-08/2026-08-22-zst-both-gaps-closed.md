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

Validation: suite pass 78 | fail 0 | unsupported 41 (119), differential
matched 78 | mismatch 0 | skipped 0, units 15/15 + 38/38, all targets
build. `ref_local_local_simulation` axioms: propext / Classical.choice /
Quot.sound.

**References:** conformance/local/zst_ref.rs,
conformance/local/unassigned_local_addr.rs,
2026-08-22-zst-loader-gap-fixed.md (superseded HYP), proof/compiler.lean.
