# T1 and T2: the two tiers a certified branch is checked by

[FACT, as of 2026-09-25] Certificate-guided lowering
([[certificate-guided-lowering]]) follows Miri's recorded arm at every
branch, and every recorded branch is checked in one of exactly two
tiers. There is no third tier since `binOp` landed (2026-09-24): a
branch on a word the seam cannot fold is now a branch on a word the
PROGRAM computes, so T2 always applies where T1 does not.

## T1 — cross-checked while lowering (static)

The lowering can fold the discriminant itself (tracked constants per
`(local, field path)`, through tracked references; checked arithmetic
folds to `(v, 0)`), so it compares its own value against Miri's arm at
LOWERING time. Disagreement is the error "certificate disagrees with
lowering at line L", and the test is rejected before it runs. Nothing
is emitted: T1 costs no statements and no runtime.

## T2 — checked by the program (runtime)

The discriminant is a word only the execution knows (a load, an enum's
discriminant slot, a `binOp` result, a `sliceLen`). The lowering emits a
check built from statements the language ALREADY has — this is the whole
trick, and the reason no new instruction, semantics or proof was needed:

    bad := uninit                    -- scratch local, undef
    if d == v: bad := 0              -- initialise ONLY on Miri's arm
    tmp := copy bad                  -- typed read: UB iff still undef

The UB is a *typed read of uninitialised memory*: mirlite's `evalCopy`
errs with "read of uninitialized memory" (mirlite_semantics.lean) and
the compiled `Load` applies the identical rule (oseair.lean), so both
machines reject in lockstep and `--osea` compares them normally.

The `otherwise` arm inverts the shape — `bad := uninit`, then for each
excluded `v`, `if d == v: tmp := copy bad` — so the undef read fires
exactly when the discriminant IS one of the values Miri said it was not.
An `otherwise` with nothing to exclude is vacuous and emits nothing.

[FACT] Why a wrong check cannot change a correct program's verdict: the
only cells it touches are two scratch locals nothing aliases, and the
only ALIASING event it adds is the discriminant read — which Miri's own
`switchInt`/`assert` performed at that point anyway.

[FACT] How it stays out of the verdict: check statements carry sentinel
line numbers (`certLineBase = 1_000_000 + line`; the poison ending a
UB-prefix certificate uses `2 ×`). The runner maps a failing statement
by line — `≥ 2 ×` → `certExhausted`, `≥ 1 ×` → `certRejected`, else a
real `.ub` — so a failed check reports "certificate rejected at line L"
and FAILS the test rather than becoming a UB verdict
(src/conformance/harness.lean).

## Coverage, measured

[EMP, verified against this tree 2026-09-25] 24 certificates record 43
branch events between them (6 record none: straight-line executions).
All 43 are checked — 25 T1, 18 T2 across 6 entries (int-to-ptr 9,
aliasing_mut_and_shr 4, box_derefer 2, array_casts 1,
aliasing_frz_and_shr 1, local/slice_len_value 1) — and 0 are unchecked.
Coverage is total by construction, not by luck: leaving a frame with
unconsumed events is an error, so the recorded and checked counts cannot
drift apart. The harness prints the split
(`checked 43 (25 static, 18 runtime in 6 entries)`).

[FACT] T2 is the tier with teeth against a wrong certificate, and both
of its forms are demonstrated live rather than assumed:
- perturb the equality check to demand `v + 1` → int-to-ptr,
  aliasing_mut_and_shr, box_derefer report `certificate rejected`;
- perturb the exclusion check to demand membership → array_casts,
  int-to-ptr, aliasing_mut_and_shr, aliasing_frz_and_shr do;
- perturb `sliceLen` by one → local/slice_len_value does.
Together these cover all six entries that have runtime checks.

[FACT] Flipping a recorded `arm` instead usually gets caught EARLIER —
by the T1 cross-check, or by the wrong arm walking into an abort path —
which is why an arm-flip test alone does not exercise T2's statements.
Tested across every certificate: no flip reached a runtime check.
