# Certificate-guided lowering: dynamic control flow without a CFG

[FACT, as of 2026-09-23] The seam lowers `switch`/`goto`/loops/asserts
along an execution CERTIFICATE: `conformance/charon/<name>.cert.json`
(manifest field `certificate`) records, per USER-frame instance in Miri's
entry order, the arm every `switch` took and whether every `assert`
passed. Source: `scripts/gen_cert.sh` → the pinned Miri (submodule
`conformance/vendor/miri`, driver run directly since 2026-09-28; was
`cargo +nightly-2026-06-01 miri`) with `-Zmir-opt-level=0` and `MIRI_LOG="rustc_const_eval::interpret::step=info,…stack=info,…call=info"`,
parsed by `scripts/miri_cert.py`. Events are matched by KIND in
execution ORDER (block/local numbers differ between charon's built MIR
and Miri's runtime MIR); a frame ends at `popping stack frame` (or its
executed `return` when that module is absent from the log). The Lean
side: `src/conformance/certificate.lean` (`Cert`, `CertCursor`),
`lowering.lean` (`walkBlock` `.switch`/`.assert` arms, `inlineCall`
open/close frames, `emitCheckEq`/`emitCheckNotIn`, `consumeEvent`).

[FACT] Three tiers per branch. T1: the lowering FOLDS the discriminant
(constants per (local, tuple-field path); tracked references
`refOf : ConstKey ↦ UPlace` with `resolveKey` following deref chains;
checked arithmetic folds to `(v, 0)`; a write through a tracked pointer
UPDATES its target) and Miri's arm must agree — disagreement is the error
"certificate disagrees with lowering". T2: the discriminant is a faithful
runtime word (a load, an enum's slot 0, `Eq/Ne(place, const)`) →
one `check d ∈ [v]` (or `∉ vs` for `otherwise`), stuck iff the pin is
wrong; the statement carries a sentinel line (`certLineBase`) so the
harness reports `certificate rejected at line L`. [As of 2026-10-07]
`check` is a mirlite statement and an OSEA-IR instruction (`Check`),
inside the theorem (`check_simB`).
[SUPERSEDED → this paragraph, 2026-10-07] "`bad := uninit; assignIf d v
(bad := 0); tmp := copy bad`, UB iff the pin is wrong ... No mirlite,
oseair or proof change" — `assignIf` and `SkipIf` were deleted the day
`check` landed; see journal/2026-10/2026-10-07-check-statement.md.

[SUPERSEDED 2026-09-24] There WAS a third tier: a comparison on words
Miri did not log took its arm on Miri's word alone, with the result a
TAINTED placeholder barred from indices/offsets/sizes. Since mirlite
gained the word `binOp` rvalue the seam EMITS that arithmetic instead,
so the discriminant is a real computed word and T2 applies to every
branch it cannot fold; `symVals`/`tainted`/`memTainted`/`faithfulPlace`
are gone. The `pinned` counter stays in the report as the standing
witness that it is 0.

[FACT] Corpus effect (2026-09-23): 93 → 96 supported (fnentry_invalidation,
int-to-ptr, stacked-borrows::two_phase_aliasing_violation), 20 entries'
prep rewrites reverted to upstream `assert_eq!`/`+=`/`match`; 23 entries
certified, 27 checked, 14 unchecked pins (all `+=` through RefCell
guards or exposed-address arithmetic) — which `binOp` then took to 41
checked and 0 unchecked (2026-09-24, same 96/0/40). A UB-outcome
certificate is a
PREFIX: the lowering emits a poison at its end and mirlite must reach its
own UB first (`ran past Miri's UB point` otherwise).

[FACT] Why this is sound where it could have been sloppy: the checks
caught two real bugs during development — a field assignment un-tainting
a placeholder tuple, and an in-place seam retag making a reference
self-referential so `self.0` became a placeholder that flowed into a
checked `assert_eq!`. Both surfaced as `certificate rejected`, never as
a wrong verdict. See [[what-compile-correct-actually-says]] for what the
theorem does and does not cover (it covers every statement the checks
use).

See [[certificate-check-tiers]] for the two tiers in detail (what T1
and T2 are, how a T2 check becomes UB, and the measured coverage).

[FACT 2026-09-25] Coverage, measured: the 24 certificates record 43
branch events (6 record none — straight-line executions), and all 43 are
checked: 25 by folding (T1) and 18 at runtime (T2) across 6 entries
(int-to-ptr 9, aliasing_mut_and_shr 4, box_derefer 2, array_casts 1,
aliasing_frz_and_shr 1, local/slice_len_value 1). The harness now prints
that split instead of one conflated `checked` number, so "how much of
the certificate is really checked by the PROGRAM" is readable off the
report. Both runtime check forms are demonstrated live: perturbing
`emitCheckEq` (demand `v + 1`) rejects int-to-ptr, aliasing_mut_and_shr
and box_derefer; perturbing `emitCheckNotIn` (demand membership) rejects
array_casts, int-to-ptr, aliasing_mut_and_shr and aliasing_frz_and_shr.

[FACT 2026-09-24] The checks have teeth on the runtime path too, not
only on the folded one: making `emitCheckEq` demand `v + 1` turns three
corpus entries into `certificate rejected` (int-to-ptr,
aliasing_mut_and_shr, box_derefer — the entries whose branches are T2).
Flipping a recorded `arm` instead is caught EARLIER, by the T1
cross-check or by walking into an abort path, which is why the flip test
alone does not exercise the check statements.

[OPEN] `assert_eq!` on a tuple calls the tuple's `PartialEq::eq`, an
opaque std body — one rewrite stays. Slice lengths remain the next
language step.
