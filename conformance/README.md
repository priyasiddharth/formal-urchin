# SB conformance suite (obseq3 vs Miri)

Scores the obseq3 Stacked Borrows semantics against Miri's test corpus:
fail tests must be flagged as UB (at the right source line where curated),
pass tests must run clean. Design: `plans/sb_conformance_obseq3.md`.

## Layout

- `PIN` — pinned miri commit, Charon release, rustc toolchain.
- `corpus/` — pristine miri `tests/` at the pinned commit
  (regenerate: `scripts/fetch_corpus.sh`; gitignored).
- `prep/` — curated single-scenario Rust sources, one per supported
  manifest entry. Each carries a header naming the upstream test and
  every rewrite applied.
- `charon/` — ULLBC JSON artifacts (committed, so the Lean suite runs
  without a Rust toolchain; regenerate: `scripts/gen_charon.sh`).
- `tools/` — Charon prebuilt binary (gitignored; release in `PIN`).
- `manifest.json` — the test registry: per test, status
  (`supported` | `unsupported` | `xfail-model`), reason, expected
  verdict (+ optional line), miri's error text (provenance only, never
  matched), and the rewrites applied during prep.

## Running

```
scripts/run_suite.sh              # lake exe sb_conformance ...
scripts/run_suite.sh --record     # print observed verdicts (curation)
scripts/run_suite.sh --filter illegal_read
lake exe sb_conformance --unit ...          # obseq3 unit tests first
lake exe sb_conformance ... --dump <id>     # lowered program of one test
```

Outcomes: `pass`/`fail` (mismatch — missed UB is always a hard failure),
`xfail`/`xpass(!)` for documented model divergences, `unsupported`
(loader rejected, as the manifest expects), `promote(!)` (an
unsupported-marked test now loads — update the manifest).

## Current score (miri @ PIN)

- fail tests: 27/75 verdict-conformant (line-accurate on 23), 0 xfail,
  48 unsupported with per-test reasons.
- pass scenarios: 9 supported and clean; the rest unsupported with
  reasons (Box/heap, interior mutability, int-to-ptr, slices, threads,
  enums/control flow, transmute).
- Every test that loads agrees with Miri's verdict; there are no
  xfail-model divergences.

Protectors are modeled (call-frame protector sets, fn-entry retags at
inline seams, pop-guards in read/write/die). Statics are hoisted to
uninitialized locals by the lowering (initializer bodies are not run —
fine while every supported test writes a static before value-dependent
use). Remaining model exclusions: interior mutability (UnsafeCell),
deallocation, int-to-ptr exposure, enums, arrays/slices, threads,
drop glue.
