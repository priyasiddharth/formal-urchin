# 2026-09-28 — Live conformance: pinned Miri + Charon as submodules

[OBS] Before today the corpus suites never ran Miri or Charon: they read
committed ULLBC JSON and certificates and compared against manifest
verdicts recorded once. And the Miri that recorded them was rustup's
`nightly-2026-06-01` component (miri 14210df0e2), NOT the corpus pin
34d6a79544 — the corpus and the judge were two different Miris.

[OBS] Now: `conformance/vendor/{miri,charon}` are submodules at
34d6a79544 and 0c229235 (= charon release nightly-2026.08.14);
`scripts/bootstrap_tools.sh` builds both (Miri as the rustup toolchain
`miri` on its own rustc 4667d7556); `scripts/live.py` re-runs Miri
(verdict + line), Charon and certificates on all 140 entries and then
both corpus suites on the fresh artifacts. ~15 s wall, 32 jobs. CI job
`live` caches the tools keyed on the submodule commits.

[OBS] Result with the pinned Miri: 109/109 supported verdicts and lines
agree with the manifest; regenerated artifacts differ from the committed
ones only cosmetically (34 were generated from the repo root and record
`conformance/prep/…`; certificates now name the Miri build); after
`--update` there is zero drift; suites 109/0/31, osea 109 matched.

[FACT] Two tool interactions, both caught by the first parallel run
(60–100 s per entry, E0514 "std compiled by an incompatible rustc"):
- Charon's driver runs `cargo miri setup` on ITS toolchain on every call
  (charon-driver/driver.rs `setup_miri_sysroot`), honouring
  `MIRI_SYSROOT` and otherwise writing `~/.cache/miri` — i.e. it rebuilds
  Miri's sysroot with a std from rustc 14210df0e. Fix: a separate
  prebuilt sysroot passed via `CHARON_MIRI_SYSROOTS`, and `env -u
  MIRI_SYSROOT` around charon.
- cargo-miri re-checks the sysroot per invocation and parallel calls race
  ("concurrent sysroot build with different settings"). Fix: call the
  Miri driver directly on the file with cargo's flags for a dev bin
  (`--crate-type bin -C debuginfo=2`; opt-level 0 turns on debug
  assertions and overflow checks by rustc default), one sysroot resolved
  once. Certificates came out identical, so the MIR Miri sees is unchanged.

[OBS] Also fixed: `miri_local.sh` took the first `-->` span in stderr,
which for `#![feature(custom_mir)]` preps is a WARNING's (line 8), not
the UB's; and aborted (pipefail) on `error-in-other-file` UB with no span
in the test file.

[OBS] Charon's `short_names` table order varies run to run even for the
prebuilt binary; the loader never reads it, and the drift check sorts it.

## See also
conformance/README.md ("Live run"), conformance/PIN,
2026-09-25-local-witnesses-miri-checked.md
