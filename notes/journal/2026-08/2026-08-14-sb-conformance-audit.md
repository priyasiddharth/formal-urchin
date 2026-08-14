# SB conformance audit: Miri corpus survey + obseq3 plan

[OBS 2026-08-14] The only local Miri checkout is the submodule at
/home/siddharth/rustc/rust/src/tools/miri — 2020-07 vintage (old
compile-fail/run-pass layout, pre-Tree-Borrows, no both_borrows split).
Full git history + remote are present, so a `git fetch origin master`
is enough to obtain the modern corpus; no fresh clone needed.

[OBS 2026-08-14] Vintage-corpus classification (51 fail tests in
compile-fail/stacked_borrows, all 51 classified by grep): ~22 core-only
(refs/raws/locals/statics), ~5 Box-only, ~8 Cell/UnsafeCell,
~12 transmute, ~6 fn-pointer, ~3 slice/Vec. Zero use Rc/threads/dyn.
Pass side skews heavier (Vec/Cell/transmute); run-pass/stacked-borrows/
stacked-borrows.rs bundles ~13 independent core sub-scenarios worth
splitting. Modern-corpus live counts (master, 2026-08):
fail/stacked_borrows 37 + fail/both_borrows 38 = 75 fail;
pass/stacked_borrows 5 + pass/both_borrows 9 ≈ 30 scenarios after
splitting.

[OBS 2026-08-14] Coverage expectation for obseq3 after the planned
small fixes (per-cell stacks + writable raws) + Charon ingestion with
call inlining and seam retags: ~30-33/75 fail tests and ~12-14 pass
scenarios green; the rest carry machine-checked unsupported(reason)
or xfail-model markers (protectors ~12, dealloc/Box ~7, interior
mutability ~3+3, int-to-ptr ~5, slices/threads/misc ~13, SRW-grouping
xfail ~3). Full plan: plans/sb_conformance_obseq3.md.

[HYP] The SRW-grouping divergence (obseq3 raw-muts behave like MutRef
in stack discipline, so sibling raws invalidate each other) affects
only ~3 tests (disable_mut_does_not_merge_srw,
shared_rw_borrows_are_weak1/2 — triage pending); if it turns out to
bite more of the pass suite, SRW grouping moves from Phase C into
scope.

See [[v1-v2-sb-model-divergences-from-miri-sb]] and
[[mir-to-lean-ingestion-landscape]] for the durable facts distilled
from this session.
