# 2026-10-06 — Certificates record fn-entry enum variants

## Context
`assignIf` in the loader served four uses: certificate checks, the run-time
array dispatch (removed 2026-10-05), `format!` assumptions, and enum
retags at inline seams. The user asked whether Miri could record which
variant an enum argument holds, with a certificate check the loader
exercises (option 2 of the discussion).

## How Miri retags an enum (pinned toolchain)
[OBS] There is no separate retag visitor: rustc's VALIDITY walk of the typed
copy runs under a retag mode (`interpret/call.rs:520`, FnEntry for argument
passing; `step.rs:181`, Default for retagging assignments) and hands every
pointer to Miri's `retag_ptr_value`. The walk reads the discriminant and
visits only the active variant. That walk is rustc code in the toolchain:
patching it means rebuilding rustc.

## The Miri patch (fork, logging only)
[DEC] Miri implements `Machine::with_retag_mode`. The fork wraps it: after a
FnEntry argument pass, it walks each argument local (aggregates and enums
only; never through a pointer, a Box or a union), reads each enum's active
variant, and logs `formal-urchin variant: arg=N path=[.i.j] variant=K ty=T`
at info (target `miri::machine::formal_urchin`). Nothing is written; a
failed read is skipped. Fork commit 5e59a919d on branch `formal-urchin`.

[DEC] Pin policy changed: PIN gains `miri_tool_commit` (upstream
`miri_commit` + that patch). `bootstrap_tools.sh` builds the tool from it
and checks it differs from upstream only in `src/machine.rs`, and the fork
head from it only in tests/formal-urchin. `live.py` guards on it.

## Extractor and loader
[OBS] `miri_cert.py`: `RE_VARIANT`; per user frame a `variants` table
(arg, path, variant, ty). `gen_cert.sh` adds `miri::machine=info`.
`certificate.lean`: `CertVariant`, `CertCursor.variantOf?` — a LOOKUP, not
an ordered event (Miri also logs enums inside std types the loader never
retags; an ordered stream would leave them unconsumed).
[OBS] Loader: the callee's certificate frame now opens BEFORE its arguments
are bound. `emitSeamCopy` takes the argument/path key; for an enum with a
recorded variant it emits `emitCheckEq discr v` (UB unless the program's
own discriminant agrees — "certificate rejected" otherwise), then that
variant's retags, unguarded. With no recorded variant it falls back to the
guarded retags. `certBump`/`emitCheckEq` moved from lowering.lean to
emit.lean.

## Witnesses
local/enum_arg_variant_protected (UB, line 9: the `&mut` in variant B is
protected at entry, a write through an aliasing raw pointer pops it) and
local/enum_arg_variant_unprotected (ok, variant A holds no reference).
Variant chosen at run time.

## Results
[OBS] Regeneration with the patched Miri (`live.py --update`): Miri agrees
with the manifest on every entry, supported and unsupported (208/208 ok in
.live/report.txt); certificates change only in their toolchain string,
except the new `variants` tables. Only ONE corpus certificate records a
variant (`unwrap` of `Option<&RefCell<bool>>` in rust_issue_68303): enum
arguments to user functions are rare in Miri's corpus.

[OBS] Program-level enum guards (`assignIf` outside checks/assumptions)
now remain in 4 programs: 3 return-value seams (as_ref's return in
rust_issue_68303, return_invalid_{mut,shr}_option) and
pass_invalid_shr_option, whose UB Miri raises while COPYING the argument
in the caller — `foo`'s frame is never pushed, so there is nothing to
log and the certificate would have no frame for it (adding one failed:
"lowering entered foo but Miri recorded no further frame"; reverted).

[OBS] Mistake caught by the ICE files: the first patch walked array
elements with `FieldIdx::from_usize`, which overflowed on `[(); usize::MAX]`
(zst-field-retagging-terminates, an unsupported entry) — a CRASH, i.e. the
"logging only" patch changed a verdict. live.py's agreement count covers
supported entries only, so it did not show; the report did (status line)
once checked, and the rustc-ice-*.txt files did. Fixed: arrays by
`project_index`, skipped above 4096 elements; that entry is ok again.
Lesson: for a Miri change, check ALL entries' verdicts, not the supported
count.

[OBS] The corrupted-variant test: setting the recorded variant to 1 in
enum_arg_variant_unprotected's certificate gives "certificate rejected at
line 16" — the check has teeth.

[OBS] Found on the way (parked): moving an enum whose active variant
leaves payload slots uninit (a fieldless `A` of `enum { A, B(&mut u32) }`)
is a FALSE "read of uninitialized memory" in the model — the whole-value
move reads the payload; Miri's typed copy does not care. Pre-existing
(same with the guarded fallback). The witness uses `A(*mut u32)` instead.

Counts: corpus 190/0/0/18 of 208, --osea 190, --layouts 190, units 33 +
149; certificates 76 entries, 126 checked (85 at runtime), 0 unchecked.
The fork commits (5e59a919d, 46c89cef4, d5bcab3bc) are LOCAL: the branch
must be pushed to github.com/priyasiddharth/miri before CI can fetch the
submodule commit.
