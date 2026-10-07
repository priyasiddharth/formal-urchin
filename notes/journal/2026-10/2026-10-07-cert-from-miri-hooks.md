# 2026-10-07 — Can Miri emit the certificate itself? (hook survey)

## Context
The user asked whether certificate generation should move into the Miri
fork instead of scraping MIRI_LOG. Survey of the pinned Miri
(rust-version 4667d75565) before deciding.

## Findings
[OBS] The interpreter loop (`InterpCx::step`, `eval_terminator`) is in
rustc_const_eval, i.e. in the TOOLCHAIN, not the Miri repo: unpatchable
without a custom rustc. Patch points are the `Machine` hooks (Miri's
src/machine.rs) and Miri's own code.
[OBS] `Machine` has no statement or block-entry hook. `before_terminator`
fires BEFORE the terminator runs (frame loc = the terminator), so the
branch taken is only visible at the next hook in that frame. Miss: a run
that ends with UB inside the statements of the entered block never
reaches the next terminator — the last switch stays unresolved. The log's
`// executing bbN` is printed AFTER `eval_terminator` (step.rs:70), which
is why the scraper sees that block.
[OBS] Miri's own loop calls `step()` in `step_current_thread`
(src/concurrency/scheduler.rs:177). After `step()` returns, the frame's
loc is the entered block — the exact moment the log line is printed. A
flag set in `before_terminator` + a read of `frame().loc` there
reproduces `// executing bbN` structurally, no evaluation.
[OBS] Frame push/pop: `after_stack_push`, `before_stack_pop`,
`after_stack_pop`, `init_frame` (FrameExtra can carry a frame id). The
frame's `instance.def_id()` gives the crate exactly — replaces the
scraper's text heuristics for "user frame" (`is_user_frame`,
`last_segment`, the turbofish bug).
[OBS] Switch/assert shape (targets, success block, discriminant operand)
can be read from the frame's MIR body in `before_terminator` without
evaluating anything.
[DEC] Do not evaluate the discriminant THROUGH THE INTERPRETER: the patch
runs inside Miri, so `eval_operand`/`read_immediate` on a place in memory
goes through `before_memory_read` → a real SB read (disables Uniques
above the granting item, stacked_borrows/mod.rs:307), can raise UB, and
updates data-race clocks. Verdict impact is almost surely nil (Miri reads
the same operand with the same tag right after, and an SB read is
idempotent), but the error would be raised by our code and the patch
would no longer be logging-only. A raw read (`get_alloc_raw`, no hooks)
would be side-effect free. Not needed anyway: the entered block IS
Miri's outcome; evaluating would re-implement its `BinOp::Eq` compare.
(Corrected after the user asked why evaluation would touch SB state; the
first version of this note said "never evaluate".)
[OBS] The drop-flag heuristic reads executed `_N = const true/false`
assignment lines; no statement hook exists. Either read the statement
from the body in `step_current_thread` before `step()` (MIR inspection,
no evaluation) or classify statically from the body at frame push (may
differ from the executed-assignments rule; check by diffing certs).

## Decision (proposed; the user approved it)
Feasible as an observation-only patch in TWO files (machine.rs +
scheduler.rs, ~5 lines in the latter); bootstrap_tools.sh's allowlist
would widen to both. Validation: regenerate every certificate both ways,
require identical .cert.json, and all 208 Miri verdicts unchanged.

## Implementation
[OBS] Fork commit d5a505f56 (`formal-urchin: certificate events,
observation only`): `machine::formal_urchin` writes JSON lines to
FORMAL_URCHIN_EVENTS (push / pop / term / enter / assign / variant);
hooks: `after_stack_push`, `before_stack_pop` (entry, = where rustc logs
`popping stack frame`), `before_terminator` (switchInt/assert text + a
"terminator ran" flag), and in scheduler.rs `step_current_thread`
`before_step` (the `_N = ...` statement about to run) / `after_step`
(the block entered). Every hook returns at once when the variable is
unset, so the tool is inert for verdict runs.
[OBS] Found while doing it: the 2026-10-06 variant walk read the tag via
`read_discriminant` — an interpreter read, i.e. a real SB/data-race
access on the argument local. Replaced by `raw_bits` (the frame's
immediate, or `get_alloc_raw(..).read_scalar(.., false)`; a pointer's
bits are its address) + `raw_variant` (Direct/Niche decoded as
`read_discriminant` does). All 3 recorded variants come out the same.
[OBS] Validation: (1) all 76 certificates regenerated from events equal
the committed ones from MIRI_LOG, ignoring only `miri.toolchain` and the
log's module prefix in `descr` (`rustc_const_eval::interpret::step `,
diagnostic-only) — 66 switches, 58 asserts, 18 Box drops, 3 variants,
1 drop flag, 28 UB outcomes; (2) live.py with the bootstrapped tool:
ALL 208 Miri verdicts equal the manifest (checked from report.txt,
supported and unsupported); drift only in the 76 certificates, every
changed line the toolchain string or a de-prefixed `descr`; (3) suites
unchanged (units 33 + 146, corpus 190/0/0/18, --osea 190, --layouts 190).
[OBS] Speed: a certificate run takes ~0.03-0.5 s without MIRI_LOG.
[DEC] Kept the text heuristics (`is_user_frame` by name, drop flags by
assignment text) so certificates stay identical; replacing them with the
frame's def_id/crate is a follow-up, parked.

