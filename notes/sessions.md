# Sessions log

Curated index of significant sessions, newest first. For a cold start,
read the most recent entry.

## 2026-06-16 → 2026-07-01
**Session:** `6cb17359` (VSCode)
**Theme:** const_write sorry removal — reconstruct-vs-port decision,
identity-on-domain invariant, steps 1–3 landed.
**Key outputs:**
- `IdentityOnDomain` + two CompilerInv conjuncts (9-conjunct invariant)
- Step-2 execution helpers (fragment locator, `runN_CStore_step`,
  `runN_cleanupInstrs` in conditional form)
- `writeThroughPtr_sim` proved (the semantic core) + memory-framing
  helpers — all in src/obseq2/proof/common.lean (committed as
  `9706889` in the follow-up terminal session)
- Dev-log entry 2026-06-17 committed as `4fb5e45`; Aristotle docs
  committed as `d3fa01e`
**Critical corrections:**
- `runN_cleanupInstrs` cannot succeed unconditionally (`sb_die` can
  fail) → conditional "completion ⟹ preservation" form
- Dev-log stale: `const_init.lean` 5-phase skeleton no longer exists;
  the WF layer (`RegValWF`/`InstrWF`/`CompiledWF`) was never built
- `s_osea.ap = s_mir.perms` unnecessary in `writeThroughPtr_sim`'s
  signature — dropped
**Status:** paused — step 4 confirmed as next step but parked for
workflow reasons (user on another project), not technical ones.
Proof-code commit landed as `9706889`.
**Next-session pickup:** loose-ends/parked.md → "Step 4: regime-A
already-mapped-local milestone".

## 2026-07-01
**Session:** `29f0765f` (terminal) — notes bootstrap + doc sweep
**Theme:** installed better-than-fish plugin; created this notebook;
imported the VSCode session state; distilled the repo's markdown corpus
(dev log, paper.md, plans/, references/, Aristotle docs) into notes.
**Key outputs:** notes/ structure; 7 durable notes (session decisions +
document map, v1 axiom inventory, rejected alternatives, SB-vs-bounds);
journal state snapshot; parked backlog (pending commit, step 4 —
workflow hold only, user on another project — steps 5–6, symbolic-exec
tactic); this log.
**Critical corrections:** step-4 hold is workflow-only (user switched
projects), not technical.
**Status:** complete.

## 2026-08-14
**Session:** `yes-the-miri-happy-breeze` (terminal, run from
~/seahorn/sb_tests — temporary dir, to be deleted)
**Theme:** SB conformance audit — can obseq2 interpret Miri's stacked
borrows pass/fail tests? Audited the gap, planned obseq3 + a
Charon-based conformance suite.
**Key outputs:**
- plans/sb_conformance_obseq3.md (approved plan: obseq3 with per-cell
  stacks + writable raws; Charon ULLBC JSON → Lean loader/elaborator;
  manifest-driven harness against pinned modern Miri corpus)
- durable/v1-v2-sb-model-divergences-from-miri-sb.md
- durable/mir-to-lean-ingestion-landscape.md (incl. Charon-emits-no-
  Retag finding)
- journal/2026-08/2026-08-14-sb-conformance-audit.md (corpus survey,
  coverage estimate ~30-33/75 fail + ~12-14 pass scenarios)
**Critical corrections (user):**
- SB fixes land as a NEW versioned codebase src/obseq3/ (v1→v2
  precedent), not forked files inside obseq2.
- All suite data lives in formal-urchin (conformance/); the sb_tests
  scratch dir will be deleted.
- Existing mirlite tests (src/interp/test_mirlight.lean et al.) must be
  acknowledged/reused as the harness pattern.
**Status:** complete — everything landed in this session (committed as
`445cbf4`):
src/obseq3/ (per-cell stacks, writable raws with Miri's
insert-above-granting SRW placement, TwoPhase, Except errors, 10 unit
tests), src/conformance/ (ULLBC JSON loader, inlining/seam-retag
lowering, elaborator, manifest harness), conformance/ (pinned corpus,
30 preps, artifacts, 109-entry manifest). Score vs miri @ 34d6a795:
fail 23/75 verdict-conformant (19 line-accurate) + 2 xfail (protectors)
+ 50 unsupported(reason); pass scenarios 9 clean. Suite green:
pass 30 | fail 0 | xfail 2 | xpass 0. Dev-log entry 2026-08-14; see
journal/2026-08/2026-08-14-obseq3-conformance-landed.md for the
raw-retag-placement finding (the day's key semantics insight).
**Next-session pickup:** Phase C candidates — protectors first
(converts 2 xfails + ~10 unsupported; composes with seam retags),
statics hoisting cheapest (~4 tests). Reconstruct obseq3 preservation
proofs on demand.

## 2026-08-15
**Session:** `yes-the-miri-happy-breeze` (continued)
**Theme:** OSEA-IR v3 + mirlite→OSEA compiler (proof-core subset) +
`--osea` differential oracle in the conformance harness.
**Key outputs:** src/obseq3/oseair.lean (parameterized target machine,
`Rhs.Borrow`/`Die len`), src/obseq3/compile.lean (Checked family,
`ensurePlaceRoot`, `stmtLabelRanges`), src/obseq3/compile_tests.lean
(5 golden + 6 differential), harness/main `--osea`; journal
2026-08-15-osea-v3-compiler-landed; dev-log 2026-08-15 entry; parked
"OSEA-v3 remaining increments".
**Critical corrections:** none this leg (design deltas vs v2 — deref
no-die, root auto-alloc — were caught at design time, not by failures).
**Status:** complete; first differential run matched 25 | mismatch 0 |
skipped 51; suite unchanged pass 76 | fail 0.
**Next-session pickup:** parked.md → "OSEA-v3 remaining increments"
(pushProtectors first, ~31 tests), or CompilerInv port (conjuncts
6/7/8/9 are the breaking ones per the obseq2 proof inventory).

## 2026-08-15 (later)
**Session:** `yes-the-miri-happy-breeze` (continued)
**Theme:** OSEA-v3 coverage arc completed — seven follow-up increments
(protectors, uninit, heap, exposed provenance, SkipIf, ptr ops,
refSlice) ending at **matched 76 | mismatch 0 | skipped 0**: the
compiler is total on obseq3's surface and the full passing suite runs
differentially.
**Key outputs:** oseair instruction set (PushProt/PopProt, AllocN/
AllocDyn/Dealloc, ExposeAddr/FromExposed, PtrOffset, SkipIf,
BorrowRest); 8 journal entries; dev-log increments 12–18; parked
"OSEA-v3 remaining increments" section closed.
**Critical corrections:** user: never hand-maintain test counts —
runAll now derives from allTests (recorded in auto-memory conventions).
**Status:** complete; next: compiler-correctness proof skeleton
(user-chosen scope; obseq2 proof inventory in hand).
**Next-session pickup candidates:** CompilerInv-v3 skeleton plan (see
plans file / upcoming journal), SwitchInt (parked), obseq2 sorries.
