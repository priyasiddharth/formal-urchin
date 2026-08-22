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

## 2026-08-18 → 2026-08-21
**Session:** (terminal, multi-leg) — obseq3 compiler-correctness proof arc
**Theme:** drove the obseq3 proof audit from 7 named sorries to 5, with
every closed shape end-to-end: the ρt-transport family, regime A, the
mirlite deref-read alignment, and all of regime D.
**Key outputs:**
- `proof/permsim_transport.lean` — the ρt-transport family: BRIDGE 3
  `sb_write_respects_PermSim` (2026-08-18), then
  `sb_read_respects_PermSim` + `sb_die_respects_PermSim` (2026-08-19).
  Covers exactly the three SB ops that do NOT mint tags; generic
  `ListRel` transports + `TagRenameWF.beq_eq` are the workhorses.
- BRIDGE 2 `writeThroughPtr_sim` + `SourceMemSim.writeWordSeq_extend`
  (common.lean §G) and `placeToRegChecked_emits_preserves_mem` (§E) —
  all common.lean sorries closed (`c6f413e`).
- REGIME A `const_write_local_existing_simulation` (`17f3ee9`) — the
  first end-to-end statement simulation, and obseq2's long-parked
  "Step 4 regime-A milestone", now against the corrected `PermSim ρt`
  invariant rather than obseq2's false perms equality.
- mirlite `resolvePlaceAcc` (`33cfbbd`) — deref resolution performs the
  SB read, closing the plan's risk item (a); new `conformance/local/`
  for project-authored witnesses.
- REGIME D complete (`dc835e4`, `8f73b13`): `const_write_deref_local_
  simulation` then the subsuming `const_write_deref_spine_simulation`
  via `loadSpine_lowering_sim` (new `proof/spine.lean`) — every
  all-deref pointer chain of every depth.
- Invariant extensions: `PlaceRegMapBound` conjunct and the
  strengthened `MemValSim` pointer case (non-wildcard stored tags,
  referent range in ρa's domain).
- 8 journal entries (2026-08-18 ×3, 08-19, 08-21 ×3 incl. the keystone
  refactor assessment); dev-log entries 2026-08-18 ×2, 2026-08-21 ×3.
**Critical corrections:**
- The deref divergence was REAL, not a proof artifact: `q := &mut p;
  *p := v; use **q` was source-ok/target-UB, and Miri sides with the
  target. Fixed at the SOURCE (mirlite now reads) rather than weakening
  the theorem — no corpus test had the shape.
- D1's morning claim "existing machinery only, no invariant changes"
  was over-optimistic; two extensions were needed (above), caught in
  the audit rather than by a failure.
- mirlite's deref read was unbounds-checked while the target `Load`
  bounds-checks: unprovable as stated, so the read-side mirror of
  `writeResolvedPlace`'s check went into `resolvePlaceAcc` (Miri's
  dereferenceable requirement). Found by attempting the induction.
**Status:** complete for the shapes claimed; audit at 5 sorries.
Validation each leg: units 14/14 + 37/37, suite pass 77 | fail 0 (117),
differential matched 77 | mismatch 0 | skipped 0, obseq2 green.
**Next-session pickup candidates:** the `sb_ref` transport member — the
single blocker on 3 of the 5 remaining sorries
(`const_write_proj_simulation`, `const_write_deref_nonspine_simulation`,
`CompilerInv_step_ref`); needs the tag-bound WF fact (mapped and stack
tags < `NextTag` on both machines) for injectivity of the ρt extension,
its register-bound half having landed as `PlaceRegMapBound`. Then copy
(bidirectional memory relation + Memcpy exec lemma) and the fresh-local
lockstep-allocation conjunct + `sb_own` transport. Notebook debt: no
W34 digest; W33's proposed `conformance-process-patterns.md` promotion
is still unacted.

## 2026-08-22
**Session:** (terminal) — btf notebook catch-up + the `sb_ref` transport
member
**Theme:** cleared notebook debt (this log was 6 days stale), then landed
the single blocker on 3 of the audit's 5 remaining sorries.
**Key outputs:**
- `sb_ref_respects_PermSim` (`0585823`) — BRIDGE 3 family complete;
  `TagRenameBounded` + its extension lemmas (`TagRenameWF.extend`,
  `TagRenameIncr.extend`, `TagRenameBounded.extend`/`.mono`);
  `insertAboveContent` and `refCellOp` factored in sb.lean;
  `refCellContent`/`refCellStep` + their transports;
  `foldCellsIdx_ok_of_cells`.
- journal/2026-08/2026-08-22-sb-ref-transport.md; dev-log increment 26;
  audit and parked-backlog entries rewritten around the new frontier.
- The Aug 18→21 catch-up entry above (bridges, regime A, deref-read,
  regime D), which had never been logged.
**Critical corrections:** none this leg. The one design judgement worth
recording: `sb_ref_unfold` (a hand-written match equal to `sb_ref`'s
`do`-block) was abandoned rather than forced — two textually identical
matches are not defeq, and factoring the model dissolved the need for the
lemma entirely.
- `TagRenameBounded` WIRED into `CompilerInv` as an eighth conjunct
  (same session, follow-up): `sb_write_NextTag`/`sb_read_NextTag`/
  `sb_die_NextTag` counter framing, two counter conjuncts on
  `loadSpine_lowering_sim`, and the obligation discharged at both
  `CompilerInv` construction sites (regime A, deref spine). The `sb_ref`
  member is now applicable at a leaf. journal/2026-08/
  2026-08-22-tagrenamebounded-wired.md; dev-log increment 27.
- `sb_own_respects_PermSim` (same session, second follow-up) — BRIDGE 3
  now COMPLETE over all five range ops. Reused the `sb_ref` extension
  algebra verbatim and compiled first try, confirming the same-day [HYP];
  needed no model factoring (`ownCell` was already a named cell op) and
  one new bridge, `foldCells_ok_iff_foldCellsIdx_ok`, because `ownCell`
  is the only cell op that succeeds on a MISSING stack. journal/2026-08/
  2026-08-22-sb-own-member.md; dev-log increment 28.
- `AllocLockstep` wired as the NINTH `CompilerInv` conjunct (same
  session, third follow-up): `mirlite_writeWordSeq_addrStart` /
  `oseair_writeWordSeq_addrStart` framing, `AllocLockstep.writeWordSeq`,
  `AllocLockstep.allocate_eq`. The spine needed no change (it never
  touches memory). journal/2026-08/2026-08-22-alloclockstep-wired.md;
  dev-log increment 29.
**Status:** complete. Audit stays at 5 sorries — no leaf closed, but for
the first time NONE of the five is waiting on a missing lemma; every
remaining sorry is leaf-local proof work. Suite/differential/units unchanged throughout; closed leaves
stay axiom-clean.
**Next-session pickup:** loose-ends/parked.md → "obseq3 proof closure" →
`CompilerInv_step_ref` (the leaf's own work: `Borrow` fragment execution,
`MemValSim` for the stored `ptrVal` under the extended ρt, BRIDGE 2 for
the `RStore`), then the two `Borrow`-emitting const_write regimes.
Regime B is also open and fully unblocked (invert `allocateBase`, execute
the `Alloc` fragment, extend `SourceMemSim`/`LocalBindingSim`); note it
will be the third `CompilerInv` construction site, so wire any further
conjunct BEFORE closing it if one is coming. Also
still open: W34 digest, and W33's proposed
`conformance-process-patterns.md` promotion.
