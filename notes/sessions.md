# Sessions log

Curated index of significant sessions, OLDEST FIRST — append new
entries at the END. For a cold start, read the LAST entry.

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
- REGIME B CLOSED — `const_write_fresh_local_simulation` (same session,
  fourth follow-up): the fresh-local constant write, `Alloc; CStore`,
  growing BOTH renames. Added the tenth `CompilerInv` conjunct
  `UnboundLocalsUnmapped` (LocalBindingSim's converse — without it
  nothing says the fragment starts with the root `Alloc`) plus
  `runN_Assgn_Alloc_step`, `ensureLocalRegE_fresh`,
  `compileStmt_local_fresh_run`, `AddrRenameMap.extend`,
  `SourceMemSim.rename_mono`. journal/2026-08/2026-08-22-regime-b-closed.md;
  dev-log increment 30.
- REF REGIME L→L CLOSED — `ref_local_local_simulation` (same session,
  fifth follow-up), after a model-level wall: `obseq.TyVal`'s derived
  `BEq` was an opaque `partial def`, making every `RStore` step
  unprovable. User chose the hand-written structural `BEq` + `LawfulBEq`
  (obseq/types.lean, `f9a9228`); `deriving DecidableEq` refuses nested
  inductives. Also: `LocalBindingSim` block-domain conjunct,
  `runN_Assgn_Borrow_step`, `runN_RStore_step`, and the finding that the
  ref fragment has NO `Die` for a local destination (no BRIDGE 1 needed).
  journal/2026-08/2026-08-22-rstore-tyval-blocker.md and
  2026-08-22-ref-ll-closed.md; dev-log increment 31.
- ZST, both gaps CLOSED (sixth follow-up): loader keeps unit assignments
  as `uninit` inits (`a36f0a3`); target `Rhs.Borrow` check is now the
  range form; `ref_zst_residual` deleted (audit 6 → 5);
  `local/zst_ref` PASSES, differential 78/0/0. The StorageLive [HYP] was
  REFUTED by rustc (E0381) for the union-free fragment; probe registered
  `unsupported: unions`. journal/2026-08/2026-08-22-zst-loader-gap-fixed.md,
  2026-08-22-zst-both-gaps-closed.md; dev-log increments 31–32.
**Status:** complete. Audit 5 → 4 → 6 → 5. All remaining sorries are
leaf-local proof work; the SB machinery is complete and every known
model divergence is closed.
**Critical corrections (user):** none — but two decisions were the
user's and were made explicitly: the `BEq` fix (option 1 of 3) and,
implicitly, that the ZST divergence stays parked rather than being
patched into the target. Suite/differential/units unchanged throughout; closed leaves
stay axiom-clean.
**Next-session pickup:** loose-ends/parked.md → "obseq3 proof closure" →
`ref_fresh_dst_residual` (regime B ∘ L→L, all pieces exist), then the two
`Borrow`-emitting const_write regimes, then `ref_place_residual`.
Note `CompilerInv` now has THREE construction sites (regimes A, B and the
deref spine), so wire any further conjunct before closing another leaf. Also
still open: W34 digest, and W33's proposed
`conformance-process-patterns.md` promotion.

## 2026-08-23
**Session:** (terminal, continued) — ref fresh-destination regime
**Theme:** closed the last non-place ref regime; first statement whose
ρt extends twice.
**Key outputs:**
- `ref_fresh_dst_simulation` — `&src` into an UNBOUND local, fragment
  `Alloc; Borrow; RStore`, both renames growing (ρt TWICE via `sb_own`
  then `sb_ref`). Audit 5 → 4.
- `compileStmt_ref_fresh_local_run`/`_value`, `prepare_lookup_ne`,
  `layout_ne_ptrL`/`ref_dst_src_idx_ne`, `getPlaceInfo_setNextReg`.
- journal/2026-08/2026-08-23-ref-fresh-dst-closed.md; dev-log
  increment 33.
**Critical corrections:** none from the user. Self-caught: the fragment
closed form omitted the `nextReg` bump `freshRegM` performs between the
`Alloc` and the `Borrow` — the signature was a final `simp` leaving
`⊢ False` rather than a rewrite failure.
**Status:** complete. `CompilerInv_step_ref` has one residual left
(`ref_place_residual`); audit at 4.
**Next-session pickup:** `const_write_proj_simulation` /
`const_write_deref_nonspine_simulation` — the first leaves to need
BRIDGE 1 (an internal `Borrow` WITH a `Die` cleanup), a shape no closed
regime has yet. Then `ref_place_residual`, then `CompilerInv_step_copy`
(the only remaining sorry needing new machinery).

## 2026-08-27
**Session:** (terminal, continued) — regime C, and BRIDGE 1's first use
**Theme:** closed the projected-destination leaf for a bound-local base;
the keystone finally carries weight.
**Key outputs:**
- `const_write_proj_simulation` split by OFFSET: C0
  (`const_write_proj_zero_simulation`, bare `CStore`) and C1
  (`const_write_proj_offset_simulation`, `Borrow; CStore; Die`) — the
  first consumer of BRIDGE 1, twelve days after it was proved.
- `sb_ref_Mut_ok_of_sb_write_ok` and `freshTag_not_protected`: BRIDGE 1's
  two side conditions, both DERIVED from the invariant rather than
  assumed. Plus `runN_Die_step`, `ListRel.mem_right`,
  `TagListSim.mem_range`, `compileStmt_proj_zero_run`/`_offset_run`.
- journal/2026-08/2026-08-27-regime-c-closed.md; dev-log increment 34.
**Critical corrections:** none from the user. Self-caught: twice placed
new theorems BEFORE the lemmas they call (the file is order-sensitive and
the errors read as "unknown identifier", not as a placement problem).
**Status:** complete. Audit stays at 4; the C residual narrowed to a
non-local base.
**Next-session pickup:** `const_write_deref_nonspine_simulation` and
`const_write_proj_nonlocal_residual` are now the SAME shape (base
lowering emits code + a cleanup LIST) — do them together via
`runN_cleanupInstrs` ∘ BRIDGE 1. Then `ref_place_residual`, then
`CompilerInv_step_copy`.

## 2026-08-27 (later)
**Session:** (terminal, continued) — the nested-projection divergence,
found by proof and fixed by design
**Theme:** attempting the two nested residuals refuted them; the user
chose the fix (GEP stays a borrow, narrowed to the field); implemented as
proj-chain REASSOCIATION in both lowering functions.
**Key outputs:**
- witness `local/nested_proj_borrow` (`2711f06`) — target UB where the
  source (and Rust) are fine; refuted both nested residual theorems.
- the fix: `PathTo.append` + reassociating arms in
  `placeToRegChecked`/`placeToBorrowRegChecked`, `Place.depth` as the WF
  measure; `projAssoc` evidence constructors.
- proof-stack repair for the structural→WF transition: 6 `:= rfl` →
  equation lemmas, `placeToRegChecked_proj_root_eq`/`_proj_assoc_eq`
  (the conditional/unconditional arm equations), two structural
  inductions → `placeToRegChecked.induct`.
- d26 in compile_tests (teeth verified by reverting the arms).
- journal 2026-08-27-regime-c-closed.md and
  2026-08-27-nested-proj-reassoc.md; dev-log increments 34–35.
**Critical corrections (user):** keep GEP as a borrow — do NOT add an
access-free FieldPtr instruction; narrow the borrow to the field instead.
Implemented via reassociation, which achieves the narrowing with no new
instruction.
**Status:** complete. Audit at 4; the two nested residuals are TRUE
again and narrower (deref-rooted only). Suite 81/122, differential
81/0/0, units 15/15 + 39/39.
**Next-session pickup:** the deref-rooted residuals together
(`loadSpine_lowering_sim` ∘ C1 pattern + resolvePlaceAcc-offsets-add),
then `ref_place_residual`, then `CompilerInv_step_copy`.

## 2026-08-27 (night)
**Session:** (terminal, continued) — the deref-rooted residuals
**Theme:** BRIDGE 1S + both mixed proj⊗deref leaves; the nonspine
residual became a proved dispatcher.
**Key outputs:**
- `sb_ref_read_die_cancels` (BRIDGE 1S, generated by adapting the Mut
  keystone) + `readCellContent_top_ref` + `sb_ref_Shared_ok_of_sb_read_ok`.
- `const_write_proj_deref_simulation` (`(*p).f := v`, any spine) and
  `const_write_deref_proj_simulation` (`*(s.f) := v`), with fragment
  closed-forms `compileStmt_proj_deref_run`/`compileStmt_deref_proj_run`.
- dispatchers wired; `const_write_deref_deep_residual` names what's left.
- journal 2026-08-27-deref-rooted-closed.md; dev-log increment 36.
- parked: Cslib/Mathlib adoption (paper-facing repackaging).
**Critical corrections:** none from the user. Self-caught: a chunked
edit DELETED the adjacent C-deref theorem (end marker `· simp at h_w`
matched in the next proof; build stayed green minus one theorem) — found
by name-grep, reassembled from the session's patches. New rule: slice
edits get a theorem-name grep afterwards; splice markers must be unique.
**Status:** complete. Audit at 4 (deep chains, narrowed proj-nonlocal,
copy, ref-place); suite 82/123, differential 82/0/0, units 15/15+42/42.
**Next-session pickup:** `ref_place_residual` via the closed regime
patterns, or copy (bidirectional memory relation + Memcpy lemmas). The
deep-chain residual wants the pending-cleanup spine generalization.

## 2026-08-27 (late night)
**Session:** (terminal, continued) — ref regime P→L
**Theme:** `dst := &kind s.f` closed; two distinct blockers identified
and recorded for what remains of `ref_place_residual`.
**Key outputs:**
- `PathTo.offset_add_size_le` (syntax.lean) — the field-fits-its-layout
  typing bound; the only closed regime whose `Borrow` bounds obligation
  has NO semantic source.
- `compileStmt_ref_proj_local_run`/`_value`,
  `ref_proj_local_simulation`; dispatcher wired.
- Findings: (a) deref sources blocked on mirlite lacking Miri's
  retag-dereferenceable check (own parked entry — model decision);
  (b) non-local destinations need an interleaved-keystone commutation
  argument.
- journal 2026-08-27-ref-proj-closed.md.
**Critical corrections:** none.
**Status:** complete. Audit at 4; suite 82/123, differential 82/0/0,
units 15/15 + 42/42.
**Next-session pickup:** `CompilerInv_step_copy` (bidirectional memory
relation + Memcpy lemmas), or the mirlite retag check if approved.

## 2026-08-28
**Session:** (terminal, continued) — the event fix
**Theme:** mirlite `.ref` gains Miri's retag-dereferenceable check
(user-approved); the invariant-gap example pinned as tests.
**Key outputs:**
- the check (range form, ZST-admitting) in mirlite_semantics.lean;
  behaviour on reachable states unchanged (suite 82/123, differential
  82/0/0); three ref regimes repaired with one `if_neg` each.
- t16: the junk state (`ptrVal _ _ 0` at pointee u64) encoded as DATA —
  the suite's first STATE-level test; teeth verified by reverting the
  check. d30 (reachable reborrow) + d31 (ZST reborrow) cover the other
  corners. Units 16/16 + 44/44.
- journal 2026-08-28-retag-deref-check.md; parked entry resolved.
**Critical corrections:** none.
**Status:** complete. Audit at 4; deref-source ref regime unblocked,
leaf still to prove.
**Next-session pickup:** the deref-source ref leaf (now provable), or
`CompilerInv_step_copy`.


## 2026-08-28 (later)
**Session:** (terminal, continued) — regime D→L
**Theme:** the deref-source ref leaf closed — the event fix pays off.
**Key outputs:**
- `compileStmt_ref_deref_run/_value`, `ref_deref_local_simulation`
  (spine prelude + P→L endgame; Borrow bound from the retag event
  check via MemValSim's o/s equalities); dispatcher splits on
  `LoadSpine`; residual narrowed to non-spine/unbound/non-local/
  proj-of-proj shapes.
- grind pass over the new theorem (h_cancel/h_offP/h_le2/h_dr2 etc.).
- journal 2026-08-28-ref-deref-closed.md; audit entry 4 updated;
  dev-log increments 37 (event fix, backfilled) + 38.
**Critical corrections:** none.
**Status:** complete. Audit at 4; suite 82/123, differential 82/0/0,
units 16/16 + 44/44.
**Next-session pickup:** `CompilerInv_step_copy`, or the deep-chain
spine generalization (shared blocker of const_write deep + non-spine
deref refs).

## 2026-08-28 (evening)
**Session:** (terminal, continued) — copy L→L
**Theme:** `CompilerInv_step_copy` becomes a proved dispatcher; the
predicted bidirectional-memory blocker dissolves into a MemValSim
weakening.
**Key outputs:**
- `MemValSim` undef row weakened to undef-refines-anything (sound:
  observers err on undef); zero downstream proof edits.
- `readWordSeq_sim`, `runN_Memcpy_step` (common.lean);
  `compileStmt_copy_local_local_run/_value`,
  `copy_local_local_simulation`, `copy_place_residual` (copy.lean).
- journal 2026-08-28-copy-ll-closed.md; audit entry 3 updated.
**Critical corrections:** none.
**Status:** complete. Audit at 4; suite 82/123, differential 82/0/0,
units 16/16 + 44/44.
**Next-session pickup:** the pending-cleanup spine generalization
(shared blocker of const_write deep chains, non-spine deref refs, and
now non-local copy shapes), or copy P-src (proj offset, bounds by
typing — likely the cheapest remaining leaf).

## 2026-08-28 (night)
**Session:** (terminal, continued) — axiom-audit tooling
**Theme:** machine-checked whitelist audit of the main theorem's
axioms and sorries, per user request; rooted at `compile_correct` on
the user's direction (not a whole-project sweep).
**Key outputs:**
- scripts/axiom_audit.lean (collectAxioms closure vs whitelist; DFS
  sorry-root pin vs the 4 audited residuals), scripts/audit_axioms.sh;
  teeth-verified all three failure modes; CLAUDE.md validation wiring.
- journal 2026-08-28-axiom-audit-tooling.md.
**Critical corrections:** teeth-check #3 was initially a silent no-op
splice (un-asserted replace); pipe-masked exit codes on the first two.
**Status:** complete. Audit green: 4 axioms, 4 pinned sorries.
**Next-session pickup:** unchanged — pending-cleanup spine
generalization, or copy P-src.

## 2026-08-28 (late night)
**Session:** (terminal, continued) — copy P-src
**Theme:** zero-offset proj-src copy closed; nonzero offset PROVEN
blocked (countermodel), separation invariant proposed and parked.
**Key outputs:**
- `compileStmt_copy_proj_zero_run/_value`, `copy_proj_zero_simulation`
  (P0→L: bare Memcpy, bounds by typing); dispatcher splits on
  `pathOffset = 0`; d32 differential test (45/45).
- The nonzero-offset countermodel: `[Borrow(Shared); Memcpy; Die]`
  interleaves the dst useMut between BRIDGE-1S phases; overlap-junk
  states make the leaf FALSE — needs a SEPARATION conjunct (parked,
  user decision; would also unlock the non-local-dst residuals).
- journal 2026-08-28-copy-p0-closed.md; audit entry 3 updated.
**Critical corrections:** none.
**Status:** complete. Audit at 4; suite 82/123, differential 83/0/0,
units 16/16 + 45/45; axiom audit green.
**Next-session pickup:** the separation conjunct if approved (biggest
unlock), else the pending-cleanup spine generalization.

## 2026-08-28 (later still)
**Session:** (terminal, continued) — countermodel as a test
**Theme:** d33 pins the overlap divergence (user-requested example).
**Key outputs:** d33_overlap_junk_copy_diverges — forged two-machine
junk state; source copy ok, target [Borrow;Memcpy;Die] errs at Die;
teeth: un-forging the overlap flips the target to success. 46/46.
**Critical corrections:** stale-olean teeth run (rebuild first!);
`git checkout` ate the uncommitted test (recovered from session).
**Status:** complete; audit green.

## 2026-08-28 (night, cont.)
**Session:** (terminal, continued) — the deref divergence example
**Theme:** d34: FIRST reachable divergence — the lowering-order bug.
**Key outputs:** d34_deref_dst_temp_killed_by_rhs_spine (differential,
source .ok vs target .ub 5, confirmed by execution on first run);
journal 2026-08-28-lowering-order-bug.md with the three-class
divergence taxonomy; parked entry (fix = MIR's rhs-first order).
**Critical corrections:** none.
**Status:** complete. 47/47 units; suite 82/123; audit green.
**Next-session pickup:** user decisions queued: (a) lowering-order fix
(compiler change, unlocks non-local-dst residuals), (b) copy overlap
event check, (c) separation conjunct.

## 2026-08-28 (night, cont. 2)
**Session:** (terminal, continued) — the lowering-order fix
**Theme:** compiler fixed to MIR's order; d34 flips to agreement.
**Key outputs:**
- compile.lean: `RhsPre` + `compileRExprPreChecked` split; assign-place
  arm (and compileAssignChecked twin) lower rhs BEFORE dst; rhs streams
  unchanged, so closed-regime statements survived.
- d34 → expectDiff .ok (reversion teeth verified: old order → .ub 5).
- Proof fallout tiny (defeq monad laws); emit_nil relocated; new
  pothole recorded: bare `lake build` builds only Core — validate with
  explicit targets.
- journal 2026-08-28-lowering-order-fix.md; parked entry RESOLVED.
**Critical corrections:** the "full build 0 errors" sweeps before the
audit wrapper caught the breakage were vacuous (default-target trap).
**Status:** complete. All targets green; suite 82/123; units 16/16 +
47/47; axiom audit exact; audit at 4.
**Next-session pickup:** copy overlap event check (b) and/or the
separation conjunct (c) — the remaining unlocks for the residuals.

## 2026-08-28 (night, cont. 3)
**Session:** (terminal, continued) — the copy overlap event check
**Theme:** overlapping assignment is UB on both machines; d33 retired,
d35 pins the reachable case; separation invariant demoted.
**Key outputs:**
- mirlite doAssign overlap guard (copy branch only, via doAssignCont
  split; access-free resolver) + oseair Memcpy nonoverlapping check;
  runN_Memcpy_step gains h_disj; both copy leaves supply it from the
  guard. Teeth both sides. d33 → both-refuse pin; d35 differential.
- Residual/audit/parked docs: all remaining copy shapes UNBLOCKED;
  separation conjunct likely unnecessary.
**Critical corrections:** git-checkout-during-teeth destroyed
uncommitted edits AGAIN — rule upgraded (inverse-edit reverts only).
**Status:** complete. All targets; suite 82/123; units 16/16 + 48/48;
axiom audit exact; audit at 4.
**Next-session pickup:** the disjoint-range commutation lemma +
BRIDGE 1S composition (nonzero-offset copy P-src leaf), now that
nothing blocks it.

## 2026-08-28 (small hours)
**Session:** (terminal, continued) — commutation attempt
**Theme:** the disjoint-range commutation is true at find?-level but
unstatable under PermSim's positional ListRel + move-to-front SB.set —
the parked assoclist tradeoff realized. Three routes written up
(find?-quotient PermSim / stable SB.set / PtrOffset lowering);
user decision requested.
**Status:** paused at the fork; no code changed.

## 2026-08-28 (early)
**Session:** (terminal, continued) — the quotient, the slide, the leaf
**Theme:** route (a) executed: find?-quotient PermSim (StackMapSim) +
disjoint-range commutation; nonzero-offset copy P-src CLOSED.
**Key outputs:**
- common.lean: StackMapSim (+find?_some/none/imp/congr_right); PermSim
  stacks conjunct quotiented; zero downstream breakage.
- keystone.lean: chain_key_not_mem, sb_write_congr,
  sb_die_sb_write_comm (find?-level commutation).
- permsim_transport.lean: toolkit reshaped (find?_transport/set_respects
  /setChain_chain_respects at find?-level); sb_write_frames.
- copy.lean: compileStmt_copy_proj_offset_run/_value,
  copy_proj_offset_simulation; dispatcher fully split on pathOffset;
  d36 differential (49/49).
- journal 2026-08-28-copy-p-offset-closed.md (incl. new potholes:
  grind spelling-atoms, mid-script assert loses earlier edits,
  of_cells op-pinning).
**Critical corrections:** lean_verify served a stale sorryAx report
right after rebuild — cross-checked with #print axioms.
**Status:** complete. Audit at 4; all suites green; axiom audit exact.
**Next-session pickup:** copy deref-src (spine composition over the
same pieces), or the non-local-dst BRIDGE-1 compositions.

## 2026-08-28 (cont.)
**Session:** (terminal, continued) — copy deref-src
**Theme:** the read-side event fix (copy-range dereferenceability) +
regime D→L closed; copy done on all spine-shaped sources.
**Key outputs:**
- mirlite .copy range check (t17-pinned, teeth via inverse edit; the
  overlap guard incidentally caught the self-copy-through-pointer
  shape first); three one-line if_neg repairs in the closed leaves.
- resolvePlace?_of_resolveAcc (spine.lean); copy_deref_local_simulation
  + fragment lemmas; dispatcher split on LoadSpine; d37 differential.
- journal 2026-08-28-copy-deref-closed.md; audit entry 3 narrowed.
**Critical corrections:** none new (inverse-edit teeth rule held).
**Status:** complete. Audit at 4; units 17/17 + 50/50; suite 82/123;
axiom audit exact.
**Next-session pickup:** non-local-dst BRIDGE-1 compositions (largest
remaining class, shared across all three dispatchers), or const_write
deref-deep (pending-cleanup spine generalization).

## 2026-08-28 (cont. 2)
**Session:** (terminal, continued) — non-local dst class, part 1
**Theme:** the flattening recursion (stmt0-generalized leaves +
reassociation mirrored source-side) + the zero-offset deref leaf;
const_write's proj residual down to unbound roots + non-spine chains.
**Key outputs:** stmt0 triples on C0/C1/C-deref/D-spine;
resolvePlaceAcc/resolvePlace?/prepare _proj_assoc (spine.lean);
compileStmt_assign_proj_assoc_run/_value; const_write_proj_simulation
as base-induction; const_write_proj_deref_zero_simulation (+fragment);
d38/d39 (52/52). Audit entries 2 updated.
**Status:** complete; all green; audit at 4.
**Next-session pickup:** ref/copy non-local-dst arms (same recipe:
stmt0-generalize + flatten), or regime-B unbound roots.

## 2026-08-29 (cont. 3)
**Session:** (terminal, continued) — ref non-local dst, part 1
**Theme:** L→P0 closed (`dst.g := &src` @0) — ref's first non-local
destination; fragment lemmas learn the MIR-order state discipline
(base facts at the post-rhs compiler state).
**Key outputs:** compileStmt_ref_projzero_local_run/_value,
ref_local_projzero_simulation, dispatcher proj-dst arm, d40 (53/53).
**Status:** complete; all green; audit at 4.
**Next-session pickup:** the NONZERO field dst (BRIDGE 1 composition
with the rhs ρt extension).

## 2026-08-29 (cont. 4)
**Session:** (terminal, continued) — ref non-local dst, part 2
**Theme:** L→P closed (nonzero field dst) — the two-mint leaf; BRIDGE 1
composed under the rhs-extended rename, first-try build.
**Key outputs:** compileStmt_ref_projoffset_local_run/_value,
ref_local_projoffset_simulation, dispatcher wiring, d41 (54/54).
**Status:** complete; all green; audit at 4.
**Next-session pickup:** ref dst flattening recursion (stmt0 triples)
+ deref dsts; or copy's non-local dst arms (same recipe).

## 2026-08-29
**Session:** (terminal, continued) — ref dst flattening
**Theme:** nested projection dsts closed for ref via the ported
statement-transfer recursion; transfer lemmas relocated to common.
**Key outputs:** stmt0 triples on both field-dst leaves;
stepStmt_assign_proj_assoc (3-line step-level source transfer);
ref_proj_dst_simulation; dispatcher proj-dst arm = one call; d42
(55/55); residual h_stmt loosened.
**Status:** complete; all green; audit at 4.
**Next-session pickup:** deref dst bases for ref ((*p).f := &x — spine
composition), or copy's non-local dst arms (recipe ready).

## 2026-08-29 (cont.)
**Session:** (terminal, continued) — rhs-first doAssign swap
**Theme:** SEMANTICS CHANGE (flagged): mirlite doAssign moved to
Rust's rhs-before-place order — source-side completion of d34;
prerequisite for ref's deref dsts (rhs retag vs dst-spine read don't
commute). Repair sweep ~28 errors, all mechanical (dst match reduces
late: h_envD, or hD1 in fresh-dst regime; copy guard moves post-read).
**Key outputs:** doAssign swap (doAssignCont unreferenced); repairs in
ref/copy/const_write; journal 2026-08-29-rhs-first-doassign.md; dev
log increment 50.
**Status:** complete; all green; corpus byte-identical 82/123 (0
fail); units 17/17 + 55/55; audit at 4.
**Next-session pickup:** ref's deref dsts (`*p := &src` bare leaf +
`(*p).f := &src`), dispatcher wiring, differential witness d43.

## 2026-08-29 (cont. 2)
**Session:** (terminal, continued) — ref deref dst + grind audit
**Theme:** `*P := &src` closed over any load spine (the regime the
rhs-first swap unblocked); loadSpine_lowering_sim gains a
register-frame conjunct (borrow temp crosses the spine); grind audit
of the delta since 09d5472 (10 sites collapsed, 1 rejection).
**Key outputs:** compileStmt_ref_derefdst_run/_value,
ref_derefdst_local_simulation, dispatcher deref-dst arm, residual
narrowed, d43 (56/56), journal 2026-08-29-ref-derefdst-closed.md.
**Status:** complete; all green; corpus 82/123 (0 fail); audit at 4.
**Next-session pickup:** projected deref dsts (`(*p).f := &x`) or
copy's non-local dst arms (transfer recipe ready).

## 2026-08-29
**Session:** (terminal, continued) — the deep-chain blocker's core
**Theme:** `PtrChain` + `ptrChain_lowering_sim` land (plan increments
1+2): the pending-cleanup spine generalization via one BRIDGE-1S
triple per proj-under-deref level; pending list is provably ≤ 1 entry
by the lowering's own discipline. Interface: +h_tbd, target counter
`=`→`≤`, all else verbatim (PermSim at unextended ρt — the tags die).
**Key outputs:** PtrChain, PtrChain.not_proj, LoadSpine.toPtrChain,
ptrChain_lowering_sim (4 cases; derefProj = depth-1 endgame in the
induction); 5 consumers migrated (h_pnt2 rewrites → mono closers);
loadSpine_lowering_sim retired; journal
2026-08-29-ptrchain-mother-lemma.md.
**Status:** complete; all green; corpus 82/123 (0 fail); audit at 4
(unchanged — coverage widens at wiring).
**Next-session pickup:** the wiring increment — nonspine dispatchers
on PtrChain, depth-1 proj-top leaves generalized to chain bases, d44
witness (`*((*q).f) := v`), residual docstrings + compiler.lean audit.

## 2026-08-29 (cont.)
**Session:** (terminal, continued) — chain wiring
**Theme:** dispatchers + leaves re-gated LoadSpine → PtrChain (one
mechanical pass, first build green); LoadSpine retired; all-chain
pointer places (interior projs, any depth) now route to closed leaves
across const_write/copy/ref. d44 (`*(*(s.f)) := v`) + d45 (ref
sibling) pin the new coverage (58/58).
**Status:** complete; all green; corpus 82/123 (0 fail); audit at 4.
**Next-session pickup:** proj-TOP bases (`*((*q).f) := v` — generalize
const_write_deref_proj_simulation to chain bases via a mother-lemma
call), then proj-of-proj normalization, unbound roots.

## 2026-08-29 (cont. 2)
**Session:** (terminal, continued) — chain-dst leaf; subsumption
**Theme:** const_write_deref_chain_simulation (dst gated as
`PtrChain (.deref P)`, mother lemma at Mut on the WHOLE dst) SUBSUMES
the D-spine + depth-1 proj-top leaves (~750 lines deleted). Process
documented per user request: durable note
chain-leaves-gate-on-the-whole-place (4-step narrative + reusable
heuristic).
**Key outputs:** compileStmt_derefdst_run/_value, the chain-dst leaf,
dispatcher regated, nonspine collapsed to 3 arms, 4 dead theorems
removed, d46 (59/59), deep residual narrowed to proj-of-proj +
unbound roots.
**Status:** complete; all green; corpus 82/123 (0 fail); audit at 4.
**Next-session pickup:** apply the same collapse to copy D→L and ref
deref-src/deref-dst (they still hand-run the final Load); then
proj-of-proj normalization inside chains; unbound roots.

## 2026-08-29
**Session:** (terminal, continued) — the collapse travels
**Theme:** copy D→L + ref deref-dst re-founded on the whole-place
mother lemma (Shared on the src / Mut on the dst from post-Borrow);
~500 more lines deleted; chain srcs and deref-dst chains closed
(d47 `y := copy *(s.f)`, d48 `*(t.f) := &x`; 61/61).
**Key outputs:** compileStmt_copy_derefchain_run/_value,
compileStmt_ref_derefdst_run/_value (opaque-run forms),
resolvePlaceAcc_local (targeted reduction keeping siblings opaque),
dispatchers regated to PtrChain (.deref _), residual docstrings
narrowed.
**Status:** complete; all green; corpus 82/123 (0 fail); audit at 4.
**Next-session pickup:** ref deref-src collapse (borrow-deref bind
equation), proj-topped srcs/dsts over non-local bases, proj-of-proj
normalization, unbound roots (regime-B → first residual to zero).

## 2026-08-29 (cont.)
**Session:** (terminal, continued) — deref-src collapse; three-for-three
**Theme:** ref deref-src re-founded on the mother lemma (no bind
equation needed — one inner-value case split proves the fragment; the
statement run lemma needs only ok-ness, killing the incr dance). New
mother conjunct: ρa allocBase identity (ZST-referent gap in h_drange).
d49 `q := &mut *(s.f)` (62/62).
**Status:** complete; all green; corpus 82/123 (0 fail); audit at 4.
**Next-session pickup:** proj-topped srcs/dsts over non-local bases,
proj-of-proj normalization, unbound roots (regime-B).

## 2026-08-29 (cont. 2)
**Session:** (terminal, continued) — flattenPlace; FIRST RESIDUAL DIES
**Theme:** flattenPlace + congruence family (source ops + compiled
lowering agree with the flattening); flatten_chainish → every deref
dst is a chain after normalization; regime D total; deep residual +
nonspine dispatcher DELETED; whitelist 4 → 3 sorries (audit-pinned in
the same commit). d50 (63/63).
**Status:** complete; all green; corpus 82/123 (0 fail); audit at 3.
**Next-session pickup:** flatten transfer for the C-deref proj-dst
gates + copy/ref dispatchers (cheap); then regime-B unbound roots →
kill const_write_proj_nonlocal_residual.

## 2026-08-29
**Session:** (terminal, continued) — flatten transfer to copy/ref
**Theme:** all deref dispatch arms TOTAL for bound roots: 3 source
statement congruences, stmt0 surgery on the 3 collapsed leaves,
compiled statement pairs per shape (4-way agree alignment; valunit
currency; ref-src via the borrow-deref shared prefix + INNER agree).
d51 (64/64).
**Status:** complete; all green; corpus 82/123 (0 fail); audit at 3.
**Next-session pickup:** regime-B unbound roots (kills
const_write_proj_nonlocal) or C-deref collapse+flatten (proj-dst
gates); then copy/ref proj-topped and unbound classes.

## 2026-08-29
**Session:** (terminal, continued) — C-deref collapse + proj-dst deref arm total
**Theme:** both C-deref leaves collapsed onto the mother at `Mut
(.deref P)` (gate `PtrChain (.deref P)`; fragments restated over the
opaque dst run; `resolvePlaceAcc_proj_base_ok/_err` keep the chain
opaque); dispatcher deref arm TOTAL via
`compileStmt_const_projderef_flatten_run/_value` +
`PtrChain_flatten_deref`. Residual narrowed to UNBOUND ROOTS only.
Potholes: omega ignores Word-typed hypotheses (launder through Nat.*
lemmas or grind); pathOffset/PathTo.offset are distinct atoms;
dst-generic compiled flatten transfers are unstatable (match stuck on
the .local arm). d52+d53 (66/66), teeth via broken Borrow offset.
**Status:** complete; all green; corpus 82/123 (0 fail); audit at 3.
**Next-session pickup:** regime-B unbound roots (allocateRoot + the
fresh-block C0/C1 endgames) → const_write_proj_nonlocal_residual to
ZERO, whitelist 3 → 2; then copy/ref remaining classes.

## 2026-08-29 (later)
**Session:** (terminal, continued) — regime B-proj closes the second residual
**Theme:** `const_write_proj_nonlocal_residual` DELETED (whitelist 3→2).
Fresh fragments (`compileStmt_proj_fresh_zero_run/_offset_run/_value`)
over `ensureLocalRegE_fresh` + post-`setPlaceInfo` local lowering; leaf
`const_write_proj_fresh_simulation` = fresh-local §1–§3 at `blockSize σ`
+ C0/C1 endgames on the fresh block (Borrow bound from
`PathTo.offset_add_size_le`). NEW: `AddrRenameMap.extendIdRange` —
block-wide identity ρa extension (block-domain conjunct + nonzero-offset
writes need every cell, not just the base). d54 (67/67), teeth via
undersized root Alloc.
**Status:** complete; all green; corpus 82/123 (0 fail); audit exact at 2.
**Next-session pickup:** copy residual classes (proj-topped srcs over
non-local bases, unbound dst, non-local dst — BRIDGE 1 composition) and
ref residual classes (proj-topped dsts over non-local bases, non-local
srcs under non-local dsts, unbound roots) → drive to ZERO sorries.

## 2026-08-29 (third)
**Session:** (terminal, continued) — copy proj-src collapse
**Theme:** `copy_projchain_zero/offset_simulation` (gate `PtrChain B`
for src `.proj B path`) subsume the old bound-local-base P0/P→L leaves
AND `y := copy (*p).f`; src flatten transfer
(`stepStmt_assign_copysrc_anyflatten`, src-generic compiled pair,
`flatten_proj_chainish`) makes the whole proj-src dispatcher arm TOTAL
for bound dsts. 617 lines deleted. Potholes: `set` is Mathlib-only (not
available here); dependent evidence types transport only under an
EXISTENTIAL; record-update projections block `rw [if_pos]` (normalize
with any real rewrite first). d55+d56 (69/69), teeth via mis-pointed
Memcpy.
**Status:** complete; all green; corpus 82/123 (0 fail); audit at 2.
**Next-session pickup:** copy's UNBOUND dst (regime-B composition — the
`extendIdRange` machinery is in place) and NON-LOCAL dst
(`Borrow(Mut); Memcpy; Die`) → copy_place_residual to zero; then ref's
classes.

## 2026-08-29 (fourth)
**Session:** (terminal, continued) — copy: chain-src generalization + regime B
**Theme:** `copy_chainsrc_local_simulation` (any `PtrChain src`) retires
L→L (210 lines); `copy_fresh_chainsrc_simulation` closes UNBOUND
destinations for chain sources (root Alloc, then the mother lemma at the
POST-allocation states under extended renames). New:
`AddrRenameMap.extendBlock` (ZST-safe block extension — extendIdRange
alone misses an empty block's base) and `mirlite_readWordSeq_congr`.
Potholes: keep the post-alloc state ABSTRACT (no record literal in a
`cases` scrutinee); `show ….placeRegMap.lookup` blocks
`getPlaceInfo_setPlaceInfo_ne` (use a `h_gp` transport); whole-file
replaces can hit the wrong leaf. d57 (70/70), teeth via undersized Alloc.
**Status:** complete; all green; corpus 82/123 (0 fail); audit at 2.
**Next-session pickup:** unbound dst with a PROJ-TOPPED src (same Alloc
composition, projection endgames), then NON-LOCAL dst
(`Borrow(Mut); Memcpy; Die`) → copy_place_residual to zero; then ref.

## 2026-08-29 (fifth)
**Session:** (terminal, continued) — copy: fresh dst with proj-topped srcs
**Theme:** `copy_fresh_projchain_zero/offset_simulation` = regime-B
prefix (abstract post-alloc state, extendBlock, root Alloc, mother at
the post-alloc states) + the bound-dst projection endgames. With the
chain-src leaf, an UNBOUND destination now accepts every source shape;
`copy_place_residual` is down to NON-LOCAL destinations only. Potholes:
`emit_state_incr` chains must stay term-mode (refine can't synthesize
s2/instrs); register distinctness across the emit tower needs an
explicit bound + injection/omega, not grind. d58 (71/71), teeth via
mis-pointed Memcpy.
**Status:** complete; all green; corpus 82/123 (0 fail); audit at 2.
**Next-session pickup:** copy's NON-LOCAL dst (src lowering, then dst
lowering, Memcpy, two cleanups) → copy_place_residual to ZERO; then
ref's remaining classes.

## 2026-08-29 (sixth)
**Session:** (terminal, continued) — the last copy class is an ORDER mismatch
**Theme:** investigated `copy_place_residual`'s remaining class
(non-local dst) and CORRECTED the standing assessment: it is not
composition work. mirlite performs the copy's range read BEFORE the dst
resolution (rhs-first); the compiled `Memcpy` performs it AFTER the dst
lowering's pointer-cell reads, and SB reads do not commute. The class is
still TRUE — a dst-chain pointer cell inside the source range would need
τ ∋ PtrL σ and σ ↠ PtrL τ, impossible for an inductive LayoutTy — but
closing it needs either a memory well-typedness invariant in
CompilerInv or a compiler change (materialize the source into a temp
before the dst lowering). Durable note:
notes/2026-08-29-copy-nonlocal-dst-order.md.
**Status:** analysis only; no proof change; all green; audit at 2.
**Next-session pickup:** HUMAN DECISION needed (invariant vs compiler
change) for copy's last class; meanwhile ref's classes (proj-topped
dsts over non-local bases, non-local srcs under non-local dsts, unbound
roots) are independent and can proceed.

## 2026-08-30 (discussion)
**Session:** (terminal, same day as the copy increments) — Q&A on ZSTs,
rename extensions, and raw-pointer provenance. No proof delta.
**Theme:** three user questions about `AddrRenameMap.extendBlock`,
coincident ZST addresses, and whether a raw-pointer local has a unique
tag. Each answer was checked against source rather than recalled, and
each turned out to be durable.
**Key outputs:** durable/empty-blocks-need-a-separate-base-fact.md (the
range-vacuity hole and the three leaves it has bitten),
durable/zst-locals-share-addresses-harmlessly.md,
durable/raw-pointer-provenance-is-the-wildcard-tag.md,
journal/2026-08-30-zst-addresses-and-wildcard-provenance.md.
**Critical corrections:** none from the user, but one self-correction
recorded — durable/rho-maps-are-identity-on-domain.md is v2-scoped; in
obseq3 ρt is NOT identity and `PermSim` (listed there as a rejected
alternative) is the adopted design. Scope caveat appended in place
rather than superseding.
**Status:** complete.
**Next-session pickup:** unchanged — see the preceding entries.

## 2026-08-30 (seventh)
**Session:** (terminal, continued) — the temp-assignment lowering
**Theme:** COMPILER + SEMANTICS change, human-approved. copy lowers to
`Load` into a fresh REGISTER (the read, in the rhs pre-phase) then
`RStore` (the write), matching rustc's `_3 = (*_2); (*_1) = move _3`;
`Rhs.Load` now bounds-checks its whole width; mirlite's overlapping-copy
guard REMOVED (Rust permits overlap — Miri runs `*p = *p` clean). All
six copy leaves repaired (Memcpy step → Load + RStore steps, one extra
fresh register in the sim bullets); the offset leaves got SIMPLER — the
Die now precedes the write, so BRIDGE 1S is contiguous and
`sb_die_sb_write_comm` is no longer used. d33 rewritten (both machines
now succeed), d35 flipped to ok, d59 added as the regression pin.
**Status:** complete; all green; 17/17 + 72/72; corpus 82/123 (0 fail);
audit exact at 2.
**Next-session pickup:** copy's NON-LOCAL dst — now plain composition
(two place lowerings + two cleanups) with no ordering obstacle; then
ref's classes.

## 2026-08-30 (eighth)
**Session:** (terminal, continued) — non-local dst: groundwork landed, leaf in flight
**Theme:** with the ordering obstacle gone, started the last copy class.
LANDED (green): `compileStmt_copy_chaindst_run/_value` (the fragment for
a deref dst over the OPAQUE runs of BOTH lowerings — the value form is
stated over the GENERAL src cleanup, since the cleanup is only known
after the mother lemma), `PlaceInputsMapped.placeRegMap_congr`,
`PtrChain.placeToRegChecked_placeRegMap` (a chain's lowering never
touches placeRegMap — needed BEFORE the mother can run, to transfer
mapped-ness past the first lowering; induction on the CHAIN, whose
grammar has no proj-of-proj), and `emit_tower_incr₃`.
NOT LANDED: the leaf body itself. Its first half (source mother call +
Load transport) compiled; the second half (dst mother at the post-read
states, then RStore) is plumbing-heavy — the statement's emit tower
interleaves with a bind on the DST value, so `StateIncr` chains need
their intermediate states pinned. Removed rather than left sorried.
**Status:** all green; 17/17 + 72/72; corpus 82/123 (0 fail); audit at 2.
**Next-session pickup:** finish `copy_chaindst_chainsrc_simulation` —
the shape is settled (two mother calls, the temp register surviving the
dst lowering by the mother's register-frame conjunct); what remains is
the StateIncr/code-inclusion plumbing for the dst lowering at CS1.

## 2026-08-30 (ninth)
**Session:** (terminal, continued) — the two-mother leaf
**Theme:** `copy_chaindst_chainsrc_simulation` closes `*Q := copy src`
for chain dst AND chain src — the first leaf composing TWO mother calls
(source lowering, READ, destination lowering, write). Enablers: the
mother's register-frame conjunct carries the temp across the second
lowering; `PtrChain.placeToRegChecked_placeRegMap` supplies mapped-ness
BEFORE any mother runs; the value fragment quantifies over the general
source cleanup. Potholes: StateIncr chains over emit towers need every
state pinned (helper `emit_tower_incr₃`); hand-written cleanup lambdas
need annotated binders; the Load's and the dst lowering's code-inclusion
facts live at different states. Grind pass: 3 chains condensed (601 →
596 lines). d60 + teeth (RStore pointed at the source register).
**Status:** complete; all green; 17/17 + 73/73; corpus 82/123 (0 fail);
audit exact at 2.
**Next-session pickup:** copy's residual now names only (a) deref dsts
needing a FLATTEN first — write the compiled transfer for `assign
(.deref pp) (.copy src)`, same four-way agree alignment as the others —
and (b) PROJECTED dsts (the same skeleton inside the dst's Borrow/Die).

## 2026-08-30 (tenth)
**Session:** (terminal, continued) — deref-dst flatten transfer
**Theme:** `compileStmt_copy_derefdst_srcflatten_*` +
`..._dstflatten_*` make the deref-destination arm total for every
spelling whose FLATTENED source is a chain (d61: `*(s.f.g) := copy y`).
Key lesson: do NOT flatten both places in one lemma — the nested split
leaves the two sides' states spelled differently and the alignment
rewrites stop firing; two single-split lemmas compose cleanly. Second:
pick one spelling of the post-Load state per proof (unfolding
CompilerM.run/emitM moves it to `(ensurePlaceRoot _ cs).snd.val` form)
and make every later `cases` scrutinee match it.
**Status:** complete; all green; 17/17 + 74/74; corpus 82/123 (0 fail);
audit exact at 2.
**Next-session pickup:** copy's residual is down to proj-topped
FLATTENED SOURCES under a deref dst, and PROJECTED dsts — each wraps
the same two-mother skeleton in that projection's Borrow/Die. Then ref.

## 2026-08-30 (eleventh)
**Session:** (terminal, continued) — projected copy destinations
**Theme:** `copy_projdst_zero_chainsrc_simulation` (the two-mother leaf
one projection layer deep) plus `copy_projdst_simulation`, a recursive
dispatcher for projected dsts that peels nesting with the associativity
transfers (`stepStmt_assign_dst_proj_assoc` is new). Four
`compileStmt_copy_projderefdst_*flatten_*` transfers lifted verbatim
from the deref-dst four. `copy_place_residual` now takes the stmt0
triple so the recursion can fall back into it. d62 pins
`(*p).0 := copy y`.
**Key lesson:** a state-NEUTRAL wrapper (the zero-offset projection)
should be bridged, not unfolded — `placeToRegChecked_proj_zero_run/
_value` in common.lean keep it opaque inside StateIncr proofs, where
unfolding produces an identical-branch `match` no emit-tower lemma can
see. Written up in journal/2026-08-30-projected-dst-recursion.md
and durable/flatten-one-place-at-a-time.md.
**Status:** complete; all green; 17/17 + 75/75; corpus 82/123 (0 fail);
audit exact at 2.
**Next-session pickup:** copy's residual is now (a) proj-topped
flattened SOURCES under a deref dst, (b) projected dsts over a LOCAL
base. Then ref.

## 2026-08-30 (twelfth)
**Session:** (terminal, continued) — projected dsts at nonzero offset
**Theme:** `copy_projdst_offset_chainsrc_simulation` (d63) completes the
projected-destination arm for deref bases: §1–§7 from the zero leaf,
§8 from const_write's BRIDGE 1 endgame with `RStore` in place of
`CStore`. New obligations were only the temp register surviving the
`Borrow`'s insert (`RegMap.lookup_insert_ne` over the mother's register
frame), a `mirlite_readWordSeq_length` direction fix on the SB `ref`,
and keeping the projection OPAQUE in the StateIncr towers (`h_incrProj`
links the base-state facts back).
**Key lesson:** nested record updates `{ { s with … } with … }` do not
elaborate — flatten to one update. Fourth manifestation of the
record-sugar pothole in copy.lean.
**Status:** complete; all green; 17/17 + 76/76; corpus 82/123 (0 fail);
audit exact at 2.
**Next-session pickup:** copy's residual is proj-topped flattened
SOURCES under a deref dst, and projected dsts over a LOCAL base. Then
ref.

## 2026-08-30 (thirteenth)
**Session:** (terminal, continued) — proj-topped sources, zero offset
**Theme:** `copy_chaindst_projsrc_zero_simulation` (d64) closes
`*p := copy t.0`. The same two bridges that carried the destination
projection carry the source one, at `Shared`: the tower proofs never
unfold the projection, they rewrite `run (proj B path) = run B` and use
`value (proj) = ok ⟨o.result, …⟩`. The dispatcher's deref-dst arm now
splits with `flatten_chainish`, which is exactly the dichotomy
(flattened place is a chain, or a proj over a chain).
**Key lesson:** collapsing the `+ 0` on a SOURCE resolution cannot be
done by rewriting the record (`motive is not type correct` — the
resolved place feeds a dependent read); rewrite the OFFSET instead
(`simp only [h_o', Nat.add_zero]`) and let structure eta do the rest.
**Status:** complete; all green; 17/17 + 77/77; corpus 82/123 (0 fail);
audit exact at 2.
**Next-session pickup:** proj-topped sources at NONZERO offset (BRIDGE
1S around the READ — merge `copy_projchain_offset_simulation`'s source
half into the two-mother skeleton), then projected dsts over a LOCAL
base. Then ref.

## 2026-08-30 (seventh)
**Session:** (terminal) — proj-topped sources at NONZERO offset; the
deref-dst arm goes TOTAL
**Theme:** `copy_chaindst_projsrc_offset_simulation` (d65) closes
`*p := copy s.f` off zero. §1–§5/§8–§11 are d64's leaf; §6–§7 are
`copy_projchain_offset_simulation`'s BRIDGE 1S phase spliced in where
d64 had a bare `Load`. The splice needs no commutation argument: the
projection's `Borrow(Shared)` and its cleanup `Die` both sit in the rhs
pre-phase, so they bracket the READ contiguously and
`sb_ref_read_die_cancels`' `PermSim ρt perms₂ q3` drops straight into
the destination mother's argument slot. `copy_place_residual` now names
only PROJECTED destinations over a LOCAL base.
**Key lesson:** the work was term SHAPE, not mathematics. Transport
compiled states by DEFEQ (`have h' : … := h` + a trailing `rfl`), never
by `rw`/`▸` — `{ X with … }` elaborates to a `let` in hypotheses but a
flat literal in goals. Structure-instance fields on new lines must
share a column. Five-step `StateIncr` chains must be split at a named
state or the unifier dies. Written up in
journal/2026-08-30-projsrc-offset-bridge1s.md and
durable/transport-compiled-states-by-defeq.md.
**Potholes:** a heartbeat timeout here was a SYMPTOM of the doomed
unification, not of proof size — after splitting the chain the leaf
compiles at the default 200000, so no `set_option` was kept;
`expectDiff` compares
VERDICTS not values, so teeth must induce UB — an oversized
`RefKind.Shared` projection borrow is discriminating (d64 passes, d65
flips to `ub 4`).
**Environment:** the machine had NO Lean toolchain (no `lake`, no
`~/.elan`) and no `lean-lsp-mcp` venv; both were reinstalled this
session (elan + lean4 v4.28.0, `lean-lsp-mcp` 0.30.0). `lakefile.lean`
has no `require`, so `lake-manifest.json`'s mathlib entry is stale and
the build is self-contained (~2 min from scratch).
**Status:** complete; all green; 17/17 + 78/78; corpus 82/123 (0 fail,
osea matched 82); audit exact at 2, `[axioms]` untouched.
**Next-session pickup:** copy's last class — a PROJECTED destination
over a LOCAL base (`t.f := copy y`), mirroring
`const_write_proj_zero/offset_simulation` with the copy leaf's source
pre-phase in front — then ref's classes.
## 2026-08-30 (eighth)
**Session:** (terminal, continued) — non-local dst: groundwork landed, leaf in flight
**Theme:** with the ordering obstacle gone, started the last copy class.
LANDED (green): `compileStmt_copy_chaindst_run/_value` (the fragment for
a deref dst over the OPAQUE runs of BOTH lowerings — the value form is
stated over the GENERAL src cleanup, since the cleanup is only known
after the mother lemma), `PlaceInputsMapped.placeRegMap_congr`,
`PtrChain.placeToRegChecked_placeRegMap` (a chain's lowering never
touches placeRegMap — needed BEFORE the mother can run, to transfer
mapped-ness past the first lowering; induction on the CHAIN, whose
grammar has no proj-of-proj), and `emit_tower_incr₃`.
NOT LANDED: the leaf body itself. Its first half (source mother call +
Load transport) compiled; the second half (dst mother at the post-read
states, then RStore) is plumbing-heavy — the statement's emit tower
interleaves with a bind on the DST value, so `StateIncr` chains need
their intermediate states pinned. Removed rather than left sorried.
**Status:** all green; 17/17 + 72/72; corpus 82/123 (0 fail); audit at 2.
**Next-session pickup:** finish `copy_chaindst_chainsrc_simulation` —
the shape is settled (two mother calls, the temp register surviving the
dst lowering by the mother's register-frame conjunct); what remains is
the StateIncr/code-inclusion plumbing for the dst lowering at CS1.

## 2026-08-30 (ninth)
**Session:** (terminal, continued) — the two-mother leaf
**Theme:** `copy_chaindst_chainsrc_simulation` closes `*Q := copy src`
for chain dst AND chain src — the first leaf composing TWO mother calls
(source lowering, READ, destination lowering, write). Enablers: the
mother's register-frame conjunct carries the temp across the second
lowering; `PtrChain.placeToRegChecked_placeRegMap` supplies mapped-ness
BEFORE any mother runs; the value fragment quantifies over the general
source cleanup. Potholes: StateIncr chains over emit towers need every
state pinned (helper `emit_tower_incr₃`); hand-written cleanup lambdas
need annotated binders; the Load's and the dst lowering's code-inclusion
facts live at different states. Grind pass: 3 chains condensed (601 →
596 lines). d60 + teeth (RStore pointed at the source register).
**Status:** complete; all green; 17/17 + 73/73; corpus 82/123 (0 fail);
audit exact at 2.
**Next-session pickup:** copy's residual now names only (a) deref dsts
needing a FLATTEN first — write the compiled transfer for `assign
(.deref pp) (.copy src)`, same four-way agree alignment as the others —
and (b) PROJECTED dsts (the same skeleton inside the dst's Borrow/Die).

## 2026-08-30 (tenth)
**Session:** (terminal, continued) — deref-dst flatten transfer
**Theme:** `compileStmt_copy_derefdst_srcflatten_*` +
`..._dstflatten_*` make the deref-destination arm total for every
spelling whose FLATTENED source is a chain (d61: `*(s.f.g) := copy y`).
Key lesson: do NOT flatten both places in one lemma — the nested split
leaves the two sides' states spelled differently and the alignment
rewrites stop firing; two single-split lemmas compose cleanly. Second:
pick one spelling of the post-Load state per proof (unfolding
CompilerM.run/emitM moves it to `(ensurePlaceRoot _ cs).snd.val` form)
and make every later `cases` scrutinee match it.
**Status:** complete; all green; 17/17 + 74/74; corpus 82/123 (0 fail);
audit exact at 2.
**Next-session pickup:** copy's residual is down to proj-topped
FLATTENED SOURCES under a deref dst, and PROJECTED dsts — each wraps
the same two-mother skeleton in that projection's Borrow/Die. Then ref.

## 2026-08-30 (eleventh)
**Session:** (terminal, continued) — projected copy destinations
**Theme:** `copy_projdst_zero_chainsrc_simulation` (the two-mother leaf
one projection layer deep) plus `copy_projdst_simulation`, a recursive
dispatcher for projected dsts that peels nesting with the associativity
transfers (`stepStmt_assign_dst_proj_assoc` is new). Four
`compileStmt_copy_projderefdst_*flatten_*` transfers lifted verbatim
from the deref-dst four. `copy_place_residual` now takes the stmt0
triple so the recursion can fall back into it. d62 pins
`(*p).0 := copy y`.
**Key lesson:** a state-NEUTRAL wrapper (the zero-offset projection)
should be bridged, not unfolded — `placeToRegChecked_proj_zero_run/
_value` in common.lean keep it opaque inside StateIncr proofs, where
unfolding produces an identical-branch `match` no emit-tower lemma can
see. Written up in journal/2026-08-30-projected-dst-recursion.md
and durable/flatten-one-place-at-a-time.md.
**Status:** complete; all green; 17/17 + 75/75; corpus 82/123 (0 fail);
audit exact at 2.
**Next-session pickup:** copy's residual is now (a) proj-topped
flattened SOURCES under a deref dst, (b) projected dsts over a LOCAL
base. Then ref.

## 2026-08-30 (twelfth)
**Session:** (terminal, continued) — projected dsts at nonzero offset
**Theme:** `copy_projdst_offset_chainsrc_simulation` (d63) completes the
projected-destination arm for deref bases: §1–§7 from the zero leaf,
§8 from const_write's BRIDGE 1 endgame with `RStore` in place of
`CStore`. New obligations were only the temp register surviving the
`Borrow`'s insert (`RegMap.lookup_insert_ne` over the mother's register
frame), a `mirlite_readWordSeq_length` direction fix on the SB `ref`,
and keeping the projection OPAQUE in the StateIncr towers (`h_incrProj`
links the base-state facts back).
**Key lesson:** nested record updates `{ { s with … } with … }` do not
elaborate — flatten to one update. Fourth manifestation of the
record-sugar pothole in copy.lean.
**Status:** complete; all green; 17/17 + 76/76; corpus 82/123 (0 fail);
audit exact at 2.
**Next-session pickup:** copy's residual is proj-topped flattened
SOURCES under a deref dst, and projected dsts over a LOCAL base. Then
ref.

## 2026-08-30 (thirteenth)
**Session:** (terminal, continued) — proj-topped sources, zero offset
**Theme:** `copy_chaindst_projsrc_zero_simulation` (d64) closes
`*p := copy t.0`. The same two bridges that carried the destination
projection carry the source one, at `Shared`: the tower proofs never
unfold the projection, they rewrite `run (proj B path) = run B` and use
`value (proj) = ok ⟨o.result, …⟩`. The dispatcher's deref-dst arm now
splits with `flatten_chainish`, which is exactly the dichotomy
(flattened place is a chain, or a proj over a chain).
**Key lesson:** collapsing the `+ 0` on a SOURCE resolution cannot be
done by rewriting the record (`motive is not type correct` — the
resolved place feeds a dependent read); rewrite the OFFSET instead
(`simp only [h_o', Nat.add_zero]`) and let structure eta do the rest.
**Status:** complete; all green; 17/17 + 77/77; corpus 82/123 (0 fail);
audit exact at 2.
**Next-session pickup:** proj-topped sources at NONZERO offset (BRIDGE
1S around the READ — merge `copy_projchain_offset_simulation`'s source
half into the two-mother skeleton), then projected dsts over a LOCAL
base. Then ref.

## 2026-08-30 (seventh)
**Session:** (terminal) — proj-topped sources at NONZERO offset; the
deref-dst arm goes TOTAL
**Theme:** `copy_chaindst_projsrc_offset_simulation` (d65) closes
`*p := copy s.f` off zero. §1–§5/§8–§11 are d64's leaf; §6–§7 are
`copy_projchain_offset_simulation`'s BRIDGE 1S phase spliced in where
d64 had a bare `Load`. The splice needs no commutation argument: the
projection's `Borrow(Shared)` and its cleanup `Die` both sit in the rhs
pre-phase, so they bracket the READ contiguously and
`sb_ref_read_die_cancels`' `PermSim ρt perms₂ q3` drops straight into
the destination mother's argument slot. `copy_place_residual` now names
only PROJECTED destinations over a LOCAL base.
**Key lesson:** the work was term SHAPE, not mathematics. Transport
compiled states by DEFEQ (`have h' : … := h` + a trailing `rfl`), never
by `rw`/`▸` — `{ X with … }` elaborates to a `let` in hypotheses but a
flat literal in goals. Structure-instance fields on new lines must
share a column. Five-step `StateIncr` chains must be split at a named
state or the unifier dies. Written up in
journal/2026-08-30-projsrc-offset-bridge1s.md and
durable/transport-compiled-states-by-defeq.md.
**Potholes:** a heartbeat timeout here was a SYMPTOM of the doomed
unification, not of proof size — after splitting the chain the leaf
compiles at the default 200000, so no `set_option` was kept;
`expectDiff` compares
VERDICTS not values, so teeth must induce UB — an oversized
`RefKind.Shared` projection borrow is discriminating (d64 passes, d65
flips to `ub 4`).
**Environment:** the machine had NO Lean toolchain (no `lake`, no
`~/.elan`) and no `lean-lsp-mcp` venv; both were reinstalled this
session (elan + lean4 v4.28.0, `lean-lsp-mcp` 0.30.0). `lakefile.lean`
has no `require`, so `lake-manifest.json`'s mathlib entry is stale and
the build is self-contained (~2 min from scratch).
**Status:** complete; all green; 17/17 + 78/78; corpus 82/123 (0 fail,
osea matched 82); audit exact at 2, `[axioms]` untouched.
**Next-session pickup:** copy's last class — a PROJECTED destination
over a LOCAL base (`t.f := copy y`), mirroring
`const_write_proj_zero/offset_simulation` with the copy leaf's source
pre-phase in front — then ref's classes.

## 2026-08-30 (eighth)
**Session:** (terminal, continued) — projected destinations over a
LOCAL base; copy is down to ONE class
**Theme:** `t.f := copy y` closes at both offsets for both root states
(d66–d69). The BOUND half cost NO new proof: nothing in
`copy_projdst_zero/offset_chainsrc_simulation` used the `deref` shape,
so generalizing the destination base from `.deref P` to any canonical
chain base makes a bound local (`PtrChain.base`) fall out. The only
genuine difference is `preparePlaceAssign`, whose `allocateRoot` branch
is contradictory for a deref root but REACHABLE for a local one — so
the leaves now take an `h_bound` hypothesis instead of deriving it. The
four compiled fragments and the source-flatten transfer generalized the
same way (the latter renamed `compileStmt_copy_projdst_srcflatten_*`;
it was never deref-specific, only deref-spelled). The UNBOUND half is
real regime-B work: two new leaves that allocate the σ-sized root, run
the source mother lemma at the POST-allocation states under
`extendBlock`/`extend`, then write at `+ 0` or through the fresh root
register's own `Borrow(Mut)`/`Die`.
**Key lesson:** before writing a leaf a parked note asks for, check
whether an existing leaf is accidentally SPELLED for one shape rather
than gated on it. Two ~600-line proofs were avoided by a rename plus
one hypothesis.
**Correction to the record:** the parked note claimed the local-base
class was all that remained of copy. It was not — the proj-dst arm's
`¬PtrChain (flattenPlace src)` branch has always routed PROJ-TOPPED
sources under projected destinations to the residual. That is now the
sole remaining class and is parked with a resume recipe.
**Potholes:** `PtrRegisterEntry` is not a `rw`/`simp` target (keep the
lookup equation and ascribe); BRIDGE 1's `addrStart + (0 + pathOffset)`
and mirlite's `addrStart + PathTo.offset` are defeq but distinct atoms
— rewrite the GOAL, not the hypothesis; `TagRenameBounded.mono` needs
its bounds in one `exact`. The long-`StateIncr`-chain pothole recurred
twice and the durable note's prescribed fix worked verbatim both times.
**Status:** complete; all green; 17/17 + 82/82; corpus 82/123 (0 fail,
osea matched 82); audit exact at 2, `[axioms]` untouched.
**Next-session pickup:** copy's LAST class — a proj-topped flattened
source under a projected destination, composing BRIDGE 1S (source) with
BRIDGE 1 (destination); then ref's classes.

## 2026-08-30 (ninth)
**Session:** (terminal, continued) — the source lowering becomes a
PACKAGE; half the last copy class falls out
**Theme:** a proj-topped source at ZERO offset under a projected
destination is closed (d70/d71) with NO new leaf. `LoweringSim` names
`ptrChain_lowering_sim`'s twenty-conjunct conclusion and
`LoweringSimAny` makes it rename-polymorphic (regime-B leaves run the
source lowering at EXTENDED renames and a post-allocation state, so a
package fixed at `ρa, ρt, s_mir` cannot serve them — the first draft got
that wrong). `PtrChain.loweringSimAny` is two lines;
`LoweringSimAny.projZero` is ~35 and compiled first try. Four leaves
were then re-gated on the package instead of `PtrChain src` — three
edits each — and the dispatcher's proj-dst arm now splits with
`flatten_chainish` and feeds the projZero package.
**Key lesson:** the parked recipe (generalize the projsrc leaves, splice
BRIDGE 1S with BRIDGE 1) is right for the NONZERO half and unnecessary
for the zero half, because at zero offset the source projection is
state-neutral and cleanup-free — there is nothing to splice. Checking
why a hypothesis is there before writing the proof it seems to demand
has now paid twice running.
**The boundary:** a package promises `placeOut.result.cleanup = []`. A
nonzero-offset projection emits a `Borrow` and leaves a `Die`, so it
cannot supply one; that half still needs two real leaves, and the
parked entry is narrowed to exactly it with a recipe.
**Status:** complete; all green; 17/17 + 84/84; corpus 82/123 (0 fail,
osea matched 82); audit exact at 2, `[axioms]` untouched.
**Next-session pickup:** the nonzero-offset half — generalize
`compileStmt_copy_projdst_{zero,offset}_run` to a non-empty source
cleanup, then splice BRIDGE 1S into the two projdst leaves. Then ref.

## 2026-08-30 (tenth)
**Session:** (terminal, continued) — the compiled side of the last copy
class; the leaves do not land
**Theme:** three fragments for `.assign (.proj dbase dpath) (.copy
(.proj B spath))` with the source field off zero —
`compileStmt_copy_projdst_zero_projsrc_offset_run`, its `offset` twin,
and the destination-offset-agnostic
`compileStmt_copy_projdst_projsrc_offset_value`. They spell the source
tower as `Borrow(Shared)`/`Load`/`Die` and reuse the projdst
destination half. All three compile.
**Not delivered:** the two LEAVES. Deriving
`copy_projdst_zero_projsrc_offset_simulation` from
`copy_chaindst_projsrc_offset_simulation` (change the destination) got
§1–§2 right, but the three `StateIncr` towers would not close: a
projected destination adds an `Except.ok { … projZero … }` layer, so one
`split` leaves a second match, and `repeat' split` still leaves a third
occurrence inside the emitted instruction list. The fix is
`simp only [h_dval0]`, which needs `h_dval0` in the goal's MIXED normal
form — recorded in the parked entry with the instruction to read it out
of a `trace_state` rather than guess. The half-built leaf was REMOVED
rather than left broken or `sorry`-ed; the fragments stay.
**Housekeeping:** a concurrent terminal session added a Typst four-page
overview and its own sessions entry at the TOP of this file. Note the
inconsistency: the header says "newest first" but every entry below is
oldest-first, so the two conventions are now both present. Worth a
decision.
**Status:** green; 17/17 + 84/84; corpus 82/123 (0 fail, osea matched
82); audit exact at 2, `[axioms]` untouched.
**Next-session pickup:** the two leaves, from the parked recipe.

## 2026-08-30 — four-page artifact overview
**Session:** terminal
**Theme:** concise MIRLite → OSEA-IR semantics, compiler, and correctness
overview in Typst.
**Key outputs:** `mirlite-oseair-correctness.typ` and compiled PDF; one page
per topic, joined by the nonzero-field constant-write case
`Borrow(Mut); CStore; Die`; journal entry
`journal/2026-08/2026-08-30-four-page-overview.md`.
**Critical scope choices:** describes live obseq3, not the v1 `paper.md`;
separates full compiler coverage from `CoreProg`; states successful-run
forward simulation only; names both audited residual sorries instead of
claiming an axiom-free proof.
**Status:** complete — Typst 0.15.1 build and visual inspection confirmed
exactly four A4 pages. Pre-existing `src/obseq3/proof/copy.lean` changes were
left untouched.

## 2026-08-30 (eleventh)
**Session:** (terminal, continued) — the tower obstacle falls; one of
the two leaves lands
**Theme:** `copy_projdst_zero_projsrc_offset_simulation` is PROVED —
a projected destination at zero offset with a proj-topped source at
nonzero offset. The obstacle that stopped the previous attempt is
solved, and the method generalizes: put a `trace_state` in the
`StateIncr` tower, build, and lift the state spelling VERBATIM out of
the build log into `have h_dv0 : … := h_dval0` (defeq transport — no
proof obligation). `simp only [h_dv0]` then fires and the tower closes
with no `split` at all, which also sidesteps the nested-match problem
entirely. Two spellings were needed: value-flavoured for the pre-mother
tower, and a run-flavoured one derived through `h_sclean` for the two
post-mother towers. Then every other occurrence of that state in the
leaf — the destination mother's `cs` argument, `h_prmCS2`, `h_lbs1`,
`h_prb1` — must be normalized to the same spelling, or the later `rw`s
miss one at a time.
**Not delivered:** the nonzero-destination twin and the dispatcher
wiring. The twin is not a rename: its write phase is BRIDGE 1 from
`copy_projdst_offset_chainsrc_simulation` §8, whose every compiled-state
spelling is the chain-source one. And the zero leaf cannot be wired
alone — routing a package-less source needs a parallel recursive
dispatcher that only makes sense once both leaves exist. Both recorded
in the parked entry.
**Convention:** sessions.md is now explicitly OLDEST FIRST (header
fixed, the concurrent session's entry moved to the end); CLAUDE.md and
notes/CLAUDE.md say so too.
**Status:** green; 17/17 + 84/84; corpus 82/123 (0 fail, osea matched
82); audit exact at 2, `[axioms]` untouched.
**Next-session pickup:** the twin, then the recursive dispatcher, then
witnesses and teeth.

## 2026-08-30 (twelfth)
**Session:** (terminal, continued) — `csnorm`, a normal form for
compiler states
**Theme:** the spelling problem that has cost time in three consecutive
increments now has a tool. `csnorm` (common.lean) is eight `rfl`
projection lemmas — `emit`/`setPlaceInfo`/`freshReg` pushed down to the
underlying state — plus a tactic macro, used as `csnorm at h ⊢` so both
sides normalize together.
**Measured on the twin's structure:** the zero-destination leaf's three
`StateIncr` towers had needed two auxiliary hypotheses whose statements
were the destination state pasted verbatim out of a `trace_state` dump
(3188 and 3148 characters). Both are now deleted; each tower is
`have h_d := h_dval0; csnorm at h_d ⊢; simp only [h_d]`. Nine lines of
pasted spelling gone, leaf still green.
**Deliberately opt-in:** not global `@[simp]`, which would change the
normal form inside every existing leaf. A tactic macro rather than
`register_simp_attr` because that command needs `import Lean`, which
this project does not take.
**Limits, recorded:** `csnorm` normalizes SPELLINGS, not content —
`cleanupInstrs sOut.result.cleanup` vs `[Die …]` differ by `h_sclean`,
a proof, so that boundary still needs an explicit rewrite first. And
`grind` is the wrong tool for this family: these are hypotheses failing
to MATCH, not goals failing to close.
**Still open:** the nonzero-destination twin. `csnorm` makes its three
towers easy, but its write phase is genuine new content — the BRIDGE 1
endgame against the Borrow/Load/Die tower — which no normalization
helps with.
**Status:** green; 17/17 + 84/84; corpus 82/123 (0 fail, osea matched
82); audit exact at 2, `[axioms]` untouched.
**Next-session pickup:** the twin's write phase, then the recursive
dispatcher, then witnesses and teeth.

## 2026-08-30 (thirteenth)
**Session:** (terminal, continued) — the twin's write phase; both leaves
of the last copy class are proved
**Theme:** `copy_projdst_offset_projsrc_offset_simulation` closes. It is
the zero-destination leaf's §1–§8 with the BRIDGE 1 endgame replacing
the bare `RStore`: `sb_ref_use_die_cancels` around the write, three code
facts (Borrow at `s_mid2.pc`, RStore at +1, Die at +2), and a final
`LocalBindingSim` that frames the destination borrow register out with
`insert_fresh_reg h_dlbs h_prb1 h_dregmono rfl`.
**csnorm paid off exactly where predicted.** The three `StateIncr`
towers needed no traced spellings at all — only their ARITIES changed
(the destination projection adds a `freshReg` and an `emit`), which is
content, not spelling. Every remaining pothole was content too:
`PtrRegisterEntry` is not a simp target (keep an `h_lookupD2` twin and
use it in `writeThroughPtr`'s `simp` AND in `runN_RStore_step`), and
`omega` needs BOTH sides normalized or the two `emit`-laden atoms differ
(`simp only [emit] at h1 h_eq'`).
**Not delivered:** the dispatcher. `CompilerInv_step_copy` still sends
every nonzero-offset source to the residual; wiring needs a recursive
`copy_projdst_projsrc_offset_simulation` that peels nested destination
projections and then picks a leaf by destination offset. Note that even
with it, `copy_place_residual` will NOT close: an UNBOUND local root
with a nonzero-offset projected source has no leaf.
**Status:** green; 17/17 + 84/84; corpus 82/123 (0 fail, osea matched
82); audit exact at 2, `[axioms]` untouched.
**Next-session pickup:** the recursive dispatcher, then witnesses and
teeth; then the fresh-root × projsrc-offset combination if the residual
is to close.

## 2026-08-30 (fourteenth)
**Session:** terminal — MIRLite inference-rule expansion
**Theme:** expanded the Typst artifact from four to six pages, using two new
pages to make MIRLite's executable operational semantics readable as rules.
**Key outputs:** `mirlite-oseair-correctness.typ` and rebuilt PDF; page 2
contains `ACC-LOCAL`, `ACC-PROJ`, and `ACC-DEREF` plus the pure-resolution
contrast; page 3 contains `E-CONST`, `E-COPY`, `E-REF`, `WRITE`, and
`S-ASSIGN`; journal entry
`journal/2026-08/2026-08-30-mirlite-inference-rules.md`.
**Critical scope choice:** the rules are explicitly a derived presentation of
the successful branches of `resolvePlaceAcc`, `evalRExpr`,
`writeResolvedPlace`, and `doAssign`, not a second inductive semantics. They
make permission threading and RHS-before-destination evaluation order
visible without overstating what is mechanized.
**Status:** complete — Typst 0.15.1 build and a 110-PPI visual inspection
confirmed exactly six A4 pages with no overflow. The earlier four-page note
is retained and marked superseded; pre-existing proof changes were untouched.

## 2026-08-30 (fourteenth)
**Session:** (terminal, continued) — the recursive dispatcher; copy's
residual reaches ONE branch
**Theme:** `copy_projdst_projsrc_offset_simulation` mirrors
`copy_projdst_simulation` for the source shape that cannot supply a
`LoweringSim` package. It compiled first try, and wiring it into
`CompilerInv_step_copy` leaves `copy_place_residual` with a single call
site: an UNBOUND local root with a nonzero-offset projected source.
Also landed the three compiled fragments that branch needs — all three
compiled first try.
**Attempted and withdrawn:** the two regime-B leaves for that branch.
The mechanical half went in cleanly; 9 errors remained, in three known
classes (tower arities, the post-`Die` mother state and its spelling
propagation, and the BRIDGE 1S write phase). Rather than leave the tree
broken or add a sorry, the incomplete leaf was removed and the parked
entry now carries the error classes so the next attempt starts from
them instead of rediscovering them.
**Honest note on pacing:** this is the third increment in a row where
the leaf-sized piece did not land inside the session. The leaves are
600-800 lines each and take 10-15 build iterations; that is the unit of
work, and planning should treat one leaf as one increment rather than
assuming two fit together.
**Status:** green; 17/17 + 84/84; corpus 82/123 (0 fail, osea matched
82); audit exact at 2, `[axioms]` untouched.
**Next-session pickup:** the two fresh leaves, from the parked error
classes; then delete `copy_place_residual` and take the pin 2 → 1.

## 2026-08-30 (fifteenth)
**Session:** (terminal, continued) — one leaf, as planned
**Theme:** `copy_projlocal_fresh_projsrc_offset_zero_simulation` is
proved and wired: an UNBOUND local root, destination offset zero, with
a source that flattens to a projection at nonzero offset.
`copy_place_residual` is now reached only at NONZERO destination offset.
**Method that worked** (worth repeating for the twin): rewrite the
source phase STRUCTURALLY rather than patching `rw` chains — tokenize
the post-alloc source state, turn the `Load`-only state into the
`Borrow`/`Load`/`Die` tower, and remap every standalone
`Register.R CS0.nextReg` to the LOAD target `Register.R PS.nextReg`,
splitting the leaf at `subst h_sOut_eq` (`sOut0` before, `sOut` after).
Then write the write phase fresh rather than editing it. `csnorm at h1
h_eq'` fixed every `omega` that was comparing two `emit`-laden atoms.
**One non-obvious failure:** the `h_incrS1V` tower inherited no source
`placeToRegChecked_proj_root_eq` from its parent, because the parent's
source was package-supplied. Adding it plus `dif_neg h_so` was the last
error.
**Pacing:** one leaf per increment, as resolved last time, and it
landed.
**Status:** green; 17/17 + 84/84; corpus 82/123 (0 fail, osea matched
82); audit exact at 2, `[axioms]` untouched.
**Next-session pickup:** the NONZERO-destination twin — same recipe with
the BRIDGE 1 write phase from `copy_projdst_offset_projsrc_offset_
simulation` §9 — then delete `copy_place_residual` and take the pin
2 → 1.

## 2026-08-31
**Session:** (terminal, continued) — copy_place_residual is CLOSED
**Theme:** the nonzero-destination twin,
`copy_projlocal_fresh_projsrc_offset_offset_simulation`, landed; with
it every branch of the copy dispatcher reaches a leaf, so
`copy_place_residual` was DELETED and the whitelist pin went 2 → 1.
Only `ref_place_residual` remains.
**Method:** the same structural rewrite as the zero twin — tokenize the
source state, replace the `Load`-only state with the
`Borrow`/`Load`/`Die` tower, write the write phase fresh. The follow-up
errors came in the three classes now recorded in
journal/2026-08-31-copy-closes.md: arities (peel counts and tower steps
grow with the added instructions), spelling (`csnorm`, four-field
records, single-line `{ s_mid with … }`), and one content error worth
anticipating — the destination borrow mints at `q3.NextTag`, the state
AFTER the source's `Die`, not at `s_mid.perms.NextTag`.
**Witnesses:** d72 (bound dst at offset), d73 (fresh dst at zero), d74
(fresh dst at offset). Teeth: oversizing the `Shared` projection borrow
flips d73 to `ub 2` while d68 — whose Shared projections are all at
offset zero, so no borrow is emitted — stays passing. Note d71 is NOT a
valid control: its read-back is itself an offset projection.
**Status:** green; 17/17 + 87/87; corpus 82/123 (0 fail, osea matched
82); audit exact at ONE sorry, `[axioms]` untouched.
**Next-session pickup:** `ref_place_residual` — eleven call sites in
three families (unbound dst roots, non-local sources, projected dsts
over a deref base). The copy techniques transfer: the lowering PACKAGE,
regime-B leaves, and `csnorm`.

## 2026-08-31 (later)
**Session:** (terminal, continued) — ref reconnaissance, and the first
compiled fragments
**Theme:** with copy closed, `ref_place_residual` is the only sorry.
Inventoried it from the source: ELEVEN call sites in three families —
unbound destination roots (4), non-local sources (6), and a projected
destination over a deref base (1). The closed set is the complement:
local sources under every destination, non-local sources only under a
local destination.
**Key finding:** copy's package trick does NOT transfer for free.
`LoweringSim` was cheap because `ptrChain_lowering_sim` already existed
as a standalone source lemma; ref has none — every leaf inlines its own
source phase, so factoring one out means extracting and proving it per
source shape. The payoff is bigger, though:
`placeToBorrowRegChecked` ends identically in all three arms (a
`Borrow` into a fresh register, cleanup `[(tmpReg, blockSize τ)]`),
differing only in the offset, so one package would unlock all six
family-(B) sites. Unlike copy's, it should be stated WITH the cleanup
rather than against it. Recommendation recorded: build it after two or
three concrete leaves exist to generalize over.
**Landed:** `compileStmt_ref_derefdst_projsrc_run/_value` for
`*P := &kind s.f` — the proj arm differs from the local arm only in the
borrow's offset, so both are the deref-dst pair with `pathOffset f` for
`0`. Both compiled first try.
**Status:** green; 17/17 + 87/87; audit exact at ONE sorry.
**Next-session pickup:** the leaf itself — swap
`ref_derefdst_local_simulation`'s source phase for the proj arm
(`resolvePlaceAcc_proj_base_ok`, the fit check at
`bS.addr + PathTo.offset f`, the borrow offset, and the pointer value's
`(0 + pathOffset f)` / `blockSize σs`).

## 2026-08-31 (later still)

**Goal:** the leaf left as next-session pickup —
`ref_derefdst_projsrc_simulation` (`*P := &kind s.f`).
**Landed:** the leaf, green; wired into `CompilerInv_step_ref`'s
deref-destination arm under a `local` source base; witness d75 with
teeth (a disjoint live `&mut t.0` that a wrong offset would pop —
control run reports `ub`).
**Key finding:** the four substitutions off
`ref_derefdst_local_simulation` were mechanical, but the source
reduction is NOT: `simp only [mirlite.resolvePlaceAcc, ...]` unfolds
the DESTINATION's resolution too and kills the later `rw [h_dres]`.
Use the targeted `resolvePlaceAcc_proj_base_ok (resolvePlaceAcc_local
h_envS)` instead. Rule: in a leaf that keeps one half opaque for the
mother lemma, never `simp only` a definition that governs that half.
**Also landed:** `compileStmt_ref_derefdst_flatten_run/_value` never
inspected the rhs, so it was generalized in place to any
`rhs : RExpr Γ (PtrL τ)` and renamed
`compileStmt_assign_derefdst_flatten_run/_value`. Future
deref-destination leaves get flatten normalization for free.
**Status:** green; 17/17 + 88/88; audit exact at ONE sorry
(`ref_place_residual`) — unchanged; this class was one of several the
residual still covers.
**Next-session pickup:** the four UNBOUND-DESTINATION-ROOT ref sites
(regime B), or the `BorrowSim` source package now that two proj-source
leaves exist to generalize over.
See journal/2026-08-31-ref-derefdst-projsrc.md.

## 2026-08-31 (PLDI format)

**Session:** terminal — PLDI 2026 paper-format conversion
**Theme:** replaced the custom six-page A4 layout with the current PLDI
research-paper format: PACMPL-compatible `acmsmall`, single column, 10 pt,
12 pt baseline spacing, and anonymous review line numbers.
**Key outputs:** `mirlite-oseair-correctness.typ` and rebuilt PDF;
`@preview/faithful-acmart:0.1.0`; ACM Libertinus/Inconsolatazi4 fonts plus OFL
license in `assets/fonts/acm/`; journal entry
`journal/2026-08/2026-08-31-pldi-format.md`.
**Critical correction:** current PLDI research papers do not use the older
two-column SIGPLAN format. PLDI 2026 allows 20 pages of main text excluding
the bibliography and requires the single-column `acmsmall` layout. The Typst
port matches `acmart` output but remains unofficial, so final TAPS production
may require official LaTeX or Word source.
**Status:** complete — clean Typst 0.15.1 build; seven pages; all pages
visually inspected at 110 PPI; fonts embedded; no overflow or unintended box
split. The entry was appended at the end to preserve oldest-first order.

## 2026-08-31 (fourth)

**Goal:** the unbound destination roots of `ref` (four sites).
**Landed:** one of the four —
`compileStmt_ref_fresh_projsrc_run/_value` (first try) and
`ref_fresh_projsrc_simulation` (`dst := &kind s.f`, `dst` unbound),
wired, plus witness d76 with teeth (control reports `ub`). Residual
sites 12 -> 11.
**Key finding:** ref's offset rule composes with regime B for free —
the allocation half of `ref_fresh_dst_simulation` needed no change at
all. Second data point that the proj-source substitution is cheap;
weakens the case for building a `BorrowSim` package.
**Technique worth keeping:** `ref_dst_src_idx_ne` argues from TYPES
(`τ ≠ PtrL τ`) and does not survive a projected source. Two
replacements: inside the leaf, `Env.lookup env loc = env loc.idx` gives
`none = some bS` from the env facts alone; in the none/none dispatcher
branch, `ref_proj_dst_src_idx_ne` substitutes `σb = PtrL τ` and then
`cases f` closes the goal with ZERO cases — both `PathTo` constructors
fail to unify. An impossible indexed family often needs no lemma.
**Status:** green; 17/17 + 89/89; audit exact at ONE sorry.
**Next-session pickup:** the three remaining unbound-root sites — a
deref source under a fresh destination, and projected destinations over
an unbound root at zero and nonzero offset (regime B-proj for the
DESTINATION, analogue of `const_write_proj_fresh_simulation`).
See journal/2026-08-31-ref-regime-b-proj.md.

## 2026-08-31 (fifth)

**Goal:** keep going on `ref`'s unbound destination roots.
**Landed:** the second of four — `compileStmt_ref_projzero_fresh_run/_value`
and `ref_projzero_fresh_simulation` (`dst.g := &kind s` at offset 0,
root UNBOUND), stmt0-threaded so it plugs into `ref_proj_dst_simulation`;
witness d77 with teeth. Also `PathTo.sizeOf_le`,
`ref_dst_src_idx_ne_of_proj`, `prepare_lookup_ne_proj`. Residual sites
11 -> 10.
**Key finding:** the leaf is `ref_fresh_dst_simulation` with the ROOT's
layout blanket-substituted `PtrL τ -> σ`, protecting the single
occurrence where the layout names the stored VALUE
(`writeThroughPtr_sim (τ := PtrL τ)`). Only two changes are real: ρa
extends by `extendBlock` over the whole σ-sized root instead of one
cell, and the block-domain conjunct follows.
**Second finding:** a path cannot reach `PtrL τ` from `τ` — needs a
SIZE argument (`PathTo.sizeOf_le` + Lean's derived `sizeOf_spec`),
unlike the reverse direction where `cases` alone works.
**Tooling scar:** `open(p,'w').write(f(...))` truncates before
evaluating `f`; a raising `f` left ref.lean empty. Recovered from HEAD.
Compute the output string first, assert it grew, then open for writing.
**Status:** green; 17/17 + 90/90; audit exact at ONE sorry.
**Next-session pickup:** the last two unbound-root sites — a deref
source under a fresh destination, and a projected destination over an
unbound root at NONZERO offset (this leaf plus BRIDGE 1: the interior
`Borrow(Mut)` and its cleanup `Die`).
See journal/2026-08-31-ref-fresh-projected-destination.md.

## 2026-08-31 (OSEA-IR/compiler rules)

**Session:** terminal — PLDI paper semantic-rule expansion
**Theme:** added derived OSEA-IR RHS and instruction rules, compiler
place/RHS/assignment lowering rules, and the proof layer's projection
flattening normalizer to the existing PLDI-format paper.
**Key outputs:** expanded `mirlite-oseair-correctness.typ` and rebuilt PDF;
`journal/2026-08/2026-08-31-oseair-compiler-rules.md`.
**Key finding:** `projInto`/`flattenPlace` is not only syntactic tidying. Path
fusion prevents a borrow of a wide intermediate projection from invalidating
a live sibling borrow; lowering instead uses the composed offset and only the
final field width. Compiler reassociation and proof normalization agree on the
emitted run and register-plus-cleanup result.
**Status:** complete — clean Typst 0.15.1 build; eleven PLDI `acmsmall` pages;
all pages visually inspected at 110 PPI; axiom audit exact at one sorry root
(`ref_place_residual`). Entry appended after the latest concurrent proof
session to preserve strict oldest-first order.

## 2026-08-31 (sixth)

**Goal:** keep closing `ref`'s unbound destination roots.
**Landed:** the third of four —
`compileStmt_ref_projoffset_fresh_run/_value` (first try) and
`ref_projoffset_fresh_simulation` (`dst.g := &kind s` at NONZERO
offset, root UNBOUND), wired, with witness d78 and teeth. Residual
sites 10 -> 9.
**Key finding:** this leaf is the first that could NOT be reached by
substitution from a single donor — the fresh-root axis and the
nonzero-offset axis each cost a full proof (measured: 405, 560 and 433
line diffs between the candidate donors). It was assembled by SPLICING
whole sections: fresh §1-§6 verbatim, then the bound offset leaf's
BRIDGE 1 write phase, then a merged rebuild. One error on the first
full build.
**Where the seam goes:** the mirlite write inversion and BRIDGE 1 must
come BEFORE the fragment, because the interior Borrow's bounds check is
`h_nb` from splitting `writeResolvedPlace`, and q1/q2/q3 are arguments
to the execution steps. The two donors disagree on this order and the
offset one is right.
**The one real error:** `TagRenameBounded` now bounds against `q3`,
three states past `h_tbd2`; transport `h_ntle` through
`sb_write_NextTag h_useMut_tgt`. In the zero-offset leaf that bound was
an equality, so BRIDGE 1 is the only place the extra instructions leak
into the invariant.
**Status:** green; 17/17 + 91/91; audit exact at ONE sorry.
**Next-session pickup:** the LAST unbound-root site — a deref SOURCE
under a fresh destination, crossing the fresh machinery with the spine
mother lemma instead of with BRIDGE 1. Then the non-local-source
families.
See journal/2026-08-31-ref-fresh-proj-offset-bridge1.md.

## 2026-08-31 (seventh)

**Goal:** the last unbound-root site of `ref` — a deref SOURCE under a
fresh destination.
**Landed:** the compiled side only —
`compileStmt_ref_fresh_derefsrc_run/_value`, both first try, generated
from the bound pair by swapping `ensureLocalRegE_existing` for
`_fresh` and evaluating the source's lowering at the post-`Alloc`
compiler state.
**Why it stopped there:** this leaf crosses the fresh machinery with
`ptrChain_lowering_sim` rather than with an extra instruction, and that
lemma takes eleven hypotheses about the state it starts from. The fresh
root forces all of them to be re-established MID-PROOF at the post-
`Alloc` states under the extended renames — roughly 150 lines that the
other fresh leaves only ever needed at the very end. Scoped in the
journal entry; the splice method carries but the seam moves.
**Status:** green; 17/17 + 91/91; audit exact at ONE sorry; residual
sites still 9 (no leaf, so no site closes).
**Next-session pickup:** the leaf itself, then the non-local-source
families (proj-of-proj srcs, non-spine deref srcs, non-local srcs under
non-local dsts).
See journal/2026-08-31-ref-last-unbound-root-recon.md.

## 2026-08-31 (eighth)

**Goal:** finish the last unbound-root leaf of `ref`.
**Landed:** `ref_fresh_derefsrc_simulation` (`dst := &kind *chain`,
`dst` UNBOUND), wired, with witness d79 and teeth. REGIME B of ref is
now TOTAL — all four unbound-root sites closed. Residual sites 9 -> 8.
**Key finding:** this leaf crosses the fresh-root axis with the SPINE,
so `ptrChain_lowering_sim` is applied at the post-`Alloc` states and its
whole hypothesis bundle is re-established MID-PROOF. That was cheap
only because `copy_projlocal_fresh_zero_simulation` had already solved
the same problem for a different statement form — its `h_prb1`/`h_lbs1`
blocks transferred almost verbatim. Generalisation: when a leaf needs an
invariant at an unusual POINT in the statement, look for another
statement form that passes through that point, not for a leaf of the
same form.
**Tooling finding:** `simp only [emit]` unfolds `emit` inside the
compiled state when that state is an ARGUMENT to
`CheckedCompilerM.run`, splitting one term into two `omega` atoms. Use
the projection lemmas (`emit_nextLabel`, `setPlaceInfo_nextLabel`,
`emit_nextReg`, ...) instead. Second known symptom of the same
root cause as csnorm.
**Also:** `subst h : a = b` eliminated `b` (the earlier-introduced
variable), not `a`; and `LocalBindingSim.insert_fresh_reg`'s trailing
`rfl` needs the `have` to ascribe the target oseair state.
**Status:** green; 17/17 + 92/92; audit exact at ONE sorry.
**Next-session pickup:** `ref_place_residual`'s remaining classes —
non-local srcs under non-local dsts, non-spine deref srcs,
proj-of-proj srcs.
See journal/2026-08-31-ref-regime-b-total.md.

## 2026-08-31 (semantic paper rewrite)

**Session:** terminal — syntax/semantics/example restructuring
**Theme:** replaced the Lean-name-oriented rule catalog with a self-contained
semantic account organized around `x.1.0 := 42` throughout MIRLite, OSEA-IR,
compiler translation, and forward simulation.
**Key outputs:** rewritten `mirlite-oseair-correctness.typ`, rebuilt PDF, and
`journal/2026-08/2026-08-31-semantic-narrative-rewrite.md`.
**Key finding:** the nested-field example supplies a useful abstraction test.
It forces the paper to define typed paths, composed offsets, source and target
states, permission events, compiler cleanup, and the renaming relation. It
also makes flattening visibly semantic: the final one-cell borrow preserves
the sibling field that a two-cell intermediate borrow could disturb.
**Status:** complete — clean Typst 0.15.1 build; nine PLDI `acmsmall` pages;
all pages visually inspected at 110 PPI; axiom audit exact at one admitted
reference-assignment case. Appended after the latest concurrent proof session
to preserve strict oldest-first order.

## 2026-08-31 (ninth)

**Goal:** the source-flattening transfer for proj sources.
**Landed:** `placeToBorrowRegChecked_flatten_agree`,
`stepStmt_assign_refsrc_anyflatten`, the congruence
`compileStmt_ref_src_congr_local_run/_value` with the flatten and
reassoc instantiations, and the recursion
`ref_proj_src_local_simulation`. Both base leaves stmt0-threaded.
Witness d80 with teeth. Residual sites 8 -> 7.
**Probe first:** I expected the transfer to be FALSE (the unflattened
`&(s.f).h` looked like it should emit an interior borrow the flattened
form does not). A ten-line `#eval` probe showed both spellings emit ONE
`Borrow` at the summed offset, with the same register and cleanup —
`placeToBorrowRegChecked` has its own reassociating arm, added
deliberately so `&mut s.1.0` does not route through a wide Mut borrow
of `s.1`. One scratch file against a lemma that would not have been
provable.
**Key technique:** a statement-level transfer CANNOT be proved by
rewriting the place inside `compileStmtChecked` — the value's type
mentions the statement, so the motive is not type correct. Factor
through a congruence whose hypotheses are the two agreement facts about
the borrow lowering; the flatten and reassoc transfers are then
one-line instantiations.
**Status:** green; 17/17 + 93/93; audit exact at ONE sorry.
**Next-session pickup:** extend the source-flattening recursion to a
DEREF destination (closes one more site), then the projected dst over a
deref base — the one class neither recursion can normalize away.
See journal/2026-08-31-ref-source-flattening.md.

## 2026-08-31 (tenth)

**Goal:** extend the source-flattening recursion to a deref destination.
**Landed:** `compileStmt_ref_src_congr_deref_run/_value`, the two
reassociation instantiations, and `ref_proj_src_deref_simulation`,
wired; witness d81 with teeth. Residual sites 7 -> 6, and the four
classes collapse to three.
**Key finding:** the recursion generalizes by DESTINATION shape, not by
source. Everything source-side (`placeToBorrowRegChecked_flatten_agree`,
`stepStmt_assign_refsrc_anyflatten`, `flattenPlace_srcproj_assoc`,
`placeToBorrowRegChecked_projassoc_agree`) was reused verbatim; the
per-destination cost is one congruence plus the recursion skeleton.
Everything compiled first try except one point.
**That point:** the deref congruence's VALUE direction needs a case
split the local one does not. With a local destination, once the borrow
lowering succeeds nothing else can fail; with a deref destination the
destination's own `placeToRegChecked` can still fail, so its success
must be extracted from the hypothesis before concluding.
**Status:** green; 17/17 + 94/94; audit exact at ONE sorry.
**Next-session pickup:** the PROJECTED-destination instance of the same
recursion closes class 1 (2 sites) the same way. Then class 3 (three
sites needing two mother-lemma applications in one statement — copy's
two-mother skeleton is the donor) and class 2 (a projected dst over a
deref base, which needs the spine mother lemma on the DESTINATION side).
See journal/2026-08-31-ref-source-flattening.md.

## 2026-08-31 (MIRLite proofreading)

**Session:** terminal — MIRLite notation and semantic correction
**Theme:** replaced undefined and inaccurate shorthand with a typed,
self-contained presentation of layouts, places, retag kinds, state, assignment
semantics, and the complete `x.1.0 := 42` source derivation.
**Key outputs:** corrected `mirlite-oseair-correctness.typ`, rebuilt PDF, and
`journal/2026-08/2026-08-31-mirlite-proofread.md`.
**Critical corrections:** `τ`/`σ` now range explicitly over recursively sized
layouts; `k` includes raw-const, raw-mut, and two-phase as well as shared and
mutable; `ref(k,c,m,p)` carries its protector flag and `UnsafeCell` mask
through source, target, and compiler notation; assignment threads whole states
rather than reconstructing one from loose primed components.
**Status:** complete — clean ten-page Typst build; all pages visually inspected
at 110 PPI; no split tables or overflow; whole-program axiom audit exact at one
admitted reference-assignment root. Appended after the latest proof session to
preserve strict oldest-first order.

## 2026-08-31 (eleventh)

**Goal:** the projected-destination instance of the source-flattening
recursion.
**Correction first:** I had said this instance would close class 1 on
its own. It does not — its base case `t.g := &s.f` was NOT closed, so
the instance needed four new leaves first
(`ref_proj{zero,offset}_projsrc_simulation` and their fresh twins),
each the local-source leaf with `pathOffset f` for `0`. Four fragment
pairs, four leaves; all compiled with only argument-pinning fixes.
**Landed:** those, plus `compileStmt_ref_src_congr_proj_run/_value`
(the congruence, general in the destination base), the reassoc
instantiations, and `ref_proj_src_projdst_simulation`. Witnesses d82
(fresh root) and d83 (bound root), teeth checked separately.
**Count went UP, coverage went up:** residual sites 6 -> 8, because one
coarse `| proj _ _ =>` arm split into three narrow ones while
`t.g := &kind s.f` and `t.g := &kind (s.f).h` became closed. Sites were
never the metric.
**Key finding:** there is exactly one shape index disjointness cannot
reach — a projected dst and a proj src rooted at the SAME UNBOUND local
(`t.g := &kind t.f`, `t` fresh). `g : PathTo σ (PtrL τ)` and
`f : PathTo σ τ` can leave the same layout, so no type argument exists;
the allocation BINDS the source root and the step really succeeds. It
needs a leaf reading the source binding off the post-allocation state
(copy's `h_lbs1` block is the shape).
**Also:** a substitution I omitted (`Rhs.Borrow ... srcReg 0` inside the
code facts) surfaced as `pathOffset f = 0` goals — unification trying to
equate the fragment's offset with the code fact's. And normalising the
destination borrow with `Nat.zero_add` also normalises the SOURCE
borrow's register content, so both run steps must be normalised together
or the run composition stops matching.
**Status:** green; 17/17 + 96/96; audit exact at ONE sorry.
**Next-session pickup:** class 3 (the same-unbound-root leaf, 2 sites),
then class 1 (four sites needing two mother-lemma applications in one
statement) and class 2.
See journal/2026-08-31-ref-source-flattening.md.

## 2026-08-31 (twelfth)

**Goal:** class 3 — the same-unbound-root leaves.
**Landed:** `compileStmt_ref_proj{zero,offset}_fresh_selfsrc_run/_value`
and `ref_proj{zero,offset}_fresh_selfsrc_simulation`
(`t.g := &kind t.f`, `t` fresh), wired into both none/none branches of
`ref_proj_src_projdst_simulation`; witnesses d84 and d85 with teeth
checked separately. Residual sites 8 -> 6, classes 3 -> 2.
**Shape of the work:** the leaves are the distinct-root fresh leaves
with the source-facts prologue REPLACED rather than substituted — the
binding is the one `allocateRoot` just made, its register is the root
register (`getPlaceInfo_setPlaceInfo_self`, no survival argument), and
address/tag/non-wildcard/block-domain all come from the extended
renames. All four fragments and both leaves compiled first try.
**Two traps:** (1) `h_rtS1` and the non-wildcard fact are consumed by
`sb_ref_respects_PermSim`, which sits earlier than where the
distinct-root leaves define them — hoist `h0`/`h_nwD` above §5. (2)
`induction sbase` gives the source base's layout an INACCESSIBLE name,
so the `σb` from the binders is not in scope; bind it in the case
pattern (`| @«local» σ' srcLoc =>`) or the layout-equality step cannot
be stated at all. `trace_state` showed this in one build.
**Status:** green; 17/17 + 98/98; audit exact at ONE sorry.
**Next-session pickup:** the last two classes — a deref-rooted SOURCE
under a non-plain-local destination (5 sites, two mother-lemma
applications in one statement; copy's two-mother skeleton is the donor)
and a projected dst over a DEREF base (1 site, needs the spine mother
lemma on the DESTINATION side).
See durable/ref-residual-site-map.md.

## 2026-08-31 (OSEA-IR/compiler/correctness proofreading)

**Session:** terminal — semantic audit and twenty-page paper completion.
**Goal:** bring the OSEA-IR, compiler, and compiler-correctness sections to the
same self-contained standard as the corrected MIRLite section.
**Landed:** exact target runtime syntax and operational cases; compiler
state-delta judgments, root/place/reference lowering, full executable lowering
surface, prefix-label discipline, and flattening account; the ten-component
statement-boundary invariant, corrected step/whole-program statements,
canonical initial relation, observable consequences, and explicit extension
obligations.
**Critical corrections:** target registers use erased `TyVal` (`PTy` for every
pointer layout); `die` has no separate allocation-bounds check; address
renaming is identity on its domain; the compiler state remains fixed during
simulation while only address/tag maps extend.
**Verification:** clean Typst build at exactly 20 PLDI review pages; all pages
rasterized and visually checked. Axiom audit passes its whitelist at
`ddc35d1` with exactly one admitted residual reference-assignment root.
Concurrent proof and `CLAUDE.md` work was left untouched.
**Record:** journal/2026-08/2026-08-31-oseair-compiler-correctness-proofread.md.
Appended after the twelfth proof session to preserve strict oldest-first order.

## 2026-08-31 (thirteenth)

**Goal:** class 1 — the deref-rooted sources.
**Landed:** the LOCAL-destination half —
`compileStmt_ref_derefprojsrc_run/_value`,
`compileStmt_ref_fresh_derefprojsrc_run/_value`,
`ref_derefprojsrc_local_simulation`,
`ref_fresh_derefprojsrc_simulation`, wired into
`ref_proj_src_local_simulation`'s `deref` case with the source-flatten
transfer. Witness d86 exercising both leaves in one program, teeth
confirmed. Residual sites 6 -> 5.
**Key finding:** `placeToRegChecked`'s deref arm IGNORES its `kind` —
it lowers the pointer at `Shared` and `Load`s regardless. So a
deref-rooted source emits exactly the chain code a plain deref source
emits, differing only in the `Borrow`'s offset operand, and the mother
lemma can be invoked at `kind` and consumed unchanged. That made this
half the same offset substitution used five times before.
**One wrinkle:** the machines spell the stored pointer's offset
differently — mirlite `addr + off - allocBase`, oseair
`addr - allocBase + off` — agreeing only given `allocBase ≤ addr`
(`h_dle` from the mother lemma). `Nat.sub_add_comm h_dle` is the
bridge; an inline `omega` reports a spurious counterexample over
compiler-state atoms, so name the equation.
**What did NOT land:** the other four class-1 sites, all of which put
TWO mother-lemma applications in one statement (chain source × chain or
projected destination). That is genuinely new structure, not a
substitution; copy's two-mother skeleton is the donor.
**Status:** green; 17/17 + 99/99; audit exact at ONE sorry.
**Next-session pickup:** the two-mother skeleton for ref, which covers
all four remaining class-1 sites at once; then class 2.
See durable/ref-residual-site-map.md.

## 2026-08-31 (fourteenth)

**Question:** could oseair spell a pointer's offset as
`addr + off - allocBase` so the proofs line up?
**Answer: no, and it would not help.** The mismatch is a
REPRESENTATION difference, not a syntax choice: mirlite's `PlaceRes`
carries an absolute `addr` and subtracts once when a pointer value is
built; oseair's `Val.Ptr` carries the offset and `Rhs.Borrow`
accumulates it by addition. Emitting
`Val.Ptr base (base + baseOff + offset - base) ...` is the same number
unconditionally, but since `baseOff` is itself `addr - allocBase` the
term becomes `allocBase + (addr - allocBase) + off - allocBase`, which
still needs `allocBase ≤ addr`. The obligation moves, it does not
vanish — and it would change the target semantics to suit a proof and
churn 325 `Val.Ptr` spellings.
**What landed instead:** the csnorm move — name the bridge once.
`resolvedAddr_cancel` and `resolvedOffset_shift` in common.lean, with
the representation difference documented at the definition. The 38
existing inline `h_cancel` sites are left alone (churn, no gain); new
leaves use the named form.
**Status:** green; 17/17 + 99/99; audit exact at ONE sorry.
See durable/resolved-address-vs-pointer-offset.md.

## 2026-08-31 (fifteenth)

**Attempted:** reparameterize `mirlite.PlaceRes` to carry `offset` with
`addr` derived, so mirlite and oseair share one pointer representation.
**Sound and verified:** the invariant `addr = allocBase + Σoffsets`
holds in all three `resolvePlaceAcc` arms and there is no other
constructor, so it is faithful. The SEMANTICS change alone built clean
with the corpus unchanged — 17/17 + 99/99, identical verdicts. Patch
kept at notes/attic/placeres-offset-reparameterization.patch.
**Reverted, and why:** my cost estimate ("35 literals plus fallout") was
wrong. The literals were 28 and mechanical. What I missed is that
deriving `addr` changes the ASSOCIATIVITY of every projected address —
`allocBase + (offset + k)` where the proofs say `(allocBase + offset) + k`
— so ~50 sites across const_write/copy/ref stop matching. Three
automated passes moved the count 59 -> 46 -> 55 -> 67, non-monotone
because Lean reports one error per declaration and each fix unmasks the
next. It needs a per-declaration migration, not a script.
**Judgement:** the payoff (`h_dle` trivial, `h_cancel`'s 38 derivations
and 143 uses gone) is a fixed one-time cost of ~50 sites against FIVE
remaining residual sites. It would have paid for itself hundreds of
leaf-lines ago; not now. Do it first if the leaf population ever grows
again.
**Status:** reverted to green; 17/17 + 99/99; audit exact at ONE sorry.
See durable/placeres-offset-reparameterization.md.

## 2026-08-31 (sixteenth)

**Parked first:** the PlaceRes reparameterization is now recorded in
loose-ends/parked.md with soundness evidence, the revert reason, the
payoff, the trigger condition and a resume recipe.
**Then continued on class 1.** Key finding: the class is NOT uniform. A
projected destination over a LOCAL base has no spine, so
`t.g := &kind *p` and `t.g := &kind (*p).f` need only ONE mother lemma
— the source's. Only the two DEREF-destination sites need two.
**Landed (all first try):** `placeToRegChecked_deref_cleanup` (the
standalone cleanup fact, needed BEFORE the mother lemma exactly as
`PtrChain.placeToRegChecked_placeRegMap` is),
`compileStmt_ref_projzero_derefsrc_run/_value`, and
`ref_projzero_derefsrc_simulation` (`dst.g := &kind (*p).f`, both roots
bound, dst offset 0).
**Deliberately NOT wired:** wiring one quadrant of the 2x2 (dst offset x
bound/fresh root) would split one residual arm into three and fragment
the site map for no coverage gain. Precedent: commit 5e8e67c landed a
compiled side ahead of its leaf the same way.
**Also recorded:** `&kind *p` and `&kind (*p).nil` emit identical code
but are different TERMS, so the plain deref source needs its own
statement — one leaf cannot serve both.
**Status:** green; 17/17 + 99/99; audit exact at ONE sorry; residual
sites still 5.
**Next-session pickup:** the other three quadrants, then the same four
for the `.deref P` source spelling, then the two-mother skeleton for the
deref-destination pair.
See journal/2026-08-31-ref-chainsrc-projdst.md.

## 2026-08-31 (seventeenth)

**Goal:** the other three quadrants of `dst.g := &kind (*p).f`.
**Landed:** ONE of three — `ref_projzero_fresh_derefsrc_simulation`
(offset 0, FRESH root) — plus the compiled sides of BOTH nonzero
quadrants (`compileStmt_ref_projoffset_derefsrc_run/_value`). All three
fragment pairs this session went through first try.
**Not landed:** the two nonzero LEAVES. They are not substitutions: the
zero-offset destination phase is one `RStore` through the root
register, the nonzero one is four steps with BRIDGE 1, and the mirlite
write inversion has to move ahead of the execution steps to supply the
collapsed tags. Same assembly as `ref_projoffset_fresh_simulation`;
the exact splice recipe (which sections, which re-spellings, which peel
counts) is written down in the journal entry.
**Observation worth acting on:** the four quadrants differ ONLY in how
the destination lowers; everything downstream is uniform. A
DESTINATION-side package — `LoweringSim` for destinations — would
collapse all four into one leaf. The earlier decision not to build a
source-side package does not transfer: for sources each shape needed
its own extraction, whereas for destinations the four shapes already
exist as proved leaves, so the package can be read off them. Doing it
before the two-mother sites avoids repeating the four quadrants there.
**Status:** green; 17/17 + 99/99; audit exact at ONE sorry; residual
sites still 5 (nothing wired yet — the quadrants are incomplete).
See journal/2026-08-31-ref-chainsrc-projdst.md.

## 2026-08-31 (eighteenth)

**Goal:** build the destination-side package.
**Correction, checked before building:** it does not do what I claimed.
`LoweringSim` IS already the destination package for shapes that supply
it, and a projected destination at ZERO offset does — but it demands
`placeOut.result.cleanup = []`, and the projection arm at NONZERO
offset returns `cleanup ++ [(tmpReg, blockSize τ)]`. So the package
covers exactly the two quadrants that were already cheap, and covering
the other two means restating it with the cleanup and packaging
BRIDGE 1 — the very assembly it was meant to avoid.
**So I did the assemblies instead, and all four quadrants are done:**
`ref_projoffset_derefsrc_simulation` (bound) and
`ref_projoffset_fresh_derefsrc_simulation` (fresh), each the
zero-offset leaf with the write inversion moved ahead of the execution,
peel counts widened from two to four, the interior
`Borrow(Mut)`/`RStore`/`Die` added and the rebuild collapsed. Both
fragment pairs first try, as were all four in this family.
**Wired, and a site CLOSED:** `t.g := &kind (*p).f` for every
destination offset and root state, through
`ref_proj_src_projdst_simulation`. Residual sites 5 -> 4. Witness d87
at the hardest quadrant (fresh root, nonzero offset), teeth confirmed.
**Status:** green; 17/17 + 100/100; audit exact at ONE sorry.
**Next-session pickup:** class 2's `t.g := &kind *p` (a spelling
artefact — identical code, different term), then the two-mother sites.
See durable/ref-residual-site-map.md.

## 2026-08-31 (nineteenth)

**Goal:** the cheapest remaining site, `t.g := &kind *p`.
**Found:** it is a spelling artefact, and `flattenPlace` cannot fix it —
flattening never introduces an empty projection. Built the NIL
PROJECTION ETA instead: `resolvePlaceAcc_nil`,
`stepStmt_assign_refsrc_nil`, `placeToBorrowRegChecked_nil_agree`, and
the two congruence instantiations (projected and deref destinations).
The compiled halves coincide because `placeToRegChecked`'s deref arm
returns an empty cleanup, so the projection arm's `[] ++ [tmp]` is
`[tmp]` and both emit the same instructions from the same counter.
**Paid twice:** under a PROJECTED destination the eta CLOSES
`t.g := &kind *p` (into today's four quadrants); under a DEREF
destination it MERGES `*chain := &kind *chain'` into
`*chain := &kind (*p).f`. Sites 4 -> 2.
**Status:** green; 17/17 + 101/101; audit exact at ONE sorry.
Witness d88, teeth confirmed (ub at statement 7 when the source is
retargeted to `(*p).0`).
**Next-session pickup:** both remaining sites are two-mother shapes —
class 1 a source spine under a destination spine, class 2 a destination
that is itself a `derefProj` chain. `copy`'s two-mother skeleton is the
donor for both.

## 2026-08-31 (twentieth)

**Goal:** the two-mother leaf.
**Done, first try:** `ref_derefdst_derefprojsrc_simulation` —
`*D := &kind (*P).f`, a chain source under a chain destination, 453
lines, sorry-free on the first build. Source mother at `kind`, one
`Borrow` at the field offset, `sb_ref_respects_PermSim` extending ρt,
destination mother at `Mut` from the post-`Borrow` state, one `RStore`
through BRIDGE 2. The compiled fragment pair
(`compileStmt_ref_derefdst_derefprojsrc_run/_value`) also first try.
**Why it was cheap:** both `placeToRegChecked (.deref _)` calls leave an
empty cleanup, so no `Die` is emitted (no BRIDGE 1) and the whole
compiled shape is known before either mother — each of the three
code-inclusion obligations is ONE `StateIncr` step off `h_stmtRun`,
where copy's two-mother leaves need fifty-line towers.
**Wired** through `ref_proj_src_deref_simulation`, flattening both
chains (`compileStmt_ref_srcflatten_deref_run/_value` added). By the nil
eta this also closes `*chain := &kind *chain'`. Sites 2 -> 1.
**Status:** green; 17/17 + 102/102; audit exact at ONE sorry.
Witness d89, teeth confirmed.
**Next-session pickup:** the LAST site, `(*p).g := &kind _` — the same
two mothers plus the projection's interior `Borrow(Mut)`/`Die` that
BRIDGE 1 must collapse. Donors named in
durable/ref-residual-site-map.md.

## 2026-08-31 (twenty-first)

**ZERO SORRIES.** `ref_place_residual` is closed and DELETED;
`obseq3.proof.compile_correct` rests on `propext`, `Classical.choice`,
`Quot.sound` alone and the whitelist no longer lists `sorryAx`.
**The last site** was `(*p).g := &kind _`, a projected destination over
a deref base. Two leaves, split on the destination offset: at ZERO the
destination supplies the `LoweringSim` package
(`LoweringSim.projZero`) and it is the two-mother assembly respelled;
at NONZERO the projection mints its own interior `Borrow(Mut)` and
BRIDGE 1 collapses the triple — the only leaf where two mothers and
BRIDGE 1 meet.
**The move that halved the work:** both leaves are GENERIC in the
source. A leaf needs the source constructor only for a definitional
unfolding, so `placeToBorrowRegChecked_proj_root_eq` (side condition
`PtrChain.not_proj`) takes its place, and `ptrChain_lowering_sim`
already covers a LOCAL source at zero steps. Four leaves became two.
**Also landed:** the nil eta at a general chain base
(`placeToBorrowRegChecked_nil_agree_local/_chain`,
`placeToRegChecked_local_cleanup`) and the destination flatten transfer
for a projection over a deref
(`compileStmt_assign_projderefdst_flatten_run/_value`).
**Status:** green; 17/17 + 103/103; audit exact at ZERO sorries.
Witnesses d89 (two mothers) and d90 (two mothers + BRIDGE 1), teeth
confirmed.
**Next-session pickup:** there is no residual left in obseq3. See
durable/ref-residual-site-map.md for the retired site map and the two
structural facts worth reusing.

## 2026-08-31 (twenty-second)

**The base case is closed too.** `compile_correct` took `CompilerInv`
at the entry as a HYPOTHESIS and nothing in-tree discharged it, so the
chain "compile a program, run it from entry" was not closed in Lean
even with zero sorries. `CompilerInv_initial` + the corollary
`compile_correct_from_initial` (proof/compiler.lean §Z) close it, and
BOTH are now audited roots of scripts/audit_axioms.sh.
**The one non-obvious conjunct:** ρa is empty at entry but ρt is NOT —
`TagRenameWF` demands the wildcard be fixed, so the initial ρt is the
singleton `wildcardTag ↦ wildcardTag`. It satisfies
`TagRenameBounded` only because `wildcardTag = 0` and both machines
start at `NextTag = 1`.
**Status:** green; 17/17 + 103/103; audit exact, two roots, ZERO
sorries, axioms `propext`/`Classical.choice`/`Quot.sound`.
**Scope, written down so it stops being re-derived:** see
durable/what-compile-correct-actually-says.md. Two limits remain and
neither is a hole — the `CoreProg` gate (three rvalues; `assignIf`,
`alloc`, `dealloc`, protectors and six other rvalues excluded), and the
DIRECTION (forward simulation of successful runs; UB preservation is
tested by the expectDiff corpus, not proven).
**Next-session pickup:** widen `CoreRhs`, or attack the backward
direction. Widening is the cheaper of the two and `uninit` is the
smallest next rvalue.

## 2026-08-31 (twenty-third)

**Started widening `CoreRhs` with `uninit`.** Regime A done: the
constant-store leaf is now GENERIC in the rvalue
(`const_store_local_existing_simulation`), `constInit` re-derives from
it as a 12-line instantiation, and `uninit_local_existing_simulation`
is the second instance.
**Why it is cheap:** the plumbing was already width-general
(`writeThroughPtr_sim`, `runN_CStore_step`, and `LocalBindingSim`'s
block-domain conjunct — which the single-cell `constInit` leaf bound
and never used). Only the leaves hardcoded `NatL`/one cell. And
`uninit`'s new obligation is free: `MemValSim`'s first clause is
`| .undef, _ => True`.
**Shape that works:** parameterize by `(rhs, vs, vs')` + three length /
relation hypotheses, and thread the compiled shape as `h_run0`/`h_val0`
— `RhsPre`'s evidence field is dependent, so "the rhs lowers to one
CStore" cannot be an equation on `compileRExprPreChecked`.
**Status:** green; 17/17 + 103/103; audit UNCHANGED (two roots, zero
sorries). `CoreRhs` deliberately NOT widened — it must stay at three
rvalues until the whole const-write dispatcher is total, so this
increment changes no theorem statement.
**Next-session pickup:** regime B (fresh local), then the five
projected-destination leaves, then regime D and the dispatchers. Same
substitution throughout; see journal/2026-08-31-uninit-regime-a.md for
the three mechanical traps.

## 2026-08-31 (twenty-fourth)

**`uninit` IS NOW A CORE RVALUE.** `CoreRhs` went from three members to
four; `compile_correct` routes `.uninit` to `CompilerInv_step_uninit`.
The theorem's scope now covers undef-fill of ANY place at ANY layout
type.
**How:** all nine const-store leaf families were restated over an
arbitrary rvalue and value pair (`const_store_*`), with `constInit`
re-derived as an instantiation; then the three dispatchers, the
statement-evidence lemma and the top-level step were generalized the
same way. The rvalue enters through ONE bundle,
`ConstStoreFrags rhs vs'` — nineteen fields, proved once per rvalue —
because for a variable `rhs` `compileRExprPreChecked rhs` does not
reduce and no fragment lemma can be generic.
**Two real corrections, not just widenings:** regime B-proj's
`extendIdRange` left a ZST referent's root base unmapped (now
`extendBlock`); and three leaves proved a `StateIncr` by a
destination-before-rhs `rfl` that holds only when the rhs pre-phase
emits nothing.
**Status:** green; 17/17 + 104/104; audit exact, two roots, ZERO
sorries. Witness d91 (wide undef fill + undef through a pointer), teeth
confirmed — and the teeth taught something: reading undef is NOT ub in
this model, only observing it as a pointer/branch/length is.
**Next-session pickup:** the cheapest remaining widenings are
`pushProtectors`/`popProtectors` — one instruction each, and both
machines run literally the same expression (see the protector agent
result quoted in obseq2-comparison.md if written up). After that, the
other six rvalues, or the backward (UB-preservation) direction.

## 2026-09-01 (twenty-fifth)

**Wrote up the protector / Charon-seam question** as
durable/protectors-and-the-charon-inlining-seam.md, from reading the
syntax, both semantics, sb.lean and src/conformance/lowering.lean.
Answers "who decides which tags are protected?": nobody in mirlite —
the LOADER does. mirlite has no calls at all; `inlineCall` splices the
callee body and emits `pushProt` / argument retags with `prot := true` /
`popProt` / an UNPROTECTED return retag around it. A tag enters a frame
in exactly one place (`sb_ref`'s `prot` branch), always the fresh child,
always the innermost frame, and an absent frame is an ERROR not a no-op.
**Also recorded:** protection is a membership SET beside the stacks, not
a field on an item; the three writes that touch `protFrames`; the
loader's limits (depth-8 inlining, no recursion, no indirect calls,
allocator shims, the known weak-box-protection divergence); and that
none of that layer is verified — it is upstream of `compile_correct`.
**Cross-linked** from durable/what-compile-correct-actually-says.md,
which also now records `uninit` as a core rvalue.
**No code changed.**

## 2026-09-01 (twenty-sixth)

**Extended the lowering note** with every other non-trivial conversion
`src/conformance/lowering.lean` performs, with verified file:line
refs: CFG linearization (loops/unwind rejected), asserts discharged by
constant folding at lowering time, the constant-propagation pass
(`constOf`/`foldBinOp` — which folds Checked/Wrapping arithmetic to
plain `Int`, a live divergence), array indices resolved to field
projections (`resolveIdxPlace`, NOT `resolveIdxProjs` — I had the name
wrong), statics hoisted with initializers NOT run, unit aggregates kept
as access-free `uninit` so ZST destinations still allocate, aggregate
desugaring and where `assignIf` really comes from (enum payload seam
retags, not branching), static fn-pointer tracking, and the heap /
interior-mutability shims.
**The pattern worth keeping:** everything dynamic is resolved
statically or the program is rejected — which is what lets mirlite be
flat with no value analysis, and why several of these are semantic
divergences that live entirely above `compile_correct`.
**No code changed.**

## 2026-09-01 (twenty-seventh)

**Skeleton refactor, items 3 and 5** — the two largest in-scope steps of
`plans/floating-strolling-shannon.md`. Proof dir 42,526 → 39,819
(with items 0–2 from earlier the same day, 43,694 → 39,819).

**Item 3, `EmitTower`** — the `h_code*` idiom located one instruction of
an emitted fragment by re-deriving the whole compiler-state tower as a
literal, at O(n−k) rewrites for the k-th of n instructions. `EmittedAt`
walks the tower instead of transcribing it; `EmitTower` makes that walk
an *instance-resolution* problem with the instruction list as an
`outParam`, so no call site spells the chain at all. 116 of 168 blocks
converted, −1,921 lines.
**The load-bearing accident:** `emitTower_nil` fires at the first state
that is not `emit`/`setNextReg`/`setPlaceInfo`, which in a leaf that
calls the mother lemma is `CheckedCompilerM.run (placeToRegChecked …)`.
So the inferred base is the mother's output `nextLabel` — exactly what
`h_dpc`/`h_spc` already say — and the indices come out *group-local*,
matching the convention the hand-written blocks already used. Every
`h_q` is `rfl`.

**Item 5, `LowersTo`** — merges `X_run`/`X_value` so their shared
preamble is paid once. Only 22 of 64 pairs may merge, and each filter
was found by a failing build: hypotheses must agree (25 pairs have a
`_run` that also needs `h_dclean`, and `ConstStoreFrags`'s `…Val` fields
deliberately lack it); only `obtain`/`have`/`let` may be shared, because
a goal-directed tactic means different things against a `run` goal and a
`value` goal; and the `_value` conclusion must really be
`∃ x, value … = .ok x` (several are congruences opening with `intro`).
−851 lines.

**Re-measured the plan — the original estimates are now stale.**
Target C (`h_inst`/`StateIncr`, estimated 2,102 lines) was already
absorbed by item 2's `CodeIncluded`: those blocks are 2 lines each now.
Target A (`CompilerInv` rebuild tails) is not one 3,150-line win but a
long tail: bullets 4–6 cost 1,453 lines, and the `getPlaceInfo` chase
inside them is *pure defeq* (`getPlaceInfo_emit`/`_setNextReg` are
`rfl`) — but sweeping that across 146 sites buys only 95 lines and
breaks ~20 chains whose later `rw` depended on the peeling. Realistic
remaining value in A is ~700 lines spread over many micro-lemmas.

**Where the repetition actually lives now.** ref 69.5% and copy 71.9% of
code lines sit in ≥8-line blocks repeated ≥2×, essentially unchanged by
skeleton factoring — but const_write is at 38.2%, and const_write is the
one file whose *leaves* were generalized over the rvalue
(`ConstStoreFrags`). That is direct evidence that leaf-collapsing, not
skeleton factoring, is what moves the number. It remains out of scope
for this plan.

**Validation after every commit:** 0 errors; audit OK, 0 sorries, axioms
unchanged (propext, Classical.choice, Quot.sound); 17/17 + 104/104.

## 2026-09-01 (twenty-eighth)

**Corrected the lowering note on two points, and found a validation gap.**

**The five "passes" in `lowering.lean`'s header are concerns, not
stages** — the docstring says "fused into one walk" and that is literal.
One `mutual` block (:627-734), one entry (:796), no intermediate IR. I
had been describing pass 1 (inline) and pass 5 (seam retags) as
sequential, which makes them a paradox: inlining destroys the call
boundary, seam retags preserve the only part of it Stacked Borrows can
see, and a real pass 5 would have to reconstruct the seams from exactly
what inlining erased. Fusion sidesteps it — `walkCall` still holds the
args, callee signature and destination, so it emits the seam *around*
the recursive `walkBlock` that inlines. Details and the emission order
(protected arg retags, unprotected return retag, emitted after
`popProt`) now in the durable note.
Also recorded there: `emitSeamCopy` is keyed on `UTy`, not on calls —
one of its three call sites (:303-307) has no call near it, because Miri
retags reference-typed values loaded through an indirection.

**Why tuple aggregates are desugared:** mirlite has no aggregate rvalue.
`RExpr` is nine constructors, each writing one value to one place. Free
under SB (Miri writes fields in turn; disjoint cells), but an aggregate
rvalue would cost a full family of simulation leaves per destination
place shape and prove nothing the `copy`/`constInit` leaves don't.

**VALIDATION GAP — the triad was missing a suite.** `sb_conformance
--unit` runs only the two in-Lean suites (17/17 mirlite semantics,
104/104 compiler witnesses). The ULLBC conformance corpus needs
`--manifest conformance/manifest.json --charon-dir conformance/charon`,
and the differential mode needs `--osea` on top. Ran both against the
current tree: **82 pass / 0 fail / 41 unsupported (123 total)**, and
**osea: 82 matched / 0 mismatch / 0 skipped**. The 0-skipped is worth
noting — every program the mirlite side accepts, the compiler also
handles, so `CoreProg` covers the whole live corpus.
Run all four from now on, not just `--unit`.

## 2026-09-01 (twenty-ninth)

**Finished the skeleton refactor. 43,694 → 39,609 for the day (−9.35%),
eight commits, zero sorries and an unchanged axiom set throughout.**

This entry covers the last four steps and, more importantly, records
which remaining plan items are DEAD so nobody re-attempts them from the
stale estimates.

**Target E — `exceptMap_agree`** (−91). All six `_src_congr` lemmas
opened with the same four-way `cases` on two `placeToBorrowRegChecked`
values. That is pure `Except` algebra. The catch: the two payload types
must be allowed to DIFFER, because the evidence in a borrow result is
indexed by the source place — which is exactly why the `_congr`
hypotheses go through `.map (·.result)` in the first place. Family 283
→ 168.

**`bridge1S_of_read`** (−35). Eight copy leaves ran the same eleven-line
ritual. Two shape decisions were forced by the sites: it takes the
already-transported read (some leaves need that `PermSim` before the
write transport), and it must return `tgtAcc.NextTag ≤ q3.NextTag`
(eleven downstream sites wanted `h_ntle`).

**Two adoptions** (−84). `resolvedAddr_cancel` at 44 sites — note it is
*definitionally* `Nat.add_sub_cancel'`, so the term swap saves nothing;
the saving is that the named lemma makes the type ascription inferable,
collapsing a 2-line `have` to 1. `AllocLockstep.writeWordSeq` at 31 of
53 bullets.

**[DEAD] item 6, `assignPlaceArm` — do not attempt.** The plan valued it
at ~160 lines on the assumption that the `_src_congr` proof BODIES were
the cost. After target E they are not: the family is 105 statement lines
to 57 proof lines, and deref+proj proof bodies total 42 — the entire
merge ceiling. A generic congruence needs its own ~20-line statement and
~20-line proof, so the net is between +20 and −5.
Against that: once `.assign dst rhs` delegates to `assignPlaceArm`,
`simp only [compileStmtChecked]` no longer reaches the do-block, so
**159 sites** (const_write 30, ref 56, copy 73) need `assignPlaceArm`
added to their simp sets — and it is a change to the compiler itself,
under both audit roots. There is no cheap route: an `h_unfold`
hypothesis avoids the churn but its explicit do-block costs what the
merge saves, and no `@[reducible]`/`@[simp]` attribute makes
`simp only [X]` reach through a separate `def`.
Worth doing ONLY if `assignPlaceArm` is wanted structurally, for naming
the arm — not for line count.

**[DEAD] target A / item 4 remains parked**, and target C was absorbed
by `CodeIncluded` back in item 2.

**Still open, all small:** the 11 AllocLockstep bullets that end in
`rw [h_addr_eq, h_sz]` (the *allocate* case, wanting
`AllocLockstep.allocate_eq`; ~11 lines); the `csnorm` global `@[simp]`
change (~20 lines, previously reverted because blind deletion of the
redundant tactics broke three `rfl`s).

**The plan is now mined out.** ref and copy are still ~70% repeated
lines; const_write is at 38%, and it is the one file whose *leaves* were
generalized over the rvalue. The remaining mass is leaf bodies, not
skeleton, and getting at it is a design change (collapsing leaves onto
bigger place classes), not a refactor — a new plan, explicitly out of
scope for this one.

## 2026-09-01 (thirtieth)

**A second refactor seam, larger than the first: 39,609 → 37,769
(−1,840) in seven commits, none of which touched a proof argument.**

The skeleton plan was mined out (see the twenty-ninth entry). What was
left turned out not to be proofs at all — it was tactic *invocations*
re-listing what could be named once, and binder lists re-declaring what
could be hoisted. Full mechanics in
[[attribute-and-binder-mechanics]]; the headlines:

| change | sites | lines |
|---|---|---|
| nine `@[grind]` registrations + 2 collapses | 27 | −187 |
| **`csMonad` simp set** | **200** | **−659** |
| `csRun` simp set | 142 | −91 |
| `csCompile`/`mirPrep`/`mirAlloc`/`csCleanup` | 264 | −137 |
| **`writeResolvedPlace_ok_inv`** | **52** | **−415** |
| `variable` hoist of ambient implicits | 64 | −208 |
| copy's towers in `with` form | 253 | −214 |

**The two biggest were both invisible to "factor out a lemma".**
`csMonad` is six lemmas that are ALREADY global `@[simp]` — every
`simp only` site re-listed them because `simp only` excludes the default
set. `writeResolvedPlace_ok_inv` replaced an eight-line `split`/`split`
header whose dead branches wrapped the whole rest of each proof in
nested bullets, so the real cost was four columns of indentation all the
way down.

**Method that found them:** rank repeated N-line windows across the leaf
files, then score each candidate by MEASURED line saving rather than
site count. That distinction mattered every time —
`{emit, List.length_cons, List.length_nil}` occurs at 78 sites and is
worth zero lines.

**Three things measured and declined**, so they are not re-attempted:
folding `compileRExprToChecked` into `csCompile` (27 lines, but 88 of
162 sites would start unfolding the rvalue compiler); hoisting the
explicit hypotheses alongside the implicits (~198 lines, but needs
`include` and reorders every leaf's explicit arguments); and converting
copy's NESTED tower records (92 more records, builds clean, makes the
file 92 lines and 22 KB *bigger* — see the note).

**Still open and correctly parked:** target A (rebuild tails, ~700),
item 6 `assignPlaceArm` (dead — see loose-ends/parked.md), the 11
AllocLockstep *allocate* bullets, and `csnorm` global `@[simp]`.

**The structural position is unchanged and is the real finding of the
day.** All of this was skeleton and notation. ref and copy still sit at
~70% repeated lines against const_write's 38%, and const_write is the
one file whose *leaves* were generalized over the rvalue. The remaining
mass is leaf bodies. Getting at it means widening the source place class
so all six source shapes go through one mother lemma — a design change
and a new plan, not another sweep.

**Validation after all seven commits, every time:** 0 errors; audit OK,
0 sorries, axioms unchanged; 17/17 + 104/104; conformance 82 pass /
0 fail; osea 82 matched / 0 mismatch / 0 skipped.

## 2026-09-01 (thirty-first)

**The leaf-collapse spike landed** (`29513f6`, `e1c846f`): the
nonzero-offset compiler equations, then `copy_projdst_zero_after_read` —
the destination half of `dst.f := copy src` proven ONCE over an abstract
post-read state, with both projdst_zero leaves ending in one call to it.

**The plan's design was wrong and the code said so before any proof
did.** Widening `LoweringSim` past `cleanup = []` was the approved
shape; in fact TWO conjuncts break at nonzero offset (the register holds
a FRESH borrow tag, falsifying the ρt-tag conjunct, and PermSim cannot
hold while the borrow is live). The decisive fact: the copy arm emits
`[Load] ++ cleanupInstrs srcRes.cleanup` in one breath, so Borrow/Load/
Die completes BEFORE the destination lowering and PermSim is restored by
the Die. The right seam is therefore the READ, not the place lowering —
`LoweringSim` and its ten users stay untouched.

**Elaborator-found facts** worth keeping: the after_read theorem needs
no `path` binder — the destination half is PROJECTION-AGNOSTIC, so the
chaindst family (same §7 marker, 3 more leaves) should reuse it as-is;
and the mirlite write runs on the POST-RESOLUTION perms `permsD`, not
the post-read `perms₂` (resolution performs SB reads of its own).

**The re-measure the plan demanded:** per-pair net is ~135 lines, not
the ~590 ceiling — the two source halves genuinely differ (53.5% bag
overlap) and survive. The real win is marginal cost: a new source shape
now costs its source half only (~150-250 lines) against ~550 for a full
leaf, and one 203-line destination half serves the family. The sweep's
value is therefore in the leaves-per-destination count (chaindst 3,
projlocal_fresh 4, fresh 3), not in pair merging.

Validation, all four suites, both commits: 0 errors; audit OK,
0 sorries, axioms unchanged; 17/17 + 104/104; 82/0; osea 82/0/0.

## 2026-09-01 (thirty-second)

**2a landed** (`3aac3b6`, −527): the seam renamed
`copy_chainwrite_after_read` and the three chaindst leaves converted
onto it — no new machinery, five leaves now share the one 203-line
destination half. chaindst 475→293 / 483→303 / 613→446.

Two splice traps recorded in the plan's constraints, both hit again:
`^theorem` anchored at the theorem's own index matches ITSELF (a block
move must search from index+1 — one red build: the docstring moved, the
theorem stayed), and the saved call template still carried the raw
`sb_read_NextTag h_read_src` instead of the `.trans h_snt1` chain.

**2b measured, not started.** projlocal_fresh INVERTS the anatomy —
fresh-root Alloc first, then source, then write — so its shareable
piece is a PREFIX lemma, not a suffix seam. The four §1–§6 prefixes are
97%/84% similar (same/cross source), ~270 lines each, with a ~35-fact
output interface: `ConstStoreFrags`-style structure, one prefix lemma,
expected ≈ +690. Write tails pair 2×2 and roughly break even — only if
the prefix goes smoothly. Details in the plan (rev. 2).

Validation, all four suites: 0 errors; audit OK, 0 sorries, axioms
unchanged; 17/17 + 104/104; 82/0; osea 82/0/0. Proof dir 37,160.

## 2026-09-01 (thirty-third)

**2b landed by a different route than planned: offset-twin merges, −465**
(`41b2017`). The FreshRootPrefix interface was measured and declined —
its real coverage shrank as the anatomy came into focus (interleaved
§1/§3 h_step inversions, §5b dst-offset fork, 61% cross-family
similarity vs the 84–97% headline; realistic net ~330 for spike-level
effort). The same measurement exposed the cheap move: destination-offset
TWINS are byte-identical through `h_incrS1V` (422/488 lines for one
pair, 194 shared middle for the other). Each pair is now ONE theorem
with `by_cases h_o` at the first genuinely forked tactic — the 2-line
offset-zeroing simp MOVES into the positive branch because nothing
between §3 and the fork touches `h_step`. Both merges compiled on the
FIRST build; the dispatch sites lost their by_cases.

**Twin-merge preconditions** (worth reusing on ref): binders differ only
in h_o; the h_o-consuming simp is movable; shared middle byte-identical
sans the two h_o' lines. Two pairs checked and FAILED the test —
fresh_projchain zero/offset (the read address itself differs at §3) and
the cross-family projdst pairs (fork at ~40, all after duplicates).

**Copy is swept.** 19 → 15 leaves: five on `copy_chainwrite_after_read`,
two twin-merged. Remaining items (fresh ×3, projdst_offset ×2,
projchain/small ×5) are break-even per the measured economics. Next is
ref (step 3): the after-BORROW seam, a fresh extraction — and the
twin-merge preconditions should be checked on ref's projzero/projoffset
pairs FIRST, since that pattern is much cheaper than a seam.

Validation, all four suites: 0 errors; audit OK, 0 sorries, axioms
unchanged; 17/17 + 104/104; 82/0; osea 82/0/0. Proof dir 36,695.

## 2026-09-02 (thirty-fourth)

**Twin-merge preconditions checked on ref: all 8 candidate pairs FAIL.**
Every projzero/projoffset pair passes the binder test (4-line diff:
name + h_o) and shares 60-86% in-order — but the first structural fork
sits at 12-42% of the body, not at the tail. The cause is categorical:
in copy's projlocal family the destination offset only mattered at the
WRITE, so everything through `h_incrS1V` was byte-identical; in ref the
offset changes the EMITTED FRAGMENT (an extra dst Borrow), which
permeates the middle — different `_lowers` fragment names mid-body,
shifted `instrAt` indices, BRIDGE 1 appearing in §8b, different
mother-call states (`tgtPerms` vs `q1`, double register insert).
Fork-then-reconverge is the failing shape; a `by_cases` would duplicate
the reconverged middle.

**The after-borrow seam is confirmed instead, per family.** Within
`projoffset_fresh`, 3 of 4 leaves (plain/projsrc/selfsrc) share a
~210-line tail that is 95%+ identical, and the ONLY differences are
parametric — the borrowed pointer's offset and length
(`Val.Ptr bS.addr (0+0) (blockSize τ)` vs
`... (pathOffset f) (blockSize σb)`). Same in `projzero_fresh`
(188/200 normalized). Cross-family is only 95/200 — the seams are per
family, two of them. `derefsrc` stays out of both (0/220 — its source
mother ends in a Load with different registers).

Value ≈ 500-600 lines across the two seams, each a copy-spike-style
extraction (boundary-scan interface + parametric (boff, blen)).
No code changed in this check.

## 2026-09-02 (thirty-fifth)

**The derefdst family is on the shared seam — first cross-file use**
(`bb85c42`, −301). Three ref leaves end in a call to
`copy_chainwrite_after_read` (spine.lean): 311→217, 324→228, and the
two-mother leaf 384→273. Eight leaves across two files now share the
one destination half. Instantiation: τ := PtrL τ, vals := the borrowed
pointer as a one-word list, ambient renames at the extended ρt; the
two-mother leaf passes sR at the post-source-mother state and composes
h_runR from the source mother's run plus the Borrow step.

**BRIDGE 2 dissolved into the interface**: ref's `writeThroughPtr_sim`
call and the seam's manual write path meet at `h_valsRel` — the
`ListRel (MemValSim ..)` evidence ref built inline moves verbatim into
the argument list.

**Elaboration trap, cost two red builds:** passing `rfl` for
`h_prmR : csR.placeRegMap = csPrefix.placeRegMap` while `csR` is a
metavariable lets unification solve csR := csPrefix, and every
downstream argument then mistypes bizarrely. PIN the implicits
(csR/sR/vreg/vals/mvals) before any rfl-shaped argument.

**Adjacent candidates checked:** `ref_deref_local` is OUT — no
destination mother at all (the store goes through the dst's own binding
entry; different shape). `ref_projzero_derefdst_chainsrc` is VIABLE —
its MOTHER 2 goes through the zero-offset package on the deref base, so
the seam applies with dbase := the base and the projection absorbed by
the proj-zero equations (~130 lines). Its projoffset sibling is NOT
(write through a dst Borrow + Die — BRIDGE 1, the different seam).

Validation, all four suites: 0 errors; audit OK, 0 sorries, axioms
unchanged; 17/17 + 104/104; 82/0; osea 82/0/0. Proof dir 36,391.

## 2026-09-02 (thirty-sixth)

**Rev. 3 (source packages) approved; A1a landed as two lemmas rather
than a package** (`9f42d02`, `715ed5b`; −271). Reading the residual
source halves before extracting showed they were only ~40% source: the
other ~120 lines per leaf were three `StateIncr` code-inclusion proofs
(after the source lowering / after the Load with SYMBOLIC cleanup /
after the destination lowering), each by unfolding the whole statement.
They mention the destination, so one lemma per destination constructor
— `copy_derefdst_incrs`, `copy_projzerodst_incrs` — but the source only
ever appears as the opaque `run (placeToRegChecked Shared src) cs`, so
each is source-generic, with the post-source state abstract (`csS`,
`h_srun`): variables pass `rfl`, zero-offset projections pass the
`proj_zero` equations, and the NONZERO-offset pair passes the
`proj_offset_{value,run}` equations from `29513f6` plus the leaf's own
`csnorm at h ⊢` as the spelling bridge. Five leaves, all first-build.

**The re-measure the plan demanded.** Residual composition of the
one-Load seam users is now hdr 25 / §1 40 / §2 25 / §3 5 / §4 13 /
§5 21 / §6 24 / tail 48. The source-only remainder (mother + read +
`h_lbsR`) is ~62 lines per leaf; the offset pair's §6–§7 (BRIDGE 1S +
three instruction steps) is ~120. So A1b's read packages are worth
~−50 (chainsrc, 3 users) and ~−100 (projsrc_offset, 2 users) on the
seam users alone — under the plan's ~150 bar — and pay only through the
fresh-family multiplier, whose source sections start at a
`setPlaceInfo` post-alloc state and carry a different (single)
code-inclusion fact. That multiplier is real but each package is a
spike. Checkpoint, not a stop: the next increment should be sized by
attempting `copy_chainsrc_read` against fresh_chainsrc's §7–§9 first,
since without that reuse the package does not clear the bar.

Validation, all four suites, both commits: 0 errors; audit OK,
0 sorries, axioms unchanged; 17/17 + 104/104; 82/0; osea 82/0/0.
Proof dir 36,035.

## 2026-09-02 (thirty-seventh)

**Rev. 3 executed end to end on copy, and the answer changed shape
twice.** Seven commits, copy.lean 10,393 → 8,811, proof dir 36,060 →
34,850 (−1,210), zero sorries, axioms untouched, four suites green at
every one.

**A1b/A4 — the source packages, and what they are actually worth.**
`copy_chainsrc_read` (the chain read) and `copy_projsrc_offset_read`
(the Borrow/Load/Die read, BRIDGE 1S inside) both take an ABSTRACT
start state `(sM, sA, csA)` and hand back the seam's input bundle. On
the BOUND-destination leaves they pay about what the previous session
predicted (chaindst_projsrc_offset 382→138, projdst_zero_projsrc_offset
370→148). The multiplier the design was for is real: the fresh leaves
call them at their post-`Alloc` states and shed 165–263 each.

**A3 answered itself: zero-offset projections are not a source shape.**
`copy_chaindst_projsrc_zero` (209→143) is `copy_chainsrc_read` composed
with `LoweringSimAny.projZero`, plus `resolvePlaceAcc_proj_base_ok` on
the mirlite side and one `rw [h_pr0] at h_runR h_prmR h_regmonoR
h_lbsR h_spc h_pcR h_vbelow` to move the returned bundle from the
projected tower onto the base's. Same three lines convert
`copy_fresh_projchain_zero`. So copy needs TWO source packages, not
three.

**The real find: the fresh family is three shared pieces, not one.**
Once the source halves were packaged, the leaves' remaining text was
visibly the same at both ends. Two more shared lemmas fell out, and
they are bigger than the packages:

  - `copy_freshroot_write_after_read` (spine, 249) — the mirror of
    `copy_chainwrite_after_read` for a destination the statement
    ALLOCATES. Abstract post-source state, abstract renames
    (`ρa'`/`ρt'` with their `Incr` facts, not the literal
    `extendBlock`/`extend`), destination resolution as an abstract `rd`
    plus `rd.addr = s_mir.mem.addrStart` / `rd.tag =
    s_mir.perms.NextTag` (both `rfl` at every call). Owns the write
    transport, the `RStore`, the memory extension and all six
    `CompilerInv` bullets. Three leaves, −494.
  - `copy_freshroot_prologue` (spine, 164) — everything BEFORE the
    rvalue. Its input is `allocateBase MSB s_mir loc = ok s1`, NOT
    `preparePlaceAssign`: that is what makes it serve both a leaf
    assigning to `loc` and one assigning to `loc.f`, since both reduce
    to the same `allocateBase` on the root local. Five leaves, −557.

A fresh leaf is now prologue → source package → write seam, ~150 lines
of glue where it was ~500.

**Honest non-win, kept anyway:** `copy_projlocal_fresh`'s zero branch
onto the chainsrc package is a WASH (88 in, 88 out) — a fresh leaf must
spell its post-`Alloc` state and compiler state as package arguments,
where a bound leaf passes `s_mir s_osea csPrefix` and pays nothing. It
was worth landing only because it made that leaf's tail match the other
three, which is what let the write seam and the prologue apply.

**Two spelling traps, each one red build.** (1) A package output stated
about a PROJECTED evidence (`{result := sOut0.result, evidence :=
.projZero …}.result.cleanup`) has to be restated at the base by defeq
before `simp only [h_sclean]` will fire. (2) `LocalBindingSim`/
`PlaceInputsMapped` facts proven at a projection and used at its base
must go through two `have`s (`h_mappedP` then `h_mappedB`); a
`show … from` forces the resolution hypothesis to the base and fails.

**Process note, cost a full rebuild:** a splice script that computes
`s.index(marker)` on the WHOLE FILE rather than on the theorem's own
slice deleted 2,800 lines between an early leaf and the intended one.
The build caught it instantly and `git checkout` plus a re-splice from
the scratchpad copy restored it, but the rule is now: every in-place
edit script slices the target theorem FIRST and indexes only inside it.

**Where copy stands.** Remaining mass: the two `projlocal_fresh` leaves
(784, 873 — projected destinations on a fresh root, whose write is a
`Borrow`/`RStore`/`Die` sandwich, i.e. a second fresh-write seam), and
`copy_projdst_offset_projsrc_offset` (814, its own destination
projection). ref.lean is untouched by rev. 3 and is now the bulk:
12,998 lines, 31 leaves, TWELVE of them fresh (~4,800 lines).

**For ref, the pieces port with one generalisation each.** The write
seam is rvalue-agnostic already (it takes `vals`/`mvals` abstractly),
but ref's fresh leaves extend `ρa` at a single address
(`ρa.extend a a`) where copy extends a block (`ρa.extendBlock a n`),
and extend `ρt` TWICE (root tag, then the borrow's). So the prologue
should take its `ρa'` facts as INPUTS (incr, identity, base, dom)
rather than producing the literal `extendBlock` — four one-line
arguments at copy's call sites — and ref's leaves transport the
prologue's singly-extended `ρt` facts once themselves.

**Same session, second half — the trio ported to ref.** Four commits
more (`aee6137`, `0b6abfc`, `89df0e2`, `5423c0e`, `93b1017`).
ref.lean 12,998 → 12,528; proof dir 34,850 → 34,419.

**The fresh skeleton is rvalue-agnostic, and that is now demonstrated,
not conjectured.** All four `ref_fresh_*` leaves call
`copy_freshroot_prologue` and `copy_freshroot_write_after_read` — the
lemmas written for copy, unchanged except for step 1 below.

    ref_fresh_dst          314 -> 216
    ref_fresh_projsrc      339 -> 240
    ref_fresh_derefsrc     407 -> 271
    ref_fresh_derefprojsrc 413 -> 277

**Step 1, the one generalisation:** the prologue produced
`ρa.extendBlock a (blockSize τ)` and its four facts; ref's fresh leaves
extend the address rename at a SINGLE address (`ρa.extend a a`) because
the root holds a pointer. The four facts became hypotheses over an
abstract `ρa'` (+38 lines at copy's five call sites, −7 in spine).
Interesting: two of ref's four fresh leaves (`derefsrc`,
`derefprojsrc`) already used `extendBlock` — the two conventions were
living side by side in the same file.

**What a ref leaf pays that a copy leaf does not.** (1) The prologue
keeps `s1` ABSTRACT; ref's leaves used to `subst` it, so every
`Env.lookup s1.env` site now goes through `h_env1`, `csAt`/`get?`
through `h_pc1`, and the `AllocLockstep` bullet through `h_memstart1`
instead of `rw [← h_s1]`. (2) The tag rename is extended TWICE (root
tag, then the borrow's), so the seam's `ρt'` is instantiated at the
composite and the prologue's singly-extended `LocalBindingSim` is
transported by `rename_mono` → `insert_fresh_reg` →
`placeRegMap_congr`. For a leaf whose source went through the MOTHER,
that last congruence needs the mother's `h_dprm`, not an `emit` peel —
it crosses the whole source lowering.

**Pinning is not optional here.** Every seam call in ref pins
`csR`, `sR`, `vreg`, `vals`, `mvals` explicitly. Without the pin,
unification fixes `csR` from the `LocalBindingSim` argument (whose
compiler state is the post-`Alloc` one, not the post-source one) and
every later argument mistypes.

**Next, and it is the biggest single item left:** ten leaves write
through a destination PROJECTION on a fresh root — ref's four
`ref_projzero_fresh_*` and four `ref_projoffset_fresh_*` (3,285 lines)
plus copy's two `projlocal_fresh` (1,657). The ZERO-offset half of
those is within reach of the existing seam if it is generalised to two
types (local `σ`, value `τ`, write at `pathOffset path` with
`pathOffset path + blockSize τ ≤ blockSize σ`); the nonzero-offset half
needs the `Borrow`/`RStore`/`Die` sandwich and is a second seam.

**Same session, third stretch — the two-type root.** Three commits
more (`0522f61`, `a31da5c`, `67563d3`). Proof dir 34,419 → 33,896.

**One inequality unlocked ten leaves.** `copy_freshroot_write_after_read`
had silently assumed the allocated root and the stored value share a
type. Splitting them (root `σ`, value `τ`) and replacing the
`writeThroughPtr` bound's `Nat.le_refl` with
`h_fit : blockSize τ ≤ blockSize σ` is the whole change — and every
ZERO-offset projected destination on a fresh root then IS the plain
fresh case, because at zero offset the store goes through the ROOT
register, not through a projection borrow. `h_fit` is
`PathTo.offset_add_size_le g` every time.

    ref_projzero_fresh          335 -> 239
    ref_projzero_fresh_projsrc  345 -> 244
    ref_projzero_fresh_derefsrc 421 -> 289
    ref_projzero_fresh_selfsrc  325 -> 228
    copy_projlocal_fresh        784 -> 691   (its zero branch)

`selfsrc` is the case worth remembering: the source borrows out of the
root the statement just allocated, so there is no pre-existing source
local and the `ListRel` evidence is built from the prologue's own
`h_ra_base`/`h_ra_dom`. The seam takes the evidence and never asks
where it came from — the same property that let it take ref's borrow
pointers and copy's read words.

**Two type variables need pinning.** With one type, `vals` determined
it; with two, ref's `RStore obseq.TyVal.PTy` unified against the ROOT
type and every later argument mistyped. All ref call sites now pass
`(τ := obseq.LayoutTy.PtrL τ)` explicitly.

**Where it stands.** Eight of ref's twelve fresh leaves and one of
copy's two `projlocal_fresh` branches are on prologue + package + seam.
The remaining six (ref's four `ref_projoffset_fresh_*`, 1,936 lines,
and the two `projlocal_fresh` NONZERO branches) write through a
destination `Borrow`/`RStore`/`Die` sandwich. That is the second
fresh-write seam and the next item; it is worth roughly 700 lines, and
its interface is the current seam's plus a destination offset and the
two extra instructions.

**Same session, fourth stretch — the second fresh-write seam.** Four
commits (`2880ae5`, `ae3aae3`, `48cd646`, `2a9bf49`). Proof dir
33,896 → 32,788; ref 12,106 → 11,227; copy 8,754 → 8,188.

`copy_freshproj_write_after_read` (spine, 307) is the write half when
the destination is a FIELD of the fresh root at a nonzero offset: the
compiler mints an interior `Borrow(Mut)`, stores through it, and
retires it with a `Die`, and BRIDGE 1 (`sb_ref_use_die_cancels`)
collapses that ref/use/die triple to the parent's single write. Six
users, and the last leaf of the fresh family with it:

    ref_projoffset_fresh          477 -> 248
    ref_projoffset_fresh_projsrc  488 -> 255
    ref_projoffset_fresh_selfsrc  468 -> 240
    ref_projoffset_fresh_derefsrc 503 -> 314
    copy_projlocal_fresh          691 -> 478  (its offset branch)
    copy_projlocal_fresh_projsrc  882 -> 529  (both branches)

**The interface lesson, and it is general.** The first seam takes the
statement's compiled tower (`h_stmtRun`) as a hypothesis. That works
only while the caller's spelling of the tower matches the seam's. It
stopped working here: a leaf's `h_stmtRun` comes from its compile lemma
(elaborated with `have __src := …`) while the seam's pinned `csR` is a
`{X with}` update (elaborated with `let __src := …`), and `csnorm`
flattens one side one level further than the other. The fix was to stop
passing the tower at all: the seam takes the THREE code facts (which
every leaf already derives from its fragment) plus the two summary
facts the rebuild actually needs — the statement's `nextLabel` and its
`placeRegMap`, each one `rw [h_stmtRun]; simp` at the call site. That
interface is spelling-proof, and the next seam should be written that
way from the start.

**And a second, smaller one:** a nested record update does not
elaborate inside a `have` TYPE (the structure's model argument stays a
metavariable), so the post-borrow state is NAMED
(`obtain ⟨sB, hsB⟩ : ∃ sB : oseair.State MSB, sB = …`) and every fact
about it is stated on `sB.reg`/`sB.perms`/`sB.mem` with `hsB` as the
bridge. In argument position the same update elaborates fine — it is
only the unknown-expected-type position that breaks.

**The fresh family is finished.** Every fresh leaf in copy and ref —
fourteen of them, plus the two two-branch `projlocal_fresh` leaves —
is now prologue → source package → write seam. What remains in ref is
the BOUND-destination half (nineteen leaves, ~7,600 lines) whose source
axis has no packages yet, and in copy the bound leaves that already sit
on the chain-write seam.

**Same session, fifth stretch — `ref_local_borrow`, and a measurement
that says stop.** One commit (`6726451`). ref 11,227 → 11,108.

The package is the borrow twin of `copy_chainsrc_read`: transported
retag, executed `Borrow`, post-`Borrow` `LocalBindingSim`, pc equation,
`ListRel` evidence — the bundle both write seams and the chain-write
seam take. Its OFFSET parameter makes it serve two source shapes at
once (`off = 0` a local, `off = pathOffset f` a projection of one), and
the borrowed pointer keeps the ROOT's size field either way.

    ref_local_local      160 -> 148
    ref_local_projzero   178 -> 169
    ref_local_projoffset 305 -> 293
    ref_derefdst_local   217 -> 182
    ref_projzero_projsrc 187 -> 176
    ref_derefdst_projsrc 228 -> 188
    ref_local_borrow (new)       98

**−119 for a 98-line package is net −16, and the rest of the family is
~12 a leaf.** The whole local/projsrc source axis in ref lands around
−60 — well under the plan's ~150 bar. The reason is structural and
worth writing down: **a borrow source is ONE instruction.** copy's
chain sources carry a mother lemma (a whole recursive lowering) and
that is what made `copy_chainsrc_read` pay; ref's `&x` carries a
`sb_ref` transport and a single `Borrow` step. There is simply less to
share. The one leaf that paid properly (`derefdst_local`, −35) did so
because of the post-`Borrow` SCAFFOLDING it handed over — the
`LocalBindingSim` at the emit tower the destination mother needs — not
because of the borrow itself.

Two interface points, both general:

  - a package that consumes a mirlite step whose minted tag the CALLER
    still names must RETURN the equation (`freshTag = sM.perms.NextTag`)
    rather than assume it; call sites destructure it as `rfl`.
  - `blockSize τ` is not injective for unification, so a layout type
    that appears only under `blockSize` cannot be inferred — make it an
    explicit argument.

**Where the mass actually is.** Eight bound leaves write through a
projection of a BOUND root (`ref_local_projzero/projoffset`,
`ref_projzero/projoffset_projsrc`, `ref_projzero/projoffset_derefsrc`,
`ref_proj_src_projdst`, `ref_proj_dst`): the destination `Borrow(Mut)` /
`RStore` / `Die` sandwich again, but off a bound root register instead
of a freshly allocated one. That is `copy_freshproj_write_after_read`
with the allocation hypotheses replaced by the destination binding —
worth ~100 a leaf, and it is the next thing to build.

**Same session, sixth stretch — the bound-root projected write seam.**
Two commits (`2699b65`, `b312bea`). ref 11,108 → 10,697.

`copy_boundproj_write_after_read` (spine, 219) is the projected write
when the destination's root is already bound: the same `Borrow(Mut)` /
`RStore` / `Die` sandwich and the same BRIDGE 1 collapse as the fresh
version, but no rename growth and no allocation lockstep, so its
conclusion is the plain `CompilerInv` the chain-write seam returns.
Written with the spelling-proof interface (three code facts plus
`nextLabel`/`placeRegMap`/`nextReg` summaries) from the start.

    ref_local_projoffset    293 -> 148
    ref_projoffset_projsrc  322 -> 153
    ref_projoffset_derefsrc 320 -> 223

−411 for a 219-line seam: **net −192 from three leaves**, against the
borrow package's −16 from six. That is the shape of the whole exercise
in one comparison: in ref the DESTINATION side carries the mass, in
copy it was the source side, and the deciding factor both times is
whether the shared piece contains a MOTHER LEMMA or just an
instruction.

**Then generalised twice, cheaply.** The seam asked for the
destination's `Binding` and `Local` and used neither: what it needs is
the resolved root (base, tag, size) plus the register holding it and
THAT REGISTER'S OWN OFFSET into the allocation. Restating it over
`dbase`/`dtag`/`dsize`/`boff` costs the three call sites a `0` and two
`by simp`s and admits chain-resolved destinations, whose register
points into the middle of its block.

**Where it stopped, and why.** `copy_projdst_offset_projsrc_offset`
(814) is exactly that chain-resolved shape and was the intended fourth
user; after a dozen build attempts it was reverted. Its towers are
spelled with `{X with}` throughout, so the mother's `h_dprm`/`h_dlbs`
carry the `let __src` form while every pin and `simp only [emit]`
produces the flat one, and the mismatch propagates into unresolved
metavariables — the seam's `h_lbsR` argument arrives with `?m` for the
layout type and the arithmetic side goals then fail with nothing to
work from. The fix is not more tactic-fiddling at the call site: it is
to normalise that leaf's towers (a `csnorm` pass over its `have`
statements) FIRST, and then the seam call is the same twenty lines as
the three that landed. Same for `ref_projoffset_derefdst_chainsrc`
(471), the other chain-resolved user.

**Same session, seventh stretch — the two chain-resolved users, and the
diagnosis that unblocked them.** Two commits (`9657d59`, and the ref
one). copy 8,188 → 7,984; ref 10,697 → 10,573; proof dir 32,253.

    copy_projdst_offset_projsrc_offset  814 -> 610
    ref_projoffset_derefdst_chainsrc    471 -> 347

**It was never the tower spellings.** The previous stretch blamed
`{X with}` vs flat records; a dozen failed builds later the real causes
were three, and all three are general:

  1. **`omega` cannot do this codebase's ADDRESS arithmetic.** Addresses
     are `Word` (coerced), so omega silently DROPS every hypothesis and
     goal atom mentioning `rd.addr`/`rd.allocBase`/`rd.allocSize` — its
     "possible counterexample" then lists only register and label
     atoms, which is exactly why the failures looked inexplicable. Use
     `grind` for addresses; `omega` is right for registers and labels,
     which are plain `Nat`.
  2. **Arithmetic side conditions must be hoisted out of the seam
     call.** Inside the application their goals still carry unassigned
     implicits, so a tactic sees metavariables where the leaf's facts
     should be.
  3. **Facts about compiler states are LIFTED, not re-proven.** A
     mother returns its `LocalBindingSim` and `RegisterBelow` at its
     INPUT state; the seam wants them at the output.
     `LocalBindingSim.placeRegMap_congr h_dprm h_dlbs`,
     `RegisterBelow.mono h_dregmono h_regbelow` and
     `h_dprm.trans h_prmCS2` say so in one line each, where a tactic
     proof cannot see past the tower.

Rule of thumb from this: when a seam call fails, do not reach for
`csnorm` first. Ask which of the three it is — wrong tactic for the
arithmetic domain, a goal elaborated too early, or a fact that needs
lifting rather than proving.

**Same session, eighth stretch — the projzero variants.** Two commits
(`421fba5`, and local_local). ref 10,573 → 10,393; proof dir 32,198.

At ZERO offset a projected destination needs no interior borrow: the
store goes straight through the root's register. So the third write
seam, `copy_boundplain_write_after_read` (124), is the projected one
minus the `Borrow(Mut)`, the `Die` and BRIDGE 1 — one code fact instead
of three, same resolved-root interface.

    ref_local_projzero    169 -> 130
    ref_projzero_projsrc  176 -> 133
    ref_projzero_derefsrc 276 -> 218
    ref_local_local       148 -> 108

The fourth projzero leaf, `ref_projzero_derefdst_chainsrc`, needed
nothing: its destination is a deref CHAIN whose projection collapses at
zero offset, and it has been on `copy_chainwrite_after_read` since the
thirty-sixth session. That is the tidy end of the classification:

    destination            write seam
    ---------------------  ---------------------------------
    chain, any offset      copy_chainwrite_after_read
    bound root, zero       copy_boundplain_write_after_read
    bound root, nonzero    copy_boundproj_write_after_read
    fresh root, zero       copy_freshroot_write_after_read
    fresh root, nonzero    copy_freshproj_write_after_read

Five seams, and every leaf in copy and ref whose statement writes to
memory now goes through exactly one of them. Each conversion after the
recipe settled took one build attempt.

**Same session, ninth stretch — the last bound leaves in ref.** One
commit (`e116ea6`). ref 10,393 → 10,244; proof dir 32,049.

    ref_proj_local          177 -> 146
    ref_deref_local         263 -> 204
    ref_derefprojsrc_local  270 -> 211

All three wrote through a BOUND local's register at offset zero, so all
three took `copy_boundplain_write_after_read`. **`grep
writeThroughPtr_sim` now matches no `*_simulation` in copy.lean or
ref.lean**: every statement in those two files that writes memory goes
through one of the five write seams, and BRIDGE 2 is called from
spine.lean only.

**const_write is NOT reachable by these seams as they stand, and the
reason is instructive.** Its eight `const_store_*` leaves (1,891 lines)
store with `CStore` — the value is an IMMEDIATE operand of the
instruction, not a register — so they end in `runN_CStore_step`, not
`runN_RStore_step`, while everything else (the resolution, BRIDGE 2,
the whole rebuild) is identical.

I tried abstracting the seam's store step into a hypothesis
(`h_store : ∀ s', writeThroughPtr … = Ok s' → runN 1 sR compProg = Ok s'`,
plus the message as a parameter) so that both instructions could
instantiate it. The seam itself took the change in one build. The
REVERT was about the call sites: each of the seven existing users then
has to hand the step lemma its own `h_ptr` (the destination register's
lookup), which the seam currently derives internally from `h_entryD` —
so the change costs a hoisted `have` at every site to buy a hypothesis
none of them needs. Not worth churning seven green proofs for.

The right shape for const_write, when it is worth doing: three CStore
siblings (plain / projected / fresh) sharing the resolved-root
interface, OR the `h_store` abstraction done ONCE while a call site is
already being rewritten for another reason. Estimated −500 to −700
across the eight leaves.

**Tenth stretch — step 6, and where it bottoms out.** Commit
`8d4c842`. copy 7,984 → 7,966; dispatch 215 → 155.

The plan's last item was "rewrite the dispatchers to case on semantic
outcomes rather than place constructors". I measured the dispatchers
before redesigning them, and the repetition was NOT in the case
structure — it was in the flatten bridges each branch restated
verbatim:

    copy_local_srcflat_bridge     (local dst, proj src)   2 users
    copy_derefdst_flat_bridge     (deref dst, any src)    3 users

Each is the same pair — the compiled RUN agrees at the original and
normalized spellings, and a compiled VALUE at the normal form yields
one at the original. Stating them once turned ~20 lines per branch into
one `obtain`. `copy_derefdst_flat_bridge` takes the source's normal
form as a parameter (`h_seq`), so the chain case passes `rfl` and the
two projection cases pass their own `h_seq` — one lemma, three
callers. The local-destination projection prelude also moved ABOVE the
env split; both env cases were flattening the same source.

**What's left in the dispatcher is irreducible at this design.** 155
lines / 13 branches ≈ 12 lines per branch, and a branch IS a leaf
invocation with its implicits pinned. The `exact ⟨ρa, ρt, …,
AddrRenameIncr.refl ρa, …⟩` tail repeats five times, but a helper to
absorb it costs about what it saves. Casing on semantic outcomes would
change WHICH LEAVES EXIST — a redesign of the leaf set, not a shrink of
the dispatcher. Under the plan's own stopping rule (under ~150 net with
no multiplier in sight, stop and re-measure) step 6 is finished.

**Session totals.** proof dir 36,060 → 32,031 (−11.2%); copy.lean
10,686 → 7,966 (−25%); ref.lean 12,998 → 10,244 (−21%). Zero sorries
and the same three axioms at every one of ~38 commits. The remaining
named opportunity is const_write's eight CStore leaves (1,891 lines,
est. −500 to −700), which needs the store step abstracted or three
CStore siblings — see the ninth stretch for why the abstraction was
reverted rather than forced.

**Eleventh stretch — const_write, and what it actually was.** Three
commits (`6cb9042`, `04cb33f`, `2ad64c6`). const_write 4,496 → 3,300
(−27%); proof dir 32,031 → 30,862.

I came in expecting to need CStore siblings of the five write seams.
That was the wrong model of the file. const_write's repetition is not
on the destination axis at all — it is the **rvalue axis**, `constInit`
vs `uninit`, duplicated from top to bottom.

**1. Sixteen dead wrappers (−765).** Each generic leaf
(`const_store_*_simulation`) is already parameterised over the rvalue,
and `ConstStoreFrags` bundles the nineteen fragment facts per rvalue.
The per-leaf instance wrappers — `const_write_*_simulation` and
`uninit_*_simulation`, two per leaf — predate that bundle. Every
reference to all sixteen was in a DOC COMMENT. The live dispatch
reaches each leaf through the frags.

**2. Thirteen twin fragment lemmas (−362 net).** `compileStmt_proj_zero_run`
and `compileStmt_proj_zero_uninit_run`, and twelve more pairs, differed
only in the rvalue and the values it stores. `ConstStoreFrags`' own doc
said these "CANNOT be shared between rvalues — for a variable `rhs`,
`compileRExprPreChecked rhs` does not reduce". True, and beside the
point: the lemmas never needed it to reduce, only to be a single
`CStore`. That is

    def PureCStore (rhs) (ty) (vs') : Prop :=
      ∀ cs, run (compileRExprPreChecked rhs) cs = cs ∧
        ∃ pre, value (compileRExprPreChecked rhs) cs = ok pre ∧
          (∀ r, pre.store r = [Instr.CStore ty vs' r]) ∧ pre.postCleanup = []

and both rvalues prove it by `rfl`. The proof edit is one move: where a
lemma unfolded `csCompile` (which drags in `compileRExprPreChecked`) it
now unfolds `compileStmtChecked` alone and rewrites with the witness.

**3. The bundle itself (−69).** With the twins gone the two frags
instances were the same 75 lines twice. `pureCStore_frags` builds all
nineteen fields from one witness, taking the rvalue's evidence from
`pre.ev` instead of naming a constructor; each instance is now one line.
A third constant rvalue would cost one `PureCStore` proof.

**The one real surprise.** Two frag fields were written as "destination
lowering, THEN `compileRExprToChecked`". That is defeq to the compiler's
actual order only because a constant rvalue's pre-phase is a `pure`.
With `rhs` opaque the true order shows: `ensurePlaceRoot`, then the rhs
PRE-phase, then the destination lowering — exactly the d34 ordering the
compiler's own comment describes. Generalising made the proof say what
the compiler does.

**Session totals.** proof dir 36,060 → 30,862 (−14.4%); copy 10,686 →
7,966; ref 12,998 → 10,244; const_write 4,497 → 3,300. ~42 commits,
zero sorries and the same three axioms throughout, four suites green at
every one.

**Twelfth stretch — the dead-code sweep, and why it found so little.**
Commit `7f66618`. −95 lines; proof dir 30,862 → 30,768.

Swept all 538 declarations in `src/obseq3/proof` (plus the non-proof
obseq3 sources). Thirteen had no qualified reference outside their own
definition. **Eleven of the thirteen were live.**

They are reached by generalized field notation, which no name-based
search can tell from an unrelated lemma with the same suffix:

    h.find?_some / h.find?_none    StackMapSim.*
    i.out.snoc / .setNextReg / .setPlaceInfo   EmittedAt.*, via the
                                    EmitTower instances
    h.loweringSim                  PtrChain.loweringSim
    .fragmentOf .fragmentAt .rebase .instrAt .mono
                                   CodeIncluded.*, FragmentAt.*

`.mono` alone has 137 occurrences across the tree, nearly all of them
`RegisterBelow.mono` or `AddrRenameIncr.mono`. A suffix count is
therefore worthless as evidence in either direction: it neither
confirms life nor confirms death. **The only sound test is deletion
plus a build**, so each candidate was cut and rebuilt, restoring the
ones that broke — six rounds.

Actually dead: `oseair_runN_trans'` (9), `dieCellContent_transport`
(85), and `tD61` (1) — a Place in ΓD61 that the d61 program never
assigns, unlike every other D-series test.

Left in place deliberately: `resolveWildcard`, `AccessPerms.isProtected`
(sb.lean) and `Mem.removeRange` (oseair.lean) are unreferenced one-line
wrappers that keep the model's vocabulary symmetric with mirlite's.
Removing them is a statement about what the semantics SAYS, not a
cleanup, so it is the human's call.

Not swept: `src/obseq/` (the v1 reference implementation) and
`src/obseq2/` (the port source). Unreferenced declarations there are
the point of those directories.

**Contrast with the const_write find.** That sweep removed 765 lines in
one go because those sixteen wrappers were referenced by FULLY
QUALIFIED name — in doc comments only. Qualified-name evidence is
reliable; suffix evidence is not. Worth remembering before the next
sweep: the cheap grep is only a candidate generator.

**Thirteenth stretch — the three wrappers, and a bug in my own sweep.**
Commit `4a8b1e2`-ish (`sb: drop the two unused AccessPerms wrappers`).

Asked to remove the three wrappers I had flagged but left. Two went:
`resolveWildcard` and `AccessPerms.isProtected`, each of which wrapped a
live function (`resolveWildcardIn`, `isProtectedIn`) by supplying one
field of an `AccessPerms`. Nothing called either; every call site uses
the wrapped form directly.

The third, `Mem.removeRange`, is **live** — `oseair.lean:358` calls it
as `state.mem.removeRange`. My sweep had reported `fld=0` for it. The
counter's guard was

    (?<![A-Za-z0-9_])\.removeRange(?![A-Za-z0-9_])

which requires the `.` NOT be preceded by an identifier character — and
that excludes exactly the common shape `x.y.method`. So the guard was
inverted for chained projections: it could only ever see field notation
on a bare variable.

Two lessons, one already recorded and one new:
* the suffix count proves nothing either way (twelfth stretch), and
* **my "clean, fld=0" classification was not even a correct suffix
  count.** The non-proof candidate list was therefore untrustworthy in
  BOTH directions. The proof-directory conclusions still stand, because
  candidates there were selected by qualified-reference count (which the
  bug does not touch) and every one was confirmed by deletion + build.

The build test remains the only evidence worth acting on.
