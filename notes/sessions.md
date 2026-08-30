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

## 2026-08-29 (early)
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
- journal 2026-08-29-copy-p-offset-closed.md (incl. new potholes:
  grind spelling-atoms, mid-script assert loses earlier edits,
  of_cells op-pinning).
**Critical corrections:** lean_verify served a stale sorryAx report
right after rebuild — cross-checked with #print axioms.
**Status:** complete. Audit at 4; all suites green; axiom audit exact.
**Next-session pickup:** copy deref-src (spine composition over the
same pieces), or the non-local-dst BRIDGE-1 compositions.

## 2026-08-29 (cont.)
**Session:** (terminal, continued) — copy deref-src
**Theme:** the read-side event fix (copy-range dereferenceability) +
regime D→L closed; copy done on all spine-shaped sources.
**Key outputs:**
- mirlite .copy range check (t17-pinned, teeth via inverse edit; the
  overlap guard incidentally caught the self-copy-through-pointer
  shape first); three one-line if_neg repairs in the closed leaves.
- resolvePlace?_of_resolveAcc (spine.lean); copy_deref_local_simulation
  + fragment lemmas; dispatcher split on LoadSpine; d37 differential.
- journal 2026-08-29-copy-deref-closed.md; audit entry 3 narrowed.
**Critical corrections:** none new (inverse-edit teeth rule held).
**Status:** complete. Audit at 4; units 17/17 + 50/50; suite 82/123;
axiom audit exact.
**Next-session pickup:** non-local-dst BRIDGE-1 compositions (largest
remaining class, shared across all three dispatchers), or const_write
deref-deep (pending-cleanup spine generalization).

## 2026-08-29 (cont. 2)
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

## 2026-08-30
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

## 2026-08-30 (cont.)
**Session:** (terminal, continued) — rhs-first doAssign swap
**Theme:** SEMANTICS CHANGE (flagged): mirlite doAssign moved to
Rust's rhs-before-place order — source-side completion of d34;
prerequisite for ref's deref dsts (rhs retag vs dst-spine read don't
commute). Repair sweep ~28 errors, all mechanical (dst match reduces
late: h_envD, or hD1 in fresh-dst regime; copy guard moves post-read).
**Key outputs:** doAssign swap (doAssignCont unreferenced); repairs in
ref/copy/const_write; journal 2026-08-30-rhs-first-doassign.md; dev
log increment 50.
**Status:** complete; all green; corpus byte-identical 82/123 (0
fail); units 17/17 + 55/55; audit at 4.
**Next-session pickup:** ref's deref dsts (`*p := &src` bare leaf +
`(*p).f := &src`), dispatcher wiring, differential witness d43.

## 2026-08-30 (cont. 2)
**Session:** (terminal, continued) — ref deref dst + grind audit
**Theme:** `*P := &src` closed over any load spine (the regime the
rhs-first swap unblocked); loadSpine_lowering_sim gains a
register-frame conjunct (borrow temp crosses the spine); grind audit
of the delta since 09d5472 (10 sites collapsed, 1 rejection).
**Key outputs:** compileStmt_ref_derefdst_run/_value,
ref_derefdst_local_simulation, dispatcher deref-dst arm, residual
narrowed, d43 (56/56), journal 2026-08-30-ref-derefdst-closed.md.
**Status:** complete; all green; corpus 82/123 (0 fail); audit at 4.
**Next-session pickup:** projected deref dsts (`(*p).f := &x`) or
copy's non-local dst arms (transfer recipe ready).

## 2026-08-31
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
2026-08-30-ptrchain-mother-lemma.md.
**Status:** complete; all green; corpus 82/123 (0 fail); audit at 4
(unchanged — coverage widens at wiring).
**Next-session pickup:** the wiring increment — nonspine dispatchers
on PtrChain, depth-1 proj-top leaves generalized to chain bases, d44
witness (`*((*q).f) := v`), residual docstrings + compiler.lean audit.

## 2026-08-31 (cont.)
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

## 2026-08-31 (cont. 2)
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

## 2026-09-01
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

## 2026-09-01 (cont.)
**Session:** (terminal, continued) — deref-src collapse; three-for-three
**Theme:** ref deref-src re-founded on the mother lemma (no bind
equation needed — one inner-value case split proves the fragment; the
statement run lemma needs only ok-ness, killing the incr dance). New
mother conjunct: ρa allocBase identity (ZST-referent gap in h_drange).
d49 `q := &mut *(s.f)` (62/62).
**Status:** complete; all green; corpus 82/123 (0 fail); audit at 4.
**Next-session pickup:** proj-topped srcs/dsts over non-local bases,
proj-of-proj normalization, unbound roots (regime-B).

## 2026-09-01 (cont. 2)
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

## 2026-09-02
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

## 2026-09-03
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

## 2026-09-03 (later)
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

## 2026-09-03 (third)
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

## 2026-09-03 (fourth)
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

## 2026-09-03 (fifth)
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

## 2026-09-03 (sixth)
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
notes/2026-09-03-copy-nonlocal-dst-order.md.
**Status:** analysis only; no proof change; all green; audit at 2.
**Next-session pickup:** HUMAN DECISION needed (invariant vs compiler
change) for copy's last class; meanwhile ref's classes (proj-topped
dsts over non-local bases, non-local srcs under non-local dsts, unbound
roots) are independent and can proceed.

## 2026-09-03 (discussion)
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
journal/2026-09-03-zst-addresses-and-wildcard-provenance.md.
**Critical corrections:** none from the user, but one self-correction
recorded — durable/rho-maps-are-identity-on-domain.md is v2-scoped; in
obseq3 ρt is NOT identity and `PermSim` (listed there as a rejected
alternative) is the adopted design. Scope caveat appended in place
rather than superseding.
**Status:** complete.
**Next-session pickup:** unchanged — see the preceding entries.

## 2026-09-03 (seventh)
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

## 2026-09-03 (eighth)
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

## 2026-09-03 (ninth)
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

## 2026-09-03 (tenth)
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

## 2026-09-03 (eleventh)
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
see. Written up in journal/2026-09-03-projected-dst-recursion.md
and durable/flatten-one-place-at-a-time.md.
**Status:** complete; all green; 17/17 + 75/75; corpus 82/123 (0 fail);
audit exact at 2.
**Next-session pickup:** copy's residual is now (a) proj-topped
flattened SOURCES under a deref dst, (b) projected dsts over a LOCAL
base. Then ref.

## 2026-09-03 (twelfth)
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
