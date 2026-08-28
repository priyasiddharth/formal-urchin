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
