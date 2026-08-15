# Parked loose ends

## OSEA symbolic-execution tactic (planned twice, never built)
**Status:** parked 2026-07-01 (idea dates to v1 era)
**Context:** both `plans/osea_symbolic_exec.md` and the v2 plan
(src/obseq/obseq2.md: "add symbolic execution support for short OSEA
fragments early") call for automating `runN n s prog = Ok final`
goals: per-instruction step lemmas → `runN_step_succ` chaining →
an `osea_symbolic_exec` tactic. paper.md §6 argues the fragment-local
proof style makes exactly this automation plausible.
**Why parked:** never scheduled; the plan file predates v2 (it uses
`StartsAt`/`List.get?`, both dead in v2's code map — the locator story
is now `compileStmt_emitted_in_compProg` + `simp`).
**To resume:** v2 already has pieces: `runN_CStore_step`,
`step_Die_preserves_reg`, `runN_allDie_preserves`, `oseair_runN_add`.
Missing: step lemmas for the remaining instructions, the chaining
lemma, then the tactic. Payoff rises with copy/ref/proj work
(steps 5–6) — consider before, not after, those.
**Effort estimate:** ~1 day for lemma layer; tactic metaprogramming extra
**References:** plans/osea_symbolic_exec.md,
durable/where-design-knowledge-lives.md

## Step 4: regime-A already-mapped-local milestone — THE next step
**Status:** parked 2026-07-01
**Context:** close the n=1 slice of `const_write_resolved_simulation`
(dst = already-mapped local; fragment is just `[CStore NatTy [Dat v]
dstReg]`). Wire locator + `runN_CStore_step` + `writeThroughPtr_sim`;
discharge `h_le` (le_refl), `h_dom` and `PlaceRegReady` from
`LocalBindingSim`; ap/tag reconciliation is trivial for a local
(t' = ρt(resolved.tag) = resolved.tag under identity); reconstruct the
9-conjunct CompilerInv via `oseair_runN_add`.
**Why parked:** workflow only — user switched to another project. No
technical blocker; all prerequisites are proved. This is the confirmed
next step when obseq2 resumes.
**To resume:** start in const_write.lean:87 replacing the sorry for
the local case; validates the full reconstruction end-to-end with
minimal surface.
**Effort estimate:** ~half-day
**References:** durable/writethroughptr-sim-is-place-kind-agnostic.md

## Steps 5–6: proj/deref + fresh-local regimes, then copy/ref
**Status:** parked 2026-07-01
**Context:** step 5 = `placeToRegChecked_run_sim` (run place fragment:
mem unchanged, PlaceRegReady with fresh borrow tag, sims preserved) —
unlocks proj/deref const-write AND is the main shared machinery for
the copy.lean/ref.lean sorries. Step 6 = regime B
(`const_write_fresh_local_simulation`): allocator correspondence,
identity-extension of ρa/ρt, sim monotonicity (only
`MemValSim.rename_mono` exists; SourceMemSim/LocalBindingSim analogs
needed).
**Why parked:** sequenced after step 4.
**To resume:** journal snapshot has the full plan; die-success
(`sb_die` after `useMut`) is the known deferred obligation.
**Effort estimate:** step 5 ~1-2 days; step 6 ~1 day
**References:** journal/2026-07/2026-07-01-vscode-session-state-const-write.md

## obseq3 proof reconstruction / obseq2↔obseq3 reconciliation
**Status:** parked 2026-08-14
**Context:** `src/obseq3/` (per-cell SB stacks, writable raws with
insert-above-granting placement, TwoPhase, length-parameterized
PermissionModel) is executable-only — zero preservation lemmas. obseq2's
proofs still target the old single-address model, so the proved semantics
and the conformance-tested semantics have diverged. Per
durable/dont-port-v1-proofs-reconstruct-in-v2.md, reconstruct on the new
model rather than port. `SBValid`-style structural invariants
(addr-unique, tag-unique per stack) are the natural starting layer;
`insertAboveCell` needs its own preservation story (it splices mid-stack).
**Why parked:** conformance suite prioritized; proofs not needed for
verdict scoring.
**To resume:** state `sb_read/sb_write/sb_ref/sb_own` preservation of a
per-cell SBValid; then decide whether obseq2's compiler-correctness work
migrates to obseq3 or obseq3 stays a conformance-only fork.
**Effort estimate:** invariant layer ~1 day; migration decision separate
**References:** plans/sb_conformance_obseq3.md,
durable/v1-v2-sb-model-divergences-from-miri-sb.md

## Conformance Phase C: protectors first, statics cheapest
**Status:** partially resolved 2026-08-14 (same day) — protectors and
statics hoisting landed as sketched below; suite now 34 pass / 0 fail /
0 xfail, fail tests 27/75. Remaining after the eighth increment (slices/runtime-length retags,
fail 53/75, journal/2026-08/2026-08-14-slices-landed.md): the 22
unsupported fail tests all need dynamic control flow (SwitchInt
execution: zst_slice, buggy_split_at_mut, Option matches), std
containers (Vec/String/Rc: buggy_as_mut_slice, illegal_read5),
threads (retag_data_race_*), drop glue (drop_in_place_*), closures/
fn-ptr protectors (deallocate_against_protector*, newtype_*), unions
(illegal_read3), or MaybeUninit. The retag-rule frontier is done.
Originally parked 2026-08-14
**Context:** score stands at fail 23/75 + 2 xfail (protectors), pass 9
scenarios (commit 445cbf4). Protectors would convert both xfails plus
~10 unsupported tests and compose with the existing inline-seam retag
machinery: protector flag on seam-retagged items, cleared at the inline
return, "would pop protected" ⇒ UB in read/write. Statics hoisting (a
lowering pass: hoist static/static mut to pc-0-initialized locals)
unlocks ~4 tests (pointer_smuggling, mut_exclusive_violation1,
unescaped_static, static_memory_modification) with no interpreter
change. Then: enums/Option (~3), dealloc (~7), UnsafeCell (~6).
**Why parked:** core conformance claim reached; each extension grows
interpreter surface, which the user wants minimal.
**To resume:** protectors = Item gains `protected : Bool` + seam-retag
emits protected items + a pop-guard in sb.lean + an unprotect pseudo-op
at inline returns; statics = lowering.lean pass only.
**Effort estimate:** protectors ~1 day; statics ~2 h
**References:** conformance/README.md, plans/sb_conformance_obseq3.md,
journal/2026-08/2026-08-14-obseq3-conformance-landed.md

## SwitchInt execution (runtime control flow in obseq3)
**Status:** parked 2026-08-15
**Context:** The executed obseq3 program is a straight-line statement
list; all control flow is discharged at LOWERING time (goto followed,
calls inlined, asserts const-folded, loops rejected). SwitchInt is the
first construct with a runtime-chosen successor, so supporting it means
jumps in the executed IR for the first time: `Stmt.switch`/`Stmt.goto`
with a non-monotonic pc, the lowering emitting ALL blocks with a
block→pc layout instead of walking one path, runtime BinaryOp results
and Discriminant reads feeding the scrutinee, and panic arms lowered to
abort. The subtle cost: the static trackers (constVals for array
indices, fnPtrs for indirect calls, assert discharge) are sound only
because execution is single-path — with CFG joins they need
flow-sensitive invalidation or per-block scoping.
**Why parked:** the conformance claim is complete without it — no SB
rule needs it; it only re-reaches existing rules through more program
shapes. The remaining fail tests it would unlock (zst_slice,
buggy_split_at_mut, fnentry_invalidation, un-rewriting the
Option-match mains, un-eliding RefCell's borrow flags) are language
surface.
**To resume:** (1) add Stmt.goto/Stmt.switch + non-monotonic pc to
obseq3 (runN already runs on fuel, loops are safe); (2) restructure
lowerCrate to emit per-block statement runs with a block→pc map and
patch targets after layout — inlining still concatenates per-function
layouts; (3) demote constVals/fnPtrs to per-block scope (invalidate at
block entry) or make them a simple forward analysis; (4) support
runtime BinaryOp results (word semantics exist; drop the const-only
restriction) and the Discriminant rvalue (read payload slot 0);
(5) lower Assert dynamic arms and panic edges to an abort statement.
**Effort estimate:** ~1-2 days (the lowering restructure dominates)
**References:** journal/2026-08/2026-08-14-slices-landed.md (the
"retag-rule frontier is done" boundary), conformance/README.md
(remaining-exclusions list), durable/sb-conformance-claim.md
