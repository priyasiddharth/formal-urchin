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
0 xfail, fail tests 27/75. [superseded 2026-08-15] The remaining-bucket details now live in ONE
place: the MASTER INVENTORY entry at the end of this file.
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

## `RStore`'s `TyVal` guard is unprovable (blocks the ref leaf)
**Status:** RESOLVED 2026-08-22 (same day) — user chose option (1).
**Resolution:** hand-written mutual structural `TyVal.beq`/`beqList` +
`LawfulBEq TyVal` in obseq/types.lean (commit `f9a9228`). `deriving
DecidableEq` was tried first and refuses nested inductives. The root cause
was the derived instance being a `partial def` ⇒ `opaque`. With
`LawfulBEq`, `runN_RStore_step` holds over a variable `ty`, so every
future `RStore`-shaped leaf inherits it. Suites unchanged.
**References:** journal/2026-08/2026-08-22-rstore-tyval-blocker.md,
2026-08-22-ref-ll-closed.md.


## ZST retag divergence (target `Borrow` bounds check vs mirlite `M.ref`)
**Status:** RESOLVED 2026-08-22, both gaps, same day.
**Resolution:** (1) loader keeps unit assignments as access-free `uninit`
inits (`a36f0a3`); (2) target `Rhs.Borrow` check is now the range form
`addr + len > base + size` (Miri's dereferenceable-for-`len`; admits
one-past-the-end for `len = 0`; same form as `writeThroughPtr`). Stricter
for multi-cell retags, and the differential did not move: matched 78 |
mismatch 0. Proof side: `runN_Assgn_Borrow_step` takes the range bound,
`ref_local_local_simulation` lost `h_nz`, `ref_zst_residual` deleted
(audit 6 → 5). Witness `local/zst_ref` PASSES.
**References:** journal/2026-08/2026-08-22-zst-both-gaps-closed.md.


## StorageLive-vs-first-assignment probe (`local/unassigned_local_addr`)
**Status:** parked 2026-08-22 as UNSUPPORTED (unions)
**Context:** the lowering drops `StorageLive`/`StorageDead` and allocates
locals at first assignment. HYP was that a local borrowed before any write
would expose this. rustc rejects `let x: u64; &raw const x` (E0381); the
only legal form is `MaybeUninit::uninit()`, a bodyless call on a union
type, and unions are outside the surface.
**Why parked:** the refusal is itself the answer for the supported
fragment — without unions, the borrow checker guarantees every local is
written before it is borrowed, so first-assignment allocation is sound
BY CONSTRUCTION. The witness is registered `unsupported: unions` so it
lights up if unions ever land.
**To resume:** only if unions land: shim `MaybeUninit::uninit` →
`.assign dst .uninit`, give `MaybeUninit<T>` the layout of `T`.
**Effort estimate:** n/a until unions.
**References:** conformance/local/unassigned_local_addr.rs.

## Cslib/Mathlib adoption (paper-facing repackaging + Forall₂ dedup)
**Status:** parked 2026-08-27
**Context:** leanprover/cslib (Foundations/Semantics: LTS + behavioral
equivalences; Relation utilities) could state `compile_correct` as a
standard simulation between two LTSs — comparable, citable vocabulary for
paper.md. It HARD-REQUIRES Mathlib; this repo is deliberately
dependency-free (`ListRel` is a local stand-in for `List.Forall₂` by
design). If Mathlib ever comes in anyway: ~200 lines of `ListRel`
transports collapse into `Forall₂` lemmas, and the `set`-is-Mathlib-only /
omega-helper potholes disappear. Note: lake-manifest.json STALELY declares
mathlib (no `require` in the lakefile, `.lake/packages` absent) — clean
that up whenever this is decided either way.
**Why parked:** mid-proof it is churn with zero leaf-closing payoff; the
effort lives in the specific diagram (CompilerInv, bridges, folds), which
no generic framework shrinks.
**To resume:** after the audit hits zero, when packaging for the paper:
(1) decide the Mathlib policy; (2) if yes, restate compile_correct over
cslib LTSs + swap ListRel for Forall₂; (3) either way, fix the stale
manifest.
**Effort estimate:** policy decision n/a; restatement ~1 day; Forall₂ swap
~half-day.
**References:** src/obseq3/proof/permsim_transport.lean (ListRel
docstring), paper.md.

## mirlite `.ref` lacks Miri's retag-dereferenceable check
**Status:** RESOLVED 2026-08-28 — the event fix landed (user-approved):
`.ref` errs on `addr + blockSize σ > allocBase + allocSize` (range form).
Reachable behaviour unchanged (suite/differential identical); the three
closed ref regimes repaired with one `if_neg` each (L→L/F→L by
`lt_irrefl`, P→L by the typing lemma). Gap example pinned as t16 (the
FORGED junk state, teeth-verified) + d30/d31 (reachable reborrow, ZST
twist). The deref-source regime is now unblocked; leaf still to prove.
**Original context (kept):** parked 2026-08-27 — BLOCKED the deref-source ref regime
**Context:** Miri requires a retag's whole range to be dereferenceable;
mirlite's `evalRExpr .ref` performs `sb_ref` with NO bounds check. For
`L := &kind *p` the target `Borrow` checks `offset + blockSize τ ≤ size`
against the LOADED pointer and nothing on the source side implies it
(`MemValSim` is untyped — no pointee-size fact is even statable there).
Same finding-shape as the 2026-08-21 deref-read gap: a check Miri has,
mirlite lacks, discovered by attempting the proof.
**Why parked:** model change — user's call.
**To resume:** add `resolved.addr + blockSize τ > resolved.allocBase +
resolved.allocSize → err` to mirlite's `.ref` (mirror of
`writeResolvedPlace`'s check; consider `.refSlice` too), re-run suite +
differential (expect unchanged: corpus pointers are all well-sized),
then close the deref-source regime — source success then implies the
target check via MemValSim's `o' = o ∧ s' = s`.
**Effort estimate:** ~1 h model+validation; ~half-day for the regime.
**References:** journal/2026-08/2026-08-27-ref-proj-closed.md,
proof/ref.lean (`ref_place_residual` docstring).

## MASTER INVENTORY: everything unimplemented or approximated (obseq3 conformance)
**Status:** living inventory, started 2026-08-15 — THE single place for
this; update here, not in scattered journal entries. Per-test blockers
live in conformance/manifest.json (`reason`/`note` fields); this is the
feature-level view.

### A. Language/std features not implemented (block the 19 unsupported fail tests + pass files)
1. **SwitchInt / runtime control flow** — parked with a resume plan
   (own entry below). Blocks: zst_slice, buggy_split_at_mut,
   fnentry_invalidation, the Option-match mains (currently rewritten),
   RefCell's real borrow-flag checks, Result/unwrap paths.
2. **Runtime integer arithmetic** (BinaryOp with non-const operands) —
   only const-foldable arithmetic exists (bounds checks). Collapses
   into #1 when unparked. Blocks split_at_mut's len math.
3. **Runtime array indexing / subslicing** — Index projections resolve
   only through tracked constants; range indexing (`&a[0..0]`) needs
   the std Index chain (#1).
4. **Std containers**: Vec/String/vec! (buggy_as_mut_slice,
   box-custom-alloc-aliasing), Rc (illegal_read5), NonNull
   (mut_exclusive_violation2).
5. **Threads + the data-race detector** (retag_data_race_* ×3) — a
   different checker's interaction with retags; out of scope for SB.
6. **Drop glue** — real Drop impls (drop_in_place_retag/protector);
   drops currently lower to no-op gotos, box frees via the dealloc shim.
7. **Closures / fn-ptr arguments** beyond statically-tracked reified
   fns (newtype_retagging, newtype_pair_retagging,
   deallocate_against_protector1/2, track_caller).
8. **Unions** (illegal_read3).
9. **Misc std/lang**: MaybeUninit, coroutines, C variadics, trait
   objects/dyn, Pin/UnsafePinned, custom allocators (pass files).
10. **Static initializers** — hoisted statics start undef; a test
    READING a static's initial value would need initializer inlining.
11. **Miri-internal tests**: stack-printing, unknown-bottom-gc,
    zst-field-retagging-terminates.

### B. SB-model approximations (implemented, but simplified — all noted where they apply)
1. **Wildcard determinization**: accesses resolve to the topmost
   exposed granting item vs miri's angelic/"unknown bottom" reading.
   Verdicts coincide on all covered tests.
2. **Box protector strength**: modeled with strong-style pop-blocking;
   miri's WEAK protector differs only in allowing dealloc during the
   call (unexercised). Plain Box-typed assignments (`let b2 = b`) are
   not retagged (miri's AddRetag would; unexercised).
3. **RefCell flag elision**: borrow/borrow_mut/deref/replace shims skip
   the borrow flag — valid only for conflict-free executions (all the
   corpus exercises); a test relying on a borrow-flag panic stays
   unsupported.
4. **Slice length convention**: a slice value is one cell; length =
   rest of its allocation (size − offset). No subslices.
5. **Enum layout**: discriminant word + prefix-merged payload — no
   niche optimization; incompatible variant layouts and nested refs in
   payloads are unsupported; payload seam retags are assignIf-guarded;
   the assignIf discriminant read is a raw memory inspection (no SB
   access; miri validity-reads it).
6. **Interior-mutability fallbacks**: Atomic* = one-word cell;
   UnsafeCell/Cell with uninferrable pointee falls back to one word.
7. **Layout/alignment**: Layout ≈ its size word; alignment is ignored
   everywhere (alignment UB is not SB); dealloc ignores the layout-size
   argument (uses the allocation's size).
8. **Value fidelity**: 1 cell per scalar (no bytes/padding — relative
   aliasing preserved, absolute sizes differ); negative constants clamp
   to 0 in value positions; `+=`-style rewrites store wrong values —
   sound because stored words re-enter the aliasing model only as
   addresses (fromExposed), discriminants (assignIf), or sizes
   (AllocLen), each of which is exact or rejected; pass tests do not
   check final memory contents.
9. **Retag placement under inlining**: fn-entry retags synthesize at
   call sites, so 8 tests are verdict-only with the line noted
   (aliasing_mut1-4; return_invalid tuple/option ×4 — miri flags the
   callee signature / `ret` line).
10. **No read-only memory**: static_memory_modification matches
    verdict+line via a frozen-write failure instead of miri's
    read-only-memory validity error.
11. **Messages**: error text approximates miri's wording (several match
    verbatim); the harness never matches text — verdict + line only.

### C. Prep rewrites
Recorded per-test in conformance/manifest.json `rewrites` and in each
prep header: asserts → plain reads, `+=` → read-then-write, post-UB
`match` → `let _`, method/intrinsic avoidance (ptr1.write → *ptr1,
transmute → cast chains where noted). Tier-3 arithmetic rewrites and
the match rewrites revert if SwitchInt is unparked.

**References:** conformance/README.md (claim + rule→witness table),
durable/sb-conformance-claim.md, manifest.json (per-test ground truth).

## OSEA-v3 remaining increments (compiler coverage beyond the proof core)
**Status:** parked 2026-08-15
**Context:** `src/obseq3/compile.lean` compiles the proof-core subset
(constInit/copy/ref/halt); `--osea` differential mode: matched 25 |
mismatch 0 | skipped 51 on the 76-passing suite. Each skipped construct
has a planned target instruction. Skip histogram with designs:
- ~~`pushProtectors`/`popProtectors`~~ **DONE 2026-08-15** (same-day
  follow-up): `Instr.PushProt`/`PopProt` calling `M.pushFrame`/
  `M.popFrame`; matched 25 → 53, mismatch still 0; remaining skips 23
  (alloc 6, uninit 6, exposeAddr 5, assignIf 3 — newly surfaced —
  ptrCast 2, ptrOffset 1).
- ~~`Stmt.alloc`/`dealloc`~~ **DONE 2026-08-15**: `Rhs.AllocN`/
  `Rhs.AllocDyn` (in-instruction SB read of a runtime length) +
  `Instr.Dealloc` on the loaded pointer; `removeRange` ported, allocs
  table still deferred (dealloc uses the ptr value's size field, as
  mirlite does — only fromExposed's resolveAddr needs the table).
  matched 56 → 63; remaining: exposeAddr 5 · assignIf 3 · ptrCast 3 ·
  ptrOffset 2.
- ~~`RExpr.uninit`~~ **DONE 2026-08-15**: CStore of `Val.Undef` cells,
  no new instruction needed (CStore already stores arbitrary Vals).
  matched 53 → 56; histogram now alloc 7 · exposeAddr 5 · assignIf 3 ·
  ptrCast 3 · ptrOffset 2.
- ~~`exposeAddr`/`fromExposed`~~ **DONE 2026-08-15** (as a pair):
  `Rhs.ExposeAddr` (place-tag read + stored-tag expose) /
  `Rhs.FromExposed` (read + resolveAddr → wildcardTag ptr); allocs
  table + resolveAddr ported to oseair.Mem. matched 63 → 68; remaining:
  assignIf 3 · ptrCast 3 · ptrOffset 2.
- ~~`ptrCast`~~ **DONE 2026-08-15**: no new instruction — mirlite's
  cast is a tag-preserving one-cell copy with an SB read = `Memcpy` at
  PTy.
- ~~`ptrOffset`~~ **DONE 2026-08-15**: `Rhs.PtrOffset (reg) (deltaCells)`
  with the delta pre-scaled to cells at compile time (delta · blockSize
  of the source pointee); reads the cell via the place's tag, shifts the
  stored pointer's offset, preserves its tag; negative-past-base errs.
  matched 71 → 75; the ONLY remaining skip is fnentry_invalidation2
  (refSlice).
- ~~`assignIf`~~ **DONE 2026-08-15**: `Instr.SkipIf` — event-free
  discriminant peek (mirlite uses raw mem.find?, no SB read), forward
  skip over the guarded block whose length comes from a dry-run
  compilation. matched 68 → 71. One latent asymmetry recorded
  (fresh-local-under-skipped-guard; unreachable from the corpus) in
  journal/2026-08/2026-08-15-osea-skipif.md.
- ~~`refSlice`~~ **DONE 2026-08-15**: `Rhs.BorrowRest (kind, prot, reg)`
  — reads the fat pointer cell, retags the runtime rest-of-allocation
  (size − offset), mask []. **SECTION CLOSED: matched 76 | mismatch 0 |
  skipped 0 — the compiler is total on obseq3's surface and the full
  passing suite runs differentially.**
**Why parked:** proof-core-first scope (user decision 2026-08-14); each
increment should land with its own differential numbers.
**To resume:** pick pushProtectors first (31 tests); add instruction to
`oseair.lean`, emission in `compileStmtChecked`, goldens + rerun `--osea`.
**Effort estimate:** pushProtectors ~1h; alloc/dealloc ~2h; others ~30min each.
**References:** journal/2026-08/2026-08-15-osea-v3-compiler-landed.md,
obseq2-comparison.md 2026-08-15 entry, MASTER INVENTORY above.

## obseq3 proof closure (8 audited sorries)
**Status:** parked 2026-08-15
**Context:** src/obseq3/proof/ skeleton landed; `CompilerInv_step` and
`compile_correct` fully proved for the CoreProg fragment modulo 8 sorries
enumerated in proof/compiler.lean's audit. The invariant is the corrected
`PermSim ρt` (obseq2's literal perms equality is false beyond local-only
places — see journal 2026-08-15-obseq3-proof-skeleton).
**Why parked:** skeleton-first scope (user decision); each sorry is an
independent increment.
**To resume:** keystone CLOSED 2026-08-15; bridges 2+3 and the §E glue
CLOSED 2026-08-18; regime A CLOSED 2026-08-18; regime D (all-deref
spines, every depth) CLOSED 2026-08-21; the BRIDGE 3 transport family is
COMPLETE as of 2026-08-22 (`sb_write`/`sb_read`/`sb_die`/`sb_ref`).
Audit now 5 named sorries.
`TagRenameBounded` WIRED into `CompilerInv` 2026-08-22 (eighth conjunct,
plus `sb_*_NextTag` framing and two counter conjuncts on
`loadSpine_lowering_sim`), so the `sb_ref` member is applicable at a leaf.
Ref regimes L→L and F→L both CLOSED
(2026-08-22/23); the ZST residual was closed by fixing the target check.
`CompilerInv_step_ref` now has ONE residual, `ref_place_residual`.
Audit 4 → 6 → 5 → 4. Regime C CLOSED 2026-08-27 for a
bound-local base (C0 bare `CStore`, C1 `Borrow; CStore; Die` — the first
and so far only consumer of BRIDGE 1). The nested-projection
divergence (found and FIXED 2026-08-27, `local/nested_proj_borrow` +
d26): the lowering now reassociates proj chains, so those two residuals
— briefly FALSE — are true again and NARROWER: only deref-rooted bases
remain (`(*p).1 := v` and kin), provable by `loadSpine_lowering_sim` ∘
the C1 pattern + a `resolvePlaceAcc`-offsets-add lemma for the
reassociation cases. DONE 2026-08-27 for the canonical
shapes: `(*p).f := v` over any spine + `*(s.f) := v` over a bound tuple
local, via BRIDGE 1S (`sb_ref_read_die_cancels`) and its supplier.
`const_write_deref_nonspine_simulation` is now a proved dispatcher. What
remains is `const_write_deref_deep_residual` (a proj segment BELOW a
deref, zero-offset pointer fields, fresh roots) — the pending-cleanup
generalization of `loadSpine_lowering_sim`. Ref P→L CLOSED 2026-08-27
(`dst := &kind s.f`, bounds by `PathTo.offset_add_size_le`);
`ref_place_residual` narrowed to deref sources (blocked on the mirlite
retag-check model gap, see its own parked entry), non-local destinations
(interleaved-keystone commutation — new pattern), and
proj-of-proj/fresh-root compositions. NEXT: `CompilerInv_step_copy`, or
the mirlite retag check if the user approves it.
Then `ref_place_residual` reuses that, and `CompilerInv_step_copy` last
(the only remaining sorry needing NEW machinery: a bidirectional memory
relation + the Memcpy execution lemma, plus — by the pattern established
in C1 — a `Memcpy`-succeeds-when lemma on the target side). Copy is independent: it still needs a
bidirectional memory relation + the Memcpy execution lemma. Regime B CLOSED 2026-08-22 (audit
5 → 4); it added the tenth `CompilerInv` conjunct
(`UnboundLocalsUnmapped`) and a third construction site, so any future
conjunct now costs three bullets rather than two — wire conjuncts BEFORE
closing the leaf that adds a site.
**Effort estimate:** CompilerInv `TagRenameBounded` wiring DONE
(~1 h actual); ref L→L DONE (~3 h incl. the `BEq` detour); ref fresh-dst
DONE (~2 h); proj/deref-nonspine ~half-day each; copy ~1-2
days (bidirectional memory relation is the real work); `sb_own` member DONE
(~1 h actual, as predicted); lockstep-allocation conjunct DONE (~1 h);
fresh-local DONE (~2 h actual).
**References:** proof/compiler.lean (audit), journal/2026-08/
2026-08-15-obseq3-proof-skeleton.md, journal/2026-08/
2026-08-22-sb-ref-transport.md, journal/2026-08/
2026-08-22-tagrenamebounded-wired.md, journal/2026-08/
2026-08-22-sb-own-member.md, journal/2026-08/
2026-08-22-alloclockstep-wired.md, journal/2026-08/
2026-08-22-regime-b-closed.md, journal/2026-08/
2026-08-23-ref-fresh-dst-closed.md, journal/2026-08/
2026-08-27-regime-c-closed.md, journal/2026-08/
2026-08-22-ref-ll-closed.md, obseq2 sorries superseded by this
decomposition (obseq2/proof stays frozen).


## Verify local conformance witnesses against real Miri
**Status:** parked 2026-08-21
**Context:** conformance/local/ holds project-authored Rust witnesses
(currently deref_read_disables_sibling.rs) with model-reasoned expected
verdicts; the Miri-derived corpus stays ground truth.
**Why parked:** running Miri needs a Miri build at the PIN commit; not
part of the current toolchain setup (tools/ has charon only).
**To resume:** build/install Miri at the PIN's miri_commit, `cargo miri
run` each local/*.rs, compare verdict+line, flip the manifest provenance
field to "miri-verified".
**Effort estimate:** ~1h once a Miri toolchain is available.
**References:** conformance/README.md (Local witnesses section),
journal/2026-08/2026-08-21-deref-read.md.

## separation-invariant (DEMOTED 2026-08-28 night — likely unnecessary)
Originally: `CompilerInv` lacks a separation conjunct, making the
interleaved-keystone shapes FALSE in overlap-junk states (d33). Both
consumers have since been dissolved WITHOUT it: the overlapping-
assignment guard + `Memcpy` nonoverlapping check supply per-statement
src/dst disjointness for every copy shape, and the lowering-order fix
removed the non-local-dst interleaving entirely (dst `Borrow;store;Die`
is contiguous — BRIDGE 1 shape). Keep parked only in case a future
regime needs cross-STATEMENT separation; nothing known does.

## lowering-order-bug (RESOLVED 2026-08-28 — the lowering-order fix)
d34 pinned a REACHABLE divergence (dst temporary minted before rhs
evaluation, killed by the rhs spine's legitimate read). FIXED the same
day: `compileRExprPreChecked` split + MIR order in the assign-place
arm; d34 flipped to `expectDiff .ok` with reversion teeth. The
interleaving obstacle is gone from the non-local-dst residuals; what
remains of those is the separation/overlap analysis.

## copy: proj-topped SOURCE at nonzero offset under a deref dst (CLOSED 2026-08-30)
`copy_chaindst_projsrc_offset_simulation` (d65) closes `*p := copy s.f`
off zero, so `copy_place_residual` names no deref destination at all —
that whole arm of the dispatcher is total. The resume recipe held up:
§1-§5 and §8-§11 from the d64 leaf, §6-§7 spliced from
`copy_projchain_offset_simulation`'s BRIDGE 1S phase. What the recipe
did NOT anticipate was that the work would be term-SHAPE work rather
than proof work — see journal/2026-08-30-projsrc-offset-bridge1s.md and
durable/transport-compiled-states-by-defeq.md.

## copy: PROJECTED destination over a LOCAL base (CLOSED 2026-08-30)
Both offsets and both root states. The BOUND root cost no new proof:
`copy_projdst_zero/offset_chainsrc_simulation` generalize from a
`.deref P` base to any canonical chain base, and a bound local IS one
(d66/d67). The UNBOUND root needed two real regime-B leaves,
`copy_projlocal_fresh_zero/offset_simulation` (d68/d69). The resume
recipe (mirror `const_write_proj_*`) would have worked but was more
work than necessary — see
journal/2026-08-30-projected-local-destinations.md.

## copy: PROJ-TOPPED source at NONZERO offset — BOTH LEAVES DONE, wiring left
**Status:** narrowed 2026-08-30 to the dispatcher only
**Done:** three compiled fragments
(`compileStmt_copy_projdst_{zero,offset}_projsrc_offset_run` and the
destination-offset-agnostic `..._projsrc_offset_value`) and BOTH leaves,
`copy_projdst_zero_projsrc_offset_simulation` and
`copy_projdst_offset_projsrc_offset_simulation`. The nonzero-destination
twin is the zero leaf's §1–§8 with the BRIDGE 1 endgame in place of the
bare `RStore`: `sb_ref_use_die_cancels` around the write, three code
facts (Borrow at `s_mid2.pc`, RStore at +1, Die at +2), and the final
`LocalBindingSim` framing the destination borrow register out with
`LocalBindingSim.insert_fresh_reg h_dlbs h_prb1 h_dregmono rfl`.
`csnorm` carried the three `StateIncr` towers with no traced spellings
at all; the potholes that remained were content, not spelling — the
`PtrRegisterEntry`-is-not-a-simp-target one (keep a `h_lookupD2` twin
and use it in `writeThroughPtr`'s `simp` AND in `runN_RStore_step`), and
`omega` needing BOTH sides normalized (`simp only [emit] at h1 h_eq'`,
or the two atoms differ).
**Left:** the DISPATCHER. `CompilerInv_step_copy`'s proj-dst arm still
sends every nonzero-offset source to the residual. Wiring needs a
recursive `copy_projdst_projsrc_offset_simulation` mirroring
`copy_projdst_simulation`: peel nested destination projections with the
associativity transfers, then `by_cases` on the DESTINATION offset and
call the matching leaf. A bound local base and a deref base both work;
an UNBOUND local root with a nonzero-offset projected source has no
leaf, so it stays residual and `copy_place_residual` does NOT close on
this increment alone.
**Effort estimate:** ~half a day for the dispatcher, plus witnesses
(`(*p).f := copy s.g` and `t.f := copy s.g`, g off zero, at both
destination offsets) and teeth (oversize the `Shared` projection
borrow — d70 takes the no-borrow branch, so it stays passing).
**References:** journal/2026-08-30-lowering-sim-package.md,
durable/csnorm-a-normal-form-for-compiler-states.md.
