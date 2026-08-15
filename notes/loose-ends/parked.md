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
- `exposeAddr`/`fromExposed` (5): `Instr.Expose (reg)` (M.expose + read),
  `Rhs.FromExposed` (needs `Mem.resolveAddr` port + wildcardTag ptr).
- `ptrCast` (2): tag-preserving one-cell copy — a Load without... no: a
  `Rhs.PtrCast (reg)` that re-types the register value, plus the M.read
  of the source cell to match mirlite's cast-as-read.
- `ptrOffset` (1): `Rhs.PtrAdd (reg) (delta)` — pure offset arithmetic
  on the register's Ptr, no permission event (mirlite does a read of the
  source cell — mirror that).
- `assignIf` (enums): `Instr.SkipIf (reg) (val) (n)` — the code-map
  design (Prog = Nat → Option Instr) was kept exactly for this.
- `refSlice`: Borrow with runtime len — `Rhs.BorrowRest` reading len
  from the pointee allocation size, as mirlite's refSlice does.
**Why parked:** proof-core-first scope (user decision 2026-08-14); each
increment should land with its own differential numbers.
**To resume:** pick pushProtectors first (31 tests); add instruction to
`oseair.lean`, emission in `compileStmtChecked`, goldens + rerun `--osea`.
**Effort estimate:** pushProtectors ~1h; alloc/dealloc ~2h; others ~30min each.
**References:** journal/2026-08/2026-08-15-osea-v3-compiler-landed.md,
obseq2-comparison.md 2026-08-15 entry, MASTER INVENTORY above.
