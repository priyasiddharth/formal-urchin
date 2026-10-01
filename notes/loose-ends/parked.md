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
**Status:** [SUPERSEDED → durable/certificate-guided-lowering.md, 2026-09-23]
— control flow is lowered along a Miri-derived certificate WITHOUT a CFG
in mirlite; the plan below (Stmt.switch/goto, block→pc layout) was not
taken. Kept as the record of the rejected alternative.
**Original status:** parked 2026-08-15
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
1. ~~**SwitchInt / runtime control flow**~~ **DONE 2026-09-23** by
   certificate-guided lowering (durable/certificate-guided-lowering.md):
   branches/loops/asserts follow Miri's recorded outcomes with runtime
   checks; fnentry_invalidation, int-to-ptr, two_phase_aliasing_violation
   flipped; the Option-match mains and the assert/`+=` rewrites reverted.
2. **Runtime integer arithmetic** — DONE 2026-09-24: folded when the
   operands are tracked, otherwise emitted as mirlite's `binOp` on two
   word places, so every branch on the result is a runtime check
   (0 unchecked pins). Fixed-width (wrapping) semantics is the remaining
   fidelity gap — own entry below.
3. **Runtime array indexing / subslicing** — `sliceLen` landed
   2026-09-24, so a runtime LENGTH is a real word and a bounds check on
   it is a real check. What remains: index PROJECTIONS still need a
   static field index, and range indexing (`&a[0..0]`) needs the std
   `Index<Range>` chain plus a `subSlice` rvalue (offset + extent from
   two runtime words) — own entry below.
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
10. **Static initializers** — DONE 2026-10-01: every global's
    initializer is inlined before `main` (outside certificate frames, the
    value stored through a scratch local so the global's stack is just
    its base item). A const whose initializer does not lower is
    unsupported; a static falls back to uninit (`null_mut()`,
    `without_provenance`: bodyless). Was: hoisted statics start undef.
12. **Integer addresses without provenance** — `transmute` ptr↔int,
    `with_addr`, `addr()`, int literals as pointers, byte-wise pointer
    copies: transmute_ptr, ptr_int_transmute, ptr_int_casts,
    ptr_int_from_exposed, provenance, option_box_transmute_ptr,
    strange_references (pass/, outside the SB dirs). mirlite has
    `exposeAddr` only; a provenance-stripping `addr` rvalue is new
    semantics + proof leaves, and the byte-level ones need a byte-level
    pointer representation the cell model does not have. [OBS 2026-10-01]
    Byte-addressing cost MEASURED (journal/2026-10/2026-10-01-byte-probe.md):
    splitting byte size from slot count breaks 20 theorems / ~3.5k proof
    lines (68 mechanical sites besides), SB layer untouched; a faithful
    C0 adds the layout-directed `readWordSeq` rework (unmeasured, est.
    20–40 more). Flips no Miri file by itself. Not before the paper.
11. **Miri-internal tests**: stack-printing, unknown-bottom-gc,
    zst-field-retagging-terminates.

### A′. Per-test blocker survey of the 39 unsupported entries (2026-09-27, HEAD c4b3c83)
Four read-only agents charon-compiled every unsupported source, ran the
loader on it and on candidate preps (scratch manifests only), and
generated Miri certificates where needed. [OBS] = observed in a run,
[HYP] = read off the source, not run. Several manifest `reason` fields
are STALE (marked †). Splitting a whole-file entry ADDS entries; the
whole-file entry stays unsupported.

**Tier 0 — no loader/model change (prep, split, or manifest only)**
**DONE 2026-09-27** — all ten below except drop_in_place_protector (left for
item q) landed: corpus 109/0/31 (was 99/0/39; +2 split-out entries),
`--osea` 109 matched, every fail entry's line pinned from Miri's own run.
| entry | what it takes | |
|---|---|---|
| illegal_read5 † | nothing: passes on the raw source (UB line 16; no Rc in it) | [OBS] |
| track_caller † | nothing: passes (line 10; Charon adds no location arg) | [OBS] |
| illegal_read3 | prep: union `HiddenRef` → `*const i32`; Miri gives the same UB line | [OBS] |
| mut_exclusive_violation2 | prep: NonNull → raw ptrs (repr(transparent)) | [OBS] |
| mixed_cell_deallocate | prep: `alloc` + store instead of `Box::new`/`into_raw` | [OBS] |
| box-cell-alias † | prep: drop trailing `val.get()` (UB fires first); real fix is item b | [OBS] |
| issue-miri-2389 | prep: `.cast::<i32>()` → `as *const i32` | [OBS] |
| 2phase::two_phase1 | split out | [OBS] |
| 2phase::two_phase_overlapping2 | split + local-trait rewrite of `+=` (keeps autoref) | [OBS] |
| basic::write_does_not_invalidate_all_aliases † | prep: `.cast` → `as` | [OBS 09-27] |
| drop_in_place_protector | only with a HEAVY prep (hand-inline drop_in_place) — prefer item q | [OBS] |

**Tier 1 — small loader/tooling fixes (each ≲ a few dozen lines)**
- a. **DONE 2026-09-29** — `ptrCast` in stdlite.lean for `*mut T::cast`,
  `*const T::cast`, `cast_mut`, `cast_const` (a tag-preserving copy; std is
  `self as _`, no retag). issue-miri-2389, write_does_not_invalidate_all_aliases
  and deallocate_against_protector2 use upstream `.cast` again. Witness
  local/ptr_cast_keeps_tag. Was: `<*T>::cast`/`cast_mut`/`cast_const` shim (tag-preserving ptrCast) —
  would remove the `.cast` rewrites above; also needed by box_into_raw,
  basic::zst, drop_in_place_retag, dealloc_against_protector2, unsafe_pinned.
- b. **DONE 2026-09-28** — function paths now keep impl blocks as
  segments (`core::cell::Cell::get`, `core::cell::<Ref as Deref>::deref`;
  `nameSegs` in ullbc_ast.lean), every shim matches its own function, and
  `Cell::get` has its own shim (reborrow + read). box-cell-alias runs its
  upstream body; interior_mutability::two_phase split out and passes.
  Was: **BUG: `Cell::get` hits the `UnsafeCell::get` shim** (both are
  `["core","cell","get"]` once impl segments are dropped;
  lowering.lean ~674) → "dst NatL vs rhs PtrL". Unlocks box-cell-alias
  honestly and interior_mutability::two_phase. [OBS]
- c. **DONE 2026-09-28** — a `Field` projection whose kind carries a
  variant (`{"Adt": [decl, v]}`) is now `.field (1 + i)`. Witnesses:
  local/enum_payload_read and the new split
  interior_mutability::rust_issue_68303 (both fail on the old code: type
  mismatch / the false UB at line 17). The two option tests never reached
  the read (it follows their UB), so their lowering is unchanged.
  Was: **BUG: enum-variant field projection drops the variant**
  (ullbc_ast.lean ~552, `findSome? asNat` over the reversed Field args), so
  `(x as Some).0` resolves to cell 0 = the discriminant, not 1+i.
  Gave a false-positive UB on a rust_issue_68303 rewrite; latent in the
  committed return_invalid_{mut,shr}_option artifacts. [OBS]
- d. **DONE 2026-09-28** (with b: `last_segment` strips a trailing `::`;
  and `is_user_frame` now judges `<Self as Trait>::f` by Self/Trait, so a
  user trait's default method on a std type is a user frame).
  Was: **BUG: `miri_cert.py` `last_segment`** — a turbofish frame
  `safe::split_at_mut::<i32>` strips to `…::` and the last segment is
  `""`, so generic user fns get no certificate events. Fix:
  `p.rstrip(": ").split("::")[-1]`. [OBS]
- e. **DONE 2026-09-29** — `propagateFnPtr` (lowering.lean) now runs on
  the seam's `.move` rvalue as well as on copies. Witness
  local/fn_ptr_moved_arg; deallocate_against_protector1/2 supported via
  the prep below, lines 19/21 pinned (model = Miri). Unsupported 31 → 29.
  Was: fn-pointer tracking lost through MOVED call args (`emitSeamBind` →
  `.move` branch doesn't propagate `fnPtrs`) → "indirect call with
  unknown target". With the prep (closure → named fn, leak → alloc,
  drop(Box) → dealloc) this alone unlocks dealloc_against_protector1/2. [OBS]
- f. **DONE 2026-09-29** — `collectBoxPointees` also reads `T` off
  `Box::new(v: T)`, `Box::from_raw(p: *mut T)`, `Box::into_raw`/`Box::leak`
  (`-> *mut T`/`&mut T`). Witness local/box_never_derefed. Flips nothing on
  its own: mixed_cell_deallocate (unprepped) and unsafe_cell_deallocate now
  stop at "call to bodyless function into_raw" — the `Box::into_raw` shim
  of item j.
  Was: Box pointee inference only from `*box` (`collectBoxPointees`); also
  infer from `Box::new`/`from_raw` argument types → mixed_cell_deallocate
  (no prep), dealloc_against_protector*, unsafe_cell_deallocate. [OBS]
- g. Integer `as` casts (`Cast Scalar`) and BitAnd/BitOr/Shl/Shr;
  offset shim should consult `constOf` for a const-tracked delta →
  buggy_split_at_mut, smallvec. [OBS]
- h. Loop visit budget (`walkBlock`, lowering.lean) compares cumulative visits
  against REMAINING events, so long certified loops trip it: 3 iterations
  pass, 100 fail → unknown-bottom-gc (+ Range→`while` rewrite or shims). [OBS]
- i. Zero-sized arrays expand to `List.replicate n` (Array type and
  Repeat) — `[(); usize::MAX]` HANGS the loader → keep ZST arrays zero
  cells; unlocks zst-field-retagging-terminates (passes at N=4). [OBS]
- j. (2026-09-29: shims now live in src/conformance/stdlite.lean — each
  new one is a `def … : Shim` plus rows in `stdlite.table`. `Box::into_raw`
  DONE 2026-09-29 (`boxIntoRaw`: fn-entry Unique, `&mut **b`, raw retag);
  mixed_cell_deallocate runs its upstream Box code. `Box::leak` DONE
  2026-09-29 (`boxLeak` = `boxIntoRaw` + `&mut *`); the protector tests
  use upstream `Box::leak(Box::new(..))` again. `ptr::write` /
  `<*mut T>::write` DONE 2026-09-29 (`ptrWrite`: a plain store) and
  `Atomic::new` as `cellNew`; illegal_dealloc1, arg_inplace_mutate,
  return_pointer_aliasing_{read,write}, arg_inplace_observe_during and
  mixed_mutability_static run their upstream `ptr.read/write` again.
  `Layout::new::<T>()` DONE 2026-09-29: `UFun.tyArgs` keeps the
  monomorphised instantiation, `stdlite.tyArgTable` holds shims that need
  it; mixed_cell_deallocate is now rewrite-free apart from annotations.
  2026-09-30: `size_of`, `UnsafeCell::raw_get`, `NonNull::{from,
  clone, as_ptr, cast, new_unchecked, as_mut}`, `ManuallyDrop::{new,
  deref, deref_mut}` DONE (NonNull = raw pointer, ManuallyDrop = its `T`
  when `T` has no references — MaybeDangling — inferred like Box's
  pointee); mut_exclusive_violation2 runs upstream NonNull code.
  `Option`/`Result` methods: NOT shimmed — a prep shadows the prelude
  `Option` with a user-written one carrying std's bodies, so Charon
  translates them and Miri's certificate records their frames and the
  `None` arm is an ordinary untaken branch (2026-09-30, pilot
  interior_mutability::rust_issue_68303, now upstream body). Needs
  `miri_cert.py` to judge plain paths without their generic arguments.
  Does not reach an Option/Result RETURNED by std (`Layout::from_size_align`).
  STILL OPEN: `null_mut` / `is_null`
  / `addr` / `without_provenance_mut` (a pointer without provenance and a
  NON-exposing address read — a mirlite/oseair change, item o);
  `slice::from_raw_parts_mut` (item r).) Std shims, each small: `Box::leak`, `Box::into_raw` (fn-entry
  Unique then raw retag), `Layout::new::<T>`, `ptr.write`, `is_null`,
  `ManuallyDrop::new`, `Option::{as_ref,unwrap,is_some}`,
  `AddAssign::add_assign`, `Layout::from_size_align`+`unwrap`.
  box_into_raw_allows_interior_mutable_alias needs only j+a. [HYP]
- k. `VaList` as an opaque word + variadic call arity; extra args bound
  WITHOUT retag (the test's point); prep needs `#![feature(c_variadic)]`
  → c_variadics. [HYP]

**Tier 2 — model / retag-rule changes (touch semantics, maybe proofs)**
- m. **DONE 2026-10-01** — `UTy.structT` deleted: struct decls parse to
  `UTy.tup`, so struct fields retag exactly as tuple fields (args,
  returns, loads); it had been the ONLY place the two differed (`elab`
  already erased it to `TupL`). Fork rewrites newtype_retagging /
  newtype_pair_retagging (closure → `fn free_it`, captured ptr → static
  `PTR`), verdict-only; no other verdict moved. Was:
  **By-value named-struct fields must be fn-entry retagged** →
  newtype_retagging, newtype_pair_retagging (both return "ok" today with
  the prep; the tuple variant passes). `containsRef (.structT _) = false`
  (emit.lean, `containsRef`) cites fnentry_invalidation2, but that test passes
  `&mut Thing` and retags never recurse through a reference, so it does
  not support the rule; newtype_retagging's own comment says "Make sure
  that we protect references inside structs". Re-run the corpus. [OBS+source]
- n. `place_base_raw`: `&raw` of a place based on a raw-pointer deref
  does NOT retag (Miri) — the loader always mints → raw_ref_to_part
  (+ Box::leak). May shift supported tests; re-run. [HYP]
- o. Zero-sized retag = no access, no bounds/liveness check; plus
  no-provenance pointers (`without_provenance_mut`) → basic::zst.
  Touches mirlite, oseair and the `ref` proof leaf. [HYP]
- p. [STEP 1 DONE 2026-10-01: weak Box protectors — see § B2. STEP 2 DONE
  2026-10-01: `UTerm.drop`; moved-place tracking (`LowerSt.moved`, keys
  as the trackers'; a move operand moves, an assignment/call destination
  re-initialises); `emitDropGlue` (Box: contents, then the certificate's
  `drop` event, then `dealloc` unless zero-sized; tuples/structs by field;
  enum holding a Box → unsupported); `mem::drop` drops its argument;
  `checkDrops` on — every Box drop in a certified test is matched against
  Miri's (`consumeDrop` / `missedDrop?`), past a UB prefix's end a drop is
  poison, not an error (`allConsumed`). 10 existing entries now really
  free their Boxes; deallocate_against_protector1 runs its upstream
  `drop(Box::from_raw(raw))` (verdict-only: Miri raises in std);
  unsafe_cell_deallocate split out. Still: drop glue of user `Drop` types,
  `drop_in_place` (item q), Vec/String.] Box drop → dealloc (Drop terminators and `mem::drop` are no-ops
  today, so several "ok" verdicts would be vacuous) — MUST land with weak
  Box protectors (B2 becomes exercised) and the `&mut !Unpin` →
  SRW/no-protector rule → not_unpin_not_protected, basic::zst freed case,
  interior_mutability::unsafe_cell_deallocate. [HYP]
- q. **STEP 1 DONE 2026-10-01** — `dropInPlace` shim (stdlite.lean):
  pushProt; protected Unique retag of `*p`; Box glue; popProt.
  drop_in_place_retag supported (verdict-only: Miri's UB span is in std;
  `miri_local.sh` reports line 9 from the "created by" help span, the call
  is line 10); witness local/drop_in_place_ok. The loader now REJECTS any
  crate with a local `impl Drop` (`userDropImpl?`): no supported artifact
  had one, and the glue silently skipped it. STEP 2 (open): Charon
  `--precise-drops` emits `drop_in_place` still opaque but per-type
  `{Destruct}::drop_glue` bodies + the user `drop` — the shim (and Drop
  terminators) must find T's glue fn and inline it [OBS]; the flag changes
  every artifact (MIR level ≥ elaborated), so cost the drift first.
  Was: `drop_in_place` shim (protected Unique retag of `*p`) + drop glue
  (Drop terminators call Charon's `drop_glue`; flags static on the
  single certified path) → drop_in_place_retag (also `cast_mut`),
  drop_in_place_protector, maybe_dangling::boxy, drop_after_sharing. [OBS]
- r. Slices from raw parts: `withLen` (runtime extent) +
  `ptrOffsetDyn` (existing parked entry) → buggy_split_at_mut (with d, g),
  buggy_as_mut_slice (+ Vec or a mini-Vec prep). Risk: Miri blames the
  tuple aggregate line 13; the loader doesn't retag ref aggregates. [OBS]
- s. `UnsafePinned` cell-like type + `&mut` to a non-`UnsafeUnpin` type
  gets the SRW retag (from a type mask, not `Unpin`) → unsafe_pinned;
  also coroutine's model need. Verify Miri's exact rule first. [HYP]
- t. `MaybeUninit<T>` = layout of T (`uninit`/`as_ptr`/`write`/
  `assume_init_ref`) → local/unassigned_local_addr,
  interior_mutability::into_interior_mutability; + unions (decl,
  aggregate, `&raw mut self.inline`, never retagged) → smallvec
  (after the g rewrites). [OBS]
- u. `MaybeDangling` (transparent, inner ref not retagged) + StorageDead
  actually killing locals → maybe_dangling (boxy also needs q). [HYP]
- v. dyn trait objects: unsize-to-dyn sets the extent, dyn reborrow
  retags `extent` cells, static dyn dispatch + `type_id` shim →
  wide_raw_ptr_in_tuple. [HYP]
- w. Vec/String container model (3-word header, push with protected
  fn-entry retag + realloc, len, as_ptr, `vec!` via `new_uninit`/
  `into_vec`, str literals, drop → dealloc) → 2phase ×5 fns,
  interior_mutability::unsafe_cell_2phase, buggy_as_mut_slice,
  drop_after_sharing, disjoint_mutable_subborrows. The biggest
  single unlock. [HYP]
- x. Closures through `FnOnce::call_once`/trait-impl calls ("call to
  non-static function") — every current closure use is avoidable by a
  named-fn prep, so it is optional.

**Tier 3 — out of scope or blocked upstream (6)**
retag_data_race_{read,write,protected_read} (threads + a data-race
checker, A5); return_pointer_aliasing_write_tail_call (pinned Charon:
"Unsupported terminator: tailcall"); coroutine-self-referential
(Charon: "Coroutines are not supported"); stack-printing (the test IS
Miri's printed stacks); box-custom-alloc-aliasing (allocator-generic
Box/Vec calling user `allocate`/`deallocate` — heaviest; revisit after w+q).

**Suggested order:** Tier 0 (8 entries flip + 2 split-outs), then b c d
e f (bugs first), then m (one rule, two tests), g+r (slice pair),
a+j (small shims), h i, then q, p, t, w.

### B. SB-model approximations (implemented, but simplified — all noted where they apply)
1. **Wildcard determinization**: accesses resolve to the topmost
   exposed granting item vs miri's angelic/"unknown bottom" reading.
   Verdicts coincide on all covered tests. NOW LOAD-BEARING FOR THE
   THEOREM (2026-09-13): with `fromExposed` inside `CoreProg`,
   `compile_correct` says the compiled program preserves THIS rule's
   verdicts. Both machines run the same rule, so the simulation is
   honest; the gap to Miri is the determinization, not the compiler.
2. **Box protector strength**: [SUPERSEDED 2026-10-01] a Box's fn-entry
   retag is `RefKind.BoxMut` (per cell = `Mut`); when protected its tag
   also goes into `AccessPerms.weakProt`, and `sb_dealloc` follows Miri's
   `Stack::dealloc`: protected items ABOVE the tag's item (popped by the
   write) are UB, weak or not; at/below it only strongly protected ones
   are. Witness local/box_arg_dealloc_weak; unit t19. Was: strong-style
   pop-blocking, weak protector's dealloc allowance unexercised. Plain Box-typed assignments (`let b2 = b`) are
   not retagged (miri's AddRetag would; unexercised).
3. **RefCell flag elision**: borrow/borrow_mut/deref/replace shims skip
   the borrow flag — valid only for conflict-free executions (all the
   corpus exercises); a test relying on a borrow-flag panic stays
   unsupported.
4. **Slice length convention**: a slice value is one cell carrying its
   own EXTENT (2026-09-23), and `sliceLen` reads the length off it in
   elements (2026-09-24). Zero-sized elements have no length in the
   extent. No sub-slices yet (range indexing).
5. **Enum freeze mask** (2026-09-30, was: every enum frozen): an enum
   holding a cell in any variant is interior-mutable as a WHOLE,
   discriminant included — exactly Miri's `visit_freeze_sensitive`,
   which treats a non-`Freeze` multi-variant enum like a union and does
   not read the variant. Remaining gap: Miri walks SINGLE-variant layouts
   field by field; the model's enum always has a discriminant cell.
   Witness local/enum_cell_shared_retag.
   **Enum layout**: discriminant word + prefix-merged payload — no
   niche optimization; incompatible variant layouts and nested refs in
   payloads are unsupported; payload seam retags are assignIf-guarded;
   [SUPERSEDED → durable/assignif-reads-its-discriminant.md, 2026-09-17]
   the discriminant read WAS a raw memory inspection; it is now an SB
   read on both machines, and the guard roots its destination first.
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
prep header. (2026-09-30: the rewrites that REPLACE std code with
user-written code live in the Miri fork, `corpus/tests/formal-urchin/`;
the rest stay in conformance/prep/. Candidates to restore upstream now
that shims exist: illegal_write2 `drop`, illegal_read7 `get_mut`,
cell_inside_struct `Cell::set`, unsafe_cell_invalidate `transmute`,
arg_inplace_observe_after / locals_alias(_ret) `ptr.read/write` notes.) The assert/`+=`/`match` rewrites were REVERTED 2026-09-23
(20 entries now run upstream code under a certificate); what remains is
method/intrinsic avoidance (ptr1.write → *ptr1, transmute → cast chains
where noted), `println!`, RefCell's flag probe, and one tuple
`assert_eq!` (the tuple's `PartialEq::eq` is an opaque std body).

## A word `binOp` rvalue (makes every certificate pin checkable)
**Status:** DONE 2026-09-24 (commits f41ddc0 model+proof, this one seam)
**Outcome:** `RExpr.binOp op a b` on two `NatL` places in mirlite,
`Rhs.BinOp op r1 r2` in oseair, `binOp_valuePkg` in proof/binop.lean
(the read package used twice; the only change to existing proofs is that
reads now export their register frame). The seam folds when it can and
emits otherwise; `symVals`/`tainted`/`memTainted`/`faithfulPlace` and the
T3 path are deleted. Corpus: 41 checked, 0 unchecked (was 27/14), same
96/0/40 and 96 matched differentially.
**References:** durable/certificate-guided-lowering.md,
journal/2026-09/2026-09-24-binop-rvalue.md

## Range sub-slicing (`&s[lo..hi]`)
**Status:** DONE 2026-09-25 (commit a955996)
**Outcome:** `RExpr.subSlice p lo hi` (three copy reads, then the
narrowed pointer — no retag, no memory event) with the register-only
`Rhs.SubSlice`; `subSlice_valuePkg` is the `binOp` package with a third
read. The seam shims `core::array::index{,_mut}` and
`core::slice::index::{index,index_mut,get_unchecked,get_unchecked_mut}`
into the receiver retag, the narrowing, and the mint over the narrowed
range. `fail/stacked_borrows/zst_slice` passes (verdict-only).
**References:** journal/2026-09/2026-09-25-sub-slicing.md,
durable/pointer-values-carry-an-extent.md

## Slices from raw parts, and runtime pointer offsets
**Status:** parked 2026-09-25
**Context:** the two slice tests still unsupported need one gap each
beyond sub-slicing. `buggy_split_at_mut` calls
`slice::from_raw_parts_mut(ptr, len)` and `ptr.offset(mid as isize)`
with a RUNTIME delta (mirlite's `ptrOffset` takes a static one).
`buggy_as_mut_slice` needs the same plus `Vec`, so it stays out until
containers land.

NOT a thin/fat distinction: mirlite has none — every pointer value is
one cell carrying `base offset extent size tag`, and the extent IS the
metadata Rust keeps in the fat half. What is missing is an rvalue that
SETS the extent from a runtime word: `sliceLen` reads it, `subSlice`
narrows it relative to the current one, `ref`/`Borrow (some n)` sets a
STATIC n, `alloc` sets the block, `fromExposed` sets `size − offset`,
and `ptrOffset` leaves it alone. Nothing sets `extent := n · elemSize`
for a runtime n.
**Why not just `subSlice p 0 n`:** it would work for this test (the
`as_mut_ptr` shim keeps the source slice's extent, so `n ≤ extent`), but
it is wrong in the direction that matters — Rust permits a length beyond
the pointer's provenance and Miri flags it at the reference creation,
while narrowing would retag a SHORTER range and MISS the UB.
**Design note for whoever picks this up:** `Borrow none` (the slice
retag) deliberately does no range check, justified by "the extent was
checked when the pointer was minted" (oseair.lean). A setting rvalue
weakens that justification. The saving grace is that every retag form
errors on a cell with no borrow stack (`sb-insert/sb-read/sb-write: no
borrow stack at address`), so an over-long extent still lands as UB —
the same verdict Miri gives, with a different message. Decide
deliberately: keep the unchecked retag and rely on the per-cell failure,
or bounds-check at the set. The same question already applies to
`ptrOffset`, which keeps the extent and so over-claims after `.add(k)`.
**Why parked:** sub-slicing was the ask, and both gaps are their own
rvalue-shaped changes.
**To resume:** (1) a `withLen` rvalue (or a `subSlice` variant taking a
thin pointer and a length) for `from_raw_parts{,_mut}`, proof by the
two-read package template; (2) `ptrOffsetDyn` reading its delta from a
word place — the same three-read shape as `subSlice`, minus the extent
change. Both tests' sources and Miri are available locally now.
**Effort estimate:** ~1 day for (1) + (2) together
**References:** journal/2026-09/2026-09-25-sub-slicing.md,
corpus/tests/fail/both_borrows/buggy_split_at_mut.rs

## Fixed-width (wrapping) arithmetic
**Status:** parked 2026-09-24
**Context:** mirlite words are unbounded `Nat` (sb.lean:30), so `binOp`
`sub` TRUNCATES at 0 and `add`/`mul` never wrap. Rust's checked ops only
differ on paths where Miri panics, and the certificate rejects those, so
no corpus verdict can silently diverge; `WrappingAdd/Sub/Mul` WOULD
diverge in value, and the corpus contains none (op strings present: Eq,
AddChecked, Lt, SubChecked). A branch on a diverged value would still be
caught by its own T2 check.
**Why parked:** it buys fidelity, not coverage, and the user chose
unbounded `Nat` when the plan costed both.
**To resume:** `binOp (t : IntTy) op a b` with arithmetic modulo `2^w`
and two's-complement comparisons, widths from Charon's operand types;
negative literals and `SwitchInt` cases become two's-complement words.
The proof does not unfold the arithmetic (`evalBinOp` is opaque to
`binOp_valuePkg`), so the cost is model + seam + tests only.
**Effort estimate:** ~half a day
**References:** notes/journal/2026-09/2026-09-24-binop-rvalue.md,
src/obseq3/types.lean `evalBinOp`

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
**Status:** DONE 2026-09-25
**Outcome:** all 13 `conformance/local/*.rs` run under the pinned Miri
(`cargo +nightly-2026-06-01 miri`, miri 0.1.0 14210df0e2) and every
verdict matches the manifest, including the UB one
(deref_read_disables_sibling, line 13 — the line the model reports, with
Miri naming the `*p = 5` on the line before as the invalidation).
Provenance flipped from "local-model-reasoned; pending real-Miri
verification" to real-Miri verified, and the run is repeatable:
`conformance/scripts/miri_local.sh` (new). [2026-09-28: Miri is now the
submodule pin 34d6a79544, and `scripts/live.py` re-checks every entry,
local witnesses included, on each CI run.]
**What the parking note got wrong:** it assumed Miri needed a build at
the PIN commit. The pinned TOOLCHAIN carries the `miri` component
(rust-toolchain in conformance/tools/ lists it) and `cargo miri` was
already usable — the corpus SOURCES are what this machine lacks
(see the certificate work's note), not Miri itself.
**References:** conformance/README.md (Local witnesses section),
journal/2026-09/2026-09-25-local-witnesses-miri-checked.md.

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

## copy: CLOSED 2026-08-31 — `copy_place_residual` is deleted
The copy dispatcher is TOTAL and the pin is 2 → 1; only
`ref_place_residual` remains. The last four leaves were
`copy_projdst_{zero,offset}_projsrc_offset_simulation` and
`copy_projlocal_fresh_projsrc_offset_{zero,offset}_simulation` —
one per (destination offset × bound/fresh root) — all carrying BRIDGE
1S around the READ. Pinned by d70-d74. See
journal/2026-08-31-copy-closes.md.

## REFACTOR: reparameterize `mirlite.PlaceRes` by offset
**Status:** parked 2026-08-31, attempted and reverted (verified sound)
**What:** carry `offset` in `PlaceRes` instead of the absolute `addr`,
deriving `addr := allocBase + offset`, so mirlite and oseair share one
pointer representation and `MemValSim`'s offset conjunct holds on the
nose instead of through `allocBase ≤ addr` arithmetic.
**Evidence it is sound:** the invariant `addr = allocBase + Σoffsets`
holds in all three `resolvePlaceAcc` arms and there is no other
constructor. The SEMANTICS change alone builds clean and leaves the
corpus untouched — 17/17 + 99/99, identical verdicts. The working patch
is kept at `notes/attic/placeres-offset-reparameterization.patch`.
**Why parked:** deriving `addr` changes the ASSOCIATIVITY of every
projected address (`allocBase + (offset + k)` where the proofs say
`(allocBase + offset) + k`), so ~50 sites across const_write, copy and
ref stop matching. A bridging simp lemma fixes the shape but must be
applied per consumer, on the goal or on a named hypothesis, and which
one is per-site: three automated passes moved the error count
59 → 46 → 55 → 67, non-monotone because Lean reports one error per
declaration and each fix unmasks the next.
**Payoff if done:** `h_dle` becomes `Nat.le_add_right`; the `h_cancel`
idiom (38 derivations, 143 uses) largely evaporates; one dead bounds
disjunct in `resolvePlaceAcc` becomes deletable.
**When to do it:** FIRST, if the leaf population ever grows again — a
second permission model, a v4, or a fourth statement form. It is a
fixed one-time cost of ~50 sites, so it pays for itself only when many
leaves are still unwritten. It did not pay against the five residual
sites left on 2026-08-31.
**Resume recipe:** apply the attic patch; rewrite the 28 `PlaceRes`
literals by script (offset is `0` or the visible `+ k`); then migrate
ONE DECLARATION AT A TIME using
`@[simp] PlaceRes.addr_shift : ({r with offset := r.offset + k}).addr = r.addr + k`,
rebuilding per file rather than per pass. See
durable/placeres-offset-reparameterization.md.

---

## the `_src_congr` destination merge (`assignPlaceArm`) — 2026-09-01

**Status:** measured and dropped. Do not re-attempt from the plan's
estimate; the plan valued it at ~160 lines and that number is dead.

**What it would be:** factor the general `.assign dst rhs` arm of
`compileStmtChecked` (compile.lean:773) into a named `assignPlaceArm`,
then merge `compileStmt_ref_src_congr_{deref,proj}_{run,value}` into one
destination-generic congruence. The `.local` arm (compile.lean:765) can
never join — it is a genuinely different compiled shape (no
`placeToRegChecked` on the destination).

**Why it is not worth it.** Target E (`exceptMap_agree`, `e7079a0`)
already took the value. The family is now 105 STATEMENT lines to 57
proof lines; deref+proj proof bodies total 42, which is the whole merge
ceiling. A generic congruence needs its own ~20-line statement and
~20-line proof. Net: between +20 and −5 lines.

**What it would cost.** Once the arm is a separate `def`,
`simp only [compileStmtChecked]` no longer reaches the do-block, so
every such site needs `assignPlaceArm` in its simp set — **159 sites**
(const_write 30, ref 56, copy 73). Plus it edits the compiler, which
sits under both audit roots.

**No cheap route exists.** Stating the congruence with an
`h_unfold : ∀ rhs, compileStmtChecked (.assign D rhs) = <do block>`
hypothesis avoids both the production change and the simp churn, but the
explicit do-block in the statement costs about what the merged bodies
save. And no attribute helps: `simp only [X]` will not reach through a
separate `def`, `@[reducible]` included.

**When to do it anyway:** if `assignPlaceArm` is wanted STRUCTURALLY —
to give future leaves a name for the arm — rather than for line count.
The 159-site sweep is mechanical and the four suites catch slips.

## Admit `ptrCast` into `CoreRhs`
**Status:** DONE 2026-09-14 (commit 42f538d). Resolved not by a second
store abstraction but by fixing the lowering — `ptrCast` was the last
caller of the `Memcpy` form `.copy` abandoned, and it carried a live
overlap divergence with mirlite. See
durable/ptrcast-was-the-last-memcpy-caller.md. `ptrOffset` landed the
same day (d9c0a41). `refSlice` is now the only excluded rvalue.

## Does `ptrOffset`'s deferred UB ever diverge from Miri?
**Status:** parked 2026-09-14
**Context:** mirlite and oseair both model `p.add(n)` as `wrapping_add` —
only `newOff < 0` is rejected, so an out-of-bounds pointer may be formed
and UB waits for the use. Rust makes the checked forms UB at the
computation. See durable/ptroffset-defers-ub-to-the-use.md.
**Why parked:** unwitnessed. Both corpus uses of `add` dereference
immediately, and the differential suite cannot see it because both
machines share the choice.
**To resume:** write a Rust witness that forms an out-of-bounds pointer
with `add` and never uses it, run it under Miri to pin the verdict, add
it to the manifest. If Miri says UB and we say ok, decide between a
bound argument on `ptrOffset` and splitting checked/wrapping.
**Effort estimate:** ~1h for the witness and the Miri run; ~half-day to
close it if it diverges.
**References:** ptroffset-defers-ub-to-the-use.md,
stacked-borrows-does-not-subsume-bounds-checks.md

## Admit `refSlice` (RESOLVED 2026-09-16 — split the mint out of the bracket)
**Status:** DONE. `refSlice` is in `CoreRhs`; `CoreRhs` is now total.
**How it went, versus what was parked here:** the parked plan was to
prove the mint COMMUTES with the `Die` it sits inside (`refFold_die_comm`
over a range, on top of a permissive `dieCellContent`). That whole line
was abandoned on the user's call. The mint was moved OUT of the bracket
instead — `Rhs.BorrowRest` split into `Rhs.Load` + `Rhs.RetagRest`, with
the compiler's shared `readRhsPre` gaining a `post` slot that runs after
the source cleanup — and `dieCellContent` went back to a strict head
match. `refFold_die_comm` was never finished and is not needed; the 472
lines of keystone machinery it sat on are deleted.
**Cost comparison, measured:** permissive die = +60 lines sb.lean, +472
keystone.lean, +27 permsim_transport.lean, one lemma still open. Split
lowering = +12 lines oseair.lean (`Rhs.RetagRest` + its arm), +35
common.lean (its step lemma), +20 compile.lean (`emit_append_state_incr`
and the arm), and the four `refSlice` proofs.
**References:** durable/split-the-mint-out-of-the-bracket.md;
durable/die-is-permissive-when-not-on-top.md (superseded);
durable/refslice-projsrc-mut-pops-the-projection-borrow.md (diagnosis).

## GEP: drop the `Borrow` at read-only projected sources (the user's call, twice)
**Status:** parked 2026-09-16, and REJECTED as scoped — recorded so it
is not re-proposed a third time.
**Context:** BRIDGE 1S proves `Borrow(Shared) +off; access through it;
Die` equals the bare access through the base's tag, so the compiler
could emit the shorter form. Two shapes: (b) `readRhsPre`'s `mk` takes
the projection offset, so the rvalue's own instruction accesses at
`base+off` through the base's tag — the access survives, the retag does
not; (c) `placeToRegChecked` emits `Rhs.PtrOffset` — tag-preserving
arithmetic, NO access. Either retires BRIDGE 1S and the `Borrow`/`Die`
at projected sources for all six read-then-store rvalues.
**Why parked:** both make field addressing unborrowed. The user's
2026-08-27 decision ("keep GEP as a borrow — do NOT add an access-free
FieldPtr; narrow the borrow to the field instead") covers (c) directly;
asked again on 2026-09-16 about (b), the user's answer was that the
offset is still applied with the base's provenance and no capability for
the field is ever created, so (b) does not escape the objection either.
The distinction between them — (b) keeps address formation fused to the
access, (c) lets a bare field pointer exist in a register — is a
difference of degree.
**To resume:** only if the decision changes. The payoff would be
deleting BRIDGE 1S, `copy_projsrc_offset_read`, and the proj-offset half
of all six read packages.
**Effort estimate:** ~1 day for (b), most of it re-checking the 45
compile facts through a changed `readRhsPre`.
**References:** obseq2-comparison.md 2026-08-27 (later);
durable/split-the-mint-out-of-the-bracket.md.

## Prove stale-item inertness at an arbitrary position
**Status:** parked 2026-09-14
**Context:** durable/a-stale-shared-item-is-unobservable.md argues, by a
case analysis over the five ways the model inspects a stack, that an
`Item.Ref t` for an unprotected, unexposed `t` is invisible to every
access. That argument is what says the differential suites could not have
caught the weak `die` — so it carries weight and deserves to be a
theorem.
**Why parked:** the three content lemmas already prove it for the LEADING
position, which is all the `refSlice` bracket needs; the general-position
version is documentation-grade rather than theorem-grade, since the
strong `die` is already in.
**CORRECTION 2026-09-14:** the first estimate here (~2-3h for a
per-access lemma) understated it. "Unobservable" cannot be stated per
access — verdicts depend on the whole trace, so the honest form is a
BISIMULATION: a relation "these states differ only by stale items",
preserved by every operation and agreeing on success. The per-access
lemma is only its inductive step.
**To resume:** (1) generalise `readCellContent_cons_ref`,
`insertAboveContent_cons_ref` and `writeCellContent_cons_ref` from
`Item.Ref t :: s` to `A ++ Item.Ref t :: B`, by induction on `A`, with
pivot-in-`A` and pivot-in-`B` as separate cases — the two list-level
ingredients, `find?_append_cons_false` and `splitStack_append_cons_ne`,
are proved and in. Each step still needs a congruence ("the access on
`x :: L` relates to the access on `x :: L'` whenever it does on `L` and
`L'`"), which does not exist yet. (2) close it into a bisimulation over
the operations.
**Effort estimate:** ~half-day for (1), unknown for (2). Documentation
grade — the strong `die` is already in, so nothing depends on this.
**References:** a-stale-shared-item-is-unobservable.md,
die-is-permissive-when-not-on-top.md

## Delete `compileStmtChecked`'s `.assign (.local loc)` fast path
**Status:** RESOLVED 2026-09-18 — deleted, with `StmtEvidence.assignLocal`.
`compileStmtChecked (.assign dst rhs) = compileAssignChecked dst rhs` is
now `rfl` for every destination. The ten local-destination compile
lemmas were repaired by ONE rewrite each: `compileStmt_local_run` /
`compileStmt_local_value_iff` (common.lean) restate the general path in
the fast path's shape (root via `ensureLocalRegE`, rvalue lowered to its
register), proved once from "a lowering never touches `placeRegMap`".
Net −90 lines. Entry kept for the trail.
**Status (original):** parked 2026-09-17
**Context:** commit dc164ad made `compileStmtChecked (.assign dst rhs) =
compileAssignChecked dst rhs` by `rfl` — for non-local `dst`. The
`.assign (.local loc)` arm survived (it carries `StmtEvidence.assignLocal`),
and it is the same stream as `compileAssignChecked (.local loc) rhs` only
up to `emit cs []` and a `placeToRegChecked Mut (.local loc)` lookup.
proof/assign_if.lean bridges the two (`compileAssignChecked_local_run`,
`_local_value`, ~60 lines) so the guarded body can hand a local
destination to the leaves.
**Why parked:** the bridge is cheap and the arm's proof did not need more;
deleting the fast path touches ~15 local-destination compile lemmas in
spine.lean/copy.lean (`compileStmt_storereg_local*`,
`compileStmt_readrhs_*srcflatten*`) that unfold the arm.
**To resume:** remove the arm and `StmtEvidence.assignLocal`; re-prove the
listed lemmas through `compileAssignChecked` (`ensurePlaceRoot (.local)`
= `ensureLocalRegE`, then `placeToRegChecked_local_value_of` /
`placeToRegChecked_local_run` from assign_if.lean); delete the bridge.
**Effort estimate:** ~2h
**References:** journal/2026-09/2026-09-17-assignif-guarded-root.md
