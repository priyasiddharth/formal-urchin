# obseq2 Development Log

Entries are newest-first. Each entry records a design discussion or decision made during obseq2 development.

---

## 2026-08-15 — OSEA-v3 uninit: CStore of Undef, No New Instruction

Thirteenth increment. `RExpr.uninit` compiles to `CStore ty (replicate blockSize Undef)` —
CStore already stores arbitrary `Val` lists through a useMut write, which is exactly
mirlite's undef fill. Undef cells are verdict-inert on both machines (SB never inspects
values), so partially-initialized aggregates copy identically through Memcpy.
Differential: **matched 56 | mismatch 0 | skipped 20**; uninit was first-blocker in only
3 of its 6 tests (histogram now alloc 7 · exposeAddr 5 · assignIf 3 · ptrCast 3 ·
ptrOffset 2). Unit tests 16/16 (golden g7, differential d9 incl. partial-init tuple copy).

---

## 2026-08-15 — OSEA-v3 Protector Frames (matched 25 → 53)

Twelfth increment, ~20 lines: `Instr.PushProt`/`PopProt` in oseair calling
`M.pushFrame`/`M.popFrame` (pop errors propagate as target UB), emitted directly from
`Stmt.pushProtectors`/`popProtectors`. The protected seam-retag borrows already carried
`prot` into `Rhs.Borrow`, so only the frame bracketing was missing. Differential:
**matched 53 | mismatch 0 | skipped 23** — every otherwise-core inlined-call test now
agrees with mirlite, protector UB attributed to the same statement. `assignIf` (3 tests)
surfaced from behind pushProtectors. Unit tests 14/14 (golden g6, differential d7/d8).

---

## 2026-08-15 — OSEA-IR v3 and the Differential Oracle (compiler back online)

Eleventh increment: the mission's compiler leg restarts on the v3 semantics.
`src/obseq3/oseair.lean` forks the v2 target with the machine parameterized by
`obseq3.PermissionModel` (`perms : M.State`, symmetric with mirlite, so a future
`CompilerInv` states `s_osea.perms = s_mir.perms` verbatim), all permission calls
range-based, and one `Rhs.Borrow (kind, prot, mask, len)` replacing the three v2 borrow
forms; `Die` carries the borrow's static length. `src/obseq3/compile.lean` ports the
Checked compiler family for the proof-core subset (constInit/copy/ref/halt; everything
else `CompilerError.unsupported`). Three deliberate scheme changes vs v2: deref lowering
no longer dies the loaded pointer register (its tag was loaded, not minted — dying it
would pop the source's own reference under per-cell stacks); `ensurePlaceRoot` allocates
a projected destination's root local before the rhs, mirroring mirlite's
`preparePlaceAssign` (aggregate desugaring assigns `_x.0` first); allocation order
matches mirlite so both machines mint identical addresses.

The harness gained `--osea`: compile each loaded program, run it, and require the same
verdict as mirlite — with target UB attributed to a source statement via per-statement
label ranges (`stmtLabelRanges`). First run: **osea: matched 25 | mismatch 0 |
skipped 51**; 14 of the matches are fail-tests UB-matched at the exact statement.
None of the plan's three GEP-as-ownership-events risks fired (the Raw-temp Die risk is
vacuous: compiler temps are never Raw). Skip histogram: pushProtectors 31 · alloc 6 ·
uninit 6 · exposeAddr 5 · ptrCast 2 · ptrOffset 1 — parked as named instruction designs.
Unit tests: 5 golden + 6 differential (2 negatives). Suite unchanged: pass 76 | fail 0.

---

## 2026-08-15 — The Box Unique Retag: Claim Unqualified

Tenth increment. Suite: **pass 76 | fail 0 | xfail 0 | xpass 0** — fail tests **56/75**
(48 line-accurate), 20 pass scenarios. Box arguments now receive miri's box retag at
inline seams: a protected Unique reborrow of the pointee (`UTy.boxT`; `Box::from_raw` =
tag-preserving copy; `mem::forget` = no-op). `box_noalias_violation` — whose expected
error, "weakly protected", is a category existing solely for this rule — is conformant at
miri's line, and all previously-passing Box tests held. The conformance claim loses its
one SB-policy qualification; what remains documented is the weak-vs-strong protector
dealloc nuance and untagged plain Box assignments, both unexercised by any reachable
test. The 19 remaining fail tests are language surface only.

---

## 2026-08-14 — The Conformance Claim: Complete SB Rule Coverage

Ninth and final increment of the session. Two stragglers whose unsupported-reasons
predated later increments turned out to already be reachable: `illegal_read_despite_exposed2`
(pure exposure machinery — the wildcard read Disables the Unique in place) and
`invalidate_against_protector3` (a `Layout::for_value` shim; protector violation on heap
cells). Suite: **pass 75 | fail 0 | xfail 0 | xpass 0** — fail tests **55/75**
(47 line-accurate), 20 pass scenarios.

With that, the claim (user's framing: compliance is about the model's rules, not the
language surface): **obseq3 implements the complete Stacked Borrows rule set**, each
mechanism witnessed by conformant tests — the rule → witness table is in
conformance/README.md, the durable statement in notes/durable/sb-conformance-claim.md.
The 20 remaining fail tests are blocked on SwitchInt, containers, threads, drop glue,
closures, or unions — the same SB rules through more language. One genuine SB-policy
simplification is documented: Box as implicit raw (no Unique box retag/protector;
box_noalias_violation alone needs it).

---

## 2026-08-14 — Slices: the First Runtime-Length Retags

Eighth same-day increment. Suite: **pass 73 | fail 0 | xfail 0 | xpass 0** — fail tests
**53/75** (45 line-accurate), 20 pass scenarios, 43 unsupported.

Slice references are one-cell fat values (the ordinary `ptrVal`) whose length is the rest
of their allocation; reborrows of slice data are `RExpr.refSlice` — the model's first
retag whose length is read at runtime (`size − offset` cells via the fat value's tag).
Unsize coercions are value copies; `as_ptr`/`as_mut_ptr` shims reproduce the receiver's
fn-entry retag before the raw data retag. Two fidelity facts pinned by
`fnentry_invalidation2` (now conformant at miri's exact line): named-struct fields are
NOT fn-entry-retagged (new `structT`/`tup` distinction — tuples ARE retagged, per
pass_invalid_shr_tuple), and call-replacing shims must carry the callee's entry retag
(the first draft missed the UB precisely because it didn't). The remaining 22 unsupported
fail tests all need dynamic control flow, std containers, threads, drop glue, unions, or
MaybeUninit — the retag-rule frontier is complete.

---

## 2026-08-14 — Arrays and Constant Pointer Arithmetic

Seventh same-day increment. Suite: **pass 72 | fail 0 | xfail 0 | xpass 0** — fail tests
**52/75** (44 line-accurate), 20 pass scenarios, 44 unsupported.

Fixed-size arrays are homogeneous tuples; charon's operand-carrying `Index` projections
resolve to static fields through tracked constant locals; `Repeat` rvalues and array
aggregates desugar per element; built-MIR bounds checks (`BinaryOp(Lt)` + `Assert`) are
const-folded away at lowering (dynamic arithmetic stays unsupported — arithmetic exists
only in statically-foldable positions). `ptr.add/offset/wrapping_offset` shim to
`RExpr.ptrOffset`: a constant delta scaled by pointee size, provenance-preserving, with
signed constants now parsed. Newly conformant: `unescaped_static` (UB at cell offset 1 —
the per-cell stacks in their purest form), `transmute-is-no-escape`
(`wrapping_offset(-1)` lands on a cell where the transmuted tag never existed), and the
`array_casts` pass scenario. Slices proper (fat pointers, runtime lengths) remain the
honest boundary.

---

## 2026-08-14 — RefCell Shims, SharedReadWrite Grouping, and the Disabled State

Sixth same-day increment. Suite: **pass 69 | fail 0 | xfail 0 | xpass 0** — fail tests
**50/75** (42 line-accurate), 19 pass scenarios, 47 unsupported.

RefCell is supported by *flag-eliding* shims (the borrow-flag discipline is a dynamic
borrow checker orthogonal to SB): `borrow`/`borrow_mut` = masked/unique reborrows of the
value region; `Ref`/`RefMut` guards = raw-layout values, deliberately unprotected at seams
(the `ref_protector` tests assert miri adds no protector for struct-wrapped refs); guard
`deref`/`deref_mut` = typed loads whose load-retag is the reborrow; `replace` and
`mem::drop` shimmed. Valid for conflict-free executions — all the corpus exercises.

Landing this forced the last core-model divergence closed, in two coupled fixes:
**SharedReadWrite grouping** (a write through an SRW item pops only above its contiguous
SRW run — `ref_mut_protector` needs the autoref sibling to survive) and **the Disabled
state** (reads disable Uniques in place rather than removing them; grouping without
Disabled merged groups and broke `disable_mut_does_not_merge_srw` + `interior_mut2` —
caught as missed-UB by the harness, exactly the failure mode miri's test comment warns
about). Newly conformant: `shared_rw_borrows_are_weak2` plus six `interior_mutability`
scenarios.

---

## 2026-08-14 — Transmute and Exposed Provenance (int-to-ptr without angelic choice)

Fifth same-day increment. Suite: **pass 62 | fail 0 | xfail 0 | xpass 0** — fail tests
**49/75** verdict-conformant (41 line-accurate), 13 pass scenarios, 48 unsupported.

The only memory-model addition is `Mem.allocs`, an allocation table making
address→(base, offset, size) a *function* — concrete Nat addresses under the deterministic
bump allocator mean int-to-ptr resolution needs no angelic choice (miri does the same
range lookup). Provenance semantics lives entirely in the SB state: an `exposed` tag set,
a reserved `wildcardTag` (so `ptrVal` and the access signatures are unchanged), and
per-access wildcard resolution to the topmost exposed granting item — a determinization of
miri's angelic wildcard, matching `-Zmiri-permissive-provenance` on all covered tests.
The ptr→int→ptr round trip deliberately destroys tag provenance: integers are bare words;
authority is re-derived at each access.

Transmute is shimmed by destination type (to-raw = tag-preserving `ptrCast`; to-ref = a
real retag — `illegal_write4` shows miri retags transmute-to-&mut results;
`transmute_copy` = a typed load). Reified fn pointers (`Cast FnPtr` + `Const FnDef`) are
tracked statically and `Dynamic` calls resolve to their targets, so the `aliasing_mut*`
family fails through genuine protected-seam collisions. Newly conformant: 13 fail tests
(aliasing_mut1-4, illegal_read8, illegal_write4, interior_mut2,
shared_rw_borrows_are_weak1, static_memory_modification, unescaped_local, exposed_only_ro,
illegal_read/write_despite_exposed1) + 2 pass scenarios (shr_and_raw, mut_below_shr).

---

## 2026-08-14 — Interior Mutability (UnsafeCell freeze masks, weak SRW protection)

Fourth same-day increment. Suite: **pass 47 | fail 0 | xfail 0 | xpass 0** — fail tests
**36/75** verdict-conformant (32 line-accurate), 11 pass scenarios, 63 unsupported.

Shared and raw-const retags now carry a type-derived per-cell **freeze mask**: cells inside
`UnsafeCell` get a SharedReadWrite item inserted above the granting item with no access;
the rest freeze. The mask is computed loader-side (`freezeMask` over `UTy`, which gained a
`cell` constructor) and carried on `RExpr.ref` — `obseq.LayoutTy` stays untouched.
Protection became **weak on SharedReadWrite** (popping/deallocating protected SRW is
allowed — verified by the `unsafe_cell_invalidate` pass scenario — while protected
Unique/frozen pops remain UB). `UnsafeCell`/`Cell` are opaque in charon output with
bodyless `new`/`get`: pointees are inferred from call sites, `new` is shimmed as identity,
`get` as a masked shared reborrow, `ptr::read` as a deref read; `Atomic*` maps to a
one-word cell. Pointer type-punning casts became tag-preserving reinterprets
(`RExpr.ptrCast`). Newly conformant: interior_mut1, illegal_read7,
mixed_mutability_static (all at miri's lines), plus cell_inside_struct and
unsafe_cell_invalidate on the pass side.

---

## 2026-08-14 — Enums (Option) and Heap Allocation/Deallocation (Box, std::alloc)

Third same-day increment. Suite: **pass 42 | fail 0 | xfail 0 | xpass 0** — fail tests
**33/75** verdict-conformant (29 line-accurate), 9 pass scenarios, 67 unsupported with
reasons. (Corrected progression: 21 → 25 → 33; earlier entries overstated by 2.)

**Semantics (obseq3):** `Stmt.alloc`/`Stmt.dealloc` (heap; `sb_dealloc` requires a live
writable tag at every cell, rejects any protected item in the stack, and removes the
borrow stacks — freed cells then fail with "no borrow stack"); `Stmt.assignIf` (an
assignment guarded on a runtime discriminant word — the variant-conditional retag
primitive); `AllocLen` (static or place-read allocation sizes).

**Loader:** type_decls parsing — monomorphized struct decls map to tuples, enum decls to
a discriminant word + prefix-merged payload cells, `Box` (opaque) to a mutable raw with
the pointee inferred from deref-projection use sites, `Layout` to its size word.
Enum-variant aggregates desugar to discriminant + payload writes. Seam copies of
enum-typed values retag payload refs under `assignIf` guards. Reference-typed values
loaded through a deref are retagged (Miri's load retag — what load_invalid_mut/shr test).
Name-based shims for `Box::new`, `std::alloc::{alloc,dealloc}`,
`Layout::from_size_align_unchecked`; `Drop` terminators lower to no-op gotos.

Newly conformant: illegal_dealloc1 (Miri's exact line and "deallocation … tag does not
exist" phrasing), illegal_write1, load_invalid_mut/shr, box_exclusive_violation1,
pass_invalid_shr_option (fails through the guarded enum retag at Miri's line),
return_invalid_{mut,shr}_option (verdict-only: call-site seam vs miri's `ret` line).
Box divergence noted: modeled as an implicit mutable raw, no Unique box retag.

---

## 2026-08-14 — Protectors and Statics Hoisting (zero conformance divergences)

Same-day follow-up to the conformance-suite entry below. Protectors landed as call-frame
protector sets in obseq3 (`AccessPerms.protFrames`; `pushProtectors`/`popProtectors`
pseudo-statements bracketing inlined calls; seam retags of reference-typed arguments —
including tuple fields — register their fresh tags as protected; read/write/die error when a
pop would remove a protected item). Statics hoisting landed loader-only (ULLBC `Global`
place roots rewritten to `uninit`-materialized locals; initializers not run). New
`RExpr.uninit`; 12 obseq3 unit tests.

Result: both protector xfails became line-accurate passes (Miri's exact lines and phrasing),
both statics tests promoted. Suite: **pass 34 | fail 0 | xfail 0 | xpass 0** — fail tests
25/75 verdict-conformant [corrected from 27/75; see notes correction 2026-08-14], and every test that loads agrees with Miri's
verdict. Remaining exclusions: interior mutability, deallocation, int-to-ptr, enums,
slices, threads, drop glue.

---

## 2026-08-14 — obseq3: Miri SB Conformance Suite (per-cell stacks, writable raws, Charon ingestion)

### Context

Goal: be able to call the SB semantics "conformant" by scoring it against Miri's test corpus
(fail tests must be flagged UB, pass tests must run clean). Audit found two v1/v2 divergences
from real SB that dominated feasibility (raws never writable; borrow stacks only at allocation
base addresses), and no executable tests on the SB-enforcing semantics at all. Full plan:
`plans/sb_conformance_obseq3.md`.

### What landed

- **`src/obseq3/`** — new versioned codebase (v1/v2 untouched, all proofs still green):
  per-cell borrow stacks (`sb_own` roots every cell; all ops range-based), mutability-carrying
  raw items (`RawPtr mutbl`: raw-mut ≈ SharedReadWrite — writable, survives reads; raw-const
  behaves like a shared item), `TwoPhase` reserved borrows, `Except String` errors with cell
  offsets, and a length-parameterized `PermissionModel`. Semantics forked from obseq2's mirlite
  with range-based access sites + implicit root allocation through projections.
  10 unit tests in `src/obseq3/tests.lean` (assert pattern + `expectErr`).
- **Faithful raw-retag placement**: raw-mut retags perform *no* parent access and insert the new
  item *directly above the granting item* (Miri's SharedReadWrite placement). This is what makes
  sibling raws coexist (`two_raw`) while `raw_tracking` still catches the invalidation — the
  earlier write-access-and-push-on-top draft was strictly stronger than Miri.
- **`src/conformance/`** — Charon ULLBC JSON → untyped AST → lowering (call inlining,
  linearization, storage/FakeRead dropping, tuple-aggregate desugaring, seam retags incl.
  composite tuple-field retags) → elaborator into the intrinsically-typed obseq3 syntax
  (`DecidableEq LayoutTy` + transport; no per-program proofs) → manifest-driven harness
  (`lake exe sb_conformance`). Charon emits no Retag statements — retags are synthesized at
  `Ref`/`RawPtr` rvalues (= the eager model) plus inline-seam retags.
- **`conformance/`** — pinned corpus (miri @ 34d6a795, 2026-08-13; charon nightly-2026.08.14),
  30 curated prep files, committed ULLBC artifacts, manifest with per-test
  status/reason/verdict/line.

### Score (miri @ 34d6a795)

- **fail tests: 21/75 verdict-conformant** [corrected from 23/75] (line-accurate on 19), 2 xfail-model
  (protector tests: our model silently pops protected items), 50 unsupported with
  per-test reasons.
- **pass scenarios: 9 clean** (incl. two_raw, mut_raw_mut, partially_invalidate_mut,
  disable-SRW-merge behaviors), rest unsupported with reasons.
- Suite: `pass 30 | fail 0 | xfail 2 | xpass 0 | unsupported 77 | total 109`; missed UB is
  always a hard failure; Miri message *text* is never matched (structural verdict + line only).

### Exclusions (documented per-test in conformance/manifest.json)

Protectors, interior mutability (UnsafeCell/Cell), deallocation/Box, int-to-ptr exposure,
transmute, enums/control flow, arrays/slices, threads, statics. These are Phase C in the plan.

---

## 2026-06-17 — Closing the `const_write` Sorry: Reconstruct-not-Port and the Identity-on-Domain Rename Invariant

### Context

`compile_correct` and its single-step driver `CompilerInv_step` are fully proved. The remaining
gaps are the three per-instruction simulation lemmas they delegate to:
`CompilerInv_step_constWrite` (via `const_write_resolved_simulation`), `CompilerInv_step_copy`,
and `CompilerInv_step_ref`. This entry records the design decisions made while planning the first
of these, the constant-write case. A v1 (`obseq`) analog — `existing_write_simulation` in
`src/obseq/proof/state_helpers.lean` — exists and is fully proved, which raised the question of
whether to port it or reconstruct natively.

### Decision 1: Reconstruct from v2, do not port v1

The v2 proof should be reconstructed against v2's own primitives; v1's `existing_write_simulation`
is a *phase-structure reference only*, not code to port. The reason is principled rather than
stylistic: v1's lemma is dominated by exactly the machinery v2 was designed to delete.

| Concern | v1 (`existing_write_simulation`) | v2 (reconstruct) |
|---|---|---|
| Fragment placement | `StartsAt` list slices, offset case-splits with literal instr lists | code-map `simp` + `compileProgFrom_code_eq_compileStmt` |
| State monotonicity | `*_state_incr` lemma family | `CompilerM.incr` (StateIncr in the monad) |
| Type consistency | explicit `PlaceMap π`, `baseLayout`/`subLayout`, `ptr_sim` | free (intrinsic typing `Place Γ τ`) |
| Invariant | `StateSim π ρa ρt … ptr_sim` + separate `TargetNonInterference` | single `CompilerInv` |
| Execution | `StepStarWith` (transitive closure) | indexed `runN n` + `oseair_runN_add` |
| Pointer-in-register | `place_runtime_sim` hypothesis | `PlaceRegReady` (packages the `useMut` witness) |

A line-by-line port would re-introduce v1 scaffolding (separate type tracking, list-slice
placement, per-function state-incr lemmas, `StepStar`, the two-part invariant) and then fight every
v2 abstraction to map it back. What actually transfers is the small *seven-step skeleton* (invert
MIR write → run fragment → transport SB → memory sim → preserve freshness → reconstruct invariant →
extend ρ), which is already encoded in `common.lean`'s factoring.

### Decision 2: Add an identity-on-domain rename conjunct, justified by lockstep bump allocators

This is the pivotal decision. `CompilerInv` carries `s_osea.ap = s_mir.perms` as **verbatim
equality**, yet `PlaceRegReady` demands `useMut s_osea.ap (b' + off) t' = some ap2` at the
**renamed** target address `b' = ρa(allocBase)`, while the source write consumed `useMut` at the
**un-renamed** source address `resolved.addr`. These reconcile only if ρa is the identity on live
addresses and ρt on live tags. Nothing in the invariant asserted this, even though it is true: the
source and target run **identical lockstep bump allocators** —

```
-- src/obseq2/mirlite_semantics.lean
def allocate (m : Mem) (sz : Nat) : Word × Mem :=
  let base := m.addrStart
  (base, { m with addrStart := base + sz })

-- src/obseq2/oseair.lean
def allocate (m : Mem) (sz : Nat) : Word × Mem :=
  (m.addrStart, { m with addrStart := m.addrStart + sz })
```

so both sides hand out the same `addrStart` in the same order, and the address/tag namespaces
coincide. We make this explicit by adding two conjuncts to `CompilerInv`:

```lean
def IdentityOnDomain {α : Type} (ρ : α → Option α) : Prop :=
  ∀ a a', ρ a = some a' → a = a'

-- CompilerInv now ends with:
--   … ∧ s_osea.ap = s_mir.perms
--   ∧ PermissionModel.stackedBorrows.WellFormed s_mir.perms
--   ∧ IdentityOnDomain ρa ∧ IdentityOnDomain ρt
```

Consequence: in `writeThroughPtr_sim`, permission transport becomes the source `useMut` verbatim
(via `s_osea.ap = s_mir.perms` + identity), the bounds check is literally the source bound
(`b' + off = allocBase + off = resolved.addr`), and memory simulation is `MemValSim (word v)
(Dat v)`. No renaming-invariance lemmas are needed in `permission.lean`.

**Alternatives rejected.** (a) Generalize `s_osea.ap = s_mir.perms` to a renamed relation
`PermSim ρa ρt s_mir.perms s_osea.ap` and prove `useMut`/`sb_use_mb` renaming-invariance lemmas —
more faithful to CompCert's `inject` model, but heavier and it touches the permission layer.
(b) Leave the invariant unchanged and derive `ρa a = a` on the fly inside the write lemma —
risk: the equality is not derivable without a global identity fact, so it would surface as a stuck
goal.

**Preservation obligation.** The conjunct must survive `AddrRenameIncr`/`TagRenameIncr`. Regime-B
fresh allocation (below) extends ρa/ρt with *identity* entries (`newAddr ↦ newAddr`), so it stays
identity-on-domain; a small preservation lemma is owed when that code lands. This is a *semantic*
invariant, categorically different from the code-placement/slice conjunct that was deliberately
kept out (see the 2026-04-28 entry on why `CompilerInv` stays lean).

### Decision 3: Split `const_write_resolved_simulation` by regime

The single lemma was quietly covering two regimes admitted by its `h_prep`/`h_res` hypotheses:

- **Regime A — existing write:** `resolvePlace? s_mir dst = some _`, so `preparePlaceAssign` was a
  no-op (`s_pre = s_mir`); ρ unchanged. The direct analog of v1's `existing_write_simulation`.
- **Regime B — fresh local:** resolves only after prepare (only reachable for `.local loc`;
  proj/deref error in `preparePlaceAssign`). `allocateBase` ran, so ρa/ρt must **extend** — this is
  where the rename maps do real work and the identity-extension preservation lemma is needed.

Keep `const_write_resolved_simulation` for A; add `const_write_fresh_local_simulation` for B;
dispatch in `CompilerInv_step_constWrite` by casing on `resolvePlace? s_mir dst`.

### The native-v2 regime-A skeleton (five phases)

1. **Locate** the fragment via `compileProgFrom_code_eq_compileStmt` + `targetLabelAt` (replaces
   v1's `StartsAt` list slicing).
2. **Run the place fragment** (`placeToRegChecked_run_sim`, shared with copy/ref) → `PlaceRegReady`;
   empty for the already-mapped-local case.
3. **CStore** via `runN_CStore_step` + `writeThroughPtr_sim`.
4. **Cleanup `Die`s** via `runN_cleanupInstrs` (none for local).
5. **Reconstruct** the invariant, composing runs with `oseair_runN_add`.

### Decision 4: `runN_cleanupInstrs` is conditional, not unconditional

The original commented stub claimed the `Die` sequence *succeeds* unconditionally. That is false:
each `Die` calls `sb_die`, which can fail. The lemma was reformulated as **"if the run completes,
it preserves memory and registers and advances the pc by the cleanup length"**; run completion
(the per-`Die` `sb_die` success, i.e. the deferred ap-coherence) stays the caller's obligation,
where the borrow facts are available. `runN_CStore_step` and the locator carry no such caveat.

### Scoping note

Not all "mechanical helpers" are on the const-write critical path. `runN_cleanupInstrs` is **not**
needed for writes to a local: the `assignLocal` branch of `compileStmtChecked` emits no
`cleanupInstrs`, and `ensureLocalRegE` returns `cleanup := []` for both existing and fresh locals,
so **both** local regimes have zero `Die`s. Cleanup is only needed for proj/deref `dst`. The
recommended first milestone is therefore regime-A already-mapped-local (`n = 1`, fragment is just
`[CStore …]`), which exercises the full reconstruction with the least scaffolding.

### Status

- Step 1 (landed): `IdentityOnDomain` predicate + the two `CompilerInv` conjuncts; the two
  destructure sites in `const_write.lean` updated. `lake build` green; only the three expected
  sorries remain.
- Step 2 (landed): mechanical execution helpers in `common.lean` —
  `compileStmt_emitted_in_compProg` (locator wrapper), `runN_CStore_step`, `step_Die_preserves_reg`,
  `runN_allDie_preserves`, `runN_cleanupInstrs`. All proved; shared with copy/ref.
- Next: `writeThroughPtr_sim` (now tractable under the identity conjunct), then the regime-A
  already-mapped-local milestone.

---

## 2026-04-30 — CompCert Memory Model and Non-Interference

### Context

The question arose whether adopting a CompCert-style `Block × Z` address space (opaque block IDs
rather than flat `Word` addresses) would simplify non-interference proofs — particularly the
simulation invariant for `placeToReg`.

### What CompCert Does

CompCert represents memory addresses as `(b : Block) × (ofs : Z)` where `Block` is a globally
unique allocation ID. Each call to `Mem.alloc` returns a fresh block strictly greater than all
existing ones. The key consequence is `Mem.load_store_other`:

```
b1 ≠ b2 → Mem.load chunk m b1 ofs = Mem.load chunk (Mem.store chunk m b2 ofs' v) b1 ofs
```

Two distinct blocks are *definitionally* disjoint — the memory map is a function over `Block` and
stores to `b2` literally do not affect the map at `b1`. Cross-allocation non-interference reduces
to `b1 ≠ b2`, which follows immediately from the allocator's freshness guarantee.

CompCert does not use a rename map for addresses between passes. Most passes use `inject_id` (the
identity injection), so source addresses and target addresses are literally the same `Block × Z`
values. No ρa equivalent is needed because the shared address namespace is preserved through
compilation.

### What It Would Help in obseq2

The main place flat arithmetic hurts currently is in `placeToReg_emits_no_mem_effects` and
`placeToReg_mem_preserved` — specifically showing that a newly allocated local (from `ensureLocalReg`
→ `Rhs.Alloc`) does not overlap with any binding already in `Env`. With a block model this reduces
to `newBlock ≠ existingBlock`, which follows directly from the allocator's freshness postcondition.
With flat addresses the `AllocatorProofSpec.alloc_fresh` field must carry explicit arithmetic facts
about `addrStart + i` not appearing in any prior `mMap` entry.

### What It Would Not Help

The harder non-interference obligation is intra-allocation aliasing: that `placeToReg` for `deref`
and `proj` emits `BorOffset`/`MutBorOffset`/`Load` instructions that do not conflict with the
destination's `useMut` permission check. This is entirely a stacked-borrows concern — `Block × Z`
addresses are orthogonal to `AccessPerms`. The permission model reasons per-address within a block,
and block separation does not rule out aliasing within a single allocation.

The real bottleneck is the stacked-borrows frame lemma: "if I hold permission `tag` at address `a`,
and `sb_ref`/`sb_read` fires at a *different* address `a'`, my permission at `a` is unaffected."
That lemma lives in `sb.lean` and has no dependency on flat vs. block addresses.

### Why the Migration Is Not Worth It Now

- `oseair.Val.Ptr` uses `(base offset size tag : Word)` — migrating to `(block : BlockId) (offset size : Word) (tag : Tag)` would require changing every pattern match.
- `sb.lean` uses flat `Word` addresses throughout `AccessPerms` and all `sb_*` operations.
  Refactoring it to `BlockId × Z` is a large surface-area change with no payoff on the central proof gap.
- The current `AllocatorProofSpec` serves the same purpose as block freshness — it just requires
  explicit arithmetic reasoning rather than deriving it from disjoint block IDs.

### Verdict

A block-based model would remove one tedious arithmetic side condition (cross-allocation freshness),
but would not touch the central difficulty (stacked-borrows frame lemmas for intra-allocation
aliasing). Migration cost is high; benefit is narrow. The pragmatic path is to keep flat addresses,
treat `AllocatorProofSpec.alloc_fresh` as the block-separation axiom, and focus proof effort on the
stacked-borrows frame lemmas that are the actual bottleneck.

---

## 2026-04-30 — Fragment Installation: Labels vs Runtime PCs

### Problem

Proof obligations such as the `placeToReg` slice in `const_init.lean` originally mixed two
different facts in one goal:

```lean
compileProgFrom cs0 prog (s_osea.pc + i) =
  dstCS.code (cs_cur.nextLabel + i)
```

The left side starts from the runtime machine PC, while the right side is indexed by compile-time
labels allocated in `CompilerState`. This works for straight-line code, but it hides the important
distinction between code layout and control-flow reachability.

### Decision: Split the Facts

Use a compile-time label predicate for code layout:

```lean
def FragmentInstalledAtLabel (m : CompilerM α) (cs : CompilerState)
    (baseLabel : Nat) (prog : oseair.Prog) : Prop := ...
```

This says: the fragment emitted by `m` from compiler state `cs` appears in `prog` starting at
compile-time label `baseLabel`. It deliberately does not mention runtime PC.

Keep the execution-facing predicate separate:

```lean
def FragInstalled (m : CompilerM α) (cs : CompilerState)
    (s : oseair.State) (prog : oseair.Prog) : Prop := ...
```

This says: the same fragment is installed at the current runtime PC, so an execution lemma such as
`placeToReg_correct` can run it with `runN`.

The bridge is explicit:

```lean
s.pc = baseLabel →
FragmentInstalledAtLabel m cs baseLabel prog →
FragInstalled m cs s prog
```

### Branching Implication

When branches are added, `FragmentInstalledAtLabel` should remain a pure compile-time layout fact.
What changes is the runtime control proof that establishes `s.pc = baseLabel`. In straight-line
code this comes from prefix compilation (`targetPcAt`); with branches it should come from a CFG or
label-map invariant saying that execution has reached the relevant source point's target label.

Naming rule: use `label` / `baseLabel` / `nextLabel` for compile-time code positions. Reserve `pc`
for runtime machine state.

---

## 2026-04-30 — CompCert-Style `StateIncr` Compiler Monad

### Problem

The 2026-04-28 code-map refactor fixed the representation problem (`Prog = Nat → Option Instr`),
but it left a large proof-engineering burden in `proof/common.lean`: every compiler function that
threaded `CompilerState` needed paired monotonicity lemmas such as:

- `placeToReg_state_incr`
- `placeToBorrowReg_state_incr`
- `compileRExprTo_state_incr`
- `compileStmt_state_incr`
- fold-level state-growth lemmas

Those lemmas all proved the same structural fact: compiler actions only extend the generated code
and fresh counters; they do not rewrite previously allocated target-code labels.

### CompCert Analogy

CompCert's RTL generator does not separately re-prove this after every compiler function. Its
code-generation monad carries a `state_incr` proof in the result type. `bind` composes those proofs
with `state_incr_trans`, so monotonicity is a construction invariant of the compiler, not a family
of after-the-fact lemmas.

### Decision: Add `CompilerM`

`src/obseq2/compile.lean` now defines the compiler-state growth relation directly:

```lean
structure StateIncr (s1 s2 : CompilerState) : Prop where
  nextLabel_le : s1.nextLabel ≤ s2.nextLabel
  nextReg_le   : s1.nextReg ≤ s2.nextReg
  code_eq      : ∀ label, label < s1.nextLabel → s2.code label = s1.code label
```

The `label` argument is deliberately not called `pc`: this is a compile-time target-code slot.
Runtime states later use natural-number PCs to index the same code map, but `StateIncr` is about
compiler state transitions.

The new compiler monad is:

```lean
abbrev CompilerM (α : Type) : Type :=
  (cs : CompilerState) → α × { cs' : CompilerState // StateIncr cs cs' }
```

`pure` returns the same state with `StateIncr.refl`. `bind` runs the first computation, then the
second from the intermediate state, and composes their witnesses with `StateIncr.trans`.

### Compiler Refactor

The compiler functions now produce monadic computations:

| Old shape | New shape |
|-----------|-----------|
| `placeToReg cs kind p : PtrResult` with `PtrResult.cs` | `placeToReg kind p : CompilerM PtrResult` |
| `placeToBorrowReg cs kind p : PtrResult` | `placeToBorrowReg kind p : CompilerM PtrResult` |
| `compileRExprTo cs dst expr : CompilerState` | `compileRExprTo dst expr : CompilerM Unit` |
| `compileStmt cs stmt : CompilerState` | `compileStmt stmt : CompilerM Unit` |
| `List.foldl compileStmt cs prog` | `CompilerM.run (compileStmts prog) cs` |

`PtrResult` and `RExprResult` no longer contain a `cs` field. Intermediate compiler states are
obtained explicitly with:

```lean
CompilerM.run m cs
```

and emitted result values with:

```lean
CompilerM.value m cs
```

The primitive operations are now:

- `emitM : List Instr → CompilerM Unit`
- `freshRegM : CompilerM Register`

Both carry their `StateIncr` proof at construction time.

### Proof Effects

The repeated per-function state-growth lemmas were removed from `src/obseq2/proof/common.lean`.
When a proof needs state monotonicity, it now uses:

```lean
CompilerM.incr computation initialState
```

For example, suffix compilation preservation in `compileProgFrom_code_eq_compileStmt` now gets the
"later statements do not overwrite this statement's emitted code" fact directly from the monadic
state witness:

```lean
(CompilerM.incr (compileStmts suffix) stmtState).code_eq label h_label
```

The code-map preservation lemmas `emit_code_lt_nextLabel` and `emit_nextLabel_ge` moved into
`compile.lean`, because they are foundational facts used by `emitM` itself rather than
proof-only infrastructure.

### Impact on `const_init.lean`

The previous `const_init` proof script was written against the old `.cs` field:

```lean
let dstRes := placeToReg cs_cur .Mut dst
dstRes.cs
```

After the monadic refactor the same proof strategy is expressed with explicit monadic state
extraction:

```lean
let dstM := placeToReg RefKind.Mut dst
let dstRes := CompilerM.value dstM cs_cur
let dstCS := CompilerM.run dstM cs_cur
let h_place_incr := CompilerM.incr dstM cs_cur
```

The old proof body was temporarily too stale to typecheck after the API break. The file now keeps
the original phase structure as a monadic skeleton:

1. prove the `placeToReg` slice in the full compiled program,
2. run `placeToReg_correct`,
3. identify and run the emitted `CStore`,
4. identify and run cleanup `Die`s,
5. reconstruct `CompilerInv`.

The detailed slot-identification proofs remain as localized `sorry`s, but the proof strategy is
preserved instead of being collapsed into a single opaque placeholder.

### Current Status

`lake build` passes with the existing proof scaffolding. The refactor reduces the long-term proof
burden: adding new compiler functions should require constructing `CompilerM` computations from
`emitM`, `freshRegM`, and other monadic compilers, rather than adding a new family of
`*_state_incr` lemmas.

---

## 2026-04-28 — Code Map Representation for OSEA-IR (`Prog = Nat → Option Instr`)

### The Problem

`const_init.lean` contains a sorry that cannot be closed without a new structural lemma:

```lean
have h_slice : ∀ (i : Fin fragLen),
    (compileProgFrom cs0 prog).get? (s_osea.pc + i.1) = some (fragInstrs.get i) := by
  sorry
```

The claim is that the instructions emitted by `placeToReg cs_cur .Mut dst` appear at position
`targetPcAt cs0 prog s_mir.pc` in `compileProgFrom cs0 prog`. Proving it requires reasoning about
`List.foldl compileStmt` and how each `emit` appends to the growing instruction buffer — a
structural fact (`compileStmt_instrs_prefix`) not currently in `common.lean`. The same pattern
recurs for `h_cstore_instr` and `h_die_instrs` in the same proof, and will repeat for the copy
and ref cases.

### How CompCert Avoids This

CompCert uses a `PTree.t instruction` (a partial map from node IDs to instructions) in its RTL
pass rather than a flat `List Instr`. Compilation writes each instruction directly to a specific
code position at emit time. The simulation relation's "current instruction" conjunct is then a
direct map lookup — `fn_code ! pc = Some instr` — not a derived fact about list structure.

### Decision: `Prog = Nat → Option Instr`, `CompilerState` uses a label allocator

**`oseair.Prog`** changes from `List Instr` to `Nat → Option Instr` — a partial function from
target PC to instruction.

**`CompilerState`** replaces `instrs : List Instr` with two fields:

```lean
structure CompilerState where
  nextReg   : Nat                 -- fresh register allocator (unchanged)
  nextLabel : Nat                 -- fresh code-position allocator
  code      : Nat → Option Instr  -- sparse map; only emitted slots are Some
```

`nextLabel` is the code-position analog of `nextReg`: it is a compile-time counter, not a runtime
construct. The name is deliberately distinct from "PC" to avoid conflating compilation order with
runtime control flow. When branches are added to oseair, `freshLabel` will allocate a slot before
its instruction is known (forward references), and `setInstr` will fill it in later — exactly the
backpatching pattern that is impossible with an append-only `List Instr`.

**`emit`** writes a batch of sequential instructions starting at `nextLabel`:

```lean
def emit (cs : CompilerState) (instrs : List Instr) : CompilerState :=
  { cs with
    nextLabel := cs.nextLabel + instrs.length,
    code      := fun pc =>
      if h : cs.nextLabel ≤ pc ∧ pc < cs.nextLabel + instrs.length
      then instrs.get? (pc - cs.nextLabel)
      else cs.code pc }
```

The slice condition `h_slice` then holds by `simp` from the `emit` definition — the instructions
are in the map by construction. `h_cstore_instr` and `h_die_instrs` close the same way.

### Why Not Just Add the Structural Lemma?

For the current straight-line IR a single `compileStmt_instrs_prefix` lemma would also close the
sorry. The code-map refactor is chosen instead because:

1. **Branches are planned.** A flat `List Instr` cannot express forward branch targets without a
   second pass. When oseair gains `Jump`/`Branch` instructions, the flat-list compiler must be
   rewritten regardless. Doing it now avoids the refactor twice.
2. **All three slice sorries disappear at once.** The lemma approach closes `h_slice` but still
   leaves `h_cstore_instr` and `h_die_instrs` as separate sorries requiring additional argument.
3. **`CompilerInv` stays at 7 conjuncts.** The 8th-conjunct approach (adding the slice fact to the
   invariant) would close the sorry but grows the invariant for every future case.

### Files Changed

| File | Change |
|------|--------|
| `src/obseq2/oseair.lean` | `abbrev Prog := Nat → Option Instr`; `stepWith` uses `prog state.pc` |
| `src/obseq2/compile.lean` | `CompilerState`: drop `instrs`, add `nextLabel` + `code`; rewrite `emit`, `freshReg`, `initLocals`, `compileProg` |
| `src/obseq2/proof/common.lean` | `CompilerStateWF`, `compileProgFrom`, `targetPcAt` updated; `h_slice` pattern closes by `simp` |
| `src/obseq2/proof/const_init.lean` | `h_slice`, `h_cstore_instr`, `h_die_instrs` sorries removed |

### Implementation Note

The refactor is now implemented. The proof-side placement argument is not a list-slice lemma
anymore; it is factored through code-map preservation lemmas:

- `emit_code_lt_nextLabel`: emitting at `nextLabel` preserves all earlier labels.
- `compileStmt_code_lt_nextLabel` and `foldl_compileStmt_code_lt_nextLabel`: compiling later
  statements cannot overwrite code below their starting label.
- `compileProgFrom_code_eq_compileStmt`: if `prog.get? pc = some stmt`, then the whole compiled
  program agrees with the code produced by compiling `stmt` from `csAt cs0 prog pc`, for every
  label before that statement's resulting `nextLabel`.

`const_init.lean` uses those facts to close the old `h_slice`, `h_cstore_instr`, and
`h_die_instrs` obligations without adding new sorries. The remaining sorries in that file are the
pre-existing semantic simulation obligations unrelated to emit placement.

---

## 2026-04-25 — Bounds Semantics, Typed OSEA-IR, and Proof Infrastructure Direction

### Should OSEA-IR be typed like MIRLite?

Considered making OSEA-IR intrinsically typed (dependent type indices on `Instr`, like MIRLite's
`RExpr Γ τ`). Decided against full typed IR. The right approach is a **proof-side WF layer** over
the flat IR:

- `RegValWF ty vals` — values have the right shape for the type
- `RegMapWF regTypes reg` — every live register matches its expected type
- `InstrWF regTypes instr regTypes'` — instruction-level typing relation tracking register effects
- `CompiledWF Γ cs` — compiled code is well-formed

This keeps OSEA-IR operationally simple while giving proofs the same benefit as typing: impossible
bad states are ruled out once by WF lemmas, not reproved at every step. Full typed OSEA-IR would
only pay off if type preservation were a stated goal; for behavioral simulation it is unnecessary.

### Two target semantics bugs fixed

**Bug 1: `RStore`/`CStore` ignoring their `ty` field**

Both instructions carried a `ty : TyVal` parameter but matched it with `_ty`, ignoring it. Fixed:
- `RStore ty src ptr` now checks `srcTy == ty` (source register type must match declared type)
- `CStore ty vals ptr` now checks `vals.length == typeSize ty`

These were invisible in obseq1 proofs because `step_RStore`/`step_CStore` take `ty` and `srcTy` as
independent unconstrained variables — no hypothesis requiring `srcTy = ty`. The proof went through
regardless, mirroring the bug.

**Bug 2: `writeThroughPtr` bounds check — matching MIRLite**

Original check: `addr >= base + size` (start-of-write only).

This was initially changed to `addr + vals.length > base + size` (end-of-write), then reverted,
then restored after understanding the full picture.

**Why it was invisible in obseq1:** All compiled `CStore`/`RStore` use freshly allocated pointers
at offset 0. With `offset = 0`, the check `addr >= addr + blockSize layout` is trivially false for
any non-empty type — it fires for no values of `vals`. The `vals` parameter was never constrained
to `vals.length = blockSize layout` because no proof obligation required it.

### Stacked borrows does not subsume bounds checking

Stacked borrows is a **per-address permission model**. It answers "does tag T have permission to
access address A?" — not "is address A within allocation B?" These are orthogonal:

| | Bounds check | Stacked borrows |
|---|---|---|
| Catches | write past end of allocation | write without valid permission |
| OOB into another live allocation | YES | NO (passes if tag valid there) |
| In-bounds write after borrow expired | NO | YES |

Relying on stacked borrows alone to catch OOB is incorrect.

### Correct bounds semantics added to MIRLite

`writeResolvedPlace` had no bounds check — only `M.useMut`. This is correct for the current typed
fragment (type system guarantees `Place.offset + blockSize τ ≤ blockSize σ`), but wrong for future
raw pointer arithmetic where offsets can be arbitrary.

Changes made in `src/obseq2/mirlite_semantics.lean`:
- `PlaceRes` gains `allocBase : Word` and `allocSize : Word`
- `resolveDirectPlace?` populates them from `Place.baseLocal` and `blockSize`
- `writeResolvedPlace` now checks `dst.addr + values.length > dst.allocBase + dst.allocSize`
  before the permission check

Changes made in `src/obseq2/oseair.lean`:
- `writeThroughPtr` checks `addr + vals.length > base + size`
- `RStore`/`CStore` now validate their `ty` field at runtime

Both sides now use the same bounds predicate: the entire write range must fit within the allocation.
For well-typed programs, `PathTo` structure guarantees this statically and the check never fires.
For future raw pointer arithmetic, both sides error on the same condition, preserving simulation.

### WF layer is the next step

Proof order going forward:
1. Target WF predicates (`RegValWF`, `InstrWF`, `CompiledWF`)
2. Step lemmas using WF as preconditions
3. Symbolic execution automation

`CompiledWF` will discharge the end-of-write obligation statically: for every `RStore`/`CStore`
emitted by the compiler, prove `vals.length = typeSize ty` and `offset + typeSize ty ≤ allocSize`.
This is derived from MIRLite's `PathTo` type structure — it is a static obligation, not a runtime
one.

---

## 2026-04-22 — Initial obseq2 Design Notes

### Why obseq2 Uses Types (vs obseq)

obseq tracks types *separately* from the IR, in compiler state (`PlaceMap`). A `Place` is just
`base : Word` + `path : List Word` (raw offsets). A `RExpr` carries no type information.
Correctness proofs must explicitly show that the compiler's type tracking is consistent with
runtime behavior — the bulk of the ~17k line proof burden.

obseq2 bakes types into the IR as dependent type indices. `RExpr Γ τ` is indexed by its result
type at compile time. `ref` always produces `RExpr Γ (PtrL τ)` — Lean's type checker enforces
this, not a proof. This eliminates the "type soundness" portion of the correctness proof: ill-typed
programs are simply unrepresentable.

What still needs proof in obseq2: memory/register correspondence, permission semantics preservation.
The `CompilerInv` scaffolding in `src/obseq2/proof/compiler.lean` sets this up.

### What `Ctx` Is

`Ctx := List LayoutTy` is the type signature of the local variable slot array. `Γ[i]` is the
layout type of local variable `i`. It does not accumulate all types seen in the program — expression
result types (e.g. `PtrL τ` from a `ref`) do not need to appear in `Γ`. Intermediate struct field
types in `PathTo` are also not in `Γ`.

`Γ` is fixed for the whole `Prog Γ`. In a real pipeline you'd need an elaboration pass over the
source that collects all local variable declarations, assigns each an index, and produces a
`Σ Γ : Ctx, Prog Γ`.

### `Place Γ τ` — What It Means

```lean
inductive Place (Γ : Ctx) : LayoutTy → Type where
| local : Local Γ τ → Place Γ τ
| proj  : Place Γ σ → PathTo σ τ → Place Γ τ
```

A type family: `Γ` is a fixed parameter, `LayoutTy` is an index that varies per value.
`Place Γ τ` is "a place in program `Γ` whose content has layout type `τ`".

- `local`: a bare local variable. `Local Γ τ` is an index `i : Fin Γ.length` with proof
  `Γ[i] = τ`. The layout type is statically known.
- `proj`: field projection. Navigates from a base place of type `σ` through a `PathTo σ τ`
  to reach a sub-place of type `τ`.

The type `τ` is a static guarantee — you cannot construct a `Place Γ NatL` that actually
points to a `PtrL` slot.

### `PathTo src dst` — Type-Indexed Field Paths

```lean
inductive PathTo : LayoutTy → LayoutTy → Type where
| nil : PathTo τ τ
| field {tys : List LayoutTy} (idx : Fin tys.length) :
    PathTo (tys.get idx) τ → PathTo (obseq.LayoutTy.TupL tys) τ
```

`PathTo src dst` is a sequence of field projections that navigates from layout type `src` down
to a sub-layout of type `dst`.

- `nil`: the empty path — source and destination are the same type.
- `field idx tail`: pick field `idx` from a tuple `TupL tys`. The field's type is `tys.get idx`,
  and `tail : PathTo (tys.get idx) τ` continues to `dst`.

Example: given `TupL [NatL, TupL [NatL, PtrL NatL]]`, the path to the inner `PtrL NatL`:
```lean
field ⟨1, _⟩ (field ⟨1, _⟩ nil)
-- type: PathTo (TupL [NatL, TupL [NatL, PtrL NatL]]) (PtrL NatL)
```

Two guarantees from the types:
- **Out-of-bounds impossible** — `idx : Fin tys.length` is bounded by the tuple length at compile time.
- **Type mismatch impossible** — `PathTo (TupL [NatL, NatL]) (PtrL NatL)` is uninhabited;
  you cannot construct a path claiming to reach a type that isn't there.

In obseq the equivalent was `path : List Word` — raw offsets with no bounds or type guarantees.

### Three Styles for Pointer Values in Memory

The `MemValue.placeTag` constructor in `mirlite_semantics.lean` stores the pointer value.
Three designs worth comparing:

**Current: symbolic typed place**
```lean
| placeTag {τ : LayoutTy} (place : Place Γ τ) (tag : Tag)
```
Stores the whole symbolic place — "pointer to local #3, field path [1]". Re-resolves the place
at each deref rather than reading a stored address.

Cost: `Γ` propagates into `MemValue → Mem → State` everywhere. The type safety is not
fully constructive — the `if τ' == τ` check at deref is still a runtime check.

Benefit: `MemValSim` in the proof can relate pointer values to source locals by index without
a separate heap correspondence invariant.

**Alternative: type + resolved address**
```lean
(τ : LayoutTy) × Word × Tag
```
No `Γ` anywhere. Cleaner types throughout. The `if τ' == τ` check is still there —
behaviorally identical to current. For proofs you'd need an explicit heap correspondence predicate
"address `w` was allocated for source local `i`", which is essentially what `MemValSim` contains
anyway. The work moves rather than disappears.

**Untyped (obseq style): raw word**
```lean
Word × Tag
```
No type anywhere. Simulation proof must track types externally — this is the path to 17k lines.

**Verdict:** The current design is shaped by proof convenience more than operational clarity.
Storing symbolic places lets the simulation invariant be stated without a separate heap
correspondence predicate, but it pays a real cost (propagating `Γ` into `State`) for a benefit
that is partly illusory (the runtime type check remains). Type + address would be cleaner
operationally with comparable proof overhead.

### Why `State` Carries `Γ`

`State (M : PermissionModel) (Γ : Ctx)` needs `Γ` for one reason: `MemValue.placeTag` stores
`Place Γ τ`, which contains a `Local Γ τ`, which is an index `Fin Γ.length` into the context.
To make that index well-typed, `MemValue` must be parameterized by `Γ`, which propagates up
through `Mem Γ` to `State`.

`Env Γ := Fin Γ.length → Option Binding` also mentions `Γ`, but only uses `Γ.length` — it
could equivalently be a bounded array. The `Γ` in `Env` is a consequence of indexing by
`Local Γ τ`, not an independent reason.

### What Is Standard vs. Novel in This Design

**Standard / textbook:**
- `Ctx` as a list, `Local` as a de Bruijn index with a type proof. Standard intrinsically-typed
  representation used throughout Lean/Agda mechanization literature (e.g. PLFA, Allais et al.
  "A Type and Scope Safe Universe of Syntaxes with Binding").
- Environment-store split. `Env` maps variable IDs to locations; `Mem` maps locations to values.
  Standard two-level memory model from operational semantics textbooks.
- Overall simulation proof structure. Rename maps `ρa`/`ρt`, pointwise memory simulation
  (`MemValSim`), top-level invariant (`CompilerInv`) follow the CompCert (Leroy) proof
  architecture: forward simulation with a lock-step invariant.

**Specific to this design:**
- `Place` as a recursive tree of projections, not a flat (base, offset) list. Allows structural
  induction on places in proofs and defers offset arithmetic to `Place.offset`/`PathTo.offset`.
- `MemValue.placeTag` — storing pointers symbolically as `Place Γ τ` rather than a resolved
  address. Lets `MemValSim` relate pointer cells to source locals by index without a separate
  heap-shape invariant, but propagates `Γ` into `MemValue → Mem → State` and leaves a runtime
  type check at deref.
- Lazy local allocation. `Env` returns `none` until the first direct assignment to a base local.
  Most source semantics allocate all locals upfront. The lazy design matches the target's
  `initLocals` behavior but makes the source semantics slightly unusual.
- Permission model abstracted as a typeclass `PermissionModel`. Source semantics parameterized
  over an arbitrary permission model rather than committing to stacked borrows directly.
  `CompilerInv` specializes to `PermissionModel.stackedBorrows`. Shaped by the goal of keeping
  source semantics reusable across permission models.
