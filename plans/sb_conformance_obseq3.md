# SB Conformance Suite for formal-urchin via Miri corpus + Charon ingestion (obseq3)

## Context

Goal: honestly call the `~/formal-urchin` Stacked Borrows semantics "SB conformant" by scoring it against Miri's test corpus (fail tests must be flagged UB, pass tests must run clean). **Everything lives in formal-urchin** — `/home/siddharth/seahorn/sb_tests` will be deleted and receives nothing.

Audit findings that shape the plan:

- **formal-urchin is a Lean 4 formalization** (`src/interp/` executable, no SB; `src/obseq/` v1 frozen SB-enforcing; `src/obseq2/` v2 current work). **Executable tests exist but only for the interp variant**: `src/interp/test_mirlight.lean`, `test_oseairlight.lean`, `test_compile.lean` (~19 assert-based tests aggregated by `src/InterpTests.lean`, whose `main` is currently dead — it's a `lean_lib`, not `lean_exe`). The SB-enforcing obseq/obseq2 semantics have zero executable tests.
- **obseq2 IR is tiny and intrinsically typed**: `Stmt = assign | halt`, `RExpr = constInit | copy | ref`, `Prog Γ = List (Stmt Γ)` straight-line, no terminators/calls/Retag statement (permission ops fire eagerly in the evaluator), types = `NatL | PtrL | TupL`.
- **Two SB divergences dominate feasibility**: (1) raw pointers never writable — no SharedReadWrite; `sb_use_mb` rejects `RawPtr` (`src/obseq/sb.lean:596-600`) and `sb_ref Raw` does a mutable parent access even off shared parents (`sb.lean:783`); (2) borrow stacks exist only at allocation base addresses — field access at offset > 0 errors "address not found".
- **No off-the-shelf MIR→Lean translator preserves the memory level** (Aeneas purifies + excludes unsafe; Creusot targets Why3). **Charon** (AeneasVerif rustc driver, MIR→ULLBC/LLBC JSON) is the reusable frontend; the Lean loader must be written.
- **Charon does NOT emit Retag** (verified: no `Retag` variant in ULLBC `StatementKind`; Charon never passes `-Zmir-emit-retag`). Retag points are synthesized during Lean lowering at `Rvalue::Ref`/`RawPtr` — matching the eager model — plus seam retags at inlined call boundaries.
- **Modern Miri corpus counts** (live master 2026-08): `tests/fail/stacked_borrows/` 37 + `tests/fail/both_borrows/` 38 (75 fail total); `tests/pass/stacked_borrows/` 5 + `tests/pass/both_borrows/` 9 (~30 scenarios after splitting bundle files). Local checkout `/home/siddharth/rustc/rust/src/tools/miri` is 2020-vintage but has full history + remote — a `git fetch` suffices.
- Lean toolchain v4.28.0 has `Lean.Data.Json` in core — no new lake dependencies for the loader. `lakefile.lean` is currently untracked (commit it as part of this work).
- `formal-urchin/CLAUDE.md` already declares the better-than-fish notebook (`notes at: notes/`) — no new CLAUDE.md needed anywhere.

## Locked decisions (user-approved)

1. **SB scope: small fixes only** — writable raws + per-cell stacks. No protectors, two-phase, or UnsafeCell; tests needing them are marked unsupported with reasons.
2. **Ingestion: Charon JSON + Lean loader**, with a phased change plan. Lowering in the loader preferred over new interpreter constructs (calls inlined, not added to the IR).
3. **Corpus: fetch modern Miri**, pin the commit.
4. **Create `src/obseq3/`** — the SB fixes and length-parameterized permission model land as a new versioned codebase following the project's v1→v2 pattern, not as forked files inside obseq2. obseq2 (including all five `src/obseq2/proof/*.lean`) stays untouched and green.
5. **All suite data in formal-urchin** (corpus, prep sources, Charon JSON, manifest, scripts). `sb_tests` is temporary and will be deleted.
6. **better-than-fish notes** for this effort go in `formal-urchin/notes/` per existing conventions.

## Plan

### Step 0 — save plan + btf notes (do first)

Save a durable copy of this plan as `formal-urchin/plans/sb_conformance_obseq3.md` (existing convention: `plans/osea_symbolic_exec.md`, `plans/state_helpers_refactor.md`).

Journal entries in `formal-urchin/notes/journal/2026-08/` (markers + file:line citations per `notes/CLAUDE.md`; `[EMP]` would stamp repo commit, these are `[FACT]`/`[OBS]`):
- `[FACT]` v1/v2 SB divergences from real SB (raws never writable; stacks only at alloc base; SB-enforcing semantics untested — only interp mirlight/oseairlight tests exist).
- `[FACT]` ingestion landscape: Aeneas purifies/excludes unsafe, Creusot→Why3; Charon is the reusable frontend; **Charon emits no Retag** — retags must be synthesized at lowering.
- `[OBS 2026-08-14]` local Miri is 2020-vintage; modern corpus counts; core-only classification (~22/51 vintage fail tests core-only).
- Append a `sessions.md` entry (theme: SB conformance audit + obseq3 plan; outputs: this plan + notes).

### Step 1 — conformance data scaffolding + corpus (all under formal-urchin)

```
formal-urchin/conformance/
  PIN                # miri commit + charon version + rust toolchain
  corpus/            # pristine miri tests/ at pinned commit
  prep/              # curated single-scenario .rs files (one per manifest entry)
  charon/            # <test>.ullbc.json artifacts (committed → Lean suite runs without a Rust toolchain)
  manifest.json      # test registry (Step 5)
  scripts/fetch_corpus.sh  preprocess.py  gen_charon.sh  run_suite.sh
```
- Fetch: `git -C /home/siddharth/rustc/rust/src/tools/miri fetch origin master`, pick tip, record in `PIN`, export via `git archive <commit> tests | tar -x -C conformance/corpus`.
- Preprocess per test (manual curation + script support): strip `//@`/`//~ ERROR` (record annotation text in manifest as provenance); split bundle files (`stacked-borrows.rs`, `basic_aliasing_model.rs`) into one scenario per file; rewrite to supported fragment where SB-access-preserving (drop `assert_eq!`; `*p += 1` → `let t = *p; *p = 1;`); header comment `// derived from miri tests/... @ <commit>`; all rewrites listed in manifest.
- Pick ~6 pilot tests first (e.g. `illegal_read1`, `illegal_write2`, `outdated_local`, `unescaped_local`, + 2 pass scenarios).

### Step 2 — Charon install + smoke test

```
charon rustc --ullbc --mir built --format json --monomorphize \
  --dest-file conformance/charon/<test>.ullbc.json -- --edition 2021 conformance/prep/<test>.rs
```
- ULLBC (not LLBC): flat basic blocks, closest to what Miri executes; straight-line-ness trivially checkable. `--mir built`: before optimizations that delete the borrows under test.
- Smoke test on `prep/illegal_read1.rs`: confirm no Retag, `Ref`/`RawPtr` rvalues carry mutability, spans present. Pin Charon release + toolchain in `PIN`.

### Step 3 — Phase A: `src/obseq3/` (new versioned codebase)

Fork obseq2's executable core into `src/obseq3/` (following the v1→v2 precedent; obseq2 and its proofs untouched):
- `types.lean`, `context.lean`, `allocator.lean`, `syntax.lean` — copied from obseq2 (syntax unchanged apart from RefKind reference).
- `common.lean` — `RefKind` gains raw mutability: `Shared | Mut | Raw (mutbl : Bool)`.
- `sb.lean` — executable SB ops (proofs reconstructed later on demand):
  - **Per-cell stacks**: `sb_own ap addr (sz : Nat)` — one fresh tag, push `[Own tag]` at each cell of `[addr, addr+sz)`; `sb_read/sb_write ap addr (len) tag` fold the single-cell op over the range (failing cell's offset in the error); `sb_ref ap addr len tag kind` — one fresh child tag; per cell: parent access then push.
  - **Writable raws**: stack-item `RawPtr (mutbl : Bool) tag`. Raw retag parent access: **write** for raw-mut, **read** for raw-const (fixes v1 `sb_ref Raw` always doing `sb_use_mb`). Write grant set `{Own, MutRef, RawMut}`; raw-const behaves like `Ref`.
  - **Documented divergence (kept)**: no SRW grouping — sibling raw-muts invalidate each other like `MutRef`s. Affected tests → `xfail-model`.
- `permission.lean` — `PermissionModel` with lengths and messages: `own : State → Word → Nat → Except String (State × Tag)`, `read/useMut : State → Word → Nat → Tag → Except String State`, `ref : … → RefKind → Except String (State × Tag)`, `die`; `stackedBorrows` instance over obseq3 sb.
- `mirlite_semantics.lean` — obseq2's semantics with range-based access sites: `allocateBaseAndWrite` passes `blockSize τ` to `own`; `.copy` passes `blockSize τ` to `read`; `.ref` passes the referenced place's `blockSize τ` to `ref`; `writeResolvedPlace` passes `values.length` to `useMut`.
- Unit tests `src/obseq3/tests.lean`, **following the existing `src/interp/test_mirlight.lean` assert-based pattern**, extended with an `expectErr` combinator for negative cases: write-through-child pops siblings above; raw-from-shared is read-only; per-cell: retag field ref at offset 1, write whole tuple through parent, use field ref ⇒ UB.
- Future reconciliation obseq2↔obseq3 (porting proofs onto the fixed model) is parked in `notes/loose-ends/parked.md`.

### Step 4 — Phase B: loader + elaborator (`src/conformance/`, new lake lib)

- **B.1 `DecidableEq LayoutTy`**: needed by the elaborator; nested `List LayoutTy` may defeat `deriving` on 4.28 — hand-write mutual `decEq` (~30 lines) if so.
- **`ullbc_ast.lean`**: untyped mirror of the consumed ULLBC slice (`UCrate/UBody/UStatement/UTerminator/UPlace/URvalue/UTy`) with `FromJson` via core `Lean.Data.Json`. Unknown constructs parse to `UStatement.unsupported (desc)` so the harness reports *which construct* blocked a test.
- **`lowering.lean`** — ULLBC → flat untyped statement list, ordered passes:
  1. Inline all calls in `main` (fresh locals, rename; recursion/indirect → `unsupported(inlining)`).
  2. Linearize: follow gotos; constant `switch` folds, dynamic → unsupported; drop overflow-check `assert` terminators; inlined `return` → assignment to call destination; main's `return` → `halt`.
  3. Drop `storageLive/Dead`, `nop`, `placeMention`, `borrowck` (FakeRead noise from built MIR — not SB accesses in Miri either).
  4. Hoist `static`/`static mut` to fresh locals initialized at pc 0 (divergence noted: real statics have interned allocations).
  5. Retag synthesis: `Rvalue::Ref` → `RExpr.ref .Shared/.Mut`, `Rvalue::RawPtr` → `.ref (.Raw mutbl)`. **B.6 seam retags (default ON)**: for each reference-typed argument/return at an inline seam, synthesize `x' := &mut *x`-style retag — without this, ~14 call-mediated fail tests (`pass_invalid_mut`, `return_invalid_shr`, `aliasing_mut1-4`, …) silently miss their UB.
  - Move lowered as copy (matches Miri for these tests). Tuple constants desugared to per-field `constInit` assignments (no interpreter change). ZST: `TupL []`, `blockSize 0` — verify empty writes don't wedge.
- **`elab.lean`** — untyped → intrinsically typed via `Except String`: `elabCtx`, `elabLocal` (bounds via `Nat.decLt`, type eq via `decEq`), `elabPlace` (field → `PathTo` with decidable `Fin` bounds; `deref` requires inferred `PtrL τ`), `elabStmt`, `elabProg : UProg → Except String ((Γ : Ctx) × Prog Γ)` targeting obseq3 syntax. ~200-300 lines.
- **Golden tests**: parse `illegal_read1.ullbc.json`, assert lowered untyped program equals hand-written expected (`Repr`-derived); elaborate an untyped rendering of obseq2 `examples.lean`'s program, run, compare verdicts.

### Step 5 — harness + manifest + lake wiring

**Manifest entry** (`conformance/manifest.json`):
```json
{ "id": "fail/stacked_borrows/illegal_read1",
  "source": "corpus/tests/fail/stacked_borrows/illegal_read1.rs",
  "prep": "prep/illegal_read1.rs", "artifact": "charon/illegal_read1.ullbc.json",
  "status": "supported",            // | "unsupported" | "xfail-model"
  "reason": null,                   // "protectors" | "interior-mutability" | "dealloc" | "int-to-ptr" | "SRW-grouping" | "inlining" | ...
  "expected": { "verdict": "ub", "stmt": 7 },   // stmt optional, curated via --record
  "miri_error": "<//~ ERROR text, provenance only>",
  "rewrites": ["stripped assert_eq at L14"] }
```

**Harness** (`src/conformance/harness.lean` + `main.lean`, `lean_exe sb_conformance --manifest <path> --charon-dir <path> [--filter s] [--record]`):
- Drives obseq3 `stepStmt` in its own fuel loop, recording `pc` before each step → `Verdict = ok | ub (pc) (msg) | loadError | fuelExhausted`.
- Outcomes: `pass` / `fail` (mismatch — **missed UB reported loudly, never xfail-able without explicit `xfail-model` reason**) / `xfail` (alarms if it unexpectedly passes) / `unsupported` (must match manifest; if it suddenly loads, report "promote me").
- Matching: verdicts always; statement index only where manifest sets `stmt` (populated via `--record` + curation against the miri `//~ ERROR` line). **Never match Miri's message text.**
- Per-bucket summary table; nonzero exit on any `fail`.

**`lakefile.lean`** (commit it): add `lean_lib Obseq3`, `lean_lib Conformance`, `lean_exe sb_conformance`, and `lean_exe interp_tests` (revives the existing dead `InterpTests.main` so the interp mirlight/oseairlight/compile suites run too).

### Step 6 — scale to full corpus

Run pilots end-to-end (vertical slice: `illegal_read1` UB + one pass scenario OK), then generate + curate the full manifest, `--record` stmt indices for the core fail set. Delete `/home/siddharth/seahorn/sb_tests` at the end (it stays empty; nothing to migrate).

## Phase C — explicitly out of scope (documents the conformance claim's exclusions)

- **Calls + protectors** (~12 tests): needs frames/Call/Return or `pushProtector/popProtector` pseudo-instructions at inline seams + protector flags in obseq3 sb. Deferred.
- **UnsafeCell/interior mutability** (~3 fail + ~3 pass): needs cell-range markers in `LayoutTy` and type-driven retag. Deferred.
- **Deallocation/Box** (~7): bump allocator never frees; needs `dealloc`, dangling detection, stack disposal. Deferred.
- **Int↔ptr expose/transmute** (~5), **slices/Vec/threads/misc** (~13): memory model lacks casts/arrays/concurrency. Deferred.

## Expected coverage / conformance claim

~30-33 of 75 modern fail tests and ~12-14 pass scenarios green after Steps 3-6; every excluded test carries a machine-checked `unsupported(reason)` or `xfail-model` marker. Claim template:

> "Core Stacked Borrows conformance: obseq3 agrees with Miri's verdict on N/75 fail tests and K pass scenarios (miri @ `<commit>`), under an eager-retag model without protectors, interior mutability, deallocation, int-to-ptr exposure, or SRW grouping; exclusions enumerated per-test in `manifest.json`."

## Verification (ordered)

1. Charon smoke test on one prep file (no Retag, mutability on Ref/RawPtr, spans present).
2. Loader golden test + elaborator round-trip vs obseq2 `examples.lean`.
3. obseq3 sb unit tests (canonical stack scenarios incl. per-cell offset case), via the revived assert-pattern from `src/interp/test_mirlight.lean` + new `expectErr`.
4. Vertical slice: `illegal_read1` → UB verdict; one pass scenario → ok.
5. Full suite via `conformance/scripts/gen_charon.sh && run_suite.sh`; drive manifest to zero `fail`s. Reproducibility: clean checkout + `PIN` reproduces the identical summary table. `lake build` stays green (obseq2 proofs untouched by design).

## Risks

- **Retag synthesis divergence**: Miri retags every typed reference assignment/arg/return; we retag only at explicit `&`/`&mut`/`&raw` sites + inline seams. A test whose UB hinges on a retag at a plain `let y = x;` reference copy would false-pass — audit the ~14 inlined tests for this during `--record` curation.
- **Charon churn**: pin release + toolchain; commit generated JSON.
- **Built-MIR shape defeats linearization** for some test: fall back per-test to `--mir elaborated`, note in manifest.
- **obseq2↔obseq3 drift** until proofs are reconstructed on obseq3 — accepted cost of zero proof breakage; parked in `notes/loose-ends/parked.md`.
- **Missed-UB direction** is the dangerous failure: harness treats it as hard failure.

## Critical files

- New: `formal-urchin/src/obseq3/{types,context,allocator,common,syntax,sb,permission,mirlite_semantics,tests}.lean`; `formal-urchin/src/conformance/{ullbc_ast,lowering,elab,harness,main,test_loader}.lean`; `formal-urchin/conformance/{PIN,manifest.json,scripts/*,prep/*,charon/*,corpus/}`; btf notes in `formal-urchin/notes/journal/2026-08/`.
- Modified: `formal-urchin/lakefile.lean` (commit + Obseq3/Conformance/sb_conformance/interp_tests targets), `formal-urchin/notes/sessions.md`, `formal-urchin/notes/loose-ends/parked.md`.
- Untouched by design: all of `src/obseq/`, all of `src/obseq2/` (incl. `proof/`), `src/interp/` sources (only re-wired as an exe).
- Deleted at end: `/home/siddharth/seahorn/sb_tests`.
