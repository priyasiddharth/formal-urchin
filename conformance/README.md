# SB conformance suite (obseq3 vs Miri)

Scores the obseq3 Stacked Borrows semantics against Miri's test corpus:
fail tests must be flagged as UB (at the right source line where curated),
pass tests must run clean. Design: `plans/sb_conformance_obseq3.md`.

## Layout

- `PIN` — pinned miri commit, Charon release, rustc toolchain.
- `corpus/` — pristine miri `tests/` at the pinned commit
  (regenerate: `scripts/fetch_corpus.sh`; gitignored).
- `prep/` — curated single-scenario Rust sources, one per supported
  manifest entry. Each carries a header naming the upstream test and
  every rewrite applied.
- `charon/` — ULLBC JSON artifacts (committed, so the Lean suite runs
  without a Rust toolchain; regenerate: `scripts/gen_charon.sh`).
- `tools/` — Charon prebuilt binary (gitignored; release in `PIN`).
- `manifest.json` — the test registry: per test, status
  (`supported` | `unsupported` | `xfail-model`), reason, expected
  verdict (+ optional line), miri's error text (provenance only, never
  matched), and the rewrites applied during prep.

## Running

```
scripts/run_suite.sh              # lake exe sb_conformance ...
scripts/run_suite.sh --record     # print observed verdicts (curation)
scripts/run_suite.sh --filter illegal_read
lake exe sb_conformance --unit ...          # obseq3 unit tests first
lake exe sb_conformance ... --dump <id>     # lowered program of one test
```

Outcomes: `pass`/`fail` (mismatch — missed UB is always a hard failure),
`xfail`/`xpass(!)` for documented model divergences, `unsupported`
(loader rejected, as the manifest expects), `promote(!)` (an
unsupported-marked test now loads — update the manifest).

## Current score (miri @ PIN)

- fail tests: 50/75 verdict-conformant (line-accurate on 42), 0 xfail,
  25 fail tests unsupported with per-test reasons (47 unsupported
  entries overall incl. pass files/scenarios).
- pass scenarios: 19 supported and clean; the rest unsupported with
  reasons (slices/arrays, threads, MaybeUninit, Vec/String, enums with
  control flow).
- Every test that loads agrees with Miri's verdict; there are no
  xfail-model divergences.

Modeled beyond the core: protectors (call-frame protector sets,
fn-entry retags at inline seams, pop-guards in read/write/die/dealloc),
statics (hoisted to uninitialized locals; initializers not run), heap
allocation and deallocation (`Box::new` / `std::alloc` shims →
`alloc`/`dealloc` statements; deallocation requires a live writable tag,
rejects protected items, and removes the borrow stacks), enums
(discriminant word + merged payload cells; variant-guarded seam retags),
struct decls (as tuples), reference-load retags (`*box`-style loads of
refs are retagged, per Miri), and interior mutability: shared/raw-const
retags carry a type-derived UnsafeCell freeze mask (masked cells get
SharedReadWrite with no access), protection is weak on SharedReadWrite
items (popping/deallocating them is allowed), `UnsafeCell`/`Cell`/
`Atomic*` map to cell-marked layouts with pointees inferred from
constructor/accessor call sites, and `UnsafeCell::{new,get}`, `Cell::new`
and `ptr::read` are shimmed. Pointer type-punning casts are
tag-preserving reinterprets (`RExpr.ptrCast`). Transmute is shimmed
(to-raw = reinterpret, to-ref = a real retag, `transmute_copy` = a typed
load); reified fn pointers are tracked statically and indirect calls
resolve to their targets (the `aliasing_mut*` family). Int-to-ptr uses
exposed provenance: ptr-to-int exposes the tag and yields the concrete
address, int-to-ptr resolves the address through the allocation table
into a wildcard pointer whose accesses re-derive authority from the
topmost exposed granting item (a determinization of miri's angelic
wildcard; matches `-Zmiri-permissive-provenance`). Remaining
RefCell is supported via flag-elided shims: `borrow`/`borrow_mut` are
masked/unique reborrows of the value region, `Ref`/`RefMut` guards are
raw-layout values (unprotected at seams — the ref_protector tests'
point), guard `deref`/`deref_mut` are typed loads (the load-retag rule
produces the reborrow), `replace` reads+writes through a masked
reborrow, `mem::drop` is a no-op. Valid for executions without borrow
conflicts — exactly what the corpus exercises; a test relying on a
borrow-flag panic would stay unsupported. The model now also implements
SharedReadWrite *grouping* (writes through an SRW item pop only above
its contiguous SRW run) and Miri's *Disabled* state (reads disable
Uniques in place instead of removing them, so SRW groups never merge —
disable_mut_does_not_merge_srw and interior_mut2 check both sides).
Remaining exclusions: arrays/slices, threads, general closures, drop
glue, unions, MaybeUninit, Rc, Vec/String, enums needing control flow.
