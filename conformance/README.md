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

## Conformance claim

**obseq3 implements the complete Stacked Borrows rule set.** Every
mechanism of the aliasing model is implemented and witnessed by
conformant tests; the remaining unsupported tests exercise those same
rules through unimplemented *language/std* features (control flow,
containers, threads, drop glue, closures, unions), not through
un-modeled SB rules. Rule → witness map:

| SB mechanism | witnessed by (examples) |
|---|---|
| per-location stacks, granting | illegal_read1/2/4/6; unescaped_static (UB at cell offset 1) |
| write pops above / read disables | illegal_write2/5; illegal_read_despite_exposed1/2 |
| Disabled-not-removed (no group merge) | disable_mut_does_not_merge_srw, interior_mut2 |
| Unique retag (write access) | raw_tracking, illegal_write4 |
| Frozen retag (read access) | illegal_write3, shr_frozen_violation1/2 |
| SRW insert-above-granting, no access | two_raw, mut_shr_then_mut_raw |
| SRW grouping | ref_mut_protector, shared_rw_borrows_are_weak1/2 |
| two-phase reserved borrows | pass_invalid_mut (TwoPhaseMut seams) |
| protectors (strong) | aliasing_mut1-4, invalidate_against_protector1/2/3, illegal_write6 |
| protectors (weak on SRW) | unsafe_cell_invalidate, ref_protector |
| fn-entry retags: args/returns, tuple fields yes, struct fields no | pass/return_invalid_* family, fnentry_invalidation2 |
| retag on reference loads | load_invalid_mut/shr |
| UnsafeCell freeze masks | interior_mut1, mixed_mutability_static, cell_inside_struct |
| deallocation (grant + protector + stack removal) | illegal_dealloc1, invalidate_against_protector3 |
| exposed provenance / wildcards | exposed_only_ro, unescaped_local, *_despite_exposed* |
| box unique retag (weak protector) | box_noalias_violation, box_exclusive_violation1 |
| provenance-preserving ptr ops | transmute-is-no-escape, illegal_read8, array_casts |
| runtime-length (slice) retags | fnentry_invalidation2 |

Documented approximations (each noted where it applies): the box
protector is modeled with the same pop-blocking as strong protectors
(miri's weak protector differs only in permitting deallocation during
the call — unexercised by any reachable test); plain Box-typed
assignments (`let b2 = b`) are not retagged (no test exercises it);
wildcard resolution is determinized (topmost exposed granting item) vs
miri's angelic reading; RefCell shims elide the borrow flag; hoisted
statics start uninitialized; the retag×data-race interaction (threads)
is out of scope.

The single consolidated inventory of everything unimplemented or
approximated lives in `notes/loose-ends/parked.md` (MASTER INVENTORY);
per-test blockers are in `manifest.json`.

## Current score (miri @ PIN)

- fail tests: 56/75 verdict-conformant (line-accurate on 48), 0 xfail,
  19 fail tests unsupported with per-test blockers (40 unsupported
  entries overall incl. pass files/scenarios).
- pass scenarios: 20 supported and clean.
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
Fixed-size arrays are supported (homogeneous tuples; constant indices
resolved through tracked const locals, with bounds-check asserts
const-folded; `[v; N]` repeats desugared; `ptr.add/offset/
wrapping_offset` with constant deltas via `RExpr.ptrOffset`, scaled by
the pointee size, provenance-preserving). Slice references are supported as one-cell fat values whose length is
the rest of their allocation: reborrows of slice data are runtime-length
retags (`RExpr.refSlice` retags `size − offset` cells via the fat
value's tag), unsize coercions are value copies, and
`as_ptr`/`as_mut_ptr` shims reproduce the receiver's fn-entry retag
before the raw data retag (the invalidation fnentry_invalidation2
tests). Named-struct fields are NOT retagged at seams (miri's behavior,
also per that test) — tuples are. Remaining exclusions: slice
indexing/subslicing (runtime bounds), Vec/String, threads, general
closures, drop glue, unions, MaybeUninit, Rc, enums needing control
flow, dynamic arithmetic.

## Local witnesses (`local/`)

`conformance/local/` holds Rust test programs written for THIS project
(not derived from the Miri corpus), lowered through the identical
charon → loader pipeline. Their manifest entries carry
`"provenance": "local-model-reasoned"`: the expected verdict is derived
from the model (and, where noted, from Miri's documented semantics)
but has NOT been verified against a real Miri run. Current entries:

- `local/deref_read_disables_sibling` — the deref-read alignment
  witness: evaluating `*p` reads `p` as an operand, disabling
  `&mut *(&raw mut p)`; motivated the 2026-08-21 mirlite change making
  deref resolution a real SB read (`resolvePlaceAcc`). Follow-up: run
  the pinned Miri on this file and upgrade the provenance.
- `local/zst_ref` — the ZST borrow witness: `&mut ()` is a legal,
  access-free retag (expected `ok`, PASSES end to end, differential
  matched). Writing it found and closed TWO gaps on 2026-08-22: the
  loader dropped unit-aggregate assignments (right for accesses, wrong
  for allocation — now kept as access-free `uninit` inits), and the OSEA
  target's `Rhs.Borrow` bounds check was `addr ≥ base + size`, rejecting
  every zero-sized retag (now the range form `addr + len > base + size`,
  Miri's dereferenceable-for-`len`). The three corpus ZST tests are
  UNSUPPORTED for unrelated reasons, so this is the suite's only ZST
  coverage.
- `local/zst_tail_field` — a ZST field at a struct TAIL: its address is
  one-past-the-end of the enclosing block (`addr = base + size`,
  `len = 0`), the NON-degenerate boundary case (`base ≠ addr`, unlike
  `local/zst_ref` where the ZST stands alone and `size = 0`). Verified to
  have teeth: restoring the pre-2026-08-22 point check
  `addr ≥ base + size` makes it mismatch on its own label, distinct from
  `zst_ref`'s.
- `local/zst_interior_field` — a ZST field in the struct INTERIOR, kept
  live alongside a `&mut` to the cell that follows it. In the model's
  cell layout `(u64, (), u64)` puts `s.1` and `s.2` at the SAME offset
  (the ZST occupies no cell), so a retag of `s.1` that wrongly used
  length 1 would write-access exactly that neighbour and invalidate it.
  NOT a boundary regression test — verified to pass under the older point
  check too, since an interior address is genuinely in bounds.
- `local/nested_proj_borrow` — the nested-projection witness (FIXED
  2026-08-27, same day it was found). Writing `s.1.1` must not invalidate
  a live `&mut s.1.0`; the compiler used to lower a nonzero-offset
  projection by retagging the WHOLE intermediate place, so a nested
  projection's inner step took a write access wider than the source's
  write. The lowering now REASSOCIATES projection chains
  (`.proj (.proj b q) p → .proj b (q.append p)`): one field-sized
  `Borrow`, anchored at the chain root, at the composed offset. GEP
  remains a borrow — BRIDGE 1 still justifies it — it just spans exactly
  the accessed field. Differential matched; pinned in-repo as
  `compile_tests` d26 (teeth verified by reverting the arms). Found by
  attempting the proof, not by testing.
- `local/unassigned_local_addr` (`unsupported: unions`) — a probe of
  whether a local can be borrowed before it is ever written (the lowering
  drops `StorageLive/Dead` and allocates at first assignment). rustc
  rejects the direct form (E0381), so the only legal form goes through
  `MaybeUninit`, a union — outside the surface. The refusal is the
  answer for the union-free fragment: the borrow checker guarantees
  every local is written before it is borrowed. Registered so it lights
  up if unions ever land.
