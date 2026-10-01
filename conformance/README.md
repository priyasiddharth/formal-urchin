# SB conformance suite (obseq3 vs Miri)

Scores the obseq3 Stacked Borrows semantics against Miri's test corpus:
fail tests must be flagged as UB (at the right source line where curated),
pass tests must run clean. Design: `plans/sb_conformance_obseq3.md`.

## Layout

- `vendor/miri` — git SUBMODULE on OUR FORK, github.com/priyasiddharth/miri
  branch `formal-urchin`: upstream Miri at `PIN`'s `miri_commit` plus
  `tests/formal-urchin/` (the rewrites that REPLACE std code with
  user-written code — a local `Option` with std's bodies, a local trait
  for a std operator, named `fn`s for closures, `dealloc` for a Box drop).
  The Miri TOOL is built from `miri_commit` itself (a worktree in
  `.tools/miri-src`), so editing those tests never rebuilds Miri or
  misses the CI cache; the bootstrap refuses a fork that differs from
  `miri_commit` anywhere else.
- `vendor/charon` — git submodule; its commit is the Charon pin.
  `scripts/bootstrap_tools.sh` builds both tools into `.tools/` and the
  rustup toolchain `miri` (idempotent; CI caches the result keyed on the
  two pins).
- `corpus` — symlink to `vendor/miri`: `corpus/tests/{pass,fail,…}` is the
  pristine upstream corpus, `corpus/tests/formal-urchin/` our std-replacing
  rewrites.
- `prep/` — the other curated single-scenario Rust sources (rewrites that
  only strip annotations, extract a scenario or drop a std call). Each
  file, here or in the fork, carries a header naming the upstream test and
  every rewrite applied.
- `charon/` — ULLBC JSON artifacts and Miri certificates (committed, so
  the Lean suite runs without a Rust toolchain). Regenerated and checked
  on every CI run by `scripts/live.py`; `--update` rewrites them.
- `manifest.json` — the test registry: per test, status
  (`supported` | `unsupported` | `xfail-model`), reason, expected
  verdict (+ optional line), miri's error text (provenance only, never
  matched), and the rewrites applied during prep.

## Running

```
scripts/run_suite.sh              # lake exe sb_conformance ... (committed artifacts)
scripts/run_suite.sh --record     # print observed verdicts (curation)
scripts/run_suite.sh --filter illegal_read
lake exe sb_conformance --unit ...          # obseq3 unit tests first
lake exe sb_conformance ... --dump <id>     # lowered program of one test
```

### Live run: Miri and Charon from source, every time

```
conformance/scripts/bootstrap_tools.sh      # once (no-op when up to date)
conformance/scripts/live.py                 # everything, ~15 s
conformance/scripts/live.py --filter zst    # a subset
conformance/scripts/live.py --update        # rewrite charon/ from the fresh run
```

For every manifest entry `live.py` runs the pinned Miri on its source
(`prep/`, `local/`, or the unprepped corpus file) and compares the verdict
and UB line with the manifest; regenerates its Charon artifact and, where
the entry has one, its certificate into `.live/charon/`; requires both to
equal the committed files (Charon's `dest_file` and its run-to-run
`short_names` order are ignored); then runs `sb_conformance` plain and
`--osea` on `.live/charon/`. Any disagreement on a SUPPORTED entry fails
the run; unsupported entries are reported only. Per-entry results:
`.live/report.txt`.

Two things the scripts rely on, both found the hard way (2026-09-28):
Miri is invoked as the driver on the file (`run_miri` in
`scripts/tools.sh`), not through a cargo crate per test — cargo-miri
re-checks the sysroot on every call and parallel calls race; and Charon
gets its OWN std sysroot (`CHARON_MIRI_SYSROOTS`) — its driver otherwise
runs `cargo miri setup` on its own toolchain per call, into
`MIRI_SYSROOT` or `~/.cache/miri`, overwriting Miri's with a std from a
different rustc.

Outcomes: `pass`/`fail` (mismatch — missed UB is always a hard failure),
`xfail`/`xpass(!)` for documented model divergences, `unsupported`
(loader rejected, as the manifest expects), `promote(!)` (an
unsupported-marked test now loads — update the manifest).

## Conformance claim

**obseq3 implements the complete Stacked Borrows rule set.** Every
mechanism of the aliasing model is implemented and witnessed by
conformant tests; the remaining unsupported tests exercise those same
rules through unimplemented *language/std* features (slice lengths,
containers, threads, drop glue, closures, unions), not through
un-modeled SB rules. Control flow is no longer a blocker: dynamic
branches and loops are lowered along a Miri-derived CERTIFICATE (see
"Certificates" below). Rule → witness map:

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
| in-place argument/return-place protection (Miri's `protect_in_place_function_argument`) | fail/function_calls/arg_inplace_*, return_pointer_aliasing_read/write |
| typed read of uninitialized memory is UB | fail/function_calls/arg_inplace_observe_after; compile_tests d9b |
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

## Certificates (2026-09-23)

A conformance program is closed and deterministic, so it has exactly one
execution. `<name>.cert.json` (beside the artifact; named by the entry's
`certificate` field) records that execution's branch outcomes as Miri
saw them — per user-function frame instance in entry order, the arm every
`switch` took and whether every `assert` passed — extracted by
`scripts/gen_cert.sh` from a `MIRI_LOG` trace on the pinned toolchain
(`scripts/miri_cert.py`). The lowering follows it: loops unroll, dynamic
`if`/`match` take the recorded arm, and every branch is one of

- **T1 checked statically** — the lowering folds the discriminant and
  Miri's arm must agree ("certificate disagrees with lowering" otherwise);
- **T2 checked at runtime** — the discriminant is a word the program
  computed (a load, an enum's discriminant, a `binOp` result — the same
  word Miri's own `switchInt`/`assert` read), and the check is built
  from existing statements only: `bad := uninit; assignIf d v (bad := 0);
  tmp := copy bad` is UB exactly when the recorded arm is wrong, reported
  as `certificate rejected at line L`, never as a program verdict.

There is no third tier since mirlite gained the word `binOp` rvalue
(2026-09-24): arithmetic the seam cannot fold is EMITTED rather than
replaced by a placeholder, so every recorded branch has a real word to
check.

Coverage as of 2026-09-25 — **every recorded event is checked**: the 24
certificates record 43 branch events between them (6 record none: those
executions are straight-line under Miri), and the lowering consumes and
checks all 43, 25 by folding (T1) and 18 by a runtime check (T2) spread
over 6 entries. A frame whose events are not all consumed is an error
(`unconsumed events`), so the counts cannot silently drift apart. The
report prints the split, lists the runtime-checked entries, and prints
`m unchecked` as the standing witness that no branch is taken on Miri's
word alone.

The runtime tier is the one with teeth against a wrong certificate, and
both of its check forms are demonstrated live rather than assumed: make
the equality check demand `v + 1` and int-to-ptr, aliasing_mut_and_shr
and box_derefer report `certificate rejected`; make the exclusion check
demand membership instead and array_casts, int-to-ptr,
aliasing_mut_and_shr and aliasing_frz_and_shr do. (Flipping a recorded
`arm` instead is usually caught EARLIER — by the T1 cross-check, or by
the wrong arm walking into an abort — which is why the flip test alone
does not exercise the check statements.)

No mirlite/oseair/proof change: the checks are ordinary statements, and
`--osea` attributes their UB like any other. Regenerate with
`scripts/gen_charon.sh <prep>` then `scripts/gen_cert.sh <prep>`; a prep
may carry `// miri-flags: -Zmiri-…` for extra Miri flags.

## Current score (miri @ PIN)

- 109 supported / 31 unsupported of 140 entries (2026-09-27); every
  supported entry agrees with Miri's verdict (and line, where
  specified); `--osea` differential 109 matched. 35 entries run under a
  certificate, with 47 branches checked (27 static, 20 runtime across 8
  entries) and 0 unchecked. What each unsupported entry still needs:
  notes/loose-ends/parked.md, MASTER INVENTORY § A′.
- No xfail-model divergences.

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
tag-preserving reinterprets (`RExpr.ptrCast`). Slices are real: `<[T]>::len` and rustc's
`PtrMetadata` place read lower to mirlite's `sliceLen`, which reads the
fat pointer (copy's read of the cell that holds it — not an access to
the slice data) and yields the extent it carries, in elements
(2026-09-24); and range SUB-slicing (`&s[lo..hi]`, `&a[..]`) lowers the
std `Index`/`array` chain to the two retags it performs — the receiver's
own, then the mint over the narrowed range — with `subSlice` (pure
pointer arithmetic: same allocation, same tag, offset moved by `lo`
elements, extent cut to `hi − lo`) between them (2026-09-25). Transmute is shimmed
(to-raw = reinterpret, to-ref = a real retag, `transmute_copy` = a typed
load); reified fn pointers are tracked statically and indirect calls
resolve to their targets (the `aliasing_mut*` family). Int-to-ptr uses
exposed provenance: ptr-to-int exposes the tag and yields the concrete
address, int-to-ptr resolves the address through the allocation table
(both casts read their source place, which must be in bounds — the
same check every access performs)
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
also per that test) — tuples are. Since 2026-09-23 a pointer value
carries its EXTENT (the slice's length in cells), so a slice retag covers
exactly its slice. Remaining exclusions: slice lengths (`.len()`/metadata)
and range sub-slicing, Vec/String, threads, general closures, drop glue,
unions, MaybeUninit, Rc, runtime VALUES for indices/offsets/sizes.

## Local witnesses (`local/`)

`conformance/local/` holds Rust test programs written for THIS project
(not derived from the Miri corpus), lowered through the identical
charon → loader pipeline. **Every one of them is checked against the
pinned Miri**, not against model reasoning: `scripts/miri_local.sh` runs
each file under the submodule's Miri and prints the verdict
(and the UB line), which is what each entry's `expected` block records.
As of 2026-09-25 all 13 agree, including the one that is UB
(`deref_read_disables_sibling`, line 13 — the same line the model
reports). `scripts/live.py` re-checks them on every CI run; to check one
by hand:

```
conformance/scripts/miri_local.sh              # all of local/
conformance/scripts/miri_local.sh local/zst_ref.rs
```

Current entries:

- `local/deref_read_disables_sibling` — the deref-read alignment
  witness: evaluating `*p` reads `p` as an operand, disabling
  `&mut *(&raw mut p)`; motivated the 2026-08-21 mirlite change making
  deref resolution a real SB read (`resolvePlaceAcc`). Miri agrees:
  UB at line 13, "attempting a read access … tag does not exist in the
  borrow stack", invalidated by the `*p = 5` on the line before.
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
- `local/split_field_borrows` — Rust's split borrows: all three fields of
  a struct mutably borrowed AT ONCE, writes interleaved. Legal Rust and
  OK under SB with no special case — retags are per cell, so disjoint
  field ranges give disjoint stacks. The only suite coverage of borrow
  COEXISTENCE (the corpus aliasing tests all exercise conflicts).
  Companion boundary scenarios are `compile_tests` d28/d29 (a parent
  write is cell-wise: kills only the child covering the written cells) —
  not expressible in safe Rust, since borrowck rejects using a borrow
  across a parent write.
- `local/slice_len_alias` — the slice-length ALIASING witness: taking
  `s.len()` through a shared reborrow of a `&mut [T]` does not disable a
  raw pointer derived from it earlier, because the length is metadata
  read out of the local holding the fat pointer, not an access to the
  slice data. Verified against the pinned Miri (verdict ok).
- `local/slice_len_value` — the slice-length VALUE witness: the program
  branches on `n != 4`, so the certificate's runtime check compares the
  lowering's own computed length against the arm Miri took. Perturbing
  `sliceLen` by one turns it into `certificate rejected at line 16`,
  which is the property being witnessed: the length is the extent's
  element count, not the rest of the allocation. Certificate extracted
  from the pinned Miri.
- `local/enum_payload_read` — the enum-payload read witness: a `Some(r)`
  match binding reads `(o as Some).0`, which is cell 1 of the enum (the
  discriminant is cell 0), and the program writes through `r`. Before
  the 2026-09-28 fix the loader read the discriminant word and rejected
  the program (type mismatch); Miri: ok.
- `local/fn_ptr_moved_arg` — a fn pointer passed as a MOVED argument
  (`apply(&mut v, set_two)`) and called in the callee. Fn pointers are
  tracked statically; before the 2026-09-29 fix the moved argument lost
  its target ("indirect call with unknown target"). Miri: ok.
- `local/box_never_derefed` — Boxes whose pointee type appears only at
  their constructor (`Box::new(5i32)`, `Box::from_raw(p: *mut u64)`),
  never through `*b`. Charon monomorphises each `Box<T>` into an opaque
  decl, so `T` is read off those calls (2026-09-29); before, "Box with
  uninferred pointee". Miri: ok.
- `local/box_into_raw_ok` / `local/box_into_raw_pops_prior_raw` — the
  `Box::into_raw` shim (2026-09-29): the returned pointer is usable (ok),
  and a raw pointer taken from the Box BEFORE `into_raw` is popped by
  `into_raw`'s fn-entry Unique retag of the Box, so writing through it is
  UB at line 13 — Miri's line and reason. A shim that merely copied the
  pointer would report ok there.
- `local/box_leak_ok` / `local/box_leak_pops_prior_raw` — the same pair for
  `Box::leak` (2026-09-29: `into_raw`'s three retags, then `&mut *ptr`):
  ok, and UB at line 11 for a raw pointer taken before `leak`, as Miri.
- `local/ptr_cast_keeps_tag` — `<*T>::cast` / `cast_mut` / `cast_const`
  (2026-09-29) are raw-to-raw casts, which do not retag: casting a pointer
  whose tag was already popped is fine when the result is unused (a
  retagging shim reports UB at line 14 — checked), and the four casts
  chain on a live pointer that stays usable. Miri: ok.
- `local/ptr_write_ok` / `local/ptr_write_popped` — `ptr::write` and
  `<*mut T>::write` (2026-09-29): stores into fresh and existing memory
  (ok), and a write through a popped pointer is UB at line 12, as Miri.
- `local/layout_new_sizes_alloc` — `Layout::new::<T>()` (2026-09-29) is
  `T`'s size, read off the call's monomorphised type argument; `alloc` is
  sized from it, so writing both fields of an allocated pair is in bounds
  only if the size is right (a constant-1 shim gives "write out of bounds"
  at line 13 — checked). Miri: ok.
- `local/std_wrappers_ok` / `local/nonnull_from_shared_write` — the
  pointer-wrapper shims (2026-09-30): `NonNull` (both `From` impls,
  `clone`, `as_ptr`, `cast`, `new_unchecked`, `as_mut`), `ManuallyDrop`
  (`new`, `deref`, `deref_mut`), `size_of` and `UnsafeCell::raw_get` (ok);
  and `NonNull::from(&T)` keeps SharedReadOnly, so a write through it is
  UB at line 12 (a shim taking the `&mut` path fails at line 11 — checked).
- `local/enum_cell_shared_retag` — a shared retag of an `Option<Cell<i32>>`
  keeps a live `&mut` into the payload usable: Miri treats a non-`Freeze`
  multi-variant enum as interior-mutable as a whole, without reading the
  variant (2026-09-30); a frozen enum mask gives false UB at line 18 —
  checked. Miri: ok.
- `local/box_arg_dealloc_weak` — a Box passed to a function may be
  deallocated by the callee (here via `Box::into_raw` + `dealloc`): Miri
  gives a Box a WEAK protector (2026-10-01, `RefKind.BoxMut` +
  `weakProt`). With only strong protectors the model reported
  "deallocating while item … is strongly protected". Miri: ok.
- `local/box_drop_use_after_free` / `local/box_drop_at_callee_end` /
  `local/box_drop_conditional` — Box drop glue (2026-10-01): `drop(b)` and
  a Box moved into a callee really free the allocation (use after free:
  UB at lines 11 / 13, as Miri), and a Box dropped on one branch is not
  dropped again at scope end. The last carries a certificate whose `drop`
  events the lowering must match one for one — a no-op `mem::drop` or an
  extra drop of the moved Box are rejected (checked).
- `local/unassigned_local_addr` (`unsupported: unions`) — a probe of
  whether a local can be borrowed before it is ever written (the lowering
  drops `StorageLive/Dead` and allocates at first assignment). rustc
  rejects the direct form (E0381), so the only legal form goes through
  `MaybeUninit`, a union — outside the surface. The refusal is the
  answer for the union-free fragment: the borrow checker guarantees
  every local is written before it is borrowed. Registered so it lights
  up if unions ever land.
