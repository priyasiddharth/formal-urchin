# Unsupported Miri tests, and why

[EMP] Verified against f79e0fb (branch `conformance-drop-in-place`),
2026-10-01. Re-stamp when the manifest or the loader changes. The counts
and reasons below are what `sb_conformance --record` and the 2026-10-01
probe of the outside `pass` tests OBSERVED; `[HYP]` marks a reason read off
the source, not run.

## Denominator

137 Miri test files are Stacked-Borrows-relevant at the pin (miri
34d6a7954): the 89 files of `tests/{fail,pass}/{stacked,both}_borrows/`,
10 `fail` tests elsewhere whose `.stack.stderr` names an SB violation, and
38 `pass` tests elsewhere that upstream runs under both aliasing models
(`//@revisions: stack tree`). Tree Borrows (`*/tree_borrows/`, 76 files) is
a different model and out of scope.

| group | files | agree with Miri | partly (scenarios) | unsupported |
|---|---|---|---|---|
| SB directories | 89 | 70 | 4 (27 scenarios) | 15 |
| `fail` elsewhere | 10 | 7 | — | 3 |
| `pass` elsewhere | 38 | 6 | — | 32 |
| **total** | **137** | **83** | **4** | **50** |

No known disagreement among the supported ones (corpus 142/0, `--osea`
142, live 142/142). One known false UB sits in an unsupported scenario
(`raw_ref_to_part`, below).

## A. SB directories — 15 files + 7 scenarios

Grouped by blocker. "parked" = `notes/loose-ends/parked.md` item; "step" =
the roadmap in the 2026-10-01 plan.

**Threads + the data-race detector (3) — out of scope.** A retag counts as
an access for Miri's vector-clock race detector; the model has no
scheduler and no race detector (a different checker from SB).
`fail/stacked_borrows/retag_data_race_read`, `…_protected_read`,
`fail/both_borrows/retag_data_race_write`.

**std containers: Vec / String (5) — parked w, step 8.** A heap container
model (3-word header, push with protected fn-entry retag + realloc, len,
as_ptr, `vec!`, drop → dealloc). `fail/both_borrows/buggy_as_mut_slice`;
`pass/both_borrows/2phase` (the whole file: `two_phase2/3`,
`two_phase_raw`, `two_phase_overlapping1`; `two_phase1` and
`two_phase_overlapping2` are split out and pass);
`basic_aliasing_model::drop_after_sharing` (String),
`::disjoint_mutable_subborrows` (String/Vec);
`pass/both_borrows/interior_mutability` as a whole file (its 10 scenarios
pass split out; the remainder, `unsafe_cell_2phase`, is Vec).

**Slices from raw parts with a runtime length (1) — parked r, step 7.**
`fail/both_borrows/buggy_split_at_mut`: `from_raw_parts_mut(ptr.add(mid),
len - mid)` needs a runtime pointer offset and a runtime extent; its
`assert`/branch is certifiable since 2026-09-23 (observed: "dynamic branch
without a certificate" is the first wall only because the entry has no
certificate yet).

**User `impl Drop` glue (1) — parked q step 2, step 4.**
`fail/both_borrows/drop_in_place_protector`: the UB is inside the user's
`drop`; the loader rejects crates with a local `impl Drop` since
2026-10-01 rather than skip the destructor. Needs Charon
`--precise-drops` (per-type `drop_glue` bodies) and inlining the glue at
`Drop` terminators and in the `drop_in_place` shim; the flag changes every
artifact's MIR level.

**`&raw` through a raw-pointer base must not retag (1) — parked n, step 2.**
`basic_aliasing_model::raw_ref_to_part`: loads with a certificate and
reports a FALSE UB (observed 2026-10-01): `addr_of_mut!((*whole).part)`
mints a tag over `part` only; Miri keeps `whole`'s tag (rustc `step.rs`,
`place_base_raw`), so the later `&mut *(part as *mut Whole)` is fine.

**Zero-sized retags do no access (1) — parked o, step 3.**
`basic_aliasing_model::zst`: `&mut *` of a dangling / out-of-bounds /
deallocated `*mut ()` and a zero-sized protector that must not block
`dealloc`; also `ptr::without_provenance_mut` (bodyless).

**Stale reason — passes as-is (1) — step 1.**
`basic_aliasing_model::box_into_raw_allows_interior_mutable_alias`: the
manifest says "Box + Cell"; the `Box::into_raw`, `Cell::set` and `.cast`
shims have since landed and the scenario runs `ok` (observed 2026-10-01).
Needs only the prep + manifest entry.

**`dyn` / vtables (1) — parked v.** `basic_aliasing_model::wide_raw_ptr_in_tuple`:
unsize-to-`dyn` fat pointers and dyn dispatch.

**`!Unpin` / `UnsafePinned` retag rule (2) — parked s.**
`basic_aliasing_model::not_unpin_not_protected` (also closures and fn
pointers), `pass/both_borrows/unsafe_pinned`: a `&mut` to a non-`Unpin`
type gets no protector / SRW treatment.

**`MaybeUninit` / unions (3) — parked t (+u).**
`pass/both_borrows/maybe_dangling` (`MaybeDangling` wrapper: inner
reference not retagged; `boxy` also needs q),
`pass/both_borrows/smallvec` (union-backed inline storage),
`interior_mutability::into_interior_mutability` (part of the whole-file
entry above).

**Custom allocator + trait objects (1) — heaviest, after w + q.**
`fail/both_borrows/box-custom-alloc-aliasing`: allocator-generic
`Box`/`Vec` calling user `allocate`/`deallocate`.

**Language features Charon or the loader lacks (4).**
`pass/both_borrows/c_variadics` (parked k: `VaList`, variadic arity);
`pass/stacked_borrows/coroutine-self-referential` (Charon: "Coroutines
are not supported"); `pass/stacked_borrows/zst-field-retagging-terminates`
(closures + a recursion-depth stress); `pass/stacked_borrows/stack-printing`
(the test IS Miri's printed stacks — not a semantics test).

**Loop budget (1) — step 1 [HYP].** `pass/stacked_borrows/unknown-bottom-gc`:
manifest says "int-to-ptr + GC internals", but the source is an in-bounds
`expose_provenance`/`with_exposed_provenance` round trip (supported) and a
`for _ in 0..1024` loop; the certificate loop budget is the likely wall.
Not re-run since the budget was set.

## B. `fail` tests elsewhere — 3

- `fail/function_calls/return_pointer_aliasing_write_tail_call`: `become`
  — the pinned Charon rejects the terminator ("Unsupported terminator:
  tailcall"). Out of scope until Charon translates it.
- `fail/extern-type-field-offset`: `extern type` (unsized, unknown
  layout). Never added. [HYP] loader: no layout for an extern type.
- `fail/async-shared-mutable`: an `async` block (coroutine). Charon cannot
  translate coroutines. Never added.

## C. `pass` tests elsewhere — 32 of 38

All 38 were run 2026-10-01: Miri `ok` on 38/38 (the `vec` "panic" is a
`catch_unwind` the test performs), Charon translated 37/38. Six are now
supported (`associated-const`, `disable-alignment-check`,
`disjoint-array-accesses`, `issue-miri-3473`, `many_shr_bor`,
`memleak_ignored`). The rest, by the FIRST wall the loader hit (a test may
have more behind it):

**std containers / iterators (14) — parked w and beyond.**
`vec`, `assume_bug` (`vec![()].into_iter()`), `vecdeque`, `hashmap`,
`btreemap`, `linked-list`, `rc`, `box-custom-alloc` (also an allocator
trait), `send-is-not-static-par-for` (`iter_mut`), `future-self-referential`
(also async), `concurrency/sync` (`Mutex::new` etc. — also threads),
`cast-rfc0401-vtable-kinds` (indirect call through a vtable — `dyn`),
`dyn-arbitrary-self` (`Pin`, `dyn`), `unsized` (unsized fn params, `str`
literals, custom MIR). None of these is reachable without a container
model; several need `dyn` (parked v) or `Pin`/async on top.

**Integer addresses without provenance (7) — parked 12; NOT planned.**
`transmute_ptr`, `ptr_int_transmute`, `ptr_int_casts`, `ptr_int_from_exposed`,
`provenance`, `option_box_transmute_ptr`, `strange_references`. Per
scenario (21 in all): 3 need a provenance-stripping `addr` rvalue (A) and
`with_addr` (B); 5 need wildcard provenance resolved at the access (E, the
one SB-genuine item: `Stacks.exposed_tags`); 8 need byte-level pointer
representation (C1: partial reads of a pointer, bytewise copies with
provenance fragments, 64-bit wrap — measured cost in
`journal/2026-10/2026-10-01-byte-probe.md`); the rest need niche layouts
(F) or `dyn`/fn-pointer addresses (G). `extern_types` (`without_provenance`
+ `extern type`) belongs here too. Decision 2026-10-01: no byte model
before the paper; these stay unsupported.

**User `impl Drop` (4) — parked q step 2.** `async-drop`, `coroutine`,
`threadleak_ignored`, `tls_macro_drop`: the `impl Drop` guard is the
first wall; behind it async/coroutines (Charon), threads, TLS.

**Threads (3) — out of scope.** `concurrency/channels` (`mpsc::channel`),
`tls/tls_static` (`thread::spawn`), `shims/available-parallelism`.

**Async / coroutines (2) — Charon.** `async-niche-aliasing` (`main` has no
body after translation), `future-self-referential` (counted above).

**`Atomic*` surface (1).** `atomic`: 37 bodyless std functions
(`store`/`load`/`fetch_*`/`compare_exchange`/fences…); each is a one-word
cell access, but the test also uses `Vec`, iterators and `Result`. Not
worth a shim table without the container model.

**Charon front end (1).** `slices`: uses the unstable library feature
`layout_for_ptr`; the pinned Charon's rustc refuses to compile it.

## What would move the number

Steps 1–5 of the plan (split-outs, `&raw` rule, zero-sized retags, Drop
glue, `MaybeUninit`) are loader/lowering work plus one small model rule
and flip ≈ 6 SB-directory entries and remove the first wall for 4 outside
files. The container model (w) is the single largest unlock (≈ 8 files +
scenarios). Threads, coroutines, tail calls, stack-printing (10 files) are
permanently out of scope for an SB model fed by this Charon.
