# `ptrOffset` defers UB to the use, so `add` is modelled as `wrapping_add`

Load this when asking whether mirlite is a faithful UB oracle for
pointer arithmetic, or when scoping `ptrOffset` into `CoreRhs`.

[FACT, 2026-09-14] **Four Rust families collapse to one constructor.**
Charon keeps `p.add(n)` as a CALL, and the ingestion recognises eight
paths — `add` / `offset` / `wrapping_add` / `wrapping_offset` ×
`mut_ptr` / `const_ptr` — mapping all of them to the same
`.ptrOffset p delta`, with the delta required to be a literal
("unsupported: runtime pointer offset" otherwise).
→ src/conformance/lowering.lean:560-577

[FACT, 2026-09-14] **Neither machine checks the upper bound.** Both
check only that the new offset is non-negative:

    -- mirlite_semantics.lean:287
    let newOff : Int := (offset : Int) + delta * (blockSize σ : Int)
    if newOff < 0 then .err "pointer offset before the allocation base"

    -- oseair.lean:227 (deltaCells pre-scaled by the compiler)
    let newOff : Int := (pOff : Int) + deltaCells
    if newOff < 0 then RhsResult.Err "pointer offset before the allocation base"

So a pointer may be moved past the end of its allocation, and UB is
deferred to the USE — the read/write bounds-checks it. That is exactly
`wrapping_*` semantics.

[FACT, 2026-09-14] **Hence the model is PERMISSIVE for the checked
forms.** In Rust, `p.add(n)` / `p.offset(n)` are UB at the COMPUTATION
when the result leaves the allocation (one-past-the-end excepted);
`wrapping_*` are not. A program that computes an out-of-bounds pointer
with `add` and never dereferences it is UB in Rust and OK in mirlite.
The direction matters: `compile_correct` is a forward simulation of
SUCCESSFUL mirlite runs, so permissiveness widens the set of covered
programs rather than breaking the theorem — but it means mirlite is not
a faithful UB oracle here, which is what the differential corpus exists
to establish.

[FACT, 2026-09-14] **The differential corpus cannot catch it.** Both
machines make the same choice, so `--osea` agrees by construction (0
mismatches). Only the Miri-verdict comparison could, and no corpus test
exercises it: the two checked uses both dereference immediately
(`basic_aliasing_model__array_casts.rs:11,16` and
`unescaped_static.rs:10`, all `*p.add(1)`), so the use catches what the
computation let through. The one `wrapping_offset` witness
(`transmute-is-no-escape.rs:11`) is correct precisely BECAUSE the model
is lazy — its UB is the later write, via Stacked Borrows, and the test
passes.

[OPEN] Is the permissiveness reachable in a Charon-ingestible program,
and is it worth closing? Closing it means giving `ptrOffset` a bound
argument, or splitting the constructor into checked and wrapping forms —
both of which touch the compiler and oseair, under the audit roots. See
loose-ends/parked.md.

## Why this matters

Two of the three rvalues still outside `CoreRhs` are `ptrOffset` and
`refSlice`. Anyone admitting `ptrOffset` will read its mirlite arm and
should know that the arm is deliberately lazy, not accidentally
incomplete — and that the corpus's silence on the point is absence of
evidence, not evidence of absence.

## See also

- ptrcast-is-a-memcpy-not-a-store.md
- stacked-borrows-does-not-subsume-bounds-checks.md
- one-leaf-per-destination-shape.md
