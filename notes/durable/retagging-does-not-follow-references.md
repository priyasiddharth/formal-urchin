# Retagging walks a value's fields, never through a pointer

Load this before deciding whether a type's references get retagged (the
lowering's `containsRef` / `emitSeamCopy`), before citing a Miri test
for a retag rule, or when a test passes a struct, tuple or reference
into a call.

[FACT, 2026-10-01] **A retag covers every reference stored IN the value
being retagged, and nothing reachable THROUGH one.** For a function
argument, a return value or a typed load, Miri retags each pointer that
is part of the value: the value itself if it is a reference or Box, and
the fields of a tuple, struct or enum payload, recursively, however
deeply nested. It does not follow a reference to retag the references
stored in the memory it points to.

    fn by_value(n: Newtype)      { .. }  // n.0 IS retagged (+ protected)
    fn by_ref(t: &mut Thing)     { .. }  // t is retagged; t.sli is NOT

Tuples and named structs are the same thing for this rule. Since
2026-10-01 the loader parses both to `UTy.tup`; `UTy.structT` and its
"struct fields are not retagged" rule are gone.

[FACT, 2026-10-01] **Where this lives at the pin** (miri 34d6a7954,
rustc 1.99.0-nightly 4667d7556). The walk is no longer Miri's own
visitor. It is rustc's validity visitor
(`rustc_const_eval/src/interpret/validity.rs`): `visit_value` walks the
value's fields (`walk_value`), and at each pointer `check_safe_pointer`
calls the machine hook `M::retag_ptr_value` (Miri: `machine.rs` →
`borrow_tracker::retag_ptr_value` → `sb_retag_ptr_value`). Going into a
pointee happens only through `ref_tracking`, i.e. recursive validation.
Miri turns that on only for `ValidationMode::Deep`
(`enforce_validity_recursively`, `-Zmiri-recursive-validation`), which
is off by default and is not used by the corpus.

[FACT, 2026-10-01] **The two tests that pin it:**
- `fail/both_borrows/newtype_retagging` (and `_pair_`, where the struct
  is passed as a ScalarPair): a `&mut i32` inside a struct passed BY
  VALUE is retagged and protected for the call, so freeing its pointee
  during the call is UB.
- `fail/stacked_borrows/fnentry_invalidation2`: `inner(t: &mut Thing)`
  retags `t` only. `t.sli`, the `&mut [i32]` inside the pointed-to
  `Thing`, is untouched at entry, and `main`'s `ptr` into the array dies
  later, at `t.sli.as_mut_ptr()`, whose reborrow of `&mut *t.sli` writes
  to the array. The test asserts Miri blames that call, not `inner`.

**The mistake this records.** From 2026-08-14 to 2026-10-01 the model
cited fnentry_invalidation2 for "Miri does not retag named-struct
fields". That test says nothing about by-value structs. The rule made
the model report `ok` on both newtype tests, where Miri reports UB
(commit 094db2e; parked item m). When a test is cited for a retag rule,
first check whether the struct is the argument itself or the target of
a reference argument.
