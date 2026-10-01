# Miri is rustc's MIR interpreter plus a machine

Load this before looking for Miri behaviour in source, and before
comparing the model's memory with Miri's. Many answers live in rustc,
not in the Miri repo.

[FACT, 2026-10-01] **rustc contains a MIR interpreter.** rustc compiles;
it is not an interpreter. But it evaluates `const` items, `static`
initializers, array lengths and `const fn` calls in those positions at
compile time (CTFE, compile-time function evaluation) by INTERPRETING
their MIR. That interpreter is the crate `rustc_const_eval`; its
`interpret/mod.rs` opens with
`//! An interpreter for MIR used in CTFE and by miri`.

[FACT, 2026-10-01] **Miri = that interpreter + `MiriMachine`.** The
interpreter is generic over a `Machine` trait of hooks. CTFE plugs in a
restrictive machine (no heap, no I/O). Miri plugs in its own
(`vendor/miri/src/machine.rs`):

    pub type MiriInterpCx<'tcx> = InterpCx<'tcx, MiriMachine<'tcx>>;
    impl<'tcx> Machine<'tcx> for MiriMachine<'tcx> { ... }

Through the hooks Miri adds heap allocation, concrete integer addresses,
threads, OS/std shims, and the borrow tracker (Stacked/Tree Borrows),
e.g. `retag_ptr_value`, `protect_in_place_function_argument`.

**Where to look** (pin: miri 34d6a7954, rustc 1.99.0-nightly 4667d7556;
rustc sources at `~/.rustup/toolchains/miri/lib/rustlib/rustc-src/rust/
compiler/`):

| question | file |
|---|---|
| statement evaluation, `&raw` retag rule (`place_base_raw`, `is_fake`) | `rustc_const_eval/src/interpret/step.rs` |
| which pointers a retag visits (the field walk) | `rustc_const_eval/src/interpret/validity.rs` (`visit_value` → `check_safe_pointer` → `M::retag_ptr_value`) |
| call arguments, in-place passing | `rustc_const_eval/src/interpret/call.rs` |
| the allocation itself | `rustc_middle/src/mir/interpret/allocation.rs` (+ `allocation/provenance_map.rs`, init mask) |
| SB rules: stacks, items, protectors | `vendor/miri/src/borrow_tracker/stacked_borrows/` |
| hook implementations | `vendor/miri/src/machine.rs`, `borrow_tracker/mod.rs` |
| integer addresses, exposure | `vendor/miri/src/alloc_addresses/mod.rs` |

[FACT, 2026-10-01] **Miri's memory is rustc's, and it is byte-addressed.**
An `Allocation` is `bytes: Box<[u8]>` ("the bytes of a pointer represent
the offset of the pointer"), a `ProvenanceMap` (a whole-pointer entry at
a pointer's first byte, plus per-byte `PointerFrag`s when a pointer is
copied bytewise), a per-byte `InitMask`, and `align`. Miri adds
per-allocation extras: SB keeps one borrow stack per byte RANGE
(`Stacks { stacks: DedupRangeMap<Stack>, .. }`, equal neighbours merged),
and an allocation gets a concrete, aligned base address lazily
(`base_addr`) when something needs it. Arithmetic is 64-bit.

**The model is the same design at cell granularity.** mirlite/oseair
have allocations (base, size), pointers (base, offset, extent, size,
tag) and per-location borrow stacks, but the unit is one CELL per scalar
or pointer, addresses are always concrete (bump allocator), words are
unbounded `Nat`, and there is no alignment, init mask or provenance
fragment. For SB the two coincide unless a program touches part of a
value or the pointer's representation; the tests that do (transmute to
bytes, bytewise pointer copies, address arithmetic) are parked item 12
and tier C of the 2026-10-01 provenance analysis.

See also [[retagging-does-not-follow-references]].
