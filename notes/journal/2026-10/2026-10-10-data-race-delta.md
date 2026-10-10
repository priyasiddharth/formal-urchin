# 2026-10-10 — What data races would cost on top of bytes + Stacked Borrows (research, not started)

## Context
The user asked what it would take for the model to also catch data
races, and to note the answer for future exploration. Nothing was
implemented. A background research agent produced the design below;
the facts about the corpus and the code were checked at ec1afe2.

## The targets
[FACT] 3 of the 17 unsupported entries are data races, all with
`-Zmiri-deterministic-concurrency` (Miri's schedule is fixed):
`fail/stacked_borrows/retag_data_race_read`,
`fail/stacked_borrows/retag_data_race_protected_read`,
`fail/both_borrows/retag_data_race_write`. They test one rule: a RETAG
is a read for the race detector (`retag_data_race_read`: thread 1's
`&*p` races thread 2's `*p = 5`).
[FACT] `fail/both_borrows/box-custom-alloc-aliasing` spawns no thread
(and has no deterministic-concurrency flag); its allocator calls
`thread::current().id()`. That needs a shim, not a race model.

## The smallest delta [HYP]: sequential semantics, Miri's schedule in the certificate
1. Certificate. The fork already hooks `step_current_thread`
   (`before_step`/`after_step`, src/concurrency/scheduler.rs). Add a
   `thread` field to events plus `spawn{child}`/`join{child}`;
   `miri_cert.py` keeps one frame cursor per thread; the lowering emits
   each thread's statements in Miri's order, cutting only at statement
   boundaries. (The fork stays observation-only.)
2. mirlite: `onThread t` (later accesses are by `t`); `sync t₁ → t₂`
   (happens-before from spawn/join, later release/acquire); real atomic
   load/store/RMW with an ordering. Today `Atomic*` is a cell around a
   word (`parseTy`, src/conformance/ullbc_ast.lean ~l.946).
3. A race model beside `PermissionModel`, same access interface
   (read/useMut/ref/dealloc): per-thread vector clocks; per byte the
   last write (thread, timestamp, atomic?, size) and a read clock. `ref`
   counts as a read (the three tests), `dealloc` as a write. UB iff
   either model errors. No weak-memory emulation in v1.
4. The one change inside Stacked Borrows: `protFrames` (src/obseq3/sb.lean
   l.167) becomes per-thread, because interleaved threads break the
   LIFO order of push/pop frame.

## Proof impact [HYP]
- Interleaving only between statements keeps the compiler theorem
  sequential: each statement's OSEA-IR is contiguous, no atomicity
  argument. The relation adds "race state equal" (clocks hold no tags,
  so plain equality, unlike `PermSim`).
- New obligation: the compiler's EXTRA accesses (route-tag retags; the
  `binOp` fold's `readPlaces` reads) add no race. Each is a same-thread
  read of bytes the source statement itself accesses, with write-ness
  no greater, so it races only where the source access already does.
  Temporaries are fresh allocations.
- Die elision: `Die` touches only borrow stacks, never race state.

## Cost [HYP]
Small: fork events and lowering (certificate machinery + a thread id).
Moderate: the race model in Lean. Wide: per-thread protectors touch
every `PermSim`/`PermSub` frame lemma. The real new proof: "extra
accesses add no races".

## What would force a bigger design
- Weak memory: a load may return an older store, so the certificate
  must record which store each atomic load read.
- A theorem for ALL schedules, not Miri's one: real threads in the
  semantics and context switches inside compiled code (an atomicity or
  reordering argument). The schedule certificate avoids both.
