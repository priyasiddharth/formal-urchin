# Miri's in-place passing transcribed; uninit reads are UB; the corpus gap

[OBS 2026-09-21] Scanned Miri's whole `tests/` tree at the pinned commit
for `//@revisions: … stack …` (93 files) and for SB error annotations
outside the four corpus directories. Inside the four: all 47 in the
manifest. Outside: the in-place family in `fail/function_calls` (8 with
`observe_after`, which has no revision line and runs under SB by
default), `fail/box-cell-alias`, one Tree-Borrows-only test, and 38
general pass tests (2 lower and pass; 35 rejected for std/language
features; 1 does not compile under Charon). The corpus was scoped by
directory name, and Miri files the in-place tests under call semantics
because the mechanism arrived as a call-ABI feature; their revision
lines and error texts say Stacked Borrows.

[FACT 2026-09-21, verified against b719fb6+] All seven lowerable
in-place tests missed UB under the pre-change model (ours ok, Miri ub).
After transcribing Miri — protected reborrow + uninit at moved call
arguments and at the return place, and typed reads of uninit being UB —
all seven pass. See durable/move-is-a-temporary-unique-reborrow.md.

[FACT 2026-09-21] The harness's `xfail-model` rule (harness.lean
`judge`): the manifest always carries Miri's verdict; `supported`
scores a mismatch as `fail`, `xfail-model` scores a mismatch as `xfail`
and a match as `xpass` (a failure, so stale exceptions get recurated).
Direction is not recorded structurally; a `divergence: stricter|laxer`
field would make "missed UB" exceptions visible in the summary.

[FACT 2026-09-21] Why "clear the whole stack" and "dealloc then alloc
again" are not a moved-from marker (user questions, answered in the
conversation): removing the owner breaks reinitialisation of a
moved-from local, which is safe Rust; an empty stack has forgotten its
root, and remembering it is "owner stays + a moved flag", whose only
existing form is uninit memory; a fresh block reads as undef, which
mirlite treated as a value, so the observe-after read still went
through. Miri's deinit is a memory fact, orthogonal to the stacks.

[OBS 2026-09-21] rustc routes every named place through a temporary at
a call boundary (`_4 = move _1; consume(move _4)` in, `_3 = make(); _1 =
move _3` out), so Miri's in-place mechanisms touch only places the
program cannot name; the return-place case a raw pointer into the
destination local is UB on both machines for an ordinary reason (the
assignment `_1 = move _3` is a write through the owner).

## See also

- move-is-a-temporary-unique-reborrow.md
- move-deinits-its-source-at-calls.md
- 2026-09-20-move-rvalue.md
