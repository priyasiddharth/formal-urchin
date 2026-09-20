# `move` deinits its source at a call, and only there

Load this before touching `Operand::Move` in the seam, before proposing
a `move` rvalue for mirlite, or when a test moves a local into a call
and later touches it through a raw pointer.

[FACT, 2026-09-19] **A `move` operand in an ASSIGNMENT is a copy.**
rustc's interpreter (`rustc_const_eval/src/interpret/operand.rs`,
`eval_operand`) has one arm for both:
`&Copy(place) | &Move(place) => self.eval_place_to_op(place, layout)`,
preceded by `// FIXME: do some more logic on `move` to invalidate the
old location`. Stacked Borrows sees a typed read of the source and
nothing else; the source keeps its bytes and its stacks. The seam has
always lowered `.use (.move p)` as `.use (.copy p)` (lowering.lean,
`emitAssign`).

[FACT, 2026-09-19] **A `move` operand as a CALL ARGUMENT deinits its
source, in Miri.** `eval_fn_call_argument` turns `Move(place)` of an
in-memory place into `FnArg::InPlace`, documented as "destroy the value
originally stored at that place and make the place inaccessible for the
duration of the function call". After the callee's local is filled,
Miri runs `protect_in_place_function_argument` (miri `src/machine.rs`):

    // If we have a borrow tracker, we also have it set up protection so that all reads *and
    // writes* during this call are insta-UB.
    let protected_place = ecx.protect_place(place)?;
    // We do need to write `uninit` so that even after the call ends, the former contents of
    // this place cannot be observed any more. ...
    ecx.write_uninit(&protected_place)?;
    // Now we throw away the protected place, ensuring its tag is never used again.

A fresh Unique reborrow of the source with a protector (pops every item
above the owner), a write of uninit through it (the cells become
undefined), and the tag is dropped (one dead protected item stays on
top). Locals that are immediates (never in memory) are copied instead —
unobservable, they have no stacks. Intrinsics and foreign functions
(shims) get none of this: real MIR frames only.

[FACT, 2026-09-19] **Why Miri does the two-step and not just the
deinit.** In-place passing licenses codegen to pass a POINTER to the
caller's slot instead of copying, so the callee's argument aliases the
slot for the call. For that to be sound every other access to the slot
during the call must be UB. Uninit alone forbids reads (a typed read of
uninit is UB) but not writes — writing to uninitialized memory is legal
— and a write would land in the callee's live argument. The protected
item on TOP of the stack is the guard: after the retag nothing else is
above the owner, so any other access comes through the owner or a later
child of it and pops or disables the protected item, both UB while the
protector lives. Protecting the owner's own item would not work: an
access through a new child never pops the owner. The write goes through
the new tag for convenience (it checks the place is real memory) and,
for Tree Borrows, to activate the tag.

[SUPERSEDED → move-is-a-temporary-unique-reborrow.md, 2026-09-20] The
paragraph below and the 2026-09-19 journal entry predicted that a Rust
program moving a local into a call and then reading it through an older
raw pointer would be a pass-vs-Miri mismatch until the seam deinit'd
the source. Real Miri says OK on exactly that program
(local/move_arg_via_temp_spares_raw). Reason: rustc moves a NAMED place
into a call through a TEMPORARY — `_4 = move _1; consume(move _4)` —
and the assignment move is a copy, so Miri's in-place protection hits
`_4`, which nothing else can observe; `_1` keeps its bytes and its
stacks. Miri's own in-place tests use custom MIR for this reason. The
seam's deinit (and now `move`) therefore acts on the temporary, and the
corpus was verdict-neutral for a second reason, not the one I gave.
*Why I was misled:* I reasoned from the interpreter's argument-passing
code without looking at the MIR rustc emits for the call.

[FACT, 2026-09-19] **The seam does the one-step version.** It COPIES the
argument into a fresh callee local, so nothing aliases the caller's slot
and the guard has nothing to guard. `emitSeamBind` therefore emits, after
binding a `.move p` argument at an INLINED call, `p := uninit` — one
write through `p`'s owning tag, which pops every borrow above the owner
(what the retag did) and leaves the cells undefined (what the write
did). What it does not reject that Miri does: an access to the
moved-from slot DURING the call through its owning tag, reachable by
the inlined callee only via an exposed wildcard pointer. Everything
Miri rejects through a real pointer we reject too, since those tags are
popped. No mirlite or proof change: `uninit` is in `CoreRhs`.
→ src/conformance/lowering.lean `emitSeamBind`

[FACT, 2026-09-19] **Decision: `move` is NOT a mirlite surface
operation.** (a) A `move` rvalue whose semantics is copy would mislead
— rustc itself has not decided what a moved-from assignment source
means (the FIXME above). (b) A `move` rvalue with the deinit built in
writes its SOURCE during the rvalue phase, which breaks the value
package's "the pre-phase does not touch memory" (`sR.mem = sA.mem` in
`ValuePkg`) — a new leaf family, not a new member of the read-then-store
one. (c) A two-assign statement `move dst src := dst := copy src; src :=
uninit` needs the assign leaves to return `InvAt` at an intermediate
state rather than `CompilerInv`, a refactor of every leaf's tail. The
seam emission costs none of that and puts the semantics where Miri gives
it meaning: the call site.

[SUPERSEDED → move-is-a-temporary-unique-reborrow.md, 2026-09-20] The
one-step version lasted a day. The user dropped the uninit write ("don't
write uninit in memory for move; can we just clear sb") and asked for
`move` as a mirlite rvalue; the deinit paragraph above describes the
seam of 2026-09-19 only.

## Not modelled

- Miri also protects the RETURN place for in-place return passing
  ("Protect return place for in-place return value passing"). The seam
  copies the return value out of callee local 0; no aliasing, nothing
  guarded.
- `Box::new(v)` is a real MIR function in std, so Miri deinits `v`; the
  seam shims it and does not. A test that moves `v` into a `Box` and
  reads `v` through an older raw pointer would diverge (ok here, UB in
  Miri).

## See also

- protectors-and-the-charon-inlining-seam.md
- assignif-reads-its-discriminant.md
- already-rejected-design-alternatives.md
