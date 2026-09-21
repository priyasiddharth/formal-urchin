# `move` is a temporary unique reborrow of its source

Load this before touching `RExpr.move`, the seam's moved-argument
binding, or the ref leaf's `RefSrcShape`; and before claiming what a
`move` does to borrow stacks.

[FACT, 2026-09-20] **`dst := move src` = copy's value, the source's
borrow stacks CLEARED, the bytes left alone.** mirlite (`evalRExpr`,
the `.move` arm): resolve `src` for access, the bounds check, then
`M.ref … Mut false []` — mint a temporary unique child of the place's
resolved tag, which pops every item above it — then `M.read` through
the child, then `M.die` the child. Three permission events, no memory
event. The compiled code is the same three events after the source
chain's lowering: `Borrow(Mut) tmp; Load v ← tmp; Die tmp`
(`compileRExprPreChecked`, the `.move` arm: `placeToBorrowRegChecked
Mut false [] src`, i.e. the lowering `&mut src` gets, whose own cleanup
is the `Die`), and the assign then stores `v`. Golden g13.
→ src/obseq3/mirlite_semantics.lean; src/obseq3/compile.lean

[FACT, 2026-09-20] **"Clear" means: afterwards the stack of every cell
of `src` is what it was below and including the item `src` resolves
through.** For a local that is the owner's `Own` item alone. A borrow
of the moved place does not survive (differential d93 raw, d94 `&mut`,
d97 field); a borrow of a sibling field does (d96); the owner still
reads its bytes (d95). This is Miri's in-place argument passing
(move-deinits-its-source-at-calls.md) minus the protector — nothing
aliases the source in our model, the seam copies — and minus the uninit
write, dropped at the user's request.

[FACT, 2026-09-20] **Why lockstep (ref/read/die on BOTH machines) and
not a bare write access on the source side.** A mirlite `useMut`
through the owner has the same final stacks as the bracket, but
relating it to the target's `Borrow; Load; Die` needs a keystone
argument (ref-Mut-then-die cancels to write; the read through a
just-minted top item is a no-op). Minting on both sides instead makes
the proof three existing transports — `sb_ref_respects_PermSim` via the
ref mother lemma `ref_chainsrc_borrow`, `sb_read_respects_PermSim`, and
a new `sb_die_respects_PermSim` (permsim_transport.lean; the first time
mirlite kills a tag) — and, because no memory changes, the result is an
ordinary value package: every destination leaf takes it unchanged.
proof/ref.lean: `RefSrcShape` gained `movePreRun`/`movePreValue` (the
move's code at each ref source shape), `move_valuePkg_chain`,
`assignStep_move`, `CompilerInv_step_move`; `CoreRhs` admits `move`.
Also new and generic: `compileAssignChecked_congr_pre` — a statement's
lowering depends on its rvalue only through the pre-phase's run, store
and post-cleanup, so one lemma replaces the six per-destination
flatten congruences copy and ref each carry.

[SUPERSEDED → next paragraph, 2026-09-20 later] The seam paragraph
below described the first landing (call arguments only). The user's
decision the same day: EVERY `Move` operand clears — "the sb for the
src should be zero so the test should fail mirlite also".

[SUPERSEDED → next paragraph, 2026-09-21] "Every `Move` operand
clears" lasted a day. The user's final call, after seeing real Miri
accept the raw-read programs: "let's follow what Miri does — add
protector". Assignment moves are copies again.

[FACT, 2026-09-21] **The seam transcribes Miri's in-place passing, and
a typed read of uninitialized memory is UB.** Three pieces, all
verdict-level, no proof cost for the first two:
1. `emitSeamBind` (lowering.lean), for a `.move p` call argument: bind
   (`argLocal := move p`, the fn-entry retags in place), then
   `protectInPlace`: `tmp := &mut p` with `prot = true` — a fresh
   PROTECTED unique reborrow registered in the callee's frame — and
   `*tmp := uninit` through it; `tmp` is never used again. That is
   `protect_in_place_function_argument` line for line.
2. `inlineCall`: the RETURN PLACE gets the same (`dest := uninit`, which
   also roots an unbound destination, then the protected reborrow),
   before the body; the value is copied in after `popProtectors`. Unit
   destinations are skipped.
3. A TYPED read of uninitialized memory is UB on both machines:
   mirlite's `copy`/`move`/`ptrCast` fail when any read cell is `undef`;
   oseair's `Load` fails on an `Undef` value. `runN_Assgn_Load_ptr_step`
   carries the side condition; `noUndef_transport` (common.lean) moves
   it across `MemValSim`. Without this, Miri's deinit is invisible
   (`arg_inplace_observe_after` read the uninit slot as a value).
Evidence: Miri's own in-place tests, custom MIR, now in the corpus as
`fail/function_calls/arg_inplace_{observe_after, observe_during, mutate,
locals_alias, locals_alias_ret}` and `return_pointer_aliasing_{read,
write}` — 7 pass (two verdict-only: Miri attributes the alias errors to
the callee's entry, ours to the call statement); the tail-call one and
`fail/box-cell-alias` are unsupported (loader). The two local raw-read
witnesses are plain passes again (assignment move = copy; the argument
protection lands on rustc's temporary). Unit probe d9b flipped: a
whole-tuple copy with an undef field is UB, as in Miri. Corpus 93/0/43,
differential 93 matched.

[FACT, 2026-09-20, superseded 2026-09-21] **Every `Move` operand is mirlite's `move`.** The
elaborator maps `.use (.move p)` and `URvalue.move p` alike to
`RExpr.move` (elab.lean), with one exception: a moved pointer cast to a
different pointee layout (`p as *mut U`) stays the tag-preserving
`ptrCast` — the value, not the variable, is what the program uses. So
`_4 = move _1` clears `_1`'s stacks; a raw pointer into a moved-from
local is dead on both machines. This is STRICTER than Miri, which
evaluates an assignment move as a copy (rustc FIXME) and whose in-place
call protection lands on rustc's temporary. Two local witnesses record
the divergence as `xfail-model` (ours UB at the raw read, Miri ok):
local/move_arg_pops_raw, local/assign_move_pops_raw. Corpus 84 pass /
0 fail / 2 xfail / 41 unsupported; differential 86 matched (the two
machines agree with each other, as forward simulation requires).
Reasoning: a move's intended semantics is that the source is dead; Miri
has not implemented it and rustc's temporary hides the one place Miri
does act. → src/conformance/elab.lean `elabRvalue`, `elabStmt`

[FACT, 2026-09-20, first landing] **Where the seam uses it: moved CALL arguments, on
rustc's temporary.** `emitSeamBind` binds a `.move p` argument as
`argLocal := move p` and then runs the fn-entry retags on `argLocal` in
place (self-copies skipped). Since rustc moves a named place into a call
through a temporary (`_4 = move _1; consume(move _4)`), `p` IS that
temporary: the clear is unobservable in any program Charon produces,
which is why corpus and differential are verdict-neutral (86/0/41, 86
matched) and why the four local witnesses are all `ok`:
move_arg_via_temp_spares_raw, move_arg_ok, assign_move_keeps_borrows,
move_arg_field_spares_sibling — each real-Miri verified (toolchain
nightly-2026-06-01, miri 0.1.0 14210df0e2; Charon nightly-2026.08.14
prebuilt now in conformance/tools/). An ASSIGNMENT move stays a copy,
as in rustc's interpreter.

[FACT, 2026-09-20] **Design trail.** (1) First plan (2026-09-19, seam
only): copy + `src := uninit` — landed, then superseded. (2) The user
asked for an rvalue doing copy, uninit-through-owner, clear-SB; costed
as a value-package generalisation (a memory-changing pre-phase) plus
register-preservation across every leaf. (3) The user dropped the uninit
("just clear sb"): with no memory event the rvalue fits the existing
package contract, and the lockstep design made the proof a composition.
Alternatives not taken: a new oseair "touch" instruction (interpreter
churn, same keystone need); `Borrow Mut; Die` against a source-side
`useMut` (needs the cancel keystone); leaving the dead child on the
stacks on both sides (no die transport, but not "clear").

## See also

- move-deinits-its-source-at-calls.md  (Miri's in-place passing and why it protects)
- assignif-reads-its-discriminant.md
- one-leaf-per-destination-shape.md
- protectors-and-the-charon-inlining-seam.md
