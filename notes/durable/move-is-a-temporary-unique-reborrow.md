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

[FACT, 2026-09-20] **Where the seam uses it: moved CALL arguments, on
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
