# `assignIf` reads its discriminant; `SkipIf` guards a value, not a place

Load this before touching `assignIf`, `SkipIf`, or the enum seam; and
before proposing to scope a proof to "event-free" discriminants.

[FACT, 2026-09-17] **The discriminant is a Stacked Borrows READ on both
machines.** mirlite's `.assignIf` arm is `copy` of a `NatL` place
followed by a compare: `resolvePlaceAcc` (deref levels read their
pointer cells), the same bounds guard, `M.read addr 1 tag`, then
`mem.find? = word v` on the post-read state; the guarded `doAssign` and
the fall-through both run from the post-read state. The compiler lowers
it as copy's read — `placeToRegChecked Shared discr; Load NatTy;
cleanup` — and then `SkipIf r val n` on the loaded VALUE register.
`SkipIf` touches no memory.
→ src/obseq3/mirlite_semantics.lean, the `.assignIf` arm
→ src/obseq3/oseair.lean, `Instr.SkipIf`; compile.lean, the `.assignIf` arm

[FACT, 2026-09-17] **Until this change the discriminant was a raw peek —
`resolvePlace?` + `mem.find?`, no access — and that was the deviation,
not the target's borrow.** In MIR `discriminant(place)` reads the place
and Miri performs a read access through its provenance. The peek forced
the target's `SkipIf` to dereference a pointer register and peek memory
itself, with any projection temporary killed BEFORE it ("safe because
SkipIf performs no SB access" — i.e. a read through a dead tag was
being avoided by not reading). A projected discriminant at nonzero
offset lowers to a `Borrow`/`Die` bracket, correctly; against a source
that performed no access that shape was unprovable as a forward
simulation and could diverge. The honest read dissolves it.

**Why I was misled:** I first planned to keep the peek and scope
`CoreStmt`'s `assignIf` arm to "event-free" discriminant shapes (a
local, or an offset-0 projection of one — all the corpus has). The
user's question — shouldn't the discriminant read be a temporary
borrow and die, to be consistent? — is the right frame: the borrow was
never the problem.

[EMP, 2026-09-17, verified against 7764bc5+] **Verdict-neutral on
everything we have.** Units 106/106 (g11's golden stream gains the
`Load` and shifts one register; d16 taken / d17 skipped unchanged),
corpus 82/0/41, differential 82 matched. The reason: the seam emits
`dst.0 := copy src.0` before every guard `if src.0 == v: …`, so each
guard's read of `src.0` repeats a read through the same tag. An SB read
is idempotent — the Uniques above the tag are already disabled, and a
protector would have fired on the first read. `N` guarded fields cost
`N + 1` reads of the discriminant where Miri does one per match; the
extra reads change no state.

[FACT, 2026-09-17] **`SkipIf` jumps on the MISMATCH.** `assignIf` runs
the assign when equal; `SkipIf` falls through when equal and jumps over
the guarded block otherwise — same test, opposite action on the true
branch. It is a bare forward jump over `n` instructions with no body of
its own; the correspondence with `assignIf` is a property of the
lowering (`emitSkipIfAround` sets `n` to the compiled assign's length),
which is what the simulation lemma has to establish.

[FACT, 2026-09-17] **The destination's root local is allocated BEFORE
the read, on both paths.** mirlite's arm runs `ensureRoot dst` first
(allocate the root local if unbound, recursing through proj and deref);
the compiler's arm runs `ensurePlaceRoot dst` before `guardRead discr`.
Until this change the compiler rooted the destination INSIDE the guarded
block — a compile-time `placeRegMap` entry whose `Alloc` ran only when
the guard was taken; a skipped guard followed by a write to the same
local stored through a never-assigned register (probe
`rs_guarded_fresh_root_then_write`: source `.ok`, target `.ub 2`). The
seam never produces the shape (`dst.0 := copy src.0` precedes every
guard), which is why the corpus was silent. A target-only hoist would
break `AllocLockstep`; a compile-time rejection was considered and
rejected (already-rejected-design-alternatives.md). Statement order is
now root, read, compare, assign — the same root-first order `assign`
has (`preparePlaceAssign` before the rvalue).
→ src/obseq3/mirlite_semantics.lean `ensureRoot`; compile.lean, the
`.assignIf` arm and `guardRead`
→ journal/2026-09/2026-09-17-assignif-guarded-root.md

[FACT, 2026-09-17] **`assignIf` IS in `CoreStmt`**, with `CoreRhs rhs`
and no shape condition on the discriminant or the destination.
proof/assign_if.lean: `CompilerInv_step_assignIf` = the root step
(`ensureRoot_simulation`) + copy's read package with its register
exposed (`copy_readRegPkg_flat`) + one `SkipIf` step + either the assign
leaf at the fall-through state (`AssignLeaf`, every rvalue) or the
invariant rebuilt at the statement's end from the fact that the
never-run body kept the place map (`compileAssignChecked_placeRegMap_of_mapped`).

## Why this matters

The last statement gate on `CoreProg` is `alloc`/`dealloc`. The guard's
read is copy's proved read package at `NatL`, and the taken arm is the
existing assign leaves with their code starting one `SkipIf` later —
which is what the leaves' `InvAt` + `StmtFrame` interface exists for.

## See also

- journal/2026-09/2026-09-17-assignif-guarded-root.md  (the guarded-root bug)
- protectors-and-the-charon-inlining-seam.md  (where `assignIf` comes from)
- split-the-mint-out-of-the-bracket.md
- one-leaf-per-destination-shape.md
