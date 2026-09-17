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

## Why this matters

`assignIf` can now enter `CoreStmt` with NO shape condition: the guard's
read is copy's proved read package at `NatL`, and the taken arm is the
existing assign leaves with their code starting one `SkipIf` later.

## See also

- protectors-and-the-charon-inlining-seam.md  (where `assignIf` comes from)
- split-the-mint-out-of-the-bracket.md
- one-leaf-per-destination-shape.md
