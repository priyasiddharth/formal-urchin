# 2026-08-29 (cont.) — Copy D→L closed; the read-side event fix

## The event fix (semantics, both flagged and pinned)
mirlite's `.copy` gains the range-dereferenceability check — the
read-side twin of the retag fix: `resolved.addr + blockSize τ >
allocBase + allocSize → err`. Through a LOADED pointer the SB read
alone checks per-cell stacks, so pre-check the t16 junk state (a
shrunken-size ptrVal) let the source copy succeed while the target
`Memcpy` errs. For local/proj sources the check is discharged by
construction/typing (one `if_neg` repair per closed leaf — irrefl for
L→L, `PathTo.offset_add_size_le` for P0/P). Reachable behavior
unchanged (suite 82/123, differential all green). Pinned by t17
(t16's junk state consumed by a copy; teeth verified by inverse-edit
reversion — the check off, the source accepts). First t17 attempt
found the OVERLAP guard firing first (`x := copy *p` with p = &mut x
IS an overlapping assignment) — a nice incidental witness that the
guard covers deref shapes; the test now copies into a third local.

## The leaf
`copy_deref_local_simulation`: `dst := copy *P` over a load spine.
Fragment `[P-code; Load; Memcpy]` — the deref place-lowering carries
NO cleanup, so no Borrow, no Die, no keystone, no commutation: the
copy reads through the LOADED tag, exactly the source's wide read.
Composition: D→L-ref's scaffolding (agreement-lemma-backed guard
reduction, StateIncr chain, spine prelude) + the L→L Memcpy endgame +
one extra read transport. New lemma `resolvePlace?_of_resolveAcc`
(spine.lean): the pure resolver agrees with a successful access
resolution — connects the guard's ranges to the inverted ones.
No tag minted: both renames grow by refl; NextTag equalities frame
through five ops (spine, ptr-read, wide-read ×2 sides, write).
d37 covers the fragment differentially (50/50 units).

## Copy is now closed on every SPINE-SHAPED source
L→L, P0→L, P→L, D→L. The copy residual holds only mixed/proj-of-proj
chains, unbound dst, and non-local dst — all composition classes
shared with ref/const_write.

## State
All targets 0 errors; units 17/17 + 50/50; suite 82/123 (0 fail);
axiom audit exact; leaf axioms propext/Classical.choice/Quot.sound.
