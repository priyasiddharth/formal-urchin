# `move` call arguments deinit their source at the seam

[FACT 2026-09-19] The user asked for `move` in mirlite and whether a move
should "zero out the borrow stack". Answer from the sources: Miri treats
an assignment move as a copy (rustc `eval_operand`, one arm for both,
with a FIXME), and a CALL-ARGUMENT move as in-place passing — fresh
protected reborrow of the caller's slot, uninit written through it, tag
dropped. The protector exists to license pass-by-pointer codegen (the
slot must be untouchable for the call, and uninit alone forbids only
reads). Our seam copies the argument, so the guard has nothing to
guard; the observable residue is the deinit, which is one write through
the source's owning tag. Full account:
durable/move-deinits-its-source-at-calls.md.

[FACT 2026-09-19, verified against ce2c5d6+] `emitSeamBind`
(lowering.lean) now emits `p := uninit` after binding a `.move p`
argument at an inlined call. Corpus 82/0/41, differential 82 matched,
units 110/110 — verdict-neutral on everything committed, which is the
expected sign: a test that moved a local into a call and then read it
through an older raw pointer would have been a `pass`-vs-Miri mismatch
before, and the corpus had none.

[FACT 2026-09-19] `move` is NOT added to mirlite's surface language;
the three costed alternatives and why each loses are in the durable
note. No mirlite or proof change; `uninit` is in `CoreRhs`.

[OPEN 2026-09-19] No committed conformance test exercises the new
deinit (needs a Charon artifact: move a local into an inlined fn, then
read it through a raw pointer taken before the call; Miri: UB at the
read). Worth adding when a Charon toolchain is at hand — it would be the
first corpus witness of the seam's move semantics.

## See also

- move-deinits-its-source-at-calls.md
- protectors-and-the-charon-inlining-seam.md
