# ZST loader gap fixed: unit assignments allocate, and the witness turned XPASS

[FACT] `lowering.lean` no longer drops unit-aggregate assignments; it
lowers `x = ()` as `.assign dst .uninit`. The old rule's justification
("no memory access in Miri either") was true of ACCESSES and false of
ALLOCATION: `let mut z = ()` is what binds `z`, and dropping it left the
ZST local unallocated, so `&mut z` failed at resolution in mirlite
("place root local not allocated") where Miri retags an empty range and
moves on. `.uninit` is the right lowering because a zero-length write is a
no-op on BOTH machines — mirlite's `useMut` over `len 0` is `foldCells 0`,
the target's `CStore` of zero cells passes its `0 != 0` size check and
writes nothing — while `preparePlaceAssign` still allocates the root.

[OBS 2026-08-22] Blast radius was the whole suite and the suite did not
move: 76 of 77 corpus artifacts contain a unit assignment (every `fn`
returns `()` into `_0`), and all 77 verdicts AND all 49 line-accurate
positions were unchanged. Zero-length writes cannot fail and cannot shift
attribution, which is what made this safe to do in one step. Suite
pass 77 → 78 of 118 (the witness promoted from `xfail-model` to
`supported`).

[FACT] The witness behaved exactly as designed, as a self-policing test:
`XPASS(!)` the moment the loader gap closed, and with the source no longer
failing first, the `--osea` differential immediately exposed the gap
BEHIND it — `target UB (label 5: OOB), source ok` — i.e. the target's
`Rhs.Borrow` bounds check on `size = 0`. That is the divergence the ref
leaf found; it is now isolated as the differential's single mismatch
(matched 77 | mismatch 1) and stays loud until the target check is
relaxed. Layered gaps want layered signals; `xfail-model` + the
differential gave exactly that.

[SUPERSEDED → 2026-08-22-zst-both-gaps-closed.md: refuted by rustc E0381 for the union-free fragment] [HYP] The same "access vs allocation" confusion may lurk in the other
dropped statement kinds — `StorageLive`/`StorageDead` in particular are
Miri's allocation events for locals, and the lowering currently relies on
first-assignment for allocation instead. That is fine while every local
is assigned before it is borrowed, which the corpus so far satisfies; a
witness that borrows a declared-but-unassigned local (`let x: u64; let
p = &raw const x;` — legal, reads nothing) would tell.

Validation: suite pass 78 | fail 0 | xfail 0 | xpass 0 (118),
differential matched 77 | mismatch 1 (the ZST, by design) | skipped 0,
units 15/15 + 38/38, all lake targets build.

**References:** conformance/local/zst_ref.rs, conformance/README.md
(local witnesses), loose-ends/parked.md → "ZST retag divergence",
2026-08-22-ref-ll-closed.md.
