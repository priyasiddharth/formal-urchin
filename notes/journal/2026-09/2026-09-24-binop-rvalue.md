# `binOp`: dynamic word arithmetic in mirlite and oseair

2026-09-24. Asked: "can we add dynamic binop eval to mirlite and oseair?
What is the fallout to the proof surface area?" — the answer, now
measured rather than estimated.

## The model half is one constructor each

[FACT] `RExpr.binOp : BinOp → Place Γ NatL → Place Γ NatL → RExpr Γ NatL`
(syntax.lean) with `BinOp`/`evalBinOp` in **types.lean**, not syntax.lean:
oseair.lean imports `obseq3.types` only, and `Rhs.BinOp` needs the enum
for its `deriving Repr, Inhabited, BEq`. Semantics: two `evalCopy` reads
in sequence, the second in the state the first left (the `evalAllocLen`
pattern), then the word; a non-word operand or an uninitialised cell is
UB through `evalCopy`. Target: `Rhs.BinOp op r1 r2` on two VALUE
registers, no memory and no permission event. Compiler:
`readToReg a; readToReg b; fresh tmp; Assgn tmp (BinOp op r1 r2)` and an
`RStore NatTy tmp`.

[FACT] Words are unbounded `Nat` (sb.lean:30): `sub` truncates at 0,
`add`/`mul` never overflow. Rust's checked ops only differ on paths where
Miri PANICS, and the certificate rejects those paths, so no verdict can
silently diverge. Fixed width (mod 2^w, two's complement) was costed and
declined — it is recorded in parked.md as the follow-up if exact wrapping
values are ever wanted; it costs no proof work, since the package never
unfolds the arithmetic.

## The proof fallout: ONE new export, everything else is new code

[FACT] The only change to existing proofs is that the read packages now
export a REGISTER FRAME. `binOp` is the first rvalue with TWO reads, and
the first operand's register must still hold its word after the second
read has run. The mother lowering lemma already proved this
(`h_sframe`, spine.lean:1672) and both copy read lemmas DROPPED it
(copy.lean:258, :470). Now:

- `copy_chainsrc_read` / `copy_projsrc_offset_read` export the frame at
  the POST-read register map (the lemma does its own `lookup_insert_ne`
  peeling, where `h_sregmono` is in scope) — this is what makes the
  ~11 instance sites a one-line `exact`/two-line `rw`.
- `ReadPkgLowered`, `ReadPkgProjOffset`, `ReadRegPkg` gained
  `∀ r, RegisterBelow csA.nextReg r → lookup sR.reg r = lookup sA.reg r`;
  `ReadRegPkg` also re-exports the `RegisterBelow … valueReg` it dropped.
- Instances updated: copy ×2, casts ×4 (exposeAddr, fromExposed in both
  shapes), ptrarith ×6 (ptrOffset, ptrCast, refSlice in both shapes).
  Every one is `fresh_reg_ne h_below h_sregmono` (new helper,
  common.lean) under one `RegMap.lookup_insert_ne` per temporary.

[FACT] `CheckedCompilerM.incr m cs : StateIncr cs (run m cs)` is free
monotonicity for ANY compiler computation (compile.lean:148) — there is
no need to re-derive `cs.nextReg ≤ (run … cs).nextReg` from the mother.
Worth remembering: several proofs reach for the mother's `h_sregmono`
where this one-liner would do.

## The package itself

[FACT] `binOp_valuePkg` (proof/binop.lean, ~230 lines) is
`alloc_fromPlace_valuePkg` with the read package used TWICE and the
allocation replaced by `runN_Assgn_BinOp_step`. One subtlety the alloc
template does not have: `ValuePkg` demands `value (compileRExprPreChecked
rhs) csA = ok pOut` UNGATED, so the SECOND read must be known to compile
before any code fact is available. `LocalBindingSim` at the post-first-read
compiler state is gated, so the mapping has to come the other way:

- `evalCopy_state_shape`: copy's read changes ONLY `perms`.
- `resolvePlace?_perms`: `resolvePlace?` never looks at permissions.
- `readToReg_placeRegMap_any` + `PlaceInputsMapped.placeRegMap_congr`:
  the place map is the same at `csA` and after the first read.

So `b`'s root is mapped at `csA` (from the ungated `h_lbs`), hence at the
first read's end state — ungated. That three-lemma bridge is the
structural lesson: **an rvalue with two reads needs place-map
transport, not simulation transport, for its second operand.**

Audit after the change: same two roots, 3 axioms, 0 sorries. Units
18/18 and 120/120; corpus unchanged at 96/0/40 (the seam has not been
taught `binOp` yet — that is the next commit, and it is what takes the
14 unchecked pins to 0).
