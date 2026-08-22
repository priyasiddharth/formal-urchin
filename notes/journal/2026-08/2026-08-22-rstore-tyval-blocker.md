# The ref leaf is blocked by an OPAQUE derived `BEq` — a model-level wall

[FACT] `obseq.instBEqTyVal.beq` — the `BEq` instance `obseq.TyVal` gets
from `deriving BEq` — is **opaque to the logic**. `(TyVal.PTy ==
TyVal.PTy) = true` is not provable by `rfl`, `decide`, `simp`,
`with_unfolding_all`, or `unseal` (which reports "is not a definition").
`#print axioms obseq.instBEqTyVal` says it depends on no axioms, so this
is not an `opaque` declaration in the usual sense — the derived function
for this NESTED inductive (`TupTy (tys : List TyVal)`) simply carries no
equations the elaborator can use. The compiled code evaluates it fine,
which is why the conformance and differential suites are green; the gap is
purely between runtime and proof.

[FACT] The consequence: **no theorem can step over an `Instr.RStore`.**
`oseair.stepWith`'s `RStore` case is
`if srcTy != ty then Err else writeThroughPtr …`, and discharging that
guard needs exactly the unprovable reflexivity. This blocks
`CompilerInv_step_ref`, whose fragment is `Borrow; RStore`, and will block
`alloc`, `exposeAddr` and `refSlice` when they arrive. `CStore` is
unaffected — its guard is `vals.length != typeSize ty`, a `Nat`
comparison.

[OBS 2026-08-22] Found by attempting the leaf, not by testing — the same
way the deref-read divergence was found (2026-08-21). Prediction worth
recording: every remaining `RStore`-shaped construct will hit this, so
fixing it once unblocks a class, not a case.

[FACT] Everything ELSE the local→local ref regime needs now exists and is
green: `compileStmt_ref_local_local_run`/`_value` (proof/ref.lean) —
which also settles a structural question, namely that the fragment is
`Borrow; RStore` with **no `Die`**, because the borrow's cleanup is never
emitted for a stored reference, so the ref leaf does NOT need BRIDGE 1 —
plus `runN_Assgn_Borrow_step`, `sb_ref_respects_PermSim`,
`LocalBindingSim.rename_mono`, and the strengthened `LocalBindingSim`.

[FACT] `LocalBindingSim` gained a conjunct: every bound local's WHOLE
block is in ρa's domain, not just its base. `MemValSim`'s referent-range
obligation is what forces it — a `&local` whose pointer is STORED needs
the range, and the base alone does not give it. It mirrors `MemValSim`'s
own range conjunct exactly. Cost: five destructuring sites and one new
obligation in regime B (trivial there — `blockSize NatL = 1`).

[OBS 2026-08-22] A second, independent divergence found the same way: for
a ZERO-SIZED place the target's `Rhs.Borrow` bounds check
(`addr ≥ base + size` with `size = blockSize τ = 0`) fires, while
mirlite's `M.ref` has no such check and succeeds. Source-ok/target-UB, the
same shape as the deref-read finding — but here Rust sides with the
SOURCE (`&()` is legal), so the target is the divergent one. Out of the
conformance surface (`zst-field-retagging-terminates` is UNSUPPORTED), so
the closed regime will carry `0 < blockSize τ` and ZSTs become a named
residual.

[OPEN] The fix for the `BEq` blocker is a model change and therefore the
user's call. Options, cheapest first:
1. Hand-write a structural `BEq TyVal` in `src/obseq/types.lean`
   (precedent: `layoutDecEq` is already hand-written there "because obseq
   derives only BEq"). Behaviour-identical, makes the guard `rfl`.
2. Drop the `srcTy != ty` guard from `RStore` — it is a compiler-bug
   check, and `compileRExprToChecked` only ever emits `RStore` with the
   register's own type.
3. Prove reflexivity — NOT available; the function has no equations.
Option 1 is the least invasive and the most in keeping with the file's
existing style. Both 1 and 2 touch a v1/v2-shared file, so both need the
suite re-run (77/117 + differential 77/0/0) before being trusted.

Validation of what DID land: units 15/15 + 38/38, suite pass 77 | fail 0
(117), differential matched 77 | mismatch 0 | skipped 0, obseq2 green.
Audit stays at 4.

**References:** proof/common.lean §F (BLOCKER note), proof/ref.lean
(leaf docstring), 2026-08-21-deref-read.md (the analogous finding).
