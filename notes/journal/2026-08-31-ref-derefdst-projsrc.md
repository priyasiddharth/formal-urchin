# ref: deref destination with a proj-topped source

Date: 2026-08-31
Tags: obseq3, ref, deref-dst, projection, flatten

## [FACT] ref's proj source is NOT copy's proj source

In `copy`, a proj-topped source at nonzero offset mints its OWN
`Borrow(Shared)` and leaves a cleanup `Die` — that is why the copy
class needed four leaves carrying BRIDGE 1S around the read (see
2026-08-30-projsrc-offset-bridge1s.md).

In `ref`, the field offset is folded into the `Borrow`'s OFFSET
OPERAND. `placeToBorrowRegChecked`'s proj arm differs from its local
arm only in that operand. So `*p := &kind s.f` compiles to the SAME
two instructions as `*p := &kind s`, with `pathOffset f` where the
local arm had `0`. No second borrow, no second bridge, no cleanup.

Consequence: `ref_derefdst_projsrc_simulation` is
`ref_derefdst_local_simulation` with four mechanical substitutions:

1. `{srcLoc : Local Γ τ}` becomes `{srcLoc : Local Γ σb} {f : PathTo σb τ}`;
2. every `Borrow ... srcReg 0` becomes `... srcReg (pathOffset f)`;
3. the stored pointer `Val.Ptr bS.addr (0 + 0) (blockSize τ)` becomes
   `Val.Ptr bS.addr (0 + pathOffset f) (blockSize σb)` — it still
   covers the WHOLE base allocation, so its size is σb's, not τ's;
4. the mirlite side stores `ptrVal bS.addr (bS.addr + pathOffset f -
   bS.addr) (blockSize σb)`, and the addr conjunct closes with
   `simp [Nat.add_sub_cancel_left]`.

## [OBS] the source resolution must stay targeted

First attempt used `simp only [mirlite.evalRExpr,
mirlite.resolvePlaceAcc, h_envS]` to reduce the source. That UNFOLDS
`resolvePlaceAcc` globally, which also unfolds the DESTINATION's
`resolvePlaceAcc MSB _ (Place.deref P)` into a nested `match` — after
which `rw [h_dres]` cannot fire, because the destination is no longer
a syntactic `resolvePlaceAcc` application.

The parent avoids this by rewriting with the TARGETED lemma
`resolvePlaceAcc_local h_envS` rather than unfolding. The proj version
is `resolvePlaceAcc_proj_base_ok (path := f) (resolvePlaceAcc_local
h_envS)` (spine.lean:152). Two errors, one line.

Rule of thumb: in a leaf whose destination is kept OPAQUE for the
mother lemma, never put a definition in a `simp only` set if that
definition also governs the opaque half.

## [FACT] the destination flatten transfer is rhs-polymorphic

`compileStmt_ref_derefdst_flatten_run/_value` never inspected the rhs
— it treats `RExpr.ref kind prot mask (.local srcLoc)` as one opaque
`compileRExprPreChecked` argument throughout. Generalized in place to
`(rhs : RExpr Γ (PtrL τ))` and renamed
`compileStmt_assign_derefdst_flatten_run/_value`. Every future
deref-destination leaf, whatever its source shape, gets the flatten
normalization for free — no per-source twin.

The mirlite-side twin `stepStmt_assign_dstderef_flatten`
(spine.lean:1516) was already rhs-polymorphic.

## [FACT] d75's teeth are a disjoint live borrow

`expectDiff` compares verdicts, so a wrong offset must induce UB, not
a wrong value. d75 takes `r := &mut t.0` and keeps it live across
`*p := &mut t.1`; the two fields are disjoint ranges, so the new
borrow must not pop `r`, and `*r := 9` afterwards is well-defined
exactly when the offset is `1`.

Control run: retargeting the statement's source to `t.0` makes mirlite
report `ub` at statement 7. The teeth bite.

## state

Build green (Core, Obseq3, Obseq3Proof, Conformance); 17/17 + 88/88;
audit exact at ONE sorry (`ref_place_residual`) — unchanged, as this
increment closed a class the residual still covers elsewhere.

Remaining ref classes: unbound destination roots, non-local sources
under non-local destinations, proj-of-proj sources, non-spine deref
sources.
