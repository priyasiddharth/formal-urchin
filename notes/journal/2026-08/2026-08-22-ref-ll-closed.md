# Ref regime L→L closed, via a hand-written `BEq TyVal`

[FACT] `ref_local_local_simulation` (proof/ref.lean) is proved:
`dstLocal := &srcLocal`, both bound, non-zero-sized referent. The
fragment is `Borrow; RStore`. This is the first leaf that grows ρt at a
USER-visible tag — the source's fresh reference tag and the target's are
paired by `sb_ref_respects_PermSim`, and the stored pointer's `MemValSim`
holds under that extension. ρa does not grow. Audit accounting: 4 → 6
named sorries, because `CompilerInv_step_ref` became a dispatcher over a
closed regime and three residuals (ZST, fresh-dst, proj/deref) — the same
move as the D1 split on 08-21; strictly more is proved.

[FACT] The blocker from earlier today is resolved at the root. `obseq.TyVal`'s
derived `BEq` was an opaque `partial def` (nested inductive; the handler
cannot prove termination; `partial` ⇒ `opaque` ⇒ no equations).
`deriving DecidableEq` refuses the type outright ("None of the deriving
handlers … applied"), as the `layoutDecEq` precedent implied. The fix is a
mutual structural `beq`/`beqList` plus a `LawfulBEq` instance via mutual
induction — ~40 lines in obseq/types.lean, first-try clean in the
prototype. With `LawfulBEq`, `runN_RStore_step` closes over a VARIABLE
`ty` by `bne_self_eq_false`, not just on constructor forms, so the
`alloc`/`exposeAddr`/`refSlice` leaves inherit the lemma as-is.
Safety argument: the old instance had no equations, so no proof could
have depended on its behaviour; the new one is proven lawful and the
suites are unchanged (77/117, differential 77/0/0, interp tests, v1/v2
build).

[FACT] Design fact settled by the fragment lemma
(`compileStmt_ref_local_local_run`): there is NO `Die` in the ref
fragment when the destination is a local. The borrow's cleanup lives in
the rhs result and the `.assign (.local _)` arm never emits it — the
reference is the stored value and must stay alive. So BRIDGE 1 is NOT
needed for this leaf. It enters `ref` only through the destination side,
when a non-local `dst` lowers via `placeToRegChecked RefKind.Mut` with its
own `Die` (residual 6).

[FACT] `LocalBindingSim`'s new block-domain conjunct (landed earlier
today) paid off exactly as intended: the stored pointer's `MemValSim`
needs `∀ k < blockSize τ, ρa (bS.addr + k)` defined, and the source
local's binding supplies it directly (`h_domS`). Without that conjunct
this leaf would have needed a separate invariant about allocated ranges.

[EMP] (Lean 4.28) three potholes, one of them load-bearing:
- `omega` does not see through `abbrev Word := Nat` when the atoms are
  projections like `bS.addr` — it silently drops them and reports a
  counterexample over the atoms it DID parse. (The 08-18 note "no omega —
  Word" was this.) Use `Nat.lt_add_of_pos_right`/`simp only [Nat.add_zero]`
  explicitly; `omega` is fine on `nextReg`/`nextLabel`/`blockSize`.
- Structure-instance fields must sit to the RIGHT of the `{` they belong
  to (column rule): `(s_osea := { s_osea with perms := …,` followed by a
  less-indented `reg := …` line fails with "expected '}'". Put `{ s_osea
  with` on its own line and indent every field past it.
- `by omega` inside an application whose implicits are still
  metavariables at elaboration time reports the goal as unprovable with no
  atoms listed; `show <the goal> by …` fixes the order.

[OPEN] Residuals 4–6 (see the audit). The fresh-dst one is the natural
next leaf: it is regime B composed with this regime, and every piece
exists. The ZST one needs a model decision (relax the target's `Borrow`
check for `len = 0`, or keep ZSTs out of scope).

Validation: units 15/15 + 38/38, suite pass 77 | fail 0 (117),
differential matched 77 | mismatch 0 | skipped 0, interp tests pass,
v1/v2/v3/conformance build. `#print axioms ref_local_local_simulation`:
propext / Classical.choice / Quot.sound; `instLawfulBEqTyVal`: propext.

**References:** proof/compiler.lean (audit),
2026-08-22-rstore-tyval-blocker.md (the diagnosis), obseq/types.lean (the
fix), loose-ends/parked.md (ZST residual).
