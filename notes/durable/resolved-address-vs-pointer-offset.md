# [FACT] Why the two machines spell a pointer's offset differently

Tags: obseq3, mirlite, oseair, representation, arithmetic

## the two forms

- **mirlite** `PlaceRes` carries an ABSOLUTE `addr` beside `allocBase`
  and `allocSize`. A pointer VALUE is built with one subtraction, at
  the moment of the retag (`mirlite_semantics.lean`, `.ref` arm):

  ```lean
  MemValue.ptrVal resolved.allocBase (resolved.addr - resolved.allocBase)
                  resolved.allocSize freshTag
  ```

- **oseair** `Val.Ptr base offset size tag` CARRIES the offset, and
  `Rhs.Borrow` accumulates it by addition (`oseair.lean:305`):

  ```lean
  RhsResult.Ok [Val.Ptr base (baseOff + offset) size newTag] ...
  ```

  (the absolute address is reconstructed as `base + baseOff + offset`
  only for the permission check, line 293).

## the consequence

A projection applied on the SOURCE side lands as
`addr + off - allocBase`; the same projection applied on the TARGET
side lands as `addr - allocBase + off`. On `Nat` these agree only given
`allocBase ≤ addr` — which is exactly the conjunct
`ptrChain_lowering_sim` returns (`h_dle`). `MemValSim`'s pointer case
demands `o' = o` on the nose, so every leaf that builds a pointer value
discharges this once.

## [FACT] changing oseair would NOT remove the obligation

Asked 2026-08-31: could `Rhs.Borrow` emit the `addr + off - allocBase`
form instead, to make the proofs line up?

No, on three counts.

1. It is not a syntax choice but a REPRESENTATION difference. Emitting
   `Val.Ptr base (base + baseOff + offset - base) size newTag` is the
   same number unconditionally (`Nat.add_sub_cancel_left`), so the
   semantics would not change — but in the proofs `baseOff` is itself
   `addr - allocBase`, so the term becomes
   `allocBase + (addr - allocBase) + off - allocBase`, which still needs
   `allocBase ≤ addr` to reach `addr + off - allocBase`. The obligation
   MOVES; it does not vanish.
2. It changes the TARGET LANGUAGE's operational semantics to suit a
   proof, which is backwards: `compile_correct` would then assert
   something about a different oseair.
3. It would churn 325 `Val.Ptr` spellings across the proof files.

## what does help

The csnorm precedent: a normal form on the PROOF side. The bridge is
named once in `common.lean`:

```lean
theorem resolvedAddr_cancel  (h : allocBase ≤ addr) :
    allocBase + (addr - allocBase) = addr
theorem resolvedOffset_shift (h : allocBase ≤ addr) (off : Nat) :
    addr - allocBase + off = addr + off - allocBase
```

`resolvedAddr_cancel` is the fact 38 leaves currently re-derive inline
as `h_cancel := Nat.add_sub_cancel' h_dle` (143 uses); the existing
sites are left alone — renaming them is churn with no proof-power gain
— but new leaves should use the named form so the dependency on `h_dle`
stays visible.

## [OBS] do not hand this goal to a bare `omega`

`omega` on `addr + off - allocBase = addr - allocBase + off` without
`h_dle` threaded reports a counterexample over UNRELATED atoms
(compiler-state `nextLabel`/`nextReg` picked up from context), which
reads as a broken goal rather than a missing hypothesis. Name the
equation.
