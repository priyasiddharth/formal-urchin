# ρa/ρt are identity-on-domain — no address/tag transport needed

Load this when a simulation lemma seems to need renaming-invariance of
permissions, or address arithmetic across the rename maps.

[FACT] `CompilerInv` carries `IdentityOnDomain ρa ∧ IdentityOnDomain ρt`
as conjuncts 8–9 (`IdentityOnDomain {α} (ρ : α → Option α) : Prop :=
∀ a a', ρ a = some a' → a = a'`, generic over `α` to cover both
`AddrRenameMap` and `TagRenameMap`).
→ src/obseq2/proof/common.lean (`IdentityOnDomain`)
→ obseq2-comparison.md, 2026-06-17 entry

[FACT] Justification: lockstep bump allocators. mirlite `allocateBase`
(mirlite_semantics.lean:87-89) and oseair `Alloc` (oseair.lean:57-58)
bump `addrStart` identically, and `CompilerInv` already holds
`s_osea.ap = s_mir.perms` verbatim — those reconcile only if ρa/ρt are
identity on live addresses/tags. Rejected alternatives: a `PermSim`
relation, or deriving identity on the fly.

[FACT] Consequences: the target `useMut`/`sb_use_mb` is literally the
source one (permission.lean untouched); bounds transport verbatim;
`writeThroughPtr_sim` became near-trivial. Regime-B (fresh-local)
extensions must add *identity* entries `(newAddr ↦ newAddr)` to
preserve the conjunct — which they do, since source `allocate` and
target `Alloc` return the same `addrStart`.

## Why this matters

Any lemma tempted to prove "permission checks are invariant under
renaming" is doing work the invariant already did. Destructures of
`CompilerInv` carry `h_id_a`/`h_id_t` binders — use them.

## Scope caveat — v2 only; obseq3 kept HALF of this

[FACT, 2026-09-03] Everything above is stated for v2 (`src/obseq2/`).
In **obseq3** only the ADDRESS half survived. `CompilerInv` there
carries `IdentityOnDomain ρa` and `TagRenameWF ρt` — NOT identity on
tags — because the two machines' tag counters diverge (an interior
`Borrow` mints on the target that the source never makes), so ρt is a
real renaming: `sb_own_respects_PermSim` returns
`ρt.extend src.NextTag tgt.NextTag` with the two `NextTag`s different,
and `TagRenameBounded` is what relates the counters.

[FACT, 2026-09-03] Consequently the alternative this note records as
REJECTED — "a `PermSim` relation" — is exactly what obseq3 ADOPTED
(`PermSim ρt src tgt` = StackMapSim ∧ protFrames ∧ exposed ∧
`src.NextTag ≤ tgt.NextTag`), with `sb_read/write/ref_respects_PermSim`
as its transport lemmas. The v2 reasoning was not wrong for v2; the
tag-minting asymmetry that forces `PermSim` only appears once interior
borrows enter the lowering.

## See also

- writethroughptr-sim-is-place-kind-agnostic.md
- empty-blocks-need-a-separate-base-fact.md — the obseq3 fresh-block
  extension (`extendBlock`) that preserves the ADDRESS identity
