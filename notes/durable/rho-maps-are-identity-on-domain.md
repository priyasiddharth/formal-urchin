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

## See also

- writethroughptr-sim-is-place-kind-agnostic.md
