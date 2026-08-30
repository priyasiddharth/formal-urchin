# Empty blocks: range-quantified facts go vacuous, so carry the base separately

Load this when writing (or debugging) any rename-extension, referent, or
block-domain obligation. Three separate leaves have now been bitten by
the same hole, always in the same way.

[FACT, 2026-08-30] **The hole.** Every "whole block" property in the
development is quantified as `∀ k, k < blockSize τ → …`. For a
ZERO-SIZED layout (`blockSize τ = 0`) that quantifier is VACUOUS — it
supplies nothing at all, including nothing about the block's own BASE
address, which the binding/referent still genuinely has. Any obligation
of the shape "the base is mapped / in range / renamed" must therefore be
carried as its OWN conjunct, never derived from the range one by
instantiating at `k = 0`.
→ `LocalBindingSim` (src/obseq3/proof/common.lean): note it has BOTH
  `ρa binding.addr = some base` and the `∀ k < blockSize τ` conjunct.
  That redundancy at non-zero sizes is exactly what saves the ZST case.

[FACT, 2026-08-30] **Instance 1 — the mother lemma.** `ptrChain_lowering_sim`
carries a final conjunct `ρa resolved.allocBase = some resolved.allocBase`
purely for ZST referents: its range conjunct
`∀ k, k < resolved.allocSize → ∃ a', ρa (allocBase + k) = some a'` is
vacuous when `allocSize = 0`, and the consumers still need the base.
(Added 2026-08-30 during the chain-dst subsumption; the ZST-referent gap
was found by a leaf that could not discharge `h_drange` at all.)

[FACT, 2026-08-30] **Instance 2 — regime B for copy.** The address rename
extension for a freshly allocated destination is
`AddrRenameMap.extendBlock ρa base n = (ρa.extend base base).extendIdRange base n`
(src/obseq3/proof/common.lean). NEITHER half alone works:
- `extend base base` (one pair) satisfies `ρa binding.addr = some base`
  but not the block-domain conjunct — a two-word local's cell `base+1`
  stays unmapped, which breaks the moment the `Memcpy` writes it.
- `extendIdRange base n` (the range) satisfies the block-domain conjunct
  but for `n = 0` its range `[base, base)` is EMPTY, so it does not even
  map the base — while a ZST local really is bound at that address.
`extendBlock_base` proves `extendBlock ρa base n base = some base` by
splitting on `base < base + n`: non-empty blocks get it from the range,
empty blocks from the inner single pair.

[FACT, 2026-08-30] **Why const_write did not need this and copy did.**
`const_write_proj_fresh_simulation` allocates a root `σ` that always
carries a field path `PathTo σ NatL`, so `PathTo.offset_add_size_le`
forces `blockSize σ ≥ 1` and the empty case is unreachable —
`extendIdRange` alone sufficed there. A COPY destination has an
arbitrary layout, so the ZST case is live. The original bare-local
regime B was relying on the mirror-image accident: its local was `NatL`,
one cell WAS the whole block, so a single pair happened to satisfy both
conjuncts. Two accidents, opposite directions, same latent hole.

[FACT, 2026-08-30] **Rejected alternative:** widening the range to
`base ≤ x ≤ base + n` (inclusive). It would cover the ZST case in one
definition, but `base + n` is exactly where the NEXT allocation starts
under the bump allocator — ρa would be claiming an address before
anything is allocated there. The composed form keeps ρa's domain to
"cells of this block, plus this block's base", each with its own
justification.

[FACT, 2026-08-30] The extension needs NO freshness side condition
(`AddrRenameIncr.extendBlock` / `IdentityOnDomain.extendBlock` take only
`IdentityOnDomain ρa`): if an address was already in ρa's domain,
identity-on-domain says it was already mapped to itself, so re-mapping
it to itself cannot conflict. Same argument as the older
`AddrRenameIncr.extend_id`.

## See also

- zst-locals-share-addresses-harmlessly.md — why the coincident
  addresses that make this hole reachable are themselves benign
- rho-maps-are-identity-on-domain.md — the v2-era statement of the
  identity property (see its scope caveat for obseq3)
- journal/2026-08-29-copy-fresh-dst.md — the increment that added
  `extendBlock`
