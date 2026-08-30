# 2026-08-30 — ZST addresses, extendBlock's shape, wildcard provenance

Discussion session (no proof delta) following the copy regime-B
increment. Three questions from the user, each of which turned out to
have a durable answer; all three are now written up.

[OBS 2026-08-30] **Q: what decision did `extendBlock` encode?** Answer
distilled to durable/empty-blocks-need-a-separate-base-fact.md. Short
form: the block-domain conjunct is range-quantified and therefore
vacuous for a ZST, so the base pair has to be carried separately from
the range — `(ρa.extend base base).extendIdRange base n`. The inclusive
range `x ≤ base + n` was rejected because `base + n` is the next
allocation's base under the bump allocator.

[OBS 2026-08-30] **Q: two allocations can start at the same address —
isn't that a problem?** Answer distilled to
durable/zst-locals-share-addresses-harmlessly.md. Checked, not
recalled: `LocalBindingSim` (common.lean) has no injectivity clause,
and `sb_own` (sb.lean:378) folds over the range AFTER minting, so a
ZST's tag exists but is in no stack. The copy overlap guard is false at
`blockSize = 0`, so no spurious "overlapping ranges".

[OBS 2026-08-30] **Q: does a raw-pointer local have a unique tag?**
Answer distilled to
durable/raw-pointer-provenance-is-the-wildcard-tag.md. The LOCAL does
(freshTag ≥ 1); the VALUE it holds may be `wildcardTag = 0` when it came
from `fromExposed`, and wildcard accesses resolve optimistically against
`exposed` per cell. This is the reason for the
`(tag == wildcardTag) = false` side conditions that appear all over the
transport lemmas.

[OBS 2026-08-30] Side finding while writing the above: the v2 durable
note rho-maps-are-identity-on-domain.md is only HALF true in obseq3 —
ρa stayed identity-on-domain, ρt did not, and the `PermSim` relation
that note lists as a rejected alternative is obseq3's actual design. A
scope caveat was appended to that note rather than superseding it (the
v2 claim is correct for v2; the divergence is version-scoped).

## See also

- journal/2026-08-29-copy-fresh-dst.md — the increment that introduced
  `extendBlock` and `mirlite_readWordSeq_congr`
