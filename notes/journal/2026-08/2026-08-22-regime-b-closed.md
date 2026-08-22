# Regime B closed: the fresh local, and the only regime that grows BOTH renames

[FACT] `const_write_fresh_local_simulation` (proof/const_write.lean) is
proved. A constant write to an UNBOUND local — mirlite's
`preparePlaceAssign` allocates it, and the compiled fragment is two
instructions, the root `Alloc` that `ensureLocalRegE` emits followed by the
`CStore` — is simulated end to end. Audit 5 → 4, the first drop since
2026-08-21. Every other regime leaves ρa and ρt alone or grows one of
them; this is the only one that grows both.

[FACT] ρa's extension needs NO freshness side condition, unlike ρt's. For
ρt, `TagRenameBounded` is load-bearing twice over (range bound for
injectivity, domain bound so the extension is not an overwrite). For ρa,
`IdentityOnDomain` does both jobs by itself: if the fresh address were
already mapped, it would already be mapped to ITSELF, so extending at
`a ↦ a` is trivially a growth and trivially still injective-as-identity.
`AddrRenameIncr.extend_id` takes only `IdentityOnDomain`. The asymmetry is
worth remembering — the identity discipline on ρa (durable/
rho-maps-are-identity-on-domain.md) pays for itself precisely here.

[FACT] The proof needed a TENTH `CompilerInv` conjunct,
`UnboundLocalsUnmapped env cs`: a local the source has not bound is not
mapped by the compiler either. This is `LocalBindingSim`'s converse on the
mapping component, and regime B cannot start without it — without it the
fragment might be the bare `CStore` of regime A rather than
`Alloc; CStore`, and nothing in the invariant said which. Source
`preparePlaceAssign` and target `ensureLocalRegE` allocate the root at the
same statement, so the two notions of "exists yet" genuinely do agree; the
invariant just had to say so.

[OBS 2026-08-22] The prediction from the `AllocLockstep` increment held:
regime B was indeed the THIRD `CompilerInv` construction site, and the
conjunct it needed cost three bullets instead of two. Sequencing lesson
confirmed: wire conjuncts BEFORE closing the leaf that adds a site.

[EMP] (Lean 4.28) potholes:
- An implicit state argument that appears only under a PROJECTION
  (`s_pre.mem` in `writeThroughPtr_sim`'s `h_sms`) cannot be solved by
  unification from that argument. Passing the term directly assigned the
  WRONG state; wrapping it as `(by exact …)` — so the expected type is
  known first — fixes it, as does naming the state with `(s_osea := …)`.
  Rule of thumb: for a lemma whose implicit is only ever projected, pin it
  explicitly.
- `rw` with a `getPlaceInfo`-shaped lemma fails after `simp only
  [getPlaceInfo]` has already unfolded it to `List.lookup`. Keep the
  abstraction: `getPlaceInfo_emit` (an `rfl` lemma) instead of unfolding.
- The dependent local case needs `τ' = NatL` derived from
  `loc'.idx = loc.idx` via the two `hTy` fields
  (`rw [← loc'.hTy, h_idx, loc.hTy]`), then `subst`. `Local` carries its
  type proof, so the index really does determine the type — but only if
  you go through `hTy`.
- `omega` cannot see through `RegisterBelow` (a match-defined `Prop`) or
  `List.length` on a literal; unfold/`simp only` first.

[OPEN] Remaining audit (4): the two `Borrow`-emitting const_write regimes
(proj, deref-nonspine), copy (bidirectional memory relation + Memcpy exec
lemma), and the ref leaf. All four are leaf-local proof work; the SB
machinery is complete.

Validation: units 15/15 + 38/38, suite pass 77 | fail 0 (117),
differential matched 77 | mismatch 0 | skipped 0, obseq2 green. Proof
layer only. `#print axioms const_write_fresh_local_simulation`: propext /
Classical.choice / Quot.sound.

**References:** proof/compiler.lean (audit),
2026-08-22-alloclockstep-wired.md, 2026-08-22-sb-own-member.md,
durable/rho-maps-are-identity-on-domain.md.
