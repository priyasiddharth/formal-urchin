# writeThroughPtr_sim reuses verbatim for proj/deref — only hypothesis discharge differs

Load this when extending const-write to proj/deref, or starting the
copy/ref sorries.

[FACT] `writeThroughPtr_sim` (src/obseq2/proof/common.lean, proved
2026-06-17) never inspects the place kind — it works purely from
`resolved : PlaceRes`, `dstReg`, and `PlaceRegReady`. Interface (three
caller-dischargeable hypotheses): `IdentityOnDomain ρa`,
`h_le : resolved.allocBase ≤ resolved.addr`,
`h_dom : ρa resolved.addr = some resolved.addr`. It deliberately does
NOT reconcile `s_osea'.ap = s_mir'.perms` — that is the caller's job
and is case-dependent. (`s_osea.ap = s_mir.perms` turned out
unnecessary for its proof and was dropped from the signature.)

[FACT] The proj/deref-specific work is hypothesis discharge plus
teardown (slated as `placeToRegChecked_run_sim`, shared with copy/ref):
- `PlaceRegReady`'s `useMut` witness comes from the *fresh borrow tag*
  the emitted `MutBorOffset` pushes (`sb_ref`), not from
  `LocalBindingSim` — the place fragment must run first.
- `h_dom` needs the computed `base.addr + pathOffset` shown in ρa's
  domain (a local gets it directly from `LocalBindingSim`).
- After the CStore, the two `ap`s differ by the fresh borrow; the `Die`
  cleanup pops it and restores the correspondence. For a local they
  already coincide (`t' = ρt(resolved.tag) = resolved.tag` under
  identity), which is why the local milestone closes with no cleanup.

[FACT] `runN_cleanupInstrs` is *conditional* — "run completes ⟹
mem/reg preserved, pc advances". Unconditional success is false:
each `Die` calls `sb_die`, which can fail. Die-success stays the
caller's obligation, where the borrow facts live.

## See also

- rho-maps-are-identity-on-domain.md
