# ref: the last unbound-root site — reconnaissance

Date: 2026-08-31
Tags: obseq3, ref, regime-B, spine, mother-lemma, parked

## what is left

`dst := &kind *chain` with `dst`'s root UNBOUND — the fourth and last
unbound-destination-root site of `ref`. The other three closed today
(`ref_fresh_projsrc_simulation`, `ref_projzero_fresh_simulation`,
`ref_projoffset_fresh_simulation`).

## [FACT] the compiled side is DONE

`compileStmt_ref_fresh_derefsrc_run/_value` are landed and green,
generated from `compileStmt_ref_deref_run/_value` by swapping
`ensureLocalRegE_existing` for `ensureLocalRegE_fresh` and evaluating
the source's `placeToRegChecked` at the POST-`Alloc` compiler state

```
csA = setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 }
        [Assgn (R cs.nextReg) (Alloc (layoutToTyVal (PtrL τ)))])
        dstLoc.idx.1 (R cs.nextReg, PtrL τ)
```

Both compiled first try. The `RStore` goes through `R cs.nextReg`, the
root register.

## [HYP] the leaf crosses the fresh machinery with the MOTHER LEMMA

Unlike the previous three, this one does not cross fresh-root with an
extra instruction (BRIDGE 1) — it crosses it with
`ptrChain_lowering_sim`. That lemma takes ELEVEN hypotheses about the
state it starts from:

  `h_id_a h_wf_t h_spine kind cs s_osea resolved permsR h_dres h_tbd
   h_lbs h_prb h_sms h_psim h_pc h_instS`

and the fresh root means it must be applied at `csA` and at the
post-`Alloc` oseair state, under the EXTENDED ρa and ρt. So the leaf
must re-establish, MID-PROOF, what the other leaves only rebuild at the
end:

- `h_lbs` at (ρa', ρt', s1, s_oseaA, csA) — the destination is now
  bound and mapped, every other local survives ONE register insert and
  the `setPlaceInfo`. This is `ref_fresh_dst_simulation`'s rebuild
  code minus one insert.
- `h_prb` at `csA` — likewise, one fresh register.
- `h_sms` — `mirlite.allocate`/`oseair.allocate` bump `addrStart` and
  leave contents alone, so `SourceMemSim.rename_mono` should carry it;
  `ref_fresh_dst_simulation` already passes exactly this shape to
  `writeThroughPtr_sim`, which is evidence it goes through.
- `h_psim`/`h_wf`/`h_tbd` — the `sb_own` outputs.
- `h_pc` — `s_osea.pc + 1 = csA.nextLabel`, arithmetic.
- `h_instS` — one extra `emit_code_lt_nextLabel` peel for the `Alloc`.

Everything after the mother lemma is `ref_deref_local_simulation`
shifted by one instruction, with the `RStore`'s destination register
being the root rather than a pre-existing `dstReg`, and the store's
`writeThroughPtr_sim` targeting the freshly allocated binding.

Estimated size: ~450 lines, of which ~150 are the mid-proof
re-establishment. That is the same magnitude as
`ref_projoffset_fresh_simulation`, which the splice method took to
green with one error — so the method carries, but the seam is
different: there the splice point was "mirlite write inversion before
the fragment"; here it is "invariant re-establishment before the
mother lemma".

## state

Build green; 17/17 + 91/91; audit exact at ONE sorry. Residual call
sites still 9 — this commit adds only the compiled side, no leaf, so
no site closes.
