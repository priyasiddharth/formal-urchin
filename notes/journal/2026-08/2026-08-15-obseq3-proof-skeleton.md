# obseq3 compiler-correctness proof skeleton (PermSim, 8 audited sorries)

[OBS 2026-08-15] `src/obseq3/proof/` landed (Obseq3Proof lib, not in the
default target, mirroring Obseq2Proof): `common.lean` (~1290 lines),
`const_write/copy/ref.lean`, `compiler.lean`. **Both top-level theorems —
`CompilerInv_step` and `compile_correct` — are fully proved**, complete
modulo exactly 8 audited sorries (the audit lives at the top of
`proof/compiler.lean` with a suggested closing order).

## The headline: obseq2's invariant conjunct 6 was wrong

[FACT] obseq2's `s_osea.ap = s_mir.perms` (literal equality) is false
beyond local-only places: internal borrows mint tags, `die` pops items but
never rolls back `NextTag`, and once the counters split every subsequent
corresponding borrow carries DIFFERENT tag values on the two machines —
so even component-wise `StackMap` equality fails. obseq2 never noticed
because the equality is only ever *consumed* before any internal mint and
only ever *re-established* inside its three sorries. The v3 invariant
replaces it with **`PermSim ρt`**: item-wise ρt-renamed stack equality
(position- and constructor-preserving, so SRW-grouping/Disabled structure
is identical), renamed `protFrames`/`exposed`, `NextTag ≤`. ρt is
`TagRenameWF` (injective + fixes `wildcardTag`), no longer identity; ρa
stays `IdentityOnDomain` (addresses are lockstep).

[FACT] ρt-injectivity and `Die` are orthogonal: ρt absorbs tag-VALUE
divergence, `Die` collapses stack-STRUCTURE divergence (extra items with
no source counterpart) at each statement boundary. Dropping `Die` would
force junk-tolerance conditions into every SB-op lemma (the v1-`sb_sim`-
sized corpus) — recorded, not taken.

## What ported clean vs what is sorried

Fully proved (~85% of common.lean): §A prefix/`csAt`/`targetLabelAt`
machinery, `CoreProg` scoping (replaces obseq2's SupportedStmt — the v3
compiler is total, so the predicate scopes the THEOREMS), §B mem-effect
statics re-cased over the v3 instruction set (`SkipIf` excluded from
`InstrPreservesMem`: it branches), §C vocabulary incl. `PermSim` +
`rename_mono` (via a local `ListRel` — no Mathlib `Forall₂` here), §D
lowering-totality incl. the new `ensurePlaceRoot_run_eq_of_mapped`, §E
emit-preserves-mem leaves, §F `runN_allDie_preserves`/`runN_cleanupInstrs`
(cleanup now `(Register × Nat)`), §G framing + `oseair_runN_add`;
`const_write_stmt_evidence` (both resolved cases, riding
`ensurePlaceRoot_run_eq_of_mapped`), `prepare_local_assign_resolves`,
`CompilerInv_step_constWrite`'s full delegation structure.

The 8 sorries: 3 simulation leaves (const_write resolved / copy / ref),
3 bridges (`sb_ref_use_die_cancels` — the keystone stated as
ref-then-use-then-die ≡ the bare parent access up to NextTag;
`writeThroughPtr_sim` range version; `sb_write_respects_PermSim`),
2 mechanical (`placeToRegChecked_emits_preserves_mem` induction glue;
const_write_stmt_evidence's fresh-root-proj branch — NEW in v3 because
`allocateRoot` recurses through projections for aggregate desugar,
a case obseq2's prepare simply erred on).

[HYP] Closing order 4→5→6→8→1→2→7→3 (audit numbering): the keystone
first — it is where obseq2's const_write sorry actually bottoms out.

Design change en route: `oseair.runNWith` reverted to v2's idle-fuel
semantics (the stuck-pc early stop broke `oseair_runN_add`'s statement;
nothing used it — harness and tests run their own loops).

**References:** obseq2-comparison.md 2026-08-15 entry, proof/compiler.lean
audit, loose-ends/parked.md ("obseq3 proof closure").
