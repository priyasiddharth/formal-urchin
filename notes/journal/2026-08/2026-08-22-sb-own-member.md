# `sb_own` closes the BRIDGE 3 family — and the prediction held

[FACT] `sb_own_respects_PermSim` (proof/permsim_transport.lean) is proved.
The BRIDGE 3 transport family is now COMPLETE over all five range ops:
`sb_write`/`sb_read`/`sb_die` (ρt fixed) and `sb_ref`/`sb_own` (ρt grows
at the fresh pair). No SB operation in the proof core is now without a
transport.

[OBS 2026-08-22] The morning's [HYP] — "`sb_own` will reuse the `sb_ref`
increment wholesale and cost a fraction of it" — held, and precisely:
`TagRenameWF.extend`, `TagRenameIncr.extend`, `TagRenameBounded.extend`,
`PermSim.rename_mono`, `setChain_chain_respects` and the fold
characterizations all applied verbatim; the member compiled on the first
attempt. Cost: ~200 lines against `sb_ref`'s day, and — unlike `sb_ref` —
NO model factoring was needed, because `ownCell` was already a named
top-level cell op rather than an inline `match` inside the range op.
Promote the design lesson: *the shape of the model determines whether a
transport is a morning or a day.* `sb_ref` needed `refCellOp` extracted
before anything could be said about it under a `RefKind` variable;
`sb_own` needed nothing.

[FACT] One genuine difference, and it is the interesting part: `ownCell`
is the only cell op that SUCCEEDS on a missing stack — it is what creates
the cell. So it does not fit `foldCells_ok_inv`, whose `C` takes a
`BorrowStack` and whose `msgNone` hard-codes failure on absence. The
indexed fold's characterizations DO take an `Option BorrowStack`, so the
fix was a bridge rather than a duplicate: `foldCells_ok_iff_foldCellsIdx_ok`
(keystone.lean). The two folds are NOT equal as functions — they decorate
errors differently (`foldCells` names the failing address,
`foldCellsIdx` the offset) — but they agree on success, which is all any
consumer needs. Stating the iff instead of an equality is what made it a
20-line induction.

[FACT] Cell absence transports: `SB.find?_none_transport`. `PermSim`
relates stack maps positionally (`ListRel (CellSim ρt)`), so the two
machines have the same keys in the same order and absence is a shared
property. Together with `SB.find?_transport` this covers both branches of
`ownCellStep`, and both branches land on the same conclusion — the
singleton root stack with each machine's own fresh tag.

[OPEN] `const_write_fresh_local_simulation` (regime B) now has exactly ONE
machinery blocker left: the lockstep-allocation conjunct
`s_osea.mem.addrStart = s_mir.mem.addrStart`, which `CompilerInv` does not
carry. That is what lets ρa extend at the EQUAL fresh address; without it
the two machines' fresh allocations are unrelated and `MemValSim` cannot
be re-established for the new cell. Expect the wiring to be as cheap as
`TagRenameBounded`'s was (two construction sites, both untouched by an
allocation-free fragment) — see 2026-08-22-tagrenamebounded-wired.md.

Validation: units 15/15 + 38/38, suite pass 77 | fail 0 (117),
differential matched 77 | mismatch 0 | skipped 0, obseq2 green. Proof
layer only — no model files changed. Audit stays at 5 sorries.
`#print axioms sb_own_respects_PermSim`: propext / Classical.choice /
Quot.sound only.

**References:** proof/compiler.lean (audit),
2026-08-22-sb-ref-transport.md, 2026-08-22-tagrenamebounded-wired.md.
