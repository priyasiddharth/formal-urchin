# Transport family: sb_read and sb_die members land (write/read/die done)

[OBS 2026-08-19] `sb_read_respects_PermSim` and `sb_die_respects_PermSim`
proved in proof/permsim_transport.lean, mirroring the write member's
invert→transport→construct→relate shape over the fold machinery. New
pieces: `readCellContent` factored out of `readCell` in sb.lean
(behavior-preserving; suite re-verified 76/76), `ListRel.map` (the last
generic transport), `ItemSim.poppedByRead_eq`, and `ItemSim.disable_map`
— the read access's disable-in-place rewrite respects `ItemSim` because
`MutRef t ↦ Disabled t` maps related tags to related `Disabled` items
(the constructor-preserving design again).

[FACT] The transport family now covers `sb_write`/`sb_read`/`sb_die` —
the three ops that do NOT mint tags. The remaining members (`sb_ref`,
`sb_own`) both extend ρt at a fresh pair and are blocked on the same
tag-bound WF fact (mapped/stack tags < NextTag on both machines), which
is one of the named invariant extensions.

[EMP] (Lean 4.28) two textually identical `match` expressions written at
different sites compile to different matcher constants — `simp` will not
close their equality even when the display is identical; a trailing
`rfl` (defeq check unfolds matchers) does.

Copy's blocker list is now down to: bidirectional memory relation +
Memcpy execution lemma. Ref's Die-cleanup transport exists.

**References:** proof/compiler.lean audit, 2026-08-18-regime-a-closed.md.
