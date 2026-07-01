# State snapshot: const_write sorry removal (imported from VSCode session)

Imported 2026-07-01 from VSCode session `6cb17359` (2026-06-16 →
2026-07-01) so the next session can pick up cold.

[OBS 2026-07-01] Three live sorries block `compile_correct`, which is
itself fully proved (as is `CompilerInv_step`):
- `const_write_resolved_simulation` — src/obseq2/proof/const_write.lean:87
- `CompilerInv_step_copy` — src/obseq2/proof/copy.lean:9 (bare sorry)
- `CompilerInv_step_ref` — src/obseq2/proof/ref.lean:9 (bare sorry)
Build was green (19/19 jobs) with only those three expected warnings.

[OBS 2026-07-01] The 6-step landing plan (obseq2-comparison.md,
2026-06-17 entry) stands at **steps 1–3 complete**:
1. ✅ `IdentityOnDomain` + two `CompilerInv` conjuncts (now 9-conjunct);
   destructure sites in const_write.lean gained `h_id_a`/`h_id_t`.
2. ✅ Execution helpers in common.lean: `compileStmt_emitted_in_compProg`
   (fragment locator — thin wrapper, placement primitives
   `emit_code_at_new`/`compileProgFrom_code_eq_compileStmt` already
   existed), `runN_CStore_step`, `step_Die_preserves_reg`,
   `runN_allDie_preserves`, `runN_cleanupInstrs` (conditional form).
3. ✅ `writeThroughPtr_sim` + memory-framing helpers (`lookup_filter_ne`,
   `mirlite/oseair find?_write_self/_ne`, `*_writeWordSeq_single`,
   `stackedBorrows_useMut_eq_ok`).
4. ⏸ Regime-A already-mapped-local milestone (n=1, fragment =
   `[CStore]`) — **confirmed next step**; on hold for workflow reasons
   only (user switched to another project, 2026-07-01), not technical.
5. ⏳ `placeToRegChecked_run_sim` → proj/deref (shared with copy/ref).
6. ⏳ `const_write_fresh_local_simulation` (regime B, ρ extended).

[OBS 2026-07-01] Lemma split decision: regime A (existing write,
`resolvePlace? s_mir dst = some _`, ρ unchanged) stays in
`const_write_resolved_simulation`; regime B (fresh local, `allocateBase`
ran, ρ extends with identity entries) gets its own
`const_write_fresh_local_simulation`; dispatch in
`CompilerInv_step_constWrite` by casing on `resolvePlace?`.

[OBS 2026-07-01] The steps-1–3 code was uncommitted at VSCode-session
end (commit prepared but blocked by a model/permission outage).
Resolved later the same day in the terminal session: committed as
`9706889` (common.lean +269/-4, const_write.lean +4 lines changed).

Corrections captured during the session (pre-notebook, so recorded
here rather than as supersedes):
- The commented `runN_cleanupInstrs` stub asserted unconditional
  success — false, `sb_die` can fail. Landed as completion ⟹
  preservation. Misled-by: the stub was written as a wish-list before
  the Die semantics were pinned down.
- Stale dev-log claims found: `const_init.lean`'s 5-phase monadic
  skeleton no longer exists (file is `const_write.lean`, sorry is
  bare); the WF layer (`RegValWF`/`InstrWF`/`CompiledWF`) was never
  built — only a comment at common.lean:284 — so bounds are proved
  directly via the identity conjunct instead of statically from
  `PathTo`.
- `s_osea.ap = s_mir.perms` proved unnecessary for
  `writeThroughPtr_sim`'s proof; dropped from its signature.

## See also

- ../../durable/rho-maps-are-identity-on-domain.md
- ../../durable/writethroughptr-sim-is-place-kind-agnostic.md
- ../../durable/dont-port-v1-proofs-reconstruct-in-v2.md
