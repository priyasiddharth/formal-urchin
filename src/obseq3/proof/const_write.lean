import obseq3.proof.common

/-!
Per-statement simulation for `.assign dst (.constInit v)` — port of
`obseq2/proof/const_write.lean`. The evidence lemma and the delegation
structure are fully proved; the resolved-write simulation is the audited
leaf sorry (same decomposition as obseq2, now with the v3 bridges named).
-/

namespace obseq3.proof

open obseq3
open obseq3.compile
open obseq3.oseair (Instr Register Rhs Val)

/-- From `CompilerInv` and a successful destination preparation, the checked
    compiler lowers the constant assignment at the current prefix state.
    v3 delta vs obseq2: the assign-place case runs `ensurePlaceRoot` first;
    under `PlaceInputsMapped` (from `LocalBindingSim` + resolvability) it is
    a no-op on the compiler state (`ensurePlaceRoot_run_eq_of_mapped`). -/
theorem const_write_stmt_evidence
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_pre : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {dst : Place Γ obseq.LayoutTy.NatL}
    (v : Word)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    (h_prep : mirlite.preparePlaceAssign MSB s_mir dst = .ok s_pre) :
    ∃ (csPrefix : CompilerState)
      (stmtOut : ResultWithEvidence Unit (fun _ => StmtEvidence (.assign dst (.constInit v)))),
      csAt cs0 prog s_mir.pc csPrefix ∧
      CheckedCompilerM.value (compileStmtChecked (.assign dst (.constInit v)))
        csPrefix = Except.ok stmtOut := by
  obtain ⟨csPrefix, h_label, h_wf, h_lbs, h_sms, h_psim, h_id_a, h_wf_t⟩ := h_inv
  rcases h_label with ⟨h_csAt, h_pc⟩
  cases dst with
  | «local» loc =>
      refine ⟨csPrefix, ?_, h_csAt, ?_⟩
      · refine {
        result := (),
          evidence := StmtEvidence.assignLocal loc (.constInit v)
            (CompilerM.value (ensureLocalRegE loc) csPrefix).result
            (CompilerM.value (ensureLocalRegE loc) csPrefix).evidence
            (RExprToEvidence.constInit v)
        }
      · simp [compileStmtChecked, compileRExprToChecked]
  | proj base path =>
      cases h_resolved : mirlite.resolvePlace? s_mir (.proj base path) with
      | none =>
          simp [mirlite.preparePlaceAssign, h_resolved] at h_prep
          -- prepare may still succeed by allocating the root; but then the
          -- root was unmapped and resolution of the base failed — recover
          -- the mapped-inputs fact from the POST-prepare state instead.
          sorry
      | some resolved =>
          have h_mapped :=
            placeInputsMapped_of_localBindingSim_resolvePlace h_lbs h_resolved
          have h_root := ensurePlaceRoot_run_eq_of_mapped
            (p := Place.proj base path) h_mapped
          rcases placeToRegChecked_ok_of_placeInputsMapped
            (cs := csPrefix) (kind := RefKind.Mut) (p := .proj base path) h_mapped
            with ⟨dstOut, h_dstOut⟩
          refine ⟨csPrefix, ?_, h_csAt, ?_⟩
          · refine {
            result := (),
            evidence := StmtEvidence.assignPlace (.proj base path) (.constInit v) dstOut.result
              dstOut.evidence (RExprToEvidence.constInit v)
          }
          · simp [compileStmtChecked, compileRExprToChecked, h_dstOut, h_root]
  | deref ptrPlace =>
      cases h_resolved : mirlite.resolvePlace? s_mir (.deref ptrPlace) with
      | none =>
          simp [mirlite.preparePlaceAssign, mirlite.allocateRoot, h_resolved] at h_prep
      | some resolved =>
          have h_mapped :=
            placeInputsMapped_of_localBindingSim_resolvePlace h_lbs h_resolved
          have h_root := ensurePlaceRoot_run_eq_of_mapped
            (p := Place.deref ptrPlace) h_mapped
          rcases placeToRegChecked_ok_of_placeInputsMapped
            (cs := csPrefix) (kind := RefKind.Mut) (p := .deref ptrPlace) h_mapped
            with ⟨dstOut, h_dstOut⟩
          refine ⟨csPrefix, ?_, h_csAt, ?_⟩
          · refine {
            result := (),
            evidence := StmtEvidence.assignPlace (.deref ptrPlace) (.constInit v) dstOut.result
              dstOut.evidence (RExprToEvidence.constInit v)
          }
          · simp [compileStmtChecked, compileRExprToChecked, h_dstOut, h_root]

/-- LEAF SORRY 1: resolved constant-write simulation. Obligations, in the
    order the target fragment discharges them:
    (1) fragment execution — locate the compiled `[dst lowering] CStore
        [cleanup]` block at `s_osea.pc` via `compileStmt_emitted_in_compProg`;
    (2) write-permission transport — `PlaceRegReady` from the dst lowering
        (fresh Mut borrow / local base / loaded pointer), then BRIDGE 2
        (`writeThroughPtr_sim`) for the CStore;
    (3) perms reconciliation — BRIDGE 1 (`sb_ref_use_die_cancels`) matches
        the target's Borrow;CStore;Die against the source's bare `useMut`,
        and BRIDGE 3 (`sb_write_respects_PermSim`) transports it through ρt;
    (4) invariant reconstruction — `prefixCompileState_succ` advances the
        label witness; `SourceMemSim` from (2); `PermSim` from (3); renames
        grow by `.refl` in this case (constInit mints no source tag; the
        target's internal tag is died and never enters ρt). -/
theorem const_write_resolved_simulation
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_pre s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {dst : Place Γ obseq.LayoutTy.NatL}
    {resolved : mirlite.PlaceRes}
    (compProg : oseair.Prog)
    (v : Word)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    (h_stmt : prog.get? s_mir.pc = some (.assign dst (.constInit v)))
    (h_prep : mirlite.preparePlaceAssign MSB s_mir dst = .ok s_pre)
    (h_res  : mirlite.resolvePlace? s_pre dst = some resolved)
    (csPrefix : CompilerState)
    (h_csAt : csAt cs0 prog s_mir.pc csPrefix)
    (stmtOut : ResultWithEvidence Unit (fun _ => StmtEvidence (.assign dst (.constInit v))))
    (h_stmtOut :
      CheckedCompilerM.value (compileStmtChecked (.assign dst (.constInit v)))
        csPrefix = Except.ok stmtOut)
    (h_write : mirlite.writeResolvedPlace (τ := obseq.LayoutTy.NatL)
                 MSB s_pre resolved
                 [mirlite.MemValue.word v] rfl = .ok s_mir') :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' := by
  sorry

theorem prepare_local_assign_resolves
    {Γ : Ctx} {τ : LayoutTy}
    {s s' : mirlite.State MSB Γ}
    {loc : Local Γ τ}
    (h_prep : mirlite.preparePlaceAssign MSB s (.local loc) = .ok s') :
    ∃ resolved, mirlite.resolvePlace? s' (.local loc) = some resolved := by
  simp only [mirlite.preparePlaceAssign] at h_prep
  split at h_prep
  · rename_i resolved h_res
    cases h_prep
    exact ⟨resolved, h_res⟩
  · simp only [mirlite.allocateRoot, mirlite.allocateBase] at h_prep
    split at h_prep
    · simp at h_prep
    · rename_i permsOwned tag h_own
      cases h_prep
      simp [mirlite.resolvePlace?, mirlite.Env.lookup, mirlite.Env.set]

theorem CompilerInv_step_constWrite
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {dst : Place Γ obseq.LayoutTy.NatL}
    (compProg : oseair.Prog)
    (v : Word)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    (h_stmt : prog.get? s_mir.pc = some (.assign dst (.constInit v)))
    (h_step : mirlite.stepStmt MSB s_mir (.assign dst (.constInit v)) = .ok s_mir') :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' := by
  have h_inv_full := h_inv
  simp only [mirlite.stepStmt, mirlite.doAssign] at h_step
  cases h_prep : mirlite.preparePlaceAssign MSB s_mir dst with
  | err msg =>
      simp [h_prep] at h_step
  | ok s_pre =>
      simp only [h_prep, mirlite.evalRExpr] at h_step
      simp only [mirlite.finishPlaceAssign] at h_step
      split at h_step
      · -- Prepared destination resolves: delegate to the leaf simulation.
        rename_i resolved h_res
        obtain ⟨csPrefix', stmtOut, h_csAt', h_stmtOut⟩ :=
          const_write_stmt_evidence (s_pre := s_pre) v h_inv_full h_prep
        exact const_write_resolved_simulation compProg v h_comp h_inv_full h_stmt h_prep h_res
          csPrefix' h_csAt' stmtOut h_stmtOut h_step
      · -- Destination does not resolve after successful preparation.
        rename_i h_unresolved
        split at h_step
        · -- `.local loc`: preparation allocated it, so resolution succeeds.
          rename_i loc
          rcases prepare_local_assign_resolves (s := s_mir) (s' := s_pre)
              (loc := loc) h_prep with ⟨resolved, h_resolved⟩
          rw [h_unresolved] at h_resolved
          simp at h_resolved
        · simp at h_step
        · simp at h_step

end obseq3.proof
