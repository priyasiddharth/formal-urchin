import obseq2.proof.common

namespace obseq2.proof

open obseq2
open obseq2.compile
open obseq2.oseair (Instr Register Rhs Val)

/-- If a constant assignment's destination has already been prepared successfully in
  MIRLite and the source/target states satisfy `CompilerInv`, then the checked
  compiler can lower that statement at the current prefix state.

  The conclusion packages both the relevant prefix compiler state at the current
  program counter and the `StmtEvidence` witness showing that
  `compileStmtChecked` returns `Except.ok`. -/
theorem const_write_stmt_evidence
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq2.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_pre : obseq2.mirlite.State PermissionModel.stackedBorrows Γ}
    {s_osea : oseair.State}
    {dst : Place Γ obseq.LayoutTy.NatL}
    (v : Word)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    (h_prep : obseq2.mirlite.preparePlaceAssign PermissionModel.stackedBorrows s_mir dst =
      .ok s_pre) :
    ∃ (csPrefix : CompilerState)
      (stmtOut : ResultWithEvidence Unit (fun _ => StmtEvidence (.assign dst (.constInit v)))),
      csAt cs0 prog s_mir.pc csPrefix ∧
      CheckedCompilerM.value (compileStmtChecked (.assign dst (.constInit v)))
        csPrefix = Except.ok stmtOut := by
  obtain ⟨csPrefix, h_label, h_wf, h_tlr, h_lbs, h_sms, h_ap, h_wf_perms, h_id_a, h_id_t⟩ := h_inv
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
        cases h_resolved : obseq2.mirlite.resolvePlace? s_mir (.proj base path) with
        | none =>
          simp [obseq2.mirlite.preparePlaceAssign, h_resolved] at h_prep
        | some resolved =>
          rcases placeToRegChecked_ok_of_resolvePlace
            (ρa := ρa) (ρt := ρt) (s_mir := s_mir) (s_osea := s_osea)
            (cs := csPrefix) (kind := RefKind.Mut) (p := .proj base path)
            h_lbs h_resolved
            with ⟨dstOut, h_dstOut⟩
          refine ⟨csPrefix, ?_, h_csAt, ?_⟩
          · refine {
            result := (),
            evidence := StmtEvidence.assignPlace (.proj base path) (.constInit v) dstOut.result
              dstOut.evidence (RExprToEvidence.constInit v)
          }
          · simp [compileStmtChecked, compileRExprToChecked, h_dstOut]
  | deref ptrPlace =>
        cases h_resolved : obseq2.mirlite.resolvePlace? s_mir (.deref ptrPlace) with
        | none =>
          simp [obseq2.mirlite.preparePlaceAssign, h_resolved] at h_prep
        | some resolved =>
          rcases placeToRegChecked_ok_of_resolvePlace
            (ρa := ρa) (ρt := ρt) (s_mir := s_mir) (s_osea := s_osea)
            (cs := csPrefix) (kind := RefKind.Mut) (p := .deref ptrPlace)
            h_lbs h_resolved
            with ⟨dstOut, h_dstOut⟩
          refine ⟨csPrefix, ?_, h_csAt, ?_⟩
          · refine {
            result := (),
            evidence := StmtEvidence.assignPlace (.deref ptrPlace) (.constInit v) dstOut.result
              dstOut.evidence (RExprToEvidence.constInit v)
          }
          · simp [compileStmtChecked, compileRExprToChecked, h_dstOut]

/-- Existing/resolved constant writes use the same simulation shell as obseq's
    `existing_write_simulation`: after MIR destination preparation has produced a
    resolvable place, the compiled fragment writes the same constant through the
    corresponding target pointer and rebuilds `CompilerInv`.

    This is intentionally factored out of `CompilerInv_step_constWrite`; the
    proof obligations are target-fragment execution, write permission transport,
    memory simulation after `CStore`, and invariant reconstruction. -/
theorem const_write_resolved_simulation
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq2.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_pre s_mir' : obseq2.mirlite.State PermissionModel.stackedBorrows Γ}
    {s_osea : oseair.State}
    {dst : Place Γ obseq.LayoutTy.NatL}
  (compProg : oseair.Prog)
    (v : Word)
  (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    (h_stmt : prog.get? s_mir.pc = some (.assign dst (.constInit v)))
    (h_prep : obseq2.mirlite.preparePlaceAssign PermissionModel.stackedBorrows s_mir dst =
                .ok s_pre)
    (h_res  : obseq2.mirlite.resolvePlace? s_pre dst = some resolved)
    (csPrefix : CompilerState)
    (h_csAt : csAt cs0 prog s_mir.pc csPrefix)
    (stmtOut : ResultWithEvidence Unit (fun _ => StmtEvidence (.assign dst (.constInit v))))
    (h_stmtOut :
      CheckedCompilerM.value (compileStmtChecked (.assign dst (.constInit v)))
        csPrefix = Except.ok stmtOut)
    (h_write : obseq2.mirlite.writeResolvedPlace (τ := obseq.LayoutTy.NatL)
                 PermissionModel.stackedBorrows s_pre resolved
                 [obseq2.mirlite.MemValue.word v] rfl = .ok s_mir') :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State) (n : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' := by
  sorry

theorem prepare_local_assign_resolves
    {Γ : Ctx} {τ : LayoutTy}
    {s s' : obseq2.mirlite.State PermissionModel.stackedBorrows Γ}
    {loc : Local Γ τ}
    (h_prep : obseq2.mirlite.preparePlaceAssign PermissionModel.stackedBorrows s
        (.local loc) = .ok s') :
    ∃ resolved, obseq2.mirlite.resolvePlace? s' (.local loc) = some resolved := by
  simp only [obseq2.mirlite.preparePlaceAssign] at h_prep
  split at h_prep
  · rename_i resolved h_res
    cases h_prep
    exact ⟨resolved, h_res⟩
  · simp only [obseq2.mirlite.allocateBase] at h_prep
    split at h_prep
    · simp at h_prep
    · rename_i ownedTag h_own
      cases h_prep
      simp [obseq2.mirlite.resolvePlace?, obseq2.mirlite.Env.lookup,
        obseq2.mirlite.Env.set]

theorem CompilerInv_step_constWrite
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq2.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_mir' : obseq2.mirlite.State PermissionModel.stackedBorrows Γ}
    {s_osea : oseair.State}
    {dst : Place Γ obseq.LayoutTy.NatL}
    (compProg : oseair.Prog)
    (v : Word)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    (h_stmt : prog.get? s_mir.pc = some (.assign dst (.constInit v)))
    (h_step : obseq2.mirlite.stepStmt PermissionModel.stackedBorrows s_mir
                (.assign dst (.constInit v)) = .ok s_mir') :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State) (n : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' := by
  have h_inv_full := h_inv
  obtain ⟨csPrefix, h_label, h_wf, h_tlr, h_lbs, h_sms, h_ap, h_wf_perms, h_id_a, h_id_t⟩ := h_inv
  rcases h_label with ⟨h_csAt, h_pc⟩
  simp only [obseq2.mirlite.stepStmt] at h_step
  cases h_prep :
      obseq2.mirlite.preparePlaceAssign PermissionModel.stackedBorrows s_mir dst with
  | err msg =>
      simp [h_prep] at h_step
  | ok s_pre =>
      -- After the new MIRLite order, destination preparation happens before RHS
      -- evaluation. For `constInit`, RHS evaluation is pure and the remaining source
      -- step is the final place write from `s_pre`.
      simp [h_prep, obseq2.mirlite.evalRExpr] at h_step
      simp only [obseq2.mirlite.finishPlaceAssign] at h_step
      split at h_step
      · -- Prepared destination resolves: existing write, or fresh local after allocation.
        rename_i resolved h_res
        obtain ⟨csPrefix', stmtOut, h_csAt', h_stmtOut⟩ :=
          const_write_stmt_evidence (s_pre := s_pre) v h_inv_full h_prep
        exact const_write_resolved_simulation compProg v h_comp h_inv_full h_stmt h_prep h_res
          csPrefix' h_csAt' stmtOut h_stmtOut h_step
      · -- Destination still does not resolve after successful preparation.
        -- This should be impossible for direct locals and remains an error for
        -- projections/dereferences whose base could not be prepared.
        rename_i h_unresolved
        split at h_step
        · -- `.local loc`: `preparePlaceAssign` allocated it, so resolve should succeed.
          rename_i loc
          rcases prepare_local_assign_resolves (s := s_mir) (s' := s_pre)
              (loc := loc) h_prep with ⟨resolved, h_resolved⟩
          rw [h_unresolved] at h_resolved
          simp at h_resolved
        · simp at h_step
        · simp at h_step

end obseq2.proof
