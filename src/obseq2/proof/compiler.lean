import obseq2.proof.const_init
import obseq2.proof.copy
import obseq2.proof.ref

namespace obseq2.proof

open obseq2
open obseq2.compile
open obseq2.oseair (Instr Register Rhs Val)

-- One source step is simulated by finitely many target steps and CompilerInv is
-- re-established.
-- Proof plan (case split on stmt):
--   halt                    : Halt is a fixed point on both sides; 0 target steps.
--   assign dst (constInit v): delegated to CompilerInv_step_constInit.
--   assign dst (copy src)   : delegated to CompilerInv_step_copy.
--   assign dst (ref kind src): delegated to CompilerInv_step_ref.
theorem CompilerInv_step
    {Γ : Ctx}
    {cs0 : CompilerState}
    {prog : obseq2.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_mir' : obseq2.mirlite.State PermissionModel.stackedBorrows Γ}
    {s_osea : oseair.State}
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    (h_step : obseq2.mirlite.step PermissionModel.stackedBorrows s_mir prog
                = obseq2.mirlite.Result.ok s_mir') :
    ∃ (s_osea' : oseair.State) (n : Nat),
      oseair.runN n s_osea (compileProgFrom cs0 prog) = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa ρt s_mir' s_osea' := by
  simp only [obseq2.mirlite.step] at h_step
  split at h_step
  · rename_i stmt h_get
    cases stmt with
    | halt =>
        simp only [obseq2.mirlite.stepStmt] at h_step
        simp at h_step; subst h_step
        exact ⟨s_osea, 0, by simp [oseair.runN], h_inv⟩
    | assign dst rhs =>
        cases rhs with
        | constInit v =>
            exact CompilerInv_step_constInit v h_inv h_get h_step
        | copy src =>
            exact CompilerInv_step_copy h_inv h_get h_step
        | ref kind src =>
            exact CompilerInv_step_ref kind h_inv h_get h_step
  · simp at h_step; subst h_step
    exact ⟨s_osea, 0, by simp [oseair.runN], h_inv⟩

-- Main compiler correctness theorem.
-- For every n-step source execution producing s_mir', the compiled target
-- reaches a corresponding s_osea' in finitely many steps, and CompilerInv
-- relates the two final states.
-- Key observable consequence: SourceMemSim inside CompilerInv guarantees
-- that target memory at ρa(addr) agrees with source memory at addr.
-- Proof: induction on n. Base case is trivial. Succ case applies
-- CompilerInv_step (for the single source step) then the IH (for the
-- remaining n steps), composing the target runs with oseair_runN_add.
theorem compile_correct
    {Γ : Ctx}
    {prog : obseq2.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_mir' : obseq2.mirlite.State PermissionModel.stackedBorrows Γ}
    {s_osea : oseair.State}
    (n : Nat)
    (h_run : obseq2.mirlite.runN PermissionModel.stackedBorrows n s_mir prog
               = obseq2.mirlite.Result.ok s_mir')
    (h_inv : CompilerInv (initialState Γ) prog ρa ρt s_mir s_osea) :
    ∃ (s_osea' : oseair.State) (m : Nat),
      oseair.runN m s_osea (compileProg prog) = oseair.Result.Ok s_osea' ∧
      CompilerInv (initialState Γ) prog ρa ρt s_mir' s_osea' := by
  induction n generalizing s_mir s_osea with
  | zero =>
      simp [obseq2.mirlite.runN] at h_run
      exact ⟨s_osea, 0, by simp [oseair.runN], h_run ▸ h_inv⟩
  | succ n ih =>
      simp only [obseq2.mirlite.runN] at h_run
      split at h_run
      · -- halt: runN short-circuits, s_mir' = s_mir; zero target steps suffice.
        simp at h_run; subst h_run
        exact ⟨s_osea, 0, by simp [oseair.runN], h_inv⟩
      · -- none: runN short-circuits, s_mir' = s_mir; zero target steps suffice.
        simp at h_run; subst h_run
        exact ⟨s_osea, 0, by simp [oseair.runN], h_inv⟩
      · -- real step: use CompilerInv_step then IH.
        rename_i stmt h_get
        split at h_run
        · -- stepStmt succeeded; h_run is now runN n s_mid prog = .ok s_mir'.
          rename_i s_mid h_step_eq
          have h_step : obseq2.mirlite.step PermissionModel.stackedBorrows s_mir prog
              = obseq2.mirlite.Result.ok s_mid := by
            simp [obseq2.mirlite.step, h_get, h_step_eq]
          obtain ⟨s_osea_mid, k, h_target_k, h_inv_mid⟩ := CompilerInv_step h_inv h_step
          obtain ⟨s_osea', m, h_target_m, h_inv'⟩ := ih h_run h_inv_mid
          exact ⟨s_osea', k + m,
            (oseair_runN_add k m s_osea (compileProg prog) s_osea_mid h_target_k).trans
              h_target_m,
            h_inv'⟩
        · -- stepStmt errored: contradicts h_run : ... = .ok.
          simp at h_run

end obseq2.proof
