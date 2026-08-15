import obseq3.proof.const_write
import obseq3.proof.copy
import obseq3.proof.ref

/-!
Top-level compiler-correctness theorems for the proof-core fragment
(`CoreProg`: halt / assign with constInit/copy/ref), port of
`obseq2/proof/compiler.lean`. Both theorems are complete modulo the audited
sorries below.

## SORRY AUDIT (the skeleton's obligation graph)

Simulation leaves (obseq2's three, restated against v3):
1. `const_write_resolved_simulation`  (const_write.lean) — fragment
   execution + BRIDGE 1/2/3 + invariant reconstruction.
2. `CompilerInv_step_copy`            (copy.lean) — needs the Memcpy/range
   analog of BRIDGE 2 and the read transport of BRIDGE 3.
3. `CompilerInv_step_ref`             (ref.lean) — the only ρt-growing case
   (fresh tags differ across machines under `PermSim`'s `NextTag ≤`).

Bridge lemmas (stated in common.lean §G):
4. `sb_ref_use_die_cancels`  — BRIDGE 1, the keystone obseq2 never wrote:
   Borrow(Mut);use;Die ≡ the bare parent access, up to NextTag.
5. `writeThroughPtr_sim`     — BRIDGE 2, range memory-write simulation.
6. `sb_write_respects_PermSim` — BRIDGE 3, SB-op transport through the
   ρt-renamed relation (family representative; read/die/ref analogs are
   consumed by leaves 2–3 and stated when closed).

Mechanical stragglers (documented in place):
7. `placeToRegChecked_emits_preserves_mem` (common.lean §E) — induction
   glue over the Checked combinators; all leaf lemmas proved.
8. one branch of `const_write_stmt_evidence` (const_write.lean) — the
   NEW-in-v3 fresh-root prepare of a projected destination (aggregate
   desugar); needs "placeToRegChecked succeeds after ensurePlaceRoot
   allocated the root".

Suggested closing order: 4 → 5 → 6 → 8 → 1 → 2 → 7 → 3.
-/

namespace obseq3.proof

open obseq3
open obseq3.compile
open obseq3.oseair (Instr Register Rhs Val)

/-- One source step is simulated by finitely many target steps and
    `CompilerInv` is re-established, for programs in the proof-core
    fragment. -/
theorem CompilerInv_step
    {Γ : Ctx}
    {cs0 : CompilerState}
    {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    (compProg : oseair.Prog)
    (h_core : CoreProg prog)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    (h_step : srcStep s_mir prog = .ok s_mir') :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' := by
  simp only [srcStep] at h_step
  split at h_step
  · -- halt: fixed point on both sides; zero target steps.
    simp at h_step; subst h_step
    exact ⟨ρa, ρt, s_osea, 0,
      AddrRenameIncr.refl ρa, TagRenameIncr.refl ρt,
      by simp [oseair.runN], h_inv⟩
  · -- off the end: source is stuck-ok; zero target steps.
    simp at h_step; subst h_step
    exact ⟨ρa, ρt, s_osea, 0,
      AddrRenameIncr.refl ρa, TagRenameIncr.refl ρt,
      by simp [oseair.runN], h_inv⟩
  · rename_i stmt h_ne h_get
    have h_stmt_core : CoreStmt stmt := h_core _ _ h_get
    cases stmt with
    | halt =>
        simp only [mirlite.stepStmt] at h_step
        cases h_step
        exact ⟨ρa, ρt, s_osea, 0,
          AddrRenameIncr.refl ρa, TagRenameIncr.refl ρt,
          by simp [oseair.runN], h_inv⟩
    | assign dst rhs =>
        cases rhs with
        | constInit v =>
            exact CompilerInv_step_constWrite compProg v h_comp h_inv h_get h_step
        | copy src =>
            exact CompilerInv_step_copy compProg h_comp h_inv h_get h_step
        | ref kind prot mask src =>
            exact CompilerInv_step_ref kind prot mask compProg h_comp h_inv h_get h_step
        | ptrCast src => exact absurd h_stmt_core (by simp [CoreStmt, CoreRhs])
        | ptrOffset src d => exact absurd h_stmt_core (by simp [CoreStmt, CoreRhs])
        | refSlice k p src => exact absurd h_stmt_core (by simp [CoreStmt, CoreRhs])
        | exposeAddr src => exact absurd h_stmt_core (by simp [CoreStmt, CoreRhs])
        | fromExposed src => exact absurd h_stmt_core (by simp [CoreStmt, CoreRhs])
        | uninit => exact absurd h_stmt_core (by simp [CoreStmt, CoreRhs])
    | assignIf discr val dst rhs => exact absurd h_stmt_core (by simp [CoreStmt])
    | alloc dst len => exact absurd h_stmt_core (by simp [CoreStmt])
    | dealloc p => exact absurd h_stmt_core (by simp [CoreStmt])
    | pushProtectors => exact absurd h_stmt_core (by simp [CoreStmt])
    | popProtectors => exact absurd h_stmt_core (by simp [CoreStmt])

/-- Main compiler-correctness theorem (forward simulation of successful
    source runs): every n-step source execution of a proof-core program is
    matched by a finite target execution, and `CompilerInv` relates the
    final states. The observable consequence lives in the invariant:
    `SourceMemSim` at renamed addresses and `PermSim` at renamed tags. -/
theorem compile_correct
    {Γ : Ctx}
    {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    (compProg : oseair.Prog)
    (n : Nat)
    (h_core : CoreProg prog)
    (h_comp : compileProg prog = Except.ok compProg)
    (h_run : mirlite.runN MSB n s_mir prog = mirlite.Result.ok s_mir')
    (h_inv : CompilerInv (initialState Γ) prog ρa ρt s_mir s_osea) :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (m : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB m s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv (initialState Γ) prog ρa' ρt' s_mir' s_osea' := by
  induction n generalizing ρa ρt s_mir s_osea with
  | zero =>
      simp [mirlite.runN] at h_run
      exact ⟨ρa, ρt, s_osea, 0,
        AddrRenameIncr.refl ρa, TagRenameIncr.refl ρt,
        by simp [oseair.runN], h_run ▸ h_inv⟩
  | succ n ih =>
      simp only [mirlite.runN] at h_run
      split at h_run
      · -- halt: runN short-circuits.
        simp at h_run; subst h_run
        exact ⟨ρa, ρt, s_osea, 0,
          AddrRenameIncr.refl ρa, TagRenameIncr.refl ρt,
          by simp [oseair.runN], h_inv⟩
      · -- none: runN short-circuits.
        simp at h_run; subst h_run
        exact ⟨ρa, ρt, s_osea, 0,
          AddrRenameIncr.refl ρa, TagRenameIncr.refl ρt,
          by simp [oseair.runN], h_inv⟩
      · -- real step: CompilerInv_step then the induction hypothesis.
        rename_i stmt h_ne h_get
        split at h_run
        · rename_i s_mid h_step_eq
          have h_step : srcStep s_mir prog = .ok s_mid := by
            unfold srcStep
            rw [h_get]
            cases stmt with
            | halt => exact (h_ne rfl).elim
            | assign dst rhs => exact h_step_eq
            | assignIf a b c d => exact h_step_eq
            | alloc a b => exact h_step_eq
            | dealloc a => exact h_step_eq
            | pushProtectors => exact h_step_eq
            | popProtectors => exact h_step_eq
          obtain ⟨ρa_mid, ρt_mid, s_osea_mid, k,
            hρa_step, hρt_step, h_target_k, h_inv_mid⟩ :=
            CompilerInv_step compProg h_core (by simpa [compileProg] using h_comp) h_inv h_step
          obtain ⟨ρa', ρt', s_osea', m,
            hρa_tail, hρt_tail, h_target_m, h_inv'⟩ :=
            ih h_run h_inv_mid
          exact ⟨ρa', ρt', s_osea', k + m,
            AddrRenameIncr.trans hρa_step hρa_tail,
            TagRenameIncr.trans hρt_step hρt_tail,
            (oseair_runN_add k m s_osea compProg s_osea_mid h_target_k).trans
              h_target_m,
            h_inv'⟩
        · simp at h_run

end obseq3.proof
