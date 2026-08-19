import obseq3.proof.const_write
import obseq3.proof.copy
import obseq3.proof.ref

/-!
Top-level compiler-correctness theorems for the proof-core fragment
(`CoreProg`: halt / assign with constInit/copy/ref), port of
`obseq2/proof/compiler.lean`. Both theorems are complete modulo the audited
sorries below.

## SORRY AUDIT (the skeleton's obligation graph)

CLOSED:
- ✔ BRIDGE 1 `sb_ref_use_die_cancels` (proof/keystone.lean, 2026-08-15):
  Borrow(Mut);use;Die ≡ the bare parent access up to NextTag, via the
  `setChain` normal form for move-to-front assoc-list folds.
- ✔ BRIDGE 2 `writeThroughPtr_sim` (proof/common.lean §G, 2026-08-18):
  range memory-write simulation via `SourceMemSim.writeWordSeq_extend`.
- ✔ BRIDGE 3 `sb_write_respects_PermSim` (proof/permsim_transport.lean,
  2026-08-18): the ρt-transport family (ListRel transports, beq/Item
  transports, splitStack/firstProtectedIn/writeCellContent transports,
  relational setChain) — non-wildcard acting tags (core programs cannot
  mint wildcards; resolveWildcardIn transport deferred with the
  non-core constructs).
- ✔ `placeToRegChecked_emits_preserves_mem` (common.lean §E, 2026-08-18).

Remaining (5, decomposed 2026-08-18 — the const-write leaf split into
regimes with REGIME A CLOSED): every remaining sorry is blocked on a
NAMED invariant extension, which is the next design increment:
1. `const_write_fresh_local_simulation` — needs the lockstep-allocation
   conjunct (`s_osea.mem.addrStart = s_mir.mem.addrStart`) so ρa extends
   at the equal fresh address, plus the `sb_own` transport member.
2. `const_write_proj_simulation` — needs the strengthened
   `CompilerStateWF` (placeRegMap register bound, temp-collision freedom)
   and composes BRIDGE 1 with BRIDGE 3.
3. `const_write_deref_simulation` — needs SB-env coherence (bound
   locals' cells carry stacks in which the binding tag grants access)
   for the `Load`'s read-through-own success.
4. `CompilerInv_step_copy` — the `sb_read` transport member now EXISTS
   (`sb_read_respects_PermSim`, 2026-08-19); still needs a bidirectional
   memory relation (source-absent cells read as undef; one-directional
   `SourceMemSim` does not constrain the target there) plus the Memcpy
   execution lemma.
5. `CompilerInv_step_ref` — needs the `sb_ref` transport member (extends
   ρt at the fresh pair) and the tag-bound WF fact (mapped and stack
   tags < NextTag on both machines) for injectivity of the extension;
   its `Die` cleanup transport now exists (`sb_die_respects_PermSim`).

CLOSED in the leaf layer (2026-08-18):
- ✔ `const_write_stmt_evidence` — total (fresh-root branch via
  `ensurePlaceRoot_maps_root`).
- ✔ `const_write_resolved_simulation` — proved delegation over regimes;
  REGIME A (bound local) closed end-to-end by
  `const_write_local_existing_simulation`: fragment located via
  `compileStmt_emitted_in_compProg` + `compileStmt_local_existing_run`,
  executed via BRIDGE 2, permissions transported via BRIDGE 3, invariant
  rebuilt (this is obseq2's long-parked "Step 4 regime-A milestone").
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
