import obseq.proof.state_helpers

/-!
# `obseq.proof.const_existing`

Local compiler-correctness lemmas for the existing-destination word-constant
fragment.

This cluster follows the paper grammar again: `ConstOp` is word-only, so the
proved fragment here is exactly `place(base) ::= const n`.
-/

namespace obseq.proof

open obseq
open obseq.mirlite
open obseq.oseair hiding State Result
open obseq.compile
open scoped obseq.notation

theorem mem_vals_eq_word (n : Word) :
  mem_vals_eq [mirlite.MemValue.Val n] [oseair.Val.Dat n] := by
  exact mem_vals_eq.cons rfl mem_vals_eq.nil

structure ConstExistingCtx where
  base : Word
  reg : Register
  n : Word
  cs : CompilerState
  h_instrs : CompilerEmpty cs
  h_lookup : BaseReady cs base reg LayoutTy.NatL

namespace ConstExistingCtx

def stmt (ctx : ConstExistingCtx) : mirlite.Stmt :=
  place(ctx.base) ::= const ctx.n

def compiled (ctx : ConstExistingCtx) : oseair.Prog :=
  (compileStmt ctx.cs ctx.stmt).instrs

def mirStart (_ctx : ConstExistingCtx) (s_mir : mirlite.State) : mirlite.State :=
  { s_mir with pc := 0 }

def oseaStart (_ctx : ConstExistingCtx) (s_osea : oseair.State) : oseair.State :=
  { s_osea with pc := 0 }

theorem instrs_nil (ctx : ConstExistingCtx) : ctx.cs.instrs = [] :=
  ctx.h_instrs

end ConstExistingCtx

abbrev LocalSim
  (ctx : ConstExistingCtx)
  (s_mir : mirlite.State)
  (s_osea : oseair.State) : Prop :=
  StateSim ctx.cs.placeMap s_mir s_osea

/--
Source-side execution of `place(base) ::= const n` when the destination base is
already present in the MIR environment.
-/
theorem mirlite_step_const_existing_ok
  (s_mir : mirlite.State)
  (base addr tag n : Word)
  (ap' : AccessPerms)
  (h_env : s_mir.env.lookup base = some (addr, TyVal.NatTy, tag))
  (h_use : sb_use_mb s_mir.ap addr tag = SBResult.Ok ap') :
  mirlite.step { s_mir with pc := 0 } [place(base) ::= const n] =
    mirlite.Result.Ok
      { s_mir with
        ap := ap',
        mem := mirlite.writeWordSeq s_mir.mem addr [mirlite.MemValue.Val n],
        pc := 1 } := by
  simp [mirlite.step, obseq.notation.basePlace, obseq.notation.constRhs,
    mirlite.stepAssignConst, mirlite.finishPlaceAssign, mirlite.writeResolvedPlace,
    h_env, h_use, mirlite.writeWordSeq]

theorem mirlite_step_const_existing_inv
  (s_mir : mirlite.State)
  (base addr tag n : Word)
  (s_mir_next : mirlite.State)
  (h_env : s_mir.env.lookup base = some (addr, TyVal.NatTy, tag))
  (h_step :
    mirlite.step { s_mir with pc := 0 } [place(base) ::= const n] =
      mirlite.Result.Ok s_mir_next) :
  ∃ ap',
    sb_use_mb s_mir.ap addr tag = SBResult.Ok ap' ∧
    s_mir_next =
      { s_mir with
        ap := ap',
        mem := mirlite.writeWordSeq s_mir.mem addr [mirlite.MemValue.Val n],
        pc := 1 } := by
  cases h_use : sb_use_mb s_mir.ap addr tag with
  | Ok ap' =>
      have h_ok := mirlite_step_const_existing_ok s_mir base addr tag n ap' h_env h_use
      rw [h_ok] at h_step
      injection h_step with h_state
      exact ⟨ap', rfl, h_state.symm⟩
  | Err _ =>
      have : False := by
        simp [mirlite.step, obseq.notation.basePlace, obseq.notation.constRhs,
          mirlite.stepAssignConst, mirlite.finishPlaceAssign, mirlite.writeResolvedPlace,
          h_env, h_use, mirlite.writeWordSeq] at h_step
      contradiction

/--
Compiling the local constant fragment produces a singleton `CStore`.
-/
@[simp] theorem compile_const_existing
  (ctx : ConstExistingCtx) :
  compileStmt ctx.cs ctx.stmt =
    emit ctx.cs [oseair.Instr.CStore TyVal.NatTy [oseair.Val.Dat ctx.n] ctx.reg] := by
  have h_place :
      placeToReg ctx.cs { base := ctx.base, path := [] } mirlite.RefKind.Mut (some LayoutTy.NatL) =
        { reg := ctx.reg, layout := LayoutTy.NatL, cleanup := [], cs := ctx.cs } := by
    unfold placeToReg
    rw [ctx.h_lookup]
    simp [layoutResolvePath]
  unfold ConstExistingCtx.stmt compileStmt
  simp [obseq.notation.basePlace, obseq.notation.constRhs, h_place, emit, cleanupInstrs]

theorem ConstExistingCtx.compiled_eq
  (ctx : ConstExistingCtx) :
  ctx.compiled = [oseair.Instr.CStore TyVal.NatTy [oseair.Val.Dat ctx.n] ctx.reg] := by
  unfold ConstExistingCtx.compiled
  rw [compile_const_existing ctx, emit, ctx.instrs_nil]
  simp

/--
Target-side execution of the compiled singleton `CStore` fragment.
-/
theorem osea_step_const_existing_ok
  (s_osea : oseair.State)
  (addr tag n : Word)
  (reg : Register)
  (ap' : AccessPerms)
  (h_reg :
    s_osea.reg.lookup reg =
      some (TyVal.PTy, [oseair.Val.Ptr addr 0 (blockSize LayoutTy.NatL) tag]))
  (h_use : sb_use_mb s_osea.ap addr tag = SBResult.Ok ap') :
  oseair.step { s_osea with pc := 0 }
    [oseair.Instr.CStore TyVal.NatTy [oseair.Val.Dat n] reg] =
    oseair.Result.Ok
      { s_osea with
        ap := ap',
        mem := oseair.writeWordSeq s_osea.mem addr [oseair.Val.Dat n],
        pc := 1 } := by
  let instr := oseair.Instr.CStore TyVal.NatTy [oseair.Val.Dat n] reg
  unfold oseair.step oseair.writeThroughPtr
  have h_pc : ({ s_osea with pc := 0 }).pc < [instr].length := by
    exact Nat.succ_pos 0
  rw [dif_pos h_pc]
  have h_get : List.get [instr] ⟨0, h_pc⟩ = instr := by
    rfl
  rw [h_get]
  have h_in_bounds : addr < addr + blockSize LayoutTy.NatL := by
    have h_add : addr + 0 < addr + blockSize LayoutTy.NatL :=
      Nat.add_lt_add_left (by decide : 0 < blockSize LayoutTy.NatL) addr
    rw [Nat.add_zero] at h_add
    exact h_add
  have h_bound : ¬ addr >= addr + blockSize LayoutTy.NatL := by
    intro h_ge
    exact (Nat.lt_irrefl addr) (Nat.lt_of_lt_of_le h_in_bounds h_ge)
  simp [instr, h_reg, h_use, h_bound]

section ConstExisting

variable (ctx : ConstExistingCtx)
variable (s_mir : mirlite.State)
variable (s_osea : oseair.State)
variable (s_mir_next : mirlite.State)

/--
Local MIR-to-OSEA simulation for the existing-destination word-constant
fragment.

Strategy:
1. project the tracked `π` entry from `StateSim`,
2. invert the MIR step to recover the `sb_use_mb` witness,
3. replay the same permission update on the OSEA side, and
4. rebuild `StateSim` after the corresponding singleton writes.
-/
theorem local_simulation_const_existing
  (h_sim : LocalSim ctx s_mir s_osea)
  (h_mir_step :
    mirlite.step (ctx.mirStart s_mir) [ctx.stmt] =
      mirlite.Result.Ok s_mir_next) :
  ∃ s_osea_next,
    StepStar (ctx.oseaStart s_osea) ctx.compiled s_osea_next ∧
    LocalSim ctx s_mir_next s_osea_next := by
  let ⟨addr, tag, h_ptr, h_sim_mem⟩ := StateSim.place h_sim ctx.h_lookup
  have h_env : s_mir.env.lookup ctx.base = some (addr, TyVal.NatTy, tag) := h_ptr.2.1
  have h_reg :
      s_osea.reg.lookup ctx.reg =
        some (TyVal.PTy, [oseair.Val.Ptr addr 0 (blockSize LayoutTy.NatL) tag]) :=
    h_ptr.2.2
  have h_ap : s_mir.ap = s_osea.ap := StateSim.ap_eq h_sim
  have h_addrStart : s_mir.mem.addrStart = s_osea.mem.addrStart := StateSim.addrStart_eq h_sim
  have h_mir_step' :
      mirlite.step { s_mir with pc := 0 } [place(ctx.base) ::= const ctx.n] =
        mirlite.Result.Ok s_mir_next := by
    unfold ConstExistingCtx.mirStart ConstExistingCtx.stmt at h_mir_step
    exact h_mir_step
  let ⟨ap', h_use, h_next⟩ :=
    mirlite_step_const_existing_inv s_mir ctx.base addr tag ctx.n s_mir_next h_env h_mir_step'
  have h_valid_next_ap : SBValid ap' := by
    exact sb_use_mb_preserves_valid (StateSim.valid_mir h_sim) h_use
  have h_target_use : sb_use_mb s_osea.ap addr tag = SBResult.Ok ap' := by
    rw [← h_ap]
    exact h_use
  subst s_mir_next
  let s_mir_post :=
    { s_mir with
      ap := ap',
      mem := mirlite.writeWordSeq s_mir.mem addr [mirlite.MemValue.Val ctx.n],
      pc := 1 }
  let s_osea_post :=
    { s_osea with
      ap := ap',
      mem := oseair.writeWordSeq s_osea.mem addr [oseair.Val.Dat ctx.n],
      pc := 1 }
  have h_target_exec :
      StepStar (ctx.oseaStart s_osea) ctx.compiled s_osea_post := by
    rw [ctx.compiled_eq]
    exact StepStar.single (osea_step_const_existing_ok s_osea addr tag ctx.n ctx.reg ap' h_reg h_target_use)
  refine ⟨s_osea_post, h_target_exec, ?_⟩
  refine ⟨h_valid_next_ap, h_valid_next_ap, rfl, by simp [s_mir_post, s_osea_post, h_addrStart], ?_⟩
  · intro base reg layout h_lookup
    let ⟨addr0, tag0, h_ptr0, h_mem0⟩ := StateSim.place h_sim h_lookup
    refine ⟨addr0, tag0, ?_, ?_⟩
    · exact ⟨h_lookup, h_ptr0.2.1, h_ptr0.2.2⟩
    · exact sim_mem_at_write h_mem0 (mem_vals_eq_word ctx.n)

theorem local_preservation_const_existing
  (h_sim : LocalSim ctx s_mir s_osea)
  (h_mir_step :
    mirlite.step (ctx.mirStart s_mir) [ctx.stmt] =
      mirlite.Result.Ok s_mir_next) :
  ∃ s_osea_next,
    StepStar (ctx.oseaStart s_osea) ctx.compiled s_osea_next ∧
    LocalSim ctx s_mir_next s_osea_next ∧
    s_mir_next.ap = s_osea_next.ap := by
  let ⟨s_osea_next, h_steps, h_sim_next⟩ :=
    local_simulation_const_existing ctx s_mir s_osea s_mir_next h_sim h_mir_step
  exact ⟨s_osea_next, h_steps, h_sim_next, StateSim.ap_eq h_sim_next⟩

theorem local_validity_const_existing
  (h_sim : LocalSim ctx s_mir s_osea)
  (h_valid : SBValid s_mir.ap)
  (h_mir_step :
    mirlite.step (ctx.mirStart s_mir) [ctx.stmt] =
      mirlite.Result.Ok s_mir_next) :
  ∃ s_osea_next,
    StepStar (ctx.oseaStart s_osea) ctx.compiled s_osea_next ∧
    LocalSim ctx s_mir_next s_osea_next ∧
    s_mir_next.ap = s_osea_next.ap ∧
    SBValid s_mir_next.ap ∧
    SBValid s_osea_next.ap := by
  have h_pres :=
    local_preservation_const_existing ctx s_mir s_osea s_mir_next h_sim h_mir_step
  let ⟨addr, tag, h_ptr, _h_mem⟩ := StateSim.place h_sim ctx.h_lookup
  have h_env : s_mir.env.lookup ctx.base = some (addr, TyVal.NatTy, tag) := h_ptr.2.1
  have h_mir_step' :
      mirlite.step { s_mir with pc := 0 } [place(ctx.base) ::= const ctx.n] =
        mirlite.Result.Ok s_mir_next := by
    unfold ConstExistingCtx.mirStart ConstExistingCtx.stmt at h_mir_step
    exact h_mir_step
  let ⟨ap', h_use, h_next⟩ :=
    mirlite_step_const_existing_inv s_mir ctx.base addr tag ctx.n s_mir_next h_env h_mir_step'
  let ⟨s_osea_next, h_steps, h_sim_next, h_ap_eq⟩ := h_pres
  have h_valid_mir_next : SBValid s_mir_next.ap := by
    rw [h_next]
    exact sb_use_mb_preserves_valid h_valid h_use
  exact ⟨s_osea_next, h_steps, h_sim_next, h_ap_eq, h_valid_mir_next, StateSim.valid_osea h_sim_next⟩

theorem embedded_simulation_const_existing
  (prog_mir : mirlite.Prog)
  (prog_osea : oseair.Prog)
  (h_sim : LocalSim ctx s_mir s_osea)
  (h_mir_start : StartsAt prog_mir s_mir.pc [ctx.stmt])
  (h_osea_start : StartsAt prog_osea s_osea.pc ctx.compiled)
  (h_mir_step : mirlite.step s_mir prog_mir = mirlite.Result.Ok s_mir_next) :
  ∃ s_osea_next,
    StepStar s_osea prog_osea s_osea_next ∧
    LocalSim ctx s_mir_next s_osea_next := by
  let ⟨addr, tag, h_ptr, _h_mem⟩ := StateSim.place h_sim ctx.h_lookup
  have h_env : s_mir.env.lookup ctx.base = some (addr, TyVal.NatTy, tag) := h_ptr.2.1
  have h_reg :
      s_osea.reg.lookup ctx.reg =
        some (TyVal.PTy, [oseair.Val.Ptr addr 0 (blockSize LayoutTy.NatL) tag]) :=
    h_ptr.2.2
  have h_ap : s_mir.ap = s_osea.ap := StateSim.ap_eq h_sim
  have h_stmt_mir : prog_mir.get? s_mir.pc = some ctx.stmt := StartsAt.singleton h_mir_start
  rcases List.get?_eq_some_iff.mp h_stmt_mir with ⟨h_pc_mir, h_get_mir⟩
  unfold mirlite.step at h_mir_step
  rw [dif_pos h_pc_mir, h_get_mir] at h_mir_step
  cases h_use : sb_use_mb s_mir.ap addr tag with
  | Err _ =>
      simp [ConstExistingCtx.stmt, obseq.notation.basePlace, obseq.notation.constRhs,
        mirlite.stepAssignConst, mirlite.finishPlaceAssign, mirlite.writeResolvedPlace,
        h_env, h_use] at h_mir_step
  | Ok ap' =>
      have h_next_full :
          s_mir_next =
            { s_mir with
              ap := ap',
              mem := mirlite.writeWordSeq s_mir.mem addr [mirlite.MemValue.Val ctx.n],
              pc := s_mir.pc + 1 } := by
        simpa [ConstExistingCtx.stmt, obseq.notation.basePlace, obseq.notation.constRhs,
          mirlite.stepAssignConst, mirlite.finishPlaceAssign, mirlite.writeResolvedPlace,
          h_env, h_use, mirlite.writeWordSeq] using h_mir_step.symm
      let s_mir_local_next :=
        { s_mir with
          ap := ap',
          mem := mirlite.writeWordSeq s_mir.mem addr [mirlite.MemValue.Val ctx.n],
          pc := 1 }
      have h_target_use : sb_use_mb s_osea.ap addr tag = SBResult.Ok ap' := by
        rw [← h_ap]
        exact h_use
      have h_valid_next_ap : SBValid ap' := by
        exact sb_use_mb_preserves_valid (StateSim.valid_mir h_sim) h_use
      have h_stmt_osea :
          prog_osea.get? s_osea.pc =
            some (oseair.Instr.CStore TyVal.NatTy [oseair.Val.Dat ctx.n] ctx.reg) := by
        rw [ctx.compiled_eq] at h_osea_start
        simpa using StartsAt.singleton h_osea_start
      rcases List.get?_eq_some_iff.mp h_stmt_osea with ⟨h_pc_osea, h_get_osea⟩
      let s_mir_post :=
        { s_mir with
          ap := ap',
          mem := mirlite.writeWordSeq s_mir.mem addr [mirlite.MemValue.Val ctx.n],
          pc := s_mir.pc + 1 }
      let s_osea_post :=
        { s_osea with
          ap := ap',
          mem := oseair.writeWordSeq s_osea.mem addr [oseair.Val.Dat ctx.n],
          pc := s_osea.pc + 1 }
      have h_target_full :
          oseair.step s_osea prog_osea =
            oseair.Result.Ok
              s_osea_post := by
        unfold oseair.step
        rw [dif_pos h_pc_osea, h_get_osea]
        have h_in_bounds : addr < addr + blockSize LayoutTy.NatL := by
          have h_add : addr + 0 < addr + blockSize LayoutTy.NatL :=
            Nat.add_lt_add_left (by decide : 0 < blockSize LayoutTy.NatL) addr
          simpa using h_add
        have h_bound : ¬ addr >= addr + blockSize LayoutTy.NatL := by
          intro h_ge
          exact (Nat.lt_irrefl addr) (Nat.lt_of_lt_of_le h_in_bounds h_ge)
        simp [ctx.compiled_eq, s_osea_post, oseair.writeThroughPtr, h_reg, h_target_use, h_bound, Nat.add_assoc]
      refine ⟨s_osea_post, StepStar.single h_target_full, ?_⟩
      rw [h_next_full]
      refine ⟨h_valid_next_ap, h_valid_next_ap, rfl, ?_, ?_⟩
      · simpa [s_osea_post] using StateSim.addrStart_eq h_sim
      · intro base reg layout h_lookup
        let ⟨addr0, tag0, h_ptr0, h_mem0⟩ := StateSim.place h_sim h_lookup
        refine ⟨addr0, tag0, ?_, ?_⟩
        · exact ⟨h_lookup, h_ptr0.2.1, h_ptr0.2.2⟩
        · exact sim_mem_at_write h_mem0 (mem_vals_eq_word ctx.n)

theorem embedded_preservation_const_existing
  (prog_mir : mirlite.Prog)
  (prog_osea : oseair.Prog)
  (h_sim : LocalSim ctx s_mir s_osea)
  (h_mir_start : StartsAt prog_mir s_mir.pc [ctx.stmt])
  (h_osea_start : StartsAt prog_osea s_osea.pc ctx.compiled)
  (h_mir_step : mirlite.step s_mir prog_mir = mirlite.Result.Ok s_mir_next) :
  ∃ s_osea_next,
    StepStar s_osea prog_osea s_osea_next ∧
    LocalSim ctx s_mir_next s_osea_next ∧
    s_mir_next.ap = s_osea_next.ap := by
  let ⟨s_osea_next, h_steps, h_sim_next⟩ :=
    embedded_simulation_const_existing ctx s_mir s_osea s_mir_next
      prog_mir prog_osea h_sim h_mir_start h_osea_start h_mir_step
  exact ⟨s_osea_next, h_steps, h_sim_next, StateSim.ap_eq h_sim_next⟩

theorem embedded_validity_const_existing
  (prog_mir : mirlite.Prog)
  (prog_osea : oseair.Prog)
  (h_sim : LocalSim ctx s_mir s_osea)
  (h_valid : SBValid s_mir.ap)
  (h_mir_start : StartsAt prog_mir s_mir.pc [ctx.stmt])
  (h_osea_start : StartsAt prog_osea s_osea.pc ctx.compiled)
  (h_mir_step : mirlite.step s_mir prog_mir = mirlite.Result.Ok s_mir_next) :
  ∃ s_osea_next,
    StepStar s_osea prog_osea s_osea_next ∧
    LocalSim ctx s_mir_next s_osea_next ∧
    s_mir_next.ap = s_osea_next.ap ∧
    SBValid s_mir_next.ap ∧
    SBValid s_osea_next.ap := by
  let ⟨s_osea_next, h_steps, h_sim_next, h_ap_eq⟩ :=
    embedded_preservation_const_existing ctx s_mir s_osea s_mir_next
      prog_mir prog_osea h_sim h_mir_start h_osea_start h_mir_step
  let ⟨addr, tag, h_ptr, _h_mem⟩ := StateSim.place h_sim ctx.h_lookup
  have h_env : s_mir.env.lookup ctx.base = some (addr, TyVal.NatTy, tag) := h_ptr.2.1
  have h_stmt_mir : prog_mir.get? s_mir.pc = some ctx.stmt := StartsAt.singleton h_mir_start
  rcases List.get?_eq_some_iff.mp h_stmt_mir with ⟨h_pc_mir, h_get_mir⟩
  unfold mirlite.step at h_mir_step
  rw [dif_pos h_pc_mir, h_get_mir] at h_mir_step
  cases h_use : sb_use_mb s_mir.ap addr tag with
  | Err _ =>
      simp [ConstExistingCtx.stmt, obseq.notation.basePlace, obseq.notation.constRhs,
        mirlite.stepAssignConst, mirlite.finishPlaceAssign, mirlite.writeResolvedPlace,
        h_env, h_use] at h_mir_step
  | Ok ap' =>
      have h_next :
          s_mir_next =
            { s_mir with
              ap := ap',
              mem := mirlite.writeWordSeq s_mir.mem addr [mirlite.MemValue.Val ctx.n],
              pc := s_mir.pc + 1 } := by
        simpa [ConstExistingCtx.stmt, obseq.notation.basePlace, obseq.notation.constRhs,
          mirlite.stepAssignConst, mirlite.finishPlaceAssign, mirlite.writeResolvedPlace,
          h_env, h_use, mirlite.writeWordSeq] using h_mir_step.symm
      have h_valid_next : SBValid s_mir_next.ap := by
        rw [h_next]
        exact sb_use_mb_preserves_valid h_valid h_use
      exact ⟨s_osea_next, h_steps, h_sim_next, h_ap_eq, h_valid_next, StateSim.valid_osea h_sim_next⟩

end ConstExisting

end obseq.proof
