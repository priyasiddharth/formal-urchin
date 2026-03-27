import obseq.proof.state_helpers
import obseq.proof.const_existing

/-!
# `obseq.proof.const_fresh`

Local compiler-correctness lemmas for the fresh-destination word-constant
fragment.

As in `const_existing`, this is the paper-level `ConstOp(n)` case. The only
freshness-specific work is extending the source environment and the compiler
place map with the newly allocated base/register pair.
-/

namespace obseq.proof

open obseq
open obseq.mirlite
open obseq.oseair hiding State Result
open obseq.compile
open scoped obseq.notation

structure ConstFreshCtx where
  base : Word
  n : Word
  cs : CompilerState
  h_instrs : CompilerEmpty cs
  h_absent : BaseAbsent cs base
  h_regs : MappedRegsBelowNext cs

namespace ConstFreshCtx

def reg (ctx : ConstFreshCtx) : Register :=
  Register.R ctx.cs.nextReg

def postPlaceMap (ctx : ConstFreshCtx) : PlaceMap :=
  (ctx.base, (ctx.reg, LayoutTy.NatL)) :: ctx.cs.placeMap

theorem post_lookup (ctx : ConstFreshCtx) :
  ctx.postPlaceMap.lookup ctx.base = some (ctx.reg, LayoutTy.NatL) := by
  simp [ConstFreshCtx.postPlaceMap, ConstFreshCtx.reg, List.lookup]

def stmt (ctx : ConstFreshCtx) : mirlite.Stmt :=
  place(ctx.base) ::= const ctx.n

def compiled (ctx : ConstFreshCtx) : oseair.Prog :=
  (compileStmt ctx.cs ctx.stmt).instrs

def mirStart (_ctx : ConstFreshCtx) (s_mir : mirlite.State) : mirlite.State :=
  { s_mir with pc := 0 }

def oseaStart (_ctx : ConstFreshCtx) (s_osea : oseair.State) : oseair.State :=
  { s_osea with pc := 0 }

theorem instrs_nil (ctx : ConstFreshCtx) : ctx.cs.instrs = [] :=
  ctx.h_instrs

theorem base_ne_of_old_lookup
  (ctx : ConstFreshCtx)
  {base : Word} {reg : Register} {layout : LayoutTy}
  (h_lookup : ctx.cs.placeMap.lookup base = some (reg, layout)) :
  base ≠ ctx.base := by
  intro h_eq
  subst base
  have h_absent : ctx.cs.placeMap.lookup ctx.base = none := by
    simpa [BaseAbsent, getPlaceInfo] using ctx.h_absent
  rw [h_absent] at h_lookup
  contradiction

theorem reg_ne_of_old_lookup
  (ctx : ConstFreshCtx)
  {base : Word} {reg : Register} {layout : LayoutTy}
  (h_lookup : ctx.cs.placeMap.lookup base = some (reg, layout)) :
  reg ≠ ctx.reg := by
  have h_lt : regIdx reg < ctx.cs.nextReg := ctx.h_regs base reg layout h_lookup
  cases reg with
  | R idx =>
      intro h_eq
      injection h_eq with h_idx
      rw [h_idx] at h_lt
      exact Nat.lt_irrefl _ h_lt

end ConstFreshCtx

theorem mirlite_step_const_fresh_ok
  (s_mir : mirlite.State)
  (base tag n : Word)
  (ap2 ap3 : AccessPerms)
  (h_env : s_mir.env.lookup base = none)
  (h_own : sb_own s_mir.ap s_mir.mem.addrStart = (SBResult.Ok ap2, tag))
  (h_use : sb_use_mb ap2 s_mir.mem.addrStart tag = SBResult.Ok ap3) :
  mirlite.step { s_mir with pc := 0 } [place(base) ::= const n] =
    mirlite.Result.Ok
      { s_mir with
        env := s_mir.env.insert base (s_mir.mem.addrStart, TyVal.NatTy, tag),
        mem := mirlite.writeWordSeq
          { s_mir.mem with addrStart := s_mir.mem.addrStart + blockSize LayoutTy.NatL }
          s_mir.mem.addrStart [mirlite.MemValue.Val n],
        ap := ap3,
        pc := 1 } := by
  simp [mirlite.step, obseq.notation.basePlace, obseq.notation.constRhs,
    mirlite.stepAssignConst, mirlite.finishPlaceAssign, mirlite.allocateBaseAndWrite,
    h_env, h_own, h_use, mirlite.allocate, blockSize, mirlite.writeWordSeq, layoutToTyVal]

theorem mirlite_step_const_fresh_inv
  (s_mir : mirlite.State)
  (base n : Word)
  (s_mir_next : mirlite.State)
  (h_env : s_mir.env.lookup base = none)
  (h_step :
    mirlite.step { s_mir with pc := 0 } [place(base) ::= const n] =
      mirlite.Result.Ok s_mir_next) :
  ∃ tag ap2 ap3,
    sb_own s_mir.ap s_mir.mem.addrStart = (SBResult.Ok ap2, tag) ∧
    sb_use_mb ap2 s_mir.mem.addrStart tag = SBResult.Ok ap3 ∧
    s_mir_next =
      { s_mir with
        env := s_mir.env.insert base (s_mir.mem.addrStart, TyVal.NatTy, tag),
        mem := mirlite.writeWordSeq
          { s_mir.mem with addrStart := s_mir.mem.addrStart + blockSize LayoutTy.NatL }
          s_mir.mem.addrStart [mirlite.MemValue.Val n],
        ap := ap3,
        pc := 1 } := by
  cases h_own : sb_own s_mir.ap s_mir.mem.addrStart with
  | mk ownRes tag =>
      cases ownRes with
      | Err _ =>
          have : False := by
            simp [mirlite.step, obseq.notation.basePlace, obseq.notation.constRhs,
              mirlite.stepAssignConst, mirlite.finishPlaceAssign, mirlite.allocateBaseAndWrite,
              h_env, h_own, mirlite.allocate, blockSize, mirlite.writeWordSeq] at h_step
          contradiction
      | Ok ap2 =>
          cases h_use : sb_use_mb ap2 s_mir.mem.addrStart tag with
          | Err _ =>
              have : False := by
                simp [mirlite.step, obseq.notation.basePlace, obseq.notation.constRhs,
                  mirlite.stepAssignConst, mirlite.finishPlaceAssign, mirlite.allocateBaseAndWrite,
                  h_env, h_own, h_use, mirlite.allocate, blockSize, mirlite.writeWordSeq] at h_step
              contradiction
          | Ok ap3 =>
              have h_ok := mirlite_step_const_fresh_ok s_mir base tag n ap2 ap3 h_env h_own h_use
              rw [h_ok] at h_step
              injection h_step with h_state
              exact ⟨tag, ap2, ap3, rfl, h_use, h_state.symm⟩

@[simp] theorem compile_const_fresh
  (ctx : ConstFreshCtx) :
  ctx.compiled =
    [oseair.Instr.Assgn ctx.reg (oseair.Rhs.Alloc TyVal.NatTy),
     oseair.Instr.CStore TyVal.NatTy [oseair.Val.Dat ctx.n] ctx.reg] := by
  have h_place :
      placeToReg ctx.cs { base := ctx.base, path := [] } mirlite.RefKind.Mut (some LayoutTy.NatL) =
        { reg := ctx.reg, layout := LayoutTy.NatL, cleanup := [],
          cs :=
            { nextReg := ctx.cs.nextReg + 1,
              placeMap := (ctx.base, (ctx.reg, LayoutTy.NatL)) :: ctx.cs.placeMap,
              instrs := ctx.cs.instrs ++ [oseair.Instr.Assgn ctx.reg (oseair.Rhs.Alloc TyVal.NatTy)] } } := by
    unfold placeToReg ConstFreshCtx.reg
    rw [ctx.h_absent]
    simp [freshReg, emit, setPlace, layoutToTyVal, typeSize]
  unfold ConstFreshCtx.compiled ConstFreshCtx.stmt
  simp [compileStmt, obseq.notation.basePlace, obseq.notation.constRhs,
    h_place, emit, cleanupInstrs, List.map, ctx.instrs_nil, layoutToTyVal, typeSize]

theorem osea_steps_const_fresh_ok
  (s_osea : oseair.State)
  (reg : Register)
  (n tag : Word)
  (ap2 ap3 : AccessPerms)
  (h_own : sb_own s_osea.ap s_osea.mem.addrStart = (SBResult.Ok ap2, tag))
  (h_use : sb_use_mb ap2 s_osea.mem.addrStart tag = SBResult.Ok ap3) :
  StepStar
    { s_osea with pc := 0 }
    [oseair.Instr.Assgn reg (oseair.Rhs.Alloc TyVal.NatTy),
     oseair.Instr.CStore TyVal.NatTy [oseair.Val.Dat n] reg]
    { s_osea with
      reg := s_osea.reg.insert reg
        (TyVal.PTy, [oseair.Val.Ptr s_osea.mem.addrStart 0 (blockSize LayoutTy.NatL) tag]),
      mem := oseair.writeWordSeq
        { s_osea.mem with addrStart := s_osea.mem.addrStart + blockSize LayoutTy.NatL }
        s_osea.mem.addrStart [oseair.Val.Dat n],
      ap := ap3,
      pc := 2 } := by
  let s1 : oseair.State :=
    { s_osea with
      reg := s_osea.reg.insert reg
        (TyVal.PTy, [oseair.Val.Ptr s_osea.mem.addrStart 0 (blockSize LayoutTy.NatL) tag]),
      mem := { s_osea.mem with addrStart := s_osea.mem.addrStart + blockSize LayoutTy.NatL },
      ap := ap2,
      pc := 1 }
  have h_step1 :
      oseair.step { s_osea with pc := 0 }
        [oseair.Instr.Assgn reg (oseair.Rhs.Alloc TyVal.NatTy),
         oseair.Instr.CStore TyVal.NatTy [oseair.Val.Dat n] reg] =
        oseair.Result.Ok s1 := by
    unfold oseair.step
    have h_pc :
        ({ s_osea with pc := 0 }).pc <
          [oseair.Instr.Assgn reg (oseair.Rhs.Alloc TyVal.NatTy),
           oseair.Instr.CStore TyVal.NatTy [oseair.Val.Dat n] reg].length := by
      exact Nat.succ_pos 1
    rw [dif_pos h_pc]
    have h_get :
        List.get
          [oseair.Instr.Assgn reg (oseair.Rhs.Alloc TyVal.NatTy),
           oseair.Instr.CStore TyVal.NatTy [oseair.Val.Dat n] reg]
          ⟨0, h_pc⟩ =
          oseair.Instr.Assgn reg (oseair.Rhs.Alloc TyVal.NatTy) := by
      rfl
    rw [h_get]
    unfold oseair.evalRhs
    simp [h_own, s1, oseair.allocate, blockSize, layoutToTyVal]
  have h_reg :
      s1.reg.lookup reg =
        some (TyVal.PTy, [oseair.Val.Ptr s_osea.mem.addrStart 0 (blockSize LayoutTy.NatL) tag]) := by
    simp [s1]
  have h_step2 :
      oseair.step s1
        [oseair.Instr.Assgn reg (oseair.Rhs.Alloc TyVal.NatTy),
         oseair.Instr.CStore TyVal.NatTy [oseair.Val.Dat n] reg] =
        oseair.Result.Ok
          { s_osea with
            reg := s_osea.reg.insert reg
              (TyVal.PTy, [oseair.Val.Ptr s_osea.mem.addrStart 0 (blockSize LayoutTy.NatL) tag]),
            mem := oseair.writeWordSeq
              { s_osea.mem with addrStart := s_osea.mem.addrStart + blockSize LayoutTy.NatL }
              s_osea.mem.addrStart [oseair.Val.Dat n],
            ap := ap3,
            pc := 2 } := by
    unfold oseair.step oseair.writeThroughPtr
    have h_pc :
        s1.pc <
          [oseair.Instr.Assgn reg (oseair.Rhs.Alloc TyVal.NatTy),
           oseair.Instr.CStore TyVal.NatTy [oseair.Val.Dat n] reg].length := by
      exact Nat.succ_lt_succ (Nat.succ_pos 0)
    rw [dif_pos h_pc]
    have h_get :
        List.get
          [oseair.Instr.Assgn reg (oseair.Rhs.Alloc TyVal.NatTy),
           oseair.Instr.CStore TyVal.NatTy [oseair.Val.Dat n] reg]
          ⟨1, h_pc⟩ =
          oseair.Instr.CStore TyVal.NatTy [oseair.Val.Dat n] reg := by
      rfl
    rw [h_get]
    have h_in_bounds :
        s_osea.mem.addrStart < s_osea.mem.addrStart + blockSize LayoutTy.NatL := by
      have h_add :
          s_osea.mem.addrStart + 0 < s_osea.mem.addrStart + blockSize LayoutTy.NatL :=
        Nat.add_lt_add_left (by decide : 0 < blockSize LayoutTy.NatL) s_osea.mem.addrStart
      rw [Nat.add_zero] at h_add
      exact h_add
    have h_bound :
        ¬ s_osea.mem.addrStart >= s_osea.mem.addrStart + blockSize LayoutTy.NatL := by
      intro h_ge
      exact (Nat.lt_irrefl s_osea.mem.addrStart) (Nat.lt_of_lt_of_le h_in_bounds h_ge)
    simp [h_reg, h_use, s1, h_bound]
  exact StepStar.trans (StepStar.single h_step1) (StepStar.single h_step2)

section ConstFresh

variable (ctx : ConstFreshCtx)
variable (s_mir : mirlite.State)
variable (s_osea : oseair.State)
variable (s_mir_next : mirlite.State)

theorem local_simulation_const_fresh
  (h_sim : StateSim ctx.cs.placeMap s_mir s_osea)
  (h_env : s_mir.env.lookup ctx.base = none)
  (h_mir_step :
    mirlite.step (ctx.mirStart s_mir) [ctx.stmt] =
      mirlite.Result.Ok s_mir_next) :
  ∃ s_osea_next,
    StepStar (ctx.oseaStart s_osea) ctx.compiled s_osea_next ∧
    StateSim ctx.postPlaceMap s_mir_next s_osea_next := by
  have h_ap : s_mir.ap = s_osea.ap := StateSim.ap_eq h_sim
  have h_addrStart : s_mir.mem.addrStart = s_osea.mem.addrStart := StateSim.addrStart_eq h_sim
  have h_mir_step' :
      mirlite.step { s_mir with pc := 0 } [place(ctx.base) ::= const ctx.n] =
        mirlite.Result.Ok s_mir_next := by
    unfold ConstFreshCtx.mirStart ConstFreshCtx.stmt at h_mir_step
    exact h_mir_step
  let ⟨tag, ap2, ap3, h_own, h_use, h_next⟩ :=
    mirlite_step_const_fresh_inv s_mir ctx.base ctx.n s_mir_next h_env h_mir_step'
  have h_target_own :
      sb_own s_osea.ap s_osea.mem.addrStart = (SBResult.Ok ap2, tag) := by
    rw [← h_ap, ← h_addrStart]
    exact h_own
  have h_target_use :
      sb_use_mb ap2 s_osea.mem.addrStart tag = SBResult.Ok ap3 := by
    rw [← h_addrStart]
    exact h_use
  have h_valid_ap2 : SBValid ap2 := by
    exact sb_own_preserves_valid (StateSim.valid_mir h_sim) h_own
  have h_valid_ap3 : SBValid ap3 := by
    exact sb_use_mb_preserves_valid h_valid_ap2 h_use
  subst s_mir_next
  let s_mir_post :=
    { s_mir with
      env := s_mir.env.insert ctx.base (s_mir.mem.addrStart, TyVal.NatTy, tag),
      mem := mirlite.writeWordSeq
        { s_mir.mem with addrStart := s_mir.mem.addrStart + blockSize LayoutTy.NatL }
        s_mir.mem.addrStart [mirlite.MemValue.Val ctx.n],
      ap := ap3,
      pc := 1 }
  let s_osea_post :=
    { s_osea with
      reg := s_osea.reg.insert ctx.reg
        (TyVal.PTy, [oseair.Val.Ptr s_osea.mem.addrStart 0 (blockSize LayoutTy.NatL) tag]),
      mem := oseair.writeWordSeq
        { s_osea.mem with addrStart := s_osea.mem.addrStart + blockSize LayoutTy.NatL }
        s_osea.mem.addrStart [oseair.Val.Dat ctx.n],
      ap := ap3,
      pc := 2 }
  have h_target_exec :
      StepStar (ctx.oseaStart s_osea) ctx.compiled s_osea_post := by
    rw [compile_const_fresh ctx]
    exact osea_steps_const_fresh_ok s_osea ctx.reg ctx.n tag ap2 ap3 h_target_own h_target_use
  refine ⟨s_osea_post, h_target_exec, ?_⟩
  refine ⟨h_valid_ap3, h_valid_ap3, rfl, by
    simp [s_mir_post, s_osea_post, h_addrStart, blockSize, layoutToTyVal], ?_⟩
  · intro base reg layout h_lookup_post
    by_cases h_base : base = ctx.base
    · subst base
      have h_lookup_nat : ctx.reg = reg ∧ LayoutTy.NatL = layout := by
        simpa [ConstFreshCtx.postPlaceMap, List.lookup] using h_lookup_post
      rcases h_lookup_nat with ⟨h_reg_eq, h_layout_eq⟩
      subst reg layout
      refine ⟨s_mir.mem.addrStart, tag, ?_, ?_⟩
      · refine ⟨ctx.post_lookup, ?_, ?_⟩
        · simp [s_mir_post, layoutToTyVal]
        · simp [s_osea_post, ConstFreshCtx.reg, h_addrStart]
      · refine ⟨by
          simp [s_mir_post, s_osea_post, h_addrStart, blockSize, layoutToTyVal], ?_⟩
        intro i hi
        cases i with
        | zero =>
            simp [s_mir_post, s_osea_post, h_addrStart, mem_val_eq_opt, mem_val_eq,
              blockSize, layoutToTyVal, typeSize]
        | succ i =>
            simp [blockSize, layoutToTyVal, typeSize] at hi
    · have h_lookup_old : ctx.cs.placeMap.lookup base = some (reg, layout) := by
        have h_beq : (base == ctx.base) = false := by
          simp [h_base]
        simpa [ConstFreshCtx.postPlaceMap, List.lookup, h_beq] using h_lookup_post
      let ⟨addr0, tag0, h_ptr0, h_mem0⟩ := StateSim.place h_sim h_lookup_old
      have h_base_ne := ctx.base_ne_of_old_lookup h_lookup_old
      have h_reg_ne := ctx.reg_ne_of_old_lookup h_lookup_old
      refine ⟨addr0, tag0, ?_, ?_⟩
      · refine ⟨h_lookup_post, ?_, ?_⟩
        · calc
            (s_mir.env.insert ctx.base (s_mir.mem.addrStart, TyVal.NatTy, tag)).lookup base
                = s_mir.env.lookup base := by
                  simpa using env_lookup_insert_ne s_mir.env ctx.base base
                    (s_mir.mem.addrStart, TyVal.NatTy, tag) h_base_ne
            _ = some (addr0, layoutToTyVal layout, tag0) := h_ptr0.2.1
        · calc
            (s_osea.reg.insert ctx.reg
                (TyVal.PTy, [oseair.Val.Ptr s_osea.mem.addrStart 0 (blockSize LayoutTy.NatL) tag])).lookup reg
                = s_osea.reg.lookup reg := by
                  simpa using reg_lookup_insert_ne s_osea.reg ctx.reg reg
                    (TyVal.PTy, [oseair.Val.Ptr s_osea.mem.addrStart 0 (blockSize LayoutTy.NatL) tag]) h_reg_ne
            _ = some (TyVal.PTy, [oseair.Val.Ptr addr0 0 (blockSize layout) tag0]) := h_ptr0.2.2
      · let s_mir_alloc : mirlite.State :=
          { s_mir_post with
            mem := { s_mir.mem with addrStart := s_mir.mem.addrStart + blockSize LayoutTy.NatL } }
        let s_osea_alloc : oseair.State :=
          { s_osea_post with
            mem := { s_osea.mem with addrStart := s_osea.mem.addrStart + blockSize LayoutTy.NatL } }
        have h_alloc_mem : sim_mem_at s_mir_alloc s_osea_alloc addr0 layout := by
          refine ⟨by
            simp [s_mir_alloc, s_osea_alloc, s_mir_post, s_osea_post,
              h_addrStart, blockSize, layoutToTyVal, h_mem0.1], ?_⟩
          intro i hi
          exact h_mem0.2 i hi
        have h_disjoint :
            interval_disjoint addr0 (blockSize layout) s_mir.mem.addrStart (blockSize LayoutTy.NatL) :=
          (StateSim.fresh_interval
            (freshSize := blockSize LayoutTy.NatL) h_sim h_lookup_old h_ptr0.2.1 h_ptr0.2.2).1
        simpa [s_mir_post, s_osea_post, s_mir_alloc, s_osea_alloc, h_addrStart] using
          (sim_mem_at_write_disjoint
            (s_mir := s_mir_alloc)
            (s_osea := s_osea_alloc)
            (trackedAddr := addr0)
            (layout := layout)
            (dst := s_mir.mem.addrStart)
            (writtenSize := blockSize LayoutTy.NatL)
            (vals_mir := [mirlite.MemValue.Val ctx.n])
            (vals_osea := [oseair.Val.Dat ctx.n])
            h_alloc_mem
            (by simp [blockSize, layoutToTyVal, typeSize])
            (by simp [blockSize, layoutToTyVal, typeSize])
            h_disjoint)

theorem local_preservation_const_fresh
  (h_sim : StateSim ctx.cs.placeMap s_mir s_osea)
  (h_env : s_mir.env.lookup ctx.base = none)
  (h_mir_step :
    mirlite.step (ctx.mirStart s_mir) [ctx.stmt] =
      mirlite.Result.Ok s_mir_next) :
  ∃ s_osea_next,
    StepStar (ctx.oseaStart s_osea) ctx.compiled s_osea_next ∧
    StateSim ctx.postPlaceMap s_mir_next s_osea_next ∧
    s_mir_next.ap = s_osea_next.ap := by
  let ⟨s_osea_next, h_steps, h_sim_next⟩ :=
    local_simulation_const_fresh ctx s_mir s_osea s_mir_next h_sim h_env h_mir_step
  exact ⟨s_osea_next, h_steps, h_sim_next, StateSim.ap_eq h_sim_next⟩

theorem local_validity_const_fresh
  (h_sim : StateSim ctx.cs.placeMap s_mir s_osea)
  (h_valid : SBValid s_mir.ap)
  (h_env : s_mir.env.lookup ctx.base = none)
  (h_mir_step :
    mirlite.step (ctx.mirStart s_mir) [ctx.stmt] =
      mirlite.Result.Ok s_mir_next) :
  ∃ s_osea_next,
    StepStar (ctx.oseaStart s_osea) ctx.compiled s_osea_next ∧
    StateSim ctx.postPlaceMap s_mir_next s_osea_next ∧
    s_mir_next.ap = s_osea_next.ap ∧
    SBValid s_mir_next.ap ∧
    SBValid s_osea_next.ap := by
  have h_pres :=
    local_preservation_const_fresh ctx s_mir s_osea s_mir_next h_sim h_env h_mir_step
  let ⟨tag, ap2, ap3, h_own, h_use, h_next⟩ :=
    mirlite_step_const_fresh_inv s_mir ctx.base ctx.n s_mir_next h_env (by
      unfold ConstFreshCtx.mirStart ConstFreshCtx.stmt at h_mir_step
      exact h_mir_step)
  let ⟨s_osea_next, h_steps, h_sim_next, h_ap_eq⟩ := h_pres
  have h_valid_ap2 : SBValid ap2 := sb_own_preserves_valid h_valid h_own
  have h_valid_mir_next : SBValid s_mir_next.ap := by
    rw [h_next]
    exact sb_use_mb_preserves_valid h_valid_ap2 h_use
  exact ⟨s_osea_next, h_steps, h_sim_next, h_ap_eq, h_valid_mir_next, StateSim.valid_osea h_sim_next⟩

theorem embedded_simulation_const_fresh
  (prog_mir : mirlite.Prog)
  (prog_osea : oseair.Prog)
  (h_sim : StateSim ctx.cs.placeMap s_mir s_osea)
  (h_env : s_mir.env.lookup ctx.base = none)
  (h_mir_start : StartsAt prog_mir s_mir.pc [ctx.stmt])
  (h_osea_start : StartsAt prog_osea s_osea.pc ctx.compiled)
  (h_mir_step : mirlite.step s_mir prog_mir = mirlite.Result.Ok s_mir_next) :
  ∃ s_osea_next,
    StepStar s_osea prog_osea s_osea_next ∧
    StateSim ctx.postPlaceMap s_mir_next s_osea_next := by
  have h_ap : s_mir.ap = s_osea.ap := StateSim.ap_eq h_sim
  have h_addrStart : s_mir.mem.addrStart = s_osea.mem.addrStart := StateSim.addrStart_eq h_sim
  have h_stmt_mir : prog_mir.get? s_mir.pc = some ctx.stmt := StartsAt.singleton h_mir_start
  rcases List.get?_eq_some_iff.mp h_stmt_mir with ⟨h_pc_mir, h_get_mir⟩
  unfold mirlite.step at h_mir_step
  rw [dif_pos h_pc_mir, h_get_mir] at h_mir_step
  cases h_own : sb_own s_mir.ap s_mir.mem.addrStart with
  | mk ownRes tag =>
      cases ownRes with
      | Err _ =>
          simp [ConstFreshCtx.stmt, obseq.notation.basePlace, obseq.notation.constRhs,
            mirlite.stepAssignConst, mirlite.finishPlaceAssign, mirlite.allocateBaseAndWrite,
            h_env, h_own, mirlite.allocate, blockSize, mirlite.writeWordSeq, layoutToTyVal] at h_mir_step
      | Ok ap2 =>
          cases h_use : sb_use_mb ap2 s_mir.mem.addrStart tag with
          | Err _ =>
              simp [ConstFreshCtx.stmt, obseq.notation.basePlace, obseq.notation.constRhs,
                mirlite.stepAssignConst, mirlite.finishPlaceAssign, mirlite.allocateBaseAndWrite,
                h_env, h_own, h_use, mirlite.allocate, blockSize, mirlite.writeWordSeq, layoutToTyVal] at h_mir_step
          | Ok ap3 =>
              have h_next_full :
                  s_mir_next =
                    { s_mir with
                      env := s_mir.env.insert ctx.base (s_mir.mem.addrStart, TyVal.NatTy, tag),
                      mem := mirlite.writeWordSeq
                        { s_mir.mem with addrStart := s_mir.mem.addrStart + blockSize LayoutTy.NatL }
                        s_mir.mem.addrStart [mirlite.MemValue.Val ctx.n],
                      ap := ap3,
                      pc := s_mir.pc + 1 } := by
                simpa [ConstFreshCtx.stmt, obseq.notation.basePlace, obseq.notation.constRhs,
                  mirlite.stepAssignConst, mirlite.finishPlaceAssign, mirlite.allocateBaseAndWrite,
                  h_env, h_own, h_use, mirlite.allocate, blockSize, mirlite.writeWordSeq, layoutToTyVal]
                  using h_mir_step.symm
              have h_target_own :
                  sb_own s_osea.ap s_osea.mem.addrStart = (SBResult.Ok ap2, tag) := by
                rw [← h_ap, ← h_addrStart]
                exact h_own
              have h_target_use :
                  sb_use_mb ap2 s_osea.mem.addrStart tag = SBResult.Ok ap3 := by
                rw [← h_addrStart]
                exact h_use
              have h_valid_ap2 : SBValid ap2 := by
                exact sb_own_preserves_valid (StateSim.valid_mir h_sim) h_own
              have h_valid_ap3 : SBValid ap3 := by
                exact sb_use_mb_preserves_valid h_valid_ap2 h_use
              rw [compile_const_fresh ctx] at h_osea_start
              have h_stmt_osea0 :
                  prog_osea.get? s_osea.pc =
                    some (oseair.Instr.Assgn ctx.reg (oseair.Rhs.Alloc TyVal.NatTy)) := by
                simpa [StartsAt, Nat.zero_add] using (h_osea_start 0).symm
              have h_osea_tail := StartsAt.tail h_osea_start
              have h_stmt_osea1 :
                  prog_osea.get? (s_osea.pc + 1) =
                    some (oseair.Instr.CStore TyVal.NatTy [oseair.Val.Dat ctx.n] ctx.reg) := by
                simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using StartsAt.singleton h_osea_tail
              rcases List.get?_eq_some_iff.mp h_stmt_osea0 with ⟨h_pc_osea0, h_get_osea0⟩
              rcases List.get?_eq_some_iff.mp h_stmt_osea1 with ⟨h_pc_osea1, h_get_osea1⟩
              let s1 : oseair.State :=
                { s_osea with
                  reg := s_osea.reg.insert ctx.reg
                    (TyVal.PTy, [oseair.Val.Ptr s_osea.mem.addrStart 0 (blockSize LayoutTy.NatL) tag]),
                  mem := { s_osea.mem with addrStart := s_osea.mem.addrStart + blockSize LayoutTy.NatL },
                  ap := ap2,
                  pc := s_osea.pc + 1 }
              let s_osea_post :=
                { s_osea with
                  reg := s_osea.reg.insert ctx.reg
                    (TyVal.PTy, [oseair.Val.Ptr s_osea.mem.addrStart 0 (blockSize LayoutTy.NatL) tag]),
                  mem := oseair.writeWordSeq
                    { s_osea.mem with addrStart := s_osea.mem.addrStart + blockSize LayoutTy.NatL }
                    s_osea.mem.addrStart [oseair.Val.Dat ctx.n],
                  ap := ap3,
                  pc := s_osea.pc + 2 }
              let s_mir_post :=
                { s_mir with
                  env := s_mir.env.insert ctx.base (s_mir.mem.addrStart, TyVal.NatTy, tag),
                  mem := mirlite.writeWordSeq
                    { s_mir.mem with addrStart := s_mir.mem.addrStart + blockSize LayoutTy.NatL }
                    s_mir.mem.addrStart [mirlite.MemValue.Val ctx.n],
                  ap := ap3,
                  pc := s_mir.pc + 1 }
              have h_step1_full :
                  oseair.step s_osea prog_osea = oseair.Result.Ok s1 := by
                unfold oseair.step
                rw [dif_pos h_pc_osea0, h_get_osea0]
                unfold oseair.evalRhs
                simp [h_target_own, s1, oseair.allocate, blockSize, layoutToTyVal]
              have h_reg1 :
                  s1.reg.lookup ctx.reg =
                    some (TyVal.PTy, [oseair.Val.Ptr s_osea.mem.addrStart 0 (blockSize LayoutTy.NatL) tag]) := by
                simp [s1]
              have h_step2_full :
                  oseair.step s1 prog_osea = oseair.Result.Ok s_osea_post := by
                unfold oseair.step oseair.writeThroughPtr
                rw [dif_pos h_pc_osea1, h_get_osea1]
                have h_in_bounds :
                    s_osea.mem.addrStart < s_osea.mem.addrStart + blockSize LayoutTy.NatL := by
                  have h_add :
                      s_osea.mem.addrStart + 0 < s_osea.mem.addrStart + blockSize LayoutTy.NatL :=
                    Nat.add_lt_add_left (by decide : 0 < blockSize LayoutTy.NatL) s_osea.mem.addrStart
                  rw [Nat.add_zero] at h_add
                  exact h_add
                have h_bound :
                    ¬ s_osea.mem.addrStart >= s_osea.mem.addrStart + blockSize LayoutTy.NatL := by
                  intro h_ge
                  exact (Nat.lt_irrefl s_osea.mem.addrStart) (Nat.lt_of_lt_of_le h_in_bounds h_ge)
                simp [s1, s_osea_post, h_reg1, h_target_use, h_bound]
              refine ⟨s_osea_post, StepStar.trans (StepStar.single h_step1_full) (StepStar.single h_step2_full), ?_⟩
              rw [h_next_full]
              refine ⟨h_valid_ap3, h_valid_ap3, rfl, by
                simp [s_mir_post, s_osea_post, h_addrStart, blockSize, layoutToTyVal], ?_⟩
              · intro base reg layout h_lookup_post
                by_cases h_base : base = ctx.base
                · subst base
                  have h_lookup_nat : ctx.reg = reg ∧ LayoutTy.NatL = layout := by
                    simpa [ConstFreshCtx.postPlaceMap, List.lookup] using h_lookup_post
                  rcases h_lookup_nat with ⟨h_reg_eq, h_layout_eq⟩
                  subst reg layout
                  refine ⟨s_mir.mem.addrStart, tag, ?_, ?_⟩
                  · refine ⟨ctx.post_lookup, ?_, ?_⟩
                    · simp [s_mir_post, layoutToTyVal]
                    · simp [s_osea_post, ConstFreshCtx.reg, h_addrStart]
                  · refine ⟨by
                      simp [s_mir_post, s_osea_post, h_addrStart, blockSize, layoutToTyVal], ?_⟩
                    intro i hi
                    cases i with
                    | zero =>
                        simp [s_mir_post, s_osea_post, h_addrStart, mem_val_eq_opt, mem_val_eq,
                          blockSize, layoutToTyVal, typeSize]
                    | succ i =>
                        simp [blockSize, layoutToTyVal, typeSize] at hi
                · have h_lookup_old : ctx.cs.placeMap.lookup base = some (reg, layout) := by
                    have h_beq : (base == ctx.base) = false := by simp [h_base]
                    simpa [ConstFreshCtx.postPlaceMap, List.lookup, h_beq] using h_lookup_post
                  let ⟨addr0, tag0, h_ptr0, h_mem0⟩ := StateSim.place h_sim h_lookup_old
                  have h_base_ne := ctx.base_ne_of_old_lookup h_lookup_old
                  have h_reg_ne := ctx.reg_ne_of_old_lookup h_lookup_old
                  refine ⟨addr0, tag0, ?_, ?_⟩
                  · refine ⟨h_lookup_post, ?_, ?_⟩
                    · calc
                        (s_mir.env.insert ctx.base (s_mir.mem.addrStart, TyVal.NatTy, tag)).lookup base
                            = s_mir.env.lookup base := by
                              simpa using env_lookup_insert_ne s_mir.env ctx.base base
                                (s_mir.mem.addrStart, TyVal.NatTy, tag) h_base_ne
                        _ = some (addr0, layoutToTyVal layout, tag0) := h_ptr0.2.1
                    · calc
                        (s_osea.reg.insert ctx.reg
                            (TyVal.PTy, [oseair.Val.Ptr s_osea.mem.addrStart 0 (blockSize LayoutTy.NatL) tag])).lookup reg
                            = s_osea.reg.lookup reg := by
                              simpa using reg_lookup_insert_ne s_osea.reg ctx.reg reg
                                (TyVal.PTy, [oseair.Val.Ptr s_osea.mem.addrStart 0 (blockSize LayoutTy.NatL) tag]) h_reg_ne
                        _ = some (TyVal.PTy, [oseair.Val.Ptr addr0 0 (blockSize layout) tag0]) := h_ptr0.2.2
                  · let s_mir_alloc : mirlite.State :=
                      { s_mir_post with
                        mem := { s_mir.mem with addrStart := s_mir.mem.addrStart + blockSize LayoutTy.NatL } }
                    let s_osea_alloc : oseair.State :=
                      { s_osea_post with
                        mem := { s_osea.mem with addrStart := s_osea.mem.addrStart + blockSize LayoutTy.NatL } }
                    have h_alloc_mem : sim_mem_at s_mir_alloc s_osea_alloc addr0 layout := by
                      refine ⟨by
                        simp [s_mir_alloc, s_osea_alloc, s_mir_post, s_osea_post,
                          h_addrStart, blockSize, layoutToTyVal, h_mem0.1], ?_⟩
                      intro i hi
                      exact h_mem0.2 i hi
                    have h_disjoint :
                        interval_disjoint addr0 (blockSize layout) s_mir.mem.addrStart (blockSize LayoutTy.NatL) :=
                      (StateSim.fresh_interval
                        (freshSize := blockSize LayoutTy.NatL) h_sim h_lookup_old h_ptr0.2.1 h_ptr0.2.2).1
                    simpa [s_mir_post, s_osea_post, s_mir_alloc, s_osea_alloc, h_addrStart] using
                      (sim_mem_at_write_disjoint
                        (s_mir := s_mir_alloc)
                        (s_osea := s_osea_alloc)
                        (trackedAddr := addr0)
                        (layout := layout)
                        (dst := s_mir.mem.addrStart)
                        (writtenSize := blockSize LayoutTy.NatL)
                        (vals_mir := [mirlite.MemValue.Val ctx.n])
                        (vals_osea := [oseair.Val.Dat ctx.n])
                        h_alloc_mem
                        (by simp [blockSize, layoutToTyVal, typeSize])
                        (by simp [blockSize, layoutToTyVal, typeSize])
                        h_disjoint)

theorem embedded_preservation_const_fresh
  (prog_mir : mirlite.Prog)
  (prog_osea : oseair.Prog)
  (h_sim : StateSim ctx.cs.placeMap s_mir s_osea)
  (h_env : s_mir.env.lookup ctx.base = none)
  (h_mir_start : StartsAt prog_mir s_mir.pc [ctx.stmt])
  (h_osea_start : StartsAt prog_osea s_osea.pc ctx.compiled)
  (h_mir_step : mirlite.step s_mir prog_mir = mirlite.Result.Ok s_mir_next) :
  ∃ s_osea_next,
    StepStar s_osea prog_osea s_osea_next ∧
    StateSim ctx.postPlaceMap s_mir_next s_osea_next ∧
    s_mir_next.ap = s_osea_next.ap := by
  let ⟨s_osea_next, h_steps, h_sim_next⟩ :=
    embedded_simulation_const_fresh ctx s_mir s_osea s_mir_next
      prog_mir prog_osea h_sim h_env h_mir_start h_osea_start h_mir_step
  exact ⟨s_osea_next, h_steps, h_sim_next, StateSim.ap_eq h_sim_next⟩

theorem embedded_validity_const_fresh
  (prog_mir : mirlite.Prog)
  (prog_osea : oseair.Prog)
  (h_sim : StateSim ctx.cs.placeMap s_mir s_osea)
  (h_valid : SBValid s_mir.ap)
  (h_env : s_mir.env.lookup ctx.base = none)
  (h_mir_start : StartsAt prog_mir s_mir.pc [ctx.stmt])
  (h_osea_start : StartsAt prog_osea s_osea.pc ctx.compiled)
  (h_mir_step : mirlite.step s_mir prog_mir = mirlite.Result.Ok s_mir_next) :
  ∃ s_osea_next,
    StepStar s_osea prog_osea s_osea_next ∧
    StateSim ctx.postPlaceMap s_mir_next s_osea_next ∧
    s_mir_next.ap = s_osea_next.ap ∧
    SBValid s_mir_next.ap ∧
    SBValid s_osea_next.ap := by
  let ⟨s_osea_next, h_steps, h_sim_next, h_ap_eq⟩ :=
    embedded_preservation_const_fresh ctx s_mir s_osea s_mir_next
      prog_mir prog_osea h_sim h_env h_mir_start h_osea_start h_mir_step
  have h_stmt_mir : prog_mir.get? s_mir.pc = some ctx.stmt := StartsAt.singleton h_mir_start
  rcases List.get?_eq_some_iff.mp h_stmt_mir with ⟨h_pc_mir, h_get_mir⟩
  unfold mirlite.step at h_mir_step
  rw [dif_pos h_pc_mir, h_get_mir] at h_mir_step
  cases h_own : sb_own s_mir.ap s_mir.mem.addrStart with
  | mk ownRes tag =>
      cases ownRes with
      | Err _ =>
          simp [ConstFreshCtx.stmt, obseq.notation.basePlace, obseq.notation.constRhs,
            mirlite.stepAssignConst, mirlite.finishPlaceAssign, mirlite.allocateBaseAndWrite,
            h_env, h_own, mirlite.allocate, blockSize, mirlite.writeWordSeq, layoutToTyVal] at h_mir_step
      | Ok ap2 =>
          cases h_use : sb_use_mb ap2 s_mir.mem.addrStart tag with
          | Err _ =>
              simp [ConstFreshCtx.stmt, obseq.notation.basePlace, obseq.notation.constRhs,
                mirlite.stepAssignConst, mirlite.finishPlaceAssign, mirlite.allocateBaseAndWrite,
                h_env, h_own, h_use, mirlite.allocate, blockSize, mirlite.writeWordSeq, layoutToTyVal] at h_mir_step
          | Ok ap3 =>
              have h_next :
                  s_mir_next =
                    { s_mir with
                      env := s_mir.env.insert ctx.base (s_mir.mem.addrStart, TyVal.NatTy, tag),
                      mem := mirlite.writeWordSeq
                        { s_mir.mem with addrStart := s_mir.mem.addrStart + blockSize LayoutTy.NatL }
                        s_mir.mem.addrStart [mirlite.MemValue.Val ctx.n],
                      ap := ap3,
                      pc := s_mir.pc + 1 } := by
                simpa [ConstFreshCtx.stmt, obseq.notation.basePlace, obseq.notation.constRhs,
                  mirlite.stepAssignConst, mirlite.finishPlaceAssign, mirlite.allocateBaseAndWrite,
                  h_env, h_own, h_use, mirlite.allocate, blockSize, mirlite.writeWordSeq, layoutToTyVal]
                  using h_mir_step.symm
              have h_valid_ap2 : SBValid ap2 := sb_own_preserves_valid h_valid h_own
              have h_valid_next : SBValid s_mir_next.ap := by
                rw [h_next]
                exact sb_use_mb_preserves_valid h_valid_ap2 h_use
              exact ⟨s_osea_next, h_steps, h_sim_next, h_ap_eq,
                h_valid_next, StateSim.valid_osea h_sim_next⟩

end ConstFresh

end obseq.proof
