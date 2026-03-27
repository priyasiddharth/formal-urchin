import obseq.proof.struct_init_common

/-!
# `obseq.proof.struct_init_fresh`

Local compiler-correctness lemmas for the fresh-destination constant-field
tuple fragment:

- `place(base) ::= StructInitOp [ConstOp n1, ..., ConstOp nk]`

This is the fresh-allocation counterpart to `struct_init_existing`. The target
fragment is an `Alloc` followed by a block `CStore`.
-/

namespace obseq.proof

open obseq
open obseq.mirlite
open obseq.oseair hiding State Result
open obseq.compile
open scoped obseq.notation

structure StructInitFreshCtx where
  base : Word
  fields : List Word
  cs : CompilerState
  h_instrs : CompilerEmpty cs
  h_absent : BaseAbsent cs base
  h_regs : MappedRegsBelowNext cs
  h_fields : fields ≠ []

namespace StructInitFreshCtx

def reg (ctx : StructInitFreshCtx) : Register :=
  Register.R ctx.cs.nextReg

def postPlaceMap (ctx : StructInitFreshCtx) : PlaceMap :=
  (ctx.base, (ctx.reg, wordStructLayout ctx.fields)) :: ctx.cs.placeMap

theorem post_lookup (ctx : StructInitFreshCtx) :
  ctx.postPlaceMap.lookup ctx.base = some (ctx.reg, wordStructLayout ctx.fields) := by
  simp [StructInitFreshCtx.postPlaceMap, StructInitFreshCtx.reg, List.lookup]

def stmt (ctx : StructInitFreshCtx) : mirlite.Stmt :=
  place(ctx.base) ::= wordStructRhs ctx.fields

def compiled (ctx : StructInitFreshCtx) : oseair.Prog :=
  (compileStmt ctx.cs ctx.stmt).instrs

def mirStart (_ctx : StructInitFreshCtx) (s_mir : mirlite.State) : mirlite.State :=
  { s_mir with pc := 0 }

def oseaStart (_ctx : StructInitFreshCtx) (s_osea : oseair.State) : oseair.State :=
  { s_osea with pc := 0 }

theorem instrs_nil (ctx : StructInitFreshCtx) : ctx.cs.instrs = [] :=
  ctx.h_instrs

theorem base_ne_of_old_lookup
  (ctx : StructInitFreshCtx)
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
  (ctx : StructInitFreshCtx)
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

end StructInitFreshCtx

theorem mirlite_step_struct_init_fresh_ok
  (s_mir : mirlite.State)
  (base tag : Word)
  (fields : List Word)
  (ap2 ap3 : AccessPerms)
  (h_env : s_mir.env.lookup base = none)
  (h_own : sb_own s_mir.ap s_mir.mem.addrStart = (SBResult.Ok ap2, tag))
  (h_use : sb_use_mb ap2 s_mir.mem.addrStart tag = SBResult.Ok ap3) :
  mirlite.step { s_mir with pc := 0 } [place(base) ::= wordStructRhs fields] =
    mirlite.Result.Ok
      { s_mir with
        env := s_mir.env.insert base (s_mir.mem.addrStart, wordStructTy fields, tag),
        mem := mirlite.writeWordSeq
          { s_mir.mem with addrStart := s_mir.mem.addrStart + blockSize (wordStructLayout fields) }
          s_mir.mem.addrStart (wordStructMirVals fields),
        ap := ap3,
        pc := 1 } := by
  have h_words : mirlite.structConstWords? (List.map mirlite.RExpr.ConstOp fields) = some fields := by
    simpa [wordStructFields] using mirlite_structConstWords_wordStructFields fields
  simp [mirlite.step, obseq.notation.basePlace, wordStructRhs, wordStructFields,
    mirlite.structConstWords?, h_words, mirlite.stepAssignStructWords,
    mirlite.finishPlaceAssign, mirlite.allocateBaseAndWrite,
    h_env, h_own, h_use, mirlite.allocate, blockSize, wordStructTy, wordStructMirVals]

theorem mirlite_step_struct_init_fresh_inv
  (s_mir : mirlite.State)
  (base : Word)
  (fields : List Word)
  (s_mir_next : mirlite.State)
  (h_env : s_mir.env.lookup base = none)
  (h_step :
    mirlite.step { s_mir with pc := 0 } [place(base) ::= wordStructRhs fields] =
      mirlite.Result.Ok s_mir_next) :
  ∃ tag ap2 ap3,
    sb_own s_mir.ap s_mir.mem.addrStart = (SBResult.Ok ap2, tag) ∧
    sb_use_mb ap2 s_mir.mem.addrStart tag = SBResult.Ok ap3 ∧
    s_mir_next =
      { s_mir with
        env := s_mir.env.insert base (s_mir.mem.addrStart, wordStructTy fields, tag),
        mem := mirlite.writeWordSeq
          { s_mir.mem with addrStart := s_mir.mem.addrStart + blockSize (wordStructLayout fields) }
          s_mir.mem.addrStart (wordStructMirVals fields),
        ap := ap3,
        pc := 1 } := by
  cases h_own : sb_own s_mir.ap s_mir.mem.addrStart with
  | mk ownRes tag =>
      cases ownRes with
      | Err _ =>
          have : False := by
            have h_words : mirlite.structConstWords? (List.map mirlite.RExpr.ConstOp fields) = some fields := by
              simpa [wordStructFields] using mirlite_structConstWords_wordStructFields fields
            simp [mirlite.step, obseq.notation.basePlace, wordStructRhs, wordStructFields,
              mirlite.structConstWords?, h_words, mirlite.stepAssignStructWords,
              mirlite.finishPlaceAssign, mirlite.allocateBaseAndWrite,
              h_env, h_own, mirlite.allocate, blockSize, wordStructTy, wordStructMirVals] at h_step
          contradiction
      | Ok ap2 =>
          cases h_use : sb_use_mb ap2 s_mir.mem.addrStart tag with
          | Err _ =>
              have : False := by
                have h_words : mirlite.structConstWords? (List.map mirlite.RExpr.ConstOp fields) = some fields := by
                  simpa [wordStructFields] using mirlite_structConstWords_wordStructFields fields
                simp [mirlite.step, obseq.notation.basePlace, wordStructRhs, wordStructFields,
                  mirlite.structConstWords?, h_words, mirlite.stepAssignStructWords,
                  mirlite.finishPlaceAssign, mirlite.allocateBaseAndWrite,
                  h_env, h_own, h_use, mirlite.allocate, blockSize, wordStructTy, wordStructMirVals] at h_step
              contradiction
          | Ok ap3 =>
              have h_ok :=
                mirlite_step_struct_init_fresh_ok s_mir base tag fields ap2 ap3 h_env h_own h_use
              rw [h_ok] at h_step
              injection h_step with h_state
              exact ⟨tag, ap2, ap3, rfl, h_use, h_state.symm⟩

@[simp] theorem compile_struct_init_fresh
  (ctx : StructInitFreshCtx) :
  ctx.compiled =
    [oseair.Instr.Assgn ctx.reg (oseair.Rhs.Alloc (wordStructTy ctx.fields)),
     oseair.Instr.CStore (wordStructTy ctx.fields) (wordStructOseaVals ctx.fields) ctx.reg] := by
  have h_place :
      placeToReg ctx.cs { base := ctx.base, path := [] } mirlite.RefKind.Mut
        (some (wordStructLayout ctx.fields)) =
        { reg := ctx.reg, layout := wordStructLayout ctx.fields, cleanup := [],
          cs :=
            { nextReg := ctx.cs.nextReg + 1,
              placeMap := (ctx.base, (ctx.reg, wordStructLayout ctx.fields)) :: ctx.cs.placeMap,
              instrs := ctx.cs.instrs ++
                [oseair.Instr.Assgn ctx.reg (oseair.Rhs.Alloc (wordStructTy ctx.fields))] } } := by
    unfold placeToReg StructInitFreshCtx.reg
    rw [ctx.h_absent]
    simp [freshReg, emit, setPlace, layoutToTyVal_wordStructLayout]
  have h_place' :
      placeToReg ctx.cs { base := ctx.base, path := [] } mirlite.RefKind.Mut
        (some (LayoutTy.TupL (List.replicate ctx.fields.length LayoutTy.NatL))) =
        { reg := ctx.reg,
          layout := LayoutTy.TupL (List.replicate ctx.fields.length LayoutTy.NatL),
          cleanup := [],
          cs :=
            { nextReg := ctx.cs.nextReg + 1,
              placeMap :=
                (ctx.base, (ctx.reg, LayoutTy.TupL (List.replicate ctx.fields.length LayoutTy.NatL))) ::
                  ctx.cs.placeMap,
              instrs := ctx.cs.instrs ++
                [oseair.Instr.Assgn ctx.reg
                  (oseair.Rhs.Alloc (TyVal.TupTy (List.replicate ctx.fields.length TyVal.NatTy)))] } } := by
    simpa [wordStructLayout, wordStructTy] using h_place
  have h_words : compile.structConstWords? (List.map mirlite.RExpr.ConstOp ctx.fields) = some ctx.fields := by
    simpa [wordStructFields] using compile_structConstWords_wordStructFields ctx.fields
  simp [StructInitFreshCtx.compiled, StructInitFreshCtx.stmt,
    compileStmt, compile.structConstWords?, h_words, h_place', emit, cleanupInstrs, ctx.instrs_nil,
    obseq.notation.basePlace, wordStructRhs, wordStructFields, wordStructTy, wordStructOseaVals]

theorem osea_steps_struct_init_fresh_ok
  (s_osea : oseair.State)
  (reg : Register)
  (fields : List Word)
  (tag : Word)
  (ap2 ap3 : AccessPerms)
  (h_size : 0 < blockSize (wordStructLayout fields))
  (h_own : sb_own s_osea.ap s_osea.mem.addrStart = (SBResult.Ok ap2, tag))
  (h_use : sb_use_mb ap2 s_osea.mem.addrStart tag = SBResult.Ok ap3) :
  StepStar
    { s_osea with pc := 0 }
    [oseair.Instr.Assgn reg (oseair.Rhs.Alloc (wordStructTy fields)),
     oseair.Instr.CStore (wordStructTy fields) (wordStructOseaVals fields) reg]
    { s_osea with
      reg := s_osea.reg.insert reg
        (TyVal.PTy, [oseair.Val.Ptr s_osea.mem.addrStart 0 (blockSize (wordStructLayout fields)) tag]),
      mem := oseair.writeWordSeq
        { s_osea.mem with addrStart := s_osea.mem.addrStart + blockSize (wordStructLayout fields) }
        s_osea.mem.addrStart (wordStructOseaVals fields),
      ap := ap3,
      pc := 2 } := by
  simpa [wordStructTy, wordStructOseaVals, layoutToTyVal_wordStructLayout] using
    osea_steps_alloc_cstore_ok s_osea (wordStructLayout fields) (wordStructOseaVals fields)
      reg tag ap2 ap3 h_size h_own h_use

section StructInitFresh

variable (ctx : StructInitFreshCtx)
variable (s_mir : mirlite.State)
variable (s_osea : oseair.State)
variable (s_mir_next : mirlite.State)

theorem local_simulation_struct_init_fresh
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
      mirlite.step { s_mir with pc := 0 } [place(ctx.base) ::= wordStructRhs ctx.fields] =
        mirlite.Result.Ok s_mir_next := by
    unfold StructInitFreshCtx.mirStart StructInitFreshCtx.stmt at h_mir_step
    exact h_mir_step
  let ⟨tag, ap2, ap3, h_own, h_use, h_next⟩ :=
    mirlite_step_struct_init_fresh_inv s_mir ctx.base ctx.fields s_mir_next h_env h_mir_step'
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
      env := s_mir.env.insert ctx.base (s_mir.mem.addrStart, wordStructTy ctx.fields, tag),
      mem := mirlite.writeWordSeq
        { s_mir.mem with addrStart := s_mir.mem.addrStart + blockSize (wordStructLayout ctx.fields) }
        s_mir.mem.addrStart (wordStructMirVals ctx.fields),
      ap := ap3,
      pc := 1 }
  let s_osea_post :=
    { s_osea with
      reg := s_osea.reg.insert ctx.reg
        (TyVal.PTy, [oseair.Val.Ptr s_osea.mem.addrStart 0 (blockSize (wordStructLayout ctx.fields)) tag]),
      mem := oseair.writeWordSeq
        { s_osea.mem with addrStart := s_osea.mem.addrStart + blockSize (wordStructLayout ctx.fields) }
        s_osea.mem.addrStart (wordStructOseaVals ctx.fields),
      ap := ap3,
      pc := 2 }
  have h_target_exec :
      StepStar (ctx.oseaStart s_osea) ctx.compiled s_osea_post := by
    rw [compile_struct_init_fresh ctx]
    exact osea_steps_struct_init_fresh_ok s_osea ctx.reg ctx.fields tag ap2 ap3
      (wordStruct_nonempty_size ctx.h_fields) h_target_own h_target_use
  refine ⟨s_osea_post, h_target_exec, ?_⟩
  refine ⟨h_valid_ap3, h_valid_ap3, rfl, by
    simp [s_mir_post, s_osea_post, h_addrStart], ?_⟩
  · intro base reg layout h_lookup_post
    by_cases h_base : base = ctx.base
    · subst base
      have h_lookup_new : ctx.reg = reg ∧ wordStructLayout ctx.fields = layout := by
        simpa [StructInitFreshCtx.postPlaceMap, List.lookup] using h_lookup_post
      rcases h_lookup_new with ⟨h_reg_eq, h_layout_eq⟩
      subst reg layout
      refine ⟨s_mir.mem.addrStart, tag, ?_, ?_⟩
      · refine ⟨ctx.post_lookup, ?_, ?_⟩
        · simp [s_mir_post]
        · simp [s_osea_post, StructInitFreshCtx.reg, h_addrStart]
      · refine ⟨by
          simp [s_mir_post, s_osea_post, h_addrStart], ?_⟩
        intro i hi
        have h_i_mir : i < (wordStructMirVals ctx.fields).length := by
          simpa using hi
        have h_i_osea : i < (wordStructOseaVals ctx.fields).length := by
          simpa using hi
        have h_mir_written :
            { s_mir with
              env := s_mir.env.insert ctx.base (s_mir.mem.addrStart, wordStructTy ctx.fields, tag),
              mem := mirlite.writeWordSeq
                { s_mir.mem with addrStart := s_mir.mem.addrStart + blockSize (wordStructLayout ctx.fields) }
                s_mir.mem.addrStart (wordStructMirVals ctx.fields),
              ap := ap3,
              pc := 1 }.mem.find? (s_mir.mem.addrStart + i) =
              (wordStructMirVals ctx.fields).get? i := by
          simpa [s_mir_post] using
            mir_mem_find_writeWordSeq_written
              (m := { s_mir.mem with addrStart := s_mir.mem.addrStart + blockSize (wordStructLayout ctx.fields) })
              (addr := s_mir.mem.addrStart)
              (vals := wordStructMirVals ctx.fields)
              (i := i) h_i_mir
        have h_osea_written :
            { s_osea with
              reg := s_osea.reg.insert ctx.reg
                (TyVal.PTy, [oseair.Val.Ptr s_osea.mem.addrStart 0 (blockSize (wordStructLayout ctx.fields)) tag]),
              mem := oseair.writeWordSeq
                { s_osea.mem with addrStart := s_osea.mem.addrStart + blockSize (wordStructLayout ctx.fields) }
                s_osea.mem.addrStart (wordStructOseaVals ctx.fields),
              ap := ap3,
              pc := 2 }.mem.find? (s_mir.mem.addrStart + i) =
              (wordStructOseaVals ctx.fields).get? i := by
          simpa [s_osea_post, h_addrStart] using
            osea_mem_find_writeWordSeq_written
              (m := { s_osea.mem with addrStart := s_osea.mem.addrStart + blockSize (wordStructLayout ctx.fields) })
              (addr := s_osea.mem.addrStart)
              (vals := wordStructOseaVals ctx.fields)
              (i := i) h_i_osea
        rw [h_mir_written, h_osea_written]
        exact mem_vals_eq_get? (mem_vals_eq_words ctx.fields) i
    · have h_lookup_old : ctx.cs.placeMap.lookup base = some (reg, layout) := by
        have h_beq : (base == ctx.base) = false := by
          simp [h_base]
        simpa [StructInitFreshCtx.postPlaceMap, List.lookup, h_beq] using h_lookup_post
      let ⟨addr0, tag0, h_ptr0, h_mem0⟩ := StateSim.place h_sim h_lookup_old
      have h_base_ne := ctx.base_ne_of_old_lookup h_lookup_old
      have h_reg_ne := ctx.reg_ne_of_old_lookup h_lookup_old
      refine ⟨addr0, tag0, ?_, ?_⟩
      · refine ⟨h_lookup_post, ?_, ?_⟩
        · calc
            (s_mir.env.insert ctx.base (s_mir.mem.addrStart, wordStructTy ctx.fields, tag)).lookup base
                = s_mir.env.lookup base := by
                  simpa using env_lookup_insert_ne s_mir.env ctx.base base
                    (s_mir.mem.addrStart, wordStructTy ctx.fields, tag) h_base_ne
            _ = some (addr0, layoutToTyVal layout, tag0) := h_ptr0.2.1
        · calc
            (s_osea.reg.insert ctx.reg
                (TyVal.PTy,
                  [oseair.Val.Ptr s_osea.mem.addrStart 0 (blockSize (wordStructLayout ctx.fields)) tag])).lookup reg
                = s_osea.reg.lookup reg := by
                  simpa using reg_lookup_insert_ne s_osea.reg ctx.reg reg
                    (TyVal.PTy,
                      [oseair.Val.Ptr s_osea.mem.addrStart 0 (blockSize (wordStructLayout ctx.fields)) tag]) h_reg_ne
            _ = some (TyVal.PTy, [oseair.Val.Ptr addr0 0 (blockSize layout) tag0]) := h_ptr0.2.2
      · let s_mir_alloc : mirlite.State :=
          { s_mir_post with
            mem := { s_mir.mem with addrStart := s_mir.mem.addrStart + blockSize (wordStructLayout ctx.fields) } }
        let s_osea_alloc : oseair.State :=
          { s_osea_post with
            mem := { s_osea.mem with addrStart := s_osea.mem.addrStart + blockSize (wordStructLayout ctx.fields) } }
        have h_alloc_mem : sim_mem_at s_mir_alloc s_osea_alloc addr0 layout := by
          refine ⟨by
            simp [s_mir_alloc, s_osea_alloc, s_mir_post, s_osea_post,
              h_addrStart, h_mem0.1], ?_⟩
          intro i hi
          exact h_mem0.2 i hi
        have h_disjoint :
            interval_disjoint addr0 (blockSize layout) s_mir.mem.addrStart
              (blockSize (wordStructLayout ctx.fields)) :=
          (StateSim.fresh_interval
            (freshSize := blockSize (wordStructLayout ctx.fields))
            h_sim h_lookup_old h_ptr0.2.1 h_ptr0.2.2).1
        simpa [s_mir_post, s_osea_post, s_mir_alloc, s_osea_alloc, h_addrStart] using
          (sim_mem_at_write_disjoint
            (s_mir := s_mir_alloc)
            (s_osea := s_osea_alloc)
            (trackedAddr := addr0)
            (layout := layout)
            (dst := s_mir.mem.addrStart)
            (writtenSize := blockSize (wordStructLayout ctx.fields))
            (vals_mir := wordStructMirVals ctx.fields)
            (vals_osea := wordStructOseaVals ctx.fields)
            h_alloc_mem
            (by simp)
            (by simp)
            h_disjoint)

theorem local_preservation_struct_init_fresh
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
    local_simulation_struct_init_fresh ctx s_mir s_osea s_mir_next h_sim h_env h_mir_step
  exact ⟨s_osea_next, h_steps, h_sim_next, StateSim.ap_eq h_sim_next⟩

theorem local_validity_struct_init_fresh
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
    local_preservation_struct_init_fresh ctx s_mir s_osea s_mir_next h_sim h_env h_mir_step
  let ⟨tag, ap2, ap3, h_own, h_use, h_next⟩ :=
    mirlite_step_struct_init_fresh_inv s_mir ctx.base ctx.fields s_mir_next h_env (by
      unfold StructInitFreshCtx.mirStart StructInitFreshCtx.stmt at h_mir_step
      exact h_mir_step)
  let ⟨s_osea_next, h_steps, h_sim_next, h_ap_eq⟩ := h_pres
  have h_valid_ap2 : SBValid ap2 := sb_own_preserves_valid h_valid h_own
  have h_valid_mir_next : SBValid s_mir_next.ap := by
    rw [h_next]
    exact sb_use_mb_preserves_valid h_valid_ap2 h_use
  exact ⟨s_osea_next, h_steps, h_sim_next, h_ap_eq, h_valid_mir_next, StateSim.valid_osea h_sim_next⟩

theorem embedded_simulation_struct_init_fresh
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
          have h_words : mirlite.structConstWords? (List.map mirlite.RExpr.ConstOp ctx.fields) = some ctx.fields := by
            simpa [wordStructFields] using mirlite_structConstWords_wordStructFields ctx.fields
          simp [StructInitFreshCtx.stmt, obseq.notation.basePlace, wordStructRhs, wordStructFields,
            mirlite.structConstWords?, h_words, mirlite.stepAssignStructWords,
            mirlite.finishPlaceAssign, mirlite.allocateBaseAndWrite,
            h_env, h_own, mirlite.allocate, blockSize, wordStructTy, wordStructMirVals] at h_mir_step
      | Ok ap2 =>
          cases h_use : sb_use_mb ap2 s_mir.mem.addrStart tag with
          | Err _ =>
              have h_words : mirlite.structConstWords? (List.map mirlite.RExpr.ConstOp ctx.fields) = some ctx.fields := by
                simpa [wordStructFields] using mirlite_structConstWords_wordStructFields ctx.fields
              simp [StructInitFreshCtx.stmt, obseq.notation.basePlace, wordStructRhs, wordStructFields,
                mirlite.structConstWords?, h_words, mirlite.stepAssignStructWords,
                mirlite.finishPlaceAssign, mirlite.allocateBaseAndWrite,
                h_env, h_own, h_use, mirlite.allocate, blockSize, wordStructTy, wordStructMirVals] at h_mir_step
          | Ok ap3 =>
              have h_words : mirlite.structConstWords? (List.map mirlite.RExpr.ConstOp ctx.fields) = some ctx.fields := by
                simpa [wordStructFields] using mirlite_structConstWords_wordStructFields ctx.fields
              have h_next_full :
                  s_mir_next =
                    { s_mir with
                      env := s_mir.env.insert ctx.base (s_mir.mem.addrStart, wordStructTy ctx.fields, tag),
                      mem := mirlite.writeWordSeq
                        { s_mir.mem with addrStart := s_mir.mem.addrStart + blockSize (wordStructLayout ctx.fields) }
                        s_mir.mem.addrStart (wordStructMirVals ctx.fields),
                      ap := ap3,
                      pc := s_mir.pc + 1 } := by
                simpa [StructInitFreshCtx.stmt, obseq.notation.basePlace, wordStructRhs, wordStructFields,
                  mirlite.structConstWords?, h_words, mirlite.stepAssignStructWords,
                  mirlite.finishPlaceAssign, mirlite.allocateBaseAndWrite,
                  h_env, h_own, h_use, mirlite.allocate, blockSize, wordStructTy, wordStructMirVals]
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
              rw [compile_struct_init_fresh ctx] at h_osea_start
              have h_stmt_osea0 :
                  prog_osea.get? s_osea.pc =
                    some (oseair.Instr.Assgn ctx.reg (oseair.Rhs.Alloc (wordStructTy ctx.fields))) := by
                simpa [StartsAt, Nat.zero_add] using (h_osea_start 0).symm
              have h_osea_tail := StartsAt.tail h_osea_start
              have h_stmt_osea1 :
                  prog_osea.get? (s_osea.pc + 1) =
                    some (oseair.Instr.CStore (wordStructTy ctx.fields) (wordStructOseaVals ctx.fields) ctx.reg) := by
                simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using StartsAt.singleton h_osea_tail
              rcases List.get?_eq_some_iff.mp h_stmt_osea0 with ⟨h_pc_osea0, h_get_osea0⟩
              rcases List.get?_eq_some_iff.mp h_stmt_osea1 with ⟨h_pc_osea1, h_get_osea1⟩
              let s1 : oseair.State :=
                { s_osea with
                  reg := s_osea.reg.insert ctx.reg
                    (TyVal.PTy, [oseair.Val.Ptr s_osea.mem.addrStart 0 (blockSize (wordStructLayout ctx.fields)) tag]),
                  mem := { s_osea.mem with addrStart := s_osea.mem.addrStart + blockSize (wordStructLayout ctx.fields) },
                  ap := ap2,
                  pc := s_osea.pc + 1 }
              let s_osea_post :=
                { s_osea with
                  reg := s_osea.reg.insert ctx.reg
                    (TyVal.PTy, [oseair.Val.Ptr s_osea.mem.addrStart 0 (blockSize (wordStructLayout ctx.fields)) tag]),
                  mem := oseair.writeWordSeq
                    { s_osea.mem with addrStart := s_osea.mem.addrStart + blockSize (wordStructLayout ctx.fields) }
                    s_osea.mem.addrStart (wordStructOseaVals ctx.fields),
                  ap := ap3,
                  pc := s_osea.pc + 2 }
              let s_mir_post :=
                { s_mir with
                  env := s_mir.env.insert ctx.base (s_mir.mem.addrStart, wordStructTy ctx.fields, tag),
                  mem := mirlite.writeWordSeq
                    { s_mir.mem with addrStart := s_mir.mem.addrStart + blockSize (wordStructLayout ctx.fields) }
                    s_mir.mem.addrStart (wordStructMirVals ctx.fields),
                  ap := ap3,
                  pc := s_mir.pc + 1 }
              have h_size : 0 < blockSize (wordStructLayout ctx.fields) :=
                wordStruct_nonempty_size ctx.h_fields
              have h_size_len : 0 < ctx.fields.length := by
                simpa using h_size
              have h_step1_full :
                  oseair.step s_osea prog_osea = oseair.Result.Ok s1 := by
                unfold oseair.step
                rw [dif_pos h_pc_osea0, h_get_osea0]
                unfold oseair.evalRhs
                simp [h_target_own, s1, oseair.allocate, blockSize]
              have h_reg1 :
                  s1.reg.lookup ctx.reg =
                    some (TyVal.PTy, [oseair.Val.Ptr s_osea.mem.addrStart 0 (blockSize (wordStructLayout ctx.fields)) tag]) := by
                simp [s1]
              have h_step2_full :
                  oseair.step s1 prog_osea = oseair.Result.Ok s_osea_post := by
                unfold oseair.step oseair.writeThroughPtr
                rw [dif_pos h_pc_osea1, h_get_osea1]
                have h_in_bounds :
                    s_osea.mem.addrStart < s_osea.mem.addrStart + blockSize (wordStructLayout ctx.fields) := by
                  have h_add :
                      s_osea.mem.addrStart + 0 <
                        s_osea.mem.addrStart + blockSize (wordStructLayout ctx.fields) :=
                    Nat.add_lt_add_left h_size s_osea.mem.addrStart
                  simpa using h_add
                have h_bound :
                    ¬ s_osea.mem.addrStart >= s_osea.mem.addrStart + blockSize (wordStructLayout ctx.fields) := by
                  intro h_ge
                  exact (Nat.lt_irrefl s_osea.mem.addrStart) (Nat.lt_of_lt_of_le h_in_bounds h_ge)
                simp [s1, s_osea_post, h_reg1, h_target_use, h_bound, h_size, h_size_len]
              refine ⟨s_osea_post, StepStar.trans (StepStar.single h_step1_full) (StepStar.single h_step2_full), ?_⟩
              rw [h_next_full]
              refine ⟨h_valid_ap3, h_valid_ap3, rfl, by
                simp [s_mir_post, s_osea_post, h_addrStart], ?_⟩
              · intro base reg layout h_lookup_post
                by_cases h_base : base = ctx.base
                · subst base
                  have h_lookup_new : ctx.reg = reg ∧ wordStructLayout ctx.fields = layout := by
                    simpa [StructInitFreshCtx.postPlaceMap, List.lookup] using h_lookup_post
                  rcases h_lookup_new with ⟨h_reg_eq, h_layout_eq⟩
                  subst reg layout
                  refine ⟨s_mir.mem.addrStart, tag, ?_, ?_⟩
                  · refine ⟨ctx.post_lookup, ?_, ?_⟩
                    · simp [s_mir_post]
                    · simp [s_osea_post, StructInitFreshCtx.reg, h_addrStart]
                  · refine ⟨by
                      simp [s_mir_post, s_osea_post, h_addrStart], ?_⟩
                    intro i hi
                    have h_i_mir : i < (wordStructMirVals ctx.fields).length := by
                      simpa using hi
                    have h_i_osea : i < (wordStructOseaVals ctx.fields).length := by
                      simpa using hi
                    have h_mir_written :
                        { s_mir with
                          env := s_mir.env.insert ctx.base (s_mir.mem.addrStart, wordStructTy ctx.fields, tag),
                          mem := mirlite.writeWordSeq
                            { s_mir.mem with addrStart := s_mir.mem.addrStart + blockSize (wordStructLayout ctx.fields) }
                            s_mir.mem.addrStart (wordStructMirVals ctx.fields),
                          ap := ap3,
                          pc := s_mir.pc + 1 }.mem.find? (s_mir.mem.addrStart + i) =
                          (wordStructMirVals ctx.fields).get? i := by
                      simpa [s_mir_post] using
                        mir_mem_find_writeWordSeq_written
                          (m := { s_mir.mem with addrStart := s_mir.mem.addrStart + blockSize (wordStructLayout ctx.fields) })
                          (addr := s_mir.mem.addrStart)
                          (vals := wordStructMirVals ctx.fields)
                          (i := i) h_i_mir
                    have h_osea_written :
                        { s_osea with
                          reg := s_osea.reg.insert ctx.reg
                            (TyVal.PTy, [oseair.Val.Ptr s_osea.mem.addrStart 0 (blockSize (wordStructLayout ctx.fields)) tag]),
                          mem := oseair.writeWordSeq
                            { s_osea.mem with addrStart := s_osea.mem.addrStart + blockSize (wordStructLayout ctx.fields) }
                            s_osea.mem.addrStart (wordStructOseaVals ctx.fields),
                          ap := ap3,
                          pc := s_osea.pc + 2 }.mem.find? (s_mir.mem.addrStart + i) =
                          (wordStructOseaVals ctx.fields).get? i := by
                      simpa [s_osea_post, h_addrStart] using
                        osea_mem_find_writeWordSeq_written
                          (m := { s_osea.mem with addrStart := s_osea.mem.addrStart + blockSize (wordStructLayout ctx.fields) })
                          (addr := s_osea.mem.addrStart)
                          (vals := wordStructOseaVals ctx.fields)
                          (i := i) h_i_osea
                    rw [h_mir_written, h_osea_written]
                    exact mem_vals_eq_get? (mem_vals_eq_words ctx.fields) i
                · have h_lookup_old : ctx.cs.placeMap.lookup base = some (reg, layout) := by
                    have h_beq : (base == ctx.base) = false := by simp [h_base]
                    simpa [StructInitFreshCtx.postPlaceMap, List.lookup, h_beq] using h_lookup_post
                  let ⟨addr0, tag0, h_ptr0, h_mem0⟩ := StateSim.place h_sim h_lookup_old
                  have h_base_ne := ctx.base_ne_of_old_lookup h_lookup_old
                  have h_reg_ne := ctx.reg_ne_of_old_lookup h_lookup_old
                  refine ⟨addr0, tag0, ?_, ?_⟩
                  · refine ⟨h_lookup_post, ?_, ?_⟩
                    · calc
                        (s_mir.env.insert ctx.base (s_mir.mem.addrStart, wordStructTy ctx.fields, tag)).lookup base
                            = s_mir.env.lookup base := by
                              simpa using env_lookup_insert_ne s_mir.env ctx.base base
                                (s_mir.mem.addrStart, wordStructTy ctx.fields, tag) h_base_ne
                        _ = some (addr0, layoutToTyVal layout, tag0) := h_ptr0.2.1
                    · calc
                        (s_osea.reg.insert ctx.reg
                            (TyVal.PTy,
                              [oseair.Val.Ptr s_osea.mem.addrStart 0 (blockSize (wordStructLayout ctx.fields)) tag])).lookup reg
                            = s_osea.reg.lookup reg := by
                              simpa using reg_lookup_insert_ne s_osea.reg ctx.reg reg
                                (TyVal.PTy,
                                  [oseair.Val.Ptr s_osea.mem.addrStart 0 (blockSize (wordStructLayout ctx.fields)) tag]) h_reg_ne
                        _ = some (TyVal.PTy, [oseair.Val.Ptr addr0 0 (blockSize layout) tag0]) := h_ptr0.2.2
                  · let s_mir_alloc : mirlite.State :=
                      { s_mir_post with
                        mem := { s_mir.mem with addrStart := s_mir.mem.addrStart + blockSize (wordStructLayout ctx.fields) } }
                    let s_osea_alloc : oseair.State :=
                      { s_osea_post with
                        mem := { s_osea.mem with addrStart := s_osea.mem.addrStart + blockSize (wordStructLayout ctx.fields) } }
                    have h_alloc_mem : sim_mem_at s_mir_alloc s_osea_alloc addr0 layout := by
                      refine ⟨by
                        simp [s_mir_alloc, s_osea_alloc, s_mir_post, s_osea_post,
                          h_addrStart, h_mem0.1], ?_⟩
                      intro i hi
                      exact h_mem0.2 i hi
                    have h_disjoint :
                        interval_disjoint addr0 (blockSize layout) s_mir.mem.addrStart
                          (blockSize (wordStructLayout ctx.fields)) :=
                      (StateSim.fresh_interval
                        (freshSize := blockSize (wordStructLayout ctx.fields))
                        h_sim h_lookup_old h_ptr0.2.1 h_ptr0.2.2).1
                    simpa [s_mir_post, s_osea_post, s_mir_alloc, s_osea_alloc, h_addrStart] using
                      (sim_mem_at_write_disjoint
                        (s_mir := s_mir_alloc)
                        (s_osea := s_osea_alloc)
                        (trackedAddr := addr0)
                        (layout := layout)
                        (dst := s_mir.mem.addrStart)
                        (writtenSize := blockSize (wordStructLayout ctx.fields))
                        (vals_mir := wordStructMirVals ctx.fields)
                        (vals_osea := wordStructOseaVals ctx.fields)
                        h_alloc_mem
                        (by simp)
                        (by simp)
                        h_disjoint)

theorem embedded_preservation_struct_init_fresh
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
    embedded_simulation_struct_init_fresh ctx s_mir s_osea s_mir_next
      prog_mir prog_osea h_sim h_env h_mir_start h_osea_start h_mir_step
  exact ⟨s_osea_next, h_steps, h_sim_next, StateSim.ap_eq h_sim_next⟩

theorem embedded_validity_struct_init_fresh
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
    embedded_preservation_struct_init_fresh ctx s_mir s_osea s_mir_next
      prog_mir prog_osea h_sim h_env h_mir_start h_osea_start h_mir_step
  have h_stmt_mir : prog_mir.get? s_mir.pc = some ctx.stmt := StartsAt.singleton h_mir_start
  rcases List.get?_eq_some_iff.mp h_stmt_mir with ⟨h_pc_mir, h_get_mir⟩
  unfold mirlite.step at h_mir_step
  rw [dif_pos h_pc_mir, h_get_mir] at h_mir_step
  cases h_own : sb_own s_mir.ap s_mir.mem.addrStart with
  | mk ownRes tag =>
      cases ownRes with
      | Err _ =>
          have h_words : mirlite.structConstWords? (List.map mirlite.RExpr.ConstOp ctx.fields) = some ctx.fields := by
            simpa [wordStructFields] using mirlite_structConstWords_wordStructFields ctx.fields
          simp [StructInitFreshCtx.stmt, obseq.notation.basePlace, wordStructRhs, wordStructFields,
            mirlite.structConstWords?, h_words, mirlite.stepAssignStructWords,
            mirlite.finishPlaceAssign, mirlite.allocateBaseAndWrite,
            h_env, h_own, mirlite.allocate, blockSize, wordStructTy, wordStructMirVals] at h_mir_step
      | Ok ap2 =>
          cases h_use : sb_use_mb ap2 s_mir.mem.addrStart tag with
          | Err _ =>
              have h_words : mirlite.structConstWords? (List.map mirlite.RExpr.ConstOp ctx.fields) = some ctx.fields := by
                simpa [wordStructFields] using mirlite_structConstWords_wordStructFields ctx.fields
              simp [StructInitFreshCtx.stmt, obseq.notation.basePlace, wordStructRhs, wordStructFields,
                mirlite.structConstWords?, h_words, mirlite.stepAssignStructWords,
                mirlite.finishPlaceAssign, mirlite.allocateBaseAndWrite,
                h_env, h_own, h_use, mirlite.allocate, blockSize, wordStructTy, wordStructMirVals] at h_mir_step
          | Ok ap3 =>
              have h_words : mirlite.structConstWords? (List.map mirlite.RExpr.ConstOp ctx.fields) = some ctx.fields := by
                simpa [wordStructFields] using mirlite_structConstWords_wordStructFields ctx.fields
              have h_next :
                  s_mir_next =
                    { s_mir with
                      env := s_mir.env.insert ctx.base (s_mir.mem.addrStart, wordStructTy ctx.fields, tag),
                      mem := mirlite.writeWordSeq
                        { s_mir.mem with addrStart := s_mir.mem.addrStart + blockSize (wordStructLayout ctx.fields) }
                        s_mir.mem.addrStart (wordStructMirVals ctx.fields),
                      ap := ap3,
                      pc := s_mir.pc + 1 } := by
                simpa [StructInitFreshCtx.stmt, obseq.notation.basePlace, wordStructRhs, wordStructFields,
                  mirlite.structConstWords?, h_words, mirlite.stepAssignStructWords,
                  mirlite.finishPlaceAssign, mirlite.allocateBaseAndWrite,
                  h_env, h_own, h_use, mirlite.allocate, blockSize, wordStructTy, wordStructMirVals]
                  using h_mir_step.symm
              have h_valid_ap2 : SBValid ap2 := sb_own_preserves_valid h_valid h_own
              have h_valid_next : SBValid s_mir_next.ap := by
                rw [h_next]
                exact sb_use_mb_preserves_valid h_valid_ap2 h_use
              exact ⟨s_osea_next, h_steps, h_sim_next, h_ap_eq, h_valid_next, StateSim.valid_osea h_sim_next⟩

end StructInitFresh

end obseq.proof
