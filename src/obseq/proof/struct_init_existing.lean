import obseq.proof.struct_init_common

/-!
# `obseq.proof.struct_init_existing`

Local compiler-correctness lemmas for the existing-destination constant-field
tuple fragment:

- `place(base) ::= StructInitOp [ConstOp n1, ..., ConstOp nk]`

This file contains the local proof kernel. The tuple payload is flattened
left-to-right on both MIR and OSEA sides.
-/

namespace obseq.proof

open obseq
open obseq.mirlite
open obseq.oseair hiding State Result
open obseq.compile
open scoped obseq.notation

structure StructInitExistingCtx where
  base : Word
  reg : Register
  fields : List Word
  cs : CompilerState
  h_instrs : CompilerEmpty cs
  h_fields : fields ≠ []
  h_lookup : BaseReady cs base reg (wordStructLayout fields)

namespace StructInitExistingCtx

def stmt (ctx : StructInitExistingCtx) : mirlite.Stmt :=
  place(ctx.base) ::= wordStructRhs ctx.fields

def compiled (ctx : StructInitExistingCtx) : oseair.Prog :=
  (compileStmt ctx.cs ctx.stmt).instrs

def mirStart (_ctx : StructInitExistingCtx) (s_mir : mirlite.State) : mirlite.State :=
  { s_mir with pc := 0 }

def oseaStart (_ctx : StructInitExistingCtx) (s_osea : oseair.State) : oseair.State :=
  { s_osea with pc := 0 }

theorem instrs_nil (ctx : StructInitExistingCtx) : ctx.cs.instrs = [] :=
  ctx.h_instrs

end StructInitExistingCtx

abbrev StructInitExistingSim
  (ctx : StructInitExistingCtx)
  (s_mir : mirlite.State)
  (s_osea : oseair.State) : Prop :=
  StateSim ctx.cs.placeMap s_mir s_osea

theorem mirlite_step_struct_init_existing_ok
  (s_mir : mirlite.State)
  (base addr tag : Word)
  (fields : List Word)
  (ap' : AccessPerms)
  (h_env : s_mir.env.lookup base = some (addr, wordStructTy fields, tag))
  (h_use : sb_use_mb s_mir.ap addr tag = SBResult.Ok ap') :
  mirlite.step { s_mir with pc := 0 } [place(base) ::= wordStructRhs fields] =
    mirlite.Result.Ok
      { s_mir with
        ap := ap',
        mem := mirlite.writeWordSeq s_mir.mem addr (wordStructMirVals fields),
        pc := 1 } := by
  have h_words : mirlite.structConstWords? (List.map mirlite.RExpr.ConstOp fields) = some fields := by
    simpa [wordStructFields] using mirlite_structConstWords_wordStructFields fields
  simp [mirlite.step, obseq.notation.basePlace, wordStructRhs, wordStructFields,
    mirlite.structConstWords?, h_words,
    mirlite.stepAssignStructWords,
    mirlite.finishPlaceAssign, mirlite.writeResolvedPlace, h_env, h_use,
    wordStructTy, wordStructMirVals]

theorem mirlite_step_struct_init_existing_inv
  (s_mir : mirlite.State)
  (base addr tag : Word)
  (fields : List Word)
  (s_mir_next : mirlite.State)
  (h_env : s_mir.env.lookup base = some (addr, wordStructTy fields, tag))
  (h_step :
    mirlite.step { s_mir with pc := 0 } [place(base) ::= wordStructRhs fields] =
      mirlite.Result.Ok s_mir_next) :
  ∃ ap',
    sb_use_mb s_mir.ap addr tag = SBResult.Ok ap' ∧
    s_mir_next =
      { s_mir with
        ap := ap',
        mem := mirlite.writeWordSeq s_mir.mem addr (wordStructMirVals fields),
        pc := 1 } := by
  cases h_use : sb_use_mb s_mir.ap addr tag with
  | Ok ap' =>
      have h_ok :=
        mirlite_step_struct_init_existing_ok s_mir base addr tag fields ap' h_env h_use
      rw [h_ok] at h_step
      injection h_step with h_state
      exact ⟨ap', rfl, h_state.symm⟩
  | Err _ =>
      have : False := by
        have h_words : mirlite.structConstWords? (List.map mirlite.RExpr.ConstOp fields) = some fields := by
          simpa [wordStructFields] using mirlite_structConstWords_wordStructFields fields
        simp [mirlite.step, obseq.notation.basePlace, wordStructRhs, wordStructFields,
          mirlite.structConstWords?, h_words,
          mirlite.stepAssignStructWords,
          mirlite.finishPlaceAssign, mirlite.writeResolvedPlace, h_env, h_use,
          wordStructTy, wordStructMirVals] at h_step
      contradiction

@[simp] theorem compile_struct_init_existing
  (ctx : StructInitExistingCtx) :
  ctx.compiled =
    [oseair.Instr.CStore (wordStructTy ctx.fields) (wordStructOseaVals ctx.fields) ctx.reg] := by
  have h_place :
      placeToReg ctx.cs { base := ctx.base, path := [] } mirlite.RefKind.Mut
        (some (wordStructLayout ctx.fields)) =
        { reg := ctx.reg, layout := wordStructLayout ctx.fields, cleanup := [], cs := ctx.cs } := by
    unfold placeToReg
    rw [ctx.h_lookup]
    simp [layoutResolvePath]
  have h_place' :
      placeToReg ctx.cs { base := ctx.base, path := [] } mirlite.RefKind.Mut
        (some (LayoutTy.TupL (List.replicate ctx.fields.length LayoutTy.NatL))) =
        { reg := ctx.reg,
          layout := LayoutTy.TupL (List.replicate ctx.fields.length LayoutTy.NatL),
          cleanup := [], cs := ctx.cs } := by
    simpa [wordStructLayout] using h_place
  have h_words : compile.structConstWords? (List.map mirlite.RExpr.ConstOp ctx.fields) = some ctx.fields := by
    simpa [wordStructFields] using compile_structConstWords_wordStructFields ctx.fields
  simp [StructInitExistingCtx.compiled, StructInitExistingCtx.stmt,
    compileStmt, compile.structConstWords?, h_words, h_place', emit, cleanupInstrs, ctx.instrs_nil,
    obseq.notation.basePlace, wordStructRhs, wordStructFields, wordStructTy, wordStructOseaVals]

theorem local_simulation_struct_init_existing
  (ctx : StructInitExistingCtx)
  (s_mir : mirlite.State)
  (s_osea : oseair.State)
  (s_mir_next : mirlite.State)
  (h_sim : StructInitExistingSim ctx s_mir s_osea)
  (h_mir_step :
    mirlite.step (ctx.mirStart s_mir) [ctx.stmt] =
      mirlite.Result.Ok s_mir_next) :
  ∃ s_osea_next,
    StepStar (ctx.oseaStart s_osea) ctx.compiled s_osea_next ∧
    StructInitExistingSim ctx s_mir_next s_osea_next := by
  let ⟨addr, tag, h_ptr, h_mem⟩ := StateSim.place h_sim ctx.h_lookup
  have h_env :
      s_mir.env.lookup ctx.base = some (addr, wordStructTy ctx.fields, tag) := by
    simpa [wordStructTy] using h_ptr.2.1
  have h_reg :
      s_osea.reg.lookup ctx.reg =
        some (TyVal.PTy, [oseair.Val.Ptr addr 0 (blockSize (wordStructLayout ctx.fields)) tag]) :=
    h_ptr.2.2
  have h_ap : s_mir.ap = s_osea.ap := StateSim.ap_eq h_sim
  have h_addrStart : s_mir.mem.addrStart = s_osea.mem.addrStart := StateSim.addrStart_eq h_sim
  have h_mir_step' :
      mirlite.step { s_mir with pc := 0 } [place(ctx.base) ::= wordStructRhs ctx.fields] =
        mirlite.Result.Ok s_mir_next := by
    unfold StructInitExistingCtx.mirStart StructInitExistingCtx.stmt at h_mir_step
    exact h_mir_step
  let ⟨ap', h_use, h_next⟩ :=
    mirlite_step_struct_init_existing_inv s_mir ctx.base addr tag ctx.fields s_mir_next h_env h_mir_step'
  have h_valid_next_ap : SBValid ap' := by
    exact sb_use_mb_preserves_valid (StateSim.valid_mir h_sim) h_use
  have h_target_use : sb_use_mb s_osea.ap addr tag = SBResult.Ok ap' := by
    rw [← h_ap]
    exact h_use
  subst s_mir_next
  let s_mir_post :=
    { s_mir with
      ap := ap',
      mem := mirlite.writeWordSeq s_mir.mem addr (wordStructMirVals ctx.fields),
      pc := 1 }
  let s_osea_post :=
    { s_osea with
      ap := ap',
      mem := oseair.writeWordSeq s_osea.mem addr (wordStructOseaVals ctx.fields),
      pc := 1 }
  have h_target_exec :
      StepStar (ctx.oseaStart s_osea) ctx.compiled s_osea_post := by
    rw [compile_struct_init_existing ctx]
    exact StepStar.single
      (osea_step_cstore_ok s_osea (wordStructLayout ctx.fields) (wordStructOseaVals ctx.fields)
        addr tag ctx.reg ap' (wordStruct_nonempty_size ctx.h_fields) h_reg h_target_use)
  refine ⟨s_osea_post, h_target_exec, ?_⟩
  refine ⟨h_valid_next_ap, h_valid_next_ap, rfl, by
    simp [s_mir_post, s_osea_post, h_addrStart], ?_⟩
  · intro base reg layout h_lookup
    let ⟨addr0, tag0, h_ptr0, h_mem0⟩ := StateSim.place h_sim h_lookup
    refine ⟨addr0, tag0, ?_, ?_⟩
    · exact ⟨h_lookup, h_ptr0.2.1, h_ptr0.2.2⟩
    · exact sim_mem_at_write h_mem0 (mem_vals_eq_words ctx.fields)

theorem local_preservation_struct_init_existing
  (ctx : StructInitExistingCtx)
  (s_mir : mirlite.State)
  (s_osea : oseair.State)
  (s_mir_next : mirlite.State)
  (h_sim : StructInitExistingSim ctx s_mir s_osea)
  (h_mir_step :
    mirlite.step (ctx.mirStart s_mir) [ctx.stmt] =
      mirlite.Result.Ok s_mir_next) :
  ∃ s_osea_next,
    StepStar (ctx.oseaStart s_osea) ctx.compiled s_osea_next ∧
    StructInitExistingSim ctx s_mir_next s_osea_next ∧
    s_mir_next.ap = s_osea_next.ap := by
  let ⟨s_osea_next, h_steps, h_sim_next⟩ :=
    local_simulation_struct_init_existing ctx s_mir s_osea s_mir_next h_sim h_mir_step
  exact ⟨s_osea_next, h_steps, h_sim_next, StateSim.ap_eq h_sim_next⟩

theorem local_validity_struct_init_existing
  (ctx : StructInitExistingCtx)
  (s_mir : mirlite.State)
  (s_osea : oseair.State)
  (s_mir_next : mirlite.State)
  (h_sim : StructInitExistingSim ctx s_mir s_osea)
  (h_valid : SBValid s_mir.ap)
  (h_mir_step :
    mirlite.step (ctx.mirStart s_mir) [ctx.stmt] =
      mirlite.Result.Ok s_mir_next) :
  ∃ s_osea_next,
    StepStar (ctx.oseaStart s_osea) ctx.compiled s_osea_next ∧
    StructInitExistingSim ctx s_mir_next s_osea_next ∧
    s_mir_next.ap = s_osea_next.ap ∧
    SBValid s_mir_next.ap ∧
    SBValid s_osea_next.ap := by
  have h_pres :=
    local_preservation_struct_init_existing ctx s_mir s_osea s_mir_next h_sim h_mir_step
  let ⟨addr, tag, h_ptr, _h_mem⟩ := StateSim.place h_sim ctx.h_lookup
  have h_env :
      s_mir.env.lookup ctx.base = some (addr, wordStructTy ctx.fields, tag) := by
    simpa [wordStructTy] using h_ptr.2.1
  have h_mir_step' :
      mirlite.step { s_mir with pc := 0 } [place(ctx.base) ::= wordStructRhs ctx.fields] =
        mirlite.Result.Ok s_mir_next := by
    unfold StructInitExistingCtx.mirStart StructInitExistingCtx.stmt at h_mir_step
    exact h_mir_step
  let ⟨ap', h_use, h_next⟩ :=
    mirlite_step_struct_init_existing_inv s_mir ctx.base addr tag ctx.fields s_mir_next h_env h_mir_step'
  let ⟨s_osea_next, h_steps, h_sim_next, h_ap_eq⟩ := h_pres
  have h_valid_mir_next : SBValid s_mir_next.ap := by
    rw [h_next]
    exact sb_use_mb_preserves_valid h_valid h_use
  exact ⟨s_osea_next, h_steps, h_sim_next, h_ap_eq, h_valid_mir_next, StateSim.valid_osea h_sim_next⟩

theorem embedded_simulation_struct_init_existing
  (ctx : StructInitExistingCtx)
  (s_mir : mirlite.State)
  (s_osea : oseair.State)
  (s_mir_next : mirlite.State)
  (prog_mir : mirlite.Prog)
  (prog_osea : oseair.Prog)
  (h_sim : StructInitExistingSim ctx s_mir s_osea)
  (h_mir_start : StartsAt prog_mir s_mir.pc [ctx.stmt])
  (h_osea_start : StartsAt prog_osea s_osea.pc ctx.compiled)
  (h_mir_step : mirlite.step s_mir prog_mir = mirlite.Result.Ok s_mir_next) :
  ∃ s_osea_next,
    StepStar s_osea prog_osea s_osea_next ∧
    StructInitExistingSim ctx s_mir_next s_osea_next := by
  let ⟨addr, tag, h_ptr, h_mem⟩ := StateSim.place h_sim ctx.h_lookup
  have h_env :
      s_mir.env.lookup ctx.base = some (addr, wordStructTy ctx.fields, tag) := by
    simpa [wordStructTy] using h_ptr.2.1
  have h_reg :
      s_osea.reg.lookup ctx.reg =
        some (TyVal.PTy, [oseair.Val.Ptr addr 0 (blockSize (wordStructLayout ctx.fields)) tag]) :=
    h_ptr.2.2
  have h_ap : s_mir.ap = s_osea.ap := StateSim.ap_eq h_sim
  have h_addrStart : s_mir.mem.addrStart = s_osea.mem.addrStart := StateSim.addrStart_eq h_sim
  have h_stmt_mir : prog_mir.get? s_mir.pc = some ctx.stmt := StartsAt.singleton h_mir_start
  rcases List.get?_eq_some_iff.mp h_stmt_mir with ⟨h_pc_mir, h_get_mir⟩
  unfold mirlite.step at h_mir_step
  rw [dif_pos h_pc_mir, h_get_mir] at h_mir_step
  cases h_use : sb_use_mb s_mir.ap addr tag with
  | Err _ =>
      have h_words : mirlite.structConstWords? (List.map mirlite.RExpr.ConstOp ctx.fields) = some ctx.fields := by
        simpa [wordStructFields] using mirlite_structConstWords_wordStructFields ctx.fields
      simp [StructInitExistingCtx.stmt, wordStructRhs, wordStructFields,
        mirlite.structConstWords?, h_words, mirlite.stepAssignStructWords,
        mirlite.finishPlaceAssign, mirlite.writeResolvedPlace,
        obseq.notation.basePlace, h_env, h_use, wordStructTy, wordStructMirVals] at h_mir_step
  | Ok ap' =>
      have h_words : mirlite.structConstWords? (List.map mirlite.RExpr.ConstOp ctx.fields) = some ctx.fields := by
        simpa [wordStructFields] using mirlite_structConstWords_wordStructFields ctx.fields
      have h_next_full :
          s_mir_next =
            { s_mir with
              ap := ap',
              mem := mirlite.writeWordSeq s_mir.mem addr (wordStructMirVals ctx.fields),
              pc := s_mir.pc + 1 } := by
        simpa [StructInitExistingCtx.stmt, wordStructRhs, wordStructFields,
          mirlite.structConstWords?, h_words, mirlite.stepAssignStructWords,
          mirlite.finishPlaceAssign, mirlite.writeResolvedPlace,
          obseq.notation.basePlace, h_env, h_use, wordStructTy, wordStructMirVals] using h_mir_step.symm
      have h_valid_next_ap : SBValid ap' := by
        exact sb_use_mb_preserves_valid (StateSim.valid_mir h_sim) h_use
      have h_target_use : sb_use_mb s_osea.ap addr tag = SBResult.Ok ap' := by
        rw [← h_ap]
        exact h_use
      have h_stmt_osea :
          prog_osea.get? s_osea.pc =
            some (oseair.Instr.CStore (wordStructTy ctx.fields) (wordStructOseaVals ctx.fields) ctx.reg) := by
        rw [compile_struct_init_existing ctx] at h_osea_start
        simpa using StartsAt.singleton h_osea_start
      rcases List.get?_eq_some_iff.mp h_stmt_osea with ⟨h_pc_osea, h_get_osea⟩
      let s_mir_post :=
        { s_mir with
          ap := ap',
          mem := mirlite.writeWordSeq s_mir.mem addr (wordStructMirVals ctx.fields),
          pc := s_mir.pc + 1 }
      let s_osea_post :=
        { s_osea with
          ap := ap',
          mem := oseair.writeWordSeq s_osea.mem addr (wordStructOseaVals ctx.fields),
          pc := s_osea.pc + 1 }
      have h_size : 0 < blockSize (wordStructLayout ctx.fields) :=
        wordStruct_nonempty_size ctx.h_fields
      have h_size_len : 0 < ctx.fields.length := by
        simpa using h_size
      have h_target_full :
          oseair.step s_osea prog_osea = oseair.Result.Ok s_osea_post := by
        unfold oseair.step oseair.writeThroughPtr
        rw [dif_pos h_pc_osea, h_get_osea]
        have h_in_bounds : addr < addr + blockSize (wordStructLayout ctx.fields) := by
          have h_add : addr + 0 < addr + blockSize (wordStructLayout ctx.fields) :=
            Nat.add_lt_add_left h_size addr
          simpa using h_add
        have h_bound : ¬ addr >= addr + blockSize (wordStructLayout ctx.fields) := by
          intro h_ge
          exact (Nat.lt_irrefl addr) (Nat.lt_of_lt_of_le h_in_bounds h_ge)
        simp [s_osea_post, h_reg, h_target_use, h_bound, h_size, h_size_len]
      refine ⟨s_osea_post, StepStar.single h_target_full, ?_⟩
      rw [h_next_full]
      refine ⟨h_valid_next_ap, h_valid_next_ap, rfl, by
        simp [s_mir_post, s_osea_post, h_addrStart], ?_⟩
      · intro base reg layout h_lookup
        let ⟨addr0, tag0, h_ptr0, h_mem0⟩ := StateSim.place h_sim h_lookup
        refine ⟨addr0, tag0, ?_, ?_⟩
        · exact ⟨h_lookup, h_ptr0.2.1, h_ptr0.2.2⟩
        · exact sim_mem_at_write h_mem0 (mem_vals_eq_words ctx.fields)

theorem embedded_preservation_struct_init_existing
  (ctx : StructInitExistingCtx)
  (s_mir : mirlite.State)
  (s_osea : oseair.State)
  (s_mir_next : mirlite.State)
  (prog_mir : mirlite.Prog)
  (prog_osea : oseair.Prog)
  (h_sim : StructInitExistingSim ctx s_mir s_osea)
  (h_mir_start : StartsAt prog_mir s_mir.pc [ctx.stmt])
  (h_osea_start : StartsAt prog_osea s_osea.pc ctx.compiled)
  (h_mir_step : mirlite.step s_mir prog_mir = mirlite.Result.Ok s_mir_next) :
  ∃ s_osea_next,
    StepStar s_osea prog_osea s_osea_next ∧
    StructInitExistingSim ctx s_mir_next s_osea_next ∧
    s_mir_next.ap = s_osea_next.ap := by
  let ⟨s_osea_next, h_steps, h_sim_next⟩ :=
    embedded_simulation_struct_init_existing
      ctx s_mir s_osea s_mir_next prog_mir prog_osea
      h_sim h_mir_start h_osea_start h_mir_step
  exact ⟨s_osea_next, h_steps, h_sim_next, StateSim.ap_eq h_sim_next⟩

theorem embedded_validity_struct_init_existing
  (ctx : StructInitExistingCtx)
  (s_mir : mirlite.State)
  (s_osea : oseair.State)
  (s_mir_next : mirlite.State)
  (prog_mir : mirlite.Prog)
  (prog_osea : oseair.Prog)
  (h_sim : StructInitExistingSim ctx s_mir s_osea)
  (h_valid : SBValid s_mir.ap)
  (h_mir_start : StartsAt prog_mir s_mir.pc [ctx.stmt])
  (h_osea_start : StartsAt prog_osea s_osea.pc ctx.compiled)
  (h_mir_step : mirlite.step s_mir prog_mir = mirlite.Result.Ok s_mir_next) :
  ∃ s_osea_next,
    StepStar s_osea prog_osea s_osea_next ∧
    StructInitExistingSim ctx s_mir_next s_osea_next ∧
    s_mir_next.ap = s_osea_next.ap ∧
    SBValid s_mir_next.ap ∧
    SBValid s_osea_next.ap := by
  let ⟨s_osea_next, h_steps, h_sim_next, h_ap_eq⟩ :=
    embedded_preservation_struct_init_existing
      ctx s_mir s_osea s_mir_next prog_mir prog_osea
      h_sim h_mir_start h_osea_start h_mir_step
  let ⟨addr, tag, h_ptr, _h_mem⟩ := StateSim.place h_sim ctx.h_lookup
  have h_env :
      s_mir.env.lookup ctx.base = some (addr, wordStructTy ctx.fields, tag) := by
    simpa [wordStructTy] using h_ptr.2.1
  have h_stmt_mir : prog_mir.get? s_mir.pc = some ctx.stmt := StartsAt.singleton h_mir_start
  rcases List.get?_eq_some_iff.mp h_stmt_mir with ⟨h_pc_mir, h_get_mir⟩
  unfold mirlite.step at h_mir_step
  rw [dif_pos h_pc_mir, h_get_mir] at h_mir_step
  cases h_use : sb_use_mb s_mir.ap addr tag with
  | Err _ =>
      have h_words : mirlite.structConstWords? (List.map mirlite.RExpr.ConstOp ctx.fields) = some ctx.fields := by
        simpa [wordStructFields] using mirlite_structConstWords_wordStructFields ctx.fields
      simp [StructInitExistingCtx.stmt, wordStructRhs, wordStructFields,
        mirlite.structConstWords?, h_words, mirlite.stepAssignStructWords,
        mirlite.finishPlaceAssign, mirlite.writeResolvedPlace,
        obseq.notation.basePlace, h_env, h_use, wordStructTy, wordStructMirVals] at h_mir_step
  | Ok ap' =>
      have h_words : mirlite.structConstWords? (List.map mirlite.RExpr.ConstOp ctx.fields) = some ctx.fields := by
        simpa [wordStructFields] using mirlite_structConstWords_wordStructFields ctx.fields
      have h_next :
          s_mir_next =
            { s_mir with
              ap := ap',
              mem := mirlite.writeWordSeq s_mir.mem addr (wordStructMirVals ctx.fields),
              pc := s_mir.pc + 1 } := by
        simpa [StructInitExistingCtx.stmt, wordStructRhs, wordStructFields,
          mirlite.structConstWords?, h_words, mirlite.stepAssignStructWords,
          mirlite.finishPlaceAssign, mirlite.writeResolvedPlace,
          obseq.notation.basePlace, h_env, h_use, wordStructTy, wordStructMirVals] using h_mir_step.symm
      have h_valid_next : SBValid s_mir_next.ap := by
        rw [h_next]
        exact sb_use_mb_preserves_valid h_valid h_use
      exact ⟨s_osea_next, h_steps, h_sim_next, h_ap_eq, h_valid_next, StateSim.valid_osea h_sim_next⟩

end obseq.proof
