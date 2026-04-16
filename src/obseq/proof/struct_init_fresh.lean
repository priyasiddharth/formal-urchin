import obseq.proof.struct_init_common

/-!
# `obseq.proof.struct_init_fresh`

Local compiler-correctness lemmas for the fresh-destination constant-field
tuple fragment.

As in `const_fresh`, the only freshness-specific work is allocating the new
block, extending the source environment and place map, and then writing the
flattened tuple payload. As above, fresh allocation is still base-only:
projected fresh destinations remain unsupported by the current
compiler/runtime semantics.
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
  h_fields : fields ≠ []

namespace StructInitFreshCtx

def reg (ctx : StructInitFreshCtx) : Register :=
  Register.R ctx.cs.nextReg

def postPlaceMap (ctx : StructInitFreshCtx) : PlaceMap :=
  (ctx.base, (ctx.reg, wordStructLayout ctx.fields)) :: ctx.cs.placeMap

def stmt (ctx : StructInitFreshCtx) : mirlite.Stmt :=
  place(ctx.base) ::= wordStructRhs ctx.fields

def compiled (ctx : StructInitFreshCtx) : oseair.Prog :=
  (compileStmt ctx.cs ctx.stmt).instrs

theorem instrs_nil (ctx : StructInitFreshCtx) : ctx.cs.instrs = [] :=
  ctx.h_instrs

@[simp] theorem compiled_eq
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
  unfold StructInitFreshCtx.compiled StructInitFreshCtx.stmt
  simp [compileStmt, compile.structConstWords?, h_words, h_place', emit, cleanupInstrs,
    ctx.instrs_nil, obseq.notation.basePlace, wordStructRhs, wordStructFields,
    obseq.notation.placeExpr, obseq.notation.mkPlace,
    wordStructTy, wordStructOseaVals]

end StructInitFreshCtx

namespace StructInitFresh

theorem osea_run_ok
  (ctx : StructInitFreshCtx)
  (s_osea : oseair.State)
  (prog_osea : oseair.Prog)
  (tag : Word)
  (ap2 ap3 : AccessPerms)
  (h_start : StartsAt prog_osea s_osea.pc ctx.compiled)
  (h_own : sb_own s_osea.ap s_osea.mem.addrStart = (SBResult.Ok ap2, tag))
  (h_use : sb_use_mb ap2 s_osea.mem.addrStart tag = SBResult.Ok ap3) :
  oseair.runN 2 s_osea prog_osea =
    oseair.Result.Ok
      { s_osea with
        reg := s_osea.reg.insert ctx.reg
          (TyVal.PTy,
            [oseair.Val.Ptr s_osea.mem.addrStart 0 (blockSize (wordStructLayout ctx.fields)) tag]),
        mem := oseair.writeWordSeq
          { s_osea.mem with addrStart := s_osea.mem.addrStart + blockSize (wordStructLayout ctx.fields) }
          s_osea.mem.addrStart (wordStructOseaVals ctx.fields),
        ap := ap3,
        pc := s_osea.pc + 2 } := by
  rw [ctx.compiled_eq] at h_start
  have h_start' :
      StartsAt prog_osea s_osea.pc
        [oseair.Instr.Assgn ctx.reg (oseair.Rhs.Alloc (layoutToTyVal (wordStructLayout ctx.fields))),
         oseair.Instr.CStore (layoutToTyVal (wordStructLayout ctx.fields))
           (wordStructOseaVals ctx.fields) ctx.reg] := by
    simpa [layoutToTyVal_wordStructLayout] using h_start
  simpa [layoutToTyVal_wordStructLayout] using
    osea_run_alloc_cstore_embedded_ok
      s_osea prog_osea (wordStructLayout ctx.fields) (wordStructOseaVals ctx.fields)
      ctx.reg tag ap2 ap3 h_start' (wordStruct_nonempty_size ctx.h_fields) h_own h_use

theorem mirlite_step_inv
  (ctx : StructInitFreshCtx)
  (s_mir : mirlite.State)
  (s_mir_next : mirlite.State)
  (prog_mir : mirlite.Prog)
  (h_env : s_mir.env.lookup ctx.base = none)
  (h_start : StartsAt prog_mir s_mir.pc [ctx.stmt])
  (h_step : mirlite.step s_mir prog_mir = mirlite.Result.Ok s_mir_next) :
  ∃ tag ap2 ap3,
    sb_own s_mir.ap s_mir.mem.addrStart = (SBResult.Ok ap2, tag) ∧
    sb_use_mb ap2 s_mir.mem.addrStart tag = SBResult.Ok ap3 ∧
    s_mir_next =
      { s_mir with
        env := s_mir.env.insert ctx.base (s_mir.mem.addrStart, wordStructTy ctx.fields, tag),
        mem := mirlite.writeWordSeq
          { s_mir.mem with addrStart := s_mir.mem.addrStart + blockSize (wordStructLayout ctx.fields) }
          s_mir.mem.addrStart (wordStructMirVals ctx.fields),
        ap := ap3,
        pc := s_mir.pc + 1 } := by
  have h_stmt_mir : prog_mir.get? s_mir.pc = some ctx.stmt := StartsAt.singleton h_start
  rcases List.get?_eq_some_iff.mp h_stmt_mir with ⟨h_pc_mir, h_get_mir⟩
  have h_words : mirlite.structConstWords? (List.map mirlite.RExpr.ConstOp ctx.fields) = some ctx.fields := by
    simpa [wordStructFields] using mirlite_structConstWords_wordStructFields ctx.fields
  unfold mirlite.step at h_step
  rw [dif_pos h_pc_mir, h_get_mir] at h_step
  cases h_own : sb_own s_mir.ap s_mir.mem.addrStart with
  | mk ownRes tag =>
      cases ownRes with
      | Err _ =>
          have : False := by
            simp [StructInitFreshCtx.stmt, obseq.notation.basePlace, obseq.notation.placeExpr,
              obseq.notation.mkPlace, wordStructRhs, wordStructFields,
              mirlite.structConstWords?, h_words, mirlite.stepAssignStructWords,
              mirlite.finishPlaceAssign, mirlite.allocateBaseAndWrite,
              h_env, h_own, mirlite.allocate, blockSize] at h_step
          contradiction
      | Ok ap2 =>
          cases h_use : sb_use_mb ap2 s_mir.mem.addrStart tag with
          | Err _ =>
              have : False := by
                simp [StructInitFreshCtx.stmt, obseq.notation.basePlace, obseq.notation.placeExpr,
                  obseq.notation.mkPlace, wordStructRhs, wordStructFields,
                  h_words, mirlite.stepAssignStructWords,
                  mirlite.finishPlaceAssign, mirlite.allocateBaseAndWrite,
                  h_env, h_own, h_use, mirlite.allocate] at h_step
              contradiction
          | Ok ap3 =>
              refine ⟨tag, ap2, ap3, rfl, h_use, ?_⟩
              simpa [StructInitFreshCtx.stmt, obseq.notation.basePlace, obseq.notation.placeExpr,
                obseq.notation.mkPlace, wordStructRhs, wordStructFields,
                mirlite.structConstWords?, h_words, mirlite.stepAssignStructWords,
                mirlite.finishPlaceAssign, mirlite.allocateBaseAndWrite,
                h_env, h_own, h_use, mirlite.allocate, blockSize]
                using h_step.symm

variable (ctx : StructInitFreshCtx)
variable (s_mir : mirlite.State)
variable (s_osea : oseair.State)
variable (s_mir_next : mirlite.State)
variable (ρa : AddrRenameMap)
variable (ρt : TagRenameMap)

theorem simulation
  (prog_mir : mirlite.Prog)
  (prog_osea : oseair.Prog)
  (h_sim : StateSim ctx.cs.placeMap ρa ρt s_mir s_osea)
  (h_env : s_mir.env.lookup ctx.base = none)
  (h_mir_start : StartsAt prog_mir s_mir.pc [ctx.stmt])
  (h_osea_start : StartsAt prog_osea s_osea.pc ctx.compiled)
  (h_mir_step : mirlite.step s_mir prog_mir = mirlite.Result.Ok s_mir_next) :
  ∃ ρa' ρt' s_osea_next,
    StepStar s_osea prog_osea s_osea_next ∧
    StateSim ctx.postPlaceMap ρa' ρt' s_mir_next s_osea_next := by
  let ⟨tag_m, ap2_m, ap3_m, h_own, h_use, h_next_full⟩ :=
    mirlite_step_inv
      ctx s_mir s_mir_next prog_mir h_env h_mir_start h_mir_step
  rw [← layoutToTyVal_wordStructLayout] at h_next_full
  simpa [StructInitFreshCtx.postPlaceMap, StructInitFreshCtx.reg] using
    fresh_write_simulation h_sim
      (by simpa [StructInitFreshCtx.reg] using (alloc_fresh_reg (cs := ctx.cs)))
      h_own h_use
      (fun tag_o ap2_o ap3_o h_target_own h_target_use =>
        osea_run_ok ctx s_osea prog_osea tag_o ap2_o ap3_o h_osea_start h_target_own h_target_use)
      h_next_full (mem_vals_eq_words ctx.fields) (wordStructMirVals_length ctx.fields)

end StructInitFresh

end obseq.proof
