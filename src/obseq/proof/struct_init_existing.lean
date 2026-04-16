import obseq.proof.struct_init_common

/-!
# `obseq.proof.struct_init_existing`

Local compiler-correctness lemmas for the existing-destination constant-field
tuple fragment over arbitrary projected places.
-/

namespace obseq.proof

open obseq
open obseq.mirlite
open obseq.oseair hiding State Result
open obseq.compile
open scoped obseq.notation

structure StructInitExistingCtx where
  dst : mirlite.Place
  reg : Register
  fields : List Word
  cs : CompilerState
  h_instrs : CompilerEmpty cs
  h_fields : fields ≠ []
  baseLayout : LayoutTy
  off : Word
  h_lookup : BaseReady cs dst.base reg baseLayout
  h_path : layoutResolvePath baseLayout dst.path = some (off, wordStructLayout fields)

namespace StructInitExistingCtx

def tmpReg (ctx : StructInitExistingCtx) : Register :=
  Register.R ctx.cs.nextReg

def stmt (ctx : StructInitExistingCtx) : mirlite.Stmt :=
  mirlite.Stmt.Assgn (obseq.notation.placeExpr ctx.dst) (wordStructRhs ctx.fields)

def compiled (ctx : StructInitExistingCtx) : oseair.Prog :=
  (compileStmt ctx.cs ctx.stmt).instrs

theorem instrs_nil (ctx : StructInitExistingCtx) : ctx.cs.instrs = [] :=
  ctx.h_instrs

@[simp] theorem compiled_eq
  (ctx : StructInitExistingCtx) :
  ctx.compiled =
    if ctx.off = 0 then
      [oseair.Instr.CStore (wordStructTy ctx.fields) (wordStructOseaVals ctx.fields) ctx.reg]
    else
      [oseair.Instr.Assgn ctx.tmpReg (oseair.Rhs.MutBorOffset ctx.reg ctx.off),
       oseair.Instr.CStore (wordStructTy ctx.fields) (wordStructOseaVals ctx.fields) ctx.tmpReg,
       oseair.Instr.Die ctx.tmpReg] := by
  have h_words : compile.structConstWords? (List.map mirlite.RExpr.ConstOp ctx.fields) = some ctx.fields := by
    simpa [wordStructFields] using compile_structConstWords_wordStructFields ctx.fields
  by_cases h_off : ctx.off = 0
  · have h_place :
        placeToReg ctx.cs ctx.dst mirlite.RefKind.Mut (some (wordStructLayout ctx.fields)) =
          { reg := ctx.reg, layout := wordStructLayout ctx.fields, cleanup := [], cs := ctx.cs } := by
      unfold placeToReg
      rw [ctx.h_lookup]
      simp [ctx.h_path, h_off]
    have h_place' :
        placeToReg ctx.cs ctx.dst mirlite.RefKind.Mut
            (some (LayoutTy.TupL (List.replicate ctx.fields.length LayoutTy.NatL))) =
          { reg := ctx.reg,
            layout := LayoutTy.TupL (List.replicate ctx.fields.length LayoutTy.NatL),
            cleanup := [],
            cs := ctx.cs } := by
      simpa [wordStructLayout] using h_place
    unfold StructInitExistingCtx.compiled StructInitExistingCtx.stmt compileStmt
    simpa [h_off] using
      (by
        simp [h_words, h_place', emit, cleanupInstrs,
          obseq.notation.placeExpr, wordStructRhs, wordStructFields,
          wordStructTy, wordStructOseaVals, ctx.instrs_nil]
      )
  · have h_place :
        placeToReg ctx.cs ctx.dst mirlite.RefKind.Mut (some (wordStructLayout ctx.fields)) =
          { reg := ctx.tmpReg,
            layout := wordStructLayout ctx.fields,
            cleanup := [ctx.tmpReg],
            cs :=
              { nextReg := ctx.cs.nextReg + 1,
                placeMap := ctx.cs.placeMap,
                instrs := ctx.cs.instrs ++
                  [oseair.Instr.Assgn ctx.tmpReg (oseair.Rhs.MutBorOffset ctx.reg ctx.off)] } } := by
      unfold placeToReg
      rw [ctx.h_lookup]
      simp [ctx.h_path, h_off, StructInitExistingCtx.tmpReg, freshReg, emit]
    have h_place' :
        placeToReg ctx.cs ctx.dst mirlite.RefKind.Mut
            (some (LayoutTy.TupL (List.replicate ctx.fields.length LayoutTy.NatL))) =
          { reg := ctx.tmpReg,
            layout := LayoutTy.TupL (List.replicate ctx.fields.length LayoutTy.NatL),
            cleanup := [ctx.tmpReg],
            cs :=
              { nextReg := ctx.cs.nextReg + 1,
                placeMap := ctx.cs.placeMap,
                instrs := ctx.cs.instrs ++
                  [oseair.Instr.Assgn ctx.tmpReg (oseair.Rhs.MutBorOffset ctx.reg ctx.off)] } } := by
      simpa [wordStructLayout] using h_place
    unfold StructInitExistingCtx.compiled StructInitExistingCtx.stmt compileStmt
    simpa [h_off] using
      (by
        simp [h_words, h_place', emit, cleanupInstrs,
          obseq.notation.placeExpr, wordStructRhs, wordStructFields,
          wordStructTy, wordStructOseaVals, StructInitExistingCtx.tmpReg, ctx.instrs_nil]
      )

end StructInitExistingCtx

namespace StructInitExisting

abbrev LocalSim
  (ctx : StructInitExistingCtx)
  (ρa : AddrRenameMap)
  (ρt : TagRenameMap)
  (s_mir : mirlite.State)
  (s_osea : oseair.State) : Prop :=
  StateSim ctx.cs.placeMap ρa ρt s_mir s_osea

theorem mirlite_step_inv
  (ctx : StructInitExistingCtx)
  (s_mir : mirlite.State)
  (s_mir_next : mirlite.State)
  (prog_mir : mirlite.Prog)
  (addr tag : Word)
  (h_env : s_mir.env.lookup ctx.dst.base = some (addr, layoutToTyVal ctx.baseLayout, tag))
  (h_start : StartsAt prog_mir s_mir.pc [ctx.stmt])
  (h_step : mirlite.step s_mir prog_mir = mirlite.Result.Ok s_mir_next) :
  ∃ ap',
    sb_use_mb s_mir.ap (addr + ctx.off) tag = SBResult.Ok ap' ∧
    s_mir_next =
      { s_mir with
        ap := ap',
        mem := mirlite.writeWordSeq s_mir.mem (addr + ctx.off) (wordStructMirVals ctx.fields),
        pc := s_mir.pc + 1 } := by
  have h_stmt_mir : prog_mir.get? s_mir.pc = some ctx.stmt := StartsAt.singleton h_start
  rcases List.get?_eq_some_iff.mp h_stmt_mir with ⟨h_pc_mir, h_get_mir⟩
  have h_words : mirlite.structConstWords? (List.map mirlite.RExpr.ConstOp ctx.fields) = some ctx.fields := by
    simpa [wordStructFields] using mirlite_structConstWords_wordStructFields ctx.fields
  unfold mirlite.step at h_step
  rw [dif_pos h_pc_mir, h_get_mir] at h_step
  simp [StructInitExistingCtx.stmt, obseq.notation.placeExpr, wordStructRhs,
    wordStructFields, h_words, mirlite.stepAssignStructWords] at h_step
  rw [finishPlaceAssign_existing_eq h_env ctx.h_path] at h_step
  cases h_use : sb_use_mb s_mir.ap (addr + ctx.off) tag with
  | Err _ =>
      simp [h_use] at h_step
  | Ok ap' =>
      refine ⟨ap', rfl, ?_⟩
      simpa [h_use] using h_step.symm

variable (ctx : StructInitExistingCtx)
variable (s_mir : mirlite.State)
variable (s_osea : oseair.State)
variable (s_mir_next : mirlite.State)
variable (ρa : AddrRenameMap)
variable (ρt : TagRenameMap)

theorem simulation
  (prog_mir : mirlite.Prog)
  (prog_osea : oseair.Prog)
  (h_sim : LocalSim ctx ρa ρt s_mir s_osea)
  (h_mir_start : StartsAt prog_mir s_mir.pc [ctx.stmt])
  (h_osea_start : StartsAt prog_osea s_osea.pc ctx.compiled)
  (h_mir_step : mirlite.step s_mir prog_mir = mirlite.Result.Ok s_mir_next) :
  ∃ s_osea_next,
    StepStar s_osea prog_osea s_osea_next ∧
    LocalSim ctx ρa ρt s_mir_next s_osea_next := by
  let ⟨addr_m, addr_o, tag_m, tag_o, h_ptr, _h_block⟩ :=
    StateSim.place_projected h_sim ctx.h_lookup ctx.h_path
  have h_env := place_runtime_sim.env h_ptr
  have h_fit : ctx.off + blockSize (wordStructLayout ctx.fields) ≤ blockSize ctx.baseLayout :=
    layoutResolvePath_blockSize_le ctx.h_path
  let ⟨ap_m', h_use, h_next_full⟩ :=
    mirlite_step_inv ctx s_mir s_mir_next prog_mir addr_m tag_m h_env h_mir_start h_mir_step
  have h_tmp_fresh :
      ∀ base layout, ctx.cs.placeMap.lookup base = some (ctx.tmpReg, layout) → False :=
    fun base layout h_lookup => alloc_fresh_reg (cs := ctx.cs) base layout h_lookup
  exact existing_write_simulation h_sim h_ptr h_fit (wordStruct_nonempty_size ctx.h_fields)
    h_tmp_fresh
    (fun h_off => by
      simpa [ctx.compiled_eq, h_off, layoutToTyVal_wordStructLayout] using h_osea_start)
    (fun h_off => by
      simpa [ctx.compiled_eq, h_off, layoutToTyVal_wordStructLayout] using h_osea_start)
    h_use h_next_full (mem_vals_eq_words ctx.fields) (wordStructMirVals_length ctx.fields)

end StructInitExisting

end obseq.proof
