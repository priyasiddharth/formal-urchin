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

variable {A_m : mirlite.AllocatorSpec} {A_o : oseair.AllocatorSpec}

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
  (allocBase : Word)
  (allocMem : oseair.Mem)
  (tag : Word)
  (ap2 ap3 : AccessPerms)
  (h_start : StartsAt prog_osea s_osea.pc ctx.compiled)
  (h_alloc_pair :
    A_o.alloc s_osea.mem (blockSize (wordStructLayout ctx.fields)) = (allocBase, allocMem))
  (h_own : sb_own s_osea.ap allocBase = (SBResult.Ok ap2, tag))
  (h_use : sb_use_mb ap2 allocBase tag = SBResult.Ok ap3) :
  oseair.runNWith A_o 2 s_osea prog_osea =
    oseair.Result.Ok
      { s_osea with
        reg := s_osea.reg.insert ctx.reg
          (TyVal.PTy, [oseair.Val.Ptr allocBase 0 (blockSize (wordStructLayout ctx.fields)) tag]),
        mem := oseair.writeWordSeq allocMem allocBase (wordStructOseaVals ctx.fields),
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
      ctx.reg allocBase allocMem tag ap2 ap3 h_start' (wordStruct_nonempty_size ctx.h_fields)
      h_alloc_pair h_own h_use

theorem mirlite_step_inv
  (ctx : StructInitFreshCtx)
  (s_mir : mirlite.State)
  (s_mir_next : mirlite.State)
  (prog_mir : mirlite.Prog)
  (h_env : s_mir.env.lookup ctx.base = none)
  (h_start : StartsAt prog_mir s_mir.pc [ctx.stmt])
  (h_step : mirlite.stepWith A_m s_mir prog_mir = mirlite.Result.Ok s_mir_next) :
  ∃ freshAddr allocMem tag ap2 ap3,
    allocMem.mMap = s_mir.mem.mMap ∧
    sb_own s_mir.ap freshAddr = (SBResult.Ok ap2, tag) ∧
    sb_use_mb ap2 freshAddr tag = SBResult.Ok ap3 ∧
    s_mir_next =
      { s_mir with
        env := s_mir.env.insert ctx.base (freshAddr, wordStructTy ctx.fields, tag),
        mem := mirlite.writeWordSeq allocMem freshAddr (wordStructMirVals ctx.fields),
        ap := ap3,
        pc := s_mir.pc + 1 } := by
  have h_stmt_mir : prog_mir.get? s_mir.pc = some ctx.stmt := StartsAt.singleton h_start
  rcases List.get?_eq_some_iff.mp h_stmt_mir with ⟨h_pc_mir, h_get_mir⟩
  have h_words : mirlite.structConstWords? (List.map mirlite.RExpr.ConstOp ctx.fields) = some ctx.fields := by
    simpa [wordStructFields] using mirlite_structConstWords_wordStructFields ctx.fields
  let freshAddr := (A_m.alloc s_mir.mem (typeSize (wordStructTy ctx.fields))).1
  let allocMem := (A_m.alloc s_mir.mem (typeSize (wordStructTy ctx.fields))).2
  have h_alloc_pair :
      A_m.alloc s_mir.mem (typeSize (wordStructTy ctx.fields)) = (freshAddr, allocMem) := by
    simp [freshAddr, allocMem]
  have h_alloc_pair' :
      A_m.alloc s_mir.mem (typeSize (TyVal.TupTy (List.replicate ctx.fields.length TyVal.NatTy))) =
        (freshAddr, allocMem) := by
    simpa [wordStructTy] using h_alloc_pair
  have h_alloc_fst :
      (A_m.alloc s_mir.mem (typeSize (TyVal.TupTy (List.replicate ctx.fields.length TyVal.NatTy)))).fst =
        freshAddr := by
    simpa using congrArg Prod.fst h_alloc_pair'
  have h_alloc_snd :
      (A_m.alloc s_mir.mem (typeSize (TyVal.TupTy (List.replicate ctx.fields.length TyVal.NatTy)))).snd =
        allocMem := by
    simpa using congrArg Prod.snd h_alloc_pair'
  have h_alloc_mMap : allocMem.mMap = s_mir.mem.mMap := by
    simpa [h_alloc_pair] using A_m.alloc_mMap_eq s_mir.mem (typeSize (wordStructTy ctx.fields))
  unfold mirlite.stepWith at h_step
  rw [dif_pos h_pc_mir, h_get_mir] at h_step
  simp [StructInitFreshCtx.stmt, obseq.notation.basePlace, obseq.notation.placeExpr,
    obseq.notation.mkPlace, wordStructRhs, wordStructFields, h_words] at h_step
  unfold mirlite.stepAssignStructWordsWith mirlite.finishPlaceAssignWith
    mirlite.allocateBaseAndWriteWith at h_step
  simp [h_env] at h_step
  rw [h_alloc_fst, h_alloc_snd] at h_step
  cases h_own : sb_own s_mir.ap freshAddr with
  | mk ownRes tag =>
      cases ownRes with
      | Err _ =>
          rw [h_own] at h_step
          simp at h_step
      | Ok ap2 =>
          rw [h_own] at h_step
          simp at h_step
          cases h_use : sb_use_mb ap2 freshAddr tag with
          | Err _ =>
              rw [h_use] at h_step
              simp at h_step
          | Ok ap3 =>
              rw [h_use] at h_step
              simp at h_step
              refine ⟨freshAddr, allocMem, tag, ap2, ap3, h_alloc_mMap, h_own, h_use, ?_⟩
              simpa [wordStructTy, wordStructLayout, wordStructMirVals] using h_step.symm

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
  (h_mir_step : mirlite.stepWith A_m s_mir prog_mir = mirlite.Result.Ok s_mir_next) :
  ∃ ρa' ρt' s_osea_next,
    StepStarWith A_o s_osea prog_osea s_osea_next ∧
    StateSim ctx.postPlaceMap ρa' ρt' s_mir_next s_osea_next := by
  let ⟨freshAddr_m, allocMem_m, tag_m, ap2_m, ap3_m, h_alloc_mMap_m, h_own, h_use, h_next_full⟩ :=
    mirlite_step_inv
      ctx s_mir s_mir_next prog_mir h_env h_mir_start h_mir_step
  rw [← layoutToTyVal_wordStructLayout] at h_next_full
  let allocBase_o := (A_o.alloc s_osea.mem (blockSize (wordStructLayout ctx.fields))).1
  let allocMem_o := (A_o.alloc s_osea.mem (blockSize (wordStructLayout ctx.fields))).2
  have h_alloc_pair :
      A_o.alloc s_osea.mem (blockSize (wordStructLayout ctx.fields)) =
        (allocBase_o, allocMem_o) := by
    simp [allocBase_o, allocMem_o]
  have h_alloc_fst :
      (A_o.alloc s_osea.mem (blockSize (wordStructLayout ctx.fields))).fst = allocBase_o := by
    simpa using congrArg Prod.fst h_alloc_pair
  have h_alloc_snd :
      (A_o.alloc s_osea.mem (blockSize (wordStructLayout ctx.fields))).snd = allocMem_o := by
    simpa using congrArg Prod.snd h_alloc_pair
  have h_alloc_mMap_o : allocMem_o.mMap = s_osea.mem.mMap := by
    have h_alloc_mMap := A_o.alloc_mMap_eq s_osea.mem (blockSize (wordStructLayout ctx.fields))
    rw [h_alloc_pair] at h_alloc_mMap
    simpa using h_alloc_mMap
  simpa [StructInitFreshCtx.postPlaceMap, StructInitFreshCtx.reg] using
    fresh_write_simulation (freshAddr_m := freshAddr_m) h_sim
      (by simpa [StructInitFreshCtx.reg] using (alloc_fresh_reg (cs := ctx.cs)))
      h_own h_use h_alloc_mMap_m
      h_alloc_mMap_o
      (fun tag_o ap2_o ap3_o h_target_own h_target_use => by
        simpa [StructInitFreshCtx.reg, h_alloc_fst, h_alloc_snd] using
          osea_run_ok ctx s_osea prog_osea allocBase_o allocMem_o tag_o ap2_o ap3_o
            h_osea_start h_alloc_pair h_target_own h_target_use)
      h_next_full (mem_vals_eq_words ctx.fields) (wordStructMirVals_length ctx.fields)

end StructInitFresh

end obseq.proof
