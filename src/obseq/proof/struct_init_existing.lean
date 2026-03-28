import obseq.proof.struct_init_common

/-!
# `obseq.proof.struct_init_existing`

Local compiler-correctness lemmas for the existing-destination constant-field
tuple fragment.

This is the tuple-building counterpart to `const_existing`: the source step is
still a single write, but the payload is the flattened tuple block
`wordStructMirVals fields`.
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

def oseaPost (ctx : StructInitExistingCtx)
  (s_osea : oseair.State)
  (ap' : AccessPerms)
  (addr : Word) : oseair.State :=
  { s_osea with
    ap := ap',
    mem := oseair.writeWordSeq s_osea.mem addr (wordStructOseaVals ctx.fields),
    pc := 1 }

theorem instrs_nil (ctx : StructInitExistingCtx) : ctx.cs.instrs = [] :=
  ctx.h_instrs

@[simp] theorem compiled_eq
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
          cleanup := [],
          cs := ctx.cs } := by
    simpa [wordStructLayout] using h_place
  have h_words : compile.structConstWords? (List.map mirlite.RExpr.ConstOp ctx.fields) = some ctx.fields := by
    simpa [wordStructFields] using compile_structConstWords_wordStructFields ctx.fields
  unfold StructInitExistingCtx.compiled StructInitExistingCtx.stmt
  simp [compileStmt, compile.structConstWords?, h_words, h_place', emit, cleanupInstrs,
    ctx.instrs_nil, obseq.notation.basePlace, wordStructRhs, wordStructFields,
    wordStructTy, wordStructOseaVals]

end StructInitExistingCtx

namespace StructInitExisting

abbrev LocalSim
  (ctx : StructInitExistingCtx)
  (ρa : AddrRenaming)
  (ρt : TagRenaming)
  (s_mir : mirlite.State)
  (s_osea : oseair.State) : Prop :=
  StateSim ctx.cs.placeMap ρa ρt s_mir s_osea

theorem osea_run_ok
  (ctx : StructInitExistingCtx)
  (s_osea : oseair.State)
  (prog_osea : oseair.Prog)
  (addr tag : Word)
  (ap' : AccessPerms)
  (h_start : StartsAt prog_osea s_osea.pc ctx.compiled)
  (h_reg :
    s_osea.reg.lookup ctx.reg =
      some (TyVal.PTy,
        [oseair.Val.Ptr addr 0 (blockSize (wordStructLayout ctx.fields)) tag]))
  (h_use : sb_use_mb s_osea.ap addr tag = SBResult.Ok ap') :
  oseair.runN 1 s_osea prog_osea =
    oseair.Result.Ok
      { s_osea with
        ap := ap',
        mem := oseair.writeWordSeq s_osea.mem addr (wordStructOseaVals ctx.fields),
        pc := s_osea.pc + 1 } := by
  rw [ctx.compiled_eq] at h_start
  have h_start' :
      StartsAt prog_osea s_osea.pc
        [oseair.Instr.CStore (layoutToTyVal (wordStructLayout ctx.fields))
          (wordStructOseaVals ctx.fields) ctx.reg] := by
    simpa [layoutToTyVal_wordStructLayout] using h_start
  simpa [layoutToTyVal_wordStructLayout] using
    osea_run_cstore_embedded_ok
      s_osea prog_osea (wordStructLayout ctx.fields) (wordStructOseaVals ctx.fields)
      addr tag ctx.reg ap' h_start' (wordStruct_nonempty_size ctx.h_fields) h_reg h_use

/--
Paper step 1 for the existing-destination struct-init case: invert a
successful MIR step to recover the unique successful `sb_use_mb` and the exact
source post-state.
-/
theorem mirlite_step_inv
  (ctx : StructInitExistingCtx)
  (s_mir : mirlite.State)
  (s_mir_next : mirlite.State)
  (prog_mir : mirlite.Prog)
  (addr tag : Word)
  (h_env : s_mir.env.lookup ctx.base = some (addr, wordStructTy ctx.fields, tag))
  (h_start : StartsAt prog_mir s_mir.pc [ctx.stmt])
  (h_step : mirlite.step s_mir prog_mir = mirlite.Result.Ok s_mir_next) :
  ∃ ap',
    sb_use_mb s_mir.ap addr tag = SBResult.Ok ap' ∧
    s_mir_next =
      { s_mir with
        ap := ap',
        mem := mirlite.writeWordSeq s_mir.mem addr (wordStructMirVals ctx.fields),
        pc := s_mir.pc + 1 } := by
  have h_stmt_mir : prog_mir.get? s_mir.pc = some ctx.stmt := StartsAt.singleton h_start
  rcases List.get?_eq_some_iff.mp h_stmt_mir with ⟨h_pc_mir, h_get_mir⟩
  have h_words : mirlite.structConstWords? (List.map mirlite.RExpr.ConstOp ctx.fields) = some ctx.fields := by
    simpa [wordStructFields] using mirlite_structConstWords_wordStructFields ctx.fields
  unfold mirlite.step at h_step
  rw [dif_pos h_pc_mir, h_get_mir] at h_step
  cases h_use : sb_use_mb s_mir.ap addr tag with
  | Err _ =>
      have : False := by
        simp [StructInitExistingCtx.stmt, obseq.notation.basePlace, wordStructRhs, wordStructFields,
          mirlite.structConstWords?, h_words, mirlite.stepAssignStructWords,
          mirlite.finishPlaceAssign, mirlite.writeResolvedPlace,
          h_env, h_use, wordStructTy, wordStructMirVals] at h_step
      contradiction
  | Ok ap' =>
      refine ⟨ap', rfl, ?_⟩
      simpa [StructInitExistingCtx.stmt, obseq.notation.basePlace, wordStructRhs, wordStructFields,
        mirlite.structConstWords?, h_words, mirlite.stepAssignStructWords,
        mirlite.finishPlaceAssign, mirlite.writeResolvedPlace,
        h_env, h_use, wordStructTy, wordStructMirVals] using h_step.symm

variable (ctx : StructInitExistingCtx)
variable (s_mir : mirlite.State)
variable (s_osea : oseair.State)
variable (s_mir_next : mirlite.State)
variable (ρa : AddrRenaming)
variable (ρt : TagRenaming)

/--
Paper-style embedded simulation for `place(base) ::= StructInitOp fields` with
an existing destination:

1. recover the tracked runtime pointer/register pair from `StateSim`,
2. invert the MIR step,
3. transport the successful SB use to the target and execute the singleton
   `CStore`, and
4. rebuild `StateSim` after the matching writes.
-/
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
  let ⟨addr_m, addr_o, tag_m, tag_o, h_ptr, _h_mem⟩ := StateSim.place h_sim ctx.h_lookup
  have h_env :
      s_mir.env.lookup ctx.base = some (addr_m, wordStructTy ctx.fields, tag_m) := by
    simpa [layoutToTyVal_wordStructLayout] using place_runtime_sim.env h_ptr
  have h_reg :
      s_osea.reg.lookup ctx.reg =
        some (TyVal.PTy,
          [oseair.Val.Ptr addr_o 0 (blockSize (wordStructLayout ctx.fields)) tag_o]) :=
    place_runtime_sim.reg h_ptr
  have h_addr : ρa addr_m = some addr_o := place_runtime_sim.addr h_ptr
  have h_tag : ρt tag_m = some tag_o := place_runtime_sim.tag h_ptr

  let ⟨ap_m', h_use, h_next_full⟩ :=
    mirlite_step_inv
      ctx s_mir s_mir_next prog_mir addr_m tag_m h_env h_mir_start h_mir_step
  let ⟨ap_o', h_target_use, h_sb_next⟩ :=
    sb_use_mb_sim_ok (StateSim.sb h_sim) h_addr h_tag h_use

  let s_osea_post :=
    { s_osea with
      ap := ap_o',
      mem := oseair.writeWordSeq s_osea.mem addr_o (wordStructOseaVals ctx.fields),
      pc := s_osea.pc + 1 }
  have h_target_run :
      oseair.runN 1 s_osea prog_osea = oseair.Result.Ok s_osea_post := by
    simpa [s_osea_post] using
      osea_run_ok
        ctx s_osea prog_osea addr_o tag_o ap_o' h_osea_start h_reg h_target_use

  refine ⟨s_osea_post, StepStar.of_runN_ok h_target_run, ?_⟩
  rw [h_next_full]
  simpa [s_osea_post] using
    state_sim_write
      (π := ctx.cs.placeMap)
      (ρa := ρa)
      (ρt := ρt)
      (dst_mir := addr_m)
      (dst_osea := addr_o)
      (ap_m' := ap_m')
      (ap_o' := ap_o')
      (pc_mir := s_mir.pc + 1)
      (pc_osea := s_osea.pc + 1)
      (vals_mir := wordStructMirVals ctx.fields)
      (vals_osea := wordStructOseaVals ctx.fields)
      h_sim h_sb_next (mem_vals_eq_words ctx.fields)

end StructInitExisting

end obseq.proof
