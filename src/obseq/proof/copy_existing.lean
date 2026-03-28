import obseq.proof.state_helpers

/-!
# `obseq.proof.copy_existing`

Local compiler-correctness lemmas for the existing-source/existing-destination
copy fragment `place(dst) ::= copy src`.

This cluster is now layout-parametric: the copied payload is the full block of
size `blockSize layout`, not a hardcoded single word.
-/

namespace obseq.proof

open obseq
open obseq.mirlite
open obseq.oseair hiding State Result
open obseq.compile
open scoped obseq.notation

def CopyMirPost
  (layout : LayoutTy)
  (s_mir : mirlite.State)
  (apWrite : AccessPerms)
  (srcAddr dstAddr : Word) : mirlite.State :=
  { s_mir with
    ap := apWrite,
    mem := mirlite.writeWordSeq s_mir.mem dstAddr
      (mirlite.readWordSeq s_mir.mem srcAddr (blockSize layout)),
    pc := s_mir.pc + 1 }

def CopyOseaPost
  (layout : LayoutTy)
  (s_osea : oseair.State)
  (apWrite : AccessPerms)
  (srcAddr dstAddr : Word) : oseair.State :=
  { s_osea with
    ap := apWrite,
    mem := oseair.writeWordSeq s_osea.mem dstAddr
      (oseair.readWordSeq s_osea.mem srcAddr (blockSize layout)),
    pc := s_osea.pc + 1 }

structure CopyExistingCtx where
  srcBase : Word
  srcReg : Register
  dstBase : Word
  dstReg : Register
  layout : LayoutTy
  cs : CompilerState
  h_instrs : CompilerEmpty cs
  h_src_lookup : BaseReady cs srcBase srcReg layout
  h_dst_lookup : BaseReady cs dstBase dstReg layout

namespace CopyExistingCtx

def stmt (ctx : CopyExistingCtx) : mirlite.Stmt :=
  place(ctx.dstBase) ::= copy ctx.srcBase

def compiled (ctx : CopyExistingCtx) : oseair.Prog :=
  (compileStmt ctx.cs ctx.stmt).instrs

theorem instrs_nil (ctx : CopyExistingCtx) : ctx.cs.instrs = [] :=
  ctx.h_instrs

end CopyExistingCtx

theorem CopyExistingCtx.compiled_eq
  (ctx : CopyExistingCtx) :
  ctx.compiled =
    [oseair.Instr.Memcpy ctx.dstReg ctx.srcReg (layoutToTyVal ctx.layout)] := by
  have h_src_place :
      placeToReg ctx.cs { base := ctx.srcBase, path := [] } mirlite.RefKind.Shared none =
        { reg := ctx.srcReg, layout := ctx.layout, cleanup := [], cs := ctx.cs } := by
    unfold placeToReg
    rw [ctx.h_src_lookup]
    simp [layoutResolvePath]
  have h_dst_place :
      placeToReg ctx.cs { base := ctx.dstBase, path := [] } mirlite.RefKind.Mut (some ctx.layout) =
        { reg := ctx.dstReg, layout := ctx.layout, cleanup := [], cs := ctx.cs } := by
    unfold placeToReg
    rw [ctx.h_dst_lookup]
    simp [layoutResolvePath]
  unfold CopyExistingCtx.compiled CopyExistingCtx.stmt
  simp [compileStmt, obseq.notation.placeExpr, obseq.notation.mkPlace,
    obseq.notation.copyPlaceRhs, obseq.notation.copyRhs, obseq.notation.basePlace,
    h_src_place, h_dst_place, emit, cleanupInstrs, ctx.instrs_nil, layoutToTyVal, List.map]

namespace CopyExisting

abbrev LocalSim
  (ctx : CopyExistingCtx)
  (ρa : AddrRenaming)
  (ρt : TagRenaming)
  (s_mir : mirlite.State)
  (s_osea : oseair.State) : Prop :=
  StateSim ctx.cs.placeMap ρa ρt s_mir s_osea

theorem osea_run_ok
  (ctx : CopyExistingCtx)
  (s_osea : oseair.State)
  (prog_osea : oseair.Prog)
  (srcAddr srcTag dstAddr dstTag : Word)
  (apRead apWrite : AccessPerms)
  (h_start : StartsAt prog_osea s_osea.pc ctx.compiled)
  (h_src_reg :
    s_osea.reg.lookup ctx.srcReg =
      some (TyVal.PTy, [oseair.Val.Ptr srcAddr 0 (blockSize ctx.layout) srcTag]))
  (h_dst_reg :
    s_osea.reg.lookup ctx.dstReg =
      some (TyVal.PTy, [oseair.Val.Ptr dstAddr 0 (blockSize ctx.layout) dstTag]))
  (h_read : sb_read s_osea.ap srcAddr srcTag = SBResult.Ok apRead)
  (h_write : sb_use_mb apRead dstAddr dstTag = SBResult.Ok apWrite) :
  oseair.runN 1 s_osea prog_osea =
    oseair.Result.Ok (CopyOseaPost ctx.layout s_osea apWrite srcAddr dstAddr) := by
  rw [ctx.compiled_eq] at h_start
  simpa [CopyOseaPost] using
    osea_run_memcpy_embedded_ok
      s_osea prog_osea ctx.layout
      srcAddr srcTag dstAddr dstTag ctx.srcReg ctx.dstReg
      apRead apWrite h_start h_src_reg h_dst_reg h_read h_write

/--
Paper step 1 for the existing-source/existing-destination copy case: invert a
successful MIR step to recover the unique successful `sb_read`, `sb_use_mb`,
and the exact source post-state.
-/
theorem mirlite_step_inv
  (ctx : CopyExistingCtx)
  (s_mir : mirlite.State)
  (s_mir_next : mirlite.State)
  (prog_mir : mirlite.Prog)
  (srcAddr srcTag dstAddr dstTag : Word)
  (h_src : s_mir.env.lookup ctx.srcBase = some (srcAddr, layoutToTyVal ctx.layout, srcTag))
  (h_dst : s_mir.env.lookup ctx.dstBase = some (dstAddr, layoutToTyVal ctx.layout, dstTag))
  (h_start : StartsAt prog_mir s_mir.pc [ctx.stmt])
  (h_step : mirlite.step s_mir prog_mir = mirlite.Result.Ok s_mir_next) :
  ∃ apRead apWrite,
    sb_read s_mir.ap srcAddr srcTag = SBResult.Ok apRead ∧
    sb_use_mb apRead dstAddr dstTag = SBResult.Ok apWrite ∧
    s_mir_next = CopyMirPost ctx.layout s_mir apWrite srcAddr dstAddr := by
  have h_stmt_mir : prog_mir.get? s_mir.pc = some ctx.stmt := StartsAt.singleton h_start
  rcases List.get?_eq_some_iff.mp h_stmt_mir with ⟨h_pc_mir, h_get_mir⟩
  unfold mirlite.step at h_step
  rw [dif_pos h_pc_mir, h_get_mir] at h_step
  cases h_read : sb_read s_mir.ap srcAddr srcTag with
  | Err _ =>
      simp [CopyExistingCtx.stmt, obseq.notation.placeExpr, obseq.notation.mkPlace,
        obseq.notation.copyPlaceRhs, obseq.notation.copyRhs, obseq.notation.basePlace,
        mirlite.stepAssignCopy, mirlite.finishPlaceAssign, mirlite.writeResolvedPlace,
        h_src, h_dst, h_read, blockSize] at h_step
  | Ok apRead =>
      cases h_write : sb_use_mb apRead dstAddr dstTag with
      | Err _ =>
          simp [CopyExistingCtx.stmt, obseq.notation.placeExpr, obseq.notation.mkPlace,
            obseq.notation.copyPlaceRhs, obseq.notation.copyRhs, obseq.notation.basePlace,
            mirlite.stepAssignCopy, mirlite.finishPlaceAssign, mirlite.writeResolvedPlace,
            h_src, h_dst, h_read, h_write, blockSize] at h_step
      | Ok apWrite =>
          refine ⟨apRead, apWrite, rfl, h_write, ?_⟩
          simpa [CopyExistingCtx.stmt, obseq.notation.placeExpr, obseq.notation.mkPlace,
            obseq.notation.copyPlaceRhs, obseq.notation.copyRhs, obseq.notation.basePlace,
            mirlite.stepAssignCopy, mirlite.finishPlaceAssign, mirlite.writeResolvedPlace,
            h_src, h_dst, h_read, h_write, blockSize, CopyMirPost] using h_step.symm

variable (ctx : CopyExistingCtx)
variable (s_mir : mirlite.State)
variable (s_osea : oseair.State)
variable (s_mir_next : mirlite.State)
variable (ρa : AddrRenaming)
variable (ρt : TagRenaming)

/--
Paper-style embedded simulation for `place(dst) ::= copy src` with existing
source and destination bases:

1. recover the tracked source and destination pointer/register pairs from
   `StateSim`,
2. invert the MIR step,
3. transport the successful SB read and write to the target and execute the
   singleton `Memcpy`, and
4. rebuild `StateSim` after the matching block copy.
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
  let ⟨srcAddr_m, srcAddr_o, srcTag_m, srcTag_o, h_src_ptr, h_src_mem⟩ := StateSim.place h_sim ctx.h_src_lookup
  let ⟨dstAddr_m, dstAddr_o, dstTag_m, dstTag_o, h_dst_ptr, _h_dst_mem⟩ := StateSim.place h_sim ctx.h_dst_lookup
  have h_src_env :
      s_mir.env.lookup ctx.srcBase =
        some (srcAddr_m, layoutToTyVal ctx.layout, srcTag_m) := place_runtime_sim.env h_src_ptr
  have h_src_reg :
      s_osea.reg.lookup ctx.srcReg =
        some (TyVal.PTy, [oseair.Val.Ptr srcAddr_o 0 (blockSize ctx.layout) srcTag_o]) :=
    place_runtime_sim.reg h_src_ptr
  have h_dst_env :
      s_mir.env.lookup ctx.dstBase =
        some (dstAddr_m, layoutToTyVal ctx.layout, dstTag_m) := place_runtime_sim.env h_dst_ptr
  have h_dst_reg :
      s_osea.reg.lookup ctx.dstReg =
        some (TyVal.PTy, [oseair.Val.Ptr dstAddr_o 0 (blockSize ctx.layout) dstTag_o]) :=
    place_runtime_sim.reg h_dst_ptr
  have h_src_addr : ρa srcAddr_m = some srcAddr_o := place_runtime_sim.addr h_src_ptr
  have h_src_tag : ρt srcTag_m = some srcTag_o := place_runtime_sim.tag h_src_ptr
  have h_dst_addr : ρa dstAddr_m = some dstAddr_o := place_runtime_sim.addr h_dst_ptr
  have h_dst_tag : ρt dstTag_m = some dstTag_o := place_runtime_sim.tag h_dst_ptr
  let ⟨apRead_m, apWrite_m, h_read, h_write, h_next_full⟩ :=
    mirlite_step_inv
      ctx s_mir s_mir_next prog_mir
      srcAddr_m srcTag_m dstAddr_m dstTag_m h_src_env h_dst_env h_mir_start h_mir_step
  let ⟨apRead_o, h_target_read, h_sb_read⟩ :=
    sb_read_sim_ok (StateSim.sb h_sim) h_src_addr h_src_tag h_read
  let ⟨apWrite_o, h_target_write, h_sb_write⟩ :=
    sb_use_mb_sim_ok h_sb_read h_dst_addr h_dst_tag h_write
  let s_osea_post := CopyOseaPost ctx.layout s_osea apWrite_o srcAddr_o dstAddr_o
  have h_target_run :
      oseair.runN 1 s_osea prog_osea = oseair.Result.Ok s_osea_post := by
    simpa [s_osea_post] using
      osea_run_ok
        ctx s_osea prog_osea srcAddr_o srcTag_o dstAddr_o dstTag_o
        apRead_o apWrite_o h_osea_start h_src_reg h_dst_reg h_target_read h_target_write
  have h_src_vals :
      mem_vals_eq
        (mirlite.readWordSeq s_mir.mem srcAddr_m (blockSize ctx.layout))
        (oseair.readWordSeq s_osea.mem srcAddr_o (blockSize ctx.layout)) :=
    mem_vals_eq_readWordSeq h_src_mem
  refine ⟨s_osea_post, StepStar.of_runN_ok h_target_run, ?_⟩
  rw [h_next_full]
  simpa [LocalSim, CopyMirPost, CopyOseaPost, s_osea_post] using
    state_sim_write
      (π := ctx.cs.placeMap)
      (ρa := ρa)
      (ρt := ρt)
      (dst_base := ctx.dstBase)
      (dst_reg := ctx.dstReg)
      (dst_layout := ctx.layout)
      (dst_mir := dstAddr_m)
      (dst_osea := dstAddr_o)
      (dst_tag_m := dstTag_m)
      (dst_tag_o := dstTag_o)
      (ap_m' := apWrite_m)
      (ap_o' := apWrite_o)
      (pc_mir := s_mir.pc + 1)
      (pc_osea := s_osea.pc + 1)
      (vals_mir := mirlite.readWordSeq s_mir.mem srcAddr_m (blockSize ctx.layout))
      (vals_osea := oseair.readWordSeq s_osea.mem srcAddr_o (blockSize ctx.layout))
      h_sim h_dst_ptr h_sb_write h_src_vals
      (mirlite_readWordSeq_length s_mir.mem srcAddr_m (blockSize ctx.layout))

end CopyExisting

/-! ## Remaining Work -/

-- TODO: Add the fresh-destination copy case in the block-sized setting.
-- TODO: Extend the supported fragment proof to block-sized binop cases.

end obseq.proof
