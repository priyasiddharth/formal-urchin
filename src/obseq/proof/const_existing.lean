import obseq.proof.state_helpers

/-!
# `obseq.proof.const_existing`

Local compiler-correctness lemmas for the existing-destination word-constant
fragment.

Unlike the fresh fragment, the existing destination may now be an arbitrary
projected place. The proof therefore tracks the base layout and the resolved
projection offset explicitly, while `StateSim` itself remains keyed by base
places only.
-/

namespace obseq.proof

open obseq
open obseq.mirlite
open obseq.oseair hiding State Result
open obseq.compile
open scoped obseq.notation

structure ConstExistingCtx where
  dst : mirlite.Place
  reg : Register
  n : Word
  cs : CompilerState
  h_instrs : CompilerEmpty cs
  baseLayout : LayoutTy
  off : Word
  h_lookup : BaseReady cs dst.base reg baseLayout
  h_path : layoutResolvePath baseLayout dst.path = some (off, LayoutTy.NatL)

namespace ConstExistingCtx

def tmpReg (ctx : ConstExistingCtx) : Register :=
  Register.R ctx.cs.nextReg

def stmt (ctx : ConstExistingCtx) : mirlite.Stmt :=
  mirlite.Stmt.Assgn (obseq.notation.placeExpr ctx.dst) (obseq.notation.constRhs ctx.n)

def compiled (ctx : ConstExistingCtx) : oseair.Prog :=
  (compileStmt ctx.cs ctx.stmt).instrs

theorem instrs_nil (ctx : ConstExistingCtx) : ctx.cs.instrs = [] :=
  ctx.h_instrs

@[simp] theorem compiled_eq
  (ctx : ConstExistingCtx) :
  ctx.compiled =
    if ctx.off = 0 then
      [oseair.Instr.CStore TyVal.NatTy [oseair.Val.Dat ctx.n] ctx.reg]
    else
      [oseair.Instr.Assgn ctx.tmpReg (oseair.Rhs.MutBorOffset ctx.reg ctx.off),
       oseair.Instr.CStore TyVal.NatTy [oseair.Val.Dat ctx.n] ctx.tmpReg,
       oseair.Instr.Die ctx.tmpReg] := by
  by_cases h_off : ctx.off = 0
  · have h_place :
        placeToReg ctx.cs ctx.dst mirlite.RefKind.Mut (some LayoutTy.NatL) =
          { reg := ctx.reg, layout := LayoutTy.NatL, cleanup := [], cs := ctx.cs } := by
      unfold placeToReg
      rw [ctx.h_lookup]
      simp [ctx.h_path, h_off]
    unfold ConstExistingCtx.compiled ConstExistingCtx.stmt compileStmt
    simpa [h_off] using
      (by
        simp [h_place, emit, cleanupInstrs, obseq.notation.placeExpr,
      obseq.notation.constRhs, ctx.instrs_nil]
      )
  · have h_place :
        placeToReg ctx.cs ctx.dst mirlite.RefKind.Mut (some LayoutTy.NatL) =
          { reg := ctx.tmpReg,
            layout := LayoutTy.NatL,
            cleanup := [ctx.tmpReg],
            cs :=
              { nextReg := ctx.cs.nextReg + 1,
                placeMap := ctx.cs.placeMap,
                instrs := ctx.cs.instrs ++
                  [oseair.Instr.Assgn ctx.tmpReg (oseair.Rhs.MutBorOffset ctx.reg ctx.off)] } } := by
      unfold placeToReg
      rw [ctx.h_lookup]
      simp [ctx.h_path, h_off, ConstExistingCtx.tmpReg, freshReg, emit]
    unfold ConstExistingCtx.compiled ConstExistingCtx.stmt compileStmt
    simpa [h_off] using
      (by
        simp [h_place, emit, cleanupInstrs, obseq.notation.placeExpr,
      obseq.notation.constRhs, ConstExistingCtx.tmpReg, ctx.instrs_nil]
      )

end ConstExistingCtx

namespace ConstExisting

abbrev LocalSim
  (ctx : ConstExistingCtx)
  (ρa : AddrRenaming)
  (ρt : TagRenaming)
  (s_mir : mirlite.State)
  (s_osea : oseair.State) : Prop :=
  StateSim ctx.cs.placeMap ρa ρt s_mir s_osea

theorem mirlite_step_inv
  (ctx : ConstExistingCtx)
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
        mem := mirlite.writeWordSeq s_mir.mem (addr + ctx.off) [mirlite.MemValue.Val ctx.n],
        pc := s_mir.pc + 1 } := by
  have h_stmt_mir : prog_mir.get? s_mir.pc = some ctx.stmt := StartsAt.singleton h_start
  rcases List.get?_eq_some_iff.mp h_stmt_mir with ⟨h_pc_mir, h_get_mir⟩
  unfold mirlite.step at h_step
  rw [dif_pos h_pc_mir, h_get_mir] at h_step
  simp [ConstExistingCtx.stmt, obseq.notation.placeExpr, obseq.notation.constRhs,
    mirlite.stepAssignConst] at h_step
  rw [finishPlaceAssign_existing_eq h_env ctx.h_path] at h_step
  cases h_use : sb_use_mb s_mir.ap (addr + ctx.off) tag with
  | Err _ =>
      simp [h_use] at h_step
  | Ok ap' =>
      refine ⟨ap', rfl, ?_⟩
      simpa [h_use] using h_step.symm

variable (ctx : ConstExistingCtx)
variable (s_mir : mirlite.State)
variable (s_osea : oseair.State)
variable (s_mir_next : mirlite.State)
variable (ρa : AddrRenaming)
variable (ρt : TagRenaming)

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
  have h_env :
      s_mir.env.lookup ctx.dst.base =
        some (addr_m, layoutToTyVal ctx.baseLayout, tag_m) :=
    place_runtime_sim.env h_ptr
  have h_reg :
      s_osea.reg.lookup ctx.reg =
        some (TyVal.PTy, [oseair.Val.Ptr addr_o 0 (blockSize ctx.baseLayout) tag_o]) :=
    place_runtime_sim.reg h_ptr
  have h_addr_base : ρa addr_m = some addr_o := place_runtime_sim.addr h_ptr
  have h_addr : ρa (addr_m + ctx.off) = some (addr_o + ctx.off) :=
    addr_rename_offset h_addr_base
  have h_tag : ρt tag_m = some tag_o := place_runtime_sim.tag h_ptr
  have h_fit : ctx.off + blockSize LayoutTy.NatL ≤ blockSize ctx.baseLayout :=
    layoutResolvePath_blockSize_le ctx.h_path

  let ⟨ap_m', h_use, h_next_full⟩ :=
    mirlite_step_inv ctx s_mir s_mir_next prog_mir addr_m tag_m h_env h_mir_start h_mir_step
  let ⟨ap_parent_o, h_target_parent_use, h_sb_parent⟩ :=
    sb_use_mb_sim_ok (StateSim.sb h_sim) h_addr h_tag h_use

  by_cases h_off : ctx.off = 0
  · have h_base_nonempty : 0 < blockSize ctx.baseLayout := by
      have h_nat_le : blockSize LayoutTy.NatL ≤ blockSize ctx.baseLayout := by
        simpa [h_off] using h_fit
      exact Nat.lt_of_lt_of_le (by decide : 0 < blockSize LayoutTy.NatL) h_nat_le
    let s_osea_post :=
      { s_osea with
        ap := ap_parent_o,
        mem := oseair.writeWordSeq s_osea.mem addr_o [oseair.Val.Dat ctx.n],
        pc := s_osea.pc + 1 }
    have h_target_use0 : sb_use_mb s_osea.ap (addr_o + 0) tag_o = SBResult.Ok ap_parent_o := by
      simpa [h_off] using h_target_parent_use
    have h_target_run :
        oseair.runN 1 s_osea prog_osea = oseair.Result.Ok s_osea_post := by
      have h_osea_start' :
          StartsAt prog_osea s_osea.pc
            [oseair.Instr.CStore TyVal.NatTy [oseair.Val.Dat ctx.n] ctx.reg] := by
        simpa [ctx.compiled_eq, h_off] using h_osea_start
      simpa [s_osea_post, h_off] using
        osea_run_ptr_cstore_embedded_ok
          s_osea prog_osea LayoutTy.NatL [oseair.Val.Dat ctx.n]
          addr_o 0 (blockSize ctx.baseLayout) tag_o ctx.reg ap_parent_o
          h_osea_start' h_reg h_base_nonempty h_target_use0
    refine ⟨s_osea_post, StepStar.of_runN_ok h_target_run, ?_⟩
    rw [h_next_full]
    simpa [s_osea_post, h_off] using
      state_sim_write_subrange
        (π := ctx.cs.placeMap)
        (ρa := ρa)
        (ρt := ρt)
        (dst_base := ctx.dst.base)
        (dst_reg := ctx.reg)
        (baseLayout := ctx.baseLayout)
        (subLayout := LayoutTy.NatL)
        (dst_mir := addr_m)
        (dst_osea := addr_o)
        (dst_tag_m := tag_m)
        (dst_tag_o := tag_o)
        (off := ctx.off)
        (ap_m' := ap_m')
        (ap_o' := ap_parent_o)
        (pc_mir := s_mir.pc + 1)
        (pc_osea := s_osea.pc + 1)
        (vals_mir := [mirlite.MemValue.Val ctx.n])
        (vals_osea := [oseair.Val.Dat ctx.n])
        h_sim h_ptr h_sb_parent (mem_vals_eq_word ctx.n) rfl h_fit
  · have h_off_lt : ctx.off < blockSize ctx.baseLayout := by
      exact Nat.lt_of_lt_of_le
        (Nat.lt_add_of_pos_right (by decide : 0 < blockSize LayoutTy.NatL))
        h_fit
    have h_tmp_fresh :
        ∀ base layout, ctx.cs.placeMap.lookup base = some (ctx.tmpReg, layout) → False := by
      intro base layout h_lookup
      exact alloc_fresh_reg (cs := ctx.cs) base layout h_lookup
    have h_reg_ne : ctx.reg ≠ ctx.tmpReg := by
      intro h_eq
      have h_lookup_tmp : ctx.cs.placeMap.lookup ctx.dst.base = some (ctx.tmpReg, ctx.baseLayout) := by
        simpa [ConstExistingCtx.tmpReg, h_eq] using ctx.h_lookup
      exact h_tmp_fresh ctx.dst.base ctx.baseLayout h_lookup_tmp
    let ⟨tempTag, ap_ref_o, ap_use_o, ap_final_o, h_ref, h_use_tmp, h_die, h_stack_eq⟩ :=
      sb_ref_mut_use_die_ok_of_use_ok h_target_parent_use
    have h_sb_final : sb_sim ρa ρt ap_m' ap_final_o :=
      sb_sim_of_right_stackMap_eq h_sb_parent h_stack_eq
    let s_osea_post :=
      { s_osea with
        reg := s_osea.reg.insert ctx.tmpReg
          (TyVal.PTy, [oseair.Val.Ptr addr_o ctx.off (blockSize ctx.baseLayout) tempTag]),
        ap := ap_final_o,
        mem := oseair.writeWordSeq s_osea.mem (addr_o + ctx.off) [oseair.Val.Dat ctx.n],
        pc := s_osea.pc + 3 }
    have h_target_run :
        oseair.runN 3 s_osea prog_osea = oseair.Result.Ok s_osea_post := by
      have h_osea_start' :
          StartsAt prog_osea s_osea.pc
            [oseair.Instr.Assgn ctx.tmpReg (oseair.Rhs.MutBorOffset ctx.reg ctx.off),
             oseair.Instr.CStore TyVal.NatTy [oseair.Val.Dat ctx.n] ctx.tmpReg,
             oseair.Instr.Die ctx.tmpReg] := by
        simpa [ctx.compiled_eq, h_off] using h_osea_start
      simpa [s_osea_post, ConstExistingCtx.tmpReg] using
        osea_run_projected_cstore_embedded_ok
          s_osea prog_osea ctx.baseLayout LayoutTy.NatL [oseair.Val.Dat ctx.n]
          addr_o tag_o ctx.reg ctx.tmpReg ctx.off tempTag
          ap_ref_o ap_use_o ap_final_o
          h_osea_start' h_reg h_off_lt h_ref h_use_tmp h_die
    have h_sim_reg :
        StateSim ctx.cs.placeMap ρa ρt
          s_mir
          { s_osea with
            reg := s_osea.reg.insert ctx.tmpReg
              (TyVal.PTy, [oseair.Val.Ptr addr_o ctx.off (blockSize ctx.baseLayout) tempTag]) } := by
      exact state_sim_reg_insert_other h_sim h_tmp_fresh
    have h_ptr_reg :
        place_runtime_sim ctx.cs.placeMap ρa ρt
          s_mir
          { s_osea with
            reg := s_osea.reg.insert ctx.tmpReg
              (TyVal.PTy, [oseair.Val.Ptr addr_o ctx.off (blockSize ctx.baseLayout) tempTag]) }
          ctx.dst.base ctx.reg addr_m addr_o tag_m tag_o ctx.baseLayout :=
      place_runtime_sim_reg_insert_other h_ptr h_reg_ne
    refine ⟨s_osea_post, StepStar.of_runN_ok h_target_run, ?_⟩
    rw [h_next_full]
    simpa [s_osea_post] using
      state_sim_write_subrange
        (π := ctx.cs.placeMap)
        (ρa := ρa)
        (ρt := ρt)
        (dst_base := ctx.dst.base)
        (dst_reg := ctx.reg)
        (baseLayout := ctx.baseLayout)
        (subLayout := LayoutTy.NatL)
        (dst_mir := addr_m)
        (dst_osea := addr_o)
        (dst_tag_m := tag_m)
        (dst_tag_o := tag_o)
        (off := ctx.off)
        (ap_m' := ap_m')
        (ap_o' := ap_final_o)
        (pc_mir := s_mir.pc + 1)
        (pc_osea := s_osea.pc + 3)
        (vals_mir := [mirlite.MemValue.Val ctx.n])
        (vals_osea := [oseair.Val.Dat ctx.n])
        h_sim_reg h_ptr_reg h_sb_final (mem_vals_eq_word ctx.n) rfl h_fit

end ConstExisting

end obseq.proof
