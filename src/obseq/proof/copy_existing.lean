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
    pc := 1 }

def CopyOseaPost
  (layout : LayoutTy)
  (s_osea : oseair.State)
  (apWrite : AccessPerms)
  (srcAddr dstAddr : Word) : oseair.State :=
  { s_osea with
    ap := apWrite,
    mem := oseair.writeWordSeq s_osea.mem dstAddr
      (oseair.readWordSeq s_osea.mem srcAddr (blockSize layout)),
    pc := 1 }

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

def mirStart (_ctx : CopyExistingCtx) (s_mir : mirlite.State) : mirlite.State :=
  { s_mir with pc := 0 }

def oseaStart (_ctx : CopyExistingCtx) (s_osea : oseair.State) : oseair.State :=
  { s_osea with pc := 0 }

theorem instrs_nil (ctx : CopyExistingCtx) : ctx.cs.instrs = [] :=
  ctx.h_instrs

def sim (ctx : CopyExistingCtx) (s_mir : mirlite.State) (s_osea : oseair.State) : Prop :=
  StateSim ctx.cs.placeMap s_mir s_osea

def oseaPost (ctx : CopyExistingCtx)
  (s_osea : oseair.State)
  (apWrite : AccessPerms)
  (srcAddr dstAddr : Word) : oseair.State :=
  CopyOseaPost ctx.layout s_osea apWrite srcAddr dstAddr

end CopyExistingCtx

theorem mirlite_step_copy_existing_ok
  (s_mir : mirlite.State)
  (layout : LayoutTy)
  (srcBase dstBase srcAddr srcTag dstAddr dstTag : Word)
  (apRead apWrite : AccessPerms)
  (h_src : s_mir.env.lookup srcBase = some (srcAddr, layoutToTyVal layout, srcTag))
  (h_dst : s_mir.env.lookup dstBase = some (dstAddr, layoutToTyVal layout, dstTag))
  (h_read : sb_read s_mir.ap srcAddr srcTag = SBResult.Ok apRead)
  (h_write : sb_use_mb apRead dstAddr dstTag = SBResult.Ok apWrite) :
  mirlite.step { s_mir with pc := 0 }
    [place(dstBase) ::= copy srcBase] =
    mirlite.Result.Ok (CopyMirPost layout s_mir apWrite srcAddr dstAddr) := by
  let stmt := (place(dstBase) ::= copy srcBase)
  unfold mirlite.step
  have h_pc : ({ s_mir with pc := 0 }).pc < [stmt].length := by
    exact Nat.succ_pos 0
  rw [dif_pos h_pc]
  have h_get : List.get [stmt] ⟨0, h_pc⟩ = stmt := by
    rfl
  rw [h_get]
  unfold mirlite.stepAssignCopy mirlite.finishPlaceAssign mirlite.writeResolvedPlace CopyMirPost
  simp [stmt, obseq.notation.basePlace, obseq.notation.copyRhs, h_src, h_dst,
    h_read, h_write, blockSize]

theorem mirlite_step_copy_existing_inv
  (s_mir : mirlite.State)
  (layout : LayoutTy)
  (srcBase dstBase : Word)
  (s_mir_next : mirlite.State)
  (srcAddr srcTag dstAddr dstTag : Word)
  (h_src : s_mir.env.lookup srcBase = some (srcAddr, layoutToTyVal layout, srcTag))
  (h_dst : s_mir.env.lookup dstBase = some (dstAddr, layoutToTyVal layout, dstTag))
  (h_step :
    mirlite.step { s_mir with pc := 0 }
      [place(dstBase) ::= copy srcBase] =
      mirlite.Result.Ok s_mir_next) :
  ∃ apRead apWrite,
    sb_read s_mir.ap srcAddr srcTag = SBResult.Ok apRead ∧
    sb_use_mb apRead dstAddr dstTag = SBResult.Ok apWrite ∧
    s_mir_next = CopyMirPost layout s_mir apWrite srcAddr dstAddr := by
  cases h_read : sb_read s_mir.ap srcAddr srcTag with
  | Err msg =>
      let stmt := (place(dstBase) ::= copy srcBase)
      unfold mirlite.step at h_step
      have h_pc : ({ s_mir with pc := 0 }).pc < [stmt].length := by
        exact Nat.succ_pos 0
      rw [dif_pos h_pc] at h_step
      have h_get : List.get [stmt] ⟨0, h_pc⟩ = stmt := by
        rfl
      rw [h_get] at h_step
      unfold mirlite.stepAssignCopy mirlite.finishPlaceAssign mirlite.writeResolvedPlace at h_step
      simp [stmt, obseq.notation.basePlace, obseq.notation.copyRhs, h_src, h_dst,
        h_read, blockSize] at h_step
  | Ok apRead =>
      cases h_write : sb_use_mb apRead dstAddr dstTag with
      | Err msg =>
          let stmt := (place(dstBase) ::= copy srcBase)
          unfold mirlite.step at h_step
          have h_pc : ({ s_mir with pc := 0 }).pc < [stmt].length := by
            exact Nat.succ_pos 0
          rw [dif_pos h_pc] at h_step
          have h_get : List.get [stmt] ⟨0, h_pc⟩ = stmt := by
            rfl
          rw [h_get] at h_step
          unfold mirlite.stepAssignCopy mirlite.finishPlaceAssign mirlite.writeResolvedPlace at h_step
          simp [stmt, obseq.notation.basePlace, obseq.notation.copyRhs, h_src, h_dst,
            h_read, h_write, blockSize] at h_step
      | Ok apWrite =>
          have h_ok :=
            mirlite_step_copy_existing_ok
              s_mir layout srcBase dstBase srcAddr srcTag dstAddr dstTag apRead apWrite
              h_src h_dst h_read h_write
          rw [h_ok] at h_step
          injection h_step with h_state
          refine ⟨apRead, apWrite, rfl, h_write, h_state.symm⟩

@[simp] theorem compile_copy_existing
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
  simp [compileStmt, obseq.notation.basePlace, obseq.notation.copyRhs,
    h_src_place, h_dst_place, emit, cleanupInstrs, ctx.instrs_nil, layoutToTyVal, List.map]

/--
Tuple-typed copies are still handled by the same singleton `Memcpy` lowering.

This is the proof-facing sanity check that `copy_existing` remains tuple-capable
even though `ConstOp` is word-only again.
-/
example
  (srcBase dstBase : Word)
  (srcReg dstReg : Register)
  (cs : CompilerState)
  (h_instrs : CompilerEmpty cs)
  (h_src : BaseReady cs srcBase srcReg (LayoutTy.TupL [LayoutTy.NatL, LayoutTy.NatL]))
  (h_dst : BaseReady cs dstBase dstReg (LayoutTy.TupL [LayoutTy.NatL, LayoutTy.NatL])) :
  ({ srcBase := srcBase
   , srcReg := srcReg
   , dstBase := dstBase
   , dstReg := dstReg
   , layout := LayoutTy.TupL [LayoutTy.NatL, LayoutTy.NatL]
   , cs := cs
   , h_instrs := h_instrs
   , h_src_lookup := h_src
   , h_dst_lookup := h_dst } : CopyExistingCtx).compiled =
    [oseair.Instr.Memcpy dstReg srcReg (TyVal.TupTy [TyVal.NatTy, TyVal.NatTy])] := by
  rw [compile_copy_existing
    ({ srcBase := srcBase
     , srcReg := srcReg
     , dstBase := dstBase
     , dstReg := dstReg
     , layout := LayoutTy.TupL [LayoutTy.NatL, LayoutTy.NatL]
     , cs := cs
     , h_instrs := h_instrs
     , h_src_lookup := h_src
     , h_dst_lookup := h_dst } : CopyExistingCtx)]
  simp [layoutToTyVal, layoutToTyValList]

theorem osea_step_copy_existing_ok
  (s_osea : oseair.State)
  (layout : LayoutTy)
  (srcAddr srcTag dstAddr dstTag : Word)
  (srcReg dstReg : Register)
  (apRead apWrite : AccessPerms)
  (h_src_reg :
    s_osea.reg.lookup srcReg =
      some (TyVal.PTy, [oseair.Val.Ptr srcAddr 0 (blockSize layout) srcTag]))
  (h_dst_reg :
    s_osea.reg.lookup dstReg =
      some (TyVal.PTy, [oseair.Val.Ptr dstAddr 0 (blockSize layout) dstTag]))
  (h_read : sb_read s_osea.ap srcAddr srcTag = SBResult.Ok apRead)
  (h_write : sb_use_mb apRead dstAddr dstTag = SBResult.Ok apWrite) :
  oseair.step { s_osea with pc := 0 }
    [oseair.Instr.Memcpy dstReg srcReg (layoutToTyVal layout)] =
    oseair.Result.Ok (CopyOseaPost layout s_osea apWrite srcAddr dstAddr) := by
  let instr := oseair.Instr.Memcpy dstReg srcReg (layoutToTyVal layout)
  unfold oseair.step CopyOseaPost
  have h_pc : ({ s_osea with pc := 0 }).pc < [instr].length := by
    exact Nat.succ_pos 0
  rw [dif_pos h_pc]
  have h_get : List.get [instr] ⟨0, h_pc⟩ = instr := by
    rfl
  rw [h_get]
  simp [instr, h_src_reg, h_dst_reg, h_read, h_write, blockSize]

section CopyExisting

variable (ctx : CopyExistingCtx)
variable (s_mir : mirlite.State)
variable (s_osea : oseair.State)
variable (s_mir_next : mirlite.State)

theorem local_simulation_copy_existing
  (h_sim : ctx.sim s_mir s_osea)
  (h_mir_step :
    mirlite.step (ctx.mirStart s_mir) [ctx.stmt] =
      mirlite.Result.Ok s_mir_next) :
  ∃ s_osea_next,
    StepStar (ctx.oseaStart s_osea) ctx.compiled s_osea_next ∧
    ctx.sim s_mir_next s_osea_next := by
  let ⟨srcAddr, srcTag, h_src_ptr, h_src_mem⟩ := StateSim.place h_sim ctx.h_src_lookup
  let ⟨dstAddr, dstTag, h_dst_ptr, h_dst_mem⟩ := StateSim.place h_sim ctx.h_dst_lookup
  have h_src_env :
      s_mir.env.lookup ctx.srcBase =
        some (srcAddr, layoutToTyVal ctx.layout, srcTag) := h_src_ptr.2.1
  have h_src_reg :
      s_osea.reg.lookup ctx.srcReg =
        some (TyVal.PTy, [oseair.Val.Ptr srcAddr 0 (blockSize ctx.layout) srcTag]) :=
    h_src_ptr.2.2
  have h_dst_env :
      s_mir.env.lookup ctx.dstBase =
        some (dstAddr, layoutToTyVal ctx.layout, dstTag) := h_dst_ptr.2.1
  have h_dst_reg :
      s_osea.reg.lookup ctx.dstReg =
        some (TyVal.PTy, [oseair.Val.Ptr dstAddr 0 (blockSize ctx.layout) dstTag]) :=
    h_dst_ptr.2.2
  have h_ap : s_mir.ap = s_osea.ap := StateSim.ap_eq h_sim
  have h_addrStart : s_mir.mem.addrStart = s_osea.mem.addrStart := StateSim.addrStart_eq h_sim
  have h_mir_step' :
      mirlite.step { s_mir with pc := 0 }
        [place(ctx.dstBase) ::= copy ctx.srcBase] =
        mirlite.Result.Ok s_mir_next := by
    unfold CopyExistingCtx.mirStart CopyExistingCtx.stmt at h_mir_step
    exact h_mir_step
  let ⟨apRead, apWrite, h_read, h_write, h_next⟩ :=
    mirlite_step_copy_existing_inv
      s_mir ctx.layout ctx.srcBase ctx.dstBase s_mir_next
      srcAddr srcTag dstAddr dstTag h_src_env h_dst_env h_mir_step'
  have h_valid_read : SBValid apRead := by
    have h_valid : SBValid s_mir.ap := StateSim.valid_mir h_sim
    exact sb_read_preserves_valid h_valid h_read
  have h_valid_write : SBValid apWrite := sb_use_mb_preserves_valid h_valid_read h_write
  have h_target_read : sb_read s_osea.ap srcAddr srcTag = SBResult.Ok apRead := by
    rw [← h_ap]
    exact h_read
  have h_target_write : sb_use_mb apRead dstAddr dstTag = SBResult.Ok apWrite := by
    exact h_write
  subst s_mir_next
  let s_mir_post := CopyMirPost ctx.layout s_mir apWrite srcAddr dstAddr
  let s_osea_post := ctx.oseaPost s_osea apWrite srcAddr dstAddr
  have h_target_exec :
      StepStar (ctx.oseaStart s_osea) ctx.compiled s_osea_post := by
    rw [compile_copy_existing ctx]
    exact StepStar.single
      (osea_step_copy_existing_ok
        s_osea ctx.layout srcAddr srcTag dstAddr dstTag ctx.srcReg ctx.dstReg
        apRead apWrite h_src_reg h_dst_reg h_target_read h_target_write)
  have h_src_vals :
      mem_vals_eq
        (mirlite.readWordSeq s_mir.mem srcAddr (blockSize ctx.layout))
        (oseair.readWordSeq s_osea.mem srcAddr (blockSize ctx.layout)) :=
    mem_vals_eq_readWordSeq h_src_mem.2
  have h_mir_addrStart_post : s_mir_post.mem.addrStart = s_mir.mem.addrStart := by
    simp [s_mir_post, CopyMirPost]
  have h_osea_addrStart_post : s_osea_post.mem.addrStart = s_osea.mem.addrStart := by
    simp [s_osea_post, CopyOseaPost, CopyExistingCtx.oseaPost]
  refine ⟨s_osea_post, h_target_exec, ?_⟩
  refine ⟨h_valid_write, h_valid_write, rfl, by
    rw [h_mir_addrStart_post, h_osea_addrStart_post]
    exact h_addrStart, ?_⟩
  · intro base reg layout h_lookup
    let ⟨addr0, tag0, h_ptr0, h_mem0⟩ := StateSim.place h_sim h_lookup
    refine ⟨addr0, tag0, ?_, ?_⟩
    · exact ⟨h_lookup, h_ptr0.2.1, h_ptr0.2.2⟩
    · exact sim_mem_at_write h_mem0 h_src_vals

theorem local_preservation_copy_existing
  (h_sim : ctx.sim s_mir s_osea)
  (h_mir_step :
    mirlite.step (ctx.mirStart s_mir) [ctx.stmt] =
      mirlite.Result.Ok s_mir_next) :
  ∃ s_osea_next,
    StepStar (ctx.oseaStart s_osea) ctx.compiled s_osea_next ∧
    ctx.sim s_mir_next s_osea_next ∧
    s_mir_next.ap = s_osea_next.ap := by
  have h_local :=
    local_simulation_copy_existing ctx s_mir s_osea s_mir_next h_sim h_mir_step
  cases h_local with
  | intro s_osea_next h_rest =>
      exact ⟨s_osea_next, h_rest.1, h_rest.2, StateSim.ap_eq h_rest.2⟩

theorem local_validity_copy_existing
  (h_sim : ctx.sim s_mir s_osea)
  (h_valid : SBValid s_mir.ap)
  (h_mir_step :
    mirlite.step (ctx.mirStart s_mir) [ctx.stmt] =
      mirlite.Result.Ok s_mir_next) :
  ∃ s_osea_next,
    StepStar (ctx.oseaStart s_osea) ctx.compiled s_osea_next ∧
    ctx.sim s_mir_next s_osea_next ∧
    s_mir_next.ap = s_osea_next.ap ∧
    SBValid s_mir_next.ap ∧
    SBValid s_osea_next.ap := by
  have h_pres :=
    local_preservation_copy_existing ctx s_mir s_osea s_mir_next h_sim h_mir_step
  let ⟨srcAddr, srcTag, h_src_ptr, _h_src_mem⟩ := StateSim.place h_sim ctx.h_src_lookup
  let ⟨dstAddr, dstTag, h_dst_ptr, _h_dst_mem⟩ := StateSim.place h_sim ctx.h_dst_lookup
  have h_src_env :
      s_mir.env.lookup ctx.srcBase =
        some (srcAddr, layoutToTyVal ctx.layout, srcTag) := h_src_ptr.2.1
  have h_dst_env :
      s_mir.env.lookup ctx.dstBase =
        some (dstAddr, layoutToTyVal ctx.layout, dstTag) := h_dst_ptr.2.1
  have h_mir_step' :
      mirlite.step { s_mir with pc := 0 }
        [place(ctx.dstBase) ::= copy ctx.srcBase] =
        mirlite.Result.Ok s_mir_next := by
    unfold CopyExistingCtx.mirStart CopyExistingCtx.stmt at h_mir_step
    exact h_mir_step
  let ⟨apRead, apWrite, h_read, h_write, h_next⟩ :=
    mirlite_step_copy_existing_inv
      s_mir ctx.layout ctx.srcBase ctx.dstBase s_mir_next
      srcAddr srcTag dstAddr dstTag h_src_env h_dst_env h_mir_step'
  cases h_pres with
  | intro s_osea_next h_rest =>
      let ⟨h_steps, h_sim_next, h_ap_eq⟩ := h_rest
      have h_valid_read : SBValid apRead := sb_read_preserves_valid h_valid h_read
      have h_valid_write : SBValid apWrite := sb_use_mb_preserves_valid h_valid_read h_write
      have h_valid_mir_next : SBValid s_mir_next.ap := by
        rw [h_next]
        exact h_valid_write
      have h_valid_osea_next : SBValid s_osea_next.ap := StateSim.valid_osea h_sim_next
      exact ⟨s_osea_next, h_steps, h_sim_next, h_ap_eq,
        h_valid_mir_next, h_valid_osea_next⟩

theorem embedded_simulation_copy_existing
  (prog_mir : mirlite.Prog)
  (prog_osea : oseair.Prog)
  (h_sim : ctx.sim s_mir s_osea)
  (h_mir_start : StartsAt prog_mir s_mir.pc [ctx.stmt])
  (h_osea_start : StartsAt prog_osea s_osea.pc ctx.compiled)
  (h_mir_step : mirlite.step s_mir prog_mir = mirlite.Result.Ok s_mir_next) :
  ∃ s_osea_next,
    StepStar s_osea prog_osea s_osea_next ∧
    ctx.sim s_mir_next s_osea_next := by
  let ⟨srcAddr, srcTag, h_src_ptr, h_src_mem⟩ := StateSim.place h_sim ctx.h_src_lookup
  let ⟨dstAddr, dstTag, h_dst_ptr, h_dst_mem⟩ := StateSim.place h_sim ctx.h_dst_lookup
  have h_src_env :
      s_mir.env.lookup ctx.srcBase =
        some (srcAddr, layoutToTyVal ctx.layout, srcTag) := h_src_ptr.2.1
  have h_src_reg :
      s_osea.reg.lookup ctx.srcReg =
        some (TyVal.PTy, [oseair.Val.Ptr srcAddr 0 (blockSize ctx.layout) srcTag]) :=
    h_src_ptr.2.2
  have h_dst_env :
      s_mir.env.lookup ctx.dstBase =
        some (dstAddr, layoutToTyVal ctx.layout, dstTag) := h_dst_ptr.2.1
  have h_dst_reg :
      s_osea.reg.lookup ctx.dstReg =
        some (TyVal.PTy, [oseair.Val.Ptr dstAddr 0 (blockSize ctx.layout) dstTag]) :=
    h_dst_ptr.2.2
  have h_ap : s_mir.ap = s_osea.ap := StateSim.ap_eq h_sim
  have h_addrStart : s_mir.mem.addrStart = s_osea.mem.addrStart := StateSim.addrStart_eq h_sim
  have h_stmt_mir : prog_mir.get? s_mir.pc = some ctx.stmt := StartsAt.singleton h_mir_start
  rcases List.get?_eq_some_iff.mp h_stmt_mir with ⟨h_pc_mir, h_get_mir⟩
  unfold mirlite.step at h_mir_step
  rw [dif_pos h_pc_mir, h_get_mir] at h_mir_step
  cases h_read : sb_read s_mir.ap srcAddr srcTag with
  | Err _ =>
      simp [CopyExistingCtx.stmt, obseq.notation.basePlace, obseq.notation.copyRhs,
        mirlite.stepAssignCopy, mirlite.finishPlaceAssign, mirlite.writeResolvedPlace,
        h_src_env, h_dst_env, h_read, blockSize] at h_mir_step
  | Ok apRead =>
      cases h_write : sb_use_mb apRead dstAddr dstTag with
      | Err _ =>
          simp [CopyExistingCtx.stmt, obseq.notation.basePlace, obseq.notation.copyRhs,
            mirlite.stepAssignCopy, mirlite.finishPlaceAssign, mirlite.writeResolvedPlace,
            h_src_env, h_dst_env, h_read, h_write, blockSize] at h_mir_step
      | Ok apWrite =>
          have h_next_full :
              s_mir_next =
                { s_mir with
                  ap := apWrite,
                  mem := mirlite.writeWordSeq s_mir.mem dstAddr
                    (mirlite.readWordSeq s_mir.mem srcAddr (blockSize ctx.layout)),
                  pc := s_mir.pc + 1 } := by
            simpa [CopyExistingCtx.stmt, obseq.notation.basePlace, obseq.notation.copyRhs,
              mirlite.stepAssignCopy, mirlite.finishPlaceAssign, mirlite.writeResolvedPlace,
              h_src_env, h_dst_env, h_read, h_write, blockSize] using h_mir_step.symm
          have h_valid_read : SBValid apRead := by
            exact sb_read_preserves_valid (StateSim.valid_mir h_sim) h_read
          have h_valid_write : SBValid apWrite := sb_use_mb_preserves_valid h_valid_read h_write
          have h_target_read : sb_read s_osea.ap srcAddr srcTag = SBResult.Ok apRead := by
            rw [← h_ap]
            exact h_read
          have h_target_write : sb_use_mb apRead dstAddr dstTag = SBResult.Ok apWrite := by
            exact h_write
          have h_stmt_osea :
              prog_osea.get? s_osea.pc =
                some (oseair.Instr.Memcpy ctx.dstReg ctx.srcReg (layoutToTyVal ctx.layout)) := by
            rw [compile_copy_existing ctx] at h_osea_start
            simpa using StartsAt.singleton h_osea_start
          rcases List.get?_eq_some_iff.mp h_stmt_osea with ⟨h_pc_osea, h_get_osea⟩
          let s_mir_post :=
            { s_mir with
              ap := apWrite,
              mem := mirlite.writeWordSeq s_mir.mem dstAddr
                (mirlite.readWordSeq s_mir.mem srcAddr (blockSize ctx.layout)),
              pc := s_mir.pc + 1 }
          let s_osea_post :=
            { s_osea with
              ap := apWrite,
              mem := oseair.writeWordSeq s_osea.mem dstAddr
                (oseair.readWordSeq s_osea.mem srcAddr (blockSize ctx.layout)),
              pc := s_osea.pc + 1 }
          have h_target_full :
              oseair.step s_osea prog_osea = oseair.Result.Ok s_osea_post := by
            unfold oseair.step
            rw [dif_pos h_pc_osea, h_get_osea]
            simp [s_osea_post, h_src_reg, h_dst_reg, h_target_read, h_target_write, blockSize]
          have h_src_vals :
              mem_vals_eq
                (mirlite.readWordSeq s_mir.mem srcAddr (blockSize ctx.layout))
                (oseair.readWordSeq s_osea.mem srcAddr (blockSize ctx.layout)) :=
            mem_vals_eq_readWordSeq h_src_mem.2
          have h_mir_addrStart_post : s_mir_post.mem.addrStart = s_mir.mem.addrStart := by
            simp [s_mir_post]
          have h_osea_addrStart_post : s_osea_post.mem.addrStart = s_osea.mem.addrStart := by
            simp [s_osea_post]
          refine ⟨s_osea_post, StepStar.single h_target_full, ?_⟩
          rw [h_next_full]
          refine ⟨h_valid_write, h_valid_write, rfl, by
            rw [h_mir_addrStart_post, h_osea_addrStart_post]
            exact h_addrStart, ?_⟩
          · intro base reg layout h_lookup
            let ⟨addr0, tag0, h_ptr0, h_mem0⟩ := StateSim.place h_sim h_lookup
            refine ⟨addr0, tag0, ?_, ?_⟩
            · exact ⟨h_lookup, h_ptr0.2.1, h_ptr0.2.2⟩
            · exact sim_mem_at_write h_mem0 h_src_vals

theorem embedded_preservation_copy_existing
  (prog_mir : mirlite.Prog)
  (prog_osea : oseair.Prog)
  (h_sim : ctx.sim s_mir s_osea)
  (h_mir_start : StartsAt prog_mir s_mir.pc [ctx.stmt])
  (h_osea_start : StartsAt prog_osea s_osea.pc ctx.compiled)
  (h_mir_step : mirlite.step s_mir prog_mir = mirlite.Result.Ok s_mir_next) :
  ∃ s_osea_next,
    StepStar s_osea prog_osea s_osea_next ∧
    ctx.sim s_mir_next s_osea_next ∧
    s_mir_next.ap = s_osea_next.ap := by
  let ⟨s_osea_next, h_steps, h_sim_next⟩ :=
    embedded_simulation_copy_existing ctx s_mir s_osea s_mir_next
      prog_mir prog_osea h_sim h_mir_start h_osea_start h_mir_step
  exact ⟨s_osea_next, h_steps, h_sim_next, StateSim.ap_eq h_sim_next⟩

theorem embedded_validity_copy_existing
  (prog_mir : mirlite.Prog)
  (prog_osea : oseair.Prog)
  (h_sim : ctx.sim s_mir s_osea)
  (h_valid : SBValid s_mir.ap)
  (h_mir_start : StartsAt prog_mir s_mir.pc [ctx.stmt])
  (h_osea_start : StartsAt prog_osea s_osea.pc ctx.compiled)
  (h_mir_step : mirlite.step s_mir prog_mir = mirlite.Result.Ok s_mir_next) :
  ∃ s_osea_next,
    StepStar s_osea prog_osea s_osea_next ∧
    ctx.sim s_mir_next s_osea_next ∧
    s_mir_next.ap = s_osea_next.ap ∧
    SBValid s_mir_next.ap ∧
    SBValid s_osea_next.ap := by
  let ⟨s_osea_next, h_steps, h_sim_next, h_ap_eq⟩ :=
    embedded_preservation_copy_existing ctx s_mir s_osea s_mir_next
      prog_mir prog_osea h_sim h_mir_start h_osea_start h_mir_step
  let ⟨srcAddr, srcTag, h_src_ptr, _h_src_mem⟩ := StateSim.place h_sim ctx.h_src_lookup
  let ⟨dstAddr, dstTag, h_dst_ptr, _h_dst_mem⟩ := StateSim.place h_sim ctx.h_dst_lookup
  have h_src_env :
      s_mir.env.lookup ctx.srcBase =
        some (srcAddr, layoutToTyVal ctx.layout, srcTag) := h_src_ptr.2.1
  have h_dst_env :
      s_mir.env.lookup ctx.dstBase =
        some (dstAddr, layoutToTyVal ctx.layout, dstTag) := h_dst_ptr.2.1
  have h_stmt_mir : prog_mir.get? s_mir.pc = some ctx.stmt := StartsAt.singleton h_mir_start
  rcases List.get?_eq_some_iff.mp h_stmt_mir with ⟨h_pc_mir, h_get_mir⟩
  unfold mirlite.step at h_mir_step
  rw [dif_pos h_pc_mir, h_get_mir] at h_mir_step
  cases h_read : sb_read s_mir.ap srcAddr srcTag with
  | Err _ =>
      simp [CopyExistingCtx.stmt, obseq.notation.basePlace, obseq.notation.copyRhs,
        mirlite.stepAssignCopy, mirlite.finishPlaceAssign, mirlite.writeResolvedPlace,
        h_src_env, h_dst_env, h_read, blockSize] at h_mir_step
  | Ok apRead =>
      cases h_write : sb_use_mb apRead dstAddr dstTag with
      | Err _ =>
          simp [CopyExistingCtx.stmt, obseq.notation.basePlace, obseq.notation.copyRhs,
            mirlite.stepAssignCopy, mirlite.finishPlaceAssign, mirlite.writeResolvedPlace,
            h_src_env, h_dst_env, h_read, h_write, blockSize] at h_mir_step
      | Ok apWrite =>
          have h_next :
              s_mir_next =
                { s_mir with
                  ap := apWrite,
                  mem := mirlite.writeWordSeq s_mir.mem dstAddr
                    (mirlite.readWordSeq s_mir.mem srcAddr (blockSize ctx.layout)),
                  pc := s_mir.pc + 1 } := by
            simpa [CopyExistingCtx.stmt, obseq.notation.basePlace, obseq.notation.copyRhs,
              mirlite.stepAssignCopy, mirlite.finishPlaceAssign, mirlite.writeResolvedPlace,
              h_src_env, h_dst_env, h_read, h_write, blockSize] using h_mir_step.symm
          have h_valid_read : SBValid apRead := sb_read_preserves_valid h_valid h_read
          have h_valid_next : SBValid s_mir_next.ap := by
            rw [h_next]
            exact sb_use_mb_preserves_valid h_valid_read h_write
          exact ⟨s_osea_next, h_steps, h_sim_next, h_ap_eq,
            h_valid_next, StateSim.valid_osea h_sim_next⟩

end CopyExisting

/-! ## Remaining Work -/

-- TODO: Add the fresh-destination copy case in the block-sized setting.
-- TODO: Extend the supported fragment proof to block-sized binop cases.

end obseq.proof
