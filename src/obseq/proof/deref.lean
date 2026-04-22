import obseq.proof.state_helpers

/-!
# `obseq.proof.deref`

Simulation proofs for the `DrefOp` MIR operation.

This file covers:

- existing destinations, including projected source/destination paths, and
- fresh base-only destinations.

The shared MIR shape is:

1. Read the `PlaceTag q gq` stored at `src`.
2. Resolve `q` to the pointed-to block.
3. Read that block through tag `gq`.
4. Write the resulting payload either to an existing destination or into a
   freshly allocated base-only destination.
-/

namespace obseq.proof

open obseq
open obseq.mirlite
open obseq.oseair hiding State Result
open obseq.compile
open scoped obseq.notation

variable {A_m : mirlite.AllocatorSpec} {A_o : oseair.AllocatorSpec}

def derefStmt (src dst : mirlite.Place) : mirlite.Stmt :=
  mirlite.Stmt.Assgn (mirlite.LExpr.Place dst)
    (mirlite.RExpr.DrefOp src)

def derefResReg (cs : CompilerState) : Register :=
  Register.R cs.nextReg

def derefSrcTmpReg (cs : CompilerState) : Register :=
  Register.R (cs.nextReg + 1)

def derefLoadedPtrReg (cs : CompilerState) (srcOff : Word) : Register :=
  if srcOff = 0 then Register.R (cs.nextReg + 1) else Register.R (cs.nextReg + 2)

def derefDstTmpReg (cs : CompilerState) (srcOff : Word) : Register :=
  if srcOff = 0 then Register.R (cs.nextReg + 2) else Register.R (cs.nextReg + 3)

abbrev derefInnerTy (innerLayout : LayoutTy) : TyVal :=
  layoutToTyVal innerLayout

/-! ## Context -/

/--
Proof context for an existing-destination `DrefOp` with base-only source and
destination.

The source place `src` must have a pointer layout `PtrL innerLayout` — the
memory at `src` contains a `PlaceTag` (MIR) / `Ptr` (OSEA) that points to
the actual data.
-/
structure DerefExistingCtx where
  src : mirlite.Place
  dst : mirlite.Place
  srcReg : Register
  dstReg : Register
  innerLayout : LayoutTy
  cs : CompilerState
  h_regs_below : PlaceMapRegsBelowNextReg cs
  h_instrs : CompilerEmpty cs
  h_src_lookup : BaseReady cs src.base srcReg (LayoutTy.PtrL innerLayout)
  h_dst_lookup : BaseReady cs dst.base dstReg innerLayout
  h_src_base : src.path = []
  h_dst_base : dst.path = []

namespace DerefExisting

variable (ctx : DerefExistingCtx)

/-- The MIR statement being compiled. -/
abbrev stmt : mirlite.Stmt :=
  mirlite.Stmt.Assgn (mirlite.LExpr.Place ctx.dst)
    (mirlite.RExpr.DrefOp ctx.src)

/-- Source layout is `PtrL innerLayout`. -/
abbrev srcLayout : LayoutTy := LayoutTy.PtrL ctx.innerLayout

/-- Temporary register for the allocated result block. -/
abbrev resReg : Register := Register.R ctx.cs.nextReg

/-- Temporary register for the loaded pointer. -/
abbrev loadedPtrReg : Register := Register.R (ctx.cs.nextReg + 1)

/-- The inner type value. -/
abbrev innerTy : TyVal := layoutToTyVal ctx.innerLayout

/-- Local simulation abbreviation. -/
abbrev LocalSim
  (ρa : AddrRenameMap) (ρt : TagRenameMap)
  (s_mir : mirlite.State) (s_osea : oseair.State)
  (ptr_sim : PtrSimPred := defaultPtrSim) : Prop :=
  StateSim ctx.cs.placeMap ρa ρt s_mir s_osea ptr_sim

/-! ## MIR step inversion -/

theorem resolveDirectPlace_ok_state_eq
  {state : mirlite.State}
  {p : mirlite.Place}
  {s' : mirlite.State}
  {res : mirlite.PlaceRes}
  (h :
    mirlite.resolveDirectPlace state p =
      (mirlite.Result.Ok s', res)) :
  s' = state := by
  cases p with
  | mk base path =>
      unfold mirlite.resolveDirectPlace at h
      cases h_env : state.env.lookup base with
      | none =>
          simp [h_env] at h
      | some entry =>
          rcases entry with ⟨baseAddr, baseTy, baseTag⟩
          cases h_path : mirlite.resolvePath baseTy path with
          | none =>
              simp [h_env, h_path] at h
          | some entry' =>
              rcases entry' with ⟨offset, ty⟩
              simp [h_env, h_path] at h
              exact h.1.symm

theorem mirlite_step_inv_common
  (src dst : mirlite.Place)
  (srcBaseLayout innerLayout dstBaseLayout : LayoutTy)
  (srcOff dstOff : Word)
  (s_mir s_mir_next : mirlite.State)
  (prog_mir : mirlite.Prog)
  (srcBaseAddr srcTag dstBaseAddr dstTag : Word)
  (h_src_env :
    s_mir.env.lookup src.base =
      some (srcBaseAddr, layoutToTyVal srcBaseLayout, srcTag))
  (h_dst_env :
    s_mir.env.lookup dst.base =
      some (dstBaseAddr, layoutToTyVal dstBaseLayout, dstTag))
  (h_src_path :
    layoutResolvePath srcBaseLayout src.path = some (srcOff, LayoutTy.PtrL innerLayout))
  (h_dst_path :
    layoutResolvePath dstBaseLayout dst.path = some (dstOff, innerLayout))
  (h_start : StartsAt prog_mir s_mir.pc [derefStmt src dst])
  (h_step : mirlite.stepWith A_m s_mir prog_mir = mirlite.Result.Ok s_mir_next) :
  ∃ (ap_src_read : AccessPerms)
    (q : mirlite.Place) (gq : Tag) (targetRes : mirlite.PlaceRes)
    (ap_target_read ap_write : AccessPerms),
    sb_read s_mir.ap (srcBaseAddr + srcOff) srcTag = SBResult.Ok ap_src_read ∧
    s_mir.mem.find? (srcBaseAddr + srcOff) = some (mirlite.MemValue.PlaceTag q gq) ∧
    mirlite.resolveDirectPlace { s_mir with ap := ap_src_read } q =
      (mirlite.Result.Ok { s_mir with ap := ap_src_read }, targetRes) ∧
    sb_read ap_src_read targetRes.addr gq = SBResult.Ok ap_target_read ∧
    sb_use_mb ap_target_read (dstBaseAddr + dstOff) dstTag = SBResult.Ok ap_write ∧
    s_mir_next =
      { s_mir with
        ap := ap_write,
        mem := mirlite.writeWordSeq s_mir.mem (dstBaseAddr + dstOff)
          (mirlite.readWordSeq s_mir.mem targetRes.addr (typeSize targetRes.ty)),
        pc := s_mir.pc + 1 } := by
  have h_stmt_mir : prog_mir.get? s_mir.pc = some (derefStmt src dst) := StartsAt.singleton h_start
  rcases List.get?_eq_some_iff.mp h_stmt_mir with ⟨h_pc_mir, h_get_mir⟩
  unfold mirlite.stepWith at h_step
  rw [dif_pos h_pc_mir, h_get_mir] at h_step
  simp [derefStmt, mirlite.stepAssignGenericWith, mirlite.evalRExpr] at h_step
  unfold mirlite.resolvePlace at h_step
  rw [resolveDirectPlace_eq_of_env_lookup h_src_env h_src_path] at h_step
  cases h_src_read : sb_read s_mir.ap (srcBaseAddr + srcOff) srcTag with
  | Err _ =>
      simp [h_src_read] at h_step
  | Ok ap_src_read =>
      simp [h_src_read] at h_step
      cases h_src_find : s_mir.mem.find? (srcBaseAddr + srcOff) with
      | none =>
          simp [mirlite.readWordSeq, h_src_find] at h_step
      | some v =>
          cases v with
          | Undef =>
              simp [mirlite.readWordSeq, h_src_find] at h_step
          | Val n =>
              simp [mirlite.readWordSeq, h_src_find] at h_step
          | PlaceTag q gq =>
              simp [mirlite.readWordSeq, h_src_find] at h_step
              cases h_resolve :
                mirlite.resolveDirectPlace { s_mir with ap := ap_src_read } q with
              | mk res resTarget =>
                  cases res with
                  | Err _ =>
                      simp [mirlite.resolvePlace, h_resolve] at h_step
                  | Ok s_res =>
                      have hs_res : s_res = { s_mir with ap := ap_src_read } :=
                        resolveDirectPlace_ok_state_eq h_resolve
                      cases hs_res
                      simp [mirlite.resolvePlace, h_resolve] at h_step
                      cases h_target_read : sb_read ap_src_read resTarget.addr gq with
                      | Err _ =>
                          simp [h_target_read] at h_step
                      | Ok ap_target_read =>
                          simp [h_target_read] at h_step
                          have h_dst_env' :
                              { s_mir with ap := ap_target_read }.env.lookup dst.base =
                                some (dstBaseAddr, layoutToTyVal dstBaseLayout, dstTag) := by
                            simpa using h_dst_env
                          rw [finishPlaceAssignWith_existing_eq
                            (pc0 := s_mir.pc)
                            (state := { s_mir with ap := ap_target_read })
                            (p := dst)
                            (vals := mirlite.readWordSeq s_mir.mem
                              resTarget.addr (typeSize resTarget.ty))
                            (ty := resTarget.ty)
                            (addr := dstBaseAddr)
                            (tag := dstTag)
                            (off := dstOff)
                            (baseLayout := dstBaseLayout)
                            (subLayout := innerLayout)
                            h_dst_env' h_dst_path] at h_step
                          cases h_use : sb_use_mb ap_target_read (dstBaseAddr + dstOff) dstTag with
                          | Err _ =>
                              simp [h_use] at h_step
                          | Ok ap_write =>
                              refine ⟨ap_src_read, q, gq, resTarget, ap_target_read, ap_write,
                                ?_, ?_, ?_, ?_, ?_, ?_⟩
                              · rfl
                              · rfl
                              · exact h_resolve
                              · exact h_target_read
                              · exact h_use
                              · simpa [h_use] using h_step.symm

end DerefExisting

/-! ## Projected Existing Destination -/

structure DerefProjectedExistingCtx where
  src : mirlite.Place
  dst : mirlite.Place
  srcReg : Register
  dstReg : Register
  srcBaseLayout : LayoutTy
  innerLayout : LayoutTy
  dstBaseLayout : LayoutTy
  srcOff : Word
  dstOff : Word
  cs : CompilerState
  h_regs_below : PlaceMapRegsBelowNextReg cs
  h_instrs : CompilerEmpty cs
  h_src_lookup : BaseReady cs src.base srcReg srcBaseLayout
  h_dst_lookup : BaseReady cs dst.base dstReg dstBaseLayout
  h_src_path : layoutResolvePath srcBaseLayout src.path = some (srcOff, LayoutTy.PtrL innerLayout)
  h_dst_path : layoutResolvePath dstBaseLayout dst.path = some (dstOff, innerLayout)

namespace DerefProjectedExistingCtx

def stmt (ctx : DerefProjectedExistingCtx) : mirlite.Stmt :=
  mirlite.Stmt.Assgn (mirlite.LExpr.Place ctx.dst)
    (mirlite.RExpr.DrefOp ctx.src)

def resReg (ctx : DerefProjectedExistingCtx) : Register :=
  Register.R ctx.cs.nextReg

def srcTmpReg (ctx : DerefProjectedExistingCtx) : Register :=
  Register.R (ctx.cs.nextReg + 1)

def loadedPtrReg (ctx : DerefProjectedExistingCtx) : Register :=
  if ctx.srcOff = 0 then Register.R (ctx.cs.nextReg + 1) else Register.R (ctx.cs.nextReg + 2)

def dstTmpReg (ctx : DerefProjectedExistingCtx) : Register :=
  if ctx.srcOff = 0 then Register.R (ctx.cs.nextReg + 2) else Register.R (ctx.cs.nextReg + 3)

def innerTy (ctx : DerefProjectedExistingCtx) : TyVal :=
  layoutToTyVal ctx.innerLayout

def compiled (ctx : DerefProjectedExistingCtx) : oseair.Prog :=
  (compileStmt ctx.cs ctx.stmt).instrs

theorem instrs_nil (ctx : DerefProjectedExistingCtx) : ctx.cs.instrs = [] :=
  ctx.h_instrs

@[simp] theorem compiled_eq
  (ctx : DerefProjectedExistingCtx) :
  ctx.compiled =
    if ctx.srcOff = 0 then
      if ctx.dstOff = 0 then
        [oseair.Instr.Assgn (ctx.resReg) (oseair.Rhs.Alloc (ctx.innerTy)),
         oseair.Instr.Assgn (ctx.loadedPtrReg) (oseair.Rhs.Load TyVal.PTy ctx.srcReg),
         oseair.Instr.Memcpy (ctx.resReg) (ctx.loadedPtrReg) (ctx.innerTy),
         oseair.Instr.Memcpy ctx.dstReg (ctx.resReg) (ctx.innerTy)]
      else
        [oseair.Instr.Assgn (ctx.resReg) (oseair.Rhs.Alloc (ctx.innerTy)),
         oseair.Instr.Assgn (ctx.loadedPtrReg) (oseair.Rhs.Load TyVal.PTy ctx.srcReg),
         oseair.Instr.Memcpy (ctx.resReg) (ctx.loadedPtrReg) (ctx.innerTy),
         oseair.Instr.Assgn (ctx.dstTmpReg) (oseair.Rhs.MutBorOffset ctx.dstReg ctx.dstOff),
         oseair.Instr.Memcpy (ctx.dstTmpReg) (ctx.resReg) (ctx.innerTy),
         oseair.Instr.Die (ctx.dstTmpReg)]
    else
      if ctx.dstOff = 0 then
        [oseair.Instr.Assgn (ctx.resReg) (oseair.Rhs.Alloc (ctx.innerTy)),
         oseair.Instr.Assgn (ctx.srcTmpReg) (oseair.Rhs.BorOffset ctx.srcReg ctx.srcOff),
         oseair.Instr.Assgn (ctx.loadedPtrReg) (oseair.Rhs.Load TyVal.PTy (ctx.srcTmpReg)),
         oseair.Instr.Die (ctx.srcTmpReg),
         oseair.Instr.Memcpy (ctx.resReg) (ctx.loadedPtrReg) (ctx.innerTy),
         oseair.Instr.Memcpy ctx.dstReg (ctx.resReg) (ctx.innerTy)]
      else
        [oseair.Instr.Assgn (ctx.resReg) (oseair.Rhs.Alloc (ctx.innerTy)),
         oseair.Instr.Assgn (ctx.srcTmpReg) (oseair.Rhs.BorOffset ctx.srcReg ctx.srcOff),
         oseair.Instr.Assgn (ctx.loadedPtrReg) (oseair.Rhs.Load TyVal.PTy (ctx.srcTmpReg)),
         oseair.Instr.Die (ctx.srcTmpReg),
         oseair.Instr.Memcpy (ctx.resReg) (ctx.loadedPtrReg) (ctx.innerTy),
         oseair.Instr.Assgn (ctx.dstTmpReg) (oseair.Rhs.MutBorOffset ctx.dstReg ctx.dstOff),
         oseair.Instr.Memcpy (ctx.dstTmpReg) (ctx.resReg) (ctx.innerTy),
         oseair.Instr.Die (ctx.dstTmpReg)] := by
  let csAlloc : CompilerState :=
    { nextReg := ctx.cs.nextReg + 1,
      placeMap := ctx.cs.placeMap,
      instrs := ctx.cs.instrs ++
        [oseair.Instr.Assgn (ctx.resReg) (oseair.Rhs.Alloc (ctx.innerTy))] }
  have h_src_lookup_alloc :
      getPlaceInfo csAlloc ctx.src.base = some (ctx.srcReg, ctx.srcBaseLayout) := by
    simpa [csAlloc, getPlaceInfo] using ctx.h_src_lookup
  have h_src_place_layout :
      placeLayout? ctx.cs ctx.src = some (LayoutTy.PtrL ctx.innerLayout) := by
    unfold placeLayout?
    rw [ctx.h_src_lookup]
    simp [ctx.h_src_path]
  have h_layout :
      inferRExprLayout ctx.cs (mirlite.RExpr.DrefOp ctx.src) = ctx.innerLayout := by
    simp [inferRExprLayout, h_src_place_layout]
  by_cases h_src_off : ctx.srcOff = 0
  · let rhsCs : CompilerState :=
      { nextReg := ctx.cs.nextReg + 2,
        placeMap := ctx.cs.placeMap,
        instrs := ctx.cs.instrs ++
          [oseair.Instr.Assgn (ctx.resReg) (oseair.Rhs.Alloc (ctx.innerTy)),
           oseair.Instr.Assgn (ctx.loadedPtrReg) (oseair.Rhs.Load TyVal.PTy ctx.srcReg),
           oseair.Instr.Memcpy (ctx.resReg) (ctx.loadedPtrReg) (ctx.innerTy)] }
    have h_src_place :
        placeToReg csAlloc ctx.src mirlite.RefKind.Shared =
          { reg := ctx.srcReg,
            layout := LayoutTy.PtrL ctx.innerLayout,
            cleanup := [],
            cs := csAlloc } := by
      unfold placeToReg
      rw [h_src_lookup_alloc]
      simp [ctx.h_src_path, h_src_off, csAlloc]
    have h_rhs_to :
        compileRExprToFuel 1 csAlloc (ctx.resReg) (mirlite.RExpr.DrefOp ctx.src) = rhsCs := by
      simp [compileRExprToFuel, staticRExprData?]
      rw [h_src_place]
      simp [rhsCs, csAlloc, ctx.instrs_nil, DerefProjectedExistingCtx.loadedPtrReg,
        DerefProjectedExistingCtx.resReg, DerefProjectedExistingCtx.innerTy,
        freshReg, emit, layoutDeref?, h_src_off]
    have h_rhs :
        compileRExpr ctx.cs (mirlite.RExpr.DrefOp ctx.src) =
          { reg := ctx.resReg, layout := ctx.innerLayout, cs := rhsCs } := by
      simpa [compileRExpr, compileRExprFuel, mirlite.rExprFuel, h_layout, csAlloc, rhsCs,
        ctx.instrs_nil, DerefProjectedExistingCtx.resReg, DerefProjectedExistingCtx.loadedPtrReg,
        freshReg, emit, h_src_off] using h_rhs_to
    have h_dst_lookup_rhs :
        getPlaceInfo rhsCs ctx.dst.base = some (ctx.dstReg, ctx.dstBaseLayout) := by
      simpa [rhsCs, getPlaceInfo] using ctx.h_dst_lookup
    by_cases h_dst_off : ctx.dstOff = 0
    · have h_dst_place :
          placeToReg rhsCs ctx.dst mirlite.RefKind.Mut (some ctx.innerLayout) =
            { reg := ctx.dstReg,
              layout := ctx.innerLayout,
              cleanup := [],
              cs := rhsCs } := by
        unfold placeToReg
        rw [h_dst_lookup_rhs]
        simp [ctx.h_dst_path, rhsCs, h_dst_off]
      unfold DerefProjectedExistingCtx.compiled DerefProjectedExistingCtx.stmt compileStmt
      simp [h_rhs]
      rw [h_dst_place]
      simp [rhsCs, emit, cleanupInstrs, ctx.instrs_nil, h_src_off, h_dst_off,
        DerefProjectedExistingCtx.innerTy, DerefProjectedExistingCtx.loadedPtrReg,
        DerefProjectedExistingCtx.resReg]
    · have h_dst_place :
          placeToReg rhsCs ctx.dst mirlite.RefKind.Mut (some ctx.innerLayout) =
            { reg := ctx.dstTmpReg,
              layout := ctx.innerLayout,
              cleanup := [ctx.dstTmpReg],
              cs :=
                { nextReg := ctx.cs.nextReg + 3,
                  placeMap := ctx.cs.placeMap,
                  instrs := ctx.cs.instrs ++
                    [oseair.Instr.Assgn (ctx.resReg) (oseair.Rhs.Alloc (ctx.innerTy)),
                     oseair.Instr.Assgn (ctx.loadedPtrReg) (oseair.Rhs.Load TyVal.PTy ctx.srcReg),
                     oseair.Instr.Memcpy (ctx.resReg) (ctx.loadedPtrReg) (ctx.innerTy),
                     oseair.Instr.Assgn (ctx.dstTmpReg)
                       (oseair.Rhs.MutBorOffset ctx.dstReg ctx.dstOff)] } } := by
        unfold placeToReg
        rw [h_dst_lookup_rhs]
        simp [ctx.h_dst_path, rhsCs, h_dst_off, DerefProjectedExistingCtx.dstTmpReg,
          DerefProjectedExistingCtx.loadedPtrReg, freshReg, emit, h_src_off]
      unfold DerefProjectedExistingCtx.compiled DerefProjectedExistingCtx.stmt compileStmt
      simp [h_rhs]
      rw [h_dst_place]
      simp [emit, cleanupInstrs, ctx.instrs_nil, h_src_off, h_dst_off,
        DerefProjectedExistingCtx.innerTy, DerefProjectedExistingCtx.loadedPtrReg,
        DerefProjectedExistingCtx.resReg, DerefProjectedExistingCtx.dstTmpReg]
  · let rhsCs : CompilerState :=
      { nextReg := ctx.cs.nextReg + 3,
        placeMap := ctx.cs.placeMap,
        instrs := ctx.cs.instrs ++
          [oseair.Instr.Assgn (ctx.resReg) (oseair.Rhs.Alloc (ctx.innerTy)),
           oseair.Instr.Assgn (ctx.srcTmpReg) (oseair.Rhs.BorOffset ctx.srcReg ctx.srcOff),
           oseair.Instr.Assgn (ctx.loadedPtrReg) (oseair.Rhs.Load TyVal.PTy (ctx.srcTmpReg)),
           oseair.Instr.Die (ctx.srcTmpReg),
           oseair.Instr.Memcpy (ctx.resReg) (ctx.loadedPtrReg) (ctx.innerTy)] }
    have h_src_place :
        placeToReg csAlloc ctx.src mirlite.RefKind.Shared =
          { reg := ctx.srcTmpReg,
            layout := LayoutTy.PtrL ctx.innerLayout,
            cleanup := [ctx.srcTmpReg],
            cs :=
              { nextReg := ctx.cs.nextReg + 2,
                placeMap := ctx.cs.placeMap,
                instrs := ctx.cs.instrs ++
                  [oseair.Instr.Assgn (ctx.resReg) (oseair.Rhs.Alloc (ctx.innerTy)),
                   oseair.Instr.Assgn (ctx.srcTmpReg)
                     (oseair.Rhs.BorOffset ctx.srcReg ctx.srcOff)] } } := by
      unfold placeToReg
      rw [h_src_lookup_alloc]
      simp [ctx.h_src_path, h_src_off, csAlloc, DerefProjectedExistingCtx.srcTmpReg,
        freshReg, emit]
    have h_rhs_to :
        compileRExprToFuel 1 csAlloc (ctx.resReg) (mirlite.RExpr.DrefOp ctx.src) = rhsCs := by
      simp [compileRExprToFuel, staticRExprData?]
      rw [h_src_place]
      simp [rhsCs, ctx.instrs_nil, DerefProjectedExistingCtx.innerTy,
        DerefProjectedExistingCtx.srcTmpReg, DerefProjectedExistingCtx.loadedPtrReg,
        DerefProjectedExistingCtx.resReg, freshReg, emit, cleanupInstrs, layoutDeref?, h_src_off]
    have h_rhs :
        compileRExpr ctx.cs (mirlite.RExpr.DrefOp ctx.src) =
          { reg := ctx.resReg, layout := ctx.innerLayout, cs := rhsCs } := by
      simpa [compileRExpr, compileRExprFuel, mirlite.rExprFuel, h_layout, csAlloc, rhsCs,
        ctx.instrs_nil, DerefProjectedExistingCtx.srcTmpReg, DerefProjectedExistingCtx.loadedPtrReg,
        DerefProjectedExistingCtx.resReg, freshReg, emit, cleanupInstrs, h_src_off] using h_rhs_to
    have h_dst_lookup_rhs :
        getPlaceInfo rhsCs ctx.dst.base = some (ctx.dstReg, ctx.dstBaseLayout) := by
      simpa [rhsCs, getPlaceInfo] using ctx.h_dst_lookup
    by_cases h_dst_off : ctx.dstOff = 0
    · have h_dst_place :
          placeToReg rhsCs ctx.dst mirlite.RefKind.Mut (some ctx.innerLayout) =
            { reg := ctx.dstReg,
              layout := ctx.innerLayout,
              cleanup := [],
              cs := rhsCs } := by
        unfold placeToReg
        rw [h_dst_lookup_rhs]
        simp [ctx.h_dst_path, rhsCs, h_dst_off]
      unfold DerefProjectedExistingCtx.compiled DerefProjectedExistingCtx.stmt compileStmt
      simp [h_rhs]
      rw [h_dst_place]
      simp [rhsCs, emit, cleanupInstrs, ctx.instrs_nil, h_src_off, h_dst_off,
        DerefProjectedExistingCtx.innerTy, DerefProjectedExistingCtx.srcTmpReg,
        DerefProjectedExistingCtx.loadedPtrReg, DerefProjectedExistingCtx.resReg]
    · have h_dst_place :
          placeToReg rhsCs ctx.dst mirlite.RefKind.Mut (some ctx.innerLayout) =
            { reg := ctx.dstTmpReg,
              layout := ctx.innerLayout,
              cleanup := [ctx.dstTmpReg],
              cs :=
                { nextReg := ctx.cs.nextReg + 4,
                  placeMap := ctx.cs.placeMap,
                  instrs := ctx.cs.instrs ++
                    [oseair.Instr.Assgn (ctx.resReg) (oseair.Rhs.Alloc (ctx.innerTy)),
                     oseair.Instr.Assgn (ctx.srcTmpReg) (oseair.Rhs.BorOffset ctx.srcReg ctx.srcOff),
                     oseair.Instr.Assgn (ctx.loadedPtrReg) (oseair.Rhs.Load TyVal.PTy (ctx.srcTmpReg)),
                     oseair.Instr.Die (ctx.srcTmpReg),
                     oseair.Instr.Memcpy (ctx.resReg) (ctx.loadedPtrReg) (ctx.innerTy),
                     oseair.Instr.Assgn (ctx.dstTmpReg)
                       (oseair.Rhs.MutBorOffset ctx.dstReg ctx.dstOff)] } } := by
        unfold placeToReg
        rw [h_dst_lookup_rhs]
        simp [ctx.h_dst_path, rhsCs, h_dst_off, DerefProjectedExistingCtx.srcTmpReg,
          DerefProjectedExistingCtx.loadedPtrReg, DerefProjectedExistingCtx.dstTmpReg,
          freshReg, emit, h_src_off]
      unfold DerefProjectedExistingCtx.compiled DerefProjectedExistingCtx.stmt compileStmt
      simp [h_rhs]
      rw [h_dst_place]
      simp [emit, cleanupInstrs, ctx.instrs_nil, h_src_off, h_dst_off,
        DerefProjectedExistingCtx.innerTy, DerefProjectedExistingCtx.srcTmpReg,
        DerefProjectedExistingCtx.loadedPtrReg, DerefProjectedExistingCtx.resReg,
        DerefProjectedExistingCtx.dstTmpReg]

end DerefProjectedExistingCtx

namespace DerefProjectedExisting

abbrev stmt (ctx : DerefProjectedExistingCtx) : mirlite.Stmt :=
  DerefProjectedExistingCtx.stmt ctx

abbrev resReg (ctx : DerefProjectedExistingCtx) : Register :=
  DerefProjectedExistingCtx.resReg ctx

abbrev srcTmpReg (ctx : DerefProjectedExistingCtx) : Register :=
  DerefProjectedExistingCtx.srcTmpReg ctx

abbrev loadedPtrReg (ctx : DerefProjectedExistingCtx) : Register :=
  DerefProjectedExistingCtx.loadedPtrReg ctx

abbrev dstTmpReg (ctx : DerefProjectedExistingCtx) : Register :=
  DerefProjectedExistingCtx.dstTmpReg ctx

abbrev innerTy (ctx : DerefProjectedExistingCtx) : TyVal :=
  DerefProjectedExistingCtx.innerTy ctx

abbrev LocalSim
  (ctx : DerefProjectedExistingCtx)
  (ρa : AddrRenameMap) (ρt : TagRenameMap)
  (s_mir : mirlite.State) (s_osea : oseair.State)
  (ptr_sim : PtrSimPred := defaultPtrSim) : Prop :=
  StateSim ctx.cs.placeMap ρa ρt s_mir s_osea ptr_sim

theorem mirlite_step_inv
  (ctx : DerefProjectedExistingCtx)
  (s_mir s_mir_next : mirlite.State)
  (prog_mir : mirlite.Prog)
  (srcBaseAddr srcTag dstBaseAddr dstTag : Word)
  (h_src_env :
    s_mir.env.lookup ctx.src.base =
      some (srcBaseAddr, layoutToTyVal ctx.srcBaseLayout, srcTag))
  (h_dst_env :
    s_mir.env.lookup ctx.dst.base =
      some (dstBaseAddr, layoutToTyVal ctx.dstBaseLayout, dstTag))
  (h_start : StartsAt prog_mir s_mir.pc [stmt ctx])
  (h_step : mirlite.stepWith A_m s_mir prog_mir = mirlite.Result.Ok s_mir_next) :
  ∃ (ap_src_read : AccessPerms)
    (q : mirlite.Place) (gq : Tag) (targetRes : mirlite.PlaceRes)
    (ap_target_read ap_write : AccessPerms),
    sb_read s_mir.ap (srcBaseAddr + ctx.srcOff) srcTag = SBResult.Ok ap_src_read ∧
    s_mir.mem.find? (srcBaseAddr + ctx.srcOff) = some (mirlite.MemValue.PlaceTag q gq) ∧
    mirlite.resolveDirectPlace { s_mir with ap := ap_src_read } q =
      (mirlite.Result.Ok { s_mir with ap := ap_src_read }, targetRes) ∧
    sb_read ap_src_read targetRes.addr gq = SBResult.Ok ap_target_read ∧
    sb_use_mb ap_target_read (dstBaseAddr + ctx.dstOff) dstTag = SBResult.Ok ap_write ∧
    s_mir_next =
      { s_mir with
        ap := ap_write,
        mem := mirlite.writeWordSeq s_mir.mem (dstBaseAddr + ctx.dstOff)
          (mirlite.readWordSeq s_mir.mem targetRes.addr (typeSize targetRes.ty)),
        pc := s_mir.pc + 1 } := by
  simpa [stmt] using
    (DerefExisting.mirlite_step_inv_common
      (src := ctx.src)
      (dst := ctx.dst)
      (srcBaseLayout := ctx.srcBaseLayout)
      (innerLayout := ctx.innerLayout)
      (dstBaseLayout := ctx.dstBaseLayout)
      (srcOff := ctx.srcOff)
      (dstOff := ctx.dstOff)
      s_mir s_mir_next prog_mir srcBaseAddr srcTag dstBaseAddr dstTag
      h_src_env h_dst_env ctx.h_src_path ctx.h_dst_path h_start h_step)

theorem osea_rhs_direct_run_ok
  (ctx : DerefProjectedExistingCtx)
  (s_osea : oseair.State)
  (prog_osea : oseair.Prog)
  (srcBase_o srcTag_o : Word)
  (targetBase_o targetOff_o targetSize_o targetTag_o : Word)
  (allocBase_o : Word)
  (allocMem_o : oseair.Mem)
  (allocTag_o : Tag)
  (ap_alloc ap_load ap_memcpy_read ap_memcpy_write : AccessPerms)
  (h_src_off : ctx.srcOff = 0)
  (h_stmt0 :
    prog_osea.get? s_osea.pc =
      some (oseair.Instr.Assgn (resReg ctx) (oseair.Rhs.Alloc (innerTy ctx))))
  (h_stmt1 :
    prog_osea.get? (s_osea.pc + 1) =
      some (oseair.Instr.Assgn (loadedPtrReg ctx) (oseair.Rhs.Load TyVal.PTy ctx.srcReg)))
  (h_stmt2 :
    prog_osea.get? (s_osea.pc + 2) =
      some (oseair.Instr.Memcpy (resReg ctx) (loadedPtrReg ctx) (innerTy ctx)))
  (h_src_reg :
    s_osea.reg.lookup ctx.srcReg =
      some (TyVal.PTy, [oseair.Val.Ptr srcBase_o 0 (blockSize ctx.srcBaseLayout) srcTag_o]))
  (h_src_mem :
    oseair.readWordSeq s_osea.mem (srcBase_o + ctx.srcOff) 1 =
      [oseair.Val.Ptr targetBase_o targetOff_o targetSize_o targetTag_o])
  (h_alloc_pair :
    A_o.alloc s_osea.mem (blockSize ctx.innerLayout) = (allocBase_o, allocMem_o))
  (h_alloc_mMap_o : allocMem_o.mMap = s_osea.mem.mMap)
  (h_alloc : sb_own s_osea.ap allocBase_o = (SBResult.Ok ap_alloc, allocTag_o))
  (h_load :
    sb_read ap_alloc (srcBase_o + ctx.srcOff) srcTag_o = SBResult.Ok ap_load)
  (h_memcpy_read :
    sb_read ap_load (targetBase_o + targetOff_o) targetTag_o = SBResult.Ok ap_memcpy_read)
  (h_memcpy_write :
    sb_use_mb ap_memcpy_read allocBase_o allocTag_o = SBResult.Ok ap_memcpy_write)
  (h_src_fit :
    ctx.srcOff + blockSize (LayoutTy.PtrL ctx.innerLayout) ≤ blockSize ctx.srcBaseLayout)
  (h_target_fit : targetOff_o + blockSize ctx.innerLayout ≤ targetSize_o) :
  oseair.runNWith A_o 3 s_osea prog_osea =
    oseair.Result.Ok
      { s_osea with
        reg :=
          (s_osea.reg.insert (resReg ctx)
            (TyVal.PTy,
              [oseair.Val.Ptr allocBase_o 0 (blockSize ctx.innerLayout) allocTag_o])).insert
            (loadedPtrReg ctx)
            (TyVal.PTy,
              [oseair.Val.Ptr targetBase_o targetOff_o targetSize_o targetTag_o]),
        ap := ap_memcpy_write,
        mem := oseair.writeWordSeq allocMem_o allocBase_o
          (oseair.readWordSeq s_osea.mem (targetBase_o + targetOff_o) (blockSize ctx.innerLayout)),
        pc := s_osea.pc + 3 } := by
  rcases List.get?_eq_some_iff.mp h_stmt0 with ⟨h_pc0, h_get0⟩
  let s1 : oseair.State :=
    { s_osea with
      reg := s_osea.reg.insert (resReg ctx)
        (TyVal.PTy, [oseair.Val.Ptr allocBase_o 0 (blockSize ctx.innerLayout) allocTag_o]),
      ap := ap_alloc,
      mem := allocMem_o,
      pc := s_osea.pc + 1 }
  have h_step0 := oseair.step_Assgn_AllocWith A_o
    s_osea prog_osea (resReg ctx) (innerTy ctx) allocBase_o allocMem_o
    ap_alloc allocTag_o (blockSize ctx.innerLayout)
    h_pc0 h_get0 rfl h_alloc_pair h_alloc
  rcases List.get?_eq_some_iff.mp h_stmt1 with ⟨h_pc1, h_get1⟩
  let s2 : oseair.State :=
    { s1 with
      reg := s1.reg.insert (loadedPtrReg ctx)
        (TyVal.PTy, [oseair.Val.Ptr targetBase_o targetOff_o targetSize_o targetTag_o]),
      ap := ap_load,
      pc := s1.pc + 1 }
  have h_src_ne_res : ctx.srcReg ≠ resReg ctx := by
    intro h_eq
    exact (alloc_fresh_reg_of_ge (cs := ctx.cs) ctx.h_regs_below (Nat.le_refl _)
      ctx.src.base ctx.srcBaseLayout)
      (by simpa [resReg, h_eq] using ctx.h_src_lookup)
  have h_src_reg1 :
      s1.reg.lookup ctx.srcReg =
        some (TyVal.PTy, [oseair.Val.Ptr srcBase_o 0 (blockSize ctx.srcBaseLayout) srcTag_o]) := by
    simpa [s1, h_src_ne_res] using h_src_reg
  have h_ptr_nonempty : 0 < blockSize (LayoutTy.PtrL ctx.innerLayout) := by
    simp [blockSize, layoutSize]
  have h_src_off_lt : ctx.srcOff < blockSize ctx.srcBaseLayout := by
    exact Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right h_ptr_nonempty) h_src_fit
  have h_src_bound : srcBase_o + 0 < srcBase_o + blockSize ctx.srcBaseLayout := by
    simpa [h_src_off, Nat.zero_add] using Nat.add_lt_add_left h_src_off_lt srcBase_o
  have h_load' : sb_read ap_alloc (srcBase_o + 0) srcTag_o = SBResult.Ok ap_load := by
    simpa [h_src_off] using h_load
  have h_step1 := oseair.step_Assgn_LoadWith A_o
    s1 prog_osea (loadedPtrReg ctx) ctx.srcReg TyVal.PTy
    srcBase_o 0 (blockSize ctx.srcBaseLayout) srcTag_o TyVal.PTy ap_load
    h_pc1 h_get1 h_src_reg1 h_src_bound h_load'
  have h_s1_read_src :
      oseair.readWordSeq s1.mem (srcBase_o + 0) 1 =
        [oseair.Val.Ptr targetBase_o targetOff_o targetSize_o targetTag_o] := by
    calc
      oseair.readWordSeq s1.mem (srcBase_o + 0) 1
          = oseair.readWordSeq allocMem_o (srcBase_o + 0) 1 := by
              simp [s1]
      _ = oseair.readWordSeq s_osea.mem (srcBase_o + 0) 1 := by
          simpa using oseair_readWordSeq_eq_of_mMap_eq h_alloc_mMap_o (srcBase_o + 0) 1
      _ = [oseair.Val.Ptr targetBase_o targetOff_o targetSize_o targetTag_o] := by
          simpa [h_src_off] using h_src_mem
  have h_s1_read_src_ty :
      oseair.readWordSeq s1.mem (srcBase_o + 0) (typeSize TyVal.PTy) =
        [oseair.Val.Ptr targetBase_o targetOff_o targetSize_o targetTag_o] := by
    simpa using h_s1_read_src
  have h_step1' : oseair.stepWith A_o s1 prog_osea = oseair.Result.Ok s2 := by
    rw [h_s1_read_src_ty] at h_step1
    simpa [s1, s2] using h_step1
  rcases List.get?_eq_some_iff.mp h_stmt2 with ⟨h_pc2, h_get2⟩
  have h_res_ne_loaded : resReg ctx ≠ loadedPtrReg ctx := by
    intro h_eq
    unfold resReg loadedPtrReg DerefProjectedExistingCtx.resReg
      DerefProjectedExistingCtx.loadedPtrReg at h_eq
    have h_reg : Register.R ctx.cs.nextReg = Register.R (ctx.cs.nextReg + 1) := by
      simpa [h_src_off] using h_eq
    injection h_reg with h_nat
    exact (Nat.ne_of_lt (Nat.lt_succ_self ctx.cs.nextReg)) h_nat
  have h_res_reg :
      s2.reg.lookup (resReg ctx) =
        some (TyVal.PTy, [oseair.Val.Ptr allocBase_o 0 (blockSize ctx.innerLayout) allocTag_o]) := by
    simpa [s2, s1, h_res_ne_loaded] using
      show s1.reg.lookup (resReg ctx) =
        some (TyVal.PTy, [oseair.Val.Ptr allocBase_o 0 (blockSize ctx.innerLayout) allocTag_o]) by
          simp [s1]
  have h_loaded_reg :
      s2.reg.lookup (loadedPtrReg ctx) =
        some (TyVal.PTy, [oseair.Val.Ptr targetBase_o targetOff_o targetSize_o targetTag_o]) := by
    simp [s2]
  let s3 : oseair.State :=
    { s_osea with
      reg :=
        (s_osea.reg.insert (resReg ctx)
          (TyVal.PTy,
            [oseair.Val.Ptr allocBase_o 0 (blockSize ctx.innerLayout) allocTag_o])).insert
          (loadedPtrReg ctx)
          (TyVal.PTy,
            [oseair.Val.Ptr targetBase_o targetOff_o targetSize_o targetTag_o]),
      ap := ap_memcpy_write,
      mem := oseair.writeWordSeq allocMem_o allocBase_o
        (oseair.readWordSeq s_osea.mem (targetBase_o + targetOff_o) (blockSize ctx.innerLayout)),
      pc := s_osea.pc + 3 }
  have h_s2_read_target_ty :
      oseair.readWordSeq s2.mem (targetBase_o + targetOff_o) (typeSize (innerTy ctx)) =
        oseair.readWordSeq s_osea.mem (targetBase_o + targetOff_o) (typeSize (innerTy ctx)) := by
    simpa [innerTy, DerefProjectedExistingCtx.innerTy, s2, s1] using
      (oseair_readWordSeq_eq_of_mMap_eq h_alloc_mMap_o
        (targetBase_o + targetOff_o) (typeSize (innerTy ctx)))
  have h_step2 := oseair.step_MemcpyWith A_o
    s2 prog_osea (resReg ctx) (loadedPtrReg ctx) (innerTy ctx)
    allocBase_o 0 (blockSize ctx.innerLayout) allocTag_o
    targetBase_o targetOff_o targetSize_o targetTag_o
    ap_memcpy_read ap_memcpy_write
    h_pc2 h_get2 h_res_reg h_loaded_reg
    (by
      simpa [innerTy, DerefProjectedExistingCtx.innerTy,
        blockSize_eq_layoutSize, typeSize_layoutToTyVal])
    (by
      simpa [Nat.add_assoc, innerTy, DerefProjectedExistingCtx.innerTy,
        blockSize_eq_layoutSize, typeSize_layoutToTyVal] using
        Nat.add_le_add_left h_target_fit targetBase_o)
    h_memcpy_read h_memcpy_write
  have h_step2' : oseair.stepWith A_o s2 prog_osea = oseair.Result.Ok s3 := by
    rw [h_s2_read_target_ty] at h_step2
    simpa [s1, s2, s3, innerTy, DerefProjectedExistingCtx.innerTy,
      blockSize_eq_layoutSize, typeSize_layoutToTyVal] using h_step2
  rw [oseair.runNWith_succ]
  rw [h_step0]
  calc
    (match oseair.stepWith A_o s1 prog_osea with
      | oseair.Result.Ok state' =>
          match oseair.stepWith A_o state' prog_osea with
          | oseair.Result.Ok state' => oseair.Result.Ok state'
          | oseair.Result.Err msg => oseair.Result.Err msg
      | oseair.Result.Err msg => oseair.Result.Err msg)
        = (match oseair.Result.Ok s2 with
          | oseair.Result.Ok state' =>
              match oseair.stepWith A_o state' prog_osea with
              | oseair.Result.Ok state' => oseair.Result.Ok state'
              | oseair.Result.Err msg => oseair.Result.Err msg
          | oseair.Result.Err msg => oseair.Result.Err msg) := by
            rw [h_step1']
    _ = (match oseair.stepWith A_o s2 prog_osea with
          | oseair.Result.Ok state' => oseair.Result.Ok state'
          | oseair.Result.Err msg => oseair.Result.Err msg) := by
            rfl
    _ = (match oseair.Result.Ok s3 with
          | oseair.Result.Ok state' => oseair.Result.Ok state'
          | oseair.Result.Err msg => oseair.Result.Err msg) := by
            rw [h_step2']
    _ = _ := by
            rfl

theorem osea_rhs_projected_run_ok
  (ctx : DerefProjectedExistingCtx)
  (s_osea : oseair.State)
  (prog_osea : oseair.Prog)
  (srcBase_o srcTag_o : Word)
  (srcTempTag_o : Tag)
  (targetBase_o targetOff_o targetSize_o targetTag_o : Word)
  (allocBase_o : Word)
  (allocMem_o : oseair.Mem)
  (allocTag_o : Tag)
  (ap_alloc ap_src_ref ap_load ap_load_final ap_memcpy_read ap_memcpy_write : AccessPerms)
  (h_src_off : ctx.srcOff ≠ 0)
  (h_stmt0 :
    prog_osea.get? s_osea.pc =
      some (oseair.Instr.Assgn (resReg ctx) (oseair.Rhs.Alloc (innerTy ctx))))
  (h_stmt1 :
    prog_osea.get? (s_osea.pc + 1) =
      some (oseair.Instr.Assgn (srcTmpReg ctx) (oseair.Rhs.BorOffset ctx.srcReg ctx.srcOff)))
  (h_stmt2 :
    prog_osea.get? (s_osea.pc + 2) =
      some (oseair.Instr.Assgn (loadedPtrReg ctx) (oseair.Rhs.Load TyVal.PTy (srcTmpReg ctx))))
  (h_stmt3 :
    prog_osea.get? (s_osea.pc + 3) =
      some (oseair.Instr.Die (srcTmpReg ctx)))
  (h_stmt4 :
    prog_osea.get? (s_osea.pc + 4) =
      some (oseair.Instr.Memcpy (resReg ctx) (loadedPtrReg ctx) (innerTy ctx)))
  (h_src_reg :
    s_osea.reg.lookup ctx.srcReg =
      some (TyVal.PTy, [oseair.Val.Ptr srcBase_o 0 (blockSize ctx.srcBaseLayout) srcTag_o]))
  (h_src_mem :
    oseair.readWordSeq s_osea.mem (srcBase_o + ctx.srcOff) 1 =
      [oseair.Val.Ptr targetBase_o targetOff_o targetSize_o targetTag_o])
  (h_alloc_pair :
    A_o.alloc s_osea.mem (blockSize ctx.innerLayout) = (allocBase_o, allocMem_o))
  (h_alloc_mMap_o : allocMem_o.mMap = s_osea.mem.mMap)
  (h_alloc : sb_own s_osea.ap allocBase_o = (SBResult.Ok ap_alloc, allocTag_o))
  (h_ref :
    sb_ref ap_alloc (srcBase_o + ctx.srcOff) srcTag_o RefOpKind.Shared =
      (SBResult.Ok ap_src_ref, srcTempTag_o))
  (h_load :
    sb_read ap_src_ref (srcBase_o + ctx.srcOff) srcTempTag_o = SBResult.Ok ap_load)
  (h_die :
    sb_die ap_load (srcBase_o + ctx.srcOff) srcTempTag_o = SBResult.Ok ap_load_final)
  (h_memcpy_read :
    sb_read ap_load_final (targetBase_o + targetOff_o) targetTag_o = SBResult.Ok ap_memcpy_read)
  (h_memcpy_write :
    sb_use_mb ap_memcpy_read allocBase_o allocTag_o = SBResult.Ok ap_memcpy_write)
  (h_src_fit :
    ctx.srcOff + blockSize (LayoutTy.PtrL ctx.innerLayout) ≤ blockSize ctx.srcBaseLayout)
  (h_target_fit : targetOff_o + blockSize ctx.innerLayout ≤ targetSize_o) :
  oseair.runNWith A_o 5 s_osea prog_osea =
    oseair.Result.Ok
      { s_osea with
        reg :=
          ((s_osea.reg.insert (resReg ctx)
            (TyVal.PTy,
              [oseair.Val.Ptr allocBase_o 0 (blockSize ctx.innerLayout) allocTag_o])).insert
            (srcTmpReg ctx)
            (TyVal.PTy,
              [oseair.Val.Ptr srcBase_o ctx.srcOff (blockSize ctx.srcBaseLayout) srcTempTag_o])).insert
            (loadedPtrReg ctx)
            (TyVal.PTy,
              [oseair.Val.Ptr targetBase_o targetOff_o targetSize_o targetTag_o]),
        ap := ap_memcpy_write,
        mem := oseair.writeWordSeq allocMem_o allocBase_o
          (oseair.readWordSeq s_osea.mem (targetBase_o + targetOff_o) (blockSize ctx.innerLayout)),
        pc := s_osea.pc + 5 } := by
  rcases List.get?_eq_some_iff.mp h_stmt0 with ⟨h_pc0, h_get0⟩
  let s1 : oseair.State :=
    { s_osea with
      reg := s_osea.reg.insert (resReg ctx)
        (TyVal.PTy, [oseair.Val.Ptr allocBase_o 0 (blockSize ctx.innerLayout) allocTag_o]),
      ap := ap_alloc,
      mem := allocMem_o,
      pc := s_osea.pc + 1 }
  have h_step0 := oseair.step_Assgn_AllocWith A_o
    s_osea prog_osea (resReg ctx) (innerTy ctx) allocBase_o allocMem_o
    ap_alloc allocTag_o (blockSize ctx.innerLayout)
    h_pc0 h_get0 rfl h_alloc_pair h_alloc
  rcases List.get?_eq_some_iff.mp h_stmt1 with ⟨h_pc1, h_get1⟩
  let s2 : oseair.State :=
    { s_osea with
      reg :=
        (s_osea.reg.insert (resReg ctx)
          (TyVal.PTy, [oseair.Val.Ptr allocBase_o 0 (blockSize ctx.innerLayout) allocTag_o])).insert
          (srcTmpReg ctx)
          (TyVal.PTy, [oseair.Val.Ptr srcBase_o ctx.srcOff (blockSize ctx.srcBaseLayout) srcTempTag_o]),
      ap := ap_src_ref,
      mem := allocMem_o,
      pc := s_osea.pc + 2 }
  have h_src_ne_res : ctx.srcReg ≠ resReg ctx := by
    intro h_eq
    exact (alloc_fresh_reg_of_ge (cs := ctx.cs) ctx.h_regs_below (Nat.le_refl _)
      ctx.src.base ctx.srcBaseLayout)
      (by simpa [resReg, h_eq] using ctx.h_src_lookup)
  have h_src_reg1 :
      s1.reg.lookup ctx.srcReg =
        some (TyVal.PTy, [oseair.Val.Ptr srcBase_o 0 (blockSize ctx.srcBaseLayout) srcTag_o]) := by
    simpa [s1, h_src_ne_res] using h_src_reg
  have h_ptr_nonempty : 0 < blockSize (LayoutTy.PtrL ctx.innerLayout) := by
    simp [blockSize, layoutSize]
  have h_src_off_lt : ctx.srcOff < blockSize ctx.srcBaseLayout := by
    exact Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right h_ptr_nonempty) h_src_fit
  have h_src_bound : srcBase_o + ctx.srcOff < srcBase_o + blockSize ctx.srcBaseLayout := by
    simpa [Nat.zero_add] using Nat.add_lt_add_left h_src_off_lt srcBase_o
  have h_step1 := oseair.step_Assgn_BorOffsetWith A_o
    s1 prog_osea (srcTmpReg ctx) ctx.srcReg ctx.srcOff
    srcBase_o 0 (blockSize ctx.srcBaseLayout) srcTag_o
    ap_src_ref srcTempTag_o
    h_pc1 h_get1 h_src_reg1
    (by simpa [Nat.zero_add] using h_src_bound) h_ref
  have h_step1' : oseair.stepWith A_o s1 prog_osea = oseair.Result.Ok s2 := by
    simpa [s1, s2] using h_step1
  rcases List.get?_eq_some_iff.mp h_stmt2 with ⟨h_pc2, h_get2⟩
  let s3 : oseair.State :=
    { s_osea with
      reg :=
        ((s_osea.reg.insert (resReg ctx)
          (TyVal.PTy, [oseair.Val.Ptr allocBase_o 0 (blockSize ctx.innerLayout) allocTag_o])).insert
          (srcTmpReg ctx)
          (TyVal.PTy, [oseair.Val.Ptr srcBase_o ctx.srcOff (blockSize ctx.srcBaseLayout) srcTempTag_o])).insert
          (loadedPtrReg ctx)
          (TyVal.PTy, [oseair.Val.Ptr targetBase_o targetOff_o targetSize_o targetTag_o]),
      ap := ap_load,
      mem := allocMem_o,
      pc := s_osea.pc + 3 }
  have h_tmp_ne_loaded : srcTmpReg ctx ≠ loadedPtrReg ctx := by
    intro h_eq
    unfold srcTmpReg loadedPtrReg DerefProjectedExistingCtx.srcTmpReg
      DerefProjectedExistingCtx.loadedPtrReg at h_eq
    by_cases h_zero : ctx.srcOff = 0
    · simp [h_zero] at h_eq
      exact h_src_off h_zero
    · have h_reg : Register.R (ctx.cs.nextReg + 1) = Register.R (ctx.cs.nextReg + 2) := by
        simpa [h_zero] using h_eq
      injection h_reg with h_nat
      exact (Nat.ne_of_lt (Nat.lt_succ_self (ctx.cs.nextReg + 1))) h_nat
  have h_tmp_reg :
      s2.reg.lookup (srcTmpReg ctx) =
        some (TyVal.PTy, [oseair.Val.Ptr srcBase_o ctx.srcOff (blockSize ctx.srcBaseLayout) srcTempTag_o]) := by
    simp [s2]
  have h_s2_read_src :
      oseair.readWordSeq s2.mem (srcBase_o + ctx.srcOff) 1 =
        [oseair.Val.Ptr targetBase_o targetOff_o targetSize_o targetTag_o] := by
    calc
      oseair.readWordSeq s2.mem (srcBase_o + ctx.srcOff) 1
          = oseair.readWordSeq allocMem_o (srcBase_o + ctx.srcOff) 1 := by
              simp [s2]
      _ = oseair.readWordSeq s_osea.mem (srcBase_o + ctx.srcOff) 1 := by
          simpa using oseair_readWordSeq_eq_of_mMap_eq h_alloc_mMap_o (srcBase_o + ctx.srcOff) 1
      _ = [oseair.Val.Ptr targetBase_o targetOff_o targetSize_o targetTag_o] := h_src_mem
  have h_step2 := oseair.step_Assgn_LoadWith A_o
    s2 prog_osea (loadedPtrReg ctx) (srcTmpReg ctx) TyVal.PTy
    srcBase_o ctx.srcOff (blockSize ctx.srcBaseLayout) srcTempTag_o TyVal.PTy ap_load
    h_pc2 h_get2 h_tmp_reg h_src_bound h_load
  have h_s2_read_src_ty :
      oseair.readWordSeq allocMem_o (srcBase_o + ctx.srcOff) (typeSize TyVal.PTy) =
        [oseair.Val.Ptr targetBase_o targetOff_o targetSize_o targetTag_o] := by
    simpa [s2] using h_s2_read_src
  have h_step2' : oseair.stepWith A_o s2 prog_osea = oseair.Result.Ok s3 := by
    rw [h_s2_read_src_ty] at h_step2
    simpa [s2, s3] using h_step2
  rcases List.get?_eq_some_iff.mp h_stmt3 with ⟨h_pc3, h_get3⟩
  let s4 : oseair.State :=
    { s_osea with
      reg :=
        ((s_osea.reg.insert (resReg ctx)
          (TyVal.PTy, [oseair.Val.Ptr allocBase_o 0 (blockSize ctx.innerLayout) allocTag_o])).insert
          (srcTmpReg ctx)
          (TyVal.PTy, [oseair.Val.Ptr srcBase_o ctx.srcOff (blockSize ctx.srcBaseLayout) srcTempTag_o])).insert
          (loadedPtrReg ctx)
          (TyVal.PTy, [oseair.Val.Ptr targetBase_o targetOff_o targetSize_o targetTag_o]),
      ap := ap_load_final,
      mem := allocMem_o,
      pc := s_osea.pc + 4 }
  have h_tmp_reg3 :
      s3.reg.lookup (srcTmpReg ctx) =
        some (TyVal.PTy, [oseair.Val.Ptr srcBase_o ctx.srcOff (blockSize ctx.srcBaseLayout) srcTempTag_o]) := by
    simpa [s3, s2, h_tmp_ne_loaded] using h_tmp_reg
  have h_step3 := oseair.step_DieWith A_o
    s3 prog_osea (srcTmpReg ctx)
    srcBase_o ctx.srcOff (blockSize ctx.srcBaseLayout) srcTempTag_o ap_load_final
    h_pc3 h_get3 h_tmp_reg3 h_die
  have h_step3' : oseair.stepWith A_o s3 prog_osea = oseair.Result.Ok s4 := by
    simpa [s3, s4] using h_step3
  rcases List.get?_eq_some_iff.mp h_stmt4 with ⟨h_pc4, h_get4⟩
  have h_res_ne_tmp : resReg ctx ≠ srcTmpReg ctx := by
    intro h_eq
    unfold resReg srcTmpReg DerefProjectedExistingCtx.resReg
      DerefProjectedExistingCtx.srcTmpReg at h_eq
    have h_reg : Register.R ctx.cs.nextReg = Register.R (ctx.cs.nextReg + 1) := h_eq
    injection h_reg with h_nat
    exact (Nat.ne_of_lt (Nat.lt_succ_self ctx.cs.nextReg)) h_nat
  have h_res_ne_loaded : resReg ctx ≠ loadedPtrReg ctx := by
    intro h_eq
    unfold resReg loadedPtrReg DerefProjectedExistingCtx.resReg
      DerefProjectedExistingCtx.loadedPtrReg at h_eq
    by_cases h_zero : ctx.srcOff = 0
    · simp [h_zero] at h_eq
    · have h_reg : Register.R ctx.cs.nextReg = Register.R (ctx.cs.nextReg + 2) := by
        simpa [h_zero] using h_eq
      injection h_reg with h_nat
      have h_ne : ctx.cs.nextReg ≠ ctx.cs.nextReg + 2 :=
        Nat.ne_of_lt (Nat.lt_succ_of_lt (Nat.lt_succ_self ctx.cs.nextReg))
      exact h_ne h_nat
  have h_res_reg :
      s4.reg.lookup (resReg ctx) =
        some (TyVal.PTy, [oseair.Val.Ptr allocBase_o 0 (blockSize ctx.innerLayout) allocTag_o]) := by
    simp [s4, h_res_ne_tmp, h_res_ne_loaded]
  have h_loaded_reg :
      s4.reg.lookup (loadedPtrReg ctx) =
        some (TyVal.PTy, [oseair.Val.Ptr targetBase_o targetOff_o targetSize_o targetTag_o]) := by
    simp [s4]
  have h_step4 := oseair.step_MemcpyWith A_o
    s4 prog_osea (resReg ctx) (loadedPtrReg ctx) (innerTy ctx)
    allocBase_o 0 (blockSize ctx.innerLayout) allocTag_o
    targetBase_o targetOff_o targetSize_o targetTag_o
    ap_memcpy_read ap_memcpy_write
    h_pc4 h_get4 h_res_reg h_loaded_reg
    (by simp [innerTy, DerefProjectedExistingCtx.innerTy, blockSize])
    (by
      simpa [Nat.add_assoc, innerTy, DerefProjectedExistingCtx.innerTy,
        blockSize_eq_layoutSize, typeSize_layoutToTyVal] using
        Nat.add_le_add_left h_target_fit targetBase_o)
    h_memcpy_read h_memcpy_write
  have h_run_tail :
      (match oseair.stepWith A_o s1 prog_osea with
      | oseair.Result.Ok state' =>
          match oseair.stepWith A_o state' prog_osea with
          | oseair.Result.Ok state' =>
              match oseair.stepWith A_o state' prog_osea with
              | oseair.Result.Ok state' =>
                  match oseair.stepWith A_o state' prog_osea with
                  | oseair.Result.Ok state' => oseair.Result.Ok state'
                  | oseair.Result.Err msg => oseair.Result.Err msg
              | oseair.Result.Err msg => oseair.Result.Err msg
          | oseair.Result.Err msg => oseair.Result.Err msg
      | oseair.Result.Err msg => oseair.Result.Err msg) =
        oseair.Result.Ok
          { s_osea with
            reg :=
              ((s_osea.reg.insert (resReg ctx)
                (TyVal.PTy,
                  [oseair.Val.Ptr allocBase_o 0 (blockSize ctx.innerLayout) allocTag_o])).insert
                (srcTmpReg ctx)
                (TyVal.PTy,
                  [oseair.Val.Ptr srcBase_o ctx.srcOff (blockSize ctx.srcBaseLayout) srcTempTag_o])).insert
                (loadedPtrReg ctx)
                (TyVal.PTy,
                  [oseair.Val.Ptr targetBase_o targetOff_o targetSize_o targetTag_o]),
            ap := ap_memcpy_write,
            mem := oseair.writeWordSeq allocMem_o allocBase_o
              (oseair.readWordSeq s_osea.mem (targetBase_o + targetOff_o) (blockSize ctx.innerLayout)),
            pc := s_osea.pc + 5 } := by
    calc
      (match oseair.stepWith A_o s1 prog_osea with
      | oseair.Result.Ok state' =>
          match oseair.stepWith A_o state' prog_osea with
          | oseair.Result.Ok state' =>
              match oseair.stepWith A_o state' prog_osea with
              | oseair.Result.Ok state' =>
                  match oseair.stepWith A_o state' prog_osea with
                  | oseair.Result.Ok state' => oseair.Result.Ok state'
                  | oseair.Result.Err msg => oseair.Result.Err msg
              | oseair.Result.Err msg => oseair.Result.Err msg
          | oseair.Result.Err msg => oseair.Result.Err msg
      | oseair.Result.Err msg => oseair.Result.Err msg)
          = (match oseair.stepWith A_o s2 prog_osea with
            | oseair.Result.Ok state' =>
                match oseair.stepWith A_o state' prog_osea with
                | oseair.Result.Ok state' =>
                    match oseair.stepWith A_o state' prog_osea with
                    | oseair.Result.Ok state' => oseair.Result.Ok state'
                    | oseair.Result.Err msg => oseair.Result.Err msg
                | oseair.Result.Err msg => oseair.Result.Err msg
            | oseair.Result.Err msg => oseair.Result.Err msg) := by
              rw [h_step1']
      _ = (match oseair.stepWith A_o s3 prog_osea with
            | oseair.Result.Ok state' =>
                match oseair.stepWith A_o state' prog_osea with
                | oseair.Result.Ok state' => oseair.Result.Ok state'
                | oseair.Result.Err msg => oseair.Result.Err msg
            | oseair.Result.Err msg => oseair.Result.Err msg) := by
              rw [h_step2']
      _ = (match oseair.stepWith A_o s4 prog_osea with
            | oseair.Result.Ok state' => oseair.Result.Ok state'
            | oseair.Result.Err msg => oseair.Result.Err msg) := by
              rw [h_step3']
      _ = _ := by
            have h_read_eq :
                oseair.readWordSeq allocMem_o (targetBase_o + targetOff_o) (layoutSize ctx.innerLayout) =
                  oseair.readWordSeq s_osea.mem (targetBase_o + targetOff_o) (layoutSize ctx.innerLayout) := by
              simpa [blockSize_eq_layoutSize] using
                (oseair_readWordSeq_eq_of_mMap_eq h_alloc_mMap_o
                  (targetBase_o + targetOff_o) (blockSize ctx.innerLayout))
            rw [h_step4]
            simp [s4, innerTy, DerefProjectedExistingCtx.innerTy, blockSize_eq_layoutSize,
              typeSize_layoutToTyVal]
            exact congrArg (oseair.writeWordSeq allocMem_o allocBase_o) h_read_eq
  have h_run4 :
      oseair.runNWith A_o 4 s1 prog_osea =
        oseair.Result.Ok
          { s_osea with
            reg :=
              ((s_osea.reg.insert (resReg ctx)
                (TyVal.PTy,
                  [oseair.Val.Ptr allocBase_o 0 (blockSize ctx.innerLayout) allocTag_o])).insert
                (srcTmpReg ctx)
                (TyVal.PTy,
                  [oseair.Val.Ptr srcBase_o ctx.srcOff (blockSize ctx.srcBaseLayout) srcTempTag_o])).insert
                (loadedPtrReg ctx)
                (TyVal.PTy,
                  [oseair.Val.Ptr targetBase_o targetOff_o targetSize_o targetTag_o]),
            ap := ap_memcpy_write,
            mem := oseair.writeWordSeq allocMem_o allocBase_o
              (oseair.readWordSeq s_osea.mem (targetBase_o + targetOff_o) (blockSize ctx.innerLayout)),
            pc := s_osea.pc + 5 } := by
    simpa [s1, oseair.runNWith_succ, oseair.runNWith_zero] using h_run_tail
  rw [oseair.runNWith_succ]
  rw [h_step0]
  exact h_run4

theorem starts_rhs_direct_instrs
  (ctx : DerefProjectedExistingCtx)
  {prog_osea : oseair.Prog}
  {pc : Nat}
  (h_start : StartsAt prog_osea pc (DerefProjectedExistingCtx.compiled ctx))
  (h_src_off : ctx.srcOff = 0) :
  prog_osea.get? pc =
      some (oseair.Instr.Assgn (resReg ctx) (oseair.Rhs.Alloc (innerTy ctx))) ∧
    prog_osea.get? (pc + 1) =
      some (oseair.Instr.Assgn (loadedPtrReg ctx)
        (oseair.Rhs.Load TyVal.PTy ctx.srcReg)) ∧
    prog_osea.get? (pc + 2) =
      some (oseair.Instr.Memcpy (resReg ctx) (loadedPtrReg ctx) (innerTy ctx)) := by
  by_cases h_dst_off : ctx.dstOff = 0
  · have h_start_full :
        StartsAt prog_osea pc
          [oseair.Instr.Assgn (resReg ctx) (oseair.Rhs.Alloc (innerTy ctx)),
           oseair.Instr.Assgn (loadedPtrReg ctx) (oseair.Rhs.Load TyVal.PTy ctx.srcReg),
           oseair.Instr.Memcpy (resReg ctx) (loadedPtrReg ctx) (innerTy ctx),
           oseair.Instr.Memcpy ctx.dstReg (resReg ctx) (innerTy ctx)] := by
      simpa [DerefProjectedExistingCtx.compiled_eq, h_src_off, h_dst_off] using h_start
    have h_start1 := StartsAt.tail h_start_full
    have h_start2 := StartsAt.tail h_start1
    exact ⟨by
      have h_head := h_start_full 0 (by decide : 0 < 4)
      simpa [Nat.zero_add, List.get?] using h_head.symm,
      by
        have h_head := h_start1 0 (by decide : 0 < 3)
        simpa [Nat.zero_add, List.get?] using h_head.symm,
      by
        have h_head := h_start2 0 (by decide : 0 < 2)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, List.get?] using h_head.symm⟩
  · have h_start_full :
        StartsAt prog_osea pc
          [oseair.Instr.Assgn (resReg ctx) (oseair.Rhs.Alloc (innerTy ctx)),
           oseair.Instr.Assgn (loadedPtrReg ctx) (oseair.Rhs.Load TyVal.PTy ctx.srcReg),
           oseair.Instr.Memcpy (resReg ctx) (loadedPtrReg ctx) (innerTy ctx),
           oseair.Instr.Assgn (dstTmpReg ctx) (oseair.Rhs.MutBorOffset ctx.dstReg ctx.dstOff),
           oseair.Instr.Memcpy (dstTmpReg ctx) (resReg ctx) (innerTy ctx),
           oseair.Instr.Die (dstTmpReg ctx)] := by
      simpa [DerefProjectedExistingCtx.compiled_eq, h_src_off, h_dst_off] using h_start
    have h_start1 := StartsAt.tail h_start_full
    have h_start2 := StartsAt.tail h_start1
    exact ⟨by
      have h_head := h_start_full 0 (by decide : 0 < 6)
      simpa [Nat.zero_add, List.get?] using h_head.symm,
      by
        have h_head := h_start1 0 (by decide : 0 < 5)
        simpa [Nat.zero_add, List.get?] using h_head.symm,
      by
        have h_head := h_start2 0 (by decide : 0 < 4)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, List.get?] using h_head.symm⟩

theorem starts_rhs_projected_instrs
  (ctx : DerefProjectedExistingCtx)
  {prog_osea : oseair.Prog}
  {pc : Nat}
  (h_start : StartsAt prog_osea pc (DerefProjectedExistingCtx.compiled ctx))
  (h_src_off : ctx.srcOff ≠ 0) :
  prog_osea.get? pc =
      some (oseair.Instr.Assgn (resReg ctx) (oseair.Rhs.Alloc (innerTy ctx))) ∧
    prog_osea.get? (pc + 1) =
      some (oseair.Instr.Assgn (srcTmpReg ctx)
        (oseair.Rhs.BorOffset ctx.srcReg ctx.srcOff)) ∧
    prog_osea.get? (pc + 2) =
      some (oseair.Instr.Assgn (loadedPtrReg ctx)
        (oseair.Rhs.Load TyVal.PTy (srcTmpReg ctx))) ∧
    prog_osea.get? (pc + 3) =
      some (oseair.Instr.Die (srcTmpReg ctx)) ∧
    prog_osea.get? (pc + 4) =
      some (oseair.Instr.Memcpy (resReg ctx) (loadedPtrReg ctx) (innerTy ctx)) := by
  by_cases h_dst_off : ctx.dstOff = 0
  · have h_start_full :
        StartsAt prog_osea pc
          [oseair.Instr.Assgn (resReg ctx) (oseair.Rhs.Alloc (innerTy ctx)),
           oseair.Instr.Assgn (srcTmpReg ctx) (oseair.Rhs.BorOffset ctx.srcReg ctx.srcOff),
           oseair.Instr.Assgn (loadedPtrReg ctx)
             (oseair.Rhs.Load TyVal.PTy (srcTmpReg ctx)),
           oseair.Instr.Die (srcTmpReg ctx),
           oseair.Instr.Memcpy (resReg ctx) (loadedPtrReg ctx) (innerTy ctx),
           oseair.Instr.Memcpy ctx.dstReg (resReg ctx) (innerTy ctx)] := by
      simpa [DerefProjectedExistingCtx.compiled_eq, h_src_off, h_dst_off] using h_start
    have h_start1 := StartsAt.tail h_start_full
    have h_start2 := StartsAt.tail h_start1
    have h_start3 := StartsAt.tail h_start2
    have h_start4 := StartsAt.tail h_start3
    exact ⟨by
      have h_head := h_start_full 0 (by decide : 0 < 6)
      simpa [Nat.zero_add, List.get?] using h_head.symm,
      by
        have h_head := h_start1 0 (by decide : 0 < 5)
        simpa [Nat.zero_add, List.get?] using h_head.symm,
      by
        have h_head := h_start2 0 (by decide : 0 < 4)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, List.get?] using h_head.symm,
      by
        have h_head := h_start3 0 (by decide : 0 < 3)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, List.get?] using h_head.symm,
      by
        have h_head := h_start4 0 (by decide : 0 < 2)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, List.get?] using h_head.symm⟩
  · have h_start_full :
        StartsAt prog_osea pc
          [oseair.Instr.Assgn (resReg ctx) (oseair.Rhs.Alloc (innerTy ctx)),
           oseair.Instr.Assgn (srcTmpReg ctx) (oseair.Rhs.BorOffset ctx.srcReg ctx.srcOff),
           oseair.Instr.Assgn (loadedPtrReg ctx)
             (oseair.Rhs.Load TyVal.PTy (srcTmpReg ctx)),
           oseair.Instr.Die (srcTmpReg ctx),
           oseair.Instr.Memcpy (resReg ctx) (loadedPtrReg ctx) (innerTy ctx),
           oseair.Instr.Assgn (dstTmpReg ctx) (oseair.Rhs.MutBorOffset ctx.dstReg ctx.dstOff),
           oseair.Instr.Memcpy (dstTmpReg ctx) (resReg ctx) (innerTy ctx),
           oseair.Instr.Die (dstTmpReg ctx)] := by
      simpa [DerefProjectedExistingCtx.compiled_eq, h_src_off, h_dst_off] using h_start
    have h_start1 := StartsAt.tail h_start_full
    have h_start2 := StartsAt.tail h_start1
    have h_start3 := StartsAt.tail h_start2
    have h_start4 := StartsAt.tail h_start3
    exact ⟨by
      have h_head := h_start_full 0 (by decide : 0 < 8)
      simpa [Nat.zero_add, List.get?] using h_head.symm,
      by
        have h_head := h_start1 0 (by decide : 0 < 7)
        simpa [Nat.zero_add, List.get?] using h_head.symm,
      by
        have h_head := h_start2 0 (by decide : 0 < 6)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, List.get?] using h_head.symm,
      by
        have h_head := h_start3 0 (by decide : 0 < 5)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, List.get?] using h_head.symm,
      by
        have h_head := h_start4 0 (by decide : 0 < 4)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, List.get?] using h_head.symm⟩

theorem starts_rhs_direct_suffix_direct
  (ctx : DerefProjectedExistingCtx)
  {prog_osea : oseair.Prog}
  {pc : Nat}
  (h_start : StartsAt prog_osea pc (DerefProjectedExistingCtx.compiled ctx))
  (h_src_off : ctx.srcOff = 0)
  (h_dst_off : ctx.dstOff = 0) :
  StartsAt prog_osea (pc + 3)
    [oseair.Instr.Memcpy ctx.dstReg (resReg ctx) (innerTy ctx)] := by
  have h_start_full :
      StartsAt prog_osea pc
        [oseair.Instr.Assgn (resReg ctx) (oseair.Rhs.Alloc (innerTy ctx)),
         oseair.Instr.Assgn (loadedPtrReg ctx) (oseair.Rhs.Load TyVal.PTy ctx.srcReg),
         oseair.Instr.Memcpy (resReg ctx) (loadedPtrReg ctx) (innerTy ctx),
         oseair.Instr.Memcpy ctx.dstReg (resReg ctx) (innerTy ctx)] := by
    simpa [DerefProjectedExistingCtx.compiled_eq, h_src_off, h_dst_off] using h_start
  simpa using (StartsAt.tail (StartsAt.tail (StartsAt.tail h_start_full)))

theorem starts_rhs_direct_suffix_projected
  (ctx : DerefProjectedExistingCtx)
  {prog_osea : oseair.Prog}
  {pc : Nat}
  (h_start : StartsAt prog_osea pc (DerefProjectedExistingCtx.compiled ctx))
  (h_src_off : ctx.srcOff = 0)
  (h_dst_off : ctx.dstOff ≠ 0) :
  StartsAt prog_osea (pc + 3)
    [oseair.Instr.Assgn (dstTmpReg ctx) (oseair.Rhs.MutBorOffset ctx.dstReg ctx.dstOff),
     oseair.Instr.Memcpy (dstTmpReg ctx) (resReg ctx) (innerTy ctx),
     oseair.Instr.Die (dstTmpReg ctx)] := by
  have h_start_full :
      StartsAt prog_osea pc
        [oseair.Instr.Assgn (resReg ctx) (oseair.Rhs.Alloc (innerTy ctx)),
         oseair.Instr.Assgn (loadedPtrReg ctx) (oseair.Rhs.Load TyVal.PTy ctx.srcReg),
         oseair.Instr.Memcpy (resReg ctx) (loadedPtrReg ctx) (innerTy ctx),
         oseair.Instr.Assgn (dstTmpReg ctx) (oseair.Rhs.MutBorOffset ctx.dstReg ctx.dstOff),
         oseair.Instr.Memcpy (dstTmpReg ctx) (resReg ctx) (innerTy ctx),
         oseair.Instr.Die (dstTmpReg ctx)] := by
    simpa [DerefProjectedExistingCtx.compiled_eq, h_src_off, h_dst_off] using h_start
  simpa using (StartsAt.tail (StartsAt.tail (StartsAt.tail h_start_full)))

theorem starts_rhs_projected_suffix_direct
  (ctx : DerefProjectedExistingCtx)
  {prog_osea : oseair.Prog}
  {pc : Nat}
  (h_start : StartsAt prog_osea pc (DerefProjectedExistingCtx.compiled ctx))
  (h_src_off : ctx.srcOff ≠ 0)
  (h_dst_off : ctx.dstOff = 0) :
  StartsAt prog_osea (pc + 5)
    [oseair.Instr.Memcpy ctx.dstReg (resReg ctx) (innerTy ctx)] := by
  have h_start_full :
      StartsAt prog_osea pc
        [oseair.Instr.Assgn (resReg ctx) (oseair.Rhs.Alloc (innerTy ctx)),
         oseair.Instr.Assgn (srcTmpReg ctx) (oseair.Rhs.BorOffset ctx.srcReg ctx.srcOff),
         oseair.Instr.Assgn (loadedPtrReg ctx)
           (oseair.Rhs.Load TyVal.PTy (srcTmpReg ctx)),
         oseair.Instr.Die (srcTmpReg ctx),
         oseair.Instr.Memcpy (resReg ctx) (loadedPtrReg ctx) (innerTy ctx),
         oseair.Instr.Memcpy ctx.dstReg (resReg ctx) (innerTy ctx)] := by
    simpa [DerefProjectedExistingCtx.compiled_eq, h_src_off, h_dst_off] using h_start
  simpa using
    (StartsAt.tail
      (StartsAt.tail
        (StartsAt.tail
          (StartsAt.tail
            (StartsAt.tail h_start_full)))))

theorem starts_rhs_projected_suffix_projected
  (ctx : DerefProjectedExistingCtx)
  {prog_osea : oseair.Prog}
  {pc : Nat}
  (h_start : StartsAt prog_osea pc (DerefProjectedExistingCtx.compiled ctx))
  (h_src_off : ctx.srcOff ≠ 0)
  (h_dst_off : ctx.dstOff ≠ 0) :
  StartsAt prog_osea (pc + 5)
    [oseair.Instr.Assgn (dstTmpReg ctx) (oseair.Rhs.MutBorOffset ctx.dstReg ctx.dstOff),
     oseair.Instr.Memcpy (dstTmpReg ctx) (resReg ctx) (innerTy ctx),
     oseair.Instr.Die (dstTmpReg ctx)] := by
  have h_start_full :
      StartsAt prog_osea pc
        [oseair.Instr.Assgn (resReg ctx) (oseair.Rhs.Alloc (innerTy ctx)),
         oseair.Instr.Assgn (srcTmpReg ctx) (oseair.Rhs.BorOffset ctx.srcReg ctx.srcOff),
         oseair.Instr.Assgn (loadedPtrReg ctx)
           (oseair.Rhs.Load TyVal.PTy (srcTmpReg ctx)),
         oseair.Instr.Die (srcTmpReg ctx),
         oseair.Instr.Memcpy (resReg ctx) (loadedPtrReg ctx) (innerTy ctx),
         oseair.Instr.Assgn (dstTmpReg ctx) (oseair.Rhs.MutBorOffset ctx.dstReg ctx.dstOff),
         oseair.Instr.Memcpy (dstTmpReg ctx) (resReg ctx) (innerTy ctx),
         oseair.Instr.Die (dstTmpReg ctx)] := by
    simpa [DerefProjectedExistingCtx.compiled_eq, h_src_off, h_dst_off] using h_start
  simpa using
    (StartsAt.tail
      (StartsAt.tail
        (StartsAt.tail
          (StartsAt.tail
            (StartsAt.tail h_start_full)))))

theorem simulation
  (ctx : DerefProjectedExistingCtx)
  {ρa : AddrRenameMap}
  {ρt : TagRenameMap}
  {s_mir s_mir_next : mirlite.State}
  {s_osea : oseair.State}
  {prog_mir : mirlite.Prog}
  {prog_osea : oseair.Prog}
  (h_sim :
    LocalSim ctx ρa ρt s_mir s_osea
      (ptrSimOfCtx ρa ρt s_mir.env))
  (h_noninterference : TargetNonInterference ρa s_osea)
  (h_mir_start : StartsAt prog_mir s_mir.pc [stmt ctx])
  (h_mir_step :
    mirlite.stepWith A_m s_mir prog_mir = mirlite.Result.Ok s_mir_next)
  (h_pointee_tracked :
    ∀ srcBaseAddr_m srcTag_m q gq ap_src_read_m targetRes,
      s_mir.env.lookup ctx.src.base =
        some (srcBaseAddr_m, layoutToTyVal ctx.srcBaseLayout, srcTag_m) →
      s_mir.mem.find? (srcBaseAddr_m + ctx.srcOff) =
        some (mirlite.MemValue.PlaceTag q gq) →
      mirlite.resolveDirectPlace { s_mir with ap := ap_src_read_m } q =
        (mirlite.Result.Ok { s_mir with ap := ap_src_read_m }, targetRes) →
      ∃ targetReg targetBaseLayout targetOff targetBaseAddr,
        ctx.cs.placeMap.lookup q.base = some (targetReg, targetBaseLayout) ∧
        layoutResolvePath targetBaseLayout q.path = some (targetOff, ctx.innerLayout) ∧
        s_mir.env.lookup q.base =
          some (targetBaseAddr, layoutToTyVal targetBaseLayout, targetRes.tag) ∧
        targetRes.addr = targetBaseAddr + targetOff ∧
        targetRes.ty = layoutToTyVal ctx.innerLayout)
  (h_osea_start :
    StartsAt prog_osea s_osea.pc (DerefProjectedExistingCtx.compiled ctx))
  (h_inner_nonempty : 0 < blockSize ctx.innerLayout) :
  ∃ s_osea_next,
    StepStarWith oseair.bumpAllocator s_osea prog_osea s_osea_next ∧
    StateSim ctx.cs.placeMap ρa ρt s_mir_next s_osea_next
      (ptrSimOfCtx ρa ρt s_mir.env) ∧
    TargetNonInterference ρa s_osea_next ∧
    s_osea_next.pc = s_osea.pc + (DerefProjectedExistingCtx.compiled ctx).length := by
  let ptr_sim := ptrSimOfCtx ρa ρt s_mir.env
  let ⟨srcBase_m, srcBase_o, srcTag_m, srcTag_o, h_src_ptr, h_src_proj_block⟩ :=
    StateSim.place_projected h_sim ctx.h_src_lookup ctx.h_src_path
  let ⟨dstBase_m, dstBase_o, dstTag_m, dstTag_o, h_dst_ptr, _h_dst_block⟩ :=
    StateSim.place h_sim ctx.h_dst_lookup
  have h_src_env := place_runtime_sim.env h_src_ptr
  have h_dst_env := place_runtime_sim.env h_dst_ptr
  have h_src_reg := place_runtime_sim.reg h_src_ptr
  have h_src_addr_base : ρa srcBase_m = some srcBase_o := place_runtime_sim.addr h_src_ptr
  have h_src_addr : ρa (srcBase_m + ctx.srcOff) = some (srcBase_o + ctx.srcOff) :=
    addr_rename_offset h_src_addr_base
  have h_src_lt_old : srcBase_o + ctx.srcOff < s_osea.mem.addrStart :=
    h_noninterference.1 (srcBase_m + ctx.srcOff) (srcBase_o + ctx.srcOff) h_src_addr
  have h_src_tag : ρt srcTag_m = some srcTag_o := place_runtime_sim.tag h_src_ptr
  have h_dst_addr_base : ρa dstBase_m = some dstBase_o := place_runtime_sim.addr h_dst_ptr
  have h_dst_addr : ρa (dstBase_m + ctx.dstOff) = some (dstBase_o + ctx.dstOff) :=
    addr_rename_offset h_dst_addr_base
  have h_dst_lt_old : dstBase_o + ctx.dstOff < s_osea.mem.addrStart :=
    h_noninterference.1 (dstBase_m + ctx.dstOff) (dstBase_o + ctx.dstOff) h_dst_addr
  have h_dst_tag : ρt dstTag_m = some dstTag_o := place_runtime_sim.tag h_dst_ptr
  let allocBase_o := (oseair.bumpAllocator.alloc s_osea.mem (blockSize ctx.innerLayout)).1
  let allocMem_o := (oseair.bumpAllocator.alloc s_osea.mem (blockSize ctx.innerLayout)).2
  have h_alloc_pair :
      oseair.bumpAllocator.alloc s_osea.mem (blockSize ctx.innerLayout) =
        (allocBase_o, allocMem_o) := by
    simp [allocBase_o, allocMem_o]
  have h_alloc_mMap_o : allocMem_o.mMap = s_osea.mem.mMap := by
    have h_alloc_mMap :=
      oseair.AllocatorSpec.alloc_mMap_eq
        (A := oseair.bumpAllocator) s_osea.mem (blockSize ctx.innerLayout)
    rw [h_alloc_pair] at h_alloc_mMap
    simpa using h_alloc_mMap
  have h_alloc_base : allocBase_o = s_osea.mem.addrStart := by
    simp [allocBase_o, oseair.bumpAllocator, oseair.allocate]
  have h_alloc_addrStart' :
      allocMem_o.addrStart = s_osea.mem.addrStart + blockSize ctx.innerLayout := by
    simp [allocMem_o, oseair.bumpAllocator, oseair.allocate]
  have h_alloc_le : s_osea.mem.addrStart ≤ allocMem_o.addrStart := by
    simpa [h_alloc_addrStart'] using Nat.le_add_right s_osea.mem.addrStart (blockSize ctx.innerLayout)
  have h_alloc_lt : allocBase_o < allocMem_o.addrStart := by
    rw [h_alloc_base, h_alloc_addrStart']
    exact Nat.lt_add_of_pos_right (n := s_osea.mem.addrStart) h_inner_nonempty
  have h_next_alloc_clear :
      NextAllocClear (A_o := oseair.bumpAllocator) ρa s_osea (blockSize ctx.innerLayout) := by
    exact TargetNonInterference.next_alloc_clear h_noninterference
  have h_temp_unmapped_alloc : ∀ a, ρa a ≠ some allocBase_o := by
    exact h_next_alloc_clear.1
  have h_temp_stack_clear_alloc :
      s_osea.ap.StackMap.find? allocBase_o = none ∨
      s_osea.ap.StackMap.find? allocBase_o = some [] := by
    exact h_next_alloc_clear.2
  let ⟨ap_src_read_m, q, gq, targetRes_m,
       ap_target_read_m, ap_write_m,
       h_mir_read_src, h_mir_ptr_val, h_resolve_target,
       h_mir_read_target, h_mir_use, h_mir_next⟩ :=
    mirlite_step_inv ctx s_mir s_mir_next prog_mir
      srcBase_m srcTag_m dstBase_m dstTag_m
      h_src_env h_dst_env h_mir_start h_mir_step
  let targetAddr_m := targetRes_m.addr
  let targetTag_m := targetRes_m.tag
  have ⟨targetReg, targetBaseLayout, targetOff, targetBaseAddr_m,
        h_q_lookup, h_q_path, h_mir_target_env, h_target_addr_eq, h_target_ty⟩ :=
    h_pointee_tracked srcBase_m srcTag_m q gq ap_src_read_m targetRes_m
      h_src_env h_mir_ptr_val h_resolve_target
  let ⟨targetBaseAddr_m', targetBaseAddr_o, targetBaseTag_m', targetBaseTag_o,
       h_target_ptr, h_target_proj_block⟩ :=
    StateSim.place_projected h_sim h_q_lookup h_q_path
  have h_target_env_eq :
      some (targetBaseAddr_m', layoutToTyVal targetBaseLayout, targetBaseTag_m') =
        some (targetBaseAddr_m, layoutToTyVal targetBaseLayout, targetTag_m) := by
    exact (place_runtime_sim.env h_target_ptr).symm.trans h_mir_target_env
  cases h_target_env_eq
  have h_target_base_addr : ρa targetBaseAddr_m = some targetBaseAddr_o :=
    place_runtime_sim.addr h_target_ptr
  have h_target_addr : ρa targetAddr_m = some (targetBaseAddr_o + targetOff) := by
    show ρa targetRes_m.addr = some (targetBaseAddr_o + targetOff)
    rw [h_target_addr_eq]
    exact addr_rename_offset h_target_base_addr
  have h_target_lt_old : targetBaseAddr_o + targetOff < s_osea.mem.addrStart :=
    h_noninterference.1 targetAddr_m (targetBaseAddr_o + targetOff) h_target_addr
  have h_src_cell :
      mem_val_eq_opt
        (s_mir.mem.find? (srcBase_m + ctx.srcOff))
        (s_osea.mem.find? (srcBase_o + ctx.srcOff))
        ptr_sim := by
    simpa [blockSize, layoutSize] using
      h_src_proj_block 0 (by simp [blockSize, layoutSize])
  have h_src_find_and_tag :
      ∃ targetTag_o,
        s_osea.mem.find? (srcBase_o + ctx.srcOff) =
          some (oseair.Val.Ptr targetBaseAddr_o targetOff
            (blockSize targetBaseLayout) targetTag_o) ∧
        ρt gq = some targetTag_o := by
    cases h_find_o : s_osea.mem.find? (srcBase_o + ctx.srcOff) with
    | none =>
        simpa [h_mir_ptr_val, h_find_o, mem_val_eq_opt, mem_val_eq] using h_src_cell
    | some v =>
        cases v with
        | Undef =>
            simpa [h_mir_ptr_val, h_find_o, mem_val_eq_opt, mem_val_eq] using h_src_cell
        | Dat n =>
            simpa [h_mir_ptr_val, h_find_o, mem_val_eq_opt, mem_val_eq] using h_src_cell
        | Ptr base off size tag =>
            have h_ptr :
                ptr_sim q gq base off size tag := by
              simpa [h_mir_ptr_val, h_find_o, mem_val_eq_opt, mem_val_eq] using h_src_cell
            have ⟨h_addr_eq, h_off_eq, h_tag_eq, h_size_eq⟩ :=
              ptrSimOfCtx_elim h_ptr h_mir_target_env h_q_path
            have h_base : base = targetBaseAddr_o :=
              Option.some.inj (h_addr_eq.symm.trans h_target_base_addr)
            subst h_base; cases h_off_eq; cases h_size_eq
            exact ⟨tag, by simpa [h_find_o], h_tag_eq⟩
  obtain ⟨targetTag_o, h_src_find, h_gq_tag⟩ := h_src_find_and_tag
  have h_target_fit : targetOff + blockSize ctx.innerLayout ≤ blockSize targetBaseLayout :=
    layoutResolvePath_blockSize_le h_q_path
  have h_src_mem :
      oseair.readWordSeq s_osea.mem (srcBase_o + ctx.srcOff) 1 =
        [oseair.Val.Ptr targetBaseAddr_o targetOff
          (blockSize targetBaseLayout) targetTag_o] := by
    simp [oseair.readWordSeq, h_src_find]
  have h_target_vals :
      mem_vals_eq ptr_sim
        (mirlite.readWordSeq s_mir.mem targetAddr_m (blockSize ctx.innerLayout))
        (oseair.readWordSeq s_osea.mem (targetBaseAddr_o + targetOff) (blockSize ctx.innerLayout)) := by
    show mem_vals_eq ptr_sim
      (mirlite.readWordSeq s_mir.mem targetRes_m.addr (blockSize ctx.innerLayout))
      (oseair.readWordSeq s_osea.mem (targetBaseAddr_o + targetOff) (blockSize ctx.innerLayout))
    rw [h_target_addr_eq]
    exact mem_vals_eq_readWordSeq h_target_proj_block
  let s_mir_pre : mirlite.State := { s_mir with ap := ap_target_read_m }
  have h_mir_next_pre :
      s_mir_next =
        { s_mir_pre with
          ap := ap_write_m,
          mem := mirlite.writeWordSeq s_mir.mem (dstBase_m + ctx.dstOff)
            (mirlite.readWordSeq s_mir.mem targetAddr_m (blockSize ctx.innerLayout)),
          pc := s_mir.pc + 1 } := by
    simpa [s_mir_pre, h_target_ty, blockSize, layoutSize] using h_mir_next
  have ⟨allocTag_o, ap_alloc, h_osea_alloc⟩ :=
    sb_osea_only_own_ok h_temp_stack_clear_alloc
  have h_sb_alloc :=
    sb_osea_only_own_preserves_sim (StateSim.sb h_sim) h_temp_unmapped_alloc h_osea_alloc
  let vals_temp := oseair.readWordSeq s_osea.mem (targetBaseAddr_o + targetOff) (blockSize ctx.innerLayout)
  have h_temp_disj :
      ∀ base reg layout,
        ctx.cs.placeMap.lookup base = some (reg, layout) →
        ∀ addr_m addr_o tag_m tag_o,
          place_runtime_sim ctx.cs.placeMap ρa ρt s_mir s_osea
            base reg addr_m addr_o tag_m tag_o layout →
          blocks_disjoint addr_o (blockSize layout) allocBase_o vals_temp.length := by
    intro base reg layout h_lookup addr_m addr_o tag_m tag_o h_ptr
    simpa [vals_temp] using
      (alloc_fresh_target_disjoint
        (freshAddr_o := allocBase_o)
        (freshLayout := ctx.innerLayout)
        h_sim h_noninterference h_alloc_base h_lookup h_ptr)
  have h_sim_temp_write :
      StateSim ctx.cs.placeMap ρa ρt s_mir
        { s_osea with
          mem := oseair.writeWordSeq s_osea.mem allocBase_o vals_temp }
        ptr_sim := by
    exact state_sim_osea_write_other h_sim h_temp_disj
  have h_temp_ne_src : allocBase_o ≠ srcBase_o + ctx.srcOff := by
    intro h_eq
    exact h_temp_unmapped_alloc (srcBase_m + ctx.srcOff) (h_eq ▸ h_src_addr)
  have h_temp_ne_target : allocBase_o ≠ targetBaseAddr_o + targetOff := by
    intro h_eq
    exact h_temp_unmapped_alloc targetAddr_m (h_eq ▸ h_target_addr)
  have h_own_find :
      ap_alloc.StackMap.find? allocBase_o = some [RefKind.Own allocTag_o] :=
    sb_own_creates_find h_osea_alloc
  by_cases h_src_off : ctx.srcOff = 0
  ·
    have ⟨h_stmt0, h_stmt1, h_stmt2⟩ :=
      starts_rhs_direct_instrs ctx h_osea_start h_src_off
    let ⟨ap_load_parent, h_osea_load_parent, h_sb_load_parent⟩ :=
      sb_read_sim_ok h_sb_alloc h_src_addr h_src_tag h_mir_read_src
    have h_find_after_load :
        ap_load_parent.StackMap.find? allocBase_o =
          some [RefKind.Own allocTag_o] := by
      exact (sb_read_preserves_find_ne h_sb_alloc.valid_osea h_osea_load_parent h_temp_ne_src).trans
        h_own_find
    let ⟨ap_memcpy1_read, h_osea_memcpy1_read, h_sb_memcpy1_read⟩ :=
      sb_read_sim_ok h_sb_load_parent h_target_addr h_gq_tag h_mir_read_target
    have h_find_after_target_read :
        ap_memcpy1_read.StackMap.find? allocBase_o =
          some [RefKind.Own allocTag_o] := by
      exact (sb_read_preserves_find_ne
        h_sb_load_parent.valid_osea h_osea_memcpy1_read h_temp_ne_target).trans h_find_after_load
    have ⟨ap_memcpy1_write, h_osea_memcpy1_write⟩ :=
      sb_use_mb_of_find_own h_find_after_target_read
    have h_sb_prefix :=
      sb_osea_only_use_mb_preserves_sim h_sb_memcpy1_read h_temp_unmapped_alloc h_osea_memcpy1_write
    have h_find_temp_pre :
        ap_memcpy1_write.StackMap.find? allocBase_o =
          some [RefKind.Own allocTag_o] :=
      sb_use_mb_preserves_find_own h_find_after_target_read h_osea_memcpy1_write
    let s_osea_pre : oseair.State :=
      { s_osea with
        reg :=
          (s_osea.reg.insert (resReg ctx)
            (TyVal.PTy,
              [oseair.Val.Ptr allocBase_o 0 (blockSize ctx.innerLayout) allocTag_o])).insert
            (loadedPtrReg ctx)
            (TyVal.PTy,
              [oseair.Val.Ptr targetBaseAddr_o targetOff (blockSize targetBaseLayout) targetTag_o]),
        ap := ap_memcpy1_write,
        mem := oseair.writeWordSeq allocMem_o allocBase_o vals_temp,
        pc := s_osea.pc + 3 }
    have h_prefix_run :
        oseair.runNWith oseair.bumpAllocator 3 s_osea prog_osea = oseair.Result.Ok s_osea_pre := by
      simpa [s_osea_pre, vals_temp] using
        (osea_rhs_direct_run_ok (A_o := oseair.bumpAllocator) ctx
          s_osea prog_osea
          srcBase_o srcTag_o
          targetBaseAddr_o targetOff (blockSize targetBaseLayout) targetTag_o
          allocBase_o allocMem_o allocTag_o
          ap_alloc ap_load_parent ap_memcpy1_read ap_memcpy1_write
          h_src_off
          h_stmt0 h_stmt1 h_stmt2
          h_src_reg h_src_mem
          h_alloc_pair h_alloc_mMap_o
          h_osea_alloc
          (by simpa [h_src_off] using h_osea_load_parent)
          h_osea_memcpy1_read
          h_osea_memcpy1_write
          (by simpa [h_src_off] using layoutResolvePath_blockSize_le ctx.h_src_path)
          h_target_fit)
    have h_sim_pre_core :
        StateSim ctx.cs.placeMap ρa ρt
          s_mir_pre
          { s_osea with
            ap := ap_memcpy1_write,
            mem := oseair.writeWordSeq allocMem_o allocBase_o vals_temp }
          ptr_sim := by
      exact StateSim.of_mem_mMap_eq_sb h_sb_prefix h_sim_temp_write
        rfl rfl rfl
        (oseair_writeWordSeq_mMap_eq_of_mMap_eq h_alloc_mMap_o allocBase_o vals_temp).symm
    have h_res_fresh :
        ∀ base layout,
          ctx.cs.placeMap.lookup base = some (resReg ctx, layout) → False := by
      simpa [resReg, DerefProjectedExistingCtx.resReg] using
        (alloc_fresh_reg_of_ge (cs := ctx.cs) ctx.h_regs_below (Nat.le_refl _))
    have h_loaded_fresh :
        ∀ base layout,
          ctx.cs.placeMap.lookup base = some (loadedPtrReg ctx, layout) → False := by
      simpa [loadedPtrReg, DerefProjectedExistingCtx.loadedPtrReg, h_src_off] using
        (alloc_fresh_reg_of_ge (cs := ctx.cs) ctx.h_regs_below (Nat.le_add_right _ 1))
    have h_dstTmp_fresh :
        ∀ base layout,
          ctx.cs.placeMap.lookup base = some (dstTmpReg ctx, layout) → False := by
      simpa [dstTmpReg, DerefProjectedExistingCtx.dstTmpReg, h_src_off] using
        (alloc_fresh_reg_of_ge (cs := ctx.cs) ctx.h_regs_below (Nat.le_add_right _ 2))
    have h_sim_pre_res :
        StateSim ctx.cs.placeMap ρa ρt
          s_mir_pre
          { s_osea with
            reg := s_osea.reg.insert (resReg ctx)
              (TyVal.PTy,
                [oseair.Val.Ptr allocBase_o 0 (blockSize ctx.innerLayout) allocTag_o]),
            ap := ap_memcpy1_write,
            mem := oseair.writeWordSeq allocMem_o allocBase_o vals_temp }
          ptr_sim := by
      exact state_sim_reg_insert_other h_sim_pre_core h_res_fresh
    have h_sim_pre :
        StateSim ctx.cs.placeMap ρa ρt s_mir_pre s_osea_pre ptr_sim := by
      simpa [s_osea_pre] using
        (state_sim_reg_insert_other
          (tmpReg := loadedPtrReg ctx)
          (tmpVal :=
            (TyVal.PTy,
              [oseair.Val.Ptr targetBaseAddr_o targetOff (blockSize targetBaseLayout) targetTag_o]))
          h_sim_pre_res h_loaded_fresh)
    have h_res_ne_loaded : resReg ctx ≠ loadedPtrReg ctx := by
      intro h_eq
      unfold resReg loadedPtrReg DerefProjectedExistingCtx.resReg
        DerefProjectedExistingCtx.loadedPtrReg at h_eq
      have h_reg : Register.R ctx.cs.nextReg = Register.R (ctx.cs.nextReg + 1) := by
        simpa [h_src_off] using h_eq
      injection h_reg with h_nat
      exact (Nat.ne_of_lt (Nat.lt_succ_self ctx.cs.nextReg)) h_nat
    have h_res_ne_dstTmp : resReg ctx ≠ dstTmpReg ctx := by
      intro h_eq
      unfold resReg dstTmpReg DerefProjectedExistingCtx.resReg
        DerefProjectedExistingCtx.dstTmpReg at h_eq
      have h_reg : Register.R ctx.cs.nextReg = Register.R (ctx.cs.nextReg + 2) := by
        simpa [h_src_off] using h_eq
      injection h_reg with h_nat
      have h_ne : ctx.cs.nextReg ≠ ctx.cs.nextReg + 2 :=
        Nat.ne_of_lt (Nat.lt_succ_of_lt (Nat.lt_succ_self ctx.cs.nextReg))
      exact h_ne h_nat
    have h_src_reg_pre :
        s_osea_pre.reg.lookup (resReg ctx) =
          some (TyVal.PTy, [oseair.Val.Ptr allocBase_o 0 (blockSize ctx.innerLayout) allocTag_o]) := by
      simp [s_osea_pre, h_res_ne_loaded]
    have h_dst_ne_res : ctx.dstReg ≠ resReg ctx := by
      intro h_eq
      exact (alloc_fresh_reg_of_ge (cs := ctx.cs) ctx.h_regs_below (Nat.le_refl _)
        ctx.dst.base ctx.dstBaseLayout)
        (by simpa [resReg, DerefProjectedExistingCtx.resReg, h_eq] using ctx.h_dst_lookup)
    have h_dst_ne_loaded : ctx.dstReg ≠ loadedPtrReg ctx := by
      intro h_eq
      exact (alloc_fresh_reg_of_ge (cs := ctx.cs) ctx.h_regs_below (Nat.le_add_right _ 1)
        ctx.dst.base ctx.dstBaseLayout)
        (by simpa [loadedPtrReg, DerefProjectedExistingCtx.loadedPtrReg, h_src_off, h_eq]
          using ctx.h_dst_lookup)
    have h_dst_reg_pre :
        s_osea_pre.reg.lookup ctx.dstReg =
          some (TyVal.PTy, [oseair.Val.Ptr dstBase_o 0 (blockSize ctx.dstBaseLayout) dstTag_o]) := by
      simpa [s_osea_pre, h_dst_ne_res, h_dst_ne_loaded] using place_runtime_sim.reg h_dst_ptr
    have h_dst_pre :
        place_runtime_sim ctx.cs.placeMap ρa ρt
          s_mir_pre s_osea_pre
          ctx.dst.base ctx.dstReg dstBase_m dstBase_o dstTag_m dstTag_o ctx.dstBaseLayout := by
      refine ⟨ctx.h_dst_lookup, ?_, h_dst_reg_pre, h_dst_addr_base, h_dst_tag⟩
      simpa [s_mir_pre] using h_dst_env
    let s_osea_alloc : oseair.State := { s_osea with mem := allocMem_o, ap := ap_alloc }
    let s_osea_load_parent : oseair.State := { s_osea with mem := allocMem_o, ap := ap_load_parent }
    let s_osea_target_read : oseair.State := { s_osea with mem := allocMem_o, ap := ap_memcpy1_read }
    let s_osea_use : oseair.State := { s_osea with mem := allocMem_o, ap := ap_memcpy1_write }
    have h_valid_alloc : SBValid ap_alloc :=
      sb_own_preserves_valid (StateSim.sb h_sim).valid_osea h_osea_alloc
    have h_valid_load_parent : SBValid ap_load_parent :=
      sb_read_preserves_valid h_valid_alloc h_osea_load_parent
    have h_valid_target_read : SBValid ap_memcpy1_read :=
      sb_read_preserves_valid h_valid_load_parent h_osea_memcpy1_read
    have h_src_lt_alloc : srcBase_o + ctx.srcOff < s_osea_alloc.mem.addrStart := by
      exact Nat.lt_of_lt_of_le h_src_lt_old (by
        show s_osea.mem.addrStart ≤ s_osea_alloc.mem.addrStart
        simp [s_osea_alloc, h_alloc_addrStart'])
    have h_target_lt_alloc : targetBaseAddr_o + targetOff < s_osea_load_parent.mem.addrStart := by
      exact Nat.lt_of_lt_of_le h_target_lt_old (by
        show s_osea.mem.addrStart ≤ s_osea_load_parent.mem.addrStart
        simp [s_osea_load_parent, h_alloc_addrStart'])
    have h_nonempty_alloc : TargetNonemptyStacksBelowAddrStart s_osea_alloc := by
      exact TargetNonemptyStacksBelowAddrStart.sb_own
        h_noninterference.2 (StateSim.sb h_sim).valid_osea
        (by
          show s_osea.mem.addrStart ≤ s_osea_alloc.mem.addrStart
          simp [s_osea_alloc, h_alloc_addrStart'])
        (by simpa [s_osea_alloc] using h_alloc_lt)
        h_osea_alloc
    have h_nonempty_load_parent : TargetNonemptyStacksBelowAddrStart s_osea_load_parent := by
      exact TargetNonemptyStacksBelowAddrStart.sb_read
        (s_osea := s_osea_alloc)
        h_nonempty_alloc h_valid_alloc
        (by simpa [s_osea_alloc] using h_src_lt_alloc)
        (by simpa [s_osea_alloc, s_osea_load_parent] using h_osea_load_parent)
    have h_nonempty_target_read : TargetNonemptyStacksBelowAddrStart s_osea_target_read := by
      exact TargetNonemptyStacksBelowAddrStart.sb_read
        (s_osea := s_osea_load_parent)
        h_nonempty_load_parent h_valid_load_parent
        (by simpa [s_osea_load_parent] using h_target_lt_alloc)
        (by simpa [s_osea_load_parent, s_osea_target_read] using h_osea_memcpy1_read)
    have h_nonempty_use_core : TargetNonemptyStacksBelowAddrStart s_osea_use := by
      exact TargetNonemptyStacksBelowAddrStart.sb_use_mb
        (s_osea := s_osea_target_read)
        h_nonempty_target_read h_valid_target_read
        (by simpa [s_osea_target_read] using h_alloc_lt)
        (by simpa [s_osea_target_read, s_osea_use] using h_osea_memcpy1_write)
    have h_nonempty_pre : TargetNonemptyStacksBelowAddrStart s_osea_pre := by
      exact TargetNonemptyStacksBelowAddrStart.of_stackMap_eq
        (s_osea := s_osea_use)
        (s_osea_next := s_osea_pre)
        h_nonempty_use_core rfl (by simp [s_osea_use, s_osea_pre, oseair_writeWordSeq_addrStart_eq])
    have h_noninterference_pre : TargetNonInterference ρa s_osea_pre := by
      refine ⟨?_, h_nonempty_pre⟩
      exact TargetAddrRenameBelowAddrStart.mono h_noninterference.1
        (by simpa [s_osea_pre, oseair_writeWordSeq_addrStart_eq] using h_alloc_le)
    have h_temp_read_exact :
        oseair.readWordSeq s_osea_pre.mem allocBase_o (blockSize ctx.innerLayout) = vals_temp := by
      simpa [s_osea_pre, vals_temp] using
        (oseair_readWordSeq_write_exact allocMem_o allocBase_o vals_temp)
    have h_vals :
        mem_vals_eq ptr_sim
          (mirlite.readWordSeq s_mir.mem targetAddr_m (blockSize ctx.innerLayout))
          (oseair.readWordSeq s_osea_pre.mem allocBase_o (blockSize ctx.innerLayout)) := by
      rw [h_temp_read_exact]
      simpa [vals_temp] using h_target_vals
    have h_start_direct :
        ctx.dstOff = 0 →
          StartsAt prog_osea s_osea_pre.pc
            [oseair.Instr.Memcpy ctx.dstReg (resReg ctx) (innerTy ctx)] := by
      intro h_zero
      simpa [s_osea_pre] using
        starts_rhs_direct_suffix_direct ctx h_osea_start h_src_off h_zero
    have h_start_projected :
        ctx.dstOff ≠ 0 →
          StartsAt prog_osea s_osea_pre.pc
            [oseair.Instr.Assgn (dstTmpReg ctx) (oseair.Rhs.MutBorOffset ctx.dstReg ctx.dstOff),
             oseair.Instr.Memcpy (dstTmpReg ctx) (resReg ctx) (innerTy ctx),
             oseair.Instr.Die (dstTmpReg ctx)] := by
      intro h_ne
      simpa [s_osea_pre] using
        starts_rhs_direct_suffix_projected ctx h_osea_start h_src_off h_ne
    have h_target_direct :
        ctx.dstOff = 0 →
          ∃ ap_read_o ap_write_o,
            sb_read s_osea_pre.ap (allocBase_o + 0) allocTag_o = SBResult.Ok ap_read_o ∧
            sb_use_mb ap_read_o (dstBase_o + ctx.dstOff) dstTag_o = SBResult.Ok ap_write_o ∧
            sb_sim ρa ρt ap_write_m ap_write_o := by
      intro _h
      obtain ⟨ap_read_o, h_temp_read⟩ := sb_read_of_find_own h_find_temp_pre
      have h_sb_read :=
        sb_osea_only_read_preserves_sim h_sb_prefix h_temp_unmapped_alloc h_temp_read
      let ⟨ap_write_o, h_write_o, h_sb_write⟩ :=
        sb_use_mb_sim_ok h_sb_read h_dst_addr h_dst_tag h_mir_use
      exact ⟨ap_read_o, ap_write_o,
        by simpa [s_osea_pre, Nat.zero_add] using h_temp_read,
        h_write_o, h_sb_write⟩
    have h_target_projected :
        ctx.dstOff ≠ 0 →
          ∃ tempTag ap_ref_o ap_read_o ap_write_o ap_final_o,
            sb_ref s_osea_pre.ap (dstBase_o + ctx.dstOff) dstTag_o RefOpKind.Mut =
              (SBResult.Ok ap_ref_o, tempTag) ∧
            sb_read ap_ref_o (allocBase_o + 0) allocTag_o = SBResult.Ok ap_read_o ∧
            sb_use_mb ap_read_o (dstBase_o + ctx.dstOff) tempTag = SBResult.Ok ap_write_o ∧
            sb_die ap_write_o (dstBase_o + ctx.dstOff) tempTag = SBResult.Ok ap_final_o ∧
            sb_sim ρa ρt ap_write_m ap_final_o := by
      intro _h
      simpa [s_osea_pre, Nat.zero_add] using
        (sb_ref_mut_read_unmapped_use_die_sim_ok
          (h_sim := h_sb_prefix)
          (h_dst_addr := h_dst_addr)
          (h_dst_tag := h_dst_tag)
          (h_use_m := h_mir_use)
          (h_src_find := h_find_temp_pre)
          (h_src_unmapped := h_temp_unmapped_alloc))
    obtain ⟨s_osea_next, h_steps, h_rest⟩ :=
      existing_memcpy_simulation
        (A_o := oseair.bumpAllocator)
        (ρa := ρa) (ρt := ρt)
        (s_mir := s_mir_pre)
        (s_osea := s_osea_pre)
        (s_mir_next := s_mir_next)
        (prog_osea := prog_osea)
        (srcReg := resReg ctx)
        (dst_reg := ctx.dstReg)
        (tmpReg := dstTmpReg ctx)
        (baseLayout := ctx.dstBaseLayout)
        (subLayout := ctx.innerLayout)
        (srcBase := allocBase_o)
        (srcOff := 0)
        (srcSize := blockSize ctx.innerLayout)
        (srcTag := allocTag_o)
        (dst_base := ctx.dst.base)
        (dst_mir := dstBase_m)
        (dst_osea := dstBase_o)
        (dst_tag_m := dstTag_m)
        (dst_tag_o := dstTag_o)
        (off := ctx.dstOff)
        (vals_mir := mirlite.readWordSeq s_mir.mem targetAddr_m (blockSize ctx.innerLayout))
        (ap_m' := ap_write_m)
        (ptr_sim := ptr_sim)
        h_sim_pre h_noninterference_pre h_dst_pre
        (layoutResolvePath_blockSize_le ctx.h_dst_path)
        h_inner_nonempty
        h_dstTmp_fresh
        h_start_direct h_start_projected
        h_src_reg_pre
        (by simpa [s_osea_pre, Nat.zero_add, oseair_writeWordSeq_addrStart_eq] using h_alloc_lt)
        (by
          exact Nat.lt_of_lt_of_le h_dst_lt_old
            (by simpa [s_osea_pre, oseair_writeWordSeq_addrStart_eq] using h_alloc_le))
        h_res_ne_dstTmp
        (by simp [blockSize, layoutSize])
        h_target_direct h_target_projected
        h_mir_next_pre h_vals
    rcases h_rest with ⟨h_sim_next, h_noninterference_next, h_pc_tail⟩
    exact ⟨s_osea_next,
      StepStarWith.trans (StepStarWith.of_runN_ok h_prefix_run) h_steps,
      h_sim_next,
      h_noninterference_next,
      by
        by_cases h_dst_off : ctx.dstOff = 0
        · simpa [s_osea_pre, DerefProjectedExistingCtx.compiled_eq, h_src_off, h_dst_off, Nat.add_assoc] using
            h_pc_tail
        · simpa [s_osea_pre, DerefProjectedExistingCtx.compiled_eq, h_src_off, h_dst_off, Nat.add_assoc] using
            h_pc_tail⟩
  ·
    have ⟨h_stmt0, h_stmt1, h_stmt2, h_stmt3, h_stmt4⟩ :=
      starts_rhs_projected_instrs ctx h_osea_start h_src_off
    let ⟨ap_load_parent, h_osea_load_parent, h_sb_load_parent⟩ :=
      sb_read_sim_ok h_sb_alloc h_src_addr h_src_tag h_mir_read_src
    let ⟨srcTempTag_o, ap_src_ref_o, ap_load_o, ap_load_final_o,
      h_osea_ref, h_osea_load, h_osea_die, h_src_stack_eq⟩ :=
      sb_ref_shared_read_die_ok_of_read_ok h_osea_load_parent
    have h_sb_load_final : sb_sim ρa ρt ap_src_read_m ap_load_final_o :=
      sb_sim_of_right_stackMap_eq h_sb_load_parent h_src_stack_eq
    have h_valid_ref : SBValid ap_src_ref_o :=
      sb_ref_preserves_valid h_sb_alloc.valid_osea h_osea_ref
    have h_find_after_ref :
        ap_src_ref_o.StackMap.find? allocBase_o = some [RefKind.Own allocTag_o] := by
      exact (sb_ref_preserves_find_ne h_sb_alloc.valid_osea h_osea_ref h_temp_ne_src).trans
        h_own_find
    have h_valid_load : SBValid ap_load_o :=
      sb_read_preserves_valid h_valid_ref h_osea_load
    have h_find_after_load :
        ap_load_o.StackMap.find? allocBase_o = some [RefKind.Own allocTag_o] := by
      exact (sb_read_preserves_find_ne h_valid_ref h_osea_load h_temp_ne_src).trans
        h_find_after_ref
    have h_find_after_die :
        ap_load_final_o.StackMap.find? allocBase_o = some [RefKind.Own allocTag_o] := by
      exact (sb_die_preserves_find_ne h_valid_load h_osea_die h_temp_ne_src).trans
        h_find_after_load
    let ⟨ap_memcpy1_read, h_osea_memcpy1_read, h_sb_memcpy1_read⟩ :=
      sb_read_sim_ok h_sb_load_final h_target_addr h_gq_tag h_mir_read_target
    have h_find_after_target_read :
        ap_memcpy1_read.StackMap.find? allocBase_o = some [RefKind.Own allocTag_o] := by
      exact (sb_read_preserves_find_ne
        h_sb_load_final.valid_osea h_osea_memcpy1_read h_temp_ne_target).trans h_find_after_die
    have ⟨ap_memcpy1_write, h_osea_memcpy1_write⟩ :=
      sb_use_mb_of_find_own h_find_after_target_read
    have h_sb_prefix :=
      sb_osea_only_use_mb_preserves_sim h_sb_memcpy1_read h_temp_unmapped_alloc h_osea_memcpy1_write
    have h_find_temp_pre :
        ap_memcpy1_write.StackMap.find? allocBase_o = some [RefKind.Own allocTag_o] :=
      sb_use_mb_preserves_find_own h_find_after_target_read h_osea_memcpy1_write
    let s_osea_pre : oseair.State :=
      { s_osea with
        reg :=
          ((s_osea.reg.insert (resReg ctx)
            (TyVal.PTy,
              [oseair.Val.Ptr allocBase_o 0 (blockSize ctx.innerLayout) allocTag_o])).insert
            (srcTmpReg ctx)
            (TyVal.PTy,
              [oseair.Val.Ptr srcBase_o ctx.srcOff (blockSize ctx.srcBaseLayout) srcTempTag_o])).insert
            (loadedPtrReg ctx)
            (TyVal.PTy,
              [oseair.Val.Ptr targetBaseAddr_o targetOff (blockSize targetBaseLayout) targetTag_o]),
        ap := ap_memcpy1_write,
        mem := oseair.writeWordSeq allocMem_o allocBase_o vals_temp,
        pc := s_osea.pc + 5 }
    have h_prefix_run :
        oseair.runNWith oseair.bumpAllocator 5 s_osea prog_osea = oseair.Result.Ok s_osea_pre := by
      simpa [s_osea_pre, vals_temp] using
        (osea_rhs_projected_run_ok (A_o := oseair.bumpAllocator) ctx
          s_osea prog_osea
          srcBase_o srcTag_o srcTempTag_o
          targetBaseAddr_o targetOff (blockSize targetBaseLayout) targetTag_o
          allocBase_o allocMem_o allocTag_o
          ap_alloc ap_src_ref_o ap_load_o ap_load_final_o ap_memcpy1_read ap_memcpy1_write
          h_src_off
          h_stmt0 h_stmt1 h_stmt2 h_stmt3 h_stmt4
          h_src_reg h_src_mem
          h_alloc_pair h_alloc_mMap_o
          h_osea_alloc h_osea_ref h_osea_load h_osea_die
          h_osea_memcpy1_read h_osea_memcpy1_write
          (layoutResolvePath_blockSize_le ctx.h_src_path)
          h_target_fit)
    have h_sim_pre_core :
        StateSim ctx.cs.placeMap ρa ρt
          s_mir_pre
          { s_osea with
            ap := ap_memcpy1_write,
            mem := oseair.writeWordSeq allocMem_o allocBase_o vals_temp }
          ptr_sim := by
      exact StateSim.of_mem_mMap_eq_sb h_sb_prefix h_sim_temp_write
        rfl rfl rfl
        (oseair_writeWordSeq_mMap_eq_of_mMap_eq h_alloc_mMap_o allocBase_o vals_temp).symm
    have h_res_fresh :
        ∀ base layout,
          ctx.cs.placeMap.lookup base = some (resReg ctx, layout) → False := by
      simpa [resReg, DerefProjectedExistingCtx.resReg] using
        (alloc_fresh_reg_of_ge (cs := ctx.cs) ctx.h_regs_below (Nat.le_refl _))
    have h_srcTmp_fresh :
        ∀ base layout,
          ctx.cs.placeMap.lookup base = some (srcTmpReg ctx, layout) → False := by
      simpa [srcTmpReg, DerefProjectedExistingCtx.srcTmpReg] using
        (alloc_fresh_reg_of_ge (cs := ctx.cs) ctx.h_regs_below (Nat.le_add_right _ 1))
    have h_loaded_fresh :
        ∀ base layout,
          ctx.cs.placeMap.lookup base = some (loadedPtrReg ctx, layout) → False := by
      simpa [loadedPtrReg, DerefProjectedExistingCtx.loadedPtrReg, h_src_off] using
        (alloc_fresh_reg_of_ge (cs := ctx.cs) ctx.h_regs_below (Nat.le_add_right _ 2))
    have h_dstTmp_fresh :
        ∀ base layout,
          ctx.cs.placeMap.lookup base = some (dstTmpReg ctx, layout) → False := by
      simpa [dstTmpReg, DerefProjectedExistingCtx.dstTmpReg, h_src_off] using
        (alloc_fresh_reg_of_ge (cs := ctx.cs) ctx.h_regs_below (Nat.le_add_right _ 3))
    have h_sim_pre_res :
        StateSim ctx.cs.placeMap ρa ρt
          s_mir_pre
          { s_osea with
            reg := s_osea.reg.insert (resReg ctx)
              (TyVal.PTy,
                [oseair.Val.Ptr allocBase_o 0 (blockSize ctx.innerLayout) allocTag_o]),
            ap := ap_memcpy1_write,
            mem := oseair.writeWordSeq allocMem_o allocBase_o vals_temp }
          ptr_sim := by
      exact state_sim_reg_insert_other h_sim_pre_core h_res_fresh
    have h_sim_pre_srcTmp :
        StateSim ctx.cs.placeMap ρa ρt
          s_mir_pre
          { s_osea with
            reg :=
              (s_osea.reg.insert (resReg ctx)
                (TyVal.PTy,
                  [oseair.Val.Ptr allocBase_o 0 (blockSize ctx.innerLayout) allocTag_o])).insert
                (srcTmpReg ctx)
                (TyVal.PTy,
                  [oseair.Val.Ptr srcBase_o ctx.srcOff (blockSize ctx.srcBaseLayout) srcTempTag_o]),
            ap := ap_memcpy1_write,
            mem := oseair.writeWordSeq allocMem_o allocBase_o vals_temp }
          ptr_sim := by
      exact state_sim_reg_insert_other h_sim_pre_res h_srcTmp_fresh
    have h_sim_pre :
        StateSim ctx.cs.placeMap ρa ρt s_mir_pre s_osea_pre ptr_sim := by
      simpa [s_osea_pre] using
        (state_sim_reg_insert_other
          (tmpReg := loadedPtrReg ctx)
          (tmpVal :=
            (TyVal.PTy,
              [oseair.Val.Ptr targetBaseAddr_o targetOff (blockSize targetBaseLayout) targetTag_o]))
          h_sim_pre_srcTmp h_loaded_fresh)
    have h_res_ne_srcTmp : resReg ctx ≠ srcTmpReg ctx := by
      intro h_eq
      unfold resReg srcTmpReg DerefProjectedExistingCtx.resReg
        DerefProjectedExistingCtx.srcTmpReg at h_eq
      have h_reg : Register.R ctx.cs.nextReg = Register.R (ctx.cs.nextReg + 1) := h_eq
      injection h_reg with h_nat
      exact (Nat.ne_of_lt (Nat.lt_succ_self ctx.cs.nextReg)) h_nat
    have h_res_ne_loaded : resReg ctx ≠ loadedPtrReg ctx := by
      intro h_eq
      unfold resReg loadedPtrReg DerefProjectedExistingCtx.resReg
        DerefProjectedExistingCtx.loadedPtrReg at h_eq
      by_cases h_zero : ctx.srcOff = 0
      · exact False.elim (h_src_off h_zero)
      · have h_reg : Register.R ctx.cs.nextReg = Register.R (ctx.cs.nextReg + 2) := by
          simpa [h_zero] using h_eq
        injection h_reg with h_nat
        have h_ne : ctx.cs.nextReg ≠ ctx.cs.nextReg + 2 :=
          Nat.ne_of_lt (Nat.lt_succ_of_lt (Nat.lt_succ_self ctx.cs.nextReg))
        exact h_ne h_nat
    have h_res_ne_dstTmp : resReg ctx ≠ dstTmpReg ctx := by
      intro h_eq
      unfold resReg dstTmpReg DerefProjectedExistingCtx.resReg
        DerefProjectedExistingCtx.dstTmpReg at h_eq
      by_cases h_zero : ctx.srcOff = 0
      · exact False.elim (h_src_off h_zero)
      · have h_reg : Register.R ctx.cs.nextReg = Register.R (ctx.cs.nextReg + 3) := by
          simpa [h_zero] using h_eq
        injection h_reg with h_nat
        have h_ne : ctx.cs.nextReg ≠ ctx.cs.nextReg + 3 := by
          intro h_false
          have : ctx.cs.nextReg + 1 = ctx.cs.nextReg + 3 := by simpa using congrArg Nat.succ h_false
          exact (Nat.ne_of_lt (Nat.lt_succ_of_lt (Nat.lt_succ_self (ctx.cs.nextReg + 1)))) this
        exact h_ne h_nat
    have h_src_reg_pre :
        s_osea_pre.reg.lookup (resReg ctx) =
          some (TyVal.PTy, [oseair.Val.Ptr allocBase_o 0 (blockSize ctx.innerLayout) allocTag_o]) := by
      simp [s_osea_pre, h_res_ne_srcTmp, h_res_ne_loaded]
    have h_dst_ne_res : ctx.dstReg ≠ resReg ctx := by
      intro h_eq
      exact (alloc_fresh_reg_of_ge (cs := ctx.cs) ctx.h_regs_below (Nat.le_refl _)
        ctx.dst.base ctx.dstBaseLayout)
        (by simpa [resReg, DerefProjectedExistingCtx.resReg, h_eq] using ctx.h_dst_lookup)
    have h_dst_ne_srcTmp : ctx.dstReg ≠ srcTmpReg ctx := by
      intro h_eq
      exact (alloc_fresh_reg_of_ge (cs := ctx.cs) ctx.h_regs_below (Nat.le_add_right _ 1)
        ctx.dst.base ctx.dstBaseLayout)
        (by simpa [srcTmpReg, DerefProjectedExistingCtx.srcTmpReg, h_eq] using ctx.h_dst_lookup)
    have h_dst_ne_loaded : ctx.dstReg ≠ loadedPtrReg ctx := by
      intro h_eq
      exact (alloc_fresh_reg_of_ge (cs := ctx.cs) ctx.h_regs_below (Nat.le_add_right _ 2)
        ctx.dst.base ctx.dstBaseLayout)
        (by simpa [loadedPtrReg, DerefProjectedExistingCtx.loadedPtrReg, h_src_off, h_eq]
          using ctx.h_dst_lookup)
    have h_dst_reg_pre :
        s_osea_pre.reg.lookup ctx.dstReg =
          some (TyVal.PTy, [oseair.Val.Ptr dstBase_o 0 (blockSize ctx.dstBaseLayout) dstTag_o]) := by
      simpa [s_osea_pre, h_dst_ne_res, h_dst_ne_srcTmp, h_dst_ne_loaded] using
        place_runtime_sim.reg h_dst_ptr
    have h_dst_pre :
        place_runtime_sim ctx.cs.placeMap ρa ρt
          s_mir_pre s_osea_pre
          ctx.dst.base ctx.dstReg dstBase_m dstBase_o dstTag_m dstTag_o ctx.dstBaseLayout := by
      refine ⟨ctx.h_dst_lookup, ?_, h_dst_reg_pre, h_dst_addr_base, h_dst_tag⟩
      simpa [s_mir_pre] using h_dst_env
    let s_osea_alloc : oseair.State := { s_osea with mem := allocMem_o, ap := ap_alloc }
    let s_osea_ref : oseair.State := { s_osea with mem := allocMem_o, ap := ap_src_ref_o }
    let s_osea_load : oseair.State := { s_osea with mem := allocMem_o, ap := ap_load_o }
    let s_osea_load_final : oseair.State := { s_osea with mem := allocMem_o, ap := ap_load_final_o }
    let s_osea_target_read : oseair.State := { s_osea with mem := allocMem_o, ap := ap_memcpy1_read }
    let s_osea_use : oseair.State := { s_osea with mem := allocMem_o, ap := ap_memcpy1_write }
    have h_valid_alloc : SBValid ap_alloc :=
      sb_own_preserves_valid (StateSim.sb h_sim).valid_osea h_osea_alloc
    have h_valid_ref' : SBValid ap_src_ref_o :=
      sb_ref_preserves_valid h_valid_alloc h_osea_ref
    have h_valid_load' : SBValid ap_load_o :=
      sb_read_preserves_valid h_valid_ref' h_osea_load
    have h_valid_load_final' : SBValid ap_load_final_o :=
      sb_die_preserves_valid h_valid_load' h_osea_die
    have h_valid_target_read : SBValid ap_memcpy1_read :=
      sb_read_preserves_valid h_valid_load_final' h_osea_memcpy1_read
    have h_src_lt_alloc : srcBase_o + ctx.srcOff < s_osea_alloc.mem.addrStart := by
      exact Nat.lt_of_lt_of_le h_src_lt_old (by
        show s_osea.mem.addrStart ≤ s_osea_alloc.mem.addrStart
        simp [s_osea_alloc, h_alloc_addrStart'])
    have h_target_lt_alloc : targetBaseAddr_o + targetOff < s_osea_load_final.mem.addrStart := by
      exact Nat.lt_of_lt_of_le h_target_lt_old (by
        show s_osea.mem.addrStart ≤ s_osea_load_final.mem.addrStart
        simp [s_osea_load_final, h_alloc_addrStart'])
    have h_nonempty_alloc : TargetNonemptyStacksBelowAddrStart s_osea_alloc := by
      exact TargetNonemptyStacksBelowAddrStart.sb_own
        h_noninterference.2 (StateSim.sb h_sim).valid_osea
        (by
          show s_osea.mem.addrStart ≤ s_osea_alloc.mem.addrStart
          simp [s_osea_alloc, h_alloc_addrStart'])
        (by simpa [s_osea_alloc] using h_alloc_lt)
        h_osea_alloc
    have h_nonempty_ref : TargetNonemptyStacksBelowAddrStart s_osea_ref := by
      exact TargetNonemptyStacksBelowAddrStart.sb_ref
        (s_osea := s_osea_alloc)
        h_nonempty_alloc h_valid_alloc
        (by simpa [s_osea_alloc] using h_src_lt_alloc)
        (by simpa [s_osea_alloc, s_osea_ref] using h_osea_ref)
    have h_nonempty_load : TargetNonemptyStacksBelowAddrStart s_osea_load := by
      exact TargetNonemptyStacksBelowAddrStart.sb_read
        (s_osea := s_osea_ref)
        h_nonempty_ref h_valid_ref'
        (by simpa [s_osea_ref] using h_src_lt_alloc)
        (by simpa [s_osea_ref, s_osea_load] using h_osea_load)
    have h_nonempty_load_final : TargetNonemptyStacksBelowAddrStart s_osea_load_final := by
      exact TargetNonemptyStacksBelowAddrStart.sb_die
        (s_osea := s_osea_load)
        h_nonempty_load h_valid_load'
        (by simpa [s_osea_load] using h_src_lt_alloc)
        (by simpa [s_osea_load, s_osea_load_final] using h_osea_die)
    have h_nonempty_target_read : TargetNonemptyStacksBelowAddrStart s_osea_target_read := by
      exact TargetNonemptyStacksBelowAddrStart.sb_read
        (s_osea := s_osea_load_final)
        h_nonempty_load_final h_valid_load_final'
        (by simpa [s_osea_load_final] using h_target_lt_alloc)
        (by simpa [s_osea_load_final, s_osea_target_read] using h_osea_memcpy1_read)
    have h_nonempty_use_core : TargetNonemptyStacksBelowAddrStart s_osea_use := by
      exact TargetNonemptyStacksBelowAddrStart.sb_use_mb
        (s_osea := s_osea_target_read)
        h_nonempty_target_read h_valid_target_read
        (by simpa [s_osea_target_read] using h_alloc_lt)
        (by simpa [s_osea_target_read, s_osea_use] using h_osea_memcpy1_write)
    have h_nonempty_pre : TargetNonemptyStacksBelowAddrStart s_osea_pre := by
      exact TargetNonemptyStacksBelowAddrStart.of_stackMap_eq
        (s_osea := s_osea_use)
        (s_osea_next := s_osea_pre)
        h_nonempty_use_core rfl (by simp [s_osea_use, s_osea_pre, oseair_writeWordSeq_addrStart_eq])
    have h_noninterference_pre : TargetNonInterference ρa s_osea_pre := by
      refine ⟨?_, h_nonempty_pre⟩
      exact TargetAddrRenameBelowAddrStart.mono h_noninterference.1
        (by simpa [s_osea_pre, oseair_writeWordSeq_addrStart_eq] using h_alloc_le)
    have h_temp_read_exact :
        oseair.readWordSeq s_osea_pre.mem allocBase_o (blockSize ctx.innerLayout) = vals_temp := by
      simpa [s_osea_pre, vals_temp] using
        (oseair_readWordSeq_write_exact allocMem_o allocBase_o vals_temp)
    have h_vals :
        mem_vals_eq ptr_sim
          (mirlite.readWordSeq s_mir.mem targetAddr_m (blockSize ctx.innerLayout))
          (oseair.readWordSeq s_osea_pre.mem allocBase_o (blockSize ctx.innerLayout)) := by
      rw [h_temp_read_exact]
      simpa [vals_temp] using h_target_vals
    have h_start_direct :
        ctx.dstOff = 0 →
          StartsAt prog_osea s_osea_pre.pc
            [oseair.Instr.Memcpy ctx.dstReg (resReg ctx) (innerTy ctx)] := by
      intro h_zero
      simpa [s_osea_pre] using
        starts_rhs_projected_suffix_direct ctx h_osea_start h_src_off h_zero
    have h_start_projected :
        ctx.dstOff ≠ 0 →
          StartsAt prog_osea s_osea_pre.pc
            [oseair.Instr.Assgn (dstTmpReg ctx) (oseair.Rhs.MutBorOffset ctx.dstReg ctx.dstOff),
             oseair.Instr.Memcpy (dstTmpReg ctx) (resReg ctx) (innerTy ctx),
             oseair.Instr.Die (dstTmpReg ctx)] := by
      intro h_ne
      simpa [s_osea_pre] using
        starts_rhs_projected_suffix_projected ctx h_osea_start h_src_off h_ne
    have h_target_direct :
        ctx.dstOff = 0 →
          ∃ ap_read_o ap_write_o,
            sb_read s_osea_pre.ap (allocBase_o + 0) allocTag_o = SBResult.Ok ap_read_o ∧
            sb_use_mb ap_read_o (dstBase_o + ctx.dstOff) dstTag_o = SBResult.Ok ap_write_o ∧
            sb_sim ρa ρt ap_write_m ap_write_o := by
      intro _h
      obtain ⟨ap_read_o, h_temp_read⟩ := sb_read_of_find_own h_find_temp_pre
      have h_sb_read :=
        sb_osea_only_read_preserves_sim h_sb_prefix h_temp_unmapped_alloc h_temp_read
      let ⟨ap_write_o, h_write_o, h_sb_write⟩ :=
        sb_use_mb_sim_ok h_sb_read h_dst_addr h_dst_tag h_mir_use
      exact ⟨ap_read_o, ap_write_o,
        by simpa [s_osea_pre, Nat.zero_add] using h_temp_read,
        h_write_o, h_sb_write⟩
    have h_target_projected :
        ctx.dstOff ≠ 0 →
          ∃ tempTag ap_ref_o ap_read_o ap_write_o ap_final_o,
            sb_ref s_osea_pre.ap (dstBase_o + ctx.dstOff) dstTag_o RefOpKind.Mut =
              (SBResult.Ok ap_ref_o, tempTag) ∧
            sb_read ap_ref_o (allocBase_o + 0) allocTag_o = SBResult.Ok ap_read_o ∧
            sb_use_mb ap_read_o (dstBase_o + ctx.dstOff) tempTag = SBResult.Ok ap_write_o ∧
            sb_die ap_write_o (dstBase_o + ctx.dstOff) tempTag = SBResult.Ok ap_final_o ∧
            sb_sim ρa ρt ap_write_m ap_final_o := by
      intro _h
      simpa [s_osea_pre, Nat.zero_add] using
        (sb_ref_mut_read_unmapped_use_die_sim_ok
          (h_sim := h_sb_prefix)
          (h_dst_addr := h_dst_addr)
          (h_dst_tag := h_dst_tag)
          (h_use_m := h_mir_use)
          (h_src_find := h_find_temp_pre)
          (h_src_unmapped := h_temp_unmapped_alloc))
    obtain ⟨s_osea_next, h_steps, h_rest⟩ :=
      existing_memcpy_simulation
        (A_o := oseair.bumpAllocator)
        (ρa := ρa) (ρt := ρt)
        (s_mir := s_mir_pre)
        (s_osea := s_osea_pre)
        (s_mir_next := s_mir_next)
        (prog_osea := prog_osea)
        (srcReg := resReg ctx)
        (dst_reg := ctx.dstReg)
        (tmpReg := dstTmpReg ctx)
        (baseLayout := ctx.dstBaseLayout)
        (subLayout := ctx.innerLayout)
        (srcBase := allocBase_o)
        (srcOff := 0)
        (srcSize := blockSize ctx.innerLayout)
        (srcTag := allocTag_o)
        (dst_base := ctx.dst.base)
        (dst_mir := dstBase_m)
        (dst_osea := dstBase_o)
        (dst_tag_m := dstTag_m)
        (dst_tag_o := dstTag_o)
        (off := ctx.dstOff)
        (vals_mir := mirlite.readWordSeq s_mir.mem targetAddr_m (blockSize ctx.innerLayout))
        (ap_m' := ap_write_m)
        (ptr_sim := ptr_sim)
        h_sim_pre h_noninterference_pre h_dst_pre
        (layoutResolvePath_blockSize_le ctx.h_dst_path)
        h_inner_nonempty
        h_dstTmp_fresh
        h_start_direct h_start_projected
        h_src_reg_pre
        (by simpa [s_osea_pre, Nat.zero_add, oseair_writeWordSeq_addrStart_eq] using h_alloc_lt)
        (by
          exact Nat.lt_of_lt_of_le h_dst_lt_old
            (by simpa [s_osea_pre, oseair_writeWordSeq_addrStart_eq] using h_alloc_le))
        h_res_ne_dstTmp
        (by simp [blockSize, layoutSize])
        h_target_direct h_target_projected
        h_mir_next_pre h_vals
    rcases h_rest with ⟨h_sim_next, h_noninterference_next, h_pc_tail⟩
    exact ⟨s_osea_next,
      StepStarWith.trans (StepStarWith.of_runN_ok h_prefix_run) h_steps,
      h_sim_next,
      h_noninterference_next,
      by
        by_cases h_dst_off : ctx.dstOff = 0
        · simpa [s_osea_pre, DerefProjectedExistingCtx.compiled_eq, h_src_off, h_dst_off, Nat.add_assoc] using
            h_pc_tail
        · simpa [s_osea_pre, DerefProjectedExistingCtx.compiled_eq, h_src_off, h_dst_off, Nat.add_assoc] using
            h_pc_tail⟩

end DerefProjectedExisting

/-! ## Fresh Base Destination -/

structure DerefFreshCtx where
  src : mirlite.Place
  dst : mirlite.Place
  srcReg : Register
  srcBaseLayout : LayoutTy
  innerLayout : LayoutTy
  srcOff : Word
  cs : CompilerState
  h_regs_below : PlaceMapRegsBelowNextReg cs
  h_instrs : CompilerEmpty cs
  h_src_lookup : BaseReady cs src.base srcReg srcBaseLayout
  h_dst_absent : BaseAbsent cs dst.base
  h_src_path : layoutResolvePath srcBaseLayout src.path = some (srcOff, LayoutTy.PtrL innerLayout)
  h_dst_base : dst.path = []

namespace DerefFreshCtx

def stmt (ctx : DerefFreshCtx) : mirlite.Stmt :=
  mirlite.Stmt.Assgn (mirlite.LExpr.Place ctx.dst)
    (mirlite.RExpr.DrefOp ctx.src)

def resReg (ctx : DerefFreshCtx) : Register :=
  Register.R ctx.cs.nextReg

def srcTmpReg (ctx : DerefFreshCtx) : Register :=
  Register.R (ctx.cs.nextReg + 1)

def loadedPtrReg (ctx : DerefFreshCtx) : Register :=
  if ctx.srcOff = 0 then Register.R (ctx.cs.nextReg + 1) else Register.R (ctx.cs.nextReg + 2)

def dstReg (ctx : DerefFreshCtx) : Register :=
  if ctx.srcOff = 0 then Register.R (ctx.cs.nextReg + 2) else Register.R (ctx.cs.nextReg + 3)

def innerTy (ctx : DerefFreshCtx) : TyVal :=
  layoutToTyVal ctx.innerLayout

def compiled (ctx : DerefFreshCtx) : oseair.Prog :=
  if ctx.srcOff = 0 then
    [oseair.Instr.Assgn (ctx.resReg) (oseair.Rhs.Alloc (ctx.innerTy)),
     oseair.Instr.Assgn (ctx.loadedPtrReg) (oseair.Rhs.Load TyVal.PTy ctx.srcReg),
     oseair.Instr.Memcpy (ctx.resReg) (ctx.loadedPtrReg) (ctx.innerTy),
     oseair.Instr.Assgn (ctx.dstReg) (oseair.Rhs.Alloc (ctx.innerTy)),
     oseair.Instr.Memcpy (ctx.dstReg) (ctx.resReg) (ctx.innerTy)]
  else
    [oseair.Instr.Assgn (ctx.resReg) (oseair.Rhs.Alloc (ctx.innerTy)),
     oseair.Instr.Assgn (ctx.srcTmpReg) (oseair.Rhs.BorOffset ctx.srcReg ctx.srcOff),
     oseair.Instr.Assgn (ctx.loadedPtrReg) (oseair.Rhs.Load TyVal.PTy (ctx.srcTmpReg)),
     oseair.Instr.Die (ctx.srcTmpReg),
     oseair.Instr.Memcpy (ctx.resReg) (ctx.loadedPtrReg) (ctx.innerTy),
     oseair.Instr.Assgn (ctx.dstReg) (oseair.Rhs.Alloc (ctx.innerTy)),
     oseair.Instr.Memcpy (ctx.dstReg) (ctx.resReg) (ctx.innerTy)]

def postPlaceMap (ctx : DerefFreshCtx) : PlaceMap :=
  (ctx.dst.base, (ctx.dstReg, ctx.innerLayout)) :: ctx.cs.placeMap

theorem instrs_nil (ctx : DerefFreshCtx) : ctx.cs.instrs = [] :=
  ctx.h_instrs

@[simp] theorem compiled_eq
  (ctx : DerefFreshCtx) :
  (compileStmt ctx.cs (stmt ctx)).instrs = ctx.compiled := by
  let csAlloc : CompilerState :=
    { nextReg := ctx.cs.nextReg + 1,
      placeMap := ctx.cs.placeMap,
      instrs := ctx.cs.instrs ++
        [oseair.Instr.Assgn (ctx.resReg) (oseair.Rhs.Alloc (ctx.innerTy))] }
  have h_src_lookup_alloc :
      getPlaceInfo csAlloc ctx.src.base = some (ctx.srcReg, ctx.srcBaseLayout) := by
    simpa [csAlloc, getPlaceInfo] using ctx.h_src_lookup
  have h_src_place_layout :
      placeLayout? ctx.cs ctx.src = some (LayoutTy.PtrL ctx.innerLayout) := by
    unfold placeLayout?
    rw [ctx.h_src_lookup]
    simp [ctx.h_src_path]
  have h_layout :
      inferRExprLayout ctx.cs (mirlite.RExpr.DrefOp ctx.src) = ctx.innerLayout := by
    simp [inferRExprLayout, h_src_place_layout]
  by_cases h_src_off : ctx.srcOff = 0
  · let rhsCs : CompilerState :=
      { nextReg := ctx.cs.nextReg + 2,
        placeMap := ctx.cs.placeMap,
        instrs := ctx.cs.instrs ++
          [oseair.Instr.Assgn (ctx.resReg) (oseair.Rhs.Alloc (ctx.innerTy)),
           oseair.Instr.Assgn (ctx.loadedPtrReg) (oseair.Rhs.Load TyVal.PTy ctx.srcReg),
           oseair.Instr.Memcpy (ctx.resReg) (ctx.loadedPtrReg) (ctx.innerTy)] }
    have h_src_place :
        placeToReg csAlloc ctx.src mirlite.RefKind.Shared =
          { reg := ctx.srcReg,
            layout := LayoutTy.PtrL ctx.innerLayout,
            cleanup := [],
            cs := csAlloc } := by
      unfold placeToReg
      rw [h_src_lookup_alloc]
      simp [ctx.h_src_path, h_src_off, csAlloc]
    have h_rhs_to :
        compileRExprToFuel 1 csAlloc (ctx.resReg) (mirlite.RExpr.DrefOp ctx.src) = rhsCs := by
      simp [compileRExprToFuel, staticRExprData?]
      rw [h_src_place]
      simp [rhsCs, csAlloc, ctx.instrs_nil, DerefFreshCtx.loadedPtrReg,
        DerefFreshCtx.resReg, DerefFreshCtx.innerTy, freshReg, emit, layoutDeref?, h_src_off]
    have h_rhs :
        compileRExpr ctx.cs (mirlite.RExpr.DrefOp ctx.src) =
          { reg := ctx.resReg, layout := ctx.innerLayout, cs := rhsCs } := by
      simpa [compileRExpr, compileRExprFuel, mirlite.rExprFuel, h_layout, csAlloc, rhsCs,
        ctx.instrs_nil, DerefFreshCtx.resReg, DerefFreshCtx.loadedPtrReg,
        freshReg, emit, h_src_off] using h_rhs_to
    have h_dst_absent_rhs :
        getPlaceInfo rhsCs ctx.dst.base = none := by
      simpa [rhsCs] using ctx.h_dst_absent
    have h_dst_place :
        placeToReg rhsCs ctx.dst mirlite.RefKind.Mut (some ctx.innerLayout) =
          { reg := ctx.dstReg,
            layout := ctx.innerLayout,
            cleanup := [],
            cs :=
              { nextReg := ctx.cs.nextReg + 3,
                placeMap := (ctx.dst.base, (ctx.dstReg, ctx.innerLayout)) :: ctx.cs.placeMap,
                instrs := rhsCs.instrs ++
                  [oseair.Instr.Assgn (ctx.dstReg) (oseair.Rhs.Alloc (ctx.innerTy))] } } := by
      unfold placeToReg
      change
        (match getPlaceInfo rhsCs ctx.dst.base with
        | some (baseReg, baseLayout) =>
            match layoutResolvePath baseLayout ctx.dst.path with
            | some (offset, placeLayout) =>
                if offset = 0 then
                  ({ reg := baseReg, layout := placeLayout, cleanup := [], cs := rhsCs } : PtrResult)
                else
                  let (tmpReg, cs1) := freshReg rhsCs
                  let rhs := oseair.Rhs.MutBorOffset baseReg offset
                  let cs2 := emit cs1 [oseair.Instr.Assgn tmpReg rhs]
                  ({ reg := tmpReg, layout := placeLayout, cleanup := [tmpReg], cs := cs2 } : PtrResult)
            | none =>
                ({ reg := Register.R 0, layout := LayoutTy.NatL, cleanup := [], cs := rhsCs } : PtrResult)
        | none =>
            match some ctx.innerLayout with
            | some baseLayout =>
                if (ctx.dst.path == []) = true then
                  let (newReg, cs1) := freshReg rhsCs
                  let cs2 := emit cs1
                    [oseair.Instr.Assgn newReg (oseair.Rhs.Alloc (layoutToTyVal baseLayout))]
                  let cs3 := setPlace cs2 ctx.dst.base newReg baseLayout
                  ({ reg := newReg, layout := baseLayout, cleanup := [], cs := cs3 } : PtrResult)
                else
                  ({ reg := Register.R 0, layout := baseLayout, cleanup := [], cs := rhsCs } : PtrResult)
            | none =>
                ({ reg := Register.R 0, layout := LayoutTy.NatL, cleanup := [], cs := rhsCs } : PtrResult)) = _
      rw [h_dst_absent_rhs]
      simp [ctx.h_dst_base, rhsCs, DerefFreshCtx.dstReg, DerefFreshCtx.innerTy,
        freshReg, emit, setPlace, h_src_off]
    unfold DerefFreshCtx.stmt compileStmt
    simp [h_rhs]
    rw [h_dst_place]
    simp [DerefFreshCtx.compiled, rhsCs, emit, cleanupInstrs, ctx.instrs_nil,
      DerefFreshCtx.innerTy, h_src_off]
  · let rhsCs : CompilerState :=
      { nextReg := ctx.cs.nextReg + 3,
        placeMap := ctx.cs.placeMap,
        instrs := ctx.cs.instrs ++
          [oseair.Instr.Assgn (ctx.resReg) (oseair.Rhs.Alloc (ctx.innerTy)),
           oseair.Instr.Assgn (ctx.srcTmpReg) (oseair.Rhs.BorOffset ctx.srcReg ctx.srcOff),
           oseair.Instr.Assgn (ctx.loadedPtrReg) (oseair.Rhs.Load TyVal.PTy (ctx.srcTmpReg)),
           oseair.Instr.Die (ctx.srcTmpReg),
           oseair.Instr.Memcpy (ctx.resReg) (ctx.loadedPtrReg) (ctx.innerTy)] }
    have h_src_place :
        placeToReg csAlloc ctx.src mirlite.RefKind.Shared =
          { reg := ctx.srcTmpReg,
            layout := LayoutTy.PtrL ctx.innerLayout,
            cleanup := [ctx.srcTmpReg],
            cs :=
              { nextReg := ctx.cs.nextReg + 2,
                placeMap := ctx.cs.placeMap,
                instrs := ctx.cs.instrs ++
                  [oseair.Instr.Assgn (ctx.resReg) (oseair.Rhs.Alloc (ctx.innerTy)),
                   oseair.Instr.Assgn (ctx.srcTmpReg)
                     (oseair.Rhs.BorOffset ctx.srcReg ctx.srcOff)] } } := by
      unfold placeToReg
      rw [h_src_lookup_alloc]
      simp [ctx.h_src_path, h_src_off, csAlloc, DerefFreshCtx.srcTmpReg, freshReg, emit]
    have h_rhs_to :
        compileRExprToFuel 1 csAlloc (ctx.resReg) (mirlite.RExpr.DrefOp ctx.src) = rhsCs := by
      simp [compileRExprToFuel, staticRExprData?]
      rw [h_src_place]
      simp [rhsCs, ctx.instrs_nil, DerefFreshCtx.innerTy, DerefFreshCtx.srcTmpReg,
        DerefFreshCtx.loadedPtrReg, DerefFreshCtx.resReg, freshReg, emit,
        cleanupInstrs, layoutDeref?, h_src_off]
    have h_rhs :
        compileRExpr ctx.cs (mirlite.RExpr.DrefOp ctx.src) =
          { reg := ctx.resReg, layout := ctx.innerLayout, cs := rhsCs } := by
      simpa [compileRExpr, compileRExprFuel, mirlite.rExprFuel, h_layout, csAlloc, rhsCs,
        ctx.instrs_nil, DerefFreshCtx.srcTmpReg, DerefFreshCtx.loadedPtrReg,
        DerefFreshCtx.resReg, freshReg, emit, cleanupInstrs, h_src_off] using h_rhs_to
    have h_dst_absent_rhs :
        getPlaceInfo rhsCs ctx.dst.base = none := by
      simpa [rhsCs] using ctx.h_dst_absent
    have h_dst_place :
        placeToReg rhsCs ctx.dst mirlite.RefKind.Mut (some ctx.innerLayout) =
          { reg := ctx.dstReg,
            layout := ctx.innerLayout,
            cleanup := [],
            cs :=
              { nextReg := ctx.cs.nextReg + 4,
                placeMap := (ctx.dst.base, (ctx.dstReg, ctx.innerLayout)) :: ctx.cs.placeMap,
                instrs := rhsCs.instrs ++
                  [oseair.Instr.Assgn (ctx.dstReg) (oseair.Rhs.Alloc (ctx.innerTy))] } } := by
      unfold placeToReg
      change
        (match getPlaceInfo rhsCs ctx.dst.base with
        | some (baseReg, baseLayout) =>
            match layoutResolvePath baseLayout ctx.dst.path with
            | some (offset, placeLayout) =>
                if offset = 0 then
                  ({ reg := baseReg, layout := placeLayout, cleanup := [], cs := rhsCs } : PtrResult)
                else
                  let (tmpReg, cs1) := freshReg rhsCs
                  let rhs := oseair.Rhs.MutBorOffset baseReg offset
                  let cs2 := emit cs1 [oseair.Instr.Assgn tmpReg rhs]
                  ({ reg := tmpReg, layout := placeLayout, cleanup := [tmpReg], cs := cs2 } : PtrResult)
            | none =>
                ({ reg := Register.R 0, layout := LayoutTy.NatL, cleanup := [], cs := rhsCs } : PtrResult)
        | none =>
            match some ctx.innerLayout with
            | some baseLayout =>
                if (ctx.dst.path == []) = true then
                  let (newReg, cs1) := freshReg rhsCs
                  let cs2 := emit cs1
                    [oseair.Instr.Assgn newReg (oseair.Rhs.Alloc (layoutToTyVal baseLayout))]
                  let cs3 := setPlace cs2 ctx.dst.base newReg baseLayout
                  ({ reg := newReg, layout := baseLayout, cleanup := [], cs := cs3 } : PtrResult)
                else
                  ({ reg := Register.R 0, layout := baseLayout, cleanup := [], cs := rhsCs } : PtrResult)
            | none =>
                ({ reg := Register.R 0, layout := LayoutTy.NatL, cleanup := [], cs := rhsCs } : PtrResult)) = _
      rw [h_dst_absent_rhs]
      simp [ctx.h_dst_base, rhsCs, DerefFreshCtx.dstReg, DerefFreshCtx.innerTy,
        freshReg, emit, setPlace, h_src_off]
    unfold DerefFreshCtx.stmt compileStmt
    simp [h_rhs]
    rw [h_dst_place]
    simp [DerefFreshCtx.compiled, rhsCs, emit, cleanupInstrs, ctx.instrs_nil,
      DerefFreshCtx.innerTy, h_src_off]

@[simp] theorem rhs_nextReg
  (ctx : DerefFreshCtx) :
  (compileRExpr ctx.cs (mirlite.RExpr.DrefOp ctx.src)).cs.nextReg =
    if ctx.srcOff = 0 then ctx.cs.nextReg + 2 else ctx.cs.nextReg + 3 := by
  let csAlloc : CompilerState :=
    { nextReg := ctx.cs.nextReg + 1,
      placeMap := ctx.cs.placeMap,
      instrs := ctx.cs.instrs ++
        [oseair.Instr.Assgn (ctx.resReg) (oseair.Rhs.Alloc (ctx.innerTy))] }
  have h_src_lookup_alloc :
      getPlaceInfo csAlloc ctx.src.base = some (ctx.srcReg, ctx.srcBaseLayout) := by
    simpa [csAlloc, getPlaceInfo] using ctx.h_src_lookup
  have h_src_place_layout :
      placeLayout? ctx.cs ctx.src = some (LayoutTy.PtrL ctx.innerLayout) := by
    unfold placeLayout?
    rw [ctx.h_src_lookup]
    simp [ctx.h_src_path]
  have h_layout :
      inferRExprLayout ctx.cs (mirlite.RExpr.DrefOp ctx.src) = ctx.innerLayout := by
    simp [inferRExprLayout, h_src_place_layout]
  by_cases h_src_off : ctx.srcOff = 0
  · let rhsCs : CompilerState :=
      { nextReg := ctx.cs.nextReg + 2,
        placeMap := ctx.cs.placeMap,
        instrs := ctx.cs.instrs ++
          [oseair.Instr.Assgn (ctx.resReg) (oseair.Rhs.Alloc (ctx.innerTy)),
           oseair.Instr.Assgn (ctx.loadedPtrReg) (oseair.Rhs.Load TyVal.PTy ctx.srcReg),
           oseair.Instr.Memcpy (ctx.resReg) (ctx.loadedPtrReg) (ctx.innerTy)] }
    have h_src_place :
        placeToReg csAlloc ctx.src mirlite.RefKind.Shared =
          { reg := ctx.srcReg,
            layout := LayoutTy.PtrL ctx.innerLayout,
            cleanup := [],
            cs := csAlloc } := by
      unfold placeToReg
      rw [h_src_lookup_alloc]
      simp [ctx.h_src_path, h_src_off, csAlloc]
    have h_rhs_to :
        compileRExprToFuel 1 csAlloc (ctx.resReg) (mirlite.RExpr.DrefOp ctx.src) = rhsCs := by
      simp [compileRExprToFuel, staticRExprData?]
      rw [h_src_place]
      simp [rhsCs, csAlloc, ctx.instrs_nil, DerefFreshCtx.loadedPtrReg,
        DerefFreshCtx.resReg, DerefFreshCtx.innerTy, freshReg, emit, layoutDeref?, h_src_off]
    have h_rhs :
        compileRExpr ctx.cs (mirlite.RExpr.DrefOp ctx.src) =
          { reg := ctx.resReg, layout := ctx.innerLayout, cs := rhsCs } := by
      simpa [compileRExpr, compileRExprFuel, mirlite.rExprFuel, h_layout, csAlloc, rhsCs,
        ctx.instrs_nil, DerefFreshCtx.resReg, DerefFreshCtx.loadedPtrReg,
        freshReg, emit, h_src_off] using h_rhs_to
    simpa [rhsCs, h_src_off] using congrArg (fun res => res.cs.nextReg) h_rhs
  · let rhsCs : CompilerState :=
      { nextReg := ctx.cs.nextReg + 3,
        placeMap := ctx.cs.placeMap,
        instrs := ctx.cs.instrs ++
          [oseair.Instr.Assgn (ctx.resReg) (oseair.Rhs.Alloc (ctx.innerTy)),
           oseair.Instr.Assgn (ctx.srcTmpReg) (oseair.Rhs.BorOffset ctx.srcReg ctx.srcOff),
           oseair.Instr.Assgn (ctx.loadedPtrReg) (oseair.Rhs.Load TyVal.PTy (ctx.srcTmpReg)),
           oseair.Instr.Die (ctx.srcTmpReg),
           oseair.Instr.Memcpy (ctx.resReg) (ctx.loadedPtrReg) (ctx.innerTy)] }
    have h_src_place :
        placeToReg csAlloc ctx.src mirlite.RefKind.Shared =
          { reg := ctx.srcTmpReg,
            layout := LayoutTy.PtrL ctx.innerLayout,
            cleanup := [ctx.srcTmpReg],
            cs :=
              { nextReg := ctx.cs.nextReg + 2,
                placeMap := ctx.cs.placeMap,
                instrs := ctx.cs.instrs ++
                  [oseair.Instr.Assgn (ctx.resReg) (oseair.Rhs.Alloc (ctx.innerTy)),
                   oseair.Instr.Assgn (ctx.srcTmpReg)
                     (oseair.Rhs.BorOffset ctx.srcReg ctx.srcOff)] } } := by
      unfold placeToReg
      rw [h_src_lookup_alloc]
      simp [ctx.h_src_path, h_src_off, csAlloc, DerefFreshCtx.srcTmpReg, freshReg, emit]
    have h_rhs_to :
        compileRExprToFuel 1 csAlloc (ctx.resReg) (mirlite.RExpr.DrefOp ctx.src) = rhsCs := by
      simp [compileRExprToFuel, staticRExprData?]
      rw [h_src_place]
      simp [rhsCs, ctx.instrs_nil, DerefFreshCtx.innerTy, DerefFreshCtx.srcTmpReg,
        DerefFreshCtx.loadedPtrReg, DerefFreshCtx.resReg, freshReg, emit,
        cleanupInstrs, layoutDeref?, h_src_off]
    have h_rhs :
        compileRExpr ctx.cs (mirlite.RExpr.DrefOp ctx.src) =
          { reg := ctx.resReg, layout := ctx.innerLayout, cs := rhsCs } := by
      simpa [compileRExpr, compileRExprFuel, mirlite.rExprFuel, h_layout, csAlloc, rhsCs,
        ctx.instrs_nil, DerefFreshCtx.srcTmpReg, DerefFreshCtx.loadedPtrReg,
        DerefFreshCtx.resReg, freshReg, emit, cleanupInstrs, h_src_off] using h_rhs_to
    simpa [rhsCs, h_src_off] using congrArg (fun res => res.cs.nextReg) h_rhs

end DerefFreshCtx

namespace DerefFresh

abbrev stmt (ctx : DerefFreshCtx) : mirlite.Stmt :=
  DerefFreshCtx.stmt ctx

abbrev resReg (ctx : DerefFreshCtx) : Register :=
  DerefFreshCtx.resReg ctx

abbrev srcTmpReg (ctx : DerefFreshCtx) : Register :=
  DerefFreshCtx.srcTmpReg ctx

abbrev loadedPtrReg (ctx : DerefFreshCtx) : Register :=
  DerefFreshCtx.loadedPtrReg ctx

abbrev dstReg (ctx : DerefFreshCtx) : Register :=
  DerefFreshCtx.dstReg ctx

abbrev innerTy (ctx : DerefFreshCtx) : TyVal :=
  DerefFreshCtx.innerTy ctx

abbrev postPlaceMap (ctx : DerefFreshCtx) : PlaceMap :=
  DerefFreshCtx.postPlaceMap ctx

abbrev LocalSim
  (ctx : DerefFreshCtx)
  (ρa : AddrRenameMap) (ρt : TagRenameMap)
  (s_mir : mirlite.State) (s_osea : oseair.State)
  (ptr_sim : PtrSimPred := defaultPtrSim) : Prop :=
  StateSim ctx.cs.placeMap ρa ρt s_mir s_osea ptr_sim

theorem starts_direct_instrs
  (ctx : DerefFreshCtx)
  {prog_osea : oseair.Prog}
  {pc : Nat}
  (h_start : StartsAt prog_osea pc (DerefFreshCtx.compiled ctx))
  (h_src_off : ctx.srcOff = 0) :
  prog_osea.get? pc =
      some (oseair.Instr.Assgn (resReg ctx) (oseair.Rhs.Alloc (innerTy ctx))) ∧
    prog_osea.get? (pc + 1) =
      some (oseair.Instr.Assgn (loadedPtrReg ctx) (oseair.Rhs.Load TyVal.PTy ctx.srcReg)) ∧
    prog_osea.get? (pc + 2) =
      some (oseair.Instr.Memcpy (resReg ctx) (loadedPtrReg ctx) (innerTy ctx)) := by
  have h_start_full :
      StartsAt prog_osea pc
        [oseair.Instr.Assgn (resReg ctx) (oseair.Rhs.Alloc (innerTy ctx)),
         oseair.Instr.Assgn (loadedPtrReg ctx) (oseair.Rhs.Load TyVal.PTy ctx.srcReg),
         oseair.Instr.Memcpy (resReg ctx) (loadedPtrReg ctx) (innerTy ctx),
         oseair.Instr.Assgn (dstReg ctx) (oseair.Rhs.Alloc (innerTy ctx)),
         oseair.Instr.Memcpy (dstReg ctx) (resReg ctx) (innerTy ctx)] := by
    simpa [DerefFreshCtx.compiled, h_src_off] using h_start
  have h_start1 := StartsAt.tail h_start_full
  have h_start2 := StartsAt.tail h_start1
  refine ⟨?_, ?_, ?_⟩
  · simpa [DerefFreshCtx.compiled, h_src_off, Nat.zero_add, List.get?] using
      (h_start_full 0 (by decide : 0 < 5)).symm
  ·
    have h_head := h_start1 0 (by decide : 0 < 4)
    simpa [DerefFreshCtx.compiled, h_src_off, Nat.zero_add, List.get?] using
      h_head.symm
  ·
    have h_head := h_start2 0 (by decide : 0 < 3)
    simpa [DerefFreshCtx.compiled, h_src_off, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, List.get?] using
      h_head.symm

theorem starts_projected_instrs
  (ctx : DerefFreshCtx)
  {prog_osea : oseair.Prog}
  {pc : Nat}
  (h_start : StartsAt prog_osea pc (DerefFreshCtx.compiled ctx))
  (h_src_off : ctx.srcOff ≠ 0) :
  prog_osea.get? pc =
      some (oseair.Instr.Assgn (resReg ctx) (oseair.Rhs.Alloc (innerTy ctx))) ∧
    prog_osea.get? (pc + 1) =
      some (oseair.Instr.Assgn (srcTmpReg ctx) (oseair.Rhs.BorOffset ctx.srcReg ctx.srcOff)) ∧
    prog_osea.get? (pc + 2) =
      some (oseair.Instr.Assgn (loadedPtrReg ctx) (oseair.Rhs.Load TyVal.PTy (srcTmpReg ctx))) ∧
    prog_osea.get? (pc + 3) = some (oseair.Instr.Die (srcTmpReg ctx)) ∧
    prog_osea.get? (pc + 4) =
      some (oseair.Instr.Memcpy (resReg ctx) (loadedPtrReg ctx) (innerTy ctx)) := by
  have h_start_full :
      StartsAt prog_osea pc
        [oseair.Instr.Assgn (resReg ctx) (oseair.Rhs.Alloc (innerTy ctx)),
         oseair.Instr.Assgn (srcTmpReg ctx) (oseair.Rhs.BorOffset ctx.srcReg ctx.srcOff),
         oseair.Instr.Assgn (loadedPtrReg ctx) (oseair.Rhs.Load TyVal.PTy (srcTmpReg ctx)),
         oseair.Instr.Die (srcTmpReg ctx),
         oseair.Instr.Memcpy (resReg ctx) (loadedPtrReg ctx) (innerTy ctx),
         oseair.Instr.Assgn (dstReg ctx) (oseair.Rhs.Alloc (innerTy ctx)),
         oseair.Instr.Memcpy (dstReg ctx) (resReg ctx) (innerTy ctx)] := by
    simpa [DerefFreshCtx.compiled, if_neg h_src_off] using h_start
  have h_start1 := StartsAt.tail h_start_full
  have h_start2 := StartsAt.tail h_start1
  have h_start3 := StartsAt.tail h_start2
  have h_start4 := StartsAt.tail h_start3
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [DerefFreshCtx.compiled, if_neg h_src_off, Nat.zero_add, List.get?] using
      (h_start_full 0 (by decide : 0 < 7)).symm
  ·
    have h_head := h_start1 0 (by decide : 0 < 6)
    simpa [DerefFreshCtx.compiled, if_neg h_src_off, Nat.zero_add, List.get?] using
      h_head.symm
  ·
    have h_head := h_start2 0 (by decide : 0 < 5)
    simpa [DerefFreshCtx.compiled, if_neg h_src_off, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, List.get?] using
      h_head.symm
  ·
    have h_head := h_start3 0 (by decide : 0 < 4)
    simpa [DerefFreshCtx.compiled, if_neg h_src_off, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, List.get?] using
      h_head.symm
  ·
    have h_head := h_start4 0 (by decide : 0 < 3)
    simpa [DerefFreshCtx.compiled, if_neg h_src_off, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, List.get?] using
      h_head.symm

theorem starts_direct_suffix
  (ctx : DerefFreshCtx)
  {prog_osea : oseair.Prog}
  {pc : Nat}
  (h_start : StartsAt prog_osea pc (DerefFreshCtx.compiled ctx))
  (h_src_off : ctx.srcOff = 0) :
  StartsAt prog_osea (pc + 3)
    [oseair.Instr.Assgn (dstReg ctx) (oseair.Rhs.Alloc (innerTy ctx)),
     oseair.Instr.Memcpy (dstReg ctx) (resReg ctx) (innerTy ctx)] := by
  have h_start_full :
      StartsAt prog_osea pc
        [oseair.Instr.Assgn (resReg ctx) (oseair.Rhs.Alloc (innerTy ctx)),
         oseair.Instr.Assgn (loadedPtrReg ctx) (oseair.Rhs.Load TyVal.PTy ctx.srcReg),
         oseair.Instr.Memcpy (resReg ctx) (loadedPtrReg ctx) (innerTy ctx),
         oseair.Instr.Assgn (dstReg ctx) (oseair.Rhs.Alloc (innerTy ctx)),
         oseair.Instr.Memcpy (dstReg ctx) (resReg ctx) (innerTy ctx)] := by
    simpa [DerefFreshCtx.compiled, h_src_off] using h_start
  have h_start1 := StartsAt.tail h_start_full
  have h_start2 := StartsAt.tail h_start1
  exact StartsAt.tail h_start2

theorem starts_projected_suffix
  (ctx : DerefFreshCtx)
  {prog_osea : oseair.Prog}
  {pc : Nat}
  (h_start : StartsAt prog_osea pc (DerefFreshCtx.compiled ctx))
  (h_src_off : ctx.srcOff ≠ 0) :
  StartsAt prog_osea (pc + 5)
    [oseair.Instr.Assgn (dstReg ctx) (oseair.Rhs.Alloc (innerTy ctx)),
     oseair.Instr.Memcpy (dstReg ctx) (resReg ctx) (innerTy ctx)] := by
  have h_start_full :
      StartsAt prog_osea pc
        [oseair.Instr.Assgn (resReg ctx) (oseair.Rhs.Alloc (innerTy ctx)),
         oseair.Instr.Assgn (srcTmpReg ctx) (oseair.Rhs.BorOffset ctx.srcReg ctx.srcOff),
         oseair.Instr.Assgn (loadedPtrReg ctx) (oseair.Rhs.Load TyVal.PTy (srcTmpReg ctx)),
         oseair.Instr.Die (srcTmpReg ctx),
         oseair.Instr.Memcpy (resReg ctx) (loadedPtrReg ctx) (innerTy ctx),
         oseair.Instr.Assgn (dstReg ctx) (oseair.Rhs.Alloc (innerTy ctx)),
         oseair.Instr.Memcpy (dstReg ctx) (resReg ctx) (innerTy ctx)] := by
    simpa [DerefFreshCtx.compiled, if_neg h_src_off] using h_start
  have h_start1 := StartsAt.tail h_start_full
  have h_start2 := StartsAt.tail h_start1
  have h_start3 := StartsAt.tail h_start2
  have h_start4 := StartsAt.tail h_start3
  exact StartsAt.tail h_start4

theorem osea_rhs_direct_run_ok
  (ctx : DerefFreshCtx)
  (s_osea : oseair.State)
  (prog_osea : oseair.Prog)
  (srcBase_o srcTag_o : Word)
  (targetBase_o targetOff_o targetSize_o targetTag_o : Word)
  (allocBase_o : Word)
  (allocMem_o : oseair.Mem)
  (allocTag_o : Tag)
  (ap_alloc ap_load ap_memcpy_read ap_memcpy_write : AccessPerms)
  (h_src_off : ctx.srcOff = 0)
  (h_stmt0 :
    prog_osea.get? s_osea.pc =
      some (oseair.Instr.Assgn (resReg ctx) (oseair.Rhs.Alloc (innerTy ctx))))
  (h_stmt1 :
    prog_osea.get? (s_osea.pc + 1) =
      some (oseair.Instr.Assgn (loadedPtrReg ctx) (oseair.Rhs.Load TyVal.PTy ctx.srcReg)))
  (h_stmt2 :
    prog_osea.get? (s_osea.pc + 2) =
      some (oseair.Instr.Memcpy (resReg ctx) (loadedPtrReg ctx) (innerTy ctx)))
  (h_src_reg :
    s_osea.reg.lookup ctx.srcReg =
      some (TyVal.PTy, [oseair.Val.Ptr srcBase_o 0 (blockSize ctx.srcBaseLayout) srcTag_o]))
  (h_src_mem :
    oseair.readWordSeq s_osea.mem (srcBase_o + ctx.srcOff) 1 =
      [oseair.Val.Ptr targetBase_o targetOff_o targetSize_o targetTag_o])
  (h_alloc_pair :
    A_o.alloc s_osea.mem (blockSize ctx.innerLayout) = (allocBase_o, allocMem_o))
  (h_alloc_mMap_o : allocMem_o.mMap = s_osea.mem.mMap)
  (h_alloc : sb_own s_osea.ap allocBase_o = (SBResult.Ok ap_alloc, allocTag_o))
  (h_load :
    sb_read ap_alloc (srcBase_o + ctx.srcOff) srcTag_o = SBResult.Ok ap_load)
  (h_memcpy_read :
    sb_read ap_load (targetBase_o + targetOff_o) targetTag_o = SBResult.Ok ap_memcpy_read)
  (h_memcpy_write :
    sb_use_mb ap_memcpy_read allocBase_o allocTag_o = SBResult.Ok ap_memcpy_write)
  (h_src_fit :
    ctx.srcOff + blockSize (LayoutTy.PtrL ctx.innerLayout) ≤ blockSize ctx.srcBaseLayout)
  (h_target_fit : targetOff_o + blockSize ctx.innerLayout ≤ targetSize_o) :
  oseair.runNWith A_o 3 s_osea prog_osea =
    oseair.Result.Ok
      { s_osea with
        reg :=
          (s_osea.reg.insert (resReg ctx)
            (TyVal.PTy,
              [oseair.Val.Ptr allocBase_o 0 (blockSize ctx.innerLayout) allocTag_o])).insert
            (loadedPtrReg ctx)
            (TyVal.PTy,
              [oseair.Val.Ptr targetBase_o targetOff_o targetSize_o targetTag_o]),
        ap := ap_memcpy_write,
        mem := oseair.writeWordSeq allocMem_o allocBase_o
          (oseair.readWordSeq s_osea.mem (targetBase_o + targetOff_o) (blockSize ctx.innerLayout)),
        pc := s_osea.pc + 3 } := by
  rcases List.get?_eq_some_iff.mp h_stmt0 with ⟨h_pc0, h_get0⟩
  let s1 : oseair.State :=
    { s_osea with
      reg := s_osea.reg.insert (resReg ctx)
        (TyVal.PTy, [oseair.Val.Ptr allocBase_o 0 (blockSize ctx.innerLayout) allocTag_o]),
      mem := allocMem_o,
      ap := ap_alloc,
      pc := s_osea.pc + 1 }
  have h_step0 := oseair.step_Assgn_AllocWith A_o
    s_osea prog_osea (resReg ctx) (innerTy ctx) allocBase_o allocMem_o
    ap_alloc allocTag_o (blockSize ctx.innerLayout)
    h_pc0 h_get0 rfl h_alloc_pair h_alloc
  rcases List.get?_eq_some_iff.mp h_stmt1 with ⟨h_pc1, h_get1⟩
  let s2 : oseair.State :=
    { s1 with
      reg := s1.reg.insert (loadedPtrReg ctx)
        (TyVal.PTy, [oseair.Val.Ptr targetBase_o targetOff_o targetSize_o targetTag_o]),
      ap := ap_load,
      pc := s1.pc + 1 }
  have h_res_ne_loaded : resReg ctx ≠ loadedPtrReg ctx := by
    unfold resReg loadedPtrReg DerefFreshCtx.resReg DerefFreshCtx.loadedPtrReg
    intro h_eq
    have : Register.R ctx.cs.nextReg = Register.R (ctx.cs.nextReg + 1) := by
      simpa [h_src_off] using h_eq
    injection this with h_nat
    exact (Nat.ne_of_lt (Nat.lt_succ_self ctx.cs.nextReg)) h_nat
  have h_src_reg_s1 :
      s1.reg.lookup ctx.srcReg =
        some (TyVal.PTy, [oseair.Val.Ptr srcBase_o 0 (blockSize ctx.srcBaseLayout) srcTag_o]) := by
    have h_src_ne_res : ctx.srcReg ≠ resReg ctx := by
      intro h_eq
      exact (alloc_fresh_reg_of_ge (cs := ctx.cs) ctx.h_regs_below (Nat.le_refl _)
        ctx.src.base ctx.srcBaseLayout)
        (by simpa [resReg, DerefFreshCtx.resReg, h_eq] using ctx.h_src_lookup)
    simpa [s1, h_src_ne_res] using h_src_reg
  have h_ptr_nonempty : 0 < blockSize (LayoutTy.PtrL ctx.innerLayout) := by
    simp [blockSize, layoutSize]
  have h_src_off_lt : ctx.srcOff < blockSize ctx.srcBaseLayout := by
    exact Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right h_ptr_nonempty) h_src_fit
  have h_src_bound : srcBase_o + 0 < srcBase_o + blockSize ctx.srcBaseLayout := by
    simpa [h_src_off, Nat.zero_add] using Nat.add_lt_add_left h_src_off_lt srcBase_o
  have h_load' : sb_read ap_alloc (srcBase_o + 0) srcTag_o = SBResult.Ok ap_load := by
    simpa [h_src_off] using h_load
  have h_step1 := oseair.step_Assgn_LoadWith A_o
    s1 prog_osea (loadedPtrReg ctx) ctx.srcReg TyVal.PTy
    srcBase_o 0 (blockSize ctx.srcBaseLayout) srcTag_o TyVal.PTy ap_load
    h_pc1 h_get1 h_src_reg_s1 h_src_bound h_load'
  have h_s1_read_src :
      oseair.readWordSeq s1.mem (srcBase_o + 0) 1 =
        [oseair.Val.Ptr targetBase_o targetOff_o targetSize_o targetTag_o] := by
    calc
      oseair.readWordSeq s1.mem (srcBase_o + 0) 1
          = oseair.readWordSeq allocMem_o (srcBase_o + 0) 1 := by
              simp [s1]
      _ = oseair.readWordSeq s_osea.mem (srcBase_o + 0) 1 := by
          simpa using oseair_readWordSeq_eq_of_mMap_eq h_alloc_mMap_o (srcBase_o + 0) 1
      _ = [oseair.Val.Ptr targetBase_o targetOff_o targetSize_o targetTag_o] := by
          simpa [h_src_off] using h_src_mem
  have h_s1_read_src_ty :
      oseair.readWordSeq s1.mem (srcBase_o + 0) (typeSize TyVal.PTy) =
        [oseair.Val.Ptr targetBase_o targetOff_o targetSize_o targetTag_o] := by
    simpa using h_s1_read_src
  have h_step1' : oseair.stepWith A_o s1 prog_osea = oseair.Result.Ok s2 := by
    rw [h_s1_read_src_ty] at h_step1
    simpa [s1, s2] using h_step1
  rcases List.get?_eq_some_iff.mp h_stmt2 with ⟨h_pc2, h_get2⟩
  have h_res_reg :
      s2.reg.lookup (resReg ctx) =
        some (TyVal.PTy, [oseair.Val.Ptr allocBase_o 0 (blockSize ctx.innerLayout) allocTag_o]) := by
    simpa [s2, s1, h_res_ne_loaded] using
      show s1.reg.lookup (resReg ctx) =
        some (TyVal.PTy, [oseair.Val.Ptr allocBase_o 0 (blockSize ctx.innerLayout) allocTag_o]) by
          simp [s1]
  have h_loaded_reg :
      s2.reg.lookup (loadedPtrReg ctx) =
        some (TyVal.PTy, [oseair.Val.Ptr targetBase_o targetOff_o targetSize_o targetTag_o]) := by
    simp [s2]
  let s3 : oseair.State :=
    { s_osea with
      reg :=
        (s_osea.reg.insert (resReg ctx)
          (TyVal.PTy,
            [oseair.Val.Ptr allocBase_o 0 (blockSize ctx.innerLayout) allocTag_o])).insert
          (loadedPtrReg ctx)
          (TyVal.PTy,
            [oseair.Val.Ptr targetBase_o targetOff_o targetSize_o targetTag_o]),
      ap := ap_memcpy_write,
      mem := oseair.writeWordSeq allocMem_o allocBase_o
        (oseair.readWordSeq s_osea.mem (targetBase_o + targetOff_o) (blockSize ctx.innerLayout)),
      pc := s_osea.pc + 3 }
  have h_s2_read_target_ty :
      oseair.readWordSeq s2.mem (targetBase_o + targetOff_o) (typeSize (innerTy ctx)) =
        oseair.readWordSeq s_osea.mem (targetBase_o + targetOff_o) (typeSize (innerTy ctx)) := by
    simpa [innerTy, DerefFreshCtx.innerTy, s2, s1] using
      (oseair_readWordSeq_eq_of_mMap_eq h_alloc_mMap_o
        (targetBase_o + targetOff_o) (typeSize (innerTy ctx)))
  have h_step2 := oseair.step_MemcpyWith A_o
    s2 prog_osea (resReg ctx) (loadedPtrReg ctx) (innerTy ctx)
    allocBase_o 0 (blockSize ctx.innerLayout) allocTag_o
    targetBase_o targetOff_o targetSize_o targetTag_o
    ap_memcpy_read ap_memcpy_write
    h_pc2 h_get2 h_res_reg h_loaded_reg
    (by
      simpa [innerTy, DerefFreshCtx.innerTy,
        blockSize_eq_layoutSize, typeSize_layoutToTyVal])
    (by
      simpa [Nat.add_assoc, innerTy, DerefFreshCtx.innerTy,
        blockSize_eq_layoutSize, typeSize_layoutToTyVal] using
        Nat.add_le_add_left h_target_fit targetBase_o)
    h_memcpy_read h_memcpy_write
  have h_step2' : oseair.stepWith A_o s2 prog_osea = oseair.Result.Ok s3 := by
    rw [h_s2_read_target_ty] at h_step2
    simpa [s1, s2, s3, innerTy, DerefFreshCtx.innerTy,
      blockSize_eq_layoutSize, typeSize_layoutToTyVal] using h_step2
  rw [oseair.runNWith_succ]
  rw [h_step0]
  calc
    (match oseair.stepWith A_o s1 prog_osea with
      | oseair.Result.Ok state' =>
          match oseair.stepWith A_o state' prog_osea with
          | oseair.Result.Ok state' => oseair.Result.Ok state'
          | oseair.Result.Err msg => oseair.Result.Err msg
      | oseair.Result.Err msg => oseair.Result.Err msg)
        = (match oseair.Result.Ok s2 with
          | oseair.Result.Ok state' =>
              match oseair.stepWith A_o state' prog_osea with
              | oseair.Result.Ok state' => oseair.Result.Ok state'
              | oseair.Result.Err msg => oseair.Result.Err msg
          | oseair.Result.Err msg => oseair.Result.Err msg) := by
            rw [h_step1']
    _ = (match oseair.stepWith A_o s2 prog_osea with
          | oseair.Result.Ok state' => oseair.Result.Ok state'
          | oseair.Result.Err msg => oseair.Result.Err msg) := by
            rfl
    _ = (match oseair.Result.Ok s3 with
          | oseair.Result.Ok state' => oseair.Result.Ok state'
          | oseair.Result.Err msg => oseair.Result.Err msg) := by
            rw [h_step2']
    _ = _ := by
            rfl

theorem osea_rhs_projected_run_ok
  (ctx : DerefFreshCtx)
  (s_osea : oseair.State)
  (prog_osea : oseair.Prog)
  (srcBase_o srcTag_o srcTempTag_o : Word)
  (targetBase_o targetOff_o targetSize_o targetTag_o : Word)
  (allocBase_o : Word)
  (allocMem_o : oseair.Mem)
  (allocTag_o : Tag)
  (ap_alloc ap_src_ref ap_load ap_load_final ap_memcpy_read ap_memcpy_write : AccessPerms)
  (h_src_off : ctx.srcOff ≠ 0)
  (h_stmt0 :
    prog_osea.get? s_osea.pc =
      some (oseair.Instr.Assgn (resReg ctx) (oseair.Rhs.Alloc (innerTy ctx))))
  (h_stmt1 :
    prog_osea.get? (s_osea.pc + 1) =
      some (oseair.Instr.Assgn (srcTmpReg ctx) (oseair.Rhs.BorOffset ctx.srcReg ctx.srcOff)))
  (h_stmt2 :
    prog_osea.get? (s_osea.pc + 2) =
      some (oseair.Instr.Assgn (loadedPtrReg ctx) (oseair.Rhs.Load TyVal.PTy (srcTmpReg ctx))))
  (h_stmt3 :
    prog_osea.get? (s_osea.pc + 3) = some (oseair.Instr.Die (srcTmpReg ctx)))
  (h_stmt4 :
    prog_osea.get? (s_osea.pc + 4) =
      some (oseair.Instr.Memcpy (resReg ctx) (loadedPtrReg ctx) (innerTy ctx)))
  (h_src_reg :
    s_osea.reg.lookup ctx.srcReg =
      some (TyVal.PTy, [oseair.Val.Ptr srcBase_o 0 (blockSize ctx.srcBaseLayout) srcTag_o]))
  (h_src_mem :
    oseair.readWordSeq s_osea.mem (srcBase_o + ctx.srcOff) 1 =
      [oseair.Val.Ptr targetBase_o targetOff_o targetSize_o targetTag_o])
  (h_alloc_pair :
    A_o.alloc s_osea.mem (blockSize ctx.innerLayout) = (allocBase_o, allocMem_o))
  (h_alloc_mMap_o : allocMem_o.mMap = s_osea.mem.mMap)
  (h_alloc : sb_own s_osea.ap allocBase_o = (SBResult.Ok ap_alloc, allocTag_o))
  (h_ref :
    sb_ref ap_alloc (srcBase_o + ctx.srcOff) srcTag_o RefOpKind.Shared =
      (SBResult.Ok ap_src_ref, srcTempTag_o))
  (h_load :
    sb_read ap_src_ref (srcBase_o + ctx.srcOff) srcTempTag_o = SBResult.Ok ap_load)
  (h_die :
    sb_die ap_load (srcBase_o + ctx.srcOff) srcTempTag_o = SBResult.Ok ap_load_final)
  (h_memcpy_read :
    sb_read ap_load_final (targetBase_o + targetOff_o) targetTag_o = SBResult.Ok ap_memcpy_read)
  (h_memcpy_write :
    sb_use_mb ap_memcpy_read allocBase_o allocTag_o = SBResult.Ok ap_memcpy_write)
  (h_src_fit :
    ctx.srcOff + blockSize (LayoutTy.PtrL ctx.innerLayout) ≤ blockSize ctx.srcBaseLayout)
  (h_target_fit : targetOff_o + blockSize ctx.innerLayout ≤ targetSize_o) :
  oseair.runNWith A_o 5 s_osea prog_osea =
    oseair.Result.Ok
      { s_osea with
        reg :=
          ((s_osea.reg.insert (resReg ctx)
            (TyVal.PTy,
              [oseair.Val.Ptr allocBase_o 0 (blockSize ctx.innerLayout) allocTag_o])).insert
            (srcTmpReg ctx)
            (TyVal.PTy,
              [oseair.Val.Ptr srcBase_o ctx.srcOff (blockSize ctx.srcBaseLayout) srcTempTag_o])).insert
            (loadedPtrReg ctx)
            (TyVal.PTy,
              [oseair.Val.Ptr targetBase_o targetOff_o targetSize_o targetTag_o]),
        ap := ap_memcpy_write,
        mem := oseair.writeWordSeq allocMem_o allocBase_o
          (oseair.readWordSeq s_osea.mem (targetBase_o + targetOff_o) (blockSize ctx.innerLayout)),
        pc := s_osea.pc + 5 } := by
  rcases List.get?_eq_some_iff.mp h_stmt0 with ⟨h_pc0, h_get0⟩
  let s1 : oseair.State :=
    { s_osea with
      reg := s_osea.reg.insert (resReg ctx)
        (TyVal.PTy, [oseair.Val.Ptr allocBase_o 0 (blockSize ctx.innerLayout) allocTag_o]),
      mem := allocMem_o,
      ap := ap_alloc,
      pc := s_osea.pc + 1 }
  have h_step0 := oseair.step_Assgn_AllocWith A_o
    s_osea prog_osea (resReg ctx) (innerTy ctx) allocBase_o allocMem_o
    ap_alloc allocTag_o (blockSize ctx.innerLayout)
    h_pc0 h_get0 rfl h_alloc_pair h_alloc
  rcases List.get?_eq_some_iff.mp h_stmt1 with ⟨h_pc1, h_get1⟩
  let s2 : oseair.State :=
    { s_osea with
      reg :=
        (s_osea.reg.insert (resReg ctx)
          (TyVal.PTy, [oseair.Val.Ptr allocBase_o 0 (blockSize ctx.innerLayout) allocTag_o])).insert
          (srcTmpReg ctx)
          (TyVal.PTy,
            [oseair.Val.Ptr srcBase_o ctx.srcOff (blockSize ctx.srcBaseLayout) srcTempTag_o]),
      mem := allocMem_o,
      ap := ap_src_ref,
      pc := s_osea.pc + 2 }
  have h_off_lt : ctx.srcOff < blockSize ctx.srcBaseLayout := by
    exact Nat.lt_of_lt_of_le
      (Nat.lt_add_of_pos_right (by simp [blockSize, layoutSize]))
      h_src_fit
  have h_src_bound : srcBase_o + 0 + ctx.srcOff < srcBase_o + blockSize ctx.srcBaseLayout := by
    simpa [Nat.zero_add] using Nat.add_lt_add_left h_off_lt srcBase_o
  have h_src_reg_s1 :
      s1.reg.lookup ctx.srcReg =
        some (TyVal.PTy, [oseair.Val.Ptr srcBase_o 0 (blockSize ctx.srcBaseLayout) srcTag_o]) := by
    have h_src_ne_res : ctx.srcReg ≠ resReg ctx := by
      intro h_eq
      exact (alloc_fresh_reg_of_ge (cs := ctx.cs) ctx.h_regs_below (Nat.le_refl _)
        ctx.src.base ctx.srcBaseLayout)
        (by simpa [resReg, DerefFreshCtx.resReg, h_eq] using ctx.h_src_lookup)
    simpa [s1, h_src_ne_res] using h_src_reg
  have h_step1 := step_Assgn_BorOffsetWith A_o s1 prog_osea (srcTmpReg ctx) ctx.srcReg ctx.srcOff
    srcBase_o 0 (blockSize ctx.srcBaseLayout) srcTag_o ap_src_ref srcTempTag_o
    h_pc1 h_get1 h_src_reg_s1 h_src_bound h_ref
  have h_step1' : oseair.stepWith A_o s1 prog_osea = oseair.Result.Ok s2 := by
    simpa [s1, s2] using h_step1
  rcases List.get?_eq_some_iff.mp h_stmt2 with ⟨h_pc2, h_get2⟩
  let s3 : oseair.State :=
    { s_osea with
      reg :=
        ((s_osea.reg.insert (resReg ctx)
          (TyVal.PTy, [oseair.Val.Ptr allocBase_o 0 (blockSize ctx.innerLayout) allocTag_o])).insert
          (srcTmpReg ctx)
          (TyVal.PTy,
            [oseair.Val.Ptr srcBase_o ctx.srcOff (blockSize ctx.srcBaseLayout) srcTempTag_o])).insert
          (loadedPtrReg ctx)
          (TyVal.PTy, [oseair.Val.Ptr targetBase_o targetOff_o targetSize_o targetTag_o]),
      mem := allocMem_o,
      ap := ap_load,
      pc := s_osea.pc + 3 }
  have h_tmp_ne_loaded : srcTmpReg ctx ≠ loadedPtrReg ctx := by
    intro h_eq
    unfold srcTmpReg loadedPtrReg DerefFreshCtx.srcTmpReg
      DerefFreshCtx.loadedPtrReg at h_eq
    by_cases h_zero : ctx.srcOff = 0
    · simp [h_zero] at h_eq
      exact h_src_off h_zero
    · have h_reg : Register.R (ctx.cs.nextReg + 1) = Register.R (ctx.cs.nextReg + 2) := by
        simpa [h_zero] using h_eq
      injection h_reg with h_nat
      exact (Nat.ne_of_lt (Nat.lt_succ_self (ctx.cs.nextReg + 1))) h_nat
  have h_srcTmp_reg :
      s2.reg.lookup (srcTmpReg ctx) =
        some (TyVal.PTy,
          [oseair.Val.Ptr srcBase_o ctx.srcOff (blockSize ctx.srcBaseLayout) srcTempTag_o]) := by
    simp [s2]
  have h_s2_read_src :
      oseair.readWordSeq s2.mem (srcBase_o + ctx.srcOff) 1 =
        [oseair.Val.Ptr targetBase_o targetOff_o targetSize_o targetTag_o] := by
    calc
      oseair.readWordSeq s2.mem (srcBase_o + ctx.srcOff) 1
          = oseair.readWordSeq allocMem_o (srcBase_o + ctx.srcOff) 1 := by
              simp [s2]
      _ = oseair.readWordSeq s_osea.mem (srcBase_o + ctx.srcOff) 1 := by
          simpa using oseair_readWordSeq_eq_of_mMap_eq h_alloc_mMap_o (srcBase_o + ctx.srcOff) 1
      _ = [oseair.Val.Ptr targetBase_o targetOff_o targetSize_o targetTag_o] := h_src_mem
  have h_step2 := oseair.step_Assgn_LoadWith A_o
    s2 prog_osea (loadedPtrReg ctx) (srcTmpReg ctx) TyVal.PTy
    srcBase_o ctx.srcOff (blockSize ctx.srcBaseLayout) srcTempTag_o TyVal.PTy ap_load
    h_pc2 h_get2 h_srcTmp_reg h_src_bound h_load
  have h_s2_read_src_ty :
      oseair.readWordSeq allocMem_o (srcBase_o + ctx.srcOff) (typeSize TyVal.PTy) =
        [oseair.Val.Ptr targetBase_o targetOff_o targetSize_o targetTag_o] := by
    simpa [s2] using h_s2_read_src
  have h_step2' : oseair.stepWith A_o s2 prog_osea = oseair.Result.Ok s3 := by
    rw [h_s2_read_src_ty] at h_step2
    simpa [s2, s3] using h_step2
  rcases List.get?_eq_some_iff.mp h_stmt3 with ⟨h_pc3, h_get3⟩
  let s4 : oseair.State :=
    { s_osea with
      reg :=
        ((s_osea.reg.insert (resReg ctx)
          (TyVal.PTy, [oseair.Val.Ptr allocBase_o 0 (blockSize ctx.innerLayout) allocTag_o])).insert
          (srcTmpReg ctx)
          (TyVal.PTy,
            [oseair.Val.Ptr srcBase_o ctx.srcOff (blockSize ctx.srcBaseLayout) srcTempTag_o])).insert
          (loadedPtrReg ctx)
          (TyVal.PTy, [oseair.Val.Ptr targetBase_o targetOff_o targetSize_o targetTag_o]),
      mem := allocMem_o,
      ap := ap_load_final,
      pc := s_osea.pc + 4 }
  have h_tmp_reg3 :
      s3.reg.lookup (srcTmpReg ctx) =
        some (TyVal.PTy, [oseair.Val.Ptr srcBase_o ctx.srcOff (blockSize ctx.srcBaseLayout) srcTempTag_o]) := by
    simpa [s3, s2, h_tmp_ne_loaded] using h_srcTmp_reg
  have h_step3 := oseair.step_DieWith A_o
    s3 prog_osea (srcTmpReg ctx)
    srcBase_o ctx.srcOff (blockSize ctx.srcBaseLayout) srcTempTag_o ap_load_final
    h_pc3 h_get3 h_tmp_reg3 h_die
  have h_step3' : oseair.stepWith A_o s3 prog_osea = oseair.Result.Ok s4 := by
    simpa [s3, s4] using h_step3
  rcases List.get?_eq_some_iff.mp h_stmt4 with ⟨h_pc4, h_get4⟩
  have h_res_reg :
      s4.reg.lookup (resReg ctx) =
        some (TyVal.PTy, [oseair.Val.Ptr allocBase_o 0 (blockSize ctx.innerLayout) allocTag_o]) := by
    have h_res_ne_srcTmp : resReg ctx ≠ srcTmpReg ctx := by
      intro h_eq
      unfold resReg srcTmpReg DerefFreshCtx.resReg DerefFreshCtx.srcTmpReg at h_eq
      injection h_eq with h_nat
      exact (Nat.ne_of_lt (Nat.lt_succ_self ctx.cs.nextReg)) h_nat
    have h_res_ne_loaded : resReg ctx ≠ loadedPtrReg ctx := by
      intro h_eq
      unfold resReg loadedPtrReg DerefFreshCtx.resReg
        DerefFreshCtx.loadedPtrReg at h_eq
      by_cases h_zero : ctx.srcOff = 0
      · simp [h_zero] at h_eq
      · have h_reg : Register.R ctx.cs.nextReg = Register.R (ctx.cs.nextReg + 2) := by
          simpa [h_zero] using h_eq
        injection h_reg with h_nat
        have h_ne : ctx.cs.nextReg ≠ ctx.cs.nextReg + 2 :=
          Nat.ne_of_lt (Nat.lt_succ_of_lt (Nat.lt_succ_self ctx.cs.nextReg))
        exact h_ne h_nat
    simp [s4, h_res_ne_srcTmp, h_res_ne_loaded]
  have h_loaded_reg :
      s4.reg.lookup (loadedPtrReg ctx) =
        some (TyVal.PTy, [oseair.Val.Ptr targetBase_o targetOff_o targetSize_o targetTag_o]) := by
    simp [s4]
  have h_step4 := oseair.step_MemcpyWith A_o
    s4 prog_osea (resReg ctx) (loadedPtrReg ctx) (innerTy ctx)
    allocBase_o 0 (blockSize ctx.innerLayout) allocTag_o
    targetBase_o targetOff_o targetSize_o targetTag_o
    ap_memcpy_read ap_memcpy_write
    h_pc4 h_get4 h_res_reg h_loaded_reg
    (by simp [innerTy, DerefFreshCtx.innerTy, blockSize])
    (by
      simpa [Nat.add_assoc, innerTy, DerefFreshCtx.innerTy,
        blockSize_eq_layoutSize, typeSize_layoutToTyVal] using
        Nat.add_le_add_left h_target_fit targetBase_o)
    h_memcpy_read h_memcpy_write
  have h_run_tail :
      (match oseair.stepWith A_o s1 prog_osea with
      | oseair.Result.Ok state' =>
          match oseair.stepWith A_o state' prog_osea with
          | oseair.Result.Ok state' =>
              match oseair.stepWith A_o state' prog_osea with
              | oseair.Result.Ok state' =>
                  match oseair.stepWith A_o state' prog_osea with
                  | oseair.Result.Ok state' => oseair.Result.Ok state'
                  | oseair.Result.Err msg => oseair.Result.Err msg
              | oseair.Result.Err msg => oseair.Result.Err msg
          | oseair.Result.Err msg => oseair.Result.Err msg
      | oseair.Result.Err msg => oseair.Result.Err msg) =
        oseair.Result.Ok
          { s_osea with
            reg :=
              ((s_osea.reg.insert (resReg ctx)
                (TyVal.PTy,
                  [oseair.Val.Ptr allocBase_o 0 (blockSize ctx.innerLayout) allocTag_o])).insert
                (srcTmpReg ctx)
                (TyVal.PTy,
                  [oseair.Val.Ptr srcBase_o ctx.srcOff (blockSize ctx.srcBaseLayout) srcTempTag_o])).insert
                (loadedPtrReg ctx)
                (TyVal.PTy,
                  [oseair.Val.Ptr targetBase_o targetOff_o targetSize_o targetTag_o]),
            ap := ap_memcpy_write,
            mem := oseair.writeWordSeq allocMem_o allocBase_o
              (oseair.readWordSeq s_osea.mem (targetBase_o + targetOff_o) (blockSize ctx.innerLayout)),
            pc := s_osea.pc + 5 } := by
    calc
      (match oseair.stepWith A_o s1 prog_osea with
      | oseair.Result.Ok state' =>
          match oseair.stepWith A_o state' prog_osea with
          | oseair.Result.Ok state' =>
              match oseair.stepWith A_o state' prog_osea with
              | oseair.Result.Ok state' =>
                  match oseair.stepWith A_o state' prog_osea with
                  | oseair.Result.Ok state' => oseair.Result.Ok state'
                  | oseair.Result.Err msg => oseair.Result.Err msg
              | oseair.Result.Err msg => oseair.Result.Err msg
          | oseair.Result.Err msg => oseair.Result.Err msg
      | oseair.Result.Err msg => oseair.Result.Err msg)
          = (match oseair.stepWith A_o s2 prog_osea with
            | oseair.Result.Ok state' =>
                match oseair.stepWith A_o state' prog_osea with
                | oseair.Result.Ok state' =>
                    match oseair.stepWith A_o state' prog_osea with
                    | oseair.Result.Ok state' => oseair.Result.Ok state'
                    | oseair.Result.Err msg => oseair.Result.Err msg
                | oseair.Result.Err msg => oseair.Result.Err msg
            | oseair.Result.Err msg => oseair.Result.Err msg) := by
              rw [h_step1']
      _ = (match oseair.stepWith A_o s3 prog_osea with
            | oseair.Result.Ok state' =>
                match oseair.stepWith A_o state' prog_osea with
                | oseair.Result.Ok state' => oseair.Result.Ok state'
                | oseair.Result.Err msg => oseair.Result.Err msg
            | oseair.Result.Err msg => oseair.Result.Err msg) := by
              rw [h_step2']
      _ = (match oseair.stepWith A_o s4 prog_osea with
            | oseair.Result.Ok state' => oseair.Result.Ok state'
            | oseair.Result.Err msg => oseair.Result.Err msg) := by
              rw [h_step3']
      _ = _ := by
            have h_read_eq :
                oseair.readWordSeq allocMem_o (targetBase_o + targetOff_o) (layoutSize ctx.innerLayout) =
                  oseair.readWordSeq s_osea.mem (targetBase_o + targetOff_o) (layoutSize ctx.innerLayout) := by
              simpa [blockSize_eq_layoutSize] using
                (oseair_readWordSeq_eq_of_mMap_eq h_alloc_mMap_o
                  (targetBase_o + targetOff_o) (blockSize ctx.innerLayout))
            rw [h_step4]
            simp [s4, innerTy, DerefFreshCtx.innerTy, blockSize_eq_layoutSize,
              typeSize_layoutToTyVal]
            exact congrArg (oseair.writeWordSeq allocMem_o allocBase_o) h_read_eq
  have h_run4 :
      oseair.runNWith A_o 4 s1 prog_osea =
        oseair.Result.Ok
          { s_osea with
            reg :=
              ((s_osea.reg.insert (resReg ctx)
                (TyVal.PTy,
                  [oseair.Val.Ptr allocBase_o 0 (blockSize ctx.innerLayout) allocTag_o])).insert
                (srcTmpReg ctx)
                (TyVal.PTy,
                  [oseair.Val.Ptr srcBase_o ctx.srcOff (blockSize ctx.srcBaseLayout) srcTempTag_o])).insert
                (loadedPtrReg ctx)
                (TyVal.PTy,
                  [oseair.Val.Ptr targetBase_o targetOff_o targetSize_o targetTag_o]),
            ap := ap_memcpy_write,
            mem := oseair.writeWordSeq allocMem_o allocBase_o
              (oseair.readWordSeq s_osea.mem (targetBase_o + targetOff_o) (blockSize ctx.innerLayout)),
            pc := s_osea.pc + 5 } := by
    simpa [s1, oseair.runNWith_succ, oseair.runNWith_zero] using h_run_tail
  rw [oseair.runNWith_succ]
  rw [h_step0]
  exact h_run4

theorem mirlite_step_inv
  (ctx : DerefFreshCtx)
  (s_mir s_mir_next : mirlite.State)
  (prog_mir : mirlite.Prog)
  (srcBaseAddr srcTag : Word)
  (h_src_env :
    s_mir.env.lookup ctx.src.base =
      some (srcBaseAddr, layoutToTyVal ctx.srcBaseLayout, srcTag))
  (h_dst_env : s_mir.env.lookup ctx.dst.base = none)
  (h_start : StartsAt prog_mir s_mir.pc [stmt ctx])
  (h_step : mirlite.stepWith A_m s_mir prog_mir = mirlite.Result.Ok s_mir_next) :
  ∃ (ap_src_read : AccessPerms)
    (q : mirlite.Place) (gq : Tag) (targetRes : mirlite.PlaceRes)
    (ap_target_read : AccessPerms)
    (freshAddr : Word) (allocMem : mirlite.Mem)
    (freshTag : Tag) (ap_alloc ap_write : AccessPerms),
    sb_read s_mir.ap (srcBaseAddr + ctx.srcOff) srcTag = SBResult.Ok ap_src_read ∧
    s_mir.mem.find? (srcBaseAddr + ctx.srcOff) = some (mirlite.MemValue.PlaceTag q gq) ∧
    mirlite.resolveDirectPlace { s_mir with ap := ap_src_read } q =
      (mirlite.Result.Ok { s_mir with ap := ap_src_read }, targetRes) ∧
    sb_read ap_src_read targetRes.addr gq = SBResult.Ok ap_target_read ∧
    A_m.alloc s_mir.mem (typeSize targetRes.ty) = (freshAddr, allocMem) ∧
    allocMem.mMap = s_mir.mem.mMap ∧
    sb_own ap_target_read freshAddr = (SBResult.Ok ap_alloc, freshTag) ∧
    sb_use_mb ap_alloc freshAddr freshTag = SBResult.Ok ap_write ∧
    s_mir_next =
      { s_mir with
        env := s_mir.env.insert ctx.dst.base (freshAddr, targetRes.ty, freshTag),
        mem := mirlite.writeWordSeq allocMem freshAddr
          (mirlite.readWordSeq s_mir.mem targetRes.addr (typeSize targetRes.ty)),
        ap := ap_write,
        pc := s_mir.pc + 1 } := by
  have h_stmt_mir : prog_mir.get? s_mir.pc = some (derefStmt ctx.src ctx.dst) := by
    simpa [stmt, DerefFreshCtx.stmt, derefStmt] using (StartsAt.singleton h_start)
  rcases List.get?_eq_some_iff.mp h_stmt_mir with ⟨h_pc_mir, h_get_mir⟩
  unfold mirlite.stepWith at h_step
  rw [dif_pos h_pc_mir, h_get_mir] at h_step
  simp [derefStmt, mirlite.stepAssignGenericWith, mirlite.evalRExpr] at h_step
  unfold mirlite.resolvePlace at h_step
  rw [resolveDirectPlace_eq_of_env_lookup h_src_env ctx.h_src_path] at h_step
  cases h_src_read : sb_read s_mir.ap (srcBaseAddr + ctx.srcOff) srcTag with
  | Err _ =>
      simp [h_src_read] at h_step
  | Ok ap_src_read =>
      simp [h_src_read] at h_step
      cases h_src_find : s_mir.mem.find? (srcBaseAddr + ctx.srcOff) with
      | none =>
          simp [mirlite.readWordSeq, h_src_find] at h_step
      | some v =>
          cases v with
          | Undef =>
              simp [mirlite.readWordSeq, h_src_find] at h_step
          | Val n =>
              simp [mirlite.readWordSeq, h_src_find] at h_step
          | PlaceTag q gq =>
              simp [mirlite.readWordSeq, h_src_find] at h_step
              cases h_resolve :
                mirlite.resolveDirectPlace { s_mir with ap := ap_src_read } q with
              | mk res resTarget =>
                  cases res with
                  | Err _ =>
                      simp [mirlite.resolvePlace, h_resolve] at h_step
                  | Ok s_res =>
                      have hs_res : s_res = { s_mir with ap := ap_src_read } :=
                        DerefExisting.resolveDirectPlace_ok_state_eq h_resolve
                      cases hs_res
                      simp [mirlite.resolvePlace, h_resolve] at h_step
                      cases h_target_read : sb_read ap_src_read resTarget.addr gq with
                      | Err _ =>
                          simp [h_target_read] at h_step
                      | Ok ap_target_read =>
                          simp [h_target_read] at h_step
                          have h_dst_env' :
                              { s_mir with ap := ap_target_read }.env.lookup ctx.dst.base = none := by
                            simpa using h_dst_env
                          unfold mirlite.finishPlaceAssignWith at h_step
                          rw [h_dst_env'] at h_step
                          simp [ctx.h_dst_base] at h_step
                          unfold mirlite.allocateBaseAndWriteWith at h_step
                          let freshAddr := (A_m.alloc s_mir.mem (typeSize resTarget.ty)).1
                          let allocMem := (A_m.alloc s_mir.mem (typeSize resTarget.ty)).2
                          have h_alloc_pair :
                              A_m.alloc s_mir.mem (typeSize resTarget.ty) = (freshAddr, allocMem) := by
                            simp [freshAddr, allocMem]
                          have h_alloc_mMap : allocMem.mMap = s_mir.mem.mMap := by
                            simpa [h_alloc_pair] using
                              A_m.alloc_mMap_eq s_mir.mem (typeSize resTarget.ty)
                          rw [h_alloc_pair] at h_step
                          cases h_own : sb_own ap_target_read freshAddr with
                          | mk ownRes freshTag =>
                              cases ownRes with
                              | Err _ =>
                                  simp [h_own] at h_step
                              | Ok ap_alloc =>
                                  simp [h_own] at h_step
                                  cases h_use : sb_use_mb ap_alloc freshAddr freshTag with
                                  | Err _ =>
                                      simp [h_use] at h_step
                                  | Ok ap_write =>
                                      refine ⟨ap_src_read, q, gq, resTarget, ap_target_read,
                                        freshAddr, allocMem, freshTag, ap_alloc, ap_write,
                                        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                                      · rfl
                                      · rfl
                                      · exact h_resolve
                                      · exact h_target_read
                                      · exact h_alloc_pair
                                      · exact h_alloc_mMap
                                      · exact h_own
                                      · exact h_use
                                      · simpa [h_use] using h_step.symm

theorem finish_from_pre
  (ctx : DerefFreshCtx)
  {ρa : AddrRenameMap}
  {ρt : TagRenameMap}
  {ptr_sim : PtrSimPred}
  {s_mir_pre s_mir_next : mirlite.State}
  {s_osea_pre : oseair.State}
  {prog_osea : oseair.Prog}
  {vals_mir : List mirlite.MemValue}
  {freshAddr_m : Word}
  {allocMem_m : mirlite.Mem}
  {freshTag_m : Tag}
  {ap_alloc_m ap_write_m : AccessPerms}
  {tempBase_o tempTag_o : Word}
  (h_sim_pre : StateSim ctx.cs.placeMap ρa ρt s_mir_pre s_osea_pre ptr_sim)
  (h_noninterference_pre : TargetNonInterference ρa s_osea_pre)
  (h_source_below_pre : SourceBlocksBelowAddrStart ctx.cs.placeMap s_mir_pre)
  (h_tag_fresh_pre : ∀ tag, freshTag_m ≤ tag → ρt tag = none)
  (h_temp_unmapped : ∀ a, ρa a ≠ some tempBase_o)
  (h_find_temp_pre : s_osea_pre.ap.StackMap.find? tempBase_o = some [RefKind.Own tempTag_o])
  (h_start :
    StartsAt prog_osea s_osea_pre.pc
      [oseair.Instr.Assgn (dstReg ctx) (oseair.Rhs.Alloc (innerTy ctx)),
       oseair.Instr.Memcpy (dstReg ctx) (resReg ctx) (innerTy ctx)])
  (h_src_reg_pre :
    s_osea_pre.reg.lookup (resReg ctx) =
      some (TyVal.PTy, [oseair.Val.Ptr tempBase_o 0 (blockSize ctx.innerLayout) tempTag_o]))
  (h_dstReg_fresh :
    ∀ base layout, ctx.cs.placeMap.lookup base = some (dstReg ctx, layout) → False)
  (h_own_m : sb_own s_mir_pre.ap freshAddr_m = (SBResult.Ok ap_alloc_m, freshTag_m))
  (h_use_m : sb_use_mb ap_alloc_m freshAddr_m freshTag_m = SBResult.Ok ap_write_m)
  (h_alloc_mMap_m : allocMem_m.mMap = s_mir_pre.mem.mMap)
  (h_alloc_base_m : freshAddr_m = s_mir_pre.mem.addrStart)
  (h_alloc_base :
    (A_o.alloc s_osea_pre.mem (blockSize ctx.innerLayout)).1 = s_osea_pre.mem.addrStart)
  (h_alloc_addrStart :
    (A_o.alloc s_osea_pre.mem (blockSize ctx.innerLayout)).2.addrStart =
      s_osea_pre.mem.addrStart + blockSize ctx.innerLayout)
  (h_inner_nonempty : 0 < blockSize ctx.innerLayout)
  (h_next_full :
    s_mir_next =
      { s_mir_pre with
        env := s_mir_pre.env.insert ctx.dst.base (freshAddr_m, layoutToTyVal ctx.innerLayout, freshTag_m),
        mem := mirlite.writeWordSeq allocMem_m freshAddr_m vals_mir,
        ap := ap_write_m,
        pc := s_mir_pre.pc + 1 })
  (h_vals :
    mem_vals_eq ptr_sim vals_mir
      (oseair.readWordSeq s_osea_pre.mem tempBase_o (blockSize ctx.innerLayout)))
  (h_len : vals_mir.length = blockSize ctx.innerLayout) :
  ∃ allocBase_o freshTag_o ρa' ρt' s_osea_next,
    ρa' = extendAddrRenameMap ρa freshAddr_m allocBase_o ∧
    ρt' = extendTagRenameMap ρt freshTag_m freshTag_o ∧
    StepStarWith A_o s_osea_pre prog_osea s_osea_next ∧
    StateSim (postPlaceMap ctx) ρa' ρt' s_mir_next s_osea_next ptr_sim ∧
    TargetNonInterference ρa' s_osea_next ∧
    s_osea_next.pc = s_osea_pre.pc + 2 := by
  let allocBase_o := (A_o.alloc s_osea_pre.mem (blockSize ctx.innerLayout)).1
  let allocMem_o := (A_o.alloc s_osea_pre.mem (blockSize ctx.innerLayout)).2
  have h_alloc_pair :
      A_o.alloc s_osea_pre.mem (blockSize ctx.innerLayout) = (allocBase_o, allocMem_o) := by
    simp [allocBase_o, allocMem_o]
  have h_alloc_mMap_o : allocMem_o.mMap = s_osea_pre.mem.mMap := by
    simpa [allocBase_o, allocMem_o] using
      A_o.alloc_mMap_eq s_osea_pre.mem (blockSize ctx.innerLayout)
  have h_alloc_base' : allocBase_o = s_osea_pre.mem.addrStart := by
    simpa [allocBase_o] using h_alloc_base
  have h_alloc_addrStart' :
      allocMem_o.addrStart = s_osea_pre.mem.addrStart + blockSize ctx.innerLayout := by
    simpa [allocMem_o] using h_alloc_addrStart
  let ρa' := extendAddrRenameMap ρa freshAddr_m allocBase_o
  let ⟨freshTag_o, ap_alloc_o, h_target_own, h_sb_own⟩ :=
    sb_own_sim_extend (addr_o := allocBase_o) (h_sim := StateSim.sb h_sim_pre) h_own_m
  have h_temp_ne_dst : tempBase_o ≠ allocBase_o := by
    intro h_eq
    have : sb_own s_osea_pre.ap tempBase_o = (SBResult.Ok ap_alloc_o, freshTag_o) := by
      simpa [h_eq] using h_target_own
    unfold sb_own at this
    rw [h_find_temp_pre] at this
    simp at this
  have h_valid_pre : SBValid s_osea_pre.ap := (StateSim.sb h_sim_pre).valid_osea
  have h_find_temp_after_own :
      ap_alloc_o.StackMap.find? tempBase_o = some [RefKind.Own tempTag_o] := by
    rw [sb_own_preserves_find_ne h_valid_pre h_target_own h_temp_ne_dst]
    exact h_find_temp_pre
  obtain ⟨ap_read_o, h_temp_read⟩ := sb_read_of_find_own h_find_temp_after_own
  have h_temp_unmapped' : ∀ a, ρa' a ≠ some tempBase_o := by
    intro a
    by_cases h_eq : a = freshAddr_m
    · subst h_eq
      intro h_map
      have h_map' : some allocBase_o = some tempBase_o := by
        simpa [ρa'] using h_map
      have h_eq' : allocBase_o = tempBase_o := Option.some.inj h_map'
      exact h_temp_ne_dst h_eq'.symm
    · rw [show ρa' a = ρa a by
            simp [ρa', extendAddrRenameMap_ne ρa freshAddr_m allocBase_o a h_eq]]
      exact h_temp_unmapped a
  have h_sb_read :=
    sb_osea_only_read_preserves_sim h_sb_own h_temp_unmapped' h_temp_read
  let ρt' := extendTagRenameMap ρt freshTag_m freshTag_o
  have h_new_addr : ρa' freshAddr_m = some allocBase_o := by
    simp [ρa']
  have h_new_tag : ρt' freshTag_m = some freshTag_o := by
    simp [ρt']
  let ⟨ap_write_o, h_target_use, h_sb_write⟩ :=
    sb_use_mb_sim_ok (ρa := ρa') (ρt := ρt') h_sb_read h_new_addr h_new_tag h_use_m
  let s_osea_post :=
    { s_osea_pre with
      reg := s_osea_pre.reg.insert (dstReg ctx)
        (TyVal.PTy, [oseair.Val.Ptr allocBase_o 0 (blockSize ctx.innerLayout) freshTag_o]),
      ap := ap_write_o,
      mem := oseair.writeWordSeq allocMem_o allocBase_o
        (oseair.readWordSeq s_osea_pre.mem tempBase_o (blockSize ctx.innerLayout)),
      pc := s_osea_pre.pc + 2 }
  have h_res_ne_dst : resReg ctx ≠ dstReg ctx := by
    intro h_eq
    unfold resReg dstReg DerefFreshCtx.resReg DerefFreshCtx.dstReg at h_eq
    by_cases h_zero : ctx.srcOff = 0
    · have h_reg : Register.R ctx.cs.nextReg = Register.R (ctx.cs.nextReg + 2) := by
        simpa [h_zero] using h_eq
      injection h_reg with h_nat
      have h_ne : ctx.cs.nextReg ≠ ctx.cs.nextReg + 2 :=
        Nat.ne_of_lt (Nat.lt_succ_of_lt (Nat.lt_succ_self ctx.cs.nextReg))
      exact h_ne h_nat
    · have h_reg : Register.R ctx.cs.nextReg = Register.R (ctx.cs.nextReg + 3) := by
        simpa [h_zero] using h_eq
      injection h_reg with h_nat
      have h_ne : ctx.cs.nextReg ≠ ctx.cs.nextReg + 3 :=
        Nat.ne_of_lt (Nat.lt_succ_of_lt (Nat.lt_succ_of_lt (Nat.lt_succ_self ctx.cs.nextReg)))
      exact h_ne h_nat
  have h_target_run :
      oseair.runNWith A_o 2 s_osea_pre prog_osea = oseair.Result.Ok s_osea_post := by
    simpa [s_osea_post] using
      osea_run_alloc_ptr_memcpy_embedded_ok
        (A_o := A_o)
        s_osea_pre prog_osea ctx.innerLayout
        tempBase_o 0 (blockSize ctx.innerLayout) tempTag_o
        (dstReg ctx) (resReg ctx)
        allocBase_o allocMem_o freshTag_o
        ap_alloc_o ap_read_o ap_write_o
        h_start h_res_ne_dst
        h_src_reg_pre h_alloc_pair h_alloc_mMap_o h_target_own
        (by simpa [Nat.zero_add] using h_temp_read) h_target_use (by simp)
  let s_osea_alloc : oseair.State := { s_osea_pre with mem := allocMem_o, ap := ap_alloc_o }
  let s_osea_read : oseair.State := { s_osea_pre with mem := allocMem_o, ap := ap_read_o }
  let s_osea_use : oseair.State := { s_osea_pre with mem := allocMem_o, ap := ap_write_o }
  have h_valid_alloc : SBValid ap_alloc_o :=
    sb_own_preserves_valid h_valid_pre h_target_own
  have h_valid_read : SBValid ap_read_o :=
    sb_read_preserves_valid h_valid_alloc h_temp_read
  have h_alloc_le : s_osea_pre.mem.addrStart ≤ s_osea_alloc.mem.addrStart := by
    show s_osea_pre.mem.addrStart ≤ allocMem_o.addrStart
    rw [h_alloc_addrStart']
    exact Nat.le_add_right s_osea_pre.mem.addrStart (blockSize ctx.innerLayout)
  have h_alloc_lt : allocBase_o < s_osea_alloc.mem.addrStart := by
    show allocBase_o < allocMem_o.addrStart
    rw [h_alloc_base', h_alloc_addrStart']
    exact Nat.lt_add_of_pos_right (n := s_osea_pre.mem.addrStart) h_inner_nonempty
  have h_temp_lt_pre : tempBase_o < s_osea_pre.mem.addrStart := by
    exact h_noninterference_pre.2 tempBase_o [RefKind.Own tempTag_o] h_find_temp_pre (by simp)
  have h_temp_lt_alloc : tempBase_o < s_osea_alloc.mem.addrStart := by
    exact Nat.lt_of_lt_of_le h_temp_lt_pre h_alloc_le
  have h_nonempty_alloc : TargetNonemptyStacksBelowAddrStart s_osea_alloc := by
    exact TargetNonemptyStacksBelowAddrStart.sb_own
      h_noninterference_pre.2 h_valid_pre h_alloc_le h_alloc_lt h_target_own
  have h_nonempty_read : TargetNonemptyStacksBelowAddrStart s_osea_read := by
    exact TargetNonemptyStacksBelowAddrStart.sb_read
      (s_osea := s_osea_alloc)
      h_nonempty_alloc h_valid_alloc
      (by simpa [s_osea_alloc] using h_temp_lt_alloc)
      (by simpa [s_osea_alloc, s_osea_read] using h_temp_read)
  have h_nonempty_use_core : TargetNonemptyStacksBelowAddrStart s_osea_use := by
    exact TargetNonemptyStacksBelowAddrStart.sb_use_mb
      (s_osea := s_osea_read)
      h_nonempty_read h_valid_read
      (by simpa [s_osea_read] using h_alloc_lt)
      (by simpa [s_osea_read, s_osea_use] using h_target_use)
  have h_nonempty_next : TargetNonemptyStacksBelowAddrStart s_osea_post := by
    exact TargetNonemptyStacksBelowAddrStart.of_stackMap_eq
      (s_osea := s_osea_use)
      (s_osea_next := s_osea_post)
      h_nonempty_use_core rfl
      (by simp [s_osea_use, s_osea_post, oseair_writeWordSeq_addrStart_eq])
  have h_noninterference_next : TargetNonInterference ρa' s_osea_post := by
    refine ⟨?_, h_nonempty_next⟩
    exact TargetAddrRenameBelowAddrStart.extend_fresh
      (s_osea := s_osea_pre)
      (s_osea_next := s_osea_post)
      (freshAddr_m := freshAddr_m)
      (allocBase_o := allocBase_o)
      (sz := blockSize ctx.innerLayout)
      h_noninterference_pre.1 rfl h_alloc_base'
      (by simpa [s_osea_post, oseair_writeWordSeq_addrStart_eq] using h_alloc_addrStart')
      h_inner_nonempty
  have h_fresh_old :
      ∀ {base' : Word} {reg' : Register} {layout' : LayoutTy}
        {addr_m addr_o tag_m' tag_o' : Word},
        ctx.cs.placeMap.lookup base' = some (reg', layout') →
        place_runtime_sim ctx.cs.placeMap ρa ρt s_mir_pre s_osea_pre
          base' reg' addr_m addr_o tag_m' tag_o' layout' →
        addr_m ≠ freshAddr_m ∧
        blocks_disjoint addr_m (blockSize layout') freshAddr_m (blockSize ctx.innerLayout) ∧
        blocks_disjoint addr_o (blockSize layout') allocBase_o (blockSize ctx.innerLayout) := by
    intro base' reg' layout' addr_m addr_o tag_m' tag_o' h_lookup h_ptr
    simpa using
      (alloc_fresh_disjoint
        (freshAddr_m := freshAddr_m)
        (freshAddr_o := allocBase_o)
        (freshLayout := ctx.innerLayout)
        h_sim_pre h_source_below_pre h_noninterference_pre h_alloc_base_m h_alloc_base' h_lookup h_ptr)
  have h_fresh_tag :
      ∀ {base' : Word} {reg' : Register} {layout' : LayoutTy}
        {addr_m addr_o tag_m' tag_o' : Word},
        ctx.cs.placeMap.lookup base' = some (reg', layout') →
        place_runtime_sim ctx.cs.placeMap ρa ρt s_mir_pre s_osea_pre
          base' reg' addr_m addr_o tag_m' tag_o' layout' →
        tag_m' ≠ freshTag_m := by
    intro base' reg' layout' addr_m addr_o tag_m' tag_o' h_lookup h_ptr
    exact alloc_fresh_tag (freshTag := freshTag_m) h_sim_pre h_tag_fresh_pre h_lookup h_ptr
  refine ⟨allocBase_o, freshTag_o, ρa', ρt', s_osea_post, rfl, rfl,
    StepStarWith.of_runN_ok h_target_run, ?_, h_noninterference_next, ?_⟩
  rw [h_next_full]
  · simpa [postPlaceMap, DerefFreshCtx.postPlaceMap, s_osea_post, ρa', ρt'] using
    state_sim_alloc_write
      (allocMem_m := allocMem_m)
      (allocMem_o := allocMem_o)
      (base := ctx.dst.base)
      (reg := dstReg ctx)
      (layout := ctx.innerLayout)
      (freshAddr_m := freshAddr_m)
      (freshAddr_o := allocBase_o)
      (tag_m := freshTag_m)
      (tag_o := freshTag_o)
      (ap_m' := ap_write_m)
      (ap_o' := ap_write_o)
      (pc_mir := s_mir_pre.pc + 1)
      (pc_osea := s_osea_pre.pc + 2)
      (vals_mir := vals_mir)
      (vals_osea := oseair.readWordSeq s_osea_pre.mem tempBase_o (blockSize ctx.innerLayout))
        h_sim_pre rfl rfl h_dstReg_fresh h_alloc_mMap_m h_alloc_mMap_o
        h_fresh_old h_fresh_tag h_sb_write h_vals h_len
  · simp [s_osea_post]

end DerefFresh

namespace DerefFresh

theorem simulation_structured
  (ctx : DerefFreshCtx)
  {ρa : AddrRenameMap}
  {ρt : TagRenameMap}
  {s_mir s_mir_next : mirlite.State}
  {s_osea : oseair.State}
  {prog_mir : mirlite.Prog}
  {prog_osea : oseair.Prog}
  (h_sim :
    LocalSim ctx ρa ρt s_mir s_osea
      (ptrSimOfCtx ρa ρt s_mir.env))
  (h_noninterference : TargetNonInterference ρa s_osea)
  (h_source_below : SourceBlocksBelowAddrStart ctx.cs.placeMap s_mir)
  (h_tag_fresh : ∀ tag, s_mir.ap.NextTag ≤ tag → ρt tag = none)
  (h_source_alloc_base :
    (A_m.alloc s_mir.mem (typeSize (layoutToTyVal ctx.innerLayout))).1 = s_mir.mem.addrStart)
  (h_dst_env : s_mir.env.lookup ctx.dst.base = none)
  (h_mir_start : StartsAt prog_mir s_mir.pc [stmt ctx])
  (h_mir_step :
    mirlite.stepWith A_m s_mir prog_mir = mirlite.Result.Ok s_mir_next)
  (h_pointee_tracked :
    ∀ srcBaseAddr_m srcTag_m q gq ap_src_read_m targetRes,
      s_mir.env.lookup ctx.src.base =
        some (srcBaseAddr_m, layoutToTyVal ctx.srcBaseLayout, srcTag_m) →
      s_mir.mem.find? (srcBaseAddr_m + ctx.srcOff) =
        some (mirlite.MemValue.PlaceTag q gq) →
      mirlite.resolveDirectPlace { s_mir with ap := ap_src_read_m } q =
        (mirlite.Result.Ok { s_mir with ap := ap_src_read_m }, targetRes) →
      ∃ targetReg targetBaseLayout targetOff targetBaseAddr,
        ctx.cs.placeMap.lookup q.base = some (targetReg, targetBaseLayout) ∧
        layoutResolvePath targetBaseLayout q.path = some (targetOff, ctx.innerLayout) ∧
        s_mir.env.lookup q.base =
          some (targetBaseAddr, layoutToTyVal targetBaseLayout, targetRes.tag) ∧
        targetRes.addr = targetBaseAddr + targetOff ∧
        targetRes.ty = layoutToTyVal ctx.innerLayout)
  (h_osea_start :
    StartsAt prog_osea s_osea.pc (DerefFreshCtx.compiled ctx))
  (_h_inner_nonempty : 0 < blockSize ctx.innerLayout) :
  ∃ freshAddr_m allocBase_o freshTag_m freshTag_o ρa' ρt' s_osea_next,
    freshTag_m = s_mir.ap.NextTag ∧
    ρa' = extendAddrRenameMap ρa freshAddr_m allocBase_o ∧
    ρt' = extendTagRenameMap ρt freshTag_m freshTag_o ∧
    StepStarWith oseair.bumpAllocator s_osea prog_osea s_osea_next ∧
    StateSim (postPlaceMap ctx) ρa' ρt' s_mir_next s_osea_next
      (ptrSimOfCtx ρa ρt s_mir.env) ∧
    TargetNonInterference ρa' s_osea_next ∧
    s_mir_next.env =
      s_mir.env.insert ctx.dst.base (freshAddr_m, layoutToTyVal ctx.innerLayout, freshTag_m) ∧
    s_mir_next.ap.NextTag = s_mir.ap.NextTag + 1 ∧
    s_osea_next.pc = s_osea.pc + (DerefFreshCtx.compiled ctx).length := by
  let ptr_sim := ptrSimOfCtx ρa ρt s_mir.env
  let ⟨srcBase_m, srcBase_o, srcTag_m, srcTag_o, h_src_ptr, h_src_proj_block⟩ :=
    StateSim.place_projected h_sim ctx.h_src_lookup ctx.h_src_path
  have h_src_env := place_runtime_sim.env h_src_ptr
  have h_src_reg := place_runtime_sim.reg h_src_ptr
  have h_src_addr_base : ρa srcBase_m = some srcBase_o := place_runtime_sim.addr h_src_ptr
  have h_src_addr : ρa (srcBase_m + ctx.srcOff) = some (srcBase_o + ctx.srcOff) :=
    addr_rename_offset h_src_addr_base
  have h_src_tag : ρt srcTag_m = some srcTag_o := place_runtime_sim.tag h_src_ptr
  let allocBase_o := (oseair.bumpAllocator.alloc s_osea.mem (blockSize ctx.innerLayout)).1
  let allocMem_o := (oseair.bumpAllocator.alloc s_osea.mem (blockSize ctx.innerLayout)).2
  have h_alloc_pair :
      oseair.bumpAllocator.alloc s_osea.mem (blockSize ctx.innerLayout) =
        (allocBase_o, allocMem_o) := by
    simp [allocBase_o, allocMem_o]
  have h_alloc_mMap_o : allocMem_o.mMap = s_osea.mem.mMap := by
    simpa [allocBase_o, allocMem_o] using
      oseair.AllocatorSpec.alloc_mMap_eq
        (A := oseair.bumpAllocator) s_osea.mem (blockSize ctx.innerLayout)
  have h_alloc_base' : allocBase_o = s_osea.mem.addrStart := by
    simp [allocBase_o, oseair.bumpAllocator, oseair.allocate]
  have h_alloc_addrStart' :
      allocMem_o.addrStart = s_osea.mem.addrStart + blockSize ctx.innerLayout := by
    simp [allocMem_o, oseair.bumpAllocator, oseair.allocate]
  have h_next_alloc_clear :
      NextAllocClear (A_o := oseair.bumpAllocator) ρa s_osea (blockSize ctx.innerLayout) := by
    exact TargetNonInterference.next_alloc_clear h_noninterference
  have h_temp_unmapped_alloc : ∀ a, ρa a ≠ some allocBase_o := by
    exact h_next_alloc_clear.1
  have h_temp_stack_clear_alloc :
      s_osea.ap.StackMap.find? allocBase_o = none ∨
      s_osea.ap.StackMap.find? allocBase_o = some [] := by
    exact h_next_alloc_clear.2
  let ⟨ap_src_read_m, q, gq, targetRes_m, ap_target_read_m,
       freshAddr_m, allocMem_m, freshTag_m, ap_alloc_m, ap_write_m,
       h_mir_read_src, h_mir_ptr_val, h_resolve_target,
       h_mir_read_target, h_alloc_pair_m, h_alloc_mMap_m, h_mir_own, h_mir_use, h_mir_next⟩ :=
    mirlite_step_inv ctx s_mir s_mir_next prog_mir srcBase_m srcTag_m
      h_src_env h_dst_env h_mir_start h_mir_step
  let targetAddr_m := targetRes_m.addr
  let targetTag_m := targetRes_m.tag
  have ⟨targetReg, targetBaseLayout, targetOff, targetBaseAddr_m,
        h_q_lookup, h_q_path, h_mir_target_env, h_target_addr_eq, h_target_ty⟩ :=
    h_pointee_tracked srcBase_m srcTag_m q gq ap_src_read_m targetRes_m
      h_src_env h_mir_ptr_val h_resolve_target
  let ⟨targetBaseAddr_m', targetBaseAddr_o, targetBaseTag_m', targetBaseTag_o,
       h_target_ptr, h_target_proj_block⟩ :=
    StateSim.place_projected h_sim h_q_lookup h_q_path
  have h_target_env_eq :
      some (targetBaseAddr_m', layoutToTyVal targetBaseLayout, targetBaseTag_m') =
        some (targetBaseAddr_m, layoutToTyVal targetBaseLayout, targetTag_m) := by
    exact (place_runtime_sim.env h_target_ptr).symm.trans h_mir_target_env
  cases h_target_env_eq
  have h_target_base_addr : ρa targetBaseAddr_m = some targetBaseAddr_o :=
    place_runtime_sim.addr h_target_ptr
  have h_target_addr : ρa targetAddr_m = some (targetBaseAddr_o + targetOff) := by
    show ρa targetRes_m.addr = some (targetBaseAddr_o + targetOff)
    rw [h_target_addr_eq]
    exact addr_rename_offset h_target_base_addr
  have h_src_cell :
      mem_val_eq_opt
        (s_mir.mem.find? (srcBase_m + ctx.srcOff))
        (s_osea.mem.find? (srcBase_o + ctx.srcOff))
        ptr_sim := by
    simpa [blockSize, layoutSize] using
      h_src_proj_block 0 (by simp [blockSize, layoutSize])
  have h_src_find_and_tag :
      ∃ targetTag_o,
        s_osea.mem.find? (srcBase_o + ctx.srcOff) =
          some (oseair.Val.Ptr targetBaseAddr_o targetOff
            (blockSize targetBaseLayout) targetTag_o) ∧
        ρt gq = some targetTag_o := by
    cases h_find_o : s_osea.mem.find? (srcBase_o + ctx.srcOff) with
    | none =>
        simpa [h_mir_ptr_val, h_find_o, mem_val_eq_opt, mem_val_eq] using h_src_cell
    | some v =>
        cases v with
        | Undef =>
            simpa [h_mir_ptr_val, h_find_o, mem_val_eq_opt, mem_val_eq] using h_src_cell
        | Dat n =>
            simpa [h_mir_ptr_val, h_find_o, mem_val_eq_opt, mem_val_eq] using h_src_cell
        | Ptr base off size tag =>
            have h_ptr :
                ptr_sim q gq base off size tag := by
              simpa [h_mir_ptr_val, h_find_o, mem_val_eq_opt, mem_val_eq] using h_src_cell
            have ⟨h_addr_eq, h_off_eq, h_tag_eq, h_size_eq⟩ :=
              ptrSimOfCtx_elim h_ptr h_mir_target_env h_q_path
            have h_base : base = targetBaseAddr_o :=
              Option.some.inj (h_addr_eq.symm.trans h_target_base_addr)
            subst h_base; cases h_off_eq; cases h_size_eq
            exact ⟨tag, by simpa [h_find_o], h_tag_eq⟩
  obtain ⟨targetTag_o, h_src_find, h_gq_tag⟩ := h_src_find_and_tag
  have h_target_fit : targetOff + blockSize ctx.innerLayout ≤ blockSize targetBaseLayout :=
    layoutResolvePath_blockSize_le h_q_path
  have h_src_mem :
      oseair.readWordSeq s_osea.mem (srcBase_o + ctx.srcOff) 1 =
        [oseair.Val.Ptr targetBaseAddr_o targetOff
          (blockSize targetBaseLayout) targetTag_o] := by
    simp [oseair.readWordSeq, h_src_find]
  have h_target_vals :
      mem_vals_eq ptr_sim
        (mirlite.readWordSeq s_mir.mem targetAddr_m (blockSize ctx.innerLayout))
        (oseair.readWordSeq s_osea.mem (targetBaseAddr_o + targetOff) (blockSize ctx.innerLayout)) := by
    show mem_vals_eq ptr_sim
      (mirlite.readWordSeq s_mir.mem targetRes_m.addr (blockSize ctx.innerLayout))
      (oseair.readWordSeq s_osea.mem (targetBaseAddr_o + targetOff) (blockSize ctx.innerLayout))
    rw [h_target_addr_eq]
    exact mem_vals_eq_readWordSeq h_target_proj_block
  let s_mir_pre : mirlite.State := { s_mir with ap := ap_target_read_m }
  have h_mir_next_pre :
      s_mir_next =
        { s_mir_pre with
          env := s_mir_pre.env.insert ctx.dst.base
            (freshAddr_m, layoutToTyVal ctx.innerLayout, freshTag_m),
          mem := mirlite.writeWordSeq allocMem_m freshAddr_m
            (mirlite.readWordSeq s_mir.mem targetAddr_m (blockSize ctx.innerLayout)),
          ap := ap_write_m,
          pc := s_mir.pc + 1 } := by
    simpa [s_mir_pre, h_target_ty, blockSize, layoutSize] using h_mir_next
  have h_ap_src_read_next : ap_src_read_m.NextTag = s_mir.ap.NextTag := by
    exact obseq.sb_read_nextTag_eq h_mir_read_src
  have h_ap_target_read_next : ap_target_read_m.NextTag = s_mir.ap.NextTag := by
    rw [obseq.sb_read_nextTag_eq h_mir_read_target]
    exact h_ap_src_read_next
  have h_freshTag_eq_next : freshTag_m = s_mir.ap.NextTag := by
    rw [obseq.sb_own_tag_eq_nextTag h_mir_own]
    exact h_ap_target_read_next
  have h_source_below_pre : SourceBlocksBelowAddrStart ctx.cs.placeMap s_mir_pre := by
    simpa [s_mir_pre] using h_source_below
  have h_tag_fresh_pre : ∀ tag, freshTag_m ≤ tag → ρt tag = none := by
    simpa [h_freshTag_eq_next] using h_tag_fresh
  have h_alloc_base_m : freshAddr_m = s_mir_pre.mem.addrStart := by
    have h_fst := congrArg Prod.fst h_alloc_pair_m
    exact h_fst.symm.trans (by simpa [s_mir_pre, h_target_ty] using h_source_alloc_base)
  have h_ap_alloc_next : ap_alloc_m.NextTag = s_mir.ap.NextTag + 1 := by
    rw [obseq.sb_own_nextTag_succ h_mir_own, h_ap_target_read_next]
  have h_ap_write_next : ap_write_m.NextTag = s_mir.ap.NextTag + 1 := by
    rw [obseq.sb_use_mb_nextTag_eq h_mir_use]
    exact h_ap_alloc_next
  have h_env_next :
      s_mir_next.env =
        s_mir.env.insert ctx.dst.base (freshAddr_m, layoutToTyVal ctx.innerLayout, freshTag_m) := by
    simpa [s_mir_pre] using congrArg (fun st => st.env) h_mir_next_pre
  have h_nextTag_post : s_mir_next.ap.NextTag = s_mir.ap.NextTag + 1 := by
    have h_post_next : s_mir_next.ap.NextTag = ap_write_m.NextTag := by
      simpa [s_mir_pre] using congrArg (fun st => st.ap.NextTag) h_mir_next_pre
    exact h_post_next.trans h_ap_write_next
  have ⟨allocTag_o, ap_alloc, h_osea_alloc⟩ :=
    sb_osea_only_own_ok h_temp_stack_clear_alloc
  have h_sb_alloc :=
    sb_osea_only_own_preserves_sim (StateSim.sb h_sim) h_temp_unmapped_alloc h_osea_alloc
  let vals_temp := oseair.readWordSeq s_osea.mem (targetBaseAddr_o + targetOff) (blockSize ctx.innerLayout)
  have h_temp_disj :
      ∀ base reg layout,
        ctx.cs.placeMap.lookup base = some (reg, layout) →
        ∀ addr_m addr_o tag_m tag_o,
          place_runtime_sim ctx.cs.placeMap ρa ρt s_mir s_osea
            base reg addr_m addr_o tag_m tag_o layout →
          blocks_disjoint addr_o (blockSize layout) allocBase_o vals_temp.length := by
    intro base reg layout h_lookup addr_m addr_o tag_m tag_o h_ptr
    simpa [vals_temp] using
      (alloc_fresh_target_disjoint
        (freshAddr_o := allocBase_o)
        (freshLayout := ctx.innerLayout)
        h_sim h_noninterference h_alloc_base' h_lookup h_ptr)
  have h_sim_temp_write :
      StateSim ctx.cs.placeMap ρa ρt s_mir
        { s_osea with mem := oseair.writeWordSeq s_osea.mem allocBase_o vals_temp }
        ptr_sim := by
    exact state_sim_osea_write_other h_sim h_temp_disj
  have h_temp_ne_src : allocBase_o ≠ srcBase_o + ctx.srcOff := by
    intro h_eq
    exact h_temp_unmapped_alloc (srcBase_m + ctx.srcOff) (h_eq ▸ h_src_addr)
  have h_temp_ne_target : allocBase_o ≠ targetBaseAddr_o + targetOff := by
    intro h_eq
    exact h_temp_unmapped_alloc targetAddr_m (h_eq ▸ h_target_addr)
  have h_own_find :
      ap_alloc.StackMap.find? allocBase_o = some [RefKind.Own allocTag_o] :=
    sb_own_creates_find h_osea_alloc
  by_cases h_src_off : ctx.srcOff = 0
  · have ⟨h_stmt0, h_stmt1, h_stmt2⟩ :=
      starts_direct_instrs ctx h_osea_start h_src_off
    let ⟨ap_load_parent, h_osea_load_parent, h_sb_load_parent⟩ :=
      sb_read_sim_ok h_sb_alloc h_src_addr h_src_tag h_mir_read_src
    have h_find_after_load :
        ap_load_parent.StackMap.find? allocBase_o = some [RefKind.Own allocTag_o] := by
      exact (sb_read_preserves_find_ne h_sb_alloc.valid_osea h_osea_load_parent h_temp_ne_src).trans
        h_own_find
    let ⟨ap_memcpy1_read, h_osea_memcpy1_read, h_sb_memcpy1_read⟩ :=
      sb_read_sim_ok h_sb_load_parent h_target_addr h_gq_tag h_mir_read_target
    have h_find_after_target_read :
        ap_memcpy1_read.StackMap.find? allocBase_o = some [RefKind.Own allocTag_o] := by
      exact (sb_read_preserves_find_ne
        h_sb_load_parent.valid_osea h_osea_memcpy1_read h_temp_ne_target).trans h_find_after_load
    have ⟨ap_memcpy1_write, h_osea_memcpy1_write⟩ :=
      sb_use_mb_of_find_own h_find_after_target_read
    have h_sb_prefix :=
      sb_osea_only_use_mb_preserves_sim h_sb_memcpy1_read h_temp_unmapped_alloc h_osea_memcpy1_write
    have h_find_temp_pre :
        ap_memcpy1_write.StackMap.find? allocBase_o = some [RefKind.Own allocTag_o] :=
      sb_use_mb_preserves_find_own h_find_after_target_read h_osea_memcpy1_write
    let s_osea_pre : oseair.State :=
      { s_osea with
        reg :=
          (s_osea.reg.insert (resReg ctx)
            (TyVal.PTy,
              [oseair.Val.Ptr allocBase_o 0 (blockSize ctx.innerLayout) allocTag_o])).insert
            (loadedPtrReg ctx)
            (TyVal.PTy,
              [oseair.Val.Ptr targetBaseAddr_o targetOff (blockSize targetBaseLayout) targetTag_o]),
        ap := ap_memcpy1_write,
        mem := oseair.writeWordSeq allocMem_o allocBase_o vals_temp,
        pc := s_osea.pc + 3 }
    have h_prefix_run :
        oseair.runNWith oseair.bumpAllocator 3 s_osea prog_osea = oseair.Result.Ok s_osea_pre := by
      simpa [s_osea_pre, vals_temp] using
        osea_rhs_direct_run_ok
          (A_o := oseair.bumpAllocator) ctx s_osea prog_osea
          srcBase_o srcTag_o
          targetBaseAddr_o targetOff (blockSize targetBaseLayout) targetTag_o
          allocBase_o allocMem_o allocTag_o
          ap_alloc ap_load_parent ap_memcpy1_read ap_memcpy1_write
          h_src_off h_stmt0 h_stmt1 h_stmt2
          h_src_reg h_src_mem h_alloc_pair h_alloc_mMap_o h_osea_alloc
          (by simpa [h_src_off] using h_osea_load_parent)
          h_osea_memcpy1_read h_osea_memcpy1_write
          (by simpa [h_src_off] using layoutResolvePath_blockSize_le ctx.h_src_path)
          h_target_fit
    have h_sim_pre_core :
        StateSim ctx.cs.placeMap ρa ρt
          s_mir_pre
          { s_osea with
            ap := ap_memcpy1_write,
            mem := oseair.writeWordSeq allocMem_o allocBase_o vals_temp }
          ptr_sim := by
      exact StateSim.of_mem_mMap_eq_sb h_sb_prefix h_sim_temp_write
        rfl rfl rfl
        (oseair_writeWordSeq_mMap_eq_of_mMap_eq h_alloc_mMap_o allocBase_o vals_temp).symm
    have h_res_fresh :
        ∀ base layout,
          ctx.cs.placeMap.lookup base = some (resReg ctx, layout) → False := by
      simpa [resReg, DerefFreshCtx.resReg] using
        (alloc_fresh_reg_of_ge (cs := ctx.cs) ctx.h_regs_below (Nat.le_refl _))
    have h_loaded_fresh :
        ∀ base layout,
          ctx.cs.placeMap.lookup base = some (loadedPtrReg ctx, layout) → False := by
      simpa [loadedPtrReg, DerefFreshCtx.loadedPtrReg, h_src_off] using
        (alloc_fresh_reg_of_ge (cs := ctx.cs) ctx.h_regs_below (Nat.le_add_right _ 1))
    have h_sim_pre_res :
        StateSim ctx.cs.placeMap ρa ρt
          s_mir_pre
          { s_osea with
            reg := s_osea.reg.insert (resReg ctx)
              (TyVal.PTy, [oseair.Val.Ptr allocBase_o 0 (blockSize ctx.innerLayout) allocTag_o]),
            ap := ap_memcpy1_write,
            mem := oseair.writeWordSeq allocMem_o allocBase_o vals_temp }
          ptr_sim := by
      exact state_sim_reg_insert_other h_sim_pre_core h_res_fresh
    have h_sim_pre :
        StateSim ctx.cs.placeMap ρa ρt s_mir_pre s_osea_pre ptr_sim := by
      simpa [s_osea_pre] using
        (state_sim_reg_insert_other
          (tmpReg := loadedPtrReg ctx)
          (tmpVal :=
            (TyVal.PTy, [oseair.Val.Ptr targetBaseAddr_o targetOff (blockSize targetBaseLayout) targetTag_o]))
          h_sim_pre_res h_loaded_fresh)
    let s_osea_alloc : oseair.State := { s_osea with mem := allocMem_o, ap := ap_alloc }
    let s_osea_load_parent : oseair.State := { s_osea with mem := allocMem_o, ap := ap_load_parent }
    let s_osea_target_read : oseair.State := { s_osea with mem := allocMem_o, ap := ap_memcpy1_read }
    let s_osea_use : oseair.State := { s_osea with mem := allocMem_o, ap := ap_memcpy1_write }
    have h_valid_alloc : SBValid ap_alloc :=
      sb_own_preserves_valid (StateSim.sb h_sim).valid_osea h_osea_alloc
    have h_valid_load_parent : SBValid ap_load_parent :=
      sb_read_preserves_valid h_valid_alloc h_osea_load_parent
    have h_valid_target_read : SBValid ap_memcpy1_read :=
      sb_read_preserves_valid h_valid_load_parent h_osea_memcpy1_read
    have h_src_lt_old : srcBase_o + ctx.srcOff < s_osea.mem.addrStart :=
      h_noninterference.1 _ _ h_src_addr
    have h_target_lt_old : targetBaseAddr_o + targetOff < s_osea.mem.addrStart :=
      h_noninterference.1 _ _ h_target_addr
    have h_src_lt_alloc : srcBase_o + ctx.srcOff < s_osea_alloc.mem.addrStart := by
      exact Nat.lt_of_lt_of_le h_src_lt_old (by
        show s_osea.mem.addrStart ≤ s_osea_alloc.mem.addrStart
        simp [s_osea_alloc, h_alloc_addrStart'])
    have h_target_lt_alloc : targetBaseAddr_o + targetOff < s_osea_load_parent.mem.addrStart := by
      exact Nat.lt_of_lt_of_le h_target_lt_old (by
        show s_osea.mem.addrStart ≤ s_osea_load_parent.mem.addrStart
        simp [s_osea_load_parent, h_alloc_addrStart'])
    have h_nonempty_alloc : TargetNonemptyStacksBelowAddrStart s_osea_alloc := by
      exact TargetNonemptyStacksBelowAddrStart.sb_own
        h_noninterference.2 (StateSim.sb h_sim).valid_osea
        (by
          show s_osea.mem.addrStart ≤ s_osea_alloc.mem.addrStart
          simp [s_osea_alloc, h_alloc_addrStart'])
        (by
          show allocBase_o < s_osea_alloc.mem.addrStart
          show allocBase_o < allocMem_o.addrStart
          rw [h_alloc_base', h_alloc_addrStart']
          exact Nat.lt_add_of_pos_right (n := s_osea.mem.addrStart) _h_inner_nonempty)
        h_osea_alloc
    have h_nonempty_load_parent : TargetNonemptyStacksBelowAddrStart s_osea_load_parent := by
      exact TargetNonemptyStacksBelowAddrStart.sb_read
        (s_osea := s_osea_alloc)
        h_nonempty_alloc h_valid_alloc
        (by simpa [s_osea_alloc] using h_src_lt_alloc)
        (by simpa [s_osea_alloc, s_osea_load_parent] using h_osea_load_parent)
    have h_nonempty_target_read : TargetNonemptyStacksBelowAddrStart s_osea_target_read := by
      exact TargetNonemptyStacksBelowAddrStart.sb_read
        (s_osea := s_osea_load_parent)
        h_nonempty_load_parent h_valid_load_parent
        (by simpa [s_osea_load_parent] using h_target_lt_alloc)
        (by simpa [s_osea_load_parent, s_osea_target_read] using h_osea_memcpy1_read)
    have h_nonempty_use_core : TargetNonemptyStacksBelowAddrStart s_osea_use := by
      exact TargetNonemptyStacksBelowAddrStart.sb_use_mb
        (s_osea := s_osea_target_read)
        h_nonempty_target_read h_valid_target_read
        (by
          show allocBase_o < s_osea_target_read.mem.addrStart
          show allocBase_o < allocMem_o.addrStart
          rw [h_alloc_base', h_alloc_addrStart']
          exact Nat.lt_add_of_pos_right (n := s_osea.mem.addrStart) _h_inner_nonempty)
        (by simpa [s_osea_target_read, s_osea_use] using h_osea_memcpy1_write)
    have h_nonempty_pre : TargetNonemptyStacksBelowAddrStart s_osea_pre := by
      exact TargetNonemptyStacksBelowAddrStart.of_stackMap_eq
        (s_osea := s_osea_use)
        (s_osea_next := s_osea_pre)
        h_nonempty_use_core rfl
        (by simp [s_osea_use, s_osea_pre, oseair_writeWordSeq_addrStart_eq])
    have h_noninterference_pre : TargetNonInterference ρa s_osea_pre := by
      refine ⟨?_, h_nonempty_pre⟩
      exact TargetAddrRenameBelowAddrStart.mono h_noninterference.1 (by
        have h_le : s_osea.mem.addrStart ≤ allocMem_o.addrStart := by
          rw [h_alloc_addrStart']
          exact Nat.le_add_right s_osea.mem.addrStart (blockSize ctx.innerLayout)
        simpa [s_osea_pre, oseair_writeWordSeq_addrStart_eq] using h_le)
    have h_res_ne_loaded : resReg ctx ≠ loadedPtrReg ctx := by
      intro h_eq
      unfold resReg loadedPtrReg DerefFreshCtx.resReg DerefFreshCtx.loadedPtrReg at h_eq
      have h_reg : Register.R ctx.cs.nextReg = Register.R (ctx.cs.nextReg + 1) := by
        simpa [h_src_off] using h_eq
      injection h_reg with h_nat
      exact (Nat.ne_of_lt (Nat.lt_succ_self ctx.cs.nextReg)) h_nat
    have h_src_reg_pre :
        s_osea_pre.reg.lookup (resReg ctx) =
          some (TyVal.PTy, [oseair.Val.Ptr allocBase_o 0 (blockSize ctx.innerLayout) allocTag_o]) := by
      simp [s_osea_pre, h_res_ne_loaded]
    have h_dstReg_fresh :
        ∀ base layout,
          ctx.cs.placeMap.lookup base = some (dstReg ctx, layout) → False := by
      simpa [dstReg, DerefFreshCtx.dstReg, h_src_off] using
        (alloc_fresh_reg_of_ge (cs := ctx.cs) ctx.h_regs_below (Nat.le_add_right _ 2))
    have h_temp_read_exact :
        oseair.readWordSeq s_osea_pre.mem allocBase_o (blockSize ctx.innerLayout) = vals_temp := by
      simpa [s_osea_pre, vals_temp] using
        (oseair_readWordSeq_write_exact allocMem_o allocBase_o vals_temp)
    have h_vals :
        mem_vals_eq ptr_sim
          (mirlite.readWordSeq s_mir.mem targetAddr_m (blockSize ctx.innerLayout))
          (oseair.readWordSeq s_osea_pre.mem allocBase_o (blockSize ctx.innerLayout)) := by
      rw [h_temp_read_exact]
      simpa [vals_temp] using h_target_vals
    have h_start_suffix :
        StartsAt prog_osea s_osea_pre.pc
          [oseair.Instr.Assgn (dstReg ctx) (oseair.Rhs.Alloc (innerTy ctx)),
           oseair.Instr.Memcpy (dstReg ctx) (resReg ctx) (innerTy ctx)] := by
      simpa [s_osea_pre] using starts_direct_suffix ctx h_osea_start h_src_off
    have h_len :
        (mirlite.readWordSeq s_mir.mem targetAddr_m (blockSize ctx.innerLayout)).length =
          blockSize ctx.innerLayout := by
      simpa using mirlite_readWordSeq_length s_mir.mem targetAddr_m (blockSize ctx.innerLayout)
    obtain ⟨allocBase_o, freshTag_o, ρa', ρt', s_osea_next,
        h_ρa', h_ρt', h_steps, h_sim_next, h_noninterference_next, h_pc_tail⟩ :=
      finish_from_pre
        (A_o := oseair.bumpAllocator) ctx
        (ptr_sim := ptr_sim)
        (s_mir_pre := s_mir_pre)
        (s_mir_next := s_mir_next)
        (s_osea_pre := s_osea_pre)
        (prog_osea := prog_osea)
        (vals_mir := mirlite.readWordSeq s_mir.mem targetAddr_m (blockSize ctx.innerLayout))
        (freshAddr_m := freshAddr_m)
        (allocMem_m := allocMem_m)
        (freshTag_m := freshTag_m)
        (ap_alloc_m := ap_alloc_m)
        (ap_write_m := ap_write_m)
        (tempBase_o := allocBase_o)
        (tempTag_o := allocTag_o)
        h_sim_pre h_noninterference_pre h_source_below_pre h_tag_fresh_pre
        h_temp_unmapped_alloc h_find_temp_pre
        h_start_suffix h_src_reg_pre h_dstReg_fresh
        h_mir_own h_mir_use h_alloc_mMap_m h_alloc_base_m
        (by simp [oseair.bumpAllocator, oseair.allocate])
        (by simp [oseair.bumpAllocator, oseair.allocate])
        _h_inner_nonempty h_mir_next_pre h_vals h_len
    exact ⟨freshAddr_m, allocBase_o, freshTag_m, freshTag_o, ρa', ρt', s_osea_next,
      h_freshTag_eq_next, h_ρa', h_ρt',
      StepStarWith.trans (StepStarWith.of_runN_ok h_prefix_run) h_steps,
      h_sim_next, h_noninterference_next, h_env_next, h_nextTag_post,
      by
        simpa [s_osea_pre, DerefFreshCtx.compiled, h_src_off, Nat.add_assoc] using h_pc_tail⟩
  · have ⟨h_stmt0, h_stmt1, h_stmt2, h_stmt3, h_stmt4⟩ :=
      starts_projected_instrs ctx h_osea_start h_src_off
    let ⟨ap_load_parent, h_osea_load_parent, h_sb_load_parent⟩ :=
      sb_read_sim_ok h_sb_alloc h_src_addr h_src_tag h_mir_read_src
    let ⟨srcTempTag_o, ap_src_ref_o, ap_load_o, ap_load_final_o,
      h_osea_ref, h_osea_load, h_osea_die, h_src_stack_eq⟩ :=
      sb_ref_shared_read_die_ok_of_read_ok h_osea_load_parent
    have h_sb_load_final : sb_sim ρa ρt ap_src_read_m ap_load_final_o :=
      sb_sim_of_right_stackMap_eq h_sb_load_parent h_src_stack_eq
    have h_valid_ref : SBValid ap_src_ref_o :=
      sb_ref_preserves_valid h_sb_alloc.valid_osea h_osea_ref
    have h_find_after_ref :
        ap_src_ref_o.StackMap.find? allocBase_o = some [RefKind.Own allocTag_o] := by
      exact (sb_ref_preserves_find_ne h_sb_alloc.valid_osea h_osea_ref h_temp_ne_src).trans
        h_own_find
    have h_valid_load : SBValid ap_load_o := sb_read_preserves_valid h_valid_ref h_osea_load
    have h_find_after_load :
        ap_load_o.StackMap.find? allocBase_o = some [RefKind.Own allocTag_o] := by
      exact (sb_read_preserves_find_ne h_valid_ref h_osea_load h_temp_ne_src).trans h_find_after_ref
    have h_find_after_die :
        ap_load_final_o.StackMap.find? allocBase_o = some [RefKind.Own allocTag_o] := by
      exact (sb_die_preserves_find_ne h_valid_load h_osea_die h_temp_ne_src).trans h_find_after_load
    let ⟨ap_memcpy1_read, h_osea_memcpy1_read, h_sb_memcpy1_read⟩ :=
      sb_read_sim_ok h_sb_load_final h_target_addr h_gq_tag h_mir_read_target
    have h_find_after_target_read :
        ap_memcpy1_read.StackMap.find? allocBase_o = some [RefKind.Own allocTag_o] := by
      exact (sb_read_preserves_find_ne
        h_sb_load_final.valid_osea h_osea_memcpy1_read h_temp_ne_target).trans h_find_after_die
    have ⟨ap_memcpy1_write, h_osea_memcpy1_write⟩ :=
      sb_use_mb_of_find_own h_find_after_target_read
    have h_sb_prefix :=
      sb_osea_only_use_mb_preserves_sim h_sb_memcpy1_read h_temp_unmapped_alloc h_osea_memcpy1_write
    have h_find_temp_pre :
        ap_memcpy1_write.StackMap.find? allocBase_o = some [RefKind.Own allocTag_o] :=
      sb_use_mb_preserves_find_own h_find_after_target_read h_osea_memcpy1_write
    let s_osea_pre : oseair.State :=
      { s_osea with
        reg :=
          ((s_osea.reg.insert (resReg ctx)
            (TyVal.PTy,
              [oseair.Val.Ptr allocBase_o 0 (blockSize ctx.innerLayout) allocTag_o])).insert
            (srcTmpReg ctx)
            (TyVal.PTy,
              [oseair.Val.Ptr srcBase_o ctx.srcOff (blockSize ctx.srcBaseLayout) srcTempTag_o])).insert
            (loadedPtrReg ctx)
            (TyVal.PTy,
              [oseair.Val.Ptr targetBaseAddr_o targetOff (blockSize targetBaseLayout) targetTag_o]),
        ap := ap_memcpy1_write,
        mem := oseair.writeWordSeq allocMem_o allocBase_o vals_temp,
        pc := s_osea.pc + 5 }
    have h_prefix_run :
        oseair.runNWith oseair.bumpAllocator 5 s_osea prog_osea = oseair.Result.Ok s_osea_pre := by
      simpa [s_osea_pre, vals_temp] using
        osea_rhs_projected_run_ok
          (A_o := oseair.bumpAllocator) ctx s_osea prog_osea
          srcBase_o srcTag_o srcTempTag_o
          targetBaseAddr_o targetOff (blockSize targetBaseLayout) targetTag_o
          allocBase_o allocMem_o allocTag_o
          ap_alloc ap_src_ref_o ap_load_o ap_load_final_o ap_memcpy1_read ap_memcpy1_write
          h_src_off h_stmt0 h_stmt1 h_stmt2 h_stmt3 h_stmt4
          h_src_reg h_src_mem h_alloc_pair h_alloc_mMap_o
          h_osea_alloc h_osea_ref h_osea_load h_osea_die
          h_osea_memcpy1_read h_osea_memcpy1_write
          (layoutResolvePath_blockSize_le ctx.h_src_path)
          h_target_fit
    have h_sim_pre_core :
        StateSim ctx.cs.placeMap ρa ρt
          s_mir_pre
          { s_osea with
            ap := ap_memcpy1_write,
            mem := oseair.writeWordSeq allocMem_o allocBase_o vals_temp }
          ptr_sim := by
      exact StateSim.of_mem_mMap_eq_sb h_sb_prefix h_sim_temp_write
        rfl rfl rfl
        (oseair_writeWordSeq_mMap_eq_of_mMap_eq h_alloc_mMap_o allocBase_o vals_temp).symm
    have h_res_fresh :
        ∀ base layout,
          ctx.cs.placeMap.lookup base = some (resReg ctx, layout) → False := by
      simpa [resReg, DerefFreshCtx.resReg] using
        (alloc_fresh_reg_of_ge (cs := ctx.cs) ctx.h_regs_below (Nat.le_refl _))
    have h_srcTmp_fresh :
        ∀ base layout,
          ctx.cs.placeMap.lookup base = some (srcTmpReg ctx, layout) → False := by
      simpa [srcTmpReg, DerefFreshCtx.srcTmpReg] using
        (alloc_fresh_reg_of_ge (cs := ctx.cs) ctx.h_regs_below (Nat.le_add_right _ 1))
    have h_loaded_fresh :
        ∀ base layout,
          ctx.cs.placeMap.lookup base = some (loadedPtrReg ctx, layout) → False := by
      simpa [loadedPtrReg, DerefFreshCtx.loadedPtrReg, h_src_off] using
        (alloc_fresh_reg_of_ge (cs := ctx.cs) ctx.h_regs_below (Nat.le_add_right _ 2))
    have h_sim_pre_res :
        StateSim ctx.cs.placeMap ρa ρt
          s_mir_pre
          { s_osea with
            reg := s_osea.reg.insert (resReg ctx)
              (TyVal.PTy, [oseair.Val.Ptr allocBase_o 0 (blockSize ctx.innerLayout) allocTag_o]),
            ap := ap_memcpy1_write,
            mem := oseair.writeWordSeq allocMem_o allocBase_o vals_temp }
          ptr_sim := by
      exact state_sim_reg_insert_other h_sim_pre_core h_res_fresh
    have h_sim_pre_srcTmp :
        StateSim ctx.cs.placeMap ρa ρt
          s_mir_pre
          { s_osea with
            reg :=
              (s_osea.reg.insert (resReg ctx)
                (TyVal.PTy, [oseair.Val.Ptr allocBase_o 0 (blockSize ctx.innerLayout) allocTag_o])).insert
                (srcTmpReg ctx)
                (TyVal.PTy,
                  [oseair.Val.Ptr srcBase_o ctx.srcOff (blockSize ctx.srcBaseLayout) srcTempTag_o]),
            ap := ap_memcpy1_write,
            mem := oseair.writeWordSeq allocMem_o allocBase_o vals_temp }
          ptr_sim := by
      exact state_sim_reg_insert_other h_sim_pre_res h_srcTmp_fresh
    have h_sim_pre :
        StateSim ctx.cs.placeMap ρa ρt s_mir_pre s_osea_pre ptr_sim := by
      simpa [s_osea_pre] using
        (state_sim_reg_insert_other
          (tmpReg := loadedPtrReg ctx)
          (tmpVal :=
            (TyVal.PTy, [oseair.Val.Ptr targetBaseAddr_o targetOff (blockSize targetBaseLayout) targetTag_o]))
          h_sim_pre_srcTmp h_loaded_fresh)
    let s_osea_alloc : oseair.State := { s_osea with mem := allocMem_o, ap := ap_alloc }
    let s_osea_ref : oseair.State := { s_osea with mem := allocMem_o, ap := ap_src_ref_o }
    let s_osea_load : oseair.State := { s_osea with mem := allocMem_o, ap := ap_load_o }
    let s_osea_load_final : oseair.State := { s_osea with mem := allocMem_o, ap := ap_load_final_o }
    let s_osea_target_read : oseair.State := { s_osea with mem := allocMem_o, ap := ap_memcpy1_read }
    let s_osea_use : oseair.State := { s_osea with mem := allocMem_o, ap := ap_memcpy1_write }
    have h_valid_alloc : SBValid ap_alloc :=
      sb_own_preserves_valid (StateSim.sb h_sim).valid_osea h_osea_alloc
    have h_valid_ref' : SBValid ap_src_ref_o :=
      sb_ref_preserves_valid h_valid_alloc h_osea_ref
    have h_valid_load' : SBValid ap_load_o :=
      sb_read_preserves_valid h_valid_ref' h_osea_load
    have h_valid_load_final' : SBValid ap_load_final_o :=
      sb_die_preserves_valid h_valid_load' h_osea_die
    have h_valid_target_read : SBValid ap_memcpy1_read :=
      sb_read_preserves_valid h_valid_load_final' h_osea_memcpy1_read
    have h_src_lt_old : srcBase_o + ctx.srcOff < s_osea.mem.addrStart :=
      h_noninterference.1 _ _ h_src_addr
    have h_target_lt_old : targetBaseAddr_o + targetOff < s_osea.mem.addrStart :=
      h_noninterference.1 _ _ h_target_addr
    have h_src_lt_alloc : srcBase_o + ctx.srcOff < s_osea_alloc.mem.addrStart := by
      exact Nat.lt_of_lt_of_le h_src_lt_old (by
        show s_osea.mem.addrStart ≤ s_osea_alloc.mem.addrStart
        simp [s_osea_alloc, h_alloc_addrStart'])
    have h_target_lt_alloc : targetBaseAddr_o + targetOff < s_osea_load_final.mem.addrStart := by
      exact Nat.lt_of_lt_of_le h_target_lt_old (by
        show s_osea.mem.addrStart ≤ s_osea_load_final.mem.addrStart
        simp [s_osea_load_final, h_alloc_addrStart'])
    have h_nonempty_alloc : TargetNonemptyStacksBelowAddrStart s_osea_alloc := by
      exact TargetNonemptyStacksBelowAddrStart.sb_own
        h_noninterference.2 (StateSim.sb h_sim).valid_osea
        (by
          show s_osea.mem.addrStart ≤ s_osea_alloc.mem.addrStart
          simp [s_osea_alloc, h_alloc_addrStart'])
        (by
          show allocBase_o < s_osea_alloc.mem.addrStart
          show allocBase_o < allocMem_o.addrStart
          rw [h_alloc_base', h_alloc_addrStart']
          exact Nat.lt_add_of_pos_right (n := s_osea.mem.addrStart) _h_inner_nonempty)
        h_osea_alloc
    have h_nonempty_ref : TargetNonemptyStacksBelowAddrStart s_osea_ref := by
      exact TargetNonemptyStacksBelowAddrStart.sb_ref
        (s_osea := s_osea_alloc)
        h_nonempty_alloc h_valid_alloc
        (by simpa [s_osea_alloc] using h_src_lt_alloc)
        (by simpa [s_osea_alloc, s_osea_ref] using h_osea_ref)
    have h_nonempty_load : TargetNonemptyStacksBelowAddrStart s_osea_load := by
      exact TargetNonemptyStacksBelowAddrStart.sb_read
        (s_osea := s_osea_ref)
        h_nonempty_ref h_valid_ref'
        (by simpa [s_osea_ref] using h_src_lt_alloc)
        (by simpa [s_osea_ref, s_osea_load] using h_osea_load)
    have h_nonempty_load_final : TargetNonemptyStacksBelowAddrStart s_osea_load_final := by
      exact TargetNonemptyStacksBelowAddrStart.sb_die
        (s_osea := s_osea_load)
        h_nonempty_load h_valid_load'
        (by simpa [s_osea_load] using h_src_lt_alloc)
        (by simpa [s_osea_load, s_osea_load_final] using h_osea_die)
    have h_nonempty_target_read : TargetNonemptyStacksBelowAddrStart s_osea_target_read := by
      exact TargetNonemptyStacksBelowAddrStart.sb_read
        (s_osea := s_osea_load_final)
        h_nonempty_load_final h_valid_load_final'
        (by simpa [s_osea_load_final] using h_target_lt_alloc)
        (by simpa [s_osea_load_final, s_osea_target_read] using h_osea_memcpy1_read)
    have h_nonempty_use_core : TargetNonemptyStacksBelowAddrStart s_osea_use := by
      exact TargetNonemptyStacksBelowAddrStart.sb_use_mb
        (s_osea := s_osea_target_read)
        h_nonempty_target_read h_valid_target_read
        (by
          show allocBase_o < s_osea_target_read.mem.addrStart
          show allocBase_o < allocMem_o.addrStart
          rw [h_alloc_base', h_alloc_addrStart']
          exact Nat.lt_add_of_pos_right (n := s_osea.mem.addrStart) _h_inner_nonempty)
        (by simpa [s_osea_target_read, s_osea_use] using h_osea_memcpy1_write)
    have h_nonempty_pre : TargetNonemptyStacksBelowAddrStart s_osea_pre := by
      exact TargetNonemptyStacksBelowAddrStart.of_stackMap_eq
        (s_osea := s_osea_use)
        (s_osea_next := s_osea_pre)
        h_nonempty_use_core rfl
        (by simp [s_osea_use, s_osea_pre, oseair_writeWordSeq_addrStart_eq])
    have h_noninterference_pre : TargetNonInterference ρa s_osea_pre := by
      refine ⟨?_, h_nonempty_pre⟩
      exact TargetAddrRenameBelowAddrStart.mono h_noninterference.1 (by
        have h_le : s_osea.mem.addrStart ≤ allocMem_o.addrStart := by
          rw [h_alloc_addrStart']
          exact Nat.le_add_right s_osea.mem.addrStart (blockSize ctx.innerLayout)
        simpa [s_osea_pre, oseair_writeWordSeq_addrStart_eq] using h_le)
    have h_res_ne_srcTmp : resReg ctx ≠ srcTmpReg ctx := by
      intro h_eq
      unfold resReg srcTmpReg DerefFreshCtx.resReg DerefFreshCtx.srcTmpReg at h_eq
      injection h_eq with h_nat
      exact (Nat.ne_of_lt (Nat.lt_succ_self ctx.cs.nextReg)) h_nat
    have h_res_ne_loaded : resReg ctx ≠ loadedPtrReg ctx := by
      intro h_eq
      unfold resReg loadedPtrReg DerefFreshCtx.resReg DerefFreshCtx.loadedPtrReg at h_eq
      have h_reg : Register.R ctx.cs.nextReg = Register.R (ctx.cs.nextReg + 2) := by
        simpa [h_src_off] using h_eq
      injection h_reg with h_nat
      have h_ne : ctx.cs.nextReg ≠ ctx.cs.nextReg + 2 :=
        Nat.ne_of_lt (Nat.lt_succ_of_lt (Nat.lt_succ_self ctx.cs.nextReg))
      exact h_ne h_nat
    have h_src_reg_pre :
        s_osea_pre.reg.lookup (resReg ctx) =
          some (TyVal.PTy, [oseair.Val.Ptr allocBase_o 0 (blockSize ctx.innerLayout) allocTag_o]) := by
      simp [s_osea_pre, h_res_ne_srcTmp, h_res_ne_loaded]
    have h_dstReg_fresh :
        ∀ base layout,
          ctx.cs.placeMap.lookup base = some (dstReg ctx, layout) → False := by
      simpa [dstReg, DerefFreshCtx.dstReg, h_src_off] using
        (alloc_fresh_reg_of_ge (cs := ctx.cs) ctx.h_regs_below (Nat.le_add_right _ 3))
    have h_temp_read_exact :
        oseair.readWordSeq s_osea_pre.mem allocBase_o (blockSize ctx.innerLayout) = vals_temp := by
      simpa [s_osea_pre, vals_temp] using
        (oseair_readWordSeq_write_exact allocMem_o allocBase_o vals_temp)
    have h_vals :
        mem_vals_eq ptr_sim
          (mirlite.readWordSeq s_mir.mem targetAddr_m (blockSize ctx.innerLayout))
          (oseair.readWordSeq s_osea_pre.mem allocBase_o (blockSize ctx.innerLayout)) := by
      rw [h_temp_read_exact]
      simpa [vals_temp] using h_target_vals
    have h_start_suffix :
        StartsAt prog_osea s_osea_pre.pc
          [oseair.Instr.Assgn (dstReg ctx) (oseair.Rhs.Alloc (innerTy ctx)),
           oseair.Instr.Memcpy (dstReg ctx) (resReg ctx) (innerTy ctx)] := by
      simpa [s_osea_pre] using starts_projected_suffix ctx h_osea_start h_src_off
    have h_len :
        (mirlite.readWordSeq s_mir.mem targetAddr_m (blockSize ctx.innerLayout)).length =
          blockSize ctx.innerLayout := by
      simpa using mirlite_readWordSeq_length s_mir.mem targetAddr_m (blockSize ctx.innerLayout)
    obtain ⟨allocBase_o, freshTag_o, ρa', ρt', s_osea_next,
        h_ρa', h_ρt', h_steps, h_sim_next, h_noninterference_next, h_pc_tail⟩ :=
      finish_from_pre
        (A_o := oseair.bumpAllocator) ctx
        (ptr_sim := ptr_sim)
        (s_mir_pre := s_mir_pre)
        (s_mir_next := s_mir_next)
        (s_osea_pre := s_osea_pre)
        (prog_osea := prog_osea)
        (vals_mir := mirlite.readWordSeq s_mir.mem targetAddr_m (blockSize ctx.innerLayout))
        (freshAddr_m := freshAddr_m)
        (allocMem_m := allocMem_m)
        (freshTag_m := freshTag_m)
        (ap_alloc_m := ap_alloc_m)
        (ap_write_m := ap_write_m)
        (tempBase_o := allocBase_o)
        (tempTag_o := allocTag_o)
        h_sim_pre h_noninterference_pre h_source_below_pre h_tag_fresh_pre
        h_temp_unmapped_alloc h_find_temp_pre
        h_start_suffix h_src_reg_pre h_dstReg_fresh
        h_mir_own h_mir_use h_alloc_mMap_m h_alloc_base_m
        (by simp [oseair.bumpAllocator, oseair.allocate])
        (by simp [oseair.bumpAllocator, oseair.allocate])
        _h_inner_nonempty h_mir_next_pre h_vals h_len
    exact ⟨freshAddr_m, allocBase_o, freshTag_m, freshTag_o, ρa', ρt', s_osea_next,
      h_freshTag_eq_next, h_ρa', h_ρt',
      StepStarWith.trans (StepStarWith.of_runN_ok h_prefix_run) h_steps,
      h_sim_next, h_noninterference_next, h_env_next, h_nextTag_post,
      by
        simpa [s_osea_pre, DerefFreshCtx.compiled, h_src_off, Nat.add_assoc] using h_pc_tail⟩

theorem simulation
  (ctx : DerefFreshCtx)
  {ρa : AddrRenameMap}
  {ρt : TagRenameMap}
  {s_mir s_mir_next : mirlite.State}
  {s_osea : oseair.State}
  {prog_mir : mirlite.Prog}
  {prog_osea : oseair.Prog}
  (h_sim :
    LocalSim ctx ρa ρt s_mir s_osea
      (ptrSimOfCtx ρa ρt s_mir.env))
  (h_noninterference : TargetNonInterference ρa s_osea)
  (h_source_below : SourceBlocksBelowAddrStart ctx.cs.placeMap s_mir)
  (h_tag_fresh : ∀ tag, s_mir.ap.NextTag ≤ tag → ρt tag = none)
  (h_source_alloc_base :
    (A_m.alloc s_mir.mem (typeSize (layoutToTyVal ctx.innerLayout))).1 = s_mir.mem.addrStart)
  (h_dst_env : s_mir.env.lookup ctx.dst.base = none)
  (h_mir_start : StartsAt prog_mir s_mir.pc [stmt ctx])
  (h_mir_step :
    mirlite.stepWith A_m s_mir prog_mir = mirlite.Result.Ok s_mir_next)
  (h_pointee_tracked :
    ∀ srcBaseAddr_m srcTag_m q gq ap_src_read_m targetRes,
      s_mir.env.lookup ctx.src.base =
        some (srcBaseAddr_m, layoutToTyVal ctx.srcBaseLayout, srcTag_m) →
      s_mir.mem.find? (srcBaseAddr_m + ctx.srcOff) =
        some (mirlite.MemValue.PlaceTag q gq) →
      mirlite.resolveDirectPlace { s_mir with ap := ap_src_read_m } q =
        (mirlite.Result.Ok { s_mir with ap := ap_src_read_m }, targetRes) →
      ∃ targetReg targetBaseLayout targetOff targetBaseAddr,
        ctx.cs.placeMap.lookup q.base = some (targetReg, targetBaseLayout) ∧
        layoutResolvePath targetBaseLayout q.path = some (targetOff, ctx.innerLayout) ∧
        s_mir.env.lookup q.base =
          some (targetBaseAddr, layoutToTyVal targetBaseLayout, targetRes.tag) ∧
        targetRes.addr = targetBaseAddr + targetOff ∧
        targetRes.ty = layoutToTyVal ctx.innerLayout)
  (h_osea_start :
    StartsAt prog_osea s_osea.pc (DerefFreshCtx.compiled ctx))
  (h_inner_nonempty : 0 < blockSize ctx.innerLayout) :
  ∃ ρa' ρt' s_osea_next,
    StepStarWith oseair.bumpAllocator s_osea prog_osea s_osea_next ∧
    StateSim (postPlaceMap ctx) ρa' ρt' s_mir_next s_osea_next
      (ptrSimOfCtx ρa ρt s_mir.env) ∧
    TargetNonInterference ρa' s_osea_next ∧
    s_osea_next.pc = s_osea.pc + (DerefFreshCtx.compiled ctx).length := by
  obtain ⟨_freshAddr_m, _allocBase_o, _freshTag_m, _freshTag_o, ρa', ρt', s_osea_next,
      _h_tag_eq, _h_ρa', _h_ρt', h_steps, h_sim_next, h_noninterference_next,
      _h_env_next, _h_nextTag_post, h_pc⟩ :=
    simulation_structured
      (A_m := A_m)
      (ctx := ctx)
      (h_sim := h_sim)
      (h_noninterference := h_noninterference)
      (h_source_below := h_source_below)
      (h_tag_fresh := h_tag_fresh)
      (h_source_alloc_base := h_source_alloc_base)
      (h_dst_env := h_dst_env)
      (h_mir_start := h_mir_start)
      (h_mir_step := h_mir_step)
      (h_pointee_tracked := h_pointee_tracked)
      (h_osea_start := h_osea_start)
      h_inner_nonempty
  exact ⟨ρa', ρt', s_osea_next, h_steps, h_sim_next, h_noninterference_next, h_pc⟩

end DerefFresh

namespace DerefExisting

def toProjectedCtx (ctx : DerefExistingCtx) : DerefProjectedExistingCtx where
  src := ctx.src
  dst := ctx.dst
  srcReg := ctx.srcReg
  dstReg := ctx.dstReg
  srcBaseLayout := LayoutTy.PtrL ctx.innerLayout
  innerLayout := ctx.innerLayout
  dstBaseLayout := ctx.innerLayout
  srcOff := 0
  dstOff := 0
  cs := ctx.cs
  h_regs_below := ctx.h_regs_below
  h_instrs := ctx.h_instrs
  h_src_lookup := ctx.h_src_lookup
  h_dst_lookup := ctx.h_dst_lookup
  h_src_path := by simp [ctx.h_src_base, layoutResolvePath]
  h_dst_path := by simp [ctx.h_dst_base, layoutResolvePath]

theorem simulation
  (ctx : DerefExistingCtx)
  {ρa : AddrRenameMap}
  {ρt : TagRenameMap}
  {s_mir s_mir_next : mirlite.State}
  {s_osea : oseair.State}
  {prog_mir : mirlite.Prog}
  {prog_osea : oseair.Prog}
  (h_sim :
    LocalSim ctx ρa ρt s_mir s_osea
      (ptrSimOfCtx ρa ρt s_mir.env))
  (h_noninterference : TargetNonInterference ρa s_osea)
  (h_mir_start : StartsAt prog_mir s_mir.pc [stmt ctx])
  (h_mir_step :
    mirlite.stepWith A_m s_mir prog_mir = mirlite.Result.Ok s_mir_next)
  (h_pointee_tracked :
    ∀ srcAddr_m srcTag_m q gq ap_src_read_m targetRes,
      s_mir.env.lookup ctx.src.base =
        some (srcAddr_m, layoutToTyVal (srcLayout ctx), srcTag_m) →
      s_mir.mem.find? srcAddr_m = some (mirlite.MemValue.PlaceTag q gq) →
      mirlite.resolveDirectPlace { s_mir with ap := ap_src_read_m } q =
        (mirlite.Result.Ok { s_mir with ap := ap_src_read_m }, targetRes) →
      ∃ targetReg targetBaseLayout targetOff targetBaseAddr,
        ctx.cs.placeMap.lookup q.base = some (targetReg, targetBaseLayout) ∧
        layoutResolvePath targetBaseLayout q.path = some (targetOff, ctx.innerLayout) ∧
        s_mir.env.lookup q.base =
          some (targetBaseAddr, layoutToTyVal targetBaseLayout, targetRes.tag) ∧
        targetRes.addr = targetBaseAddr + targetOff ∧
        targetRes.ty = layoutToTyVal ctx.innerLayout)
  (h_osea_start :
    StartsAt prog_osea s_osea.pc
      [oseair.Instr.Assgn (resReg ctx) (oseair.Rhs.Alloc (innerTy ctx)),
       oseair.Instr.Assgn (loadedPtrReg ctx)
         (oseair.Rhs.Load TyVal.PTy ctx.srcReg),
       oseair.Instr.Memcpy (resReg ctx) (loadedPtrReg ctx) (innerTy ctx),
       oseair.Instr.Memcpy ctx.dstReg (resReg ctx) (innerTy ctx)])
  (h_inner_nonempty : 0 < blockSize ctx.innerLayout) :
  ∃ s_osea_next,
    StepStarWith oseair.bumpAllocator s_osea prog_osea s_osea_next ∧
    StateSim ctx.cs.placeMap ρa ρt s_mir_next s_osea_next
      (ptrSimOfCtx ρa ρt s_mir.env) ∧
    TargetNonInterference ρa s_osea_next := by
  have h_sim' :
      DerefProjectedExisting.LocalSim (toProjectedCtx ctx) ρa ρt s_mir s_osea
        (ptrSimOfCtx ρa ρt s_mir.env) := by
    simpa [DerefProjectedExisting.LocalSim, LocalSim, toProjectedCtx]
      using h_sim
  have h_mir_start' :
      StartsAt prog_mir s_mir.pc [DerefProjectedExisting.stmt (toProjectedCtx ctx)] := by
    simpa [DerefProjectedExisting.stmt, DerefProjectedExistingCtx.stmt, stmt, toProjectedCtx]
      using h_mir_start
  have h_pointee_tracked' :
      ∀ srcBaseAddr_m srcTag_m q gq ap_src_read_m targetRes,
        s_mir.env.lookup (toProjectedCtx ctx).src.base =
          some (srcBaseAddr_m, layoutToTyVal (toProjectedCtx ctx).srcBaseLayout, srcTag_m) →
        s_mir.mem.find? (srcBaseAddr_m + (toProjectedCtx ctx).srcOff) =
          some (mirlite.MemValue.PlaceTag q gq) →
        mirlite.resolveDirectPlace { s_mir with ap := ap_src_read_m } q =
          (mirlite.Result.Ok { s_mir with ap := ap_src_read_m }, targetRes) →
        ∃ targetReg targetBaseLayout targetOff targetBaseAddr,
          ctx.cs.placeMap.lookup q.base = some (targetReg, targetBaseLayout) ∧
          layoutResolvePath targetBaseLayout q.path = some (targetOff, ctx.innerLayout) ∧
          s_mir.env.lookup q.base =
            some (targetBaseAddr, layoutToTyVal targetBaseLayout, targetRes.tag) ∧
          targetRes.addr = targetBaseAddr + targetOff ∧
          targetRes.ty = layoutToTyVal ctx.innerLayout := by
    intro srcBaseAddr_m srcTag_m q gq ap_src_read_m targetRes h_env h_find h_resolve
    simpa [toProjectedCtx, srcLayout, Nat.zero_add] using
      h_pointee_tracked srcBaseAddr_m srcTag_m q gq ap_src_read_m targetRes h_env h_find h_resolve
  have h_osea_start' :
      StartsAt prog_osea s_osea.pc (DerefProjectedExistingCtx.compiled (toProjectedCtx ctx)) := by
    simpa [toProjectedCtx, DerefProjectedExistingCtx.compiled_eq]
      using h_osea_start
  obtain ⟨s_osea_next, h_steps, h_rest⟩ :=
    DerefProjectedExisting.simulation
      (A_m := A_m)
      (ctx := toProjectedCtx ctx)
      h_sim' h_noninterference h_mir_start' h_mir_step h_pointee_tracked'
      h_osea_start' h_inner_nonempty
  rcases h_rest with ⟨h_sim_next, h_noninterference_next, _h_pc⟩
  exact ⟨s_osea_next, h_steps, by
    simpa [DerefProjectedExisting.LocalSim, LocalSim, toProjectedCtx] using h_sim_next,
    h_noninterference_next⟩

end DerefExisting

end obseq.proof
