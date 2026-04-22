import obseq.proof.state_helpers

/-!
# `obseq.proof.ref`

Simulation proof for the `RefOp` MIR operation with existing destinations and
explicit projected-place data on both the source and destination sides.
-/

namespace obseq.proof

open obseq
open obseq.mirlite
open obseq.oseair hiding State Result
open obseq.compile
open scoped obseq.notation

variable {A_m : mirlite.AllocatorSpec} {A_o : oseair.AllocatorSpec}

def kindToRefOpKind : mirlite.RefKind → RefOpKind
  | .Shared => .Shared
  | .Mut    => .Mut
  | .Raw    => .Raw

def kindToOseaRhs (kind : mirlite.RefKind) (baseReg : Register) (off : Word) : oseair.Rhs :=
  match kind with
  | .Shared => Rhs.BorOffset baseReg off
  | .Mut    => Rhs.MutBorOffset baseReg off
  | .Raw    => Rhs.CopyOffset baseReg off

theorem sb_read_nextTag_eq
  {ap ap' : AccessPerms}
  {addr tag : Word}
  (h_read : sb_read ap addr tag = SBResult.Ok ap') :
  ap'.NextTag = ap.NextTag := by
  unfold sb_read at h_read
  cases h_find : ap.StackMap.find? addr with
  | none =>
      simp [h_find] at h_read
  | some stack =>
      cases h_split : splitStack stack tag with
      | none =>
          simp [h_find, h_split] at h_read
      | some triple =>
          rcases triple with ⟨x, item, y⟩
          cases item <;> simp [h_find, h_split] at h_read
          all_goals
            cases h_read
            rfl

theorem sb_use_mb_nextTag_eq
  {ap ap' : AccessPerms}
  {addr tag : Word}
  (h_use : sb_use_mb ap addr tag = SBResult.Ok ap') :
  ap'.NextTag = ap.NextTag := by
  unfold sb_use_mb at h_use
  cases h_find : ap.StackMap.find? addr with
  | none =>
      simp [h_find] at h_use
  | some stack =>
      cases h_split : splitStack stack tag with
      | none =>
          simp [h_find, h_split] at h_use
      | some triple =>
          rcases triple with ⟨x, item, y⟩
          cases item <;> simp [h_find, h_split] at h_use
          all_goals
            cases h_use
            rfl

theorem sb_ref_tag_eq_nextTag
  {ap ap' : AccessPerms}
  {addr tag newTag : Word}
  {kind : RefOpKind}
  (h_ref : sb_ref ap addr tag kind = (SBResult.Ok ap', newTag)) :
  newTag = ap.NextTag := by
  cases kind with
  | Shared =>
      unfold sb_ref at h_ref
      cases h_parent : sb_read ap addr tag with
      | Err msg =>
          simp [h_parent] at h_ref
      | Ok ap_parent =>
          have h_parent_next : ap_parent.NextTag = ap.NextTag :=
            sb_read_nextTag_eq h_parent
          cases h_find : ap_parent.StackMap.find? addr with
          | none =>
              simp [h_parent, h_find, freshTag] at h_ref
          | some stack =>
              simp [h_parent, h_find, freshTag] at h_ref
              rcases h_ref with ⟨_h_ap, h_tag⟩
              simpa [h_parent_next] using h_tag.symm
  | Mut =>
      unfold sb_ref at h_ref
      cases h_parent : sb_use_mb ap addr tag with
      | Err msg =>
          simp [h_parent] at h_ref
      | Ok ap_parent =>
          have h_parent_next : ap_parent.NextTag = ap.NextTag :=
            sb_use_mb_nextTag_eq h_parent
          cases h_find : ap_parent.StackMap.find? addr with
          | none =>
              simp [h_parent, h_find, freshTag] at h_ref
          | some stack =>
              simp [h_parent, h_find, freshTag] at h_ref
              rcases h_ref with ⟨_h_ap, h_tag⟩
              simpa [h_parent_next] using h_tag.symm
  | Raw =>
      unfold sb_ref at h_ref
      cases h_parent : sb_use_mb ap addr tag with
      | Err msg =>
          simp [h_parent] at h_ref
      | Ok ap_parent =>
          have h_parent_next : ap_parent.NextTag = ap.NextTag :=
            sb_use_mb_nextTag_eq h_parent
          cases h_find : ap_parent.StackMap.find? addr with
          | none =>
              simp [h_parent, h_find, freshTag] at h_ref
          | some stack =>
              simp [h_parent, h_find, freshTag] at h_ref
              rcases h_ref with ⟨_h_ap, h_tag⟩
              simpa [h_parent_next] using h_tag.symm

theorem step_Assgn_BorKind
  (s : oseair.State) (prog : oseair.Prog)
  (tmpReg baseReg : Register) (kind : mirlite.RefKind) (off : Word)
  (addr baseOff size tag : Word) (ap' : AccessPerms) (newTag : Tag)
  (h_pc : s.pc < prog.length)
  (h_get : prog.get ⟨s.pc, h_pc⟩ =
    oseair.Instr.Assgn tmpReg (kindToOseaRhs kind baseReg off))
  (h_base_reg :
    s.reg.lookup baseReg = some (TyVal.PTy, [Val.Ptr addr baseOff size tag]))
  (h_off : addr + baseOff + off < addr + size)
  (h_ref :
    sb_ref s.ap (addr + baseOff + off) tag (kindToRefOpKind kind) =
      (SBResult.Ok ap', newTag)) :
  oseair.stepWith A_o s prog = oseair.Result.Ok {
    reg := s.reg.insert tmpReg
      (TyVal.PTy, [Val.Ptr addr (baseOff + off) size newTag]),
    ap := ap', mem := s.mem, pc := s.pc + 1 } := by
  cases kind with
  | Shared =>
      simpa [kindToOseaRhs, kindToRefOpKind] using
        (oseair.step_Assgn_BorOffsetWith A_o s prog tmpReg baseReg off
          addr baseOff size tag ap' newTag
          h_pc h_get h_base_reg h_off h_ref)
  | Mut =>
      simpa [kindToOseaRhs, kindToRefOpKind] using
        (oseair.step_Assgn_MutBorOffsetWith A_o s prog tmpReg baseReg off
          addr baseOff size tag ap' newTag
          h_pc h_get h_base_reg h_off h_ref)
  | Raw =>
      simpa [kindToOseaRhs, kindToRefOpKind] using
        (oseair.step_Assgn_CopyOffsetWith A_o s prog tmpReg baseReg off
          addr baseOff size tag ap' newTag
          h_pc h_get h_base_reg h_off h_ref)

structure RefExistingCtx where
  src : mirlite.Place
  dst : mirlite.Place
  kind : mirlite.RefKind
  srcReg : Register
  dstReg : Register
  srcBaseLayout : LayoutTy
  srcLayout : LayoutTy
  dstBaseLayout : LayoutTy
  srcOff : Word
  dstOff : Word
  cs : CompilerState
  h_regs_below : PlaceMapRegsBelowNextReg cs
  h_instrs : CompilerEmpty cs
  h_src_lookup : BaseReady cs src.base srcReg srcBaseLayout
  h_dst_lookup : BaseReady cs dst.base dstReg dstBaseLayout
  h_src_path : layoutResolvePath srcBaseLayout src.path = some (srcOff, srcLayout)
  h_dst_path : layoutResolvePath dstBaseLayout dst.path = some (dstOff, LayoutTy.PtrL srcLayout)

namespace RefExistingCtx

def stmt (ctx : RefExistingCtx) : mirlite.Stmt :=
  mirlite.Stmt.Assgn (mirlite.LExpr.Place ctx.dst) (mirlite.RExpr.RefOp ctx.kind ctx.src)

def resReg (ctx : RefExistingCtx) : Register :=
  Register.R ctx.cs.nextReg

def borReg (ctx : RefExistingCtx) : Register :=
  Register.R (ctx.cs.nextReg + 1)

def dstTmpReg (ctx : RefExistingCtx) : Register :=
  Register.R (ctx.cs.nextReg + 2)

def dstLayout (ctx : RefExistingCtx) : LayoutTy :=
  LayoutTy.PtrL ctx.srcLayout

def compiled (ctx : RefExistingCtx) : oseair.Prog :=
  (compileStmt ctx.cs ctx.stmt).instrs

theorem instrs_nil (ctx : RefExistingCtx) : ctx.cs.instrs = [] :=
  ctx.h_instrs

section

@[simp] theorem compiled_eq
  (ctx : RefExistingCtx) :
  ctx.compiled =
    if ctx.dstOff = 0 then
      [oseair.Instr.Assgn (ctx.resReg) (oseair.Rhs.Alloc TyVal.PTy),
       oseair.Instr.Assgn (ctx.borReg) (kindToOseaRhs ctx.kind ctx.srcReg ctx.srcOff),
       oseair.Instr.RStore TyVal.PTy (ctx.borReg) (ctx.resReg),
       oseair.Instr.Memcpy ctx.dstReg (ctx.resReg) TyVal.PTy]
    else
      [oseair.Instr.Assgn (ctx.resReg) (oseair.Rhs.Alloc TyVal.PTy),
       oseair.Instr.Assgn (ctx.borReg) (kindToOseaRhs ctx.kind ctx.srcReg ctx.srcOff),
       oseair.Instr.RStore TyVal.PTy (ctx.borReg) (ctx.resReg),
       oseair.Instr.Assgn (ctx.dstTmpReg) (oseair.Rhs.MutBorOffset ctx.dstReg ctx.dstOff),
       oseair.Instr.Memcpy (ctx.dstTmpReg) (ctx.resReg) TyVal.PTy,
       oseair.Instr.Die (ctx.dstTmpReg)] := by
  let csAlloc : CompilerState :=
    { nextReg := ctx.cs.nextReg + 1,
      placeMap := ctx.cs.placeMap,
      instrs := ctx.cs.instrs ++
        [oseair.Instr.Assgn (ctx.resReg) (oseair.Rhs.Alloc TyVal.PTy)] }
  let rhsCs : CompilerState :=
    { nextReg := ctx.cs.nextReg + 2,
      placeMap := ctx.cs.placeMap,
      instrs := ctx.cs.instrs ++
        [oseair.Instr.Assgn (ctx.resReg) (oseair.Rhs.Alloc TyVal.PTy),
         oseair.Instr.Assgn (ctx.borReg) (kindToOseaRhs ctx.kind ctx.srcReg ctx.srcOff),
         oseair.Instr.RStore TyVal.PTy (ctx.borReg) (ctx.resReg)] }
  have h_src_lookup_alloc :
      getPlaceInfo csAlloc ctx.src.base = some (ctx.srcReg, ctx.srcBaseLayout) := by
    simpa [csAlloc, getPlaceInfo] using ctx.h_src_lookup
  have h_dst_lookup_rhs :
      getPlaceInfo rhsCs ctx.dst.base = some (ctx.dstReg, ctx.dstBaseLayout) := by
    simpa [rhsCs, getPlaceInfo] using ctx.h_dst_lookup
  have h_src_place :
      placeToBorrowReg csAlloc ctx.src ctx.kind =
        { reg := ctx.borReg,
          layout := ctx.srcLayout,
          cleanup := [ctx.borReg],
          cs :=
            { nextReg := ctx.cs.nextReg + 2,
              placeMap := ctx.cs.placeMap,
              instrs := ctx.cs.instrs ++
                [oseair.Instr.Assgn (ctx.resReg) (oseair.Rhs.Alloc TyVal.PTy),
                 oseair.Instr.Assgn (ctx.borReg) (kindToOseaRhs ctx.kind ctx.srcReg ctx.srcOff)] } } := by
    unfold placeToBorrowReg
    change
      (match getPlaceInfo csAlloc ctx.src.base with
      | some (baseReg, baseLayout) =>
          match layoutResolvePath baseLayout ctx.src.path with
          | some (offset, placeLayout) =>
              let (tmpReg, cs1) := freshReg csAlloc
              let rhs := match ctx.kind with
                | mirlite.RefKind.Shared => oseair.Rhs.BorOffset baseReg offset
                | mirlite.RefKind.Mut => oseair.Rhs.MutBorOffset baseReg offset
                | mirlite.RefKind.Raw => oseair.Rhs.CopyOffset baseReg offset
              let cs2 := emit cs1 [oseair.Instr.Assgn tmpReg rhs]
              ({ reg := tmpReg, layout := placeLayout, cleanup := [tmpReg], cs := cs2 } : PtrResult)
          | none =>
              ({ reg := Register.R 0, layout := LayoutTy.NatL, cleanup := [], cs := csAlloc } : PtrResult)
      | none =>
          ({ reg := Register.R 0, layout := LayoutTy.NatL, cleanup := [], cs := csAlloc } : PtrResult)) = _
    rw [h_src_lookup_alloc]
    simp [ctx.h_src_path, csAlloc, ctx.instrs_nil,
      RefExistingCtx.borReg, RefExistingCtx.resReg,
      freshReg, emit, kindToOseaRhs]
  have h_layout :
      inferRExprLayout ctx.cs (mirlite.RExpr.RefOp ctx.kind ctx.src) =
        LayoutTy.PtrL ctx.srcLayout := by
    have h_place_layout : placeLayout? ctx.cs ctx.src = some ctx.srcLayout := by
      unfold placeLayout?
      rw [ctx.h_src_lookup]
      simp [ctx.h_src_path]
    simp [inferRExprLayout, h_place_layout]
  have h_rhs_to :
      compileRExprToFuel 1 csAlloc ctx.resReg (mirlite.RExpr.RefOp ctx.kind ctx.src) = rhsCs := by
    simp [compileRExprToFuel, staticRExprData?]
    rw [h_src_place]
    simp [rhsCs, ctx.instrs_nil, emit, kindToOseaRhs]
  have h_rhs :
      compileRExpr ctx.cs (mirlite.RExpr.RefOp ctx.kind ctx.src) =
        { reg := ctx.resReg, layout := LayoutTy.PtrL ctx.srcLayout, cs := rhsCs } := by
    simpa [compileRExpr, compileRExprFuel, mirlite.rExprFuel, h_layout, csAlloc, rhsCs,
      ctx.instrs_nil, RefExistingCtx.resReg, freshReg, emit] using h_rhs_to
  by_cases h_off : ctx.dstOff = 0
  · have h_dst_place :
        placeToReg rhsCs ctx.dst mirlite.RefKind.Mut (some (LayoutTy.PtrL ctx.srcLayout)) =
          { reg := ctx.dstReg,
            layout := LayoutTy.PtrL ctx.srcLayout,
            cleanup := [],
            cs := rhsCs } := by
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
            match some (LayoutTy.PtrL ctx.srcLayout) with
            | some baseLayout =>
                if (ctx.dst.path == []) = true then
                  let (newReg, cs1) := freshReg rhsCs
                  let cs2 := emit cs1 [oseair.Instr.Assgn newReg (oseair.Rhs.Alloc (layoutToTyVal baseLayout))]
                  let cs3 := setPlace cs2 ctx.dst.base newReg baseLayout
                  ({ reg := newReg, layout := baseLayout, cleanup := [], cs := cs3 } : PtrResult)
                else
                  ({ reg := Register.R 0, layout := baseLayout, cleanup := [], cs := rhsCs } : PtrResult)
            | none =>
                ({ reg := Register.R 0, layout := LayoutTy.NatL, cleanup := [], cs := rhsCs } : PtrResult)) = _
      rw [h_dst_lookup_rhs]
      simp [ctx.h_dst_path, rhsCs, h_off, ctx.instrs_nil]
    unfold RefExistingCtx.compiled RefExistingCtx.stmt compileStmt
    simp [h_rhs]
    rw [h_dst_place]
    simp [rhsCs, emit, cleanupInstrs, ctx.instrs_nil, layoutToTyVal, h_off]
  · have h_dst_place :
        placeToReg rhsCs ctx.dst mirlite.RefKind.Mut (some (LayoutTy.PtrL ctx.srcLayout)) =
          { reg := ctx.dstTmpReg,
            layout := LayoutTy.PtrL ctx.srcLayout,
            cleanup := [ctx.dstTmpReg],
            cs :=
              { nextReg := ctx.cs.nextReg + 3,
                placeMap := ctx.cs.placeMap,
                instrs := ctx.cs.instrs ++
                [oseair.Instr.Assgn (ctx.resReg) (oseair.Rhs.Alloc TyVal.PTy),
                 oseair.Instr.Assgn (ctx.borReg) (kindToOseaRhs ctx.kind ctx.srcReg ctx.srcOff),
                 oseair.Instr.RStore TyVal.PTy (ctx.borReg) (ctx.resReg),
                 oseair.Instr.Assgn (ctx.dstTmpReg) (oseair.Rhs.MutBorOffset ctx.dstReg ctx.dstOff)] } } := by
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
            match some (LayoutTy.PtrL ctx.srcLayout) with
            | some baseLayout =>
                if (ctx.dst.path == []) = true then
                  let (newReg, cs1) := freshReg rhsCs
                  let cs2 := emit cs1 [oseair.Instr.Assgn newReg (oseair.Rhs.Alloc (layoutToTyVal baseLayout))]
                  let cs3 := setPlace cs2 ctx.dst.base newReg baseLayout
                  ({ reg := newReg, layout := baseLayout, cleanup := [], cs := cs3 } : PtrResult)
                else
                  ({ reg := Register.R 0, layout := baseLayout, cleanup := [], cs := rhsCs } : PtrResult)
            | none =>
                ({ reg := Register.R 0, layout := LayoutTy.NatL, cleanup := [], cs := rhsCs } : PtrResult)) = _
      rw [h_dst_lookup_rhs]
      simp [ctx.h_dst_path, rhsCs, h_off, ctx.instrs_nil,
        RefExistingCtx.dstTmpReg, freshReg, emit]
    unfold RefExistingCtx.compiled RefExistingCtx.stmt compileStmt
    simp [h_rhs]
    rw [h_dst_place]
    simp [emit, cleanupInstrs, RefExistingCtx.dstTmpReg,
      ctx.instrs_nil, layoutToTyVal, h_off]

end

end RefExistingCtx

namespace RefExisting

variable (ctx : RefExistingCtx)

abbrev stmt : mirlite.Stmt := RefExistingCtx.stmt ctx
abbrev resReg : Register := RefExistingCtx.resReg ctx
abbrev borReg : Register := RefExistingCtx.borReg ctx
abbrev dstTmpReg : Register := RefExistingCtx.dstTmpReg ctx
abbrev dstLayout : LayoutTy := RefExistingCtx.dstLayout ctx

abbrev LocalSim
  (ρa : AddrRenameMap) (ρt : TagRenameMap)
  (s_mir : mirlite.State) (s_osea : oseair.State)
  (ptr_sim : PtrSimPred := defaultPtrSim) : Prop :=
  StateSim ctx.cs.placeMap ρa ρt s_mir s_osea ptr_sim

def tempVals (srcBase_o borTag_o : Word) : List oseair.Val :=
  [oseair.Val.Ptr srcBase_o ctx.srcOff (blockSize ctx.srcBaseLayout) borTag_o]

def prefixPost
  (s_osea : oseair.State)
  (allocBase_o : Word)
  (allocMem_o : oseair.Mem)
  (srcBase_o allocTag_o borTag_o : Word)
  (ap_rstore_o : AccessPerms) : oseair.State :=
  { s_osea with
    reg :=
      ((s_osea.reg.insert (resReg ctx)
        (TyVal.PTy, [oseair.Val.Ptr allocBase_o 0 1 allocTag_o])).insert
        (borReg ctx)
        (TyVal.PTy, tempVals ctx srcBase_o borTag_o)),
    ap := ap_rstore_o,
    mem := oseair.writeWordSeq allocMem_o allocBase_o (tempVals ctx srcBase_o borTag_o),
    pc := s_osea.pc + 3 }

def postPtrSim
  (ptr_sim : PtrSimPred)
  (srcBase_o newTag_m borTag_o : Word) : PtrSimPred :=
  fun p tag_m base off size tag_o =>
    ptr_sim p tag_m base off size tag_o ∨
      (p = ctx.src ∧
        tag_m = newTag_m ∧
        base = srcBase_o ∧
        off = ctx.srcOff ∧
        size = blockSize ctx.srcBaseLayout ∧
        tag_o = borTag_o)

theorem sb_read_ok_of_find_own
  {ap : AccessPerms}
  {addr tag : Word}
  (h_find : ap.StackMap.find? addr = some [RefKind.Own tag]) :
  ∃ ap', sb_read ap addr tag = SBResult.Ok ap' := by
  exact sb_read_of_find_own h_find

theorem mirlite_step_inv
  (s_mir s_mir_next : mirlite.State)
  (prog_mir : mirlite.Prog)
  (srcBaseAddr srcBaseTag dstBaseAddr dstBaseTag : Word)
  (h_src_env :
    s_mir.env.lookup ctx.src.base =
      some (srcBaseAddr, layoutToTyVal ctx.srcBaseLayout, srcBaseTag))
  (h_dst_env :
    s_mir.env.lookup ctx.dst.base =
      some (dstBaseAddr, layoutToTyVal ctx.dstBaseLayout, dstBaseTag))
  (h_start : StartsAt prog_mir s_mir.pc [stmt ctx])
  (h_step : mirlite.stepWith A_m s_mir prog_mir = mirlite.Result.Ok s_mir_next) :
  ∃ ap_ref newTag ap_write,
    sb_ref s_mir.ap (srcBaseAddr + ctx.srcOff) srcBaseTag (kindToRefOpKind ctx.kind) =
      (SBResult.Ok ap_ref, newTag) ∧
    sb_use_mb ap_ref (dstBaseAddr + ctx.dstOff) dstBaseTag = SBResult.Ok ap_write ∧
    s_mir_next =
      { s_mir with
        ap := ap_write,
        mem := mirlite.writeWordSeq s_mir.mem (dstBaseAddr + ctx.dstOff)
          [mirlite.MemValue.PlaceTag ctx.src newTag],
        pc := s_mir.pc + 1 } := by
  have h_stmt_mir : prog_mir.get? s_mir.pc = some (stmt ctx) := StartsAt.singleton h_start
  rcases List.get?_eq_some_iff.mp h_stmt_mir with ⟨h_pc_mir, h_get_mir⟩
  cases h_kind : ctx.kind with
  | Shared =>
      unfold mirlite.stepWith at h_step
      rw [dif_pos h_pc_mir, h_get_mir] at h_step
      simp [stmt, RefExistingCtx.stmt, mirlite.stepAssignGenericWith, mirlite.evalRExpr, h_kind] at h_step
      rw [resolveDirectPlace_eq_of_env_lookup h_src_env ctx.h_src_path] at h_step
      cases h_ref : sb_ref s_mir.ap (srcBaseAddr + ctx.srcOff) srcBaseTag RefOpKind.Shared with
      | mk sb_res newTag =>
          cases sb_res with
          | Err _ =>
              simp [h_ref] at h_step
          | Ok ap_ref =>
              simp [h_ref] at h_step
              have h_dst_env' :
                  { s_mir with ap := ap_ref }.env.lookup ctx.dst.base =
                    some (dstBaseAddr, layoutToTyVal ctx.dstBaseLayout, dstBaseTag) := by
                simpa using h_dst_env
              rw [finishPlaceAssignWith_existing_eq
                (pc0 := s_mir.pc)
                (state := { s_mir with ap := ap_ref })
                (p := ctx.dst)
                (vals := [mirlite.MemValue.PlaceTag ctx.src newTag])
                (ty := TyVal.PTy)
                (addr := dstBaseAddr)
                (tag := dstBaseTag)
                (off := ctx.dstOff)
                (baseLayout := ctx.dstBaseLayout)
                (subLayout := dstLayout ctx)
                h_dst_env' ctx.h_dst_path] at h_step
              cases h_use : sb_use_mb ap_ref (dstBaseAddr + ctx.dstOff) dstBaseTag with
              | Err _ =>
                  simp [h_use] at h_step
              | Ok ap_write =>
                  refine ⟨ap_ref, newTag, ap_write, by simpa [kindToRefOpKind] using h_ref, h_use, ?_⟩
                  simpa [h_use] using h_step.symm
  | Mut =>
      unfold mirlite.stepWith at h_step
      rw [dif_pos h_pc_mir, h_get_mir] at h_step
      simp [stmt, RefExistingCtx.stmt, mirlite.stepAssignGenericWith, mirlite.evalRExpr, h_kind] at h_step
      rw [resolveDirectPlace_eq_of_env_lookup h_src_env ctx.h_src_path] at h_step
      cases h_ref : sb_ref s_mir.ap (srcBaseAddr + ctx.srcOff) srcBaseTag RefOpKind.Mut with
      | mk sb_res newTag =>
          cases sb_res with
          | Err _ =>
              simp [h_ref] at h_step
          | Ok ap_ref =>
              simp [h_ref] at h_step
              have h_dst_env' :
                  { s_mir with ap := ap_ref }.env.lookup ctx.dst.base =
                    some (dstBaseAddr, layoutToTyVal ctx.dstBaseLayout, dstBaseTag) := by
                simpa using h_dst_env
              rw [finishPlaceAssignWith_existing_eq
                (pc0 := s_mir.pc)
                (state := { s_mir with ap := ap_ref })
                (p := ctx.dst)
                (vals := [mirlite.MemValue.PlaceTag ctx.src newTag])
                (ty := TyVal.PTy)
                (addr := dstBaseAddr)
                (tag := dstBaseTag)
                (off := ctx.dstOff)
                (baseLayout := ctx.dstBaseLayout)
                (subLayout := dstLayout ctx)
                h_dst_env' ctx.h_dst_path] at h_step
              cases h_use : sb_use_mb ap_ref (dstBaseAddr + ctx.dstOff) dstBaseTag with
              | Err _ =>
                  simp [h_use] at h_step
              | Ok ap_write =>
                  refine ⟨ap_ref, newTag, ap_write, by simpa [kindToRefOpKind] using h_ref, h_use, ?_⟩
                  simpa [h_use] using h_step.symm
  | Raw =>
      unfold mirlite.stepWith at h_step
      rw [dif_pos h_pc_mir, h_get_mir] at h_step
      simp [stmt, RefExistingCtx.stmt, mirlite.stepAssignGenericWith, mirlite.evalRExpr, h_kind] at h_step
      rw [resolveDirectPlace_eq_of_env_lookup h_src_env ctx.h_src_path] at h_step
      cases h_ref : sb_ref s_mir.ap (srcBaseAddr + ctx.srcOff) srcBaseTag RefOpKind.Raw with
      | mk sb_res newTag =>
          cases sb_res with
          | Err _ =>
              simp [h_ref] at h_step
          | Ok ap_ref =>
              simp [h_ref] at h_step
              have h_dst_env' :
                  { s_mir with ap := ap_ref }.env.lookup ctx.dst.base =
                    some (dstBaseAddr, layoutToTyVal ctx.dstBaseLayout, dstBaseTag) := by
                simpa using h_dst_env
              rw [finishPlaceAssignWith_existing_eq
                (pc0 := s_mir.pc)
                (state := { s_mir with ap := ap_ref })
                (p := ctx.dst)
                (vals := [mirlite.MemValue.PlaceTag ctx.src newTag])
                (ty := TyVal.PTy)
                (addr := dstBaseAddr)
                (tag := dstBaseTag)
                (off := ctx.dstOff)
                (baseLayout := ctx.dstBaseLayout)
                (subLayout := dstLayout ctx)
                h_dst_env' ctx.h_dst_path] at h_step
              cases h_use : sb_use_mb ap_ref (dstBaseAddr + ctx.dstOff) dstBaseTag with
              | Err _ =>
                  simp [h_use] at h_step
              | Ok ap_write =>
                  refine ⟨ap_ref, newTag, ap_write, by simpa [kindToRefOpKind] using h_ref, h_use, ?_⟩
                  simpa [h_use] using h_step.symm

theorem osea_prefix_run_ok
  (s_osea : oseair.State)
  (prog_osea : oseair.Prog)
  (srcBase_o srcTag_o : Word)
  (allocBase_o : Word)
  (allocMem_o : oseair.Mem)
  (allocTag_o : Tag)
  (ap_own_o : AccessPerms)
  (borTag_o : Tag)
  (ap_ref_o ap_rstore_o : AccessPerms)
  (h_stmt0 :
    prog_osea.get? s_osea.pc =
      some (oseair.Instr.Assgn (resReg ctx) (oseair.Rhs.Alloc TyVal.PTy)))
  (h_stmt1 :
    prog_osea.get? (s_osea.pc + 1) =
      some (oseair.Instr.Assgn (borReg ctx)
        (kindToOseaRhs ctx.kind ctx.srcReg ctx.srcOff)))
  (h_stmt2 :
    prog_osea.get? (s_osea.pc + 2) =
      some (oseair.Instr.RStore TyVal.PTy (borReg ctx) (resReg ctx)))
  (h_src_reg :
    s_osea.reg.lookup ctx.srcReg =
      some (TyVal.PTy, [Val.Ptr srcBase_o 0 (blockSize ctx.srcBaseLayout) srcTag_o]))
  (h_src_nonempty : 0 < blockSize ctx.srcLayout)
  (h_src_fit : ctx.srcOff + blockSize ctx.srcLayout ≤ blockSize ctx.srcBaseLayout)
  (h_alloc_pair : A_o.alloc s_osea.mem 1 = (allocBase_o, allocMem_o))
  (h_own : sb_own s_osea.ap allocBase_o = (SBResult.Ok ap_own_o, allocTag_o))
  (h_ref :
    sb_ref ap_own_o (srcBase_o + ctx.srcOff) srcTag_o (kindToRefOpKind ctx.kind) =
      (SBResult.Ok ap_ref_o, borTag_o))
  (h_rstore : sb_use_mb ap_ref_o allocBase_o allocTag_o = SBResult.Ok ap_rstore_o) :
  oseair.runNWith A_o 3 s_osea prog_osea =
    oseair.Result.Ok
      (prefixPost ctx s_osea allocBase_o allocMem_o srcBase_o allocTag_o borTag_o ap_rstore_o) := by
  rcases List.get?_eq_some_iff.mp h_stmt0 with ⟨h_pc0, h_get0⟩
  rcases List.get?_eq_some_iff.mp h_stmt1 with ⟨h_pc1, h_get1⟩
  rcases List.get?_eq_some_iff.mp h_stmt2 with ⟨h_pc2, h_get2⟩
  let s1 : oseair.State :=
    { s_osea with
      reg := s_osea.reg.insert (resReg ctx)
        (TyVal.PTy, [oseair.Val.Ptr allocBase_o 0 1 allocTag_o]),
      ap := ap_own_o,
      mem := allocMem_o,
      pc := s_osea.pc + 1 }
  let s2 : oseair.State :=
    { s_osea with
      reg :=
        (s_osea.reg.insert (resReg ctx)
          (TyVal.PTy, [oseair.Val.Ptr allocBase_o 0 1 allocTag_o])).insert
          (borReg ctx)
          (TyVal.PTy, tempVals ctx srcBase_o borTag_o),
      ap := ap_ref_o,
      mem := allocMem_o,
      pc := s_osea.pc + 2 }
  have h_step0 := oseair.step_Assgn_AllocWith A_o
    s_osea prog_osea (resReg ctx) TyVal.PTy
    allocBase_o allocMem_o ap_own_o allocTag_o 1 h_pc0 h_get0 rfl h_alloc_pair h_own
  have h_src_ne_res : ctx.srcReg ≠ resReg ctx := by
    intro h_eq
    exact (alloc_fresh_reg_of_ge (cs := ctx.cs) ctx.h_regs_below (Nat.le_refl _)
      ctx.src.base ctx.srcBaseLayout)
      (by simpa [resReg, h_eq] using ctx.h_src_lookup)
  have h_res_ne_bor : resReg ctx ≠ borReg ctx := by
    change Register.R ctx.cs.nextReg ≠ Register.R (ctx.cs.nextReg + 1)
    intro h_eq
    injection h_eq with h_num
    omega
  have h_res_reg : s1.reg.lookup (resReg ctx) =
      some (TyVal.PTy, [oseair.Val.Ptr allocBase_o 0 1 allocTag_o]) := by
    simp [s1]
  have h_src_reg1 : s1.reg.lookup ctx.srcReg =
      some (TyVal.PTy, [oseair.Val.Ptr srcBase_o 0 (blockSize ctx.srcBaseLayout) srcTag_o]) := by
    simpa [s1, h_src_ne_res] using h_src_reg
  have h_src_off_lt : ctx.srcOff < blockSize ctx.srcBaseLayout := by
    exact Nat.lt_of_lt_of_le
      (Nat.lt_add_of_pos_right h_src_nonempty)
      h_src_fit
  have h_src_bound : srcBase_o + 0 + ctx.srcOff < srcBase_o + blockSize ctx.srcBaseLayout := by
    simpa [Nat.zero_add] using Nat.add_lt_add_left h_src_off_lt srcBase_o
  have h_step1 := step_Assgn_BorKind (A_o := A_o)
    s1 prog_osea (borReg ctx) ctx.srcReg ctx.kind ctx.srcOff
    srcBase_o 0 (blockSize ctx.srcBaseLayout) srcTag_o
    ap_ref_o borTag_o
    h_pc1 h_get1 h_src_reg1 h_src_bound h_ref
  have h_step1' : oseair.stepWith A_o s1 prog_osea = oseair.Result.Ok s2 := by
    simpa [s1, s2, tempVals, Nat.zero_add] using h_step1
  have h_ptr_reg : s2.reg.lookup (resReg ctx) =
      some (TyVal.PTy, [oseair.Val.Ptr allocBase_o 0 1 allocTag_o]) := by
    simp [s2, h_res_ne_bor]
  have h_bor_reg : s2.reg.lookup (borReg ctx) =
      some (TyVal.PTy, tempVals ctx srcBase_o borTag_o) := by
    simp [s2]
  have h_step2 := step_RStoreWith A_o
    s2 prog_osea TyVal.PTy (borReg ctx) (resReg ctx)
    TyVal.PTy (tempVals ctx srcBase_o borTag_o)
    allocBase_o 0 1 allocTag_o TyVal.PTy
    ap_rstore_o
    h_pc2 h_get2 h_bor_reg h_ptr_reg
    (by simp) h_rstore
  have h_step2' :
      oseair.stepWith A_o s2 prog_osea =
        oseair.Result.Ok
          (prefixPost ctx s_osea allocBase_o allocMem_o srcBase_o allocTag_o borTag_o ap_rstore_o) := by
    simpa [s2, prefixPost, tempVals, Nat.zero_add] using h_step2
  have h_run_tail :
      (match oseair.stepWith A_o s1 prog_osea with
      | oseair.Result.Ok state' =>
          match oseair.stepWith A_o state' prog_osea with
          | oseair.Result.Ok state' => oseair.Result.Ok state'
          | oseair.Result.Err msg => oseair.Result.Err msg
      | oseair.Result.Err msg => oseair.Result.Err msg) =
        oseair.Result.Ok
          (prefixPost ctx s_osea allocBase_o allocMem_o srcBase_o allocTag_o borTag_o ap_rstore_o) := by
    simp [h_step1', h_step2']
  simp [oseair.runNWith]
  rw [h_step0]
  simpa [s1] using h_run_tail

theorem simulation_structured
  {ptr_sim : PtrSimPred}
  {ρa : AddrRenameMap}
  {ρt : TagRenameMap}
  {s_mir s_mir_next : mirlite.State}
  {s_osea : oseair.State}
  {prog_mir : mirlite.Prog}
  {prog_osea : oseair.Prog}
  (h_sim : LocalSim ctx ρa ρt s_mir s_osea ptr_sim)
  (h_noninterference : TargetNonInterference ρa s_osea)
  (h_tag_fresh : ∀ tag, s_mir.ap.NextTag ≤ tag → ρt tag = none)
  (h_mir_start : StartsAt prog_mir s_mir.pc [stmt ctx])
  (h_mir_step :
    mirlite.stepWith A_m s_mir prog_mir = mirlite.Result.Ok s_mir_next)
  (h_osea_start :
    StartsAt prog_osea s_osea.pc (RefExistingCtx.compiled ctx))
  (h_src_nonempty : 0 < blockSize ctx.srcLayout) :
  ∃ srcBase_m srcBase_o srcTag_m newTag_m borTag_o ρt' ptr_sim' s_osea_next,
    s_mir.env.lookup ctx.src.base =
      some (srcBase_m, layoutToTyVal ctx.srcBaseLayout, srcTag_m) ∧
    ρa srcBase_m = some srcBase_o ∧
    newTag_m = s_mir.ap.NextTag ∧
    ρt' = extendTagRenameMap ρt newTag_m borTag_o ∧
    ptr_sim' = postPtrSim ctx ptr_sim srcBase_o newTag_m borTag_o ∧
    StepStarWith oseair.bumpAllocator s_osea prog_osea s_osea_next ∧
    StateSim ctx.cs.placeMap ρa ρt' s_mir_next s_osea_next ptr_sim' ∧
    TargetNonInterference ρa s_osea_next ∧
    s_mir_next.env = s_mir.env ∧
    s_osea_next.pc = s_osea.pc + ctx.compiled.length := by
  let ⟨srcBase_m, srcBase_o, srcTag_m, srcTag_o, h_src_ptr, _h_src_proj_block⟩ :=
    StateSim.place_projected h_sim ctx.h_src_lookup ctx.h_src_path
  let ⟨dstBase_m, dstBase_o, dstTag_m, dstTag_o, h_dst_ptr, _h_dst_block⟩ :=
    StateSim.place h_sim ctx.h_dst_lookup
  have h_src_env := place_runtime_sim.env h_src_ptr
  have h_dst_env := place_runtime_sim.env h_dst_ptr
  have h_src_reg := place_runtime_sim.reg h_src_ptr
  have h_dst_reg := place_runtime_sim.reg h_dst_ptr
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
  let allocBase_o := (oseair.bumpAllocator.alloc s_osea.mem 1).1
  let allocMem_o := (oseair.bumpAllocator.alloc s_osea.mem 1).2
  have h_alloc_pair : oseair.bumpAllocator.alloc s_osea.mem 1 = (allocBase_o, allocMem_o) := by
    simp [allocBase_o, allocMem_o]
  have h_alloc_mMap_o : allocMem_o.mMap = s_osea.mem.mMap := by
    have h_alloc_mMap := oseair.AllocatorSpec.alloc_mMap_eq (A := oseair.bumpAllocator) s_osea.mem 1
    rw [h_alloc_pair] at h_alloc_mMap
    simpa using h_alloc_mMap
  have h_alloc_base : allocBase_o = s_osea.mem.addrStart := by
    simp [allocBase_o, oseair.bumpAllocator, oseair.allocate]
  have h_alloc_addrStart' : allocMem_o.addrStart = s_osea.mem.addrStart + 1 := by
    simp [allocMem_o, oseair.bumpAllocator, oseair.allocate]
  have h_alloc_le : s_osea.mem.addrStart ≤ allocMem_o.addrStart := by
    simpa [h_alloc_addrStart'] using Nat.le_add_right s_osea.mem.addrStart 1
  have h_alloc_lt : allocBase_o < allocMem_o.addrStart := by
    simpa [h_alloc_base, h_alloc_addrStart'] using Nat.lt_succ_self s_osea.mem.addrStart
  have h_next_alloc_clear : NextAllocClear (A_o := oseair.bumpAllocator) ρa s_osea 1 := by
    exact TargetNonInterference.next_alloc_clear h_noninterference
  have h_temp_unmapped_alloc : ∀ a, ρa a ≠ some allocBase_o := by
    exact h_next_alloc_clear.1
  have h_temp_stack_clear_alloc :
      s_osea.ap.StackMap.find? allocBase_o = none ∨
      s_osea.ap.StackMap.find? allocBase_o = some [] := by
    exact h_next_alloc_clear.2
  let ⟨ap_ref_m, newTag_m, ap_write_m, h_mir_ref, h_mir_use, h_mir_next⟩ :=
    mirlite_step_inv ctx s_mir s_mir_next prog_mir
      srcBase_m srcTag_m dstBase_m dstTag_m
      h_src_env h_dst_env h_mir_start h_mir_step
  let s_mir_ref : mirlite.State := { s_mir with ap := ap_ref_m }
  have h_mir_next_ref :
      s_mir_next =
        { s_mir_ref with
          ap := ap_write_m,
          mem := mirlite.writeWordSeq s_mir.mem (dstBase_m + ctx.dstOff)
            [mirlite.MemValue.PlaceTag ctx.src newTag_m],
          pc := s_mir.pc + 1 } := by
    simpa [s_mir_ref] using h_mir_next
  have h_newTag_eq_nextTag : newTag_m = s_mir.ap.NextTag :=
    sb_ref_tag_eq_nextTag h_mir_ref
  have h_tag_fresh' : ∀ tag, newTag_m ≤ tag → ρt tag = none := by
    simpa [h_newTag_eq_nextTag] using h_tag_fresh
  have h_env_next : s_mir_next.env = s_mir.env := by
    simpa [h_mir_next_ref, s_mir_ref]
  have ⟨allocTag_o, ap_own_o, h_osea_own⟩ :=
    sb_osea_only_own_ok h_temp_stack_clear_alloc
  have h_sb_own :=
    sb_osea_only_own_preserves_sim (StateSim.sb h_sim) h_temp_unmapped_alloc h_osea_own
  let ⟨borTag_o, ap_ref_o, h_osea_ref, h_sb_ref⟩ :=
    sb_ref_sim_ok h_sb_own h_src_addr h_src_tag h_mir_ref
  let ρt' := extendTagRenameMap ρt newTag_m borTag_o
  have h_temp_ne_src : allocBase_o ≠ srcBase_o + ctx.srcOff := by
    intro h_eq
    exact h_temp_unmapped_alloc (srcBase_m + ctx.srcOff) (h_eq ▸ h_src_addr)
  have h_own_find :
      ap_own_o.StackMap.find? allocBase_o = some [RefKind.Own allocTag_o] :=
    sb_own_creates_find h_osea_own
  have h_valid_own : SBValid ap_own_o := h_sb_own.valid_osea
  have h_find_after_ref :
      ap_ref_o.StackMap.find? allocBase_o = some [RefKind.Own allocTag_o] := by
    exact (sb_ref_preserves_find_ne h_valid_own h_osea_ref h_temp_ne_src).trans h_own_find
  have ⟨ap_rstore_o, h_osea_rstore⟩ := sb_use_mb_of_find_own h_find_after_ref
  have h_sb_rstore :=
    sb_osea_only_use_mb_preserves_sim h_sb_ref h_temp_unmapped_alloc h_osea_rstore
  have h_find_temp_pre :
      ap_rstore_o.StackMap.find? allocBase_o = some [RefKind.Own allocTag_o] :=
    sb_use_mb_preserves_find_own h_find_after_ref h_osea_rstore
  have h_dst_tag' : ρt' dstTag_m = some dstTag_o := by
    have h_dst_tag_ne : dstTag_m ≠ newTag_m :=
      alloc_fresh_tag (freshTag := newTag_m) h_sim h_tag_fresh' ctx.h_dst_lookup h_dst_ptr
    simp [ρt', h_dst_tag_ne, h_dst_tag]
  let ptr_sim' := postPtrSim ctx ptr_sim srcBase_o newTag_m borTag_o
  let vals_temp := tempVals ctx srcBase_o borTag_o
  have h_temp_disj :
      ∀ base reg layout,
        ctx.cs.placeMap.lookup base = some (reg, layout) →
        ∀ addr_m addr_o tag_m tag_o,
          place_runtime_sim ctx.cs.placeMap ρa ρt s_mir s_osea
            base reg addr_m addr_o tag_m tag_o layout →
          blocks_disjoint addr_o (blockSize layout) allocBase_o vals_temp.length := by
    intro base reg layout h_lookup addr_m addr_o tag_m tag_o h_ptr
    simpa [vals_temp, tempVals] using
      (alloc_fresh_target_disjoint
        (freshAddr_o := allocBase_o)
        (freshLayout := dstLayout ctx)
        h_sim h_noninterference h_alloc_base h_lookup h_ptr)
  have h_sim_state :
      StateSim ctx.cs.placeMap ρa ρt s_mir s_osea ptr_sim := by
    simpa [LocalSim] using h_sim
  have h_sim_temp_write :
      StateSim ctx.cs.placeMap ρa ρt s_mir
        { s_osea with mem := oseair.writeWordSeq s_osea.mem allocBase_o vals_temp }
        ptr_sim := by
    exact state_sim_osea_write_other h_sim_state h_temp_disj
  have h_sim_temp_mem :
      StateSim ctx.cs.placeMap ρa ρt s_mir
        { s_osea with mem := oseair.writeWordSeq allocMem_o allocBase_o vals_temp }
        ptr_sim := by
    refine StateSim.of_mem_mMap_eq
      (o₂ := { s_osea with mem := oseair.writeWordSeq allocMem_o allocBase_o vals_temp })
      h_sim_temp_write rfl rfl rfl rfl ?_ rfl
    simpa using
      (oseair_writeWordSeq_mMap_eq_of_mMap_eq h_alloc_mMap_o allocBase_o vals_temp).symm
  have h_res_fresh :
      ∀ base layout,
        ctx.cs.placeMap.lookup base = some (resReg ctx, layout) → False := by
    simpa [resReg] using
      (alloc_fresh_reg_of_ge (cs := ctx.cs) ctx.h_regs_below (Nat.le_refl _))
  have h_bor_fresh :
      ∀ base layout,
        ctx.cs.placeMap.lookup base = some (borReg ctx, layout) → False := by
    simpa [borReg] using
      (alloc_fresh_reg_of_ge (cs := ctx.cs) ctx.h_regs_below (Nat.le_add_right _ 1))
  have h_sim_temp_res :
      StateSim ctx.cs.placeMap ρa ρt s_mir
        { s_osea with
          reg := s_osea.reg.insert (resReg ctx)
            (TyVal.PTy, [oseair.Val.Ptr allocBase_o 0 1 allocTag_o]),
          mem := oseair.writeWordSeq allocMem_o allocBase_o vals_temp }
        ptr_sim := by
    simpa using state_sim_reg_insert_other h_sim_temp_mem h_res_fresh
  have h_sim_temp_regs :
      StateSim ctx.cs.placeMap ρa ρt s_mir
        { s_osea with
          reg :=
            (s_osea.reg.insert (resReg ctx)
              (TyVal.PTy, [oseair.Val.Ptr allocBase_o 0 1 allocTag_o])).insert
              (borReg ctx)
              (TyVal.PTy, vals_temp),
          mem := oseair.writeWordSeq allocMem_o allocBase_o vals_temp }
        ptr_sim := by
    simpa using state_sim_reg_insert_other h_sim_temp_res h_bor_fresh
  have h_sim_pre_default :
      StateSim ctx.cs.placeMap ρa ρt' s_mir_ref
        { s_osea with
          reg :=
            (s_osea.reg.insert (resReg ctx)
              (TyVal.PTy, [oseair.Val.Ptr allocBase_o 0 1 allocTag_o])).insert
              (borReg ctx)
              (TyVal.PTy, vals_temp),
          ap := ap_rstore_o,
          mem := oseair.writeWordSeq allocMem_o allocBase_o vals_temp }
        ptr_sim := by
    exact state_sim_extend_ρt_sb
      (newTag_m := newTag_m) (newTag_o := borTag_o)
      h_sim_temp_regs h_tag_fresh' h_sb_rstore
      (by simp [s_mir_ref])
      (by simp [s_mir_ref])
      rfl rfl
  have h_sim_pre :
      StateSim ctx.cs.placeMap ρa ρt' s_mir_ref
        (prefixPost ctx s_osea allocBase_o allocMem_o srcBase_o allocTag_o borTag_o ap_rstore_o)
        ptr_sim' := by
    have h_sim_pre' :
        StateSim ctx.cs.placeMap ρa ρt' s_mir_ref
          (prefixPost ctx s_osea allocBase_o allocMem_o srcBase_o allocTag_o borTag_o ap_rstore_o)
          ptr_sim := by
      simpa [prefixPost, vals_temp] using h_sim_pre_default
    exact StateSim.ptr_sim_mono
      (h_mono := by
        intro p tag_m base off size tag_o h_ptr
        exact Or.inl h_ptr)
      h_sim_pre'
  have h_vals :
      mem_vals_eq ptr_sim'
        [mirlite.MemValue.PlaceTag ctx.src newTag_m]
        (oseair.readWordSeq
          (prefixPost ctx s_osea allocBase_o allocMem_o srcBase_o allocTag_o borTag_o ap_rstore_o).mem
          allocBase_o
          (blockSize (dstLayout ctx))) := by
    have h_temp_read_exact :
        oseair.readWordSeq
          (prefixPost ctx s_osea allocBase_o allocMem_o srcBase_o allocTag_o borTag_o ap_rstore_o).mem
          allocBase_o
          (blockSize (dstLayout ctx)) =
        tempVals ctx srcBase_o borTag_o := by
      simpa [prefixPost, tempVals, dstLayout, RefExistingCtx.dstLayout, blockSize, layoutSize] using
        (oseair_readWordSeq_write_exact allocMem_o allocBase_o (tempVals ctx srcBase_o borTag_o))
    rw [h_temp_read_exact]
    apply mem_vals_eq.cons
    · right
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    · exact mem_vals_eq.nil
  have h_res_ne_bor : resReg ctx ≠ borReg ctx := by
    change Register.R ctx.cs.nextReg ≠ Register.R (ctx.cs.nextReg + 1)
    intro h_eq
    injection h_eq with h_num
    omega
  have h_src_reg_pre :
      (prefixPost ctx s_osea allocBase_o allocMem_o srcBase_o allocTag_o borTag_o ap_rstore_o).reg.lookup (resReg ctx) =
        some (TyVal.PTy, [oseair.Val.Ptr allocBase_o 0 1 allocTag_o]) := by
    simp [prefixPost, h_res_ne_bor]
  have h_src_fit_pre : 0 + blockSize (dstLayout ctx) ≤ 1 := by
    simp [dstLayout, RefExistingCtx.dstLayout, blockSize, layoutSize]
  have h_res_ne_dstTmp : resReg ctx ≠ dstTmpReg ctx := by
    change Register.R ctx.cs.nextReg ≠ Register.R (ctx.cs.nextReg + 2)
    intro h_eq
    injection h_eq with h_num
    omega
  have h_dst_ne_res : ctx.dstReg ≠ resReg ctx := by
    intro h_eq
    exact (alloc_fresh_reg_of_ge (cs := ctx.cs) ctx.h_regs_below (Nat.le_refl _)
      ctx.dst.base ctx.dstBaseLayout)
      (by simpa [resReg, h_eq] using ctx.h_dst_lookup)
  have h_dst_ne_bor : ctx.dstReg ≠ borReg ctx := by
    intro h_eq
    exact (alloc_fresh_reg_of_ge (cs := ctx.cs) ctx.h_regs_below (Nat.le_add_right _ 1)
      ctx.dst.base ctx.dstBaseLayout)
      (by simpa [borReg, h_eq] using ctx.h_dst_lookup)
  have h_dst_reg_pre :
      (prefixPost ctx s_osea allocBase_o allocMem_o srcBase_o allocTag_o borTag_o ap_rstore_o).reg.lookup ctx.dstReg =
        some (TyVal.PTy, [oseair.Val.Ptr dstBase_o 0 (blockSize ctx.dstBaseLayout) dstTag_o]) := by
    simpa [prefixPost, h_dst_ne_res, h_dst_ne_bor] using h_dst_reg
  have h_fit_dst : ctx.dstOff + blockSize (dstLayout ctx) ≤ blockSize ctx.dstBaseLayout :=
    layoutResolvePath_blockSize_le ctx.h_dst_path
  have h_dst_nonempty : 0 < blockSize (dstLayout ctx) := by
    simp [dstLayout, RefExistingCtx.dstLayout, blockSize, layoutSize]
  have h_dst_pre :
      place_runtime_sim ctx.cs.placeMap ρa ρt'
        s_mir_ref
        (prefixPost ctx s_osea allocBase_o allocMem_o srcBase_o allocTag_o borTag_o ap_rstore_o)
        ctx.dst.base ctx.dstReg dstBase_m dstBase_o dstTag_m dstTag_o ctx.dstBaseLayout := by
    refine ⟨ctx.h_dst_lookup, ?_, h_dst_reg_pre, h_dst_addr_base, h_dst_tag'⟩
    simpa [s_mir_ref] using h_dst_env
  let s_osea_alloc : oseair.State := { s_osea with mem := allocMem_o, ap := ap_own_o }
  let s_osea_ref : oseair.State := { s_osea with mem := allocMem_o, ap := ap_ref_o }
  let s_osea_use : oseair.State := { s_osea with mem := allocMem_o, ap := ap_rstore_o }
  have h_src_lt_pre : srcBase_o + ctx.srcOff < s_osea_alloc.mem.addrStart := by
    exact Nat.lt_of_lt_of_le h_src_lt_old (by
      show s_osea.mem.addrStart ≤ s_osea_alloc.mem.addrStart
      simp [s_osea_alloc, h_alloc_addrStart'])
  have h_dst_lt_pre : dstBase_o + ctx.dstOff < s_osea_use.mem.addrStart := by
    exact Nat.lt_of_lt_of_le h_dst_lt_old (by
      show s_osea.mem.addrStart ≤ s_osea_use.mem.addrStart
      simp [s_osea_use, h_alloc_addrStart'])
  have h_nonempty_alloc : TargetNonemptyStacksBelowAddrStart s_osea_alloc := by
    exact TargetNonemptyStacksBelowAddrStart.sb_own
      h_noninterference.2 (StateSim.sb h_sim).valid_osea
      (by
        show s_osea.mem.addrStart ≤ s_osea_alloc.mem.addrStart
        simp [s_osea_alloc, h_alloc_addrStart'])
      (by
        show allocBase_o < s_osea_alloc.mem.addrStart
        simp [s_osea_alloc, h_alloc_base, h_alloc_addrStart'])
      h_osea_own
  have h_nonempty_ref : TargetNonemptyStacksBelowAddrStart s_osea_ref := by
    exact TargetNonemptyStacksBelowAddrStart.sb_ref
      (s_osea := s_osea_alloc)
      h_nonempty_alloc
      (sb_own_preserves_valid (StateSim.sb h_sim).valid_osea h_osea_own)
      (by simpa [s_osea_alloc] using h_src_lt_pre)
      (by simpa [s_osea_alloc, s_osea_ref] using h_osea_ref)
  have h_nonempty_use_core : TargetNonemptyStacksBelowAddrStart s_osea_use := by
    exact TargetNonemptyStacksBelowAddrStart.sb_use_mb
      (s_osea := s_osea_ref)
      h_nonempty_ref
      (sb_ref_preserves_valid
        (sb_own_preserves_valid (StateSim.sb h_sim).valid_osea h_osea_own)
        h_osea_ref)
      (by
        show allocBase_o < s_osea_ref.mem.addrStart
        simp [s_osea_ref, h_alloc_base, h_alloc_addrStart'])
      (by simpa [s_osea_ref, s_osea_use] using h_osea_rstore)
  have h_nonempty_pre :
      TargetNonemptyStacksBelowAddrStart
        (prefixPost ctx s_osea allocBase_o allocMem_o srcBase_o allocTag_o borTag_o ap_rstore_o) := by
    exact TargetNonemptyStacksBelowAddrStart.of_stackMap_eq
      (s_osea := s_osea_use)
      (s_osea_next := prefixPost ctx s_osea allocBase_o allocMem_o srcBase_o allocTag_o borTag_o ap_rstore_o)
      h_nonempty_use_core rfl (by simp [s_osea_use, prefixPost, oseair_writeWordSeq_addrStart_eq])
  have h_noninterference_pre :
      TargetNonInterference ρa
        (prefixPost ctx s_osea allocBase_o allocMem_o srcBase_o allocTag_o borTag_o ap_rstore_o) := by
    refine ⟨?_, h_nonempty_pre⟩
    exact TargetAddrRenameBelowAddrStart.mono h_noninterference.1
      (by simpa [prefixPost, oseair_writeWordSeq_addrStart_eq] using h_alloc_le)
  by_cases h_off : ctx.dstOff = 0
  · have h_start_full :
        StartsAt prog_osea s_osea.pc
          [oseair.Instr.Assgn (resReg ctx) (oseair.Rhs.Alloc TyVal.PTy),
           oseair.Instr.Assgn (borReg ctx) (kindToOseaRhs ctx.kind ctx.srcReg ctx.srcOff),
           oseair.Instr.RStore TyVal.PTy (borReg ctx) (resReg ctx),
           oseair.Instr.Memcpy ctx.dstReg (resReg ctx) TyVal.PTy] := by
      simpa [RefExistingCtx.compiled_eq, h_off] using h_osea_start
    have h_start1 := StartsAt.tail h_start_full
    have h_start2 := StartsAt.tail h_start1
    have h_start3 := StartsAt.tail h_start2
    have h_stmt0 :
        prog_osea.get? s_osea.pc =
          some (oseair.Instr.Assgn (resReg ctx) (oseair.Rhs.Alloc TyVal.PTy)) := by
      have h_head := h_start_full 0 (by simp)
      simpa [Nat.zero_add, List.get?] using h_head.symm
    have h_stmt1 :
        prog_osea.get? (s_osea.pc + 1) =
          some (oseair.Instr.Assgn (borReg ctx) (kindToOseaRhs ctx.kind ctx.srcReg ctx.srcOff)) := by
      have h_head := h_start1 0 (by simp)
      simpa [Nat.zero_add, List.get?] using h_head.symm
    have h_stmt2 :
        prog_osea.get? (s_osea.pc + 2) =
          some (oseair.Instr.RStore TyVal.PTy (borReg ctx) (resReg ctx)) := by
      have h_head := h_start2 0 (by simp)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, List.get?] using h_head.symm
    have h_prefix_run :
        oseair.runNWith oseair.bumpAllocator 3 s_osea prog_osea =
          oseair.Result.Ok
            (prefixPost ctx s_osea allocBase_o allocMem_o srcBase_o allocTag_o borTag_o ap_rstore_o) := by
      simpa using
        osea_prefix_run_ok ctx s_osea prog_osea
          (A_o := oseair.bumpAllocator)
          srcBase_o srcTag_o allocBase_o allocMem_o allocTag_o ap_own_o borTag_o ap_ref_o ap_rstore_o
          h_stmt0 h_stmt1 h_stmt2 h_src_reg h_src_nonempty
          (layoutResolvePath_blockSize_le ctx.h_src_path)
          h_alloc_pair
          h_osea_own
          h_osea_ref
          h_osea_rstore
    have h_target_direct :
        ctx.dstOff = 0 →
          ∃ ap_read_o ap_write_o,
            sb_read
                (prefixPost ctx s_osea allocBase_o allocMem_o srcBase_o allocTag_o borTag_o ap_rstore_o).ap
                (allocBase_o + 0) allocTag_o = SBResult.Ok ap_read_o ∧
            sb_use_mb ap_read_o (dstBase_o + ctx.dstOff) dstTag_o = SBResult.Ok ap_write_o ∧
            sb_sim ρa ρt' ap_write_m ap_write_o := by
      intro _h
      obtain ⟨ap_read_o, h_temp_read⟩ := sb_read_ok_of_find_own h_find_temp_pre
      have h_sb_read :=
        sb_osea_only_read_preserves_sim h_sb_rstore h_temp_unmapped_alloc h_temp_read
      let ⟨ap_write_o, h_write_o, h_sb_write⟩ :=
        sb_use_mb_sim_ok (ρt := ρt') h_sb_read h_dst_addr h_dst_tag' h_mir_use
      exact ⟨ap_read_o, ap_write_o, by simpa [prefixPost] using h_temp_read,
        by simpa [h_off] using h_write_o, h_sb_write⟩
    have h_target_projected :
        ctx.dstOff ≠ 0 →
          ∃ tempTag ap_ref_dst_o ap_read_o ap_write_o ap_final_o,
            sb_ref
                (prefixPost ctx s_osea allocBase_o allocMem_o srcBase_o allocTag_o borTag_o ap_rstore_o).ap
                (dstBase_o + ctx.dstOff) dstTag_o RefOpKind.Mut =
              (SBResult.Ok ap_ref_dst_o, tempTag) ∧
            sb_read ap_ref_dst_o (allocBase_o + 0) allocTag_o = SBResult.Ok ap_read_o ∧
            sb_use_mb ap_read_o (dstBase_o + ctx.dstOff) tempTag = SBResult.Ok ap_write_o ∧
            sb_die ap_write_o (dstBase_o + ctx.dstOff) tempTag = SBResult.Ok ap_final_o ∧
            sb_sim ρa ρt' ap_write_m ap_final_o := by
      intro h_false
      exact False.elim (h_false h_off)
    let s_osea_pre := prefixPost ctx s_osea allocBase_o allocMem_o srcBase_o allocTag_o borTag_o ap_rstore_o
    have h_memcpy :
        ∃ s_osea_next,
          StepStarWith oseair.bumpAllocator s_osea_pre prog_osea s_osea_next ∧
          StateSim ctx.cs.placeMap ρa ρt' s_mir_next s_osea_next ptr_sim' ∧
          TargetNonInterference ρa s_osea_next ∧
          s_osea_next.pc = s_osea_pre.pc + (if ctx.dstOff = 0 then 1 else 3) := by
      simpa using
        (existing_memcpy_simulation
          (A_o := oseair.bumpAllocator)
          (ρa := ρa) (ρt := ρt')
          (s_mir := s_mir_ref)
          (s_osea := s_osea_pre)
          (s_mir_next := s_mir_next)
          (prog_osea := prog_osea)
          (srcReg := resReg ctx)
          (dst_reg := ctx.dstReg)
          (tmpReg := dstTmpReg ctx)
          (baseLayout := ctx.dstBaseLayout)
          (subLayout := dstLayout ctx)
          (srcBase := allocBase_o)
          (srcOff := 0)
          (srcSize := 1)
          (srcTag := allocTag_o)
          (dst_base := ctx.dst.base)
          (dst_mir := dstBase_m)
          (dst_osea := dstBase_o)
          (dst_tag_m := dstTag_m)
          (dst_tag_o := dstTag_o)
          (off := ctx.dstOff)
          (vals_mir := [mirlite.MemValue.PlaceTag ctx.src newTag_m])
          (ap_m' := ap_write_m)
          (ptr_sim := ptr_sim')
          h_sim_pre h_noninterference_pre h_dst_pre h_fit_dst h_dst_nonempty
          (fun base layout h_lookup => by
            exact (alloc_fresh_reg_of_ge (cs := ctx.cs) ctx.h_regs_below (Nat.le_add_right _ 2)
              base layout)
              (by simpa [dstTmpReg] using h_lookup))
          (fun _ => by simpa [prefixPost] using h_start3)
          (fun h_false => False.elim (h_false h_off))
          h_src_reg_pre
          (by simpa [s_osea_pre, prefixPost, Nat.zero_add, oseair_writeWordSeq_addrStart_eq] using h_alloc_lt)
          (by simpa [s_osea_pre, prefixPost, oseair_writeWordSeq_addrStart_eq] using h_dst_lt_pre)
          h_res_ne_dstTmp h_src_fit_pre
          h_target_direct h_target_projected
          h_mir_next_ref h_vals)
    rcases h_memcpy with ⟨s_osea_next, h_steps, h_sim_next, h_noninterference_next, h_pc_next⟩
    have h_pc_next' : s_osea_next.pc = s_osea.pc + ctx.compiled.length := by
      calc
        s_osea_next.pc = s_osea_pre.pc + (if ctx.dstOff = 0 then 1 else 3) := h_pc_next
        _ = s_osea.pc + ctx.compiled.length := by
          simp [s_osea_pre, prefixPost, RefExistingCtx.compiled_eq, h_off]
    exact ⟨srcBase_m, srcBase_o, srcTag_m, newTag_m, borTag_o, ρt', ptr_sim', s_osea_next,
      h_src_env, h_src_addr_base, h_newTag_eq_nextTag, rfl, rfl,
      StepStarWith.trans (StepStarWith.of_runN_ok h_prefix_run) h_steps,
      h_sim_next, h_noninterference_next, h_env_next, h_pc_next'⟩
  · have h_start_full :
        StartsAt prog_osea s_osea.pc
          [oseair.Instr.Assgn (resReg ctx) (oseair.Rhs.Alloc TyVal.PTy),
           oseair.Instr.Assgn (borReg ctx) (kindToOseaRhs ctx.kind ctx.srcReg ctx.srcOff),
           oseair.Instr.RStore TyVal.PTy (borReg ctx) (resReg ctx),
           oseair.Instr.Assgn (dstTmpReg ctx) (oseair.Rhs.MutBorOffset ctx.dstReg ctx.dstOff),
           oseair.Instr.Memcpy (dstTmpReg ctx) (resReg ctx) TyVal.PTy,
           oseair.Instr.Die (dstTmpReg ctx)] := by
      simpa [RefExistingCtx.compiled_eq, h_off] using h_osea_start
    have h_start1 := StartsAt.tail h_start_full
    have h_start2 := StartsAt.tail h_start1
    have h_start3 := StartsAt.tail h_start2
    have h_stmt0 :
        prog_osea.get? s_osea.pc =
          some (oseair.Instr.Assgn (resReg ctx) (oseair.Rhs.Alloc TyVal.PTy)) := by
      have h_head := h_start_full 0 (by simp)
      simpa [Nat.zero_add, List.get?] using h_head.symm
    have h_stmt1 :
        prog_osea.get? (s_osea.pc + 1) =
          some (oseair.Instr.Assgn (borReg ctx) (kindToOseaRhs ctx.kind ctx.srcReg ctx.srcOff)) := by
      have h_head := h_start1 0 (by simp)
      simpa [Nat.zero_add, List.get?] using h_head.symm
    have h_stmt2 :
        prog_osea.get? (s_osea.pc + 2) =
          some (oseair.Instr.RStore TyVal.PTy (borReg ctx) (resReg ctx)) := by
      have h_head := h_start2 0 (by simp)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, List.get?] using h_head.symm
    have h_prefix_run :
        oseair.runNWith oseair.bumpAllocator 3 s_osea prog_osea =
          oseair.Result.Ok
            (prefixPost ctx s_osea allocBase_o allocMem_o srcBase_o allocTag_o borTag_o ap_rstore_o) := by
      simpa using
        osea_prefix_run_ok ctx s_osea prog_osea
          (A_o := oseair.bumpAllocator)
          srcBase_o srcTag_o allocBase_o allocMem_o allocTag_o ap_own_o borTag_o ap_ref_o ap_rstore_o
          h_stmt0 h_stmt1 h_stmt2 h_src_reg h_src_nonempty
          (layoutResolvePath_blockSize_le ctx.h_src_path)
          h_alloc_pair
          h_osea_own
          h_osea_ref
          h_osea_rstore
    have h_target_direct :
        ctx.dstOff = 0 →
          ∃ ap_read_o ap_write_o,
            sb_read
                (prefixPost ctx s_osea allocBase_o allocMem_o srcBase_o allocTag_o borTag_o ap_rstore_o).ap
                (allocBase_o + 0) allocTag_o = SBResult.Ok ap_read_o ∧
            sb_use_mb ap_read_o (dstBase_o + ctx.dstOff) dstTag_o = SBResult.Ok ap_write_o ∧
            sb_sim ρa ρt' ap_write_m ap_write_o := by
      intro h_zero
      exact False.elim (h_off h_zero)
    have h_target_projected :
        ctx.dstOff ≠ 0 →
          ∃ tempTag ap_ref_dst_o ap_read_o ap_write_o ap_final_o,
            sb_ref
                (prefixPost ctx s_osea allocBase_o allocMem_o srcBase_o allocTag_o borTag_o ap_rstore_o).ap
                (dstBase_o + ctx.dstOff) dstTag_o RefOpKind.Mut =
              (SBResult.Ok ap_ref_dst_o, tempTag) ∧
            sb_read ap_ref_dst_o (allocBase_o + 0) allocTag_o = SBResult.Ok ap_read_o ∧
            sb_use_mb ap_read_o (dstBase_o + ctx.dstOff) tempTag = SBResult.Ok ap_write_o ∧
            sb_die ap_write_o (dstBase_o + ctx.dstOff) tempTag = SBResult.Ok ap_final_o ∧
            sb_sim ρa ρt' ap_write_m ap_final_o := by
      intro _h
      simpa [prefixPost, Nat.zero_add] using
        (sb_ref_mut_read_unmapped_use_die_sim_ok
          (h_sim := h_sb_rstore)
          (h_dst_addr := h_dst_addr)
          (h_dst_tag := h_dst_tag')
          (h_use_m := h_mir_use)
          (h_src_find := h_find_temp_pre)
          (h_src_unmapped := h_temp_unmapped_alloc))
    let s_osea_pre := prefixPost ctx s_osea allocBase_o allocMem_o srcBase_o allocTag_o borTag_o ap_rstore_o
    have h_memcpy :
        ∃ s_osea_next,
          StepStarWith oseair.bumpAllocator s_osea_pre prog_osea s_osea_next ∧
          StateSim ctx.cs.placeMap ρa ρt' s_mir_next s_osea_next ptr_sim' ∧
          TargetNonInterference ρa s_osea_next ∧
          s_osea_next.pc = s_osea_pre.pc + (if ctx.dstOff = 0 then 1 else 3) := by
      simpa using
        (existing_memcpy_simulation
          (A_o := oseair.bumpAllocator)
          (ρa := ρa) (ρt := ρt')
          (s_mir := s_mir_ref)
          (s_osea := s_osea_pre)
          (s_mir_next := s_mir_next)
          (prog_osea := prog_osea)
          (srcReg := resReg ctx)
          (dst_reg := ctx.dstReg)
          (tmpReg := dstTmpReg ctx)
          (baseLayout := ctx.dstBaseLayout)
          (subLayout := dstLayout ctx)
          (srcBase := allocBase_o)
          (srcOff := 0)
          (srcSize := 1)
          (srcTag := allocTag_o)
          (dst_base := ctx.dst.base)
          (dst_mir := dstBase_m)
          (dst_osea := dstBase_o)
          (dst_tag_m := dstTag_m)
          (dst_tag_o := dstTag_o)
          (off := ctx.dstOff)
          (vals_mir := [mirlite.MemValue.PlaceTag ctx.src newTag_m])
          (ap_m' := ap_write_m)
          (ptr_sim := ptr_sim')
          h_sim_pre h_noninterference_pre h_dst_pre h_fit_dst h_dst_nonempty
          (fun base layout h_lookup => by
            exact (alloc_fresh_reg_of_ge (cs := ctx.cs) ctx.h_regs_below (Nat.le_add_right _ 2)
              base layout)
              (by simpa [dstTmpReg] using h_lookup))
          (fun h_zero => False.elim (h_off h_zero))
          (fun _ => by simpa [prefixPost] using h_start3)
          h_src_reg_pre
          (by simpa [s_osea_pre, prefixPost, Nat.zero_add, oseair_writeWordSeq_addrStart_eq] using h_alloc_lt)
          (by simpa [s_osea_pre, prefixPost, oseair_writeWordSeq_addrStart_eq] using h_dst_lt_pre)
          h_res_ne_dstTmp h_src_fit_pre
          h_target_direct h_target_projected
          h_mir_next_ref h_vals)
    rcases h_memcpy with ⟨s_osea_next, h_steps, h_sim_next, h_noninterference_next, h_pc_next⟩
    have h_pc_next' : s_osea_next.pc = s_osea.pc + ctx.compiled.length := by
      calc
        s_osea_next.pc = s_osea_pre.pc + (if ctx.dstOff = 0 then 1 else 3) := h_pc_next
        _ = s_osea.pc + ctx.compiled.length := by
          simp [s_osea_pre, prefixPost, RefExistingCtx.compiled_eq, h_off]
    exact ⟨srcBase_m, srcBase_o, srcTag_m, newTag_m, borTag_o, ρt', ptr_sim', s_osea_next,
      h_src_env, h_src_addr_base, h_newTag_eq_nextTag, rfl, rfl,
      StepStarWith.trans (StepStarWith.of_runN_ok h_prefix_run) h_steps,
      h_sim_next, h_noninterference_next, h_env_next, h_pc_next'⟩

theorem simulation
  {ptr_sim : PtrSimPred}
  {ρa : AddrRenameMap}
  {ρt : TagRenameMap}
  {s_mir s_mir_next : mirlite.State}
  {s_osea : oseair.State}
  {prog_mir : mirlite.Prog}
  {prog_osea : oseair.Prog}
  (h_sim : LocalSim ctx ρa ρt s_mir s_osea ptr_sim)
  (h_noninterference : TargetNonInterference ρa s_osea)
  (h_tag_fresh : ∀ tag, s_mir.ap.NextTag ≤ tag → ρt tag = none)
  (h_mir_start : StartsAt prog_mir s_mir.pc [stmt ctx])
  (h_mir_step :
    mirlite.stepWith A_m s_mir prog_mir = mirlite.Result.Ok s_mir_next)
  (h_osea_start :
    StartsAt prog_osea s_osea.pc (RefExistingCtx.compiled ctx))
  (h_src_nonempty : 0 < blockSize ctx.srcLayout) :
  ∃ ρt' ptr_sim' s_osea_next,
    StepStarWith oseair.bumpAllocator s_osea prog_osea s_osea_next ∧
    StateSim ctx.cs.placeMap ρa ρt' s_mir_next s_osea_next ptr_sim' ∧
    TargetNonInterference ρa s_osea_next ∧
    s_osea_next.pc = s_osea.pc + ctx.compiled.length := by
  obtain ⟨_srcBase_m, _srcBase_o, _srcTag_m, _newTag_m, _borTag_o, ρt', ptr_sim', s_osea_next,
      _h_src_env, _h_src_addr, _h_newTag, _h_ρt', _h_ptr_sim',
      h_steps, h_sim_next, h_noninterference_next, _h_env_next, h_pc_next⟩ :=
    simulation_structured
      (ctx := ctx)
      (h_sim := h_sim)
      (h_noninterference := h_noninterference)
      (h_tag_fresh := h_tag_fresh)
      (h_mir_start := h_mir_start)
      (h_mir_step := h_mir_step)
      (h_osea_start := h_osea_start)
      (h_src_nonempty := h_src_nonempty)
  exact ⟨ρt', ptr_sim', s_osea_next, h_steps, h_sim_next, h_noninterference_next, h_pc_next⟩

end RefExisting

end obseq.proof
