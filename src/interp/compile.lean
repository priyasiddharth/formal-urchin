
import interp.units
import interp.mirlight
import interp.oseairlight
import interp.units
import interp.accessperm
import Lean.Data.AssocList

-- Add Repr instance for TyVal
instance : Repr TyVal where
  reprPrec ty _ := toString ty

-- Add Repr instance for oseair.Register so `repr reg` is available
instance : Repr oseair.Register where
  reprPrec r _ :=
    match r with
    | oseair.Register.P n => s!"P{n}"
    | oseair.Register.R n => s!"R{n}"
    | oseair.Register.M n => s!"M{n}"

namespace compiler


structure CompileCtx where
  -- placemap records allocations,
  -- fields, offsets are temporaries and are not recorded.
  placemap : Lean.AssocList BasePlace (TyVal × oseair.Register)
  -- layoutmap records the layout of each place
  -- including the complete nested structure of a datatype with nested references
  layoutmap : Lean.AssocList BasePlace LayoutTyVal
  prog : oseair.Prog
  regSuffix : Nat
  currBB: Nat

instance : Repr (Lean.AssocList BasePlace (TyVal × oseair.Register)) where
  reprPrec placemap _ :=
    let entries := placemap.toList.map (fun (k, (ty, reg)) =>
      s!"{repr k} ↦ ({repr ty}, {repr reg})")
    s!"Placemap({String.intercalate ", " entries})"

instance : ToString (Lean.AssocList BasePlace (TyVal × oseair.Register)) where
  toString placemap := Std.Format.pretty (repr placemap)

instance : Repr (Lean.AssocList BasePlace LayoutTyVal) where
  reprPrec layoutmap _ :=
    let entries := layoutmap.toList.map (fun (k, v) =>
      s!"{repr k} ↦ {repr v}")
    s!"Layoutmap({String.intercalate ", " entries})"

instance : ToString (Lean.AssocList BasePlace LayoutTyVal) where
  toString layoutmap := Std.Format.pretty (repr layoutmap)

def freshRegSuffix (ctx : CompileCtx) : Nat × CompileCtx :=
  let newSuffix := ctx.regSuffix + 1
  (ctx.regSuffix, { ctx with regSuffix := newSuffix })

-- Result type for statements
inductive CompileResult
| Ok (cctx: CompileCtx)
| Err (message : String)

-- Result type for PlaceToReg
inductive PlaceToRegResult
| Ok (v: oseair.Register) (cctx: CompileCtx)
| Err (message : String)
| NotExist (base: BasePlace) (message : String)

-- Result type for RHSExpr
inductive CompileExprResult
| Ok (stmts: List oseair.Stmt) (cctx: CompileCtx)
| Err (message : String)

def insertStmtsInCurrBB (stmts: List oseair.Stmt) (cctx: CompileCtx) : CompileResult :=
  match cctx.prog.find? cctx.currBB with
  | none => CompileResult.Err s!"Basic block {cctx.currBB} not found in compile context."
  | some stmtList =>
    let newProg := (cctx.prog.erase cctx.currBB).insert cctx.currBB (stmtList ++ stmts)
    let newCctx := { cctx with prog := newProg }
    CompileResult.Ok newCctx

-- def genCopyOpPtr, genLhsPtr
def ProjectPlaceToRegWTy (v: oseair.Register) (offsetKind: mir.RefOp) (force_proj: Bool) (place: Place) (ty: TyVal) (cctx: CompileCtx) : PlaceToRegResult :=
  match place with
  | [] => PlaceToRegResult.Err s!"Empty place"
  | _ => let offset := mir.getPlaceOffset place ty
    match offset with
    | none => PlaceToRegResult.Err s!"Offset not found for place {place} and ty {ty}"
    | some o => if o == 0 && !force_proj then PlaceToRegResult.Ok v cctx
      else
        let (newRegSuffix, newCctx) := freshRegSuffix cctx
        let newPtr := oseair.Register.P newRegSuffix
        let stmt := match offsetKind with
          | mir.RefOp.BorrowRef => oseair.Stmt.assgn newPtr (oseair.Rhs.bor_offset v o)
          | mir.RefOp.MutRef => oseair.Stmt.assgn newPtr (oseair.Rhs.mutbor_offset v o)
          | mir.RefOp.Raw => oseair.Stmt.assgn newPtr (oseair.Rhs.copy_offset v o)
        match insertStmtsInCurrBB [stmt] newCctx with
        | CompileResult.Err msg => PlaceToRegResult.Err msg
        | CompileResult.Ok newCctx1 => PlaceToRegResult.Ok newPtr newCctx1

def ExistPlaceToReg (place: Place)  (offsetKind: mir.RefOp) (force_projection: Bool) (cctx: CompileCtx) : PlaceToRegResult :=
  match place with
  | [] => PlaceToRegResult.Err s!"Empty place"
  | base :: _ => match cctx.placemap.find? base with
    | none => PlaceToRegResult.NotExist base s!"Base place {base} not found in compile context."
    | some (ty, reg) => ProjectPlaceToRegWTy reg offsetKind force_projection place ty cctx

def getPlaceLayoutAux (rexprs: List mir.RExpr) (cctx: CompileCtx) : Except String (List LayoutTyVal) :=
  match rexprs with
  | [] => .ok []
  | rexpr::rest_rexprs =>
    match rexpr with
    | mir.RExpr.CopyOp (base::rest) =>
      match cctx.layoutmap.find? base with
      | none => .error "Base place not found in layoutmap"
      | some baseLayout =>
        match getLayoutTypeFromBase rest baseLayout with
        | some layout =>
          match getPlaceLayoutAux rest_rexprs cctx with
          | .ok layouts => .ok (layout :: layouts)
          | .error msg => .error msg
        | none => .error s!"LY01: Layout type not found for {repr rest} with baseLayout {repr baseLayout}"
    | mir.RExpr.ConstOp _ =>
      match getPlaceLayoutAux rest_rexprs cctx with
      | .ok layouts => .ok (LayoutTyVal.NatTy :: layouts)
      | .error msg => .error msg
    | mir.RExpr.BinaryOp (mir.RExpr.CopyOp lop) (mir.RExpr.CopyOp rop) =>
      match (getPlaceLayoutAux [(mir.RExpr.CopyOp lop)] cctx, getPlaceLayoutAux [(mir.RExpr.CopyOp rop)] cctx) with
      | (.ok [LayoutTyVal.NatTy], .ok [LayoutTyVal.NatTy]) =>
        match getPlaceLayoutAux rest_rexprs cctx with
        | .ok layouts => .ok (LayoutTyVal.NatTy :: layouts)
        | .error msg => .error msg
      | _ => .error "BinaryOp operands must have NatTy layout"
    | mir.RExpr.RefrOp _refOp (base::rest) =>
      match cctx.layoutmap.find? base with
      | some baseLayout =>
        dbg_trace s!"Found baseLayout {repr baseLayout} for base {repr base} fullplace: {repr (base::rest)}"
        match getLayoutTypeFromBase rest baseLayout with
        | some layout =>
          match getPlaceLayoutAux rest_rexprs cctx with
          | .ok layouts =>
            dbg_trace s!"RefrOp on {repr rest} gives layout {repr layout}"
            .ok (LayoutTyVal.PTy layout :: layouts)
          | .error msg => .error msg
        | none => .error s!"LY02: Layout type not found for {repr rest} with baseLayout {repr baseLayout}"
      | none => .error "Base place not found in layoutmap"
    | mir.RExpr.DrefOp (base::rest) =>
      match cctx.layoutmap.find? base with
      | some baseLayout =>
        match baseLayout with
        | LayoutTyVal.PTy inner =>
          match getLayoutTypeFromBase rest inner with
          | none => .error s!"LY03: Layout type not found for {repr rest} with baseLayout {repr inner}"
          | some layout =>
            match getPlaceLayoutAux rest_rexprs cctx with
            | .ok layouts => .ok (layout :: layouts)
            | .error msg => .error msg
        | _ => .error "Invalid layout type"
      | _ => .error "Base place not found in layoutmap"
    | mir.RExpr.StructInitOp fields =>
      match fields with
      | [] => .error "StructInitOp fields cannot be empty"
      | fields =>
        match getPlaceLayoutAux fields cctx with
        | .ok layouts =>
           match getPlaceLayoutAux rest_rexprs cctx with
           | .ok restLayouts => .ok (layouts ++ restLayouts)
           | .error msg => .error msg
        | .error msg => .error msg
    | _ => .error s!"Unsupported {repr rexpr} for getPlaceLayout"

def getPlaceLayout (rexprs: List mir.RExpr) (cctx: CompileCtx) : Except String LayoutTyVal :=
  match getPlaceLayoutAux rexprs cctx with
  | .ok [] => .error "No expressions provided"
  | .ok [layout] => .ok layout
  | .ok layouts => .ok (LayoutTyVal.TupTy layouts)
  | .error msg => .error msg

def compileExpr (dstReg: oseair.Register) (ty: TyVal) (rexpr: mir.RExpr) (cctx: CompileCtx) : CompileExprResult :=
  match rexpr with
  | mir.RExpr.CopyOp (base::rest) =>
    match ExistPlaceToReg (base::rest) mir.RefOp.BorrowRef false cctx with
    | PlaceToRegResult.Err msg => CompileExprResult.Err msg
    | PlaceToRegResult.NotExist _baseplace msg => CompileExprResult.Err msg
    | PlaceToRegResult.Ok srcReg rhsCCtx =>
      let memcpyStmt := oseair.Stmt.memcpy dstReg srcReg ty
      CompileExprResult.Ok [memcpyStmt] rhsCCtx
  | mir.RExpr.ConstOp c =>
    let storeStmt := oseair.Stmt.cstore TyVal.NatTy [oseair.Val.Dat c] dstReg
    CompileExprResult.Ok [storeStmt] cctx
  | mir.RExpr.BinaryOp (mir.RExpr.CopyOp lopPlace) (mir.RExpr.CopyOp ropPlace) =>
    match ExistPlaceToReg lopPlace mir.RefOp.BorrowRef false cctx with
    | PlaceToRegResult.Err msg => CompileExprResult.Err msg
    | PlaceToRegResult.NotExist _baseplace msg => CompileExprResult.Err msg
    | PlaceToRegResult.Ok lopPtrReg lhsCCtx =>
      match ExistPlaceToReg ropPlace mir.RefOp.BorrowRef false lhsCCtx with
      | PlaceToRegResult.Err msg => CompileExprResult.Err msg
      | PlaceToRegResult.NotExist _baseplace msg => CompileExprResult.Err msg
      | PlaceToRegResult.Ok ropPtrReg rhsCCtx =>
        match (getPlaceLayout [mir.RExpr.CopyOp lopPlace] rhsCCtx, getPlaceLayout [mir.RExpr.CopyOp ropPlace] rhsCCtx) with
        | (.ok LayoutTyVal.NatTy, .ok LayoutTyVal.NatTy) =>
          let (newRegSuffix, rhsCCtx1) := freshRegSuffix rhsCCtx
          let lopDataReg := oseair.Register.R newRegSuffix
          let (newRegSuffix, rhsCCtx2) := freshRegSuffix rhsCCtx1
          let ropDataReg := oseair.Register.R newRegSuffix
          let lopLoadStmt := oseair.Stmt.assgn lopDataReg (oseair.Rhs.load TyVal.NatTy lopPtrReg)
          let ropLoadStmt := oseair.Stmt.assgn ropDataReg (oseair.Rhs.load TyVal.NatTy ropPtrReg)
          let (newRegSuffix, rhsCCtx3) := freshRegSuffix rhsCCtx2
          let binopDataReg := oseair.Register.R newRegSuffix
          let binopStmt := oseair.Stmt.assgn binopDataReg (oseair.Rhs.binop lopDataReg ropDataReg)
          let storeStmt := oseair.Stmt.rstore TyVal.NatTy binopDataReg dstReg
          CompileExprResult.Ok [lopLoadStmt, ropLoadStmt, binopStmt, storeStmt] rhsCCtx3
        | _ => CompileExprResult.Err "BinaryOp operands must have NatTy layout"
  | mir.RExpr.RefrOp refOp (base::rest) =>
    dbg_trace s!"Compiling RefrOp {repr refOp} on {repr (base::rest)} to {repr dstReg} of type {repr ty}"
    match ExistPlaceToReg (base::rest) refOp true /- force borrow instruction -/ cctx with
    | PlaceToRegResult.Err msg => CompileExprResult.Err msg
    | PlaceToRegResult.NotExist _baseplace msg => CompileExprResult.Err msg
    | PlaceToRegResult.Ok ptrReg rhsCCtx =>
      let rstoreStmt := oseair.Stmt.rstore TyVal.PTy ptrReg dstReg
      CompileExprResult.Ok [rstoreStmt] rhsCCtx
  | mir.RExpr.DrefOp (base::rest) =>
    -- Deref is special because _2 = (*_1).1 will first load the address stored at *_1 into a ptr,
    -- then create a new ptr at an offset 1 and then copy the data from that offset into _2
    -- We DO NOT handle the case of _2 = *(_1.1) for now.
    match ExistPlaceToReg [base] mir.RefOp.BorrowRef false cctx with
    | PlaceToRegResult.Err msg => CompileExprResult.Err msg
    | PlaceToRegResult.NotExist _baseplace msg => CompileExprResult.Err msg
    | PlaceToRegResult.Ok basePtrReg rhsCCtx =>
      match cctx.layoutmap.find? base with
      | none => CompileExprResult.Err s!"Base layout not found for base {repr base}"
      | some baseLayout =>
        match baseLayout with
        | LayoutTyVal.NatTy | LayoutTyVal.TupTy _ =>
          CompileExprResult.Err s!"Base layout for DrefOp must be a pointer type, found {repr baseLayout} for base {repr base}"
        | LayoutTyVal.PTy inner =>
            match mir.getPlaceOffset (base::rest) (layoutTyToTy inner) with
        | none => CompileExprResult.Err s!"Offset not found for place {repr (base::rest)} and ty {repr (layoutTyToTy inner)}"
        | some o =>
            let (newRegSuffix, rhsCCtx1) := freshRegSuffix rhsCCtx
            let dstPtrReg := oseair.Register.P newRegSuffix
            -- This loads the pointer in _1 into dstPtrReg
            let loadPtrStmt := oseair.Stmt.assgn dstPtrReg (oseair.Rhs.load TyVal.PTy basePtrReg)
            let p_and_c : Except String (oseair.Register × CompileCtx) :=
              if o == 0 then
                match insertStmtsInCurrBB [loadPtrStmt] rhsCCtx1 with
                | CompileResult.Err msg => .error msg
                | CompileResult.Ok rhsCCtx1 => .ok (dstPtrReg, rhsCCtx1)
              else
                let (newRegSuffix, rhsCCtx2) := freshRegSuffix rhsCCtx1
                -- This creates a pointer at offset o from dstPtrReg for (*_2).1
                let offset_stmt := oseair.Stmt.assgn (oseair.Register.P newRegSuffix) (oseair.Rhs.bor_offset dstPtrReg o)
                match insertStmtsInCurrBB [loadPtrStmt, offset_stmt] rhsCCtx2 with
                | CompileResult.Err msg => .error msg
                | CompileResult.Ok rhsCCtx3 => .ok (oseair.Register.P newRegSuffix, rhsCCtx3)
              match p_and_c with
              | .error msg => CompileExprResult.Err msg
              | .ok (ptrReg, rhsCCtx) =>
                -- memcpy from the ptrReg (which is at the correct offset) to memory behind dstReg
                let memcpyStmt := oseair.Stmt.memcpy dstReg ptrReg ty
                CompileExprResult.Ok [memcpyStmt] rhsCCtx
  | mir.RExpr.StructInitOp fields =>
    let rec compileFieldsAux := fun (dstReg: oseair.Register) (fieldsList : List mir.RExpr) (cctx' : CompileCtx) (acc : List oseair.Stmt) =>
      match fieldsList with
      | [] => CompileExprResult.Ok acc cctx'
      | f :: rest =>
        match getPlaceLayout [f] cctx' with
        | .error msg => CompileExprResult.Err msg
        | .ok layout =>
          let ty := layoutTyToTy layout
          match compileExpr dstReg ty f cctx' with
          | CompileExprResult.Err msg => CompileExprResult.Err msg
          | CompileExprResult.Ok stmts' cctx'' =>
            match rest with
            | [] => CompileExprResult.Ok (acc ++ stmts') cctx''
            | _ =>
              let (newRegSuffix, cctx3) := freshRegSuffix cctx''
              let new_dstreg := oseair.Register.P newRegSuffix
              -- The next projected field pointer is used as a write destination.
              let borStmt := oseair.Stmt.assgn new_dstreg (oseair.Rhs.mutbor_offset dstReg (layoutTypeSize layout))
              compileFieldsAux new_dstreg rest cctx3 (acc ++ stmts' ++ [borStmt])
    compileFieldsAux dstReg fields cctx []
  | _ => CompileExprResult.Err "{repr rexpr} not supported for now."

def compileStmt (stmt: mir.Stmt) (cctx: CompileCtx) : CompileResult :=
  match stmt with
  | mir.Stmt.Assgn lhsplace rexpr =>
    match lhsplace with
    | mir.LhsPlace.Place directplace =>
      match ExistPlaceToReg directplace mir.RefOp.MutRef false cctx with
      | PlaceToRegResult.NotExist lhsbase _msg =>
        match getPlaceLayout [rexpr] cctx with
        | .error msg => CompileResult.Err msg
        | .ok layout =>
          let (newRegSuffix, newCctx) := freshRegSuffix cctx
          let dstReg := oseair.Register.P newRegSuffix
          let ty := layoutTyToTy layout
          let allocStmt := oseair.Stmt.assgn dstReg (oseair.Rhs.alloc ty)
          let newPlacemap := newCctx.placemap.insert lhsbase (ty, dstReg)
          dbg_trace s!"Allocating place {repr lhsbase} of type {repr layout} at register {repr dstReg}"
          let newlayoutmap := newCctx.layoutmap.insert lhsbase layout
          let updatedCctx := { newCctx with placemap := newPlacemap, layoutmap := newlayoutmap }
          match insertStmtsInCurrBB [allocStmt] updatedCctx with
          | CompileResult.Err msg => CompileResult.Err msg
          | CompileResult.Ok updatedCctx1 =>
            let rhsResult := compileExpr dstReg ty rexpr updatedCctx1
            match rhsResult with
            | CompileExprResult.Err msg => CompileResult.Err msg
            | CompileExprResult.Ok stmts rhsCctx =>
              insertStmtsInCurrBB stmts rhsCctx
      | PlaceToRegResult.Ok dstReg cctx =>
        match getPlaceLayout [rexpr] cctx with
        | .error msg => CompileResult.Err msg
        | .ok layout =>
          let ty := layoutTyToTy layout
          let rhsResult := compileExpr dstReg ty rexpr cctx
          match rhsResult with
          | CompileExprResult.Err msg => CompileResult.Err msg
          | CompileExprResult.Ok stmts rhsCctx =>
            insertStmtsInCurrBB stmts rhsCctx
      | PlaceToRegResult.Err msg => CompileResult.Err msg
    | mir.LhsPlace.RExpr.DrefOp lplace =>
      match getPlaceLayout [mir.RExpr.DrefOp lplace] cctx with
        | .error msg => CompileResult.Err msg
        | .ok layout =>
        match ExistPlaceToReg lplace mir.RefOp.MutRef false cctx with
        | PlaceToRegResult.Err msg => CompileResult.Err msg
        | PlaceToRegResult.NotExist _baseplace msg => CompileResult.Err msg
        | PlaceToRegResult.Ok ptrReg rhsCCtx =>
          let (newRegSuffix, lhsCCtx1) := freshRegSuffix rhsCCtx
          let dstPtrReg := oseair.Register.P newRegSuffix
          let loadPtrStmt := oseair.Stmt.assgn dstPtrReg (oseair.Rhs.load
                                                          TyVal.PTy /- hardcode this to be a ptr ty -/
                                                          ptrReg)
          match insertStmtsInCurrBB [loadPtrStmt] lhsCCtx1 with
          | CompileResult.Err msg => CompileResult.Err msg
          | CompileResult.Ok lhsCCtx2 =>
            let rhsResult := compileExpr dstPtrReg (layoutTyToTy layout) rexpr lhsCCtx2
              match rhsResult with
              | CompileExprResult.Err msg => CompileResult.Err msg
              | CompileExprResult.Ok stmts rhsCctx =>
                insertStmtsInCurrBB stmts rhsCctx
  | mir.Stmt.Halt => insertStmtsInCurrBB [oseair.Stmt.halt] cctx


  def CompileBB (prog: mir.Prog) (bbNum: Nat) (cctx: CompileCtx) : CompileResult :=
    match prog.find? bbNum with
    | none => CompileResult.Err s!"Basic block {bbNum} not found in compile context."
    | some stmts =>
      let rec compileStmtsAux (stmts: List mir.Stmt) (cctx: CompileCtx) : CompileResult :=
        match stmts with
        | [] => CompileResult.Ok cctx
        | stmt :: rest =>
          match compileStmt stmt cctx with
          | CompileResult.Err msg => CompileResult.Err msg
          | CompileResult.Ok newCctx =>
            compileStmtsAux rest newCctx
      compileStmtsAux stmts cctx


  def MirMemoryToOSeairMemory (mem: mir.MemMap) (env: mir.Env) : oseair.MemMap :=
    let f := fun v ↦
      match v with
      | mir.MemValue.Val n => oseair.Val.Dat n
      | mir.MemValue.Undef => oseair.Val.Undef
      | mir.MemValue.PlaceTag place tag =>
        match mir.getPlaceBaseAddress place env with
        | none => oseair.Val.Undef
        | some base =>
          match mir.getPlaceType place env with
          | none => oseair.Val.Undef
          | some type =>
            match mir.getPlaceOffset place type with
            | none => oseair.Val.Undef
            | some offset => oseair.Val.Ptr base offset (typeSize type) tag
    Lean.AssocList.mapVal f mem

-- -- TODO: Can we break this up into smaller lemmas?
--   theorem mir_conc_step :
--     ∀
--     (N : Word) (bb: BB) (pc: PC) (pc' : PC) (ap: accessperm.AccessPerms) (ap' : accessperm.AccessPerms)
--     (prog: mir.Prog) (mem: mir.Mem) (env: mir.Env)
--     (mem': mir.Mem),
--     -- mir step
--     (prog.find? bb = some [mir.Stmt.Assgn [1] (mir.RExpr.CopyOp [0])]) →
--     (env.find? 0 = some (0, NatTy, 0)) →
--     (mem.mMap.find? 0 = some (mir.MemValue.Val 42)) →
--     mir.Eval2 (bb, pc, prog, env, mem, ap) (bb, pc', prog, env', mem', ap') →
--     -- conclusion
--     mem'.mMap.find? 1 = some (mir.MemValue.Val 42) := by
--       intros N bb pc pc' ap ap'
--             prog mem env
--             mem'
--             h_cpy_stmt h_srcInEnv h_valInMem h_mirstep
--       cases h_mirstep
--       case AssgnRel h1 h2_lplace h3_rplace h4 h5 h6 h7 h8 h9 h10 =>
--         have : h2_lplace = [1] := by
--           rw [h8] at h_cpy_stmt


--   -- TODO: Can we break this up into smaller lemmas?
--   theorem bisim_copy :
--     ∀
--     (N : Word) (bb: BB) (pc: PC) (pc' : PC) (ap: accessperm.AccessPerms) (ap' : accessperm.AccessPerms)
--     (prog: mir.Prog) (cctx: CompileCtx) (mem: mir.Mem) (env: mir.Env)
--     (srcplace: Place) (srcaddr: Addr) (srcty: TyVal) (srctag: Tag) (destplace: Place)
--     (mem': mir.Mem)
--     (seaRegMap : oseair.RegMap) (seaRegMap': oseair.RegMap)
--     (seaMem: oseair.Mem) (seaMem': oseair.Mem),
--     -- mir step
--     (prog.find? bb = some [mir.Stmt.Assgn destplace (mir.RExpr.CopyOp (srcbase :: srcrest))]) →
--     (env.find? srcbase = some (srcaddr, srcty, srctag)) →
--     (mem.mMap.find? srcaddr = some (mir.MemValue.Val N)) →
--     mir.Eval2 (bb, pc, prog, env, mem, ap) (bb, pc', prog, env', mem', ap') →
--     -- compiler function
--     compileStmt stmt cctx = CompileResult.Ok cctx' →
--     (cctx.placemap.find? srcbase = some (srcty, oseair.Register.P 0)) →
--     -- oseair step
--     oseair.Eval (seaBB, seaPC, cctx'.prog, seaReg, seaMem, seaAP) (seaBB, seaPC', cctx'.prog, seaReg', seaMem', seaAP')  →
--     MirMemoryToOSeairMemory mem.mMap env = seaMem.mMap →
--     -- conclusion
--     MirMemoryToOSeairMemory mem'.mMap env' = seaMem.mMap := by
--     intros N bb pc pc' ap ap'
--           prog cctx mem env srcplace
--           srcaddr srcty srctag destplace mem'
--           seaRegMap seaRegMap' seaMem seaMem'
--           h_cpy_stmt h_srcInEnv h_valInMem h_mirstep
--           h_compile_ok h_srcRegInPlacemap h_oseairstep
--           h_init_mem_eq
--     cases h_mirstep
--     sorry

-- assumption:  The BB can be traversed in an order that respects topological sort

end compiler
