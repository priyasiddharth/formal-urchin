import FormalUrchin.units
import FormalUrchin.mirlight
import Formal.oseairlight

import Lean.Data.AssocList

namespace compiler

structure CompileCtx where
  placemap : Lean.AssocList mir.BasePlace (mir.TyVal × oseair.Register)
  prog : oseair.Prog
  regSuffix : Nat
  currBB: Nat

def freshRegSuffix (ctx : CompileCtx) : Nat × CompileCtx :=
  let newSuffix := ctx.regSuffix + 1
  (ctx.regSuffix, { ctx with regSuffix := newSuffix })

-- Result type for RHS expr to val
inductive CompileResult
| Ok (cctx: CompileCtx)
| Err (message : String)

-- Result type for RHS expr to val
inductive CompileExprResult
| Ok (v: oseair.Register) (cctx: CompileCtx)
| Err (message : String)


-- def genCopyOpPtr, genLhsPtr

def PlaceToReg (v: oseair.Register) (place: mir.Place) (ty: mir.TyVal) (cctx: CompileCtx) : CompileExprResult :=
  match place with
  | [] => CompileExprResult.Err s!"Empty place"
  | _ => let offset := mir.getPlaceOffset place ty
    match offset with
    | none => CompileExprResult.Err s!"Offset not found for place {place}"
    | some o =>
      let (newRegSuffix, newCctx) := freshRegSuffix cctx
      let newPtr := oseair.Register.P newRegSuffix
      let stmt := oseair.Stmt.assgn newPtr (oseair.Rhs.bor_offset v o)
      match newCctx.prog.find? newCctx.currBB with
      | none => CompileExprResult.Err s!"Basic block {newCctx.currBB} not found in compile context."
      | some stmtList =>
        let newProg := newCctx.prog.insert newCctx.currBB (stmtList ++ [stmt])
        let newCctx1 := { newCctx with prog := newProg }
        CompileExprResult.Ok newPtr newCctx1

def compileStmt (stmt: mir.Stmt) (cctx: CompileCtx) : CompileResult :=
  match stmt with
  | mir.Stmt.Assgn lplace rexpr =>
       match rexpr with
      | mir.RExpr.CopyOp srcPlace =>
        match cctx.placemap.find? srcPlace with
        | none => CompileStmtResult.Err s!"Place {srcPlace} not found in context."
        | some (ty', srcReg) =>
          if ty == ty' then
            let stmt := oseair.Stmt.memcpy dstReg srcReg
            CompileStmtResult.Ok [stmt] cctx
          else
            CompileStmtResult.Err s!"Type mismatch: {ty} != {ty'}"
      | _ => CompileStmtResult.Err "Only CopyOp is supported for now."
    match lplace with
    | base :: _ => match cctx.ctx.find? base with
                    | none =>
                      let (newRegSuffix, newCctx) := freshRegSuffix cctx
                      let newPtr := oseair.Register.P newRegSuffix
                      let allocStmt := oseair.Stmt.assgn newPtr (oseair.Rhs.alloc (mir.TyVal.PtrTy 0))
    let updatedCtx := newCctx.ctx.insert lplace (ty, newReg)
    CompileStmtResult.Ok [allocStmt] { newCctx with ctx := updatedCtx }
    | some (ty, dstReg) =>


  match getPlaceAddr place env with
  | none => none
  | some addr =>
    let srcReg := oseair.Register.P addr
    let dstReg := oseair.Register.P (addr + 1) -- Assuming destination register is next to source
    let stmt := oseair.Stmt.memcpy dstReg srcReg
    some (stmt, env, mem, ap)

end compiler
