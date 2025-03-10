import FormalUrchin.units
import FormalUrchin.mirlight
import FormalUrchin.oseairlight

import Lean.Data.AssocList

namespace compiler

structure CompileCtx where
  placemap : Lean.AssocList BasePlace (TyVal × oseair.Register)
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


def insertStmtsInCurrBB (stmts: List oseair.Stmt) (cctx: CompileCtx) : CompileResult :=
  match cctx.prog.find? cctx.currBB with
  | none => CompileResult.Err s!"Basic block {cctx.currBB} not found in compile context."
  | some stmtList =>
    let newProg := (cctx.prog.erase cctx.currBB).insert cctx.currBB (stmtList ++ stmts)
    let newCctx := { cctx with prog := newProg }
    CompileResult.Ok newCctx

-- def genCopyOpPtr, genLhsPtr
def PlaceToRegWTy (v: oseair.Register) (place: mir.Place) (ty: TyVal) (cctx: CompileCtx) : CompileExprResult :=
  match place with
  | [] => CompileExprResult.Err s!"Empty place"
  | _ => let offset := mir.getPlaceOffset place ty
    match offset with
    | none => CompileExprResult.Err s!"Offset not found for place {place}"
    | some o => if o == 0 then CompileExprResult.Ok v cctx
      else
        let (newRegSuffix, newCctx) := freshRegSuffix cctx
        let newPtr := oseair.Register.P newRegSuffix
        let stmt := oseair.Stmt.assgn newPtr (oseair.Rhs.bor_offset v o)
        match insertStmtsInCurrBB [stmt] newCctx with
        | CompileResult.Err msg => CompileExprResult.Err msg
        | CompileResult.Ok newCctx1 => CompileExprResult.Ok newPtr newCctx1



def PlaceToReg (place: mir.Place) (cctx: CompileCtx) : CompileExprResult :=
  match place with
  | [] => CompileExprResult.Err s!"Emply place"
  | base :: _ => match cctx.placemap.find? base with
    | none => CompileExprResult.Err s!"Base place {base} not found in compile context."
    | some (ty, reg) => PlaceToRegWTy reg place ty cctx


def compileStmt (stmt: mir.Stmt) (cctx: CompileCtx) : CompileResult :=
  match stmt with
  | mir.Stmt.Assgn lplace rexpr =>
       match rexpr with
      | mir.RExpr.CopyOp (rbase::rest) =>
          match cctx.placemap.find? rbase with
          | none => CompileResult.Err s!"Place {rbase} not found in context."
          | some (rty, _) =>
            match PlaceToReg (rbase::rest) cctx with
            | CompileExprResult.Err msg => CompileResult.Err msg
            | CompileExprResult.Ok srcReg rhsCCtx =>
              match lplace with
              | base :: _ => match cctx.placemap.find? base with
                              | none =>
                                let (newRegSuffix, newCctx) := freshRegSuffix rhsCCtx
                                let dstReg := oseair.Register.P newRegSuffix
                                let allocStmt := oseair.Stmt.assgn dstReg (oseair.Rhs.alloc rty)
                                let memcpyStmt := oseair.Stmt.memcpy dstReg srcReg rty -- since rty == lty
                                insertStmtsInCurrBB [allocStmt, memcpyStmt] newCctx
                              | some (_ty, dstReg) =>
                                -- check that _ty == rty
                                let memcpyStmt := oseair.Stmt.memcpy dstReg srcReg rty -- since rty == lty
                                insertStmtsInCurrBB [memcpyStmt] rhsCCtx
              | [] => CompileResult.Err "Empty place"
      | _ => CompileResult.Err "Only CopyOp is supported for now."
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
        match mir.getPlaceAddr place env with
        | none => oseair.Val.Undef
        | some addr => oseair.Val.Ptr addr tag
    Lean.AssocList.mapVal f mem

-- TODO: Can we break this up into smaller lemmas?
  theorem mir_conc_step :
    ∀
    (N : Word) (bb: BB) (pc: PC) (pc' : PC) (ap: accessperm.AccessPerms) (ap' : accessperm.AccessPerms)
    (prog: mir.Prog) (mem: mir.Mem) (env: mir.Env)
    (mem': mir.Mem),
    -- mir step
    (prog.find? bb = some [mir.Stmt.Assgn [1] (mir.RExpr.CopyOp [0])]) →
    (env.find? 0 = some (0, NatTy, 0)) →
    (mem.mMap.find? 0 = some (mir.MemValue.Val 42)) →
    mir.Eval2 (bb, pc, prog, env, mem, ap) (bb, pc', prog, env', mem', ap') →
    -- conclusion
    mem'.mMap.find? 1 = some (mir.MemValue.Val 42) := by
      intros N bb pc pc' ap ap'
            prog mem env
            mem'
            h_cpy_stmt h_srcInEnv h_valInMem h_mirstep
      cases h_mirstep
      case AssgnRel h1 h2_lplace h3_rplace h4 h5 h6 h7 h8 h9 h10 =>
        have : h2_lplace = [1] := by
          rw [h8] at h_cpy_stmt


  -- TODO: Can we break this up into smaller lemmas?
  theorem bisim_copy :
    ∀
    (N : Word) (bb: BB) (pc: PC) (pc' : PC) (ap: accessperm.AccessPerms) (ap' : accessperm.AccessPerms)
    (prog: mir.Prog) (cctx: CompileCtx) (mem: mir.Mem) (env: mir.Env)
    (srcplace: Place) (srcaddr: Addr) (srcty: TyVal) (srctag: Tag) (destplace: Place)
    (mem': mir.Mem)
    (seaRegMap : oseair.RegMap) (seaRegMap': oseair.RegMap)
    (seaMem: oseair.Mem) (seaMem': oseair.Mem),
    -- mir step
    (prog.find? bb = some [mir.Stmt.Assgn destplace (mir.RExpr.CopyOp (srcbase :: srcrest))]) →
    (env.find? srcbase = some (srcaddr, srcty, srctag)) →
    (mem.mMap.find? srcaddr = some (mir.MemValue.Val N)) →
    mir.Eval2 (bb, pc, prog, env, mem, ap) (bb, pc', prog, env', mem', ap') →
    -- compiler function
    compileStmt stmt cctx = CompileResult.Ok cctx' →
    (cctx.placemap.find? srcbase = some (srcty, oseair.Register.P 0)) →
    -- oseair step
    oseair.Eval (seaBB, seaPC, cctx'.prog, seaReg, seaMem, seaAP) (seaBB, seaPC', cctx'.prog, seaReg', seaMem', seaAP')  →
    MirMemoryToOSeairMemory mem.mMap env = seaMem.mMap →
    -- conclusion
    MirMemoryToOSeairMemory mem'.mMap env' = seaMem.mMap := by
    intros N bb pc pc' ap ap'
          prog cctx mem env srcplace
          srcaddr srcty srctag destplace mem'
          seaRegMap seaRegMap' seaMem seaMem'
          h_cpy_stmt h_srcInEnv h_valInMem h_mirstep
          h_compile_ok h_srcRegInPlacemap h_oseairstep
          h_init_mem_eq
    cases h_mirstep
    sorry

-- assumption:  The BB can be traversed in an order that respects topological sort

end compiler
