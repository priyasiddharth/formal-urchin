import obseq2.syntax
import obseq2.oseair

namespace obseq2.compile

open obseq2
open obseq2.oseair (Register Instr Rhs Val)

abbrev TargetProg := obseq2.oseair.Prog

structure CompilerState where
  nextReg   : Nat
  nextLabel : Nat
  code      : Nat → Option Instr
deriving Inhabited

structure PtrResult where
  reg : Register
  cleanup : List Register
  cs : CompilerState
deriving Inhabited

structure RExprResult where
  reg : Register
  cs : CompilerState
deriving Inhabited

def emit (cs : CompilerState) (instrs : List Instr) : CompilerState :=
  let n := instrs.length
  { cs with
    nextLabel := cs.nextLabel + n,
    code      := fun pc =>
      if cs.nextLabel ≤ pc ∧ pc < cs.nextLabel + n then
        instrs.get? (pc - cs.nextLabel)
      else
        cs.code pc }

def freshReg (cs : CompilerState) : Register × CompilerState :=
  (Register.R cs.nextReg, { cs with nextReg := cs.nextReg + 1 })

def cleanupInstrs (regs : List Register) : List Instr :=
  regs.reverse.map Instr.Die

def localReg (loc : Local Γ τ) : Register :=
  Register.R loc.idx.1

def pathOffset : PathTo src dst → Nat
  | .nil => 0
  | .field (tys := tys) idx tail =>
      layoutSizeList (tys.take idx.1) + pathOffset tail

def borrowOffsetRhs (kind : RefKind) (base : Register) (offset : Word) : Rhs :=
  match kind with
  | .Shared => Rhs.BorOffset base offset
  | .Mut => Rhs.MutBorOffset base offset
  | .Raw => Rhs.CopyOffset base offset

/-- Compile a place to a register holding a pointer to the place's address. -/
def placeToReg (cs : CompilerState) (kind : RefKind) : Place Γ τ → PtrResult
  | .local loc =>
      { reg := localReg loc, cleanup := [], cs := cs }
  | .proj base path =>
      let baseRes := placeToReg cs kind base
      let offset := pathOffset path
      if offset = 0 then
        baseRes
      else
        let (tmpReg, cs1) := freshReg baseRes.cs
        let cs2 := emit cs1 [Instr.Assgn tmpReg (borrowOffsetRhs kind baseRes.reg offset)]
        { reg := tmpReg, cleanup := baseRes.cleanup ++ [tmpReg], cs := cs2 }
  | .deref ptrPlace =>
      let ptrRes := placeToReg cs .Shared ptrPlace
      let (loadedReg, cs1) := freshReg ptrRes.cs
      let cs2 := emit cs1 [Instr.Assgn loadedReg (Rhs.Load obseq.TyVal.PTy ptrRes.reg)]
      let cs3 := emit cs2 (cleanupInstrs ptrRes.cleanup)
      { reg := loadedReg, cleanup := [loadedReg], cs := cs3 }

def placeToBorrowReg (cs : CompilerState) (kind : RefKind) : Place Γ τ → PtrResult
  | .local loc =>
      let (tmpReg, cs1) := freshReg cs
      let cs2 := emit cs1 [Instr.Assgn tmpReg (borrowOffsetRhs kind (localReg loc) 0)]
      { reg := tmpReg, cleanup := [tmpReg], cs := cs2 }
  | .proj base path =>
      let baseRes := placeToReg cs kind base
      let offset := pathOffset path
      let (tmpReg, cs1) := freshReg baseRes.cs
      let cs2 := emit cs1 [Instr.Assgn tmpReg (borrowOffsetRhs kind baseRes.reg offset)]
      { reg := tmpReg, cleanup := baseRes.cleanup ++ [tmpReg], cs := cs2 }
  | .deref ptrPlace =>
      let ptrRes := placeToReg cs .Shared ptrPlace
      let (loadedReg, cs1) := freshReg ptrRes.cs
      let cs2 := emit cs1 [Instr.Assgn loadedReg (Rhs.Load obseq.TyVal.PTy ptrRes.reg)]
      let cs3 := emit cs2 (cleanupInstrs ptrRes.cleanup)
      let (tmpReg, cs4) := freshReg cs3
      let cs5 := emit cs4 [Instr.Assgn tmpReg (borrowOffsetRhs kind loadedReg 0)]
      { reg := tmpReg, cleanup := [loadedReg, tmpReg], cs := cs5 }

def compileRExprTo
  (cs : CompilerState)
  (dstPtr : Register)
  {τ : LayoutTy}
  (expr : RExpr Γ τ) : CompilerState :=
  match expr with
  | .constInit value =>
      emit cs [Instr.CStore obseq.TyVal.NatTy [Val.Dat value] dstPtr]
  | .copy (τ := τ) src =>
      let srcRes := placeToReg cs .Shared src
      emit srcRes.cs ([Instr.Memcpy dstPtr srcRes.reg (layoutToTyVal τ)] ++ cleanupInstrs srcRes.cleanup)
  | .ref kind src =>
      let srcRes := placeToBorrowReg cs kind src
      emit srcRes.cs [Instr.RStore obseq.TyVal.PTy srcRes.reg dstPtr]

def compileRExpr
  (cs : CompilerState)
  {τ : LayoutTy}
  (expr : RExpr Γ τ) : RExprResult :=
  let (resReg, cs1) := freshReg cs
  let cs2 := emit cs1 [Instr.Assgn resReg (Rhs.Alloc (layoutToTyVal τ))]
  let cs3 := compileRExprTo cs2 resReg expr
  { reg := resReg, cs := cs3 }

def compileStmt (cs : CompilerState) : Stmt Γ → CompilerState
  | .halt => emit cs [Instr.Halt]
  | .assign dst rhs =>
      let dstRes := placeToReg cs .Mut dst
      let cs1 := compileRExprTo dstRes.cs dstRes.reg rhs
      emit cs1 (cleanupInstrs dstRes.cleanup)

def initLocalsAux : Nat → Ctx → List Instr
  | _, [] => []
  | idx, layout :: rest =>
      Instr.Assgn (Register.R idx) (Rhs.Alloc (layoutToTyVal layout)) ::
        initLocalsAux (idx + 1) rest

def initLocals (Γ : Ctx) : List Instr :=
  initLocalsAux 0 Γ

def initialState (Γ : Ctx) : CompilerState :=
  emit { nextReg := Γ.length, nextLabel := 0, code := fun _ => none } (initLocals Γ)

def compileProg (prog : Prog Γ) : Nat → Option Instr :=
  (List.foldl compileStmt (initialState Γ) prog).code

end obseq2.compile
