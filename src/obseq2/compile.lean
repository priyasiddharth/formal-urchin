import obseq2.syntax
import obseq2.oseair

namespace obseq2.compile

open obseq2
open obseq2.oseair (Register Instr Rhs Val)

abbrev TargetProg := obseq2.oseair.Prog

structure CompilerState where
  nextReg : Nat
  instrs : List Instr
deriving Repr, Inhabited

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
  { cs with instrs := cs.instrs ++ instrs }

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

def placeBaseLocal : Place Γ τ → Σ σ, Local Γ σ
  | .local loc => ⟨τ, loc⟩
  | .proj base _ => placeBaseLocal base

def placeOffset : Place Γ τ → Nat
  | .local _ => 0
  | .proj base path => placeOffset base + pathOffset path

def placeBaseReg (place : Place Γ τ) : Register :=
  localReg (placeBaseLocal place).2

def borrowOffsetRhs (kind : RefKind) (base : Register) (offset : Word) : Rhs :=
  match kind with
  | .Shared => Rhs.BorOffset base offset
  | .Mut => Rhs.MutBorOffset base offset
  | .Raw => Rhs.CopyOffset base offset

def placeToBorrowReg
  (cs : CompilerState)
  (kind : RefKind)
  (place : Place Γ τ) : PtrResult :=
  let (tmpReg, cs1) := freshReg cs
  let cs2 := emit cs1 [Instr.Assgn tmpReg (borrowOffsetRhs kind (placeBaseReg place) (placeOffset place))]
  { reg := tmpReg, cleanup := [tmpReg], cs := cs2 }

def placeToReg
  (cs : CompilerState)
  (kind : RefKind)
  (place : Place Γ τ) : PtrResult :=
  let baseReg := placeBaseReg place
  let offset := placeOffset place
  if offset = 0 then
    { reg := baseReg, cleanup := [], cs := cs }
  else
    let (tmpReg, cs1) := freshReg cs
    let cs2 := emit cs1 [Instr.Assgn tmpReg (borrowOffsetRhs kind baseReg offset)]
    { reg := tmpReg, cleanup := [tmpReg], cs := cs2 }

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
  | .deref (τ := τ) src =>
      let srcRes := placeToReg cs .Shared src
      let (loadedPtr, cs1) := freshReg srcRes.cs
      emit cs1 ([Instr.Assgn loadedPtr (Rhs.Load obseq.TyVal.PTy srcRes.reg)] ++
        cleanupInstrs srcRes.cleanup ++
        [Instr.Memcpy dstPtr loadedPtr (layoutToTyVal τ)])

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

def initialState (Γ : Ctx) : CompilerState := {
  nextReg := Γ.length
  instrs := initLocals Γ
}

def compileProg (prog : Prog Γ) : TargetProg :=
  (List.foldl compileStmt (initialState Γ) prog).instrs

end obseq2.compile
