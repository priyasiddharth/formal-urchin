import obseq.mirlite
import obseq.oseair

namespace obseq.compile

open obseq
open obseq.mirlite
open obseq.oseair hiding State Result -- Avoid conflict

abbrev PlaceInfo := Register × LayoutTy
abbrev PlaceMap := List (Word × PlaceInfo)

structure CompilerState where
  nextReg : Nat
  placeMap : PlaceMap
  instrs : List oseair.Instr
deriving Repr, Inhabited

def freshReg (cs : CompilerState) : Register × CompilerState :=
  (Register.R cs.nextReg, { cs with nextReg := cs.nextReg + 1 })

def getPlaceInfo (cs : CompilerState) (base : Word) : Option PlaceInfo :=
  cs.placeMap.lookup base

def getReg (cs : CompilerState) (base : Word) : Option Register :=
  match getPlaceInfo cs base with
  | some (reg, _) => some reg
  | none => none

def getLayout (cs : CompilerState) (base : Word) : Option LayoutTy :=
  match getPlaceInfo cs base with
  | some (_, layout) => some layout
  | none => none

def setPlace (cs : CompilerState) (base : Word) (reg : Register) (layout : LayoutTy) : CompilerState :=
  { cs with placeMap := (base, (reg, layout)) :: cs.placeMap }

def emit (cs : CompilerState) (is : List oseair.Instr) : CompilerState :=
  { cs with instrs := cs.instrs ++ is }

structure PtrResult where
  reg : Register
  layout : LayoutTy
  cleanup : List Register
  cs : CompilerState
deriving Inhabited

structure RExprResult where
  reg : Register
  layout : LayoutTy
  cs : CompilerState
deriving Inhabited

def cleanupInstrs (regs : List Register) : List oseair.Instr :=
  regs.reverse.map oseair.Instr.Die

@[simp] theorem cleanupInstrs_nil : cleanupInstrs [] = [] := rfl

def layoutDeref? : LayoutTy → Option LayoutTy
| LayoutTy.PtrL inner => some inner
| _ => none

def placeLayout? (cs : CompilerState) (p : mirlite.Place) : Option LayoutTy :=
  match getPlaceInfo cs p.base with
  | some (_, baseLayout) =>
      match layoutResolvePath baseLayout p.path with
      | some (_, placeLayout) => some placeLayout
      | none => none
  | none => none

mutual
  def staticRExprData? : mirlite.RExpr → Option (LayoutTy × List oseair.Val)
  | mirlite.RExpr.ConstOp n => some (LayoutTy.NatL, [oseair.Val.Dat n])
  | mirlite.RExpr.StructInitOp fields =>
      match staticRExprDataList? fields with
      | some (layouts, vals) => some (LayoutTy.TupL layouts, vals)
      | none => none
  | _ => none

  def staticRExprDataList? : List mirlite.RExpr → Option (List LayoutTy × List oseair.Val)
  | [] => some ([], [])
  | field :: rest =>
      match staticRExprData? field, staticRExprDataList? rest with
      | some (layout, vals), some (restLayouts, restVals) =>
          some (layout :: restLayouts, vals ++ restVals)
      | _, _ => none
end

def structConstWords? : List mirlite.RExpr → Option (List Word)
  | [] => some []
  | mirlite.RExpr.ConstOp n :: rest =>
      Option.map (List.cons n) (structConstWords? rest)
  | _ => none

partial def inferRExprLayout (cs : CompilerState) : mirlite.RExpr → LayoutTy
| mirlite.RExpr.ConstOp _ => LayoutTy.NatL
| mirlite.RExpr.CopyOp p =>
    match placeLayout? cs p with
    | some layout => layout
    | none => LayoutTy.NatL
| mirlite.RExpr.MoveOp p =>
    match placeLayout? cs p with
    | some layout => layout
    | none => LayoutTy.NatL
| mirlite.RExpr.RefOp _ p =>
    LayoutTy.PtrL (match placeLayout? cs p with
      | some inner => inner
      | none => LayoutTy.NatL)
| mirlite.RExpr.DrefOp p =>
    match placeLayout? cs p with
    | some (LayoutTy.PtrL inner) => inner
    | _ => LayoutTy.NatL
| mirlite.RExpr.StructInitOp fields =>
    LayoutTy.TupL (fields.map (inferRExprLayout cs))
| mirlite.RExpr.BinaryOp _ _ => LayoutTy.NatL

partial def placeToBorrowReg
  (cs : CompilerState)
  (p : mirlite.Place)
  (kind : mirlite.RefKind) : PtrResult :=
  match getPlaceInfo cs p.base with
  | some (baseReg, baseLayout) =>
    match layoutResolvePath baseLayout p.path with
    | some (offset, placeLayout) =>
      let (tmpReg, cs1) := freshReg cs
      let rhs := match kind with
        | mirlite.RefKind.Shared => oseair.Rhs.BorOffset baseReg offset
        | mirlite.RefKind.Mut => oseair.Rhs.MutBorOffset baseReg offset
        | mirlite.RefKind.Raw => oseair.Rhs.CopyOffset baseReg offset
      let cs2 := emit cs1 [oseair.Instr.Assgn tmpReg rhs]
      { reg := tmpReg, layout := placeLayout, cleanup := [tmpReg], cs := cs2 }
    | none =>
      { reg := Register.R 0, layout := LayoutTy.NatL, cleanup := [], cs := cs }
  | none =>
      { reg := Register.R 0, layout := LayoutTy.NatL, cleanup := [], cs := cs }

def storePtrAtOffset (cs : CompilerState) (basePtr : Register) (offset : Word) :
    Register × List Register × CompilerState :=
  if offset = 0 then
    (basePtr, [], cs)
  else
    let (tmpReg, cs1) := freshReg cs
    let cs2 := emit cs1 [oseair.Instr.Assgn tmpReg (oseair.Rhs.MutBorOffset basePtr offset)]
    (tmpReg, [tmpReg], cs2)

-- Compilation Logic

-- Place to Register (returns register holding the POINTER to the place)
-- place-to-reg
-- Returns the pointer register plus the temporary projection registers that must be
-- discharged with `die` after the enclosing fragment has consumed them.
partial def placeToReg
  (cs : CompilerState)
  (p : mirlite.Place)
  (kind : mirlite.RefKind)
  (expected : Option LayoutTy := none) : PtrResult :=
  match getPlaceInfo cs p.base with
  | some (baseReg, baseLayout) =>
    match layoutResolvePath baseLayout p.path with
    | some (offset, placeLayout) =>
      if offset = 0 then
        -- The paper's `place-to-reg-exist1` reuses the base register whenever the
        -- projection offset is zero, even if the path is non-empty.
        { reg := baseReg, layout := placeLayout, cleanup := [], cs := cs }
      else
         -- Non-zero projections are modeled as temporary borrow-producing offset instructions.
         -- The offset is computed from the projected layout, not by summing path indices.
         let (tmpReg, cs1) := freshReg cs
         let rhs := match kind with
           | mirlite.RefKind.Shared => oseair.Rhs.BorOffset baseReg offset
           | mirlite.RefKind.Mut => oseair.Rhs.MutBorOffset baseReg offset
           | mirlite.RefKind.Raw => oseair.Rhs.CopyOffset baseReg offset
         let cs2 := emit cs1 [oseair.Instr.Assgn tmpReg rhs]
         { reg := tmpReg, layout := placeLayout, cleanup := [tmpReg], cs := cs2 }
    | none =>
      { reg := Register.R 0, layout := LayoutTy.NatL, cleanup := [], cs := cs }
  | none =>
    match expected with
    | some baseLayout =>
      if p.path == [] then
         let (newReg, cs1) := freshReg cs
         let cs2 := emit cs1 [oseair.Instr.Assgn newReg (oseair.Rhs.Alloc (layoutToTyVal baseLayout))]
         let cs3 := setPlace cs2 p.base newReg baseLayout
         { reg := newReg, layout := baseLayout, cleanup := [], cs := cs3 }
      else
         { reg := Register.R 0, layout := baseLayout, cleanup := [], cs := cs }
    | none =>
      { reg := Register.R 0, layout := LayoutTy.NatL, cleanup := [], cs := cs }

-- Compile RExpr to instructions, returning the pointer register that names the result
-- plus the result layout needed by later memcpy/load lowering.
mutual
  partial def compileRExprTo
    (cs : CompilerState)
    (dstPtr : Register)
    (expr : mirlite.RExpr) : CompilerState :=
    match staticRExprData? expr with
    | some (layout, vals) =>
        emit cs [oseair.Instr.CStore (layoutToTyVal layout) vals dstPtr]
    | none =>
        match expr with
        | mirlite.RExpr.CopyOp p =>
            let srcRes := placeToReg cs p mirlite.RefKind.Shared
            emit srcRes.cs ([oseair.Instr.Memcpy dstPtr srcRes.reg (layoutToTyVal srcRes.layout)] ++
              cleanupInstrs srcRes.cleanup)
        | mirlite.RExpr.RefOp kind p =>
            let srcRes := placeToBorrowReg cs p kind
            -- No cleanup: the borrow register's tag must stay live on the SB
            -- stack — it *is* the reference being created, not a temporary.
            emit srcRes.cs [oseair.Instr.RStore TyVal.PTy srcRes.reg dstPtr]
        | mirlite.RExpr.DrefOp p =>
            let pRes := placeToReg cs p mirlite.RefKind.Shared
            match layoutDeref? pRes.layout with
            | some innerLayout =>
                let (loadedPtr, cs1) := freshReg pRes.cs
                emit cs1 ([oseair.Instr.Assgn loadedPtr (oseair.Rhs.Load TyVal.PTy pRes.reg),
                  oseair.Instr.Memcpy dstPtr loadedPtr (layoutToTyVal innerLayout),
                  oseair.Instr.Die loadedPtr] ++ cleanupInstrs pRes.cleanup)
            | none => pRes.cs
        | mirlite.RExpr.StructInitOp fields =>
            let rec loop (csAcc : CompilerState) (curOffset : Word) (rest : List mirlite.RExpr) :
                CompilerState :=
              match rest with
              | [] => csAcc
              | field :: tail =>
                  let fieldLayout := inferRExprLayout csAcc field
                  let (fieldPtr, fieldCleanup, cs1) := storePtrAtOffset csAcc dstPtr curOffset
                  let cs2 := compileRExprTo cs1 fieldPtr field
                  let cs3 := emit cs2 (cleanupInstrs fieldCleanup)
                  loop cs3 (curOffset + layoutSize fieldLayout) tail
            loop cs 0 fields
        | mirlite.RExpr.BinaryOp lhs rhs =>
            let lhsRes := compileRExpr cs lhs
            let rhsRes := compileRExpr lhsRes.cs rhs
            let (lhsVal, cs1) := freshReg rhsRes.cs
            let (rhsVal, cs2) := freshReg cs1
            let (resVal, cs3) := freshReg cs2
            emit cs3 ([
              oseair.Instr.Assgn lhsVal (oseair.Rhs.Load TyVal.NatTy lhsRes.reg),
              oseair.Instr.Assgn rhsVal (oseair.Rhs.Load TyVal.NatTy rhsRes.reg),
              oseair.Instr.Assgn resVal (oseair.Rhs.BinOp lhsVal rhsVal),
              oseair.Instr.RStore TyVal.NatTy resVal dstPtr,
              oseair.Instr.Die lhsRes.reg,
              oseair.Instr.Die rhsRes.reg
            ])
        | _ => cs

  partial def compileRExpr (cs : CompilerState) (expr : mirlite.RExpr) : RExprResult :=
    let layout := inferRExprLayout cs expr
    let (resReg, cs1) := freshReg cs
    let cs2 := emit cs1 [oseair.Instr.Assgn resReg (oseair.Rhs.Alloc (layoutToTyVal layout))]
    let cs3 := compileRExprTo cs2 resReg expr
    { reg := resReg, layout := layout, cs := cs3 }
end

-- Compile Stmt
def compileStmt (cs : CompilerState) (stmt : mirlite.Stmt) : CompilerState :=
  match stmt with
  | mirlite.Stmt.Assgn (mirlite.LExpr.Place p) (mirlite.RExpr.ConstOp n) =>
    let lhsRes := placeToReg cs p mirlite.RefKind.Mut (some LayoutTy.NatL)
    emit lhsRes.cs ([oseair.Instr.CStore TyVal.NatTy [oseair.Val.Dat n] lhsRes.reg] ++
      cleanupInstrs lhsRes.cleanup)
  | mirlite.Stmt.Assgn (mirlite.LExpr.Place p) (mirlite.RExpr.StructInitOp fields) =>
    match structConstWords? fields with
    | some words =>
      let layout := LayoutTy.TupL (List.replicate words.length LayoutTy.NatL)
      let lhsRes := placeToReg cs p mirlite.RefKind.Mut (some layout)
      emit lhsRes.cs ([oseair.Instr.CStore
        (TyVal.TupTy (List.replicate words.length TyVal.NatTy))
        (words.map oseair.Val.Dat) lhsRes.reg] ++ cleanupInstrs lhsRes.cleanup)
    | none =>
      let rhs := mirlite.RExpr.StructInitOp fields
      let layout := inferRExprLayout cs rhs
      let lhsRes := placeToReg cs p mirlite.RefKind.Mut (some layout)
      let cs1 := compileRExprTo lhsRes.cs lhsRes.reg rhs
      emit cs1 (cleanupInstrs lhsRes.cleanup)
  | mirlite.Stmt.Assgn (mirlite.LExpr.Place dst) (mirlite.RExpr.CopyOp src) =>
    let srcRes := placeToReg cs src mirlite.RefKind.Shared
    let dstRes := placeToReg srcRes.cs dst mirlite.RefKind.Mut (some srcRes.layout)
    emit dstRes.cs ([oseair.Instr.Memcpy dstRes.reg srcRes.reg (layoutToTyVal srcRes.layout)] ++
      cleanupInstrs (srcRes.cleanup ++ dstRes.cleanup))
  | mirlite.Stmt.Assgn (mirlite.LExpr.Place dst)
      (mirlite.RExpr.BinaryOp (mirlite.RExpr.CopyOp lhs) (mirlite.RExpr.CopyOp rhs)) =>
    -- The operands are read through shared projected pointers, because binary evaluation only reads.
    let lhsRes := placeToReg cs lhs mirlite.RefKind.Shared
    let rhsRes := placeToReg lhsRes.cs rhs mirlite.RefKind.Shared
    -- Load concrete Nat payloads out of the operand pointers into temporary data registers.
    let (lhsVal, cs3) := freshReg rhsRes.cs
    let (rhsVal, cs4) := freshReg cs3
    -- Run the target-side arithmetic on data registers, not on pointer registers.
    let (resVal, cs5) := freshReg cs4
    -- The destination place is projected as a mutable borrow because the final step writes through it.
    let dstRes := placeToReg cs5 dst mirlite.RefKind.Mut (some LayoutTy.NatL)
    -- Lowering shape: load lhs, load rhs, compute BinOp, then store the result via the mutable pointer.
    emit dstRes.cs ([
      oseair.Instr.Assgn lhsVal (oseair.Rhs.Load TyVal.NatTy lhsRes.reg),
      oseair.Instr.Assgn rhsVal (oseair.Rhs.Load TyVal.NatTy rhsRes.reg),
      oseair.Instr.Assgn resVal (oseair.Rhs.BinOp lhsVal rhsVal),
      oseair.Instr.RStore TyVal.NatTy resVal dstRes.reg
    ] ++ cleanupInstrs (lhsRes.cleanup ++ rhsRes.cleanup ++ dstRes.cleanup))
  | mirlite.Stmt.Assgn lhs rhs =>
    -- Compile RHS to get result pointer
    let rhsRes := compileRExpr cs rhs
    -- Compile LHS to get destination pointer
    match lhs with
    | mirlite.LExpr.Place p =>
       -- If p is new (alloc), placeToReg handles it?
       -- We pass Mut kind for LHS.
       let lhsRes := placeToReg rhsRes.cs p mirlite.RefKind.Mut (some rhsRes.layout)
       -- Memcpy from RHS to LHS
       emit lhsRes.cs ([oseair.Instr.Memcpy lhsRes.reg rhsRes.reg (layoutToTyVal rhsRes.layout)] ++
         cleanupInstrs lhsRes.cleanup)
    | mirlite.LExpr.DrefOp p =>
       -- Deref assign.
       -- Resolve p to get pointer-to-pointer.
       let pRes := placeToReg rhsRes.cs p mirlite.RefKind.Shared -- Read the pointer
       match layoutDeref? pRes.layout with
       | some _ =>
         -- Load the actual target pointer and write through it using the RHS layout.
         let (targetPtr, cs3) := freshReg pRes.cs
         let cs4 := emit cs3 [oseair.Instr.Assgn targetPtr (oseair.Rhs.Load TyVal.PTy pRes.reg)]
         emit cs4 ([oseair.Instr.Memcpy targetPtr rhsRes.reg (layoutToTyVal rhsRes.layout)] ++
           cleanupInstrs pRes.cleanup)
       | none =>
         rhsRes.cs

  | mirlite.Stmt.Halt => emit cs [oseair.Instr.Halt]

end obseq.compile
