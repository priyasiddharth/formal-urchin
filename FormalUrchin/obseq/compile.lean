import FormalUrchin.obseq.mirlite
import FormalUrchin.obseq.oseair

namespace obseq.compile

open obseq.mirlite
open obseq.oseair hiding State Result -- Avoid conflict

-- Compiler State
-- Π: Place.base -> Register (We only map base places to registers holding their pointers)
-- The paper says "maps each source place to a pair <register, layoutty>".
-- But mainly used for base places.
-- For `place-to-reg-new`, we map a new place `p` to a register.
abbrev PlaceMap := List (Word × Register) -- Map mirlite.Place.base (Word) to oseair.Register

structure CompilerState where
  nextReg : Nat
  placeMap : PlaceMap
  instrs : List oseair.Instr
deriving Repr, Inhabited

def freshReg (cs : CompilerState) : Register × CompilerState :=
  (Register.R cs.nextReg, { cs with nextReg := cs.nextReg + 1 })

def getReg (cs : CompilerState) (base : Word) : Option Register :=
  cs.placeMap.lookup base

def setReg (cs : CompilerState) (base : Word) (reg : Register) : CompilerState :=
  { cs with placeMap := (base, reg) :: cs.placeMap }

def emit (cs : CompilerState) (is : List oseair.Instr) : CompilerState :=
  { cs with instrs := cs.instrs ++ is }

-- Helper to convert types
def convertTy (ty : mirlite.TyVal) : oseair.TyVal :=
  match ty with
  | mirlite.TyVal.NatTy => oseair.TyVal.NatTy
  | mirlite.TyVal.PTy => oseair.TyVal.PTy
  | mirlite.TyVal.TupTy tys => oseair.TyVal.TupTy (tys.map convertTy)


-- Compilation Logic

-- Place to Register (returns register holding the POINTER to the place)
-- place-to-reg
-- Returns: Register (ptr), updated CS
partial def placeToReg (cs : CompilerState) (p : mirlite.Place) (kind : mirlite.RefKind) : Register × CompilerState :=
  match getReg cs p.base with
  | some baseReg =>
    -- place-to-reg-1 or 2
    -- If path is empty, return baseReg.
    -- If path is not empty, emit offset instruction.
    if p.path == [] then (baseReg, cs)
    else
       -- Calculate offset (simplified: assume 1 word per path element for now or implement type awareness?)
       -- Paper uses `offsetof`. We need type info.
       -- For simplicity, let's assume flat addressing or known offsets.
       -- Or we assume the interpreter handles complex paths, but compiler generates specific offsets.
       -- Let's just emit an offset instruction with a symbolic offset (e.g., sum of path).
       -- Since we don't have types in Place struct, we assume offsets are pre-calculated or simple.
       let offset := p.path.foldl (· + ·) 0 -- Assuming path elements ARE offsets.
       let (tmpReg, cs1) := freshReg cs
       -- Emit bor/mutbor/copy offset based on kind
       let rhs := match kind with
         | mirlite.RefKind.Shared => oseair.Rhs.BorOffset baseReg offset
         | mirlite.RefKind.Mut => oseair.Rhs.MutBorOffset baseReg offset
         | mirlite.RefKind.Raw => oseair.Rhs.CopyOffset baseReg offset -- "copy_offset" for raw
       let cs2 := emit cs1 [oseair.Instr.Assgn tmpReg rhs]
       -- Note: Paper says emit `die` later.
       -- "The fragment also contains a die...".
       -- We should probably return the `die` instruction to be emitted at end of scope?
       -- For now, let's just emit Assgn. The Die is implicit or handled by scope management (not implemented here).
       -- SeaUrchin implementation says "The die statements are implied and not emitted".
       -- But OSEA-IR has explicit `die`.
       -- Let's stick to generating just the setup.
       (tmpReg, cs2)

  | none =>
    -- place-to-reg-new (Only if path is empty?)
    -- Or error?
    -- If it's a new allocation.
    -- Usually we only alloc if we see `alloc` or implicitly on first assignment.
    -- Here we assume we are compiling an assignment to `p`, so we might need to alloc.
    if p.path == [] then
       let (newReg, cs1) := freshReg cs
       -- Emit alloc. What type? We lack type info here.
       -- Assume NatTy for simplicity or pass type.
       -- Let's assume we compile `Assgn` which has RHS type.
       -- But `placeToReg` is called for `p`.
       -- We'll assume a default or parameterized type.
       let ty := oseair.TyVal.NatTy -- Placeholder
       let cs2 := emit cs1 [oseair.Instr.Assgn newReg (oseair.Rhs.Alloc ty)]
       let cs3 := setReg cs2 p.base newReg
       (newReg, cs3)
    else
       -- Cannot alloc sub-path.
       (Register.R 0, cs) -- Error placeholder

-- Compile RExpr to Instructions
-- Returns: Result Register (holding value) or Instruction Sequence?
-- "compiles ... into instruction sequence ... returns (layout) type ... and instruction sequence"
-- Here we'll return the register holding the result of evaluation.
partial def compileRExpr (cs : CompilerState) (expr : mirlite.RExpr) : Register × CompilerState :=
  match expr with
  | mirlite.RExpr.ConstOp n =>
    let (reg, cs1) := freshReg cs
    let (ptrReg, cs2) := freshReg cs1
    -- Alloc temp storage for constant?
    -- Paper: `rhs-const-to`: emits `cstore` into destination fragment.
    -- Here we want to produce a register holding the VALUE (or pointer to value?).
    -- OSEA-IR registers hold `(Ty, List Val)`.
    -- If it's a constant, we can put `Dat n` in register directly via Assgn?
    -- OSEA-IR Assgn takes `Rhs`. `Rhs` doesn't have `Const`.
    -- `Rhs` has `Load`, `Alloc`, `Bor`, `BinOp`.
    -- Ah, OSEA-IR example (Table 5) uses `cstore N, 41, R0`.
    -- This stores constant into memory pointed to by R0.
    -- It doesn't put constant in register?
    -- Wait, `Rhs` has `BinOp`. `BinOp` takes registers.
    -- `rval-binop` reads `Dat` from registers.
    -- So registers CAN hold `Dat`.
    -- But how do we load `Dat` into register?
    -- There is no `Const` in `Rhs`!
    -- OSEA-IR seems to rely on `cstore` to write to memory.
    -- And `load` to read from memory.
    -- So to get a constant in a register:
    -- 1. Alloc temp.
    -- 2. CStore constant to temp.
    -- 3. Load from temp.
    -- This seems inefficient but matches the lack of `Const` in `Rhs`.
    -- Or maybe `cstore` is just for side effects.
    -- Let's assume we alloc a temp for the result.
    let (resReg, cs3) := freshReg cs2
    let cs4 := emit cs3 [
      oseair.Instr.Assgn resReg (oseair.Rhs.Alloc oseair.TyVal.NatTy),
      oseair.Instr.CStore oseair.TyVal.NatTy [oseair.Val.Dat n] resReg
    ]
    -- Now resReg holds pointer to the constant.
    -- If we need the VALUE (e.g. for BinOp), we must Load.
    -- But `compileRExpr` generally produces a place/value?
    -- MIRLITE RExpr evaluates to `List MemValue`.
    -- OSEA-IR registers hold `List Val`.
    -- `Val` can be `Dat` or `Ptr`.
    -- If context expects value (BinOp), we load.
    -- If context expects destination (Assign), we might keep as ptr.
    -- Let's return the pointer to the result for uniformity with `placeToReg`.
    (resReg, cs4)

  | mirlite.RExpr.BinaryOp lhs rhs =>
    let (lReg, cs1) := compileRExpr cs lhs -- Ptr to lhs
    let (rReg, cs2) := compileRExpr cs1 rhs -- Ptr to rhs
    -- Load values
    let (lVal, cs3) := freshReg cs2
    let (rVal, cs4) := freshReg cs3
    let cs5 := emit cs4 [
      oseair.Instr.Assgn lVal (oseair.Rhs.Load oseair.TyVal.NatTy lReg),
      oseair.Instr.Assgn rVal (oseair.Rhs.Load oseair.TyVal.NatTy rReg)
    ]
    -- Compute
    let (resVal, cs6) := freshReg cs5
    let cs7 := emit cs6 [
       oseair.Instr.Assgn resVal (oseair.Rhs.BinOp lVal rVal)
    ]
    -- Store result (to match uniform "return pointer" strategy)
    let (resPtr, cs8) := freshReg cs7
    let cs9 := emit cs8 [
       oseair.Instr.Assgn resPtr (oseair.Rhs.Alloc oseair.TyVal.NatTy),
       oseair.Instr.RStore oseair.TyVal.NatTy resVal resPtr -- Store result
    ]
    (resPtr, cs9)

  | mirlite.RExpr.CopyOp p =>
     -- CopyOp(p).
     -- Resolve p to ptr.
     let (pReg, cs1) := placeToReg cs p mirlite.RefKind.Shared
     -- Alloc dest.
     let (dstReg, cs2) := freshReg cs1
     let cs3 := emit cs2 [
       oseair.Instr.Assgn dstReg (oseair.Rhs.Alloc oseair.TyVal.NatTy), -- Assume NatTy
       oseair.Instr.Memcpy dstReg pReg oseair.TyVal.NatTy
     ]
     (dstReg, cs3)

  | _ => (Register.R 0, cs) -- TODO: Implement others

-- Compile Stmt
def compileStmt (cs : CompilerState) (stmt : mirlite.Stmt) : CompilerState :=
  match stmt with
  | mirlite.Stmt.Assgn lhs rhs =>
    -- Compile RHS to get result pointer
    let (rhsPtr, cs1) := compileRExpr cs rhs
    -- Compile LHS to get destination pointer
    match lhs with
    | mirlite.LExpr.Place p =>
       -- If p is new (alloc), placeToReg handles it?
       -- We pass Mut kind for LHS.
       let (lhsPtr, cs2) := placeToReg cs1 p mirlite.RefKind.Mut
       -- Memcpy from RHS to LHS
       emit cs2 [oseair.Instr.Memcpy lhsPtr rhsPtr oseair.TyVal.NatTy]
    | mirlite.LExpr.DrefOp p =>
       -- Deref assign.
       -- Resolve p to get pointer-to-pointer.
       let (pPtr, cs2) := placeToReg cs1 p mirlite.RefKind.Shared -- Read the pointer
       -- Load the actual target pointer
       let (targetPtr, cs3) := freshReg cs2
       let cs4 := emit cs3 [oseair.Instr.Assgn targetPtr (oseair.Rhs.Load oseair.TyVal.PTy pPtr)]
       -- Memcpy
       emit cs4 [oseair.Instr.Memcpy targetPtr rhsPtr oseair.TyVal.NatTy]

  | mirlite.Stmt.Halt => emit cs [oseair.Instr.Halt]

end obseq.compile
