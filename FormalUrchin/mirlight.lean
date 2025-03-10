import FormalUrchin.units
import FormalUrchin.accessperm

import Lean.Data.AssocList
-- set_option diagnostics true


namespace mir

structure ProgCount where
  bb: Word
  stmt: Word
deriving Inhabited, Repr

abbrev BasicBlock := Word

def ProgCount.beq : ProgCount → ProgCount → Bool
  | ⟨bb1, stmt1⟩, ⟨bb2, stmt2⟩ =>
    bb1 == bb2 && stmt1 == stmt2

instance : BEq ProgCount where
  beq := ProgCount.beq

abbrev Tag := Word

/- Can use dep types? -/
-- Memory mapping
inductive MemValue
| Undef
| Val (value : Word)         -- A simple `Nat` value
| PlaceTag (place : Place) (tag : Word) -- A (place, tag) pair

instance : Inhabited MemValue where
  default := MemValue.Val 0xDEADBEEF

instance : Repr MemValue where
    reprPrec
    | MemValue.Undef, _ => "⊥"
    | MemValue.Val value, _ => repr value
    | MemValue.PlaceTag place tag, _ => repr (place, tag)

instance : Repr (List (Word × MemValue)) where
  reprPrec lst _ := repr lst

partial def MemValue.toString : MemValue → String
  | Undef => "⊥"
  | Val value => s!"Val({value})"
  | PlaceTag place tag => s!"PlaceTag({place}, {tag})"

instance : ToString MemValue where
  toString := MemValue.toString

abbrev MemMap := Lean.AssocList Word MemValue

instance : ToString MemMap where
  toString memMap := toString (memMap.toList.map (fun (addr, value) => s!"({addr} -> {value})"))

instance : Repr MemMap where
  reprPrec memMap _ := repr memMap.toList

def MemValue.beq : MemValue → MemValue → Bool
  | Val v1, Val v2 => v1 == v2
  | PlaceTag p1 t1, PlaceTag p2 t2 => p1 == p2 && t1 == t2
  | _, _ => false

instance : BEq MemValue where
    beq := MemValue.beq

structure Mem where
  mMap: MemMap
  addrStart: Word
deriving Inhabited, Repr

partial def MemMap.beq : MemMap → MemMap → Bool
  | Lean.AssocList.nil, Lean.AssocList.nil => true
  | Lean.AssocList.cons k1 v1 rest1, Lean.AssocList.cons k2 v2 rest2 =>
    let _ : BEq MemMap := ⟨MemMap.beq⟩
    k1 == k2 && v1 == v2 && rest1 == rest2
  | _, _ => false

instance : BEq MemMap where
  beq := MemMap.beq

partial def Mem.beq : Mem → Mem → Bool
  | ⟨m1, a1⟩, ⟨m2, a2⟩ =>
    m1 == m2 && a1 == a2

instance : BEq Mem where
  beq := Mem.beq

instance : ToString Mem where
  toString mem := s!"{toString mem.mMap}, addr_start: {mem.addrStart}"

inductive RefOp
| BorrowRef
| MutRef
| Raw

-- Expressions
inductive RExpr
--| PlaceTy (place : Place)       -- Place represented as a list of Nat
--| ConstTy (constant : Word)
| CopyOp (place : Place)
| MoveOp (place : Place)
| RefrOp (refop : RefOp) (place : Place)
| DrefOp (place : Place)
/- | BinaryOp (lop : RExpr) (rop : RExpr)
| StructInitOp (fields : List RExpr) -/

inductive Stmt
| Assgn (lplace : Place) (rexpr : RExpr) : Stmt
| Halt : Stmt

abbrev Prog := Lean.AssocList BasicBlock (List Stmt)

abbrev Env := Lean.AssocList (BasePlace) (Word × TyVal × Tag) -- Env maps Baseplaces to `(address, type, tag)`

partial def Env.beq : Env → Env → Bool
  | Lean.AssocList.nil, Lean.AssocList.nil => true
  | Lean.AssocList.cons k1 (w1, ty1, tag1) rest1, Lean.AssocList.cons k2 (w2, ty2, tag2) rest2 =>
    let _ : BEq Env := ⟨Env.beq⟩
    k1 == k2 && w1 == w2 && ty1 == ty2 && tag1 == tag2 && rest1 == rest2
   | _, _ => false

instance : BEq Env where
  beq := Env.beq

instance : ToString Env where
  toString env := toString (env.toList.map (fun (bp, (addr, ty, tag)) => s!"({bp} -> ({addr}, {ty}, {tag}))"))

-- Result type for RHS expr to val
inductive RhsResult
| Ok (values : List MemValue) (ty : TyVal) (ap : accessperm.AccessPerms) (mem : Mem)
| Err (message : String)

-- Result type for statements
inductive LhsResult
| Ok (E : Env) (ap : accessperm.AccessPerms) (mem : Mem)
| Err (message : String)


open Stmt RExpr RhsResult LhsResult MemValue

def freshTag (ap : accessperm.AccessPerms) : Tag × accessperm.AccessPerms :=
  let newTag := ap.NextTag
  let newAP := { ap with NextTag := ap.NextTag + 1 }
  (newTag, newAP)


-- Helper function for structural recursion
def typeSizeAux : List TyVal → Word → Word
| [], acc => acc
| TyVal.NatTy :: rest, acc | TyVal.PTy :: rest,acc  => typeSizeAux rest (acc + 1)
| TyVal.TupTy nested :: rest, acc =>
    let nestedSize := typeSizeAux nested 0 -- Process the nested tuple first
    typeSizeAux rest (acc + nestedSize)    -- Add its size to the accumulator

-- Main `typeSize` function
def typeSize (ty : TyVal) : Nat :=
  match ty with
  | TyVal.NatTy | TyVal.PTy => 1
  | TyVal.TupTy tys => typeSizeAux tys 0

def ReadWordSeq (mem : Mem) (addr : Word) (sz : Word) : List MemValue :=
  match sz with
  | 0 => []
  | s + 1  =>  -- Process the list of types explicitly
      let value := match mem.mMap.find? addr with
      | some v => [v]
      | none => [] -- Return an empty list if the value is not found
      let rest := ReadWordSeq mem (addr + 1) s -- read the rest of the words
      value ++ rest

def getPlaceTypeFromBase (place : Place) (bty : TyVal) : Option TyVal :=
match place with
| [] => none
| _basePlace :: rest =>
  -- Traverse the rest of the place to find the subtype
  let rec traverse (ty : TyVal) (path : Place) : Option TyVal :=
    match path with
    | [] => some ty
    | idx :: rest =>
      match ty with
      | TyVal.TupTy tys =>
        if h : idx < tys.length then
          traverse (tys.get ⟨idx, h⟩) rest
        else
          none
      | _ => none
  traverse bty rest

-- Function to get the type of a place from the environment
def getPlaceType (place : Place) (env : Env) : Option TyVal :=
match place with
| [] => none
| basePlace :: rest =>
  match env.find? basePlace with
  | some (_, ty, _) => getPlaceTypeFromBase rest ty
  | none => none

def getPlaceOffset (place: Place) (ty: TyVal) : Option Word :=
  match place with
  | [] => some 0
  | _basePlace :: rest =>
    let rec calcOffset (path: Place) (currTy: TyVal) (acc: Word) : Option Word :=
      match path with
      | [] => some acc
      | idx :: rest =>
        match currTy with
        | TyVal.TupTy tys =>
          if h : idx < tys.length then
            -- Sum sizes of preceding elements at this level
            let precedingOffset := (List.take idx tys).foldl (fun acc ty => acc + typeSize ty) 0
            -- Get type at current index
            let nextTy := tys.get ⟨idx, h⟩
            -- Recurse with accumulated offset
            calcOffset rest nextTy (acc + precedingOffset)
          else none
        | _ => none
    calcOffset rest ty 0

def exampleTupleType : TyVal :=
  TyVal.TupTy [
    TyVal.NatTy,  -- First Nat
    TyVal.TupTy [   -- Nested tuple
      TyVal.NatTy,
      TyVal.TupTy [ -- Double nested tuple
        TyVal.NatTy,
        TyVal.NatTy,
        TyVal.NatTy
      ]
    ]
  ]

def examplePlace : Place := [0, 1, 1]  -- BasePlace, 1, 2
#eval getPlaceOffset examplePlace exampleTupleType -- expected: some 2

theorem test_getPlaceOffset :
  getPlaceOffset examplePlace exampleTupleType = some 2 := by
  simp [getPlaceOffset]
  simp [examplePlace]
  simp [exampleTupleType]
  simp [getPlaceOffset.calcOffset]
  simp [typeSize]
  -- Following is a shorter way to do it
  --simp [getPlaceOffset, examplePlace, exampleTupleType, getPlaceOffset.calcOffset, typeSize]


def getPlaceAddr (place : Place) (env : Env) : Option Word :=
    match place with
    | [] => none
    | basePlace :: _ =>
        match env.find? basePlace with
        | some (addr, ty, _) =>
          match getPlaceOffset place ty with
          | none => none
          | some offset => some (addr + offset)
        | none => none

def allocate (mem : Mem) (size : Nat) : Word × Mem :=
  let newAddrStart := mem.addrStart + size
  let newMem := { mem with addrStart := newAddrStart }
  (mem.addrStart, newMem)

-- RExprToVal Function
def RExprToValFn : RExpr → Env → Mem → accessperm.AccessPerms → RhsResult
| CopyOp place, env, mem, ap =>
  match getPlaceAddr place env with
  | none => Err s!"Place {place} or address not found in environment."
  | some addr => match getPlaceType place env with
    | none => Err s!"Place {place} or address not found in environment."
    | some ty => match ReadWordSeq mem addr (typeSize ty) with
      | [] => Err s!"Address {addr} not found in memory."
      | values => Ok values ty ap mem

| MoveOp place, env, mem, ap =>
  match getPlaceAddr place env with
  | none => Err s!"Place {place} or address not found in environment."
  | some addr => match getPlaceType place env with
    | none => Err s!"Place {place} or address not found in environment."
    | some ty => match ReadWordSeq mem addr (typeSize ty) with
      | [] => Err s!"Address {addr} not found in memory."
      | values => Ok values ty ap mem

| RefrOp _refop place, env, mem, ap =>
  match place with
  | [] => Err "Empty place."
  | baseplace :: _ => match env.find? baseplace with
    | none => Err s!"Baseplace {baseplace} not found in environment."
    | some (_, _ty, _) =>
        let (newTag, newAP) := freshTag ap
        Ok [PlaceTag place newTag] TyVal.PTy newAP mem

| DrefOp place, env, mem, ap =>
  match getPlaceAddr place env with
  | none => Err s!"Place {place} or address not found in environment."
  | some addr => match getPlaceType place env with
    | none => Err s!"Place {place} or address not found in environment."
    | some ty => match ReadWordSeq mem addr (typeSize ty) with
      | [PlaceTag tplace _ttag] =>
        match getPlaceAddr tplace env with
          | none => Err s!"Target Place {place} or address not found in environment."
           | some taddr => match getPlaceType tplace env with
            | none => Err s!"Target Place {place} or address not found in environment."
            | some tty => match ReadWordSeq mem taddr (typeSize tty) with
              | [] => Err s!"Target Address {addr} not found in memory."
              | values => Ok values tty ap mem
      | _ => Err s!"Address {addr} does not contain a place."
/-
| BinaryOp lop rop, env, mem, sb =>
    match (RExprToVal lop env mem sb, RExprToVal rop env mem sb) with
    | (Ok v1 ty1 sb1 mem1, Ok v2 ty2 sb2 mem2) =>
        if ty1 = ty2 then Ok (v1 + v2) ty1 sb2 mem2 -- Simplified binary operation
        else Err s!"Type mismatch: {ty1} vs {ty2}"
    | (Err msg, _) => Err msg
    | (_, Err msg) => Err msg

| StructInitOp fields, env, mem, sb =>
    let results := fields.map (fun field => RExprToVal field env mem sb)
    if results.all (fun r => match r with | Ok _ _ _ _ => true | _ => false) then
      let values := results.map (fun r => match r with | Ok v _ _ _ => v | _ => 0)
      let tys := results.map (fun r => match r with | Ok _ ty _ _ => ty | _ => "")
      Ok 0 (tys.foldl (· ++ " ") "") sb mem -- Simplified structure creation
    else Err "Error initializing structure." -/

def WriteWordSeq (mem : Mem) (addr : Word) (values : List MemValue) : Mem :=
  let rec process (addr : Nat) (values : List MemValue) (mMap : MemMap) : MemMap :=
    match values with
    | [] => mMap
    | value :: rest =>
        let newMap := mMap.insert addr value
        process (addr + 1) rest newMap
  let newMap := process addr values mem.mMap
  { mem with mMap := newMap }

partial def EvalStmt: Stmt → Env → Mem → accessperm.AccessPerms → LhsResult
  | Assgn lplace rexpr, env, mem, ap =>
    match RExprToValFn rexpr env mem ap with
    | RhsResult.Ok values ty newAp newMem =>
      match lplace with
      | [newplace] =>
        let (newAddr, allocatedMem) := allocate newMem (typeSize ty)
        let updatedMem := WriteWordSeq allocatedMem newAddr values
        let (tag, newAp) := freshTag newAp
        let updatedEnv := env.insert newplace (newAddr, ty, tag)
        LhsResult.Ok updatedEnv newAp updatedMem
      | _ =>
        match getPlaceAddr lplace env with
        | none => LhsResult.Err s!"lhs Place {lplace} not found in environment."
        | some addr =>
          let updatedMem := WriteWordSeq newMem addr values
          LhsResult.Ok env newAp updatedMem
    | RhsResult.Err msg => LhsResult.Err msg
  | Halt, env, mem, ap => LhsResult.Ok env ap mem

inductive Eval : ProgCount × Prog × Env × Mem × accessperm.AccessPerms →
  ProgCount × Prog × Env × Mem × accessperm.AccessPerms →
    Prop
  | AssgnRel : ∀ (pc: ProgCount) (newpc: ProgCount) (lplace : Place) (rexpr : RExpr) (env : Env) (mem : Mem)
    (ap : accessperm.AccessPerms) (values : List MemValue) (ty : TyVal) (newAp : accessperm.AccessPerms)
    (newMem : Mem) (newEnv : Env) (prog: Prog) (stmt_list: List Stmt),
    prog.find? pc.bb = some stmt_list →
    (h : pc.stmt < stmt_list.length) →
    stmt_list.get ⟨pc.stmt, h⟩ = Stmt.Assgn lplace rexpr →
    RExprToValFn rexpr env mem ap = RhsResult.Ok values ty newAp newMem →
    (match lplace with
    | [newplace] =>
      let (newAddr, allocatedMem) := allocate newMem (typeSize ty)
      let updatedMem := WriteWordSeq allocatedMem newAddr values
      let (tag, newAp) := freshTag newAp
      let updatedEnv := env.insert newplace (newAddr, ty, tag)
      LhsResult.Ok updatedEnv newAp updatedMem
    | _ =>
      match getPlaceAddr lplace env with
      | none => LhsResult.Err s!"lhs Place {lplace} not found in environment."
      | some addr =>
        let updatedMem := WriteWordSeq newMem addr values
        LhsResult.Ok env newAp updatedMem) = LhsResult.Ok newEnv newAp newMem →
        newpc = {pc with stmt := pc.stmt + 1} →
    Eval (pc, prog, env, mem, ap) (newpc, prog, newEnv, newMem, newAp)
  | HaltRel : ∀ (pc: ProgCount) (prog: Prog) (env : Env) (mem : Mem) (ap : accessperm.AccessPerms) (stmt_list: List Stmt),
    prog.find? pc.bb = some stmt_list →
    (h: pc.stmt < stmt_list.length) →
    stmt_list.get ⟨pc.stmt, h⟩ = Stmt.Halt →
    Eval (pc, prog, env, mem, ap) (pc, prog, env, mem, ap)



/-  theorem step_pc_stays_same_iff_halt
    {pc : ProgCount} {prog : Prog} {env : Env} {mem : Mem} {ap : accessperm.AccessPerms}
    {stmt_list : List Stmt}
    (h_bb : prog.find? pc.bb = some stmt_list)
    (h_stmt: pc.stmt < stmt_list.length):
      (stmt_list.get ⟨pc.stmt, h_stmt⟩ = Stmt.Halt) ↔
    Eval (pc, prog, env, mem, ap) (pc, prog, env, mem, ap) := by
  apply Iff.intro
  { intros h_stmt_eq
    apply Eval.HaltRel
    exact h_bb
    exact h_stmt_eq
  }
  {
    intros h_eval
    cases h_eval
    case HaltRel s1 s2 s3 s4 =>
     -- Unify stmt_list and s1
      have : stmt_list = s1 := by
        rw [s4] at h_bb
        injection h_bb with h_eq
        symm
        exact h_eq
      subst this
      exact s3
  }

 -/

inductive Eval2 : BB × PC  × Prog × Env × Mem × accessperm.AccessPerms →
  BB × PC × Prog × Env × Mem × accessperm.AccessPerms →
    Prop
  | AssgnRel : ∀ (bb: BB)  (pc: PC) (lplace : Place) (rexpr : RExpr) (env : Env) (mem : Mem)
    (ap : accessperm.AccessPerms) (values : List MemValue) (ty : TyVal) (newAp : accessperm.AccessPerms)
    (newMem : Mem) (newEnv : Env) (prog: Prog),
    prog.find? bb = some stmt_list →
    (h : pc < stmt_list.length) →
    stmt_list.get ⟨pc, h⟩ = Stmt.Assgn lplace rexpr →
    RExprToValFn rexpr env mem ap = RhsResult.Ok values ty newAp newMem →
    (match lplace with
    | [newplace] =>
      let (newAddr, allocatedMem) := allocate newMem (typeSize ty)
      let updatedMem := WriteWordSeq allocatedMem newAddr values
      let (tag, newAp) := freshTag newAp
      let updatedEnv := env.insert newplace (newAddr, ty, tag)
      LhsResult.Ok updatedEnv newAp updatedMem
    | _ =>
      match getPlaceAddr lplace env with
      | none => LhsResult.Err s!"lhs Place {lplace} not found in environment."
      | some addr =>
        let updatedMem := WriteWordSeq newMem addr values
        LhsResult.Ok env newAp updatedMem) = LhsResult.Ok newEnv newAp newMem →
    Eval2 (bb, pc, prog, env, mem, ap) (bb, pc + 1, prog, newEnv, newMem, newAp)
  | HaltRel : ∀ (bb: BB) (pc: PC) (prog: Prog) (env : Env) (mem : Mem) (ap : accessperm.AccessPerms),
    prog.find? bb = some stmt_list →
    (h: pc < stmt_list.length) →
    stmt_list.get ⟨pc, h⟩ = Stmt.Halt →
    Eval2 (bb, pc, prog, env, mem, ap) (bb, pc, prog, env, mem, ap)

 /-   theorem assgn_updates_env :
    ∀ (pc : ProgCount) (lplace : Place) (rexpr : RExpr) (env : Env) (mem : Mem) (ap : accessperm.AccessPerms)
      (values : List MemValue) (ty : TyVal) (newAp : accessperm.AccessPerms) (newMem : Mem) (newEnv : Env) (stmts : List Stmt),
    (h : pc < stmts.length) →
    stmts.get ⟨pc, h⟩ = Stmt.Assgn lplace rexpr →
    RExprToValFn rexpr env mem ap = RhsResult.Ok values ty newAp newMem →
    (match lplace with
    | [newplace] =>
      let (newAddr, allocatedMem) := allocate newMem (typeSize ty)
      let updatedMem := WriteWordSeq allocatedMem newAddr values
      let (tag, newAp) := freshTag newAp
      let updatedEnv := env.insert newplace (newAddr, ty, tag)
      LhsResult.Ok updatedEnv newAp updatedMem
    | _ =>
      match getPlaceAddr lplace env with
      | none => LhsResult.Err s!"lhs Place {lplace} not found in environment."
      | some addr =>
        let updatedMem := WriteWordSeq newMem addr values
        LhsResult.Ok env newAp updatedMem) = LhsResult.Ok newEnv newAp newMem →
    Eval (pc, stmts, env, mem, ap) (pc + 1, stmts, newEnv, newMem, newAp) :=
  by
    intros pc lplace rexpr env mem ap values ty newAp newMem newEnv stmts h hStmt hRhs
    apply Eval.AssgnRel
    exact hStmt
    exact hRhs
 -/
inductive EvalStar :
    ProgCount × Prog × Env × Mem × accessperm.AccessPerms →
    ProgCount × Prog × Env × Mem × accessperm.AccessPerms → Prop
  | refl : ∀ s, EvalStar s s
  | step : ∀ s₁ s₂ s₃,
    Eval s₁ s₂ →
    EvalStar s₂ s₃ →
    EvalStar s₁ s₃

instance : Inhabited Env where
  default := Lean.AssocList.nil

instance : Inhabited Mem where
  default := { mMap := Lean.AssocList.nil, addrStart := 0 }


instance : Inhabited LhsResult where
  default := LhsResult.Err "Default error"

partial def EvalProg : ProgCount → Prog → Env → Mem → accessperm.AccessPerms → LhsResult
  | pc, prog, env, mem, ap =>
    match prog.find? pc.bb with
    | none => LhsResult.Err "Basic block not found: {ProgCount.bb}"
    | some stmts =>
      if h : pc.stmt < stmts.length then
        match stmts.get ⟨pc.stmt, h⟩ with
        | Halt => LhsResult.Ok env ap mem
        | stmt =>
          match EvalStmt stmt env mem ap with
          | LhsResult.Ok newEnv newAp newMem => EvalProg {pc with stmt := pc.stmt + 1} prog newEnv newMem newAp
          | LhsResult.Err msg => LhsResult.Err msg
      else
        LhsResult.Err "Program counter out of bounds"

end mir
