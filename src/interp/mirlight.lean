import interp.units
import interp.accessperm

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

-- A value in memory can be undefined, a primitive or a place (ref)
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

def MemMap.beq : MemMap → MemMap → Bool
  | m1, m2 =>
    let l1 := m1.toList
    let l2 := m2.toList
    -- Compare as sets: every (addr, val) in l1 is in l2 and vice versa
    l1.all (fun (addr, val) => m2.find? addr == some val) &&
    l2.all (fun (addr, val) => m1.find? addr == some val)

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
deriving Repr

-- Expressions
inductive RExpr
--| PlaceTy (place : Place)       -- Place represented as a list of Nat
| ConstOp (constant : Word)
| CopyOp (place : Place)
| MoveOp (place : Place)
| RefrOp (refop : RefOp) (place : Place)
| DrefOp (place : Place)
| BinaryOp (lop : RExpr) (rop : RExpr)
| StructInitOp (fields : List RExpr)
deriving Repr

inductive LhsPlace
| Place (place : Place)
| RExpr.DrefOp (place : Place)
deriving Repr

inductive Stmt
| Assgn (lhs : LhsPlace) (rexpr : RExpr) : Stmt
| Halt : Stmt
deriving Repr

abbrev Prog := Lean.AssocList BasicBlock (List Stmt)

abbrev Env := Lean.AssocList (BasePlace) (Word × TyVal × Tag) -- Env maps Baseplaces to `(address, type, tag)`

def Env.beq : Env → Env → Bool
  | env1, env2 =>
    let l1 := env1.toList
    let l2 := env2.toList
    -- Compare as sets: every (bp, val) in l1 is in l2 and vice versa
    l1.all (fun (bp, val) => env2.find? bp == some val) &&
    l2.all (fun (bp, val) => env1.find? bp == some val)

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

instance : Repr RefOp where
  reprPrec
    | RefOp.BorrowRef, _ => "&"
    | RefOp.MutRef, _ => "&mut"
    | RefOp.Raw, _ => "&raw"

instance : Repr RExpr where
  reprPrec
    | RExpr.ConstOp c, _ => s!"ConstOp({repr c})"
    | RExpr.CopyOp p, _ => s!"CopyOp({repr p})"
    | RExpr.MoveOp p, _ => s!"MoveOp({repr p})"
    | RExpr.RefrOp ro p, _ => s!"RefrOp({repr ro}, {repr p})"
    | RExpr.DrefOp p, _ => s!"DrefOp({repr p})"
    | RExpr.BinaryOp l r, _ => s!"BinaryOp({repr l}, {repr r})"
    | RExpr.StructInitOp fs, _ => s!"StructInitOp({repr fs})"

instance : Repr Stmt where
  reprPrec
    | Stmt.Assgn lhs rexpr, _ => s!"{repr lhs} = {repr rexpr}"
    | Stmt.Halt, _ => "Halt"

instance : Repr LhsPlace where
  reprPrec
    | LhsPlace.Place place, _ => s!"(_{repr place})"
    | LhsPlace.RExpr.DrefOp place, _ => s!"*({repr place})"



open Stmt RExpr RhsResult LhsResult MemValue

def freshTag (ap : accessperm.AccessPerms) : Tag × accessperm.AccessPerms :=
  let newTag := ap.NextTag
  let newAP := { ap with NextTag := ap.NextTag + 1 }
  (newTag, newAP)

  /--
  Reads a sequence of `sz` words from the given `mem` at `addr`.
  Returns [] if sz is zero or mem contains no data.
  --/
def ReadWordSeq (mem : Mem) (addr : Word) (sz : Word) : List MemValue :=
  match sz with
  | 0 =>
      dbg_trace s!"ReadWordSeq: sz=0, addr={addr} → []"
      []
  | s + 1 =>
      let value := match mem.mMap.find? addr with
        | some v =>
            dbg_trace s!"ReadWordSeq: addr={addr} found value={v}"
            [v]
        | none =>
            dbg_trace s!"ReadWordSeq: addr={addr} not found"
            []
      let rest := ReadWordSeq mem (addr + 1) s
      dbg_trace s!"ReadWordSeq: addr={addr}, sz={sz}, value={value}, rest={rest}"
      value ++ rest

-- Function to get the type of a place from the environment
def getPlaceType (place : Place) (env : Env) : Option TyVal :=
  match place with
  | [] => none
  | basePlace :: rest =>
    match env.find? basePlace with
    | some (_, ty, _) =>
      dbg_trace s!"getPlaceType: basePlace={basePlace}, ty={ty}, rest={rest}"
      match rest with
      | [] => some ty
      | _ =>
        let result := getPlaceTypeFromBase rest ty
        dbg_trace s!"getPlaceType: getPlaceTypeFromBase(rest={rest}, ty={ty}) = {result}"
        result
    | none => none

def getPlaceOffset (place: Place) (ty: TyVal) : Option Word :=
  match place with
  | [] => some 0
  | _basePlace :: rest =>
    let rec calcOffset (subplace: Place) (currTy: TyVal) (acc: Word) : Option Word :=
      match subplace with
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
          else
            dbg_trace s!"getPlaceOffset: index out of bounds idx={idx}, len={tys.length}, currTy={currTy}, subplace={subplace}"
            none
        | _ =>
          dbg_trace s!"getPlaceOffset: expected tuple type but got {currTy} at subplace={subplace}"
          none
    let result := calcOffset rest ty 0
    match result with
    | none =>
      dbg_trace s!"getPlaceOffset: failed to compute offset for place={place} with base type={ty}"
      none
    | some _ => result

/--
  Returns the base address for a place, i.e., the address of its base place in the environment.
  Returns none if the place is empty or the base place is not found.
--/
def getPlaceBaseAddress (place : Place) (env : Env) : Option Word :=
  match place with
  | [] => none
  | basePlace :: _ =>
    match env.find? basePlace with
    | some (addr, _, _) => some addr
    | none => none

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
      | some offset =>
      let computedAddr := addr + offset
      dbg_trace s!"getPlaceAddr: basePlace={basePlace}, addr={addr}, offset={offset}, computedAddr={computedAddr}"
      some computedAddr
    | none => none

def allocate (mem : Mem) (size : Nat) : Word × Mem :=
  dbg_trace s!"allocate: size={size}"
  let newAddrStart := mem.addrStart + size
  let newMem := { mem with addrStart := newAddrStart }
  (mem.addrStart, newMem)

-- RExprToVal Function
def RExprToValFn : RExpr → Env → Mem → accessperm.AccessPerms → RhsResult
| ConstOp constant, _env, mem, ap =>
  Ok [Val constant] TyVal.NatTy ap mem

| CopyOp place, env, mem, ap =>
  match getPlaceAddr place env with
  | none => Err s!"ERR_CP00:Place {place} or address not found in environment."
  | some addr => match getPlaceType place env with
    | none => Err s!"ERR_CP01:Place {place} or address not found in environment."
    | some ty => match ReadWordSeq mem addr (typeSize ty) with
      | [] => Err s!"ERR_CP02:Address {addr} not found in memory."
      | values => Ok values ty ap mem

| MoveOp place, env, mem, ap =>
  match getPlaceAddr place env with
  | none => Err s!"ERR_MV00:Place {place} or address not found in environment."
  | some addr => match getPlaceType place env with
    | none => Err s!"ERR_MV01:Place {place} or address not found in environment."
    | some ty => match ReadWordSeq mem addr (typeSize ty) with
      | [] => Err s!"ERR_MV02:Address {addr} not found in memory."
      | values => Ok values ty ap mem

| RefrOp _refop place, env, mem, ap =>
  match place with
  | [] => Err "Empty place."
  | baseplace :: _ => match env.find? baseplace with
    | none => Err s!"Baseplace {baseplace} not found in environment."
    | some (_, _ty, _) =>
        let (newTag, newAP) := freshTag ap
        Ok [PlaceTag place newTag] TyVal.PTy newAP mem

| DrefOp  place, env, mem, ap =>
  match place with
  | [] => Err "Empty place."
  | base :: rest =>
    -- We handle two kinds of deref
    -- 1. Deref _1
    -- 2. Deref (*_1)._2
    -- We DO NOT handle *(_1.2) yet
    match getPlaceAddr [base] env with
    | none => Err s!"Place {base} or address not found in environment."
    | some addr => match getPlaceType [base] env with
      | none => Err s!"Place {base} or address not found in environment."
      | some ty => match ReadWordSeq mem addr (typeSize ty) with
        | [PlaceTag tplace _ttag] =>
          match getPlaceAddr (tplace ++ rest) env with
            | none => Err s!"Target Place {tplace} or address not found in environment."
            | some taddr => match getPlaceType (tplace ++ rest) env with
              | none => Err s!"Target Place {tplace} or address not found in environment."
              | some tty => match ReadWordSeq mem taddr (typeSize tty) with
                | [] => Err s!"Target Address {addr} not found in memory."
                | values => Ok values tty ap mem
        | _ => Err s!"Address {addr} does not contain a place."

| BinaryOp lop rop, env, mem, ap =>
  -- thread env, mem, ap from left to right
  match RExprToValFn lop env mem ap with
  | RhsResult.Ok v1 ty1 ap1 mem1 =>
    match RExprToValFn rop env mem1 ap1 with
    | RhsResult.Ok v2 ty2 ap2 mem2 =>
    if ty1 == TyVal.NatTy && ty2 == TyVal.NatTy then
      match (v1, v2) with
      | ([MemValue.Val n1], [MemValue.Val n2]) =>
        Ok [MemValue.Val (n1 + n2)] ty1 ap2 mem2 -- Simplified binary operation
      | _ => Err "BinaryOp expects single Nat values"
    else
      Err s!"Type mismatch: {ty1} vs {ty2} for {v1}, {v2}"
    | RhsResult.Err msg => Err msg
  | RhsResult.Err msg => Err msg

| StructInitOp fields, env, mem, ap =>
  let rec evalFields (fields : List RExpr) (env : Env) (curMem : Mem) (curAP : accessperm.AccessPerms)
    (accVals : List MemValue) (accTys : List TyVal) : RhsResult :=
    match fields with
    | [] => RhsResult.Ok accVals (TyVal.TupTy accTys) curAP curMem
    | f :: fs =>
      match RExprToValFn f env curMem curAP with
      | RhsResult.Ok vals ty newAP newMem =>
        -- dbg_trace s!"StructInitOp: vals={vals}, ty={ty}, accVals={accVals}, accTys={accTys}"
        evalFields fs env newMem newAP (accVals ++ vals) (accTys ++ [ty])
      | RhsResult.Err msg => RhsResult.Err msg
  evalFields fields env mem ap [] []



def WriteWordSeq (mem : Mem) (addr : Word) (values : List MemValue) : Mem :=
  match values with
  | [] => mem
  | value :: rest =>
    dbg_trace s!"WriteWordSeq: addr={addr}, value={value}, rest={rest}"
    let mem' := WriteWordSeq mem (addr + 1) rest
    let newMap := mem'.mMap.insert addr value
    {mem' with mMap := newMap}

partial def EvalStmt: Stmt → Env → Mem → accessperm.AccessPerms → LhsResult
  | Assgn lplace rexpr, env, mem, ap =>
    match RExprToValFn rexpr env mem ap with
    | RhsResult.Ok values ty newAp newMem =>
      match lplace with
      | LhsPlace.Place place =>
        match getPlaceAddr place env with
        | some addr =>
          let updatedMem := WriteWordSeq newMem addr values
          LhsResult.Ok env newAp updatedMem
        | none =>
          match place with
          | [newplace] =>
            let (newAddr, allocatedMem) := allocate newMem (typeSize ty)
            let updatedMem := WriteWordSeq allocatedMem newAddr values
            let (tag, newAp) := freshTag newAp
            let updatedEnv := env.insert newplace (newAddr, ty, tag)
            LhsResult.Ok updatedEnv newAp updatedMem
          | _ =>
            LhsResult.Err s!"lhs Place {place} does not have an address in the environment."
      | LhsPlace.RExpr.DrefOp place =>
        match getPlaceAddr place env with
        | some addr =>
          -- Read the pointer value at addr, then write to the address it points to
          match getPlaceType place env with
          | none => LhsResult.Err s!"lhs Dref Place {place} does not have a type in the environment."
          | some ty =>
            match ReadWordSeq mem addr (typeSize ty) with
            | [PlaceTag tplace _ttag] =>
              match getPlaceAddr tplace env with
              | none => LhsResult.Err s!"lhs Dref Target Place {tplace} does not have an address in the environment."
              | some taddr =>
                let updatedMem := WriteWordSeq newMem taddr values
                dbg_trace s!"Deref assignment: Writing to taddr={taddr} values={values}"
                LhsResult.Ok env newAp updatedMem
            | _ => LhsResult.Err s!"lhs Dref Address {addr} does not contain a place."
        | none =>
          LhsResult.Err s!"lhs Dref Place {place} does not have an address in the environment."
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
    stmt_list.get ⟨pc.stmt, h⟩ = Stmt.Assgn (LhsPlace.Place lplace) rexpr →
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
    stmt_list.get ⟨pc, h⟩ = Stmt.Assgn (LhsPlace.Place lplace) rexpr →
    RExprToValFn rexpr env mem ap = RhsResult.Ok values ty newAp newMem →
    (match lplace with
    | [newplace] =>
      let (newBaseAddr, allocatedMem) := allocate newMem (typeSize ty)
      let updatedMem := WriteWordSeq allocatedMem newBaseAddr values
      let (tag, newAp) := freshTag newAp
      let updatedEnv := env.insert newplace (newBaseAddr, ty, tag)
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
            dbg_trace s!"EvalStmt: {repr stmt}"
            match EvalStmt stmt env mem ap with
          | LhsResult.Ok newEnv newAp newMem => EvalProg {pc with stmt := pc.stmt + 1} prog newEnv newMem newAp
          | LhsResult.Err msg => LhsResult.Err msg
      else
        LhsResult.Err "Program counter out of bounds"

end mir
