import obseq.types
import obseq.sb

namespace obseq.mirlite

open obseq

-- Basic Types
structure Place where
  base : Word
  path : List Word -- offsets or indices
deriving Repr, BEq, Inhabited

-- Memory Value
inductive MemValue
| Undef
| Val (value : Word)
| PlaceTag (place : Place) (tag : Tag) -- Pointer value in MIRLITE
deriving Repr, BEq, Inhabited

abbrev MemMap := List (Word × MemValue)

structure Mem where
  mMap : MemMap
  addrStart : Word
deriving Repr, Inhabited

def Mem.find? (m : Mem) (addr : Word) : Option MemValue :=
  List.lookup addr m.mMap

def Mem.write (m : Mem) (addr : Word) (v : MemValue) : Mem :=
  { m with mMap := (addr, v) :: m.mMap.filter (fun (a, _) => a != addr) }

-- Environment
-- Maps Base Place (Word) to (Address, Type, Tag)
abbrev Env := List (Word × (Word × TyVal × Tag))

def Env.lookup (e : Env) (base : Word) : Option (Word × TyVal × Tag) :=
  List.lookup base e

def Env.insert (e : Env) (base : Word) (info : Word × TyVal × Tag) : Env :=
  (base, info) :: e.filter (fun (b, _) => b != base)


-- Syntax
inductive RefKind
| Shared
| Mut
| Raw
deriving Repr, BEq, Inhabited

inductive RExpr
| ConstOp (value : Word)
| CopyOp (place : Place)
| MoveOp (place : Place)
| RefOp (kind : RefKind) (place : Place)
| DrefOp (place : Place)
| StructInitOp (fields : List RExpr)
| BinaryOp (lhs : RExpr) (rhs : RExpr)
deriving Repr, Inhabited

inductive LExpr
| Place (place : Place)
| DrefOp (place : Place)
deriving Repr, Inhabited

inductive Stmt
| Assgn (lhs : LExpr) (rhs : RExpr)
| Halt
deriving Repr, Inhabited

abbrev Prog := List Stmt

-- Interpreter State
structure State where
  pc : Nat
  env : Env
  mem : Mem
  ap : AccessPerms
deriving Repr, Inhabited

inductive Result
| Ok (state : State)
| Err (msg : String)
deriving Repr, Inhabited

inductive ValRes
| Ok (vals : List MemValue) (ty : TyVal) (state : State)
| Err (msg : String)
deriving Repr, Inhabited

-- Helpers
def readWordSeq (m : Mem) (addr : Word) (sz : Nat) : List MemValue :=
  match sz with
  | 0 => []
  | n + 1 =>
    match m.find? addr with
    | some v => v :: readWordSeq m (addr + 1) n
    | none => MemValue.Undef :: readWordSeq m (addr + 1) n

def writeWordSeq (m : Mem) (addr : Word) (vals : List MemValue) : Mem :=
  match vals with
  | [] => m
  | v :: vs => writeWordSeq (m.write addr v) (addr + 1) vs

def allocate (m : Mem) (sz : Nat) : Word × Mem :=
  (m.addrStart, { m with addrStart := m.addrStart + sz })

-- Place Resolution Result
structure PlaceRes where
  addr : Word
  tag : Tag
  ty : TyVal
  state : State
deriving Repr, Inhabited

-- Helper to compute offset and type for sub-place
def resolvePath (ty : TyVal) (path : List Word) : Option (Nat × TyVal) :=
  tyResolvePath ty path

def resolveDirectPlace (state : State) (p : Place) : Result × PlaceRes :=
  match state.env.lookup p.base with
  | some (baseAddr, baseTy, baseTag) =>
    match resolvePath baseTy p.path with
    | some (offset, ty) =>
      (Result.Ok state, { addr := baseAddr + offset, tag := baseTag, ty := ty, state := state })
    | none => (Result.Err s!"Invalid path {repr p.path} for type {baseTy}", default)
  | none =>
    if p.path == [] then
       (Result.Err s!"Place base {p.base} not found", default)
    else
       (Result.Err s!"Place base {p.base} not found", default)

-- Place Resolution (plc-resolv, alloc-plc-resolv, dref-plc-resolv)
partial def resolvePlace (state : State) (l : LExpr) (_forWrite : Bool) : Result × PlaceRes :=
  match l with
  | LExpr.Place p =>
    resolveDirectPlace state p

  | LExpr.DrefOp p =>
     -- dref-plc-resolv
     match resolveDirectPlace state p with
     | (Result.Ok s1, res1) =>
        -- Issue read
        match sb_read s1.ap res1.addr res1.tag with
        | SBResult.Ok ap2 =>
           let s2 := { s1 with ap := ap2 }
           match readWordSeq s2.mem res1.addr 1 with
           | [MemValue.PlaceTag q gq] =>
             -- Recursive resolve of q. q is a Place.
             match resolvePlace s2 (LExpr.Place q) false with
             | (Result.Ok s3, res3) =>
                (Result.Ok s3, { res3 with tag := gq })
             | (Result.Err msg, _) => (Result.Err msg, default)
           | _ => (Result.Err "Deref: Memory did not contain a PlaceTag", default)
        | SBResult.Err msg => (Result.Err msg, default)
     | (Result.Err msg, _) => (Result.Err msg, default)

mutual
  partial def evalStructFields (fields : List RExpr) (state : State)
      (accVals : List MemValue := []) (accTys : List TyVal := []) : ValRes :=
    match fields with
    | [] => ValRes.Ok accVals (TyVal.TupTy accTys) state
    | f :: rest =>
      match evalRExpr state f with
      | ValRes.Ok vals ty s' => evalStructFields rest s' (accVals ++ vals) (accTys ++ [ty])
      | ValRes.Err msg => ValRes.Err msg

  -- Eval RExpr
  partial def evalRExpr (state : State) (expr : RExpr) : ValRes :=
    match expr with
    | RExpr.ConstOp n => ValRes.Ok [MemValue.Val n] TyVal.NatTy state
    | RExpr.StructInitOp fields =>
       evalStructFields fields state

    | RExpr.CopyOp p =>
       -- copy-plc
       match resolveDirectPlace state p with
       | (Result.Ok s1, res) =>
         match sb_read s1.ap res.addr res.tag with
         | SBResult.Ok ap2 =>
           let s2 := { s1 with ap := ap2 }
           let vals := readWordSeq s2.mem res.addr (typeSize res.ty)
           ValRes.Ok vals res.ty s2
         | SBResult.Err msg => ValRes.Err msg
       | (Result.Err msg, _) => ValRes.Err msg

    | RExpr.MoveOp p =>
       -- move-place
       match resolveDirectPlace state p with
       | (Result.Ok s1, res) =>
         match sb_move s1.ap res.addr res.tag with
         | SBResult.Ok ap2 =>
           let s2 := { s1 with ap := ap2 }
           let vals := readWordSeq s2.mem res.addr (typeSize res.ty)
           ValRes.Ok vals res.ty s2
         | SBResult.Err msg => ValRes.Err msg
       | (Result.Err msg, _) => ValRes.Err msg

    | RExpr.RefOp kind p =>
      -- ref-place
      match resolveDirectPlace state p with
      | (Result.Ok s1, res) =>
        let (sbRes, newTag) := match kind with
          | RefKind.Mut => sb_ref s1.ap res.addr res.tag RefOpKind.Mut
          | RefKind.Shared => sb_ref s1.ap res.addr res.tag RefOpKind.Shared
          | RefKind.Raw => sb_ref s1.ap res.addr res.tag RefOpKind.Raw
        match sbRes with
        | SBResult.Ok ap2 =>
          let s2 := { s1 with ap := ap2 }
          ValRes.Ok [MemValue.PlaceTag p newTag] TyVal.PTy s2
        | SBResult.Err msg => ValRes.Err msg
      | (Result.Err msg, _) => ValRes.Err msg

    | RExpr.DrefOp p =>
      -- deref-place (Deref on RHS)
      match resolvePlace state (LExpr.DrefOp p) false with
      | (Result.Ok s1, res) =>
         match sb_read s1.ap res.addr res.tag with
         | SBResult.Ok ap2 =>
           let s2 := { s1 with ap := ap2 }
           let vals := readWordSeq s2.mem res.addr (typeSize res.ty)
           ValRes.Ok vals res.ty s2
         | SBResult.Err msg => ValRes.Err msg
      | (Result.Err msg, _) => ValRes.Err msg

    | RExpr.BinaryOp lhs rhs =>
       match evalRExpr state lhs with
       | ValRes.Ok v1 _ s1 =>
         match evalRExpr s1 rhs with
         | ValRes.Ok v2 _ s2 =>
           match (v1, v2) with
           | ([MemValue.Val n1], [MemValue.Val n2]) =>
               ValRes.Ok [MemValue.Val (n1 + n2)] TyVal.NatTy s2
           | _ => ValRes.Err "BinaryOp expects Nat"
         | ValRes.Err msg => ValRes.Err msg
       | ValRes.Err msg => ValRes.Err msg
end

def writeResolvedPlace
  (pc0 : Nat) (state : State) (addr : Word) (tag : Tag) (vals : List MemValue) : Result :=
  match sb_use_mb state.ap addr tag with
  | SBResult.Ok ap' =>
    let mem' := writeWordSeq state.mem addr vals
    let s' := { state with ap := ap', mem := mem', pc := pc0 + 1 }
    Result.Ok s'
  | SBResult.Err msg => Result.Err msg

def allocateBaseAndWrite
  (pc0 : Nat) (state : State) (base : Word) (ty : TyVal) (vals : List MemValue) : Result :=
  let (addr, mem') := allocate state.mem (typeSize ty)
  let (sbRes, tag) := sb_own state.ap addr
  match sbRes with
  | SBResult.Ok ap' =>
    let env' := state.env.insert base (addr, ty, tag)
    match sb_use_mb ap' addr tag with
    | SBResult.Ok ap'' =>
      let mem'' := writeWordSeq mem' addr vals
      let s' := { state with env := env', mem := mem'', ap := ap'', pc := pc0 + 1 }
      Result.Ok s'
    | SBResult.Err msg => Result.Err msg
  | SBResult.Err msg => Result.Err msg

def finishPlaceAssign
  (pc0 : Nat) (state : State) (p : Place) (vals : List MemValue) (ty : TyVal) : Result :=
  match state.env.lookup p.base with
  | some (addr, _, tag) =>
    if p.path == [] then
      writeResolvedPlace pc0 state addr tag vals
    else
      match resolveDirectPlace state p with
      | (Result.Ok s', res) => writeResolvedPlace pc0 s' res.addr res.tag vals
      | (Result.Err msg, _) => Result.Err msg
  | none =>
    if p.path == [] then
      allocateBaseAndWrite pc0 state p.base ty vals
    else
      Result.Err "Cannot allocate sub-path"

def stepAssignConst (state : State) (p : Place) (n : Word) : Result :=
  finishPlaceAssign state.pc state p [MemValue.Val n] TyVal.NatTy

def structConstWords? : List RExpr → Option (List Word)
  | [] => some []
  | RExpr.ConstOp n :: rest =>
      Option.map (List.cons n) (structConstWords? rest)
  | _ => none

def stepAssignStructWords (state : State) (p : Place) (fields : List Word) : Result :=
  finishPlaceAssign state.pc state p (fields.map MemValue.Val)
    (TyVal.TupTy (List.replicate fields.length TyVal.NatTy))

def stepAssignCopy (state : State) (dst src : Place) : Result :=
  if src.path == [] then
    match state.env.lookup src.base with
    | some (srcAddr, srcTy, srcTag) =>
      match sb_read state.ap srcAddr srcTag with
      | SBResult.Ok ap2 =>
        let s2 := { state with ap := ap2 }
        let vals := readWordSeq s2.mem srcAddr (typeSize srcTy)
        finishPlaceAssign state.pc s2 dst vals srcTy
      | SBResult.Err msg => Result.Err msg
    | none => Result.Err s!"Place base {src.base} not found"
  else
    match resolveDirectPlace state src with
    | (Result.Ok s1, srcRes) =>
      match sb_read s1.ap srcRes.addr srcRes.tag with
      | SBResult.Ok ap2 =>
        let s2 := { s1 with ap := ap2 }
        let vals := readWordSeq s2.mem srcRes.addr (typeSize srcRes.ty)
        finishPlaceAssign state.pc s2 dst vals srcRes.ty
      | SBResult.Err msg => Result.Err msg
    | (Result.Err msg, _) => Result.Err msg

def stepAssignGeneric (state : State) (lhs : LExpr) (rhs : RExpr) : Result :=
  match evalRExpr state rhs with
  | ValRes.Ok vals ty s1 =>
    match lhs with
    | LExpr.Place p =>
       finishPlaceAssign state.pc s1 p vals ty
    | LExpr.DrefOp _ =>
       match resolvePlace s1 lhs true with
       | (Result.Ok s2, res) =>
         writeResolvedPlace state.pc s2 res.addr res.tag vals
       | (Result.Err msg, _) => Result.Err msg
  | ValRes.Err msg => Result.Err msg

-- Eval Stmt
def step (state : State) (prog : Prog) : Result :=
  if h : state.pc < prog.length then
    let stmt := prog.get ⟨state.pc, h⟩
    match stmt with
    | Stmt.Halt => Result.Ok state
    | Stmt.Assgn (LExpr.Place p) (RExpr.ConstOp c) => stepAssignConst state p c
    | Stmt.Assgn (LExpr.Place p) (RExpr.StructInitOp fields) =>
        match structConstWords? fields with
        | some words => stepAssignStructWords state p words
        | none => stepAssignGeneric state (LExpr.Place p) (RExpr.StructInitOp fields)
    | Stmt.Assgn (LExpr.Place dst) (RExpr.CopyOp src) => stepAssignCopy state dst src
    | Stmt.Assgn lhs rhs => stepAssignGeneric state lhs rhs
  else Result.Ok state -- PC out of bounds

end obseq.mirlite
