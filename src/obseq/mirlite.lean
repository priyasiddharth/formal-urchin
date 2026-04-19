import obseq.types
import obseq.allocator

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

structure AllocatorSpec extends obseq.AllocatorSpec Mem where
  alloc_mMap : ∀ m sz, (alloc m sz).2.mMap = m.mMap

def bumpAllocator : AllocatorSpec where
  alloc := allocate
  alloc_mMap := by
    intro m sz
    rfl

theorem AllocatorSpec.alloc_mMap_eq
  (A : AllocatorSpec)
  (m : Mem)
  (sz : Nat) :
  (A.alloc m sz).2.mMap = m.mMap := by
  exact A.alloc_mMap m sz

-- Place Resolution Result
structure PlaceRes where
  addr : Word
  tag : Tag
  ty : TyVal
  state : State
deriving Repr, Inhabited

def lExprFuel : LExpr → Nat
  | LExpr.Place _ => 0
  | LExpr.DrefOp _ => 1

mutual
  def rExprFuel : RExpr → Nat
    | RExpr.ConstOp _ => 1
    | RExpr.CopyOp _ => 1
    | RExpr.MoveOp _ => 1
    | RExpr.RefOp _ _ => 1
    | RExpr.DrefOp _ => 1
    | RExpr.StructInitOp fields => rExprListFuel fields + 1
    | RExpr.BinaryOp lhs rhs => rExprFuel lhs + rExprFuel rhs + 1

  def rExprListFuel : List RExpr → Nat
    | [] => 0
    | expr :: rest => rExprFuel expr + rExprListFuel rest + 1
end

@[simp] theorem rExprFuel_binary (lhs rhs : RExpr) :
    rExprFuel (RExpr.BinaryOp lhs rhs) = rExprFuel lhs + rExprFuel rhs + 1 := rfl

@[simp] theorem rExprFuel_struct (fields : List RExpr) :
    rExprFuel (RExpr.StructInitOp fields) = rExprListFuel fields + 1 := rfl

@[simp] theorem rExprListFuel_cons (expr : RExpr) (rest : List RExpr) :
    rExprListFuel (expr :: rest) = rExprFuel expr + rExprListFuel rest + 1 := rfl

theorem rExprListFuel_lt_cons (expr : RExpr) (rest : List RExpr) :
    rExprListFuel rest < rExprListFuel (expr :: rest) := by
  have h_pos : 0 < rExprFuel expr := by
    cases expr <;> simp [rExprFuel]
  simp [rExprListFuel]
  omega

theorem rExprFuel_lt_listFuel_head (expr : RExpr) (rest : List RExpr) :
    rExprFuel expr < rExprListFuel (expr :: rest) := by
  simp [rExprListFuel]
  omega

theorem rExprListFuel_lt_struct (fields : List RExpr) :
    rExprListFuel fields < rExprFuel (RExpr.StructInitOp fields) := by
  simp [rExprFuel]

theorem rExprFuel_lt_binary_left (lhs rhs : RExpr) :
    rExprFuel lhs < rExprFuel (RExpr.BinaryOp lhs rhs) := by
  have h_pos : 0 < rExprFuel rhs := by
    cases rhs <;> simp [rExprFuel]
  simp [rExprFuel]
  omega

theorem rExprFuel_lt_binary_right (lhs rhs : RExpr) :
    rExprFuel rhs < rExprFuel (RExpr.BinaryOp lhs rhs) := by
  have h_pos : 0 < rExprFuel lhs := by
    cases lhs <;> simp [rExprFuel]
  simp [rExprFuel]
  omega

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
def resolvePlace (state : State) : LExpr → Bool → Result × PlaceRes
  | LExpr.Place p, _ =>
      resolveDirectPlace state p
  | LExpr.DrefOp p, _ =>
      -- dref-plc-resolv
      match resolveDirectPlace state p with
      | (Result.Ok s1, res1) =>
          match sb_read s1.ap res1.addr res1.tag with
          | SBResult.Ok ap2 =>
              let s2 := { s1 with ap := ap2 }
              match readWordSeq s2.mem res1.addr 1 with
              | [MemValue.PlaceTag q gq] =>
                  match resolvePlace s2 (LExpr.Place q) false with
                  | (Result.Ok s3, res3) =>
                      (Result.Ok s3, { res3 with tag := gq })
                  | (Result.Err msg, _) => (Result.Err msg, default)
              | _ => (Result.Err "Deref: Memory did not contain a PlaceTag", default)
          | SBResult.Err msg => (Result.Err msg, default)
      | (Result.Err msg, _) => (Result.Err msg, default)
termination_by l _ => lExprFuel l
decreasing_by
  simp [lExprFuel]

mutual
  def evalStructFields : List RExpr → State → List MemValue → List TyVal → ValRes
    | [], state, accVals, accTys =>
        ValRes.Ok accVals (TyVal.TupTy accTys) state
    | f :: rest, state, accVals, accTys =>
        match evalRExpr state f with
        | ValRes.Ok vals ty s' => evalStructFields rest s' (accVals ++ vals) (accTys ++ [ty])
        | ValRes.Err msg => ValRes.Err msg
  termination_by fields => rExprListFuel fields
  decreasing_by
    all_goals
      first
      | exact rExprFuel_lt_listFuel_head f rest
      | exact rExprListFuel_lt_cons f rest

  -- Eval RExpr
  def evalRExpr (state : State) : RExpr → ValRes
    | RExpr.ConstOp n => ValRes.Ok [MemValue.Val n] TyVal.NatTy state
    | RExpr.StructInitOp fields =>
        evalStructFields fields state [] []
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
  termination_by expr => rExprFuel expr
  decreasing_by
    all_goals
      first
      | exact rExprListFuel_lt_struct _
      | exact rExprFuel_lt_listFuel_head _ _
      | exact rExprFuel_lt_binary_left _ _
      | exact rExprFuel_lt_binary_right _ _
end

def writeResolvedPlace
  (pc0 : Nat) (state : State) (addr : Word) (tag : Tag) (vals : List MemValue) : Result :=
  match sb_use_mb state.ap addr tag with
  | SBResult.Ok ap' =>
    let mem' := writeWordSeq state.mem addr vals
    let s' := { state with ap := ap', mem := mem', pc := pc0 + 1 }
    Result.Ok s'
  | SBResult.Err msg => Result.Err msg

def allocateBaseAndWriteWith
  (A : AllocatorSpec)
  (pc0 : Nat) (state : State) (base : Word) (ty : TyVal) (vals : List MemValue) : Result :=
  let (addr, mem') := A.alloc state.mem (typeSize ty)
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

def allocateBaseAndWrite
  (pc0 : Nat) (state : State) (base : Word) (ty : TyVal) (vals : List MemValue) : Result :=
  allocateBaseAndWriteWith bumpAllocator pc0 state base ty vals

def finishPlaceAssignWith
  (A : AllocatorSpec)
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
      allocateBaseAndWriteWith A pc0 state p.base ty vals
    else
      Result.Err "Cannot allocate sub-path"

def finishPlaceAssign
  (pc0 : Nat) (state : State) (p : Place) (vals : List MemValue) (ty : TyVal) : Result :=
  finishPlaceAssignWith bumpAllocator pc0 state p vals ty

def stepAssignConstWith (A : AllocatorSpec) (state : State) (p : Place) (n : Word) : Result :=
  finishPlaceAssignWith A state.pc state p [MemValue.Val n] TyVal.NatTy

def stepAssignConst (state : State) (p : Place) (n : Word) : Result :=
  stepAssignConstWith bumpAllocator state p n

def structConstWords? : List RExpr → Option (List Word)
  | [] => some []
  | RExpr.ConstOp n :: rest =>
      Option.map (List.cons n) (structConstWords? rest)
  | _ => none

def stepAssignStructWordsWith (A : AllocatorSpec) (state : State) (p : Place) (fields : List Word) : Result :=
  finishPlaceAssignWith A state.pc state p (fields.map MemValue.Val)
    (TyVal.TupTy (List.replicate fields.length TyVal.NatTy))

def stepAssignStructWords (state : State) (p : Place) (fields : List Word) : Result :=
  stepAssignStructWordsWith bumpAllocator state p fields

def stepAssignCopyWith (A : AllocatorSpec) (state : State) (dst src : Place) : Result :=
  if src.path == [] then
    match state.env.lookup src.base with
    | some (srcAddr, srcTy, srcTag) =>
      match sb_read state.ap srcAddr srcTag with
      | SBResult.Ok ap2 =>
        let s2 := { state with ap := ap2 }
        let vals := readWordSeq s2.mem srcAddr (typeSize srcTy)
        finishPlaceAssignWith A state.pc s2 dst vals srcTy
      | SBResult.Err msg => Result.Err msg
    | none => Result.Err s!"Place base {src.base} not found"
  else
    match resolveDirectPlace state src with
    | (Result.Ok s1, srcRes) =>
      match sb_read s1.ap srcRes.addr srcRes.tag with
      | SBResult.Ok ap2 =>
        let s2 := { s1 with ap := ap2 }
        let vals := readWordSeq s2.mem srcRes.addr (typeSize srcRes.ty)
        finishPlaceAssignWith A state.pc s2 dst vals srcRes.ty
      | SBResult.Err msg => Result.Err msg
    | (Result.Err msg, _) => Result.Err msg

def stepAssignCopy (state : State) (dst src : Place) : Result :=
  stepAssignCopyWith bumpAllocator state dst src

def stepAssignGenericWith (A : AllocatorSpec) (state : State) (lhs : LExpr) (rhs : RExpr) : Result :=
  match evalRExpr state rhs with
  | ValRes.Ok vals ty s1 =>
    match lhs with
    | LExpr.Place p =>
       finishPlaceAssignWith A state.pc s1 p vals ty
    | LExpr.DrefOp _ =>
       match resolvePlace s1 lhs true with
       | (Result.Ok s2, res) =>
         writeResolvedPlace state.pc s2 res.addr res.tag vals
       | (Result.Err msg, _) => Result.Err msg
  | ValRes.Err msg => Result.Err msg

def stepAssignGeneric (state : State) (lhs : LExpr) (rhs : RExpr) : Result :=
  stepAssignGenericWith bumpAllocator state lhs rhs

-- Eval Stmt
def stepWith (A : AllocatorSpec) (state : State) (prog : Prog) : Result :=
  if h : state.pc < prog.length then
    let stmt := prog.get ⟨state.pc, h⟩
    match stmt with
    | Stmt.Halt => Result.Ok state
    | Stmt.Assgn (LExpr.Place p) (RExpr.ConstOp c) => stepAssignConstWith A state p c
    | Stmt.Assgn (LExpr.Place p) (RExpr.StructInitOp fields) =>
        match structConstWords? fields with
        | some words => stepAssignStructWordsWith A state p words
        | none => stepAssignGenericWith A state (LExpr.Place p) (RExpr.StructInitOp fields)
    | Stmt.Assgn (LExpr.Place dst) (RExpr.CopyOp src) => stepAssignCopyWith A state dst src
    | Stmt.Assgn lhs rhs => stepAssignGenericWith A state lhs rhs
  else Result.Ok state -- PC out of bounds

def step (state : State) (prog : Prog) : Result :=
  stepWith bumpAllocator state prog

def runNWith (A : AllocatorSpec) : Nat → State → Prog → Result
  | 0, state, _ => Result.Ok state
  | n + 1, state, prog =>
      match stepWith A state prog with
      | Result.Ok state' => runNWith A n state' prog
      | Result.Err msg => Result.Err msg

def runN : Nat → State → Prog → Result :=
  runNWith bumpAllocator

end obseq.mirlite
