import FormalUrchin.obseq.sb

namespace obseq.mirlite

open obseq

-- Basic Types
structure Place where
  base : Word
  path : List Word -- offsets or indices
deriving Repr, BEq, Inhabited

inductive TyVal
| NatTy
| PTy
| TupTy (tys : List TyVal)
deriving Repr, BEq, Inhabited

instance : ToString TyVal where
  toString t := reprStr t

def typeSize : TyVal → Nat
| TyVal.NatTy => 1
| TyVal.PTy => 1 -- Pointer size
| TyVal.TupTy tys => (tys.map typeSize).foldl (· + ·) 0

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
| ConstOp (val : Word)
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

def list_get_opt {α} : List α → Nat → Option α
| [], _ => none
| a :: _, 0 => some a
| _ :: as, n+1 => list_get_opt as n

-- Helper to compute offset and type for sub-place
def resolvePath (ty : TyVal) (path : List Word) : Option (Nat × TyVal) :=
  match path with
  | [] => some (0, ty)
  | idx :: rest =>
    match ty with
    | TyVal.TupTy tys =>
      match list_get_opt tys idx with
      | some subTy =>
        let preSize := (tys.take idx).foldl (fun acc t => acc + typeSize t) 0
        match resolvePath subTy rest with
        | some (off, finalTy) => some (preSize + off, finalTy)
        | none => none
      | none => none
    | _ => none

-- Place Resolution (plc-resolv, alloc-plc-resolv, dref-plc-resolv)
partial def resolvePlace (state : State) (l : LExpr) (forWrite : Bool) : Result × PlaceRes :=
  match l with
  | LExpr.Place p =>
    match state.env.lookup p.base with
    | some (baseAddr, baseTy, baseTag) =>
      -- plc-resolv
      match resolvePath baseTy p.path with
      | some (offset, ty) =>
        (Result.Ok state, { addr := baseAddr + offset, tag := baseTag, ty := ty, state := state })
      | none => (Result.Err s!"Invalid path {repr p.path} for type {baseTy}", default)
    | none =>
      -- alloc-plc-resolv
      if p.path == [] then
         (Result.Err s!"Place base {p.base} not found", default)
      else
         (Result.Err s!"Place base {p.base} not found", default)

  | LExpr.DrefOp p =>
     -- dref-plc-resolv
     match resolvePlace state (LExpr.Place p) false with
     | (Result.Ok s1, res1) =>
        -- Issue read
        match sb_read_safe s1.ap res1.addr res1.tag with
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

-- Eval RExpr
partial def evalRExpr (state : State) (expr : RExpr) : ValRes :=
  match expr with
  | RExpr.ConstOp n => ValRes.Ok [MemValue.Val n] TyVal.NatTy state
  | RExpr.StructInitOp fields =>
     let rec loop (fs : List RExpr) (s : State) (accVals : List MemValue) (accTys : List TyVal) : ValRes :=
       match fs with
       | [] => ValRes.Ok accVals (TyVal.TupTy accTys) s
       | f :: rest =>
         match evalRExpr s f with
         | ValRes.Ok vals ty s' => loop rest s' (accVals ++ vals) (accTys ++ [ty])
         | ValRes.Err msg => ValRes.Err msg
     loop fields state [] []

  | RExpr.CopyOp p =>
     -- copy-plc
     match resolvePlace state (LExpr.Place p) false with
     | (Result.Ok s1, res) =>
       match sb_read_safe s1.ap res.addr res.tag with
       | SBResult.Ok ap2 =>
         let s2 := { s1 with ap := ap2 }
         let vals := readWordSeq s2.mem res.addr (typeSize res.ty)
         ValRes.Ok vals res.ty s2
       | SBResult.Err msg => ValRes.Err msg
     | (Result.Err msg, _) => ValRes.Err msg

  | RExpr.MoveOp p =>
     -- move-place
     match resolvePlace state (LExpr.Place p) false with
     | (Result.Ok s1, res) =>
       match sb_mv s1.ap res.addr res.tag with
       | SBResult.Ok ap2 =>
         let s2 := { s1 with ap := ap2 }
         let vals := readWordSeq s2.mem res.addr (typeSize res.ty)
         ValRes.Ok vals res.ty s2
       | SBResult.Err msg => ValRes.Err msg
     | (Result.Err msg, _) => ValRes.Err msg

  | RExpr.RefOp kind p =>
    -- ref-place
    match resolvePlace state (LExpr.Place p) false with
    | (Result.Ok s1, res) =>
      let (sbRes, newTag) := match kind with
        | RefKind.Mut => sb_new_mut_ref_kind s1.ap res.addr res.tag obseq.RefKind.MutRef
        | RefKind.Shared => sb_new_ref s1.ap res.addr res.tag
        | RefKind.Raw => sb_new_mut_ref_kind s1.ap res.addr res.tag obseq.RefKind.RawPtr
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
       match sb_read_safe s1.ap res.addr res.tag with
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


-- Eval Stmt
def step (state : State) (prog : Prog) : Result :=
  if h : state.pc < prog.length then
    let stmt := prog.get ⟨state.pc, h⟩
    match stmt with
    | Stmt.Halt => Result.Ok state
    | Stmt.Assgn lhs rhs =>
      -- 1. Eval RHS
      match evalRExpr state rhs with
      | ValRes.Ok vals ty s1 =>
        -- 2. Resolve LHS
        -- Special case: Allocation if LHS is Place(b) and b not in Env
        match lhs with
        | LExpr.Place p =>
           match s1.env.lookup p.base with
           | some _ =>
              match resolvePlace s1 lhs true with
              | (Result.Ok s2, res) =>
                -- 3. Write
                match sb_use_mb s2.ap res.addr res.tag with
                | SBResult.Ok ap3 =>
                   let mem3 := writeWordSeq s2.mem res.addr vals
                   let s3 := { s2 with ap := ap3, mem := mem3, pc := state.pc + 1 }
                   Result.Ok s3
                | SBResult.Err msg => Result.Err msg
              | (Result.Err msg, _) => Result.Err msg
           | none =>
              -- Alloc case
              if p.path == [] then
                let (addr, mem2) := allocate s1.mem (typeSize ty)
                let (sbRes, tag) := sb_own s1.ap addr
                match sbRes with
                | SBResult.Ok ap2 =>
                   let env2 := s1.env.insert p.base (addr, ty, tag)
                   match sb_use_mb ap2 addr tag with
                   | SBResult.Ok ap3 =>
                      let mem3 := writeWordSeq mem2 addr vals
                      let s3 := { s1 with env := env2, mem := mem3, ap := ap3, pc := state.pc + 1 }
                      Result.Ok s3
                   | SBResult.Err msg => Result.Err msg
                | SBResult.Err msg => Result.Err msg
              else Result.Err "Cannot allocate sub-path"
        | LExpr.DrefOp _ =>
           match resolvePlace s1 lhs true with
           | (Result.Ok s2, res) =>
             match sb_use_mb s2.ap res.addr res.tag with
             | SBResult.Ok ap3 =>
                let mem3 := writeWordSeq s2.mem res.addr vals
                let s3 := { s2 with ap := ap3, mem := mem3, pc := state.pc + 1 }
                Result.Ok s3
             | SBResult.Err msg => Result.Err msg
           | (Result.Err msg, _) => Result.Err msg

      | ValRes.Err msg => Result.Err msg
  else Result.Ok state -- PC out of bounds

end obseq.mirlite
