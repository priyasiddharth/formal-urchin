import obseq3.mirlite

/-!
# OSEA-IR — the compiler's target

The target the compiler (`compile.lean`) lowers to: a register machine
with every unit explicit: loads, stores
and allocations carry the value's BYTE LAYOUT (`bytes.BLayout`), and
offsets, lengths, strides and extents are in bytes. Its memory is
`bytes.Mem`, and every access is checked in the order the source
(`mirlite.lean`) checks it: liveness (`bytes.Mem.freed`), bounds,
the Stacked Borrows event, then the bytes (encode/decode at the layout's
leaves). Registers hold value lists, one per leaf. The pair (source
`mirlite.lean`, this target) is what the compiler proof relates.
-/

namespace obseq3.oseair

open obseq3 obseq3.bytes
open obseq3.oseair (Register Val)
open obseq3.mirlite (MemValue)
open obseq3.mirlite (decodeV encodeAt readL writeL freedMsg)
open obseq3.oseair (ofMem)

inductive Rhs
| Load (lay : BLayout) (reg : Register)
| Alloc (lay : BLayout)
| AllocN (lay : BLayout) (n : Nat)
| AllocDyn (lay : BLayout) (lenReg : Register)
-- `len = some n`: retag `n` bytes at `base + offset`; `none`: the pointer's
-- own extent (mirlite's `.refSlice`). `mask`: one bit per BYTE.
| Borrow (kind : RefKind) (prot : Bool) (mask : List Bool) (len : Option Nat)
    (base : Register) (offset : Nat)
-- `k`: the scalar the leaf read through `srcPtr` is decoded at (the byte
-- source's `leafKind` of the place)
| ExposeAddr (k : Scalar) (srcPtr : Register)
| FromExposed (k : Scalar) (srcPtr : Register)
| PtrOffset (k : Scalar) (srcPtr : Register) (deltaBytes : Int)
| BinOp (op : BinOp) (r1 r2 : Register)
| SliceLen (elemSize : Nat) (srcPtr : Register)
| SubSlice (elemSize : Nat) (srcPtr rLo rHi : Register)
deriving Inhabited, Repr, BEq

inductive Instr
| Assgn (reg : Register) (rhs : Rhs)
| RStore (lay : BLayout) (src : Register) (ptr : Register)
| CStore (lay : BLayout) (val : List Val) (ptr : Register)
| Die (reg : Register) (len : Nat)
| Dealloc (ptr : Register)
| SkipIf (discr : Register) (val : Word) (skip : Nat)
| PushProt
| PopProt
| Halt
deriving Inhabited, Repr, BEq

abbrev Prog := Nat → Option Instr

abbrev RegMap := List (Register × List Val)

def RegMap.lookup (r : RegMap) (reg : Register) : Option (List Val) := List.lookup reg r

def RegMap.insert (r : RegMap) (reg : Register) (vals : List Val) : RegMap :=
  (reg, vals) :: r.filter (fun (rg, _) => rg != reg)

structure State (M : PermissionModel) where
  pc : Nat
  reg : RegMap
  mem : bytes.Mem
  perms : M.State

def State.initial (M : PermissionModel) : State M :=
  { pc := 0, reg := [], mem := {}, perms := M.init }

inductive Result (M : PermissionModel)
| Ok (state : State M)
| Err (msg : String)

inductive RhsResult (M : PermissionModel)
| Ok (vals : List Val) (state : State M)
| Err (msg : String)

def allocPtr (M : PermissionModel) (state : State M) (size align : Nat) : RhsResult M :=
  let (base, mem2) := state.mem.allocate size (max 1 align)
  match M.own state.perms base size with
  | .ok (perms2, tag) =>
      RhsResult.Ok [Val.Ptr base 0 size size tag] { state with mem := mem2, perms := perms2 }
  | .error msg => RhsResult.Err msg

/-- One leaf read through the pointer in `reg`: liveness, bounds, SB read,
    decode at `k` — the head of `ExposeAddr`/`FromExposed`/`PtrOffset`,
    as the source's `readCell`. -/
def readCellThrough (M : PermissionModel) (state : State M) (reg : Register) (k : Scalar) :
    Except String (Val × M.State) :=
  match state.reg.lookup reg with
  | some [Val.Ptr base offset _ size tag] =>
      let addr := base + offset
      if state.mem.isFreed base then .error freedMsg
      else if addr + k.size > base + size then .error "OOB"
      else
        match M.read state.perms addr k.size tag with
        | .error msg => .error msg
        | .ok perms2 => .ok (ofMem (decodeV k (state.mem.read addr k.size)), perms2)
  | _ => .error "expects a pointer register"

def evalRhs (M : PermissionModel) (state : State M) (rhs : Rhs) : RhsResult M :=
  match rhs with
  | .Load lay reg =>
     match state.reg.lookup reg with
     | some [Val.Ptr base offset _ size tag] =>
       let addr := base + offset
       if state.mem.isFreed base then RhsResult.Err freedMsg
       else if addr + lay.size > base + size then RhsResult.Err "OOB"
       else
         match M.read state.perms addr lay.size tag with
         | .ok perms2 =>
           let vals := (readL state.mem addr lay).map ofMem
           if vals.any (fun v => v == Val.Undef) then RhsResult.Err "read of uninitialized memory"
           else RhsResult.Ok vals { state with perms := perms2 }
         | .error msg => RhsResult.Err msg
     | _ => RhsResult.Err "Load expects Ptr"
  | .Alloc lay => allocPtr M state lay.size lay.align
  | .AllocN lay n => allocPtr M state (n * lay.size) lay.align
  | .AllocDyn lay lenReg =>
     match state.reg.lookup lenReg with
     | some [Val.Dat n] => allocPtr M state (n * lay.size) lay.align
     | _ => RhsResult.Err "AllocDyn expects a concrete word"
  | .ExposeAddr k srcPtr =>
     match readCellThrough M state srcPtr k with
     | .error msg => RhsResult.Err msg
     | .ok (Val.Ptr pBase pOff _ _ pTag, perms2) =>
         RhsResult.Ok [Val.Dat (pBase + pOff)] { state with perms := M.expose perms2 pTag }
     | .ok _ => RhsResult.Err "ptr-to-int cast of a non-pointer value"
  | .FromExposed k srcPtr =>
     match readCellThrough M state srcPtr k with
     | .error msg => RhsResult.Err msg
     | .ok (Val.Dat n, perms2) =>
         let (rBase, rSize) := (state.mem.allocOf n).getD (n, 0)
         let rOff := n - rBase
         RhsResult.Ok [Val.Ptr rBase rOff (rSize - rOff) rSize wildcardTag]
           { state with perms := perms2 }
     | .ok _ => RhsResult.Err "int-to-ptr cast of a non-integer value"
  | .PtrOffset k srcPtr deltaBytes =>
     match readCellThrough M state srcPtr k with
     | .error msg => RhsResult.Err msg
     | .ok (Val.Ptr pBase pOff pExt pSize pTag, perms2) =>
         let newOff : Int := (pOff : Int) + deltaBytes
         if newOff < 0 then RhsResult.Err "pointer offset before the allocation base"
         else RhsResult.Ok [Val.Ptr pBase newOff.toNat pExt pSize pTag]
                { state with perms := perms2 }
     | .ok _ => RhsResult.Err "pointer offset of a non-pointer value"
  | .SliceLen esz r =>
     match state.reg.lookup r with
     | some [Val.Ptr _ _ extent _ _] => RhsResult.Ok [Val.Dat (extent / esz)] state
     | _ => RhsResult.Err "SliceLen expects a pointer value"
  | .SubSlice esz rp rLo rHi =>
     match state.reg.lookup rp, state.reg.lookup rLo, state.reg.lookup rHi with
     | some [Val.Ptr base offset extent size tag], some [Val.Dat l], some [Val.Dat h] =>
         if h < l || h * esz > extent then RhsResult.Err "sub-slice range out of bounds"
         else RhsResult.Ok [Val.Ptr base (offset + l * esz) ((h - l) * esz) size tag] state
     | _, _, _ => RhsResult.Err "SubSlice expects a pointer and two words"
  | .BinOp op r1 r2 =>
     match state.reg.lookup r1, state.reg.lookup r2 with
     | some [Val.Dat x], some [Val.Dat y] =>
         match binOpUB op x y with
         | some e => RhsResult.Err e
         | none => RhsResult.Ok [Val.Dat (evalBinOp op x y)] state
     | _, _ => RhsResult.Err "BinOp expects two concrete words"
  | .Borrow kind prot mask len baseReg offset =>
     match state.reg.lookup baseReg with
     | some [Val.Ptr base baseOff extent size tag] =>
       let addr := base + baseOff + offset
       match len with
       | some n =>
         -- a zero-byte retag needs no live, in-bounds memory (as the source)
         if n != 0 && state.mem.isFreed base then RhsResult.Err freedMsg
         else if n != 0 && addr + n > base + size then RhsResult.Err "OOB"
         else
           match M.ref state.perms addr n tag kind prot mask with
           | .ok (perms2, newTag) =>
             RhsResult.Ok [Val.Ptr base (baseOff + offset) n size newTag]
               { state with perms := perms2 }
           | .error msg => RhsResult.Err msg
       | none =>
         if state.mem.isFreed base then RhsResult.Err freedMsg else
         match M.ref state.perms addr extent tag kind prot mask with
         | .ok (perms2, newTag) =>
           RhsResult.Ok [Val.Ptr base (baseOff + offset) extent size newTag]
             { state with perms := perms2 }
         | .error msg => RhsResult.Err msg
     | _ => RhsResult.Err "Borrow expects Ptr"

/-- A typed store of `vals` at layout `lay` through the pointer in `ptr`:
    liveness, bounds, the SB write over the value's bytes, the encoded
    leaves (padding uninit) — the source's `writeResolvedPlace`. -/
def writeThroughPtr (M : PermissionModel) (state : State M) (ptr : Register)
    (lay : BLayout) (vals : List Val) (invalidMsg : String) : Result M :=
  match state.reg.lookup ptr with
  | some [Val.Ptr base offset _ size tag] =>
     let addr := base + offset
     if state.mem.isFreed base then Result.Err freedMsg
     else if addr + lay.size > base + size then Result.Err "write out of bounds"
     else
       match M.useMut state.perms addr lay.size tag with
       | .ok perms2 =>
          match writeL state.mem addr lay (vals.map oseair.Val.toMem) with
          | .ok mem2 => Result.Ok { state with perms := perms2, mem := mem2, pc := state.pc + 1 }
          | .error e => Result.Err e
       | .error msg => Result.Err msg
  | _ => Result.Err invalidMsg

def step (M : PermissionModel) (state : State M) (prog : Prog) : Result M :=
  match prog state.pc with
  | none => Result.Ok state
  | some instr => match instr with
    | .Halt => Result.Ok state
    | .Assgn reg rhs =>
      match evalRhs M state rhs with
      | RhsResult.Ok vals s1 => Result.Ok { s1 with reg := s1.reg.insert reg vals, pc := state.pc + 1 }
      | RhsResult.Err msg => Result.Err msg
    | .RStore lay src ptr =>
      match state.reg.lookup src with
      | some vals => writeThroughPtr M state ptr lay vals "RStore Invalid Regs"
      | none => Result.Err "RStore Invalid Regs"
    | .CStore lay vals ptr => writeThroughPtr M state ptr lay vals "CStore Invalid Ptr"
    | .Die reg len =>
       match state.reg.lookup reg with
       | some [Val.Ptr base offset _ _ tag] =>
          match M.die state.perms (base + offset) len tag with
          | .ok perms2 => Result.Ok { state with perms := perms2, pc := state.pc + 1 }
          | .error msg => Result.Err msg
       | _ => Result.Err "Die expects Ptr"
    | .Dealloc ptr =>
       match state.reg.lookup ptr with
       | some [Val.Ptr base offset _ size tag] =>
          if offset != 0 then
            Result.Err "deallocation of a pointer that is not the beginning of its allocation"
          else
            match M.dealloc state.perms base size tag with
            | .ok perms2 =>
              let mem := state.mem.write base (List.replicate size .uninit)
              Result.Ok { state with perms := perms2, mem := { mem with freed := base :: mem.freed },
                                     pc := state.pc + 1 }
            | .error msg => Result.Err msg
       | _ => Result.Err "Dealloc expects Ptr"
    | .SkipIf discr val skip =>
       match state.reg.lookup discr with
       | some [Val.Dat v] =>
          if v == val then Result.Ok { state with pc := state.pc + 1 }
          else Result.Ok { state with pc := state.pc + 1 + skip }
       | _ => Result.Err "SkipIf expects a concrete word"
    | .PushProt => Result.Ok { state with perms := M.pushFrame state.perms, pc := state.pc + 1 }
    | .PopProt =>
       match M.popFrame state.perms with
       | .ok perms2 => Result.Ok { state with perms := perms2, pc := state.pc + 1 }
       | .error msg => Result.Err msg

def runN (M : PermissionModel) : Nat → State M → Prog → Result M
  | 0, state, _ => Result.Ok state
  | n + 1, state, prog =>
      match step M state prog with
      | Result.Ok state' => runN M n state' prog
      | Result.Err msg => Result.Err msg

end obseq3.oseair
