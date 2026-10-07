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
-- `lenB = some n`: retag `n` bytes at `base + offsetB`; `none`: the
-- pointer's own extent (mirlite's `.refSlice`). `mask`: one bit per BYTE.
| Borrow (kind : RefKind) (prot : Bool) (mask : List Bool) (lenB : Option Nat)
    (base : Register) (offsetB : Nat)
-- `k`: the scalar the leaf read through `srcPtr` is decoded at (the byte
-- source's `leafKind` of the place)
| ExposeAddr (k : Scalar) (srcPtr : Register)
| FromExposed (k : Scalar) (srcPtr : Register)
-- `inbounds`: Miri's in-bounds arithmetic (`bytes.Mem.offsetPtr`)
| PtrOffset (k : Scalar) (srcPtr : Register) (deltaB : Int) (inbounds : Bool)
-- the run-time `PtrOffset`: the pointer VALUE in `srcPtr` moved by the word
-- in `idx` (read at `t`) times `elemSizeB` (mirlite's `.ptrOffsetBy`)
| PtrOffsetBy (t : IntTy) (elemSizeB : Nat) (srcPtr idx : Register) (inbounds : Bool)
| BinOp (op : BinOp) (r1 r2 : Register)
-- the pointer VALUE in `reg`, moved by `offsetB` and claiming `extentB`
-- bytes, its tag kept: no event (mirlite's `.addrOf`)
| PlaceAddr (reg : Register) (offsetB extentB : Nat)
| SliceLen (elemSizeB : Nat) (srcPtr : Register)
| SubSlice (elemSizeB : Nat) (srcPtr rLo rHi : Register)
deriving Inhabited, Repr, BEq

inductive Instr
| Assgn (reg : Register) (rhs : Rhs)
| RStore (lay : BLayout) (src : Register) (ptr : Register)
| CStore (lay : BLayout) (val : List Val) (ptr : Register)
| Die (reg : Register) (lenB : Nat)
| Dealloc (ptr : Register)
-- continue iff the word in `discr` is in `vals` exactly when `member`;
-- otherwise the run is stuck (an error): mirlite's `check`
| Check (discr : Register) (vals : List Word) (member : Bool)
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

def allocPtr (M : PermissionModel) (state : State M) (sizeB alignB : Nat) : RhsResult M :=
  let (base, mem2) := state.mem.allocate sizeB (max 1 alignB)
  match M.own state.perms base sizeB with
  | .ok (perms2, tag) =>
      RhsResult.Ok [Val.Ptr base 0 sizeB sizeB tag] { state with mem := mem2, perms := perms2 }
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
      else if addr + k.sizeB > base + size then .error "OOB"
      else
        match M.read state.perms addr k.sizeB tag with
        | .error msg => .error msg
        | .ok perms2 => .ok (ofMem (decodeV k (state.mem.read addr k.sizeB)), perms2)
  | _ => .error "expects a pointer register"

def evalRhs (M : PermissionModel) (state : State M) (rhs : Rhs) : RhsResult M :=
  match rhs with
  | .Load lay reg =>
     match state.reg.lookup reg with
     | some [Val.Ptr base offset _ size tag] =>
       let addr := base + offset
       if state.mem.isFreed base then RhsResult.Err freedMsg
       else if addr + lay.sizeB > base + size then RhsResult.Err "OOB"
       else
         match M.read state.perms addr lay.sizeB tag with
         | .ok perms2 =>
           let vals := (readL state.mem addr lay).map ofMem
           if vals.any (fun v => v == Val.Undef) then RhsResult.Err "read of uninitialized memory"
           else RhsResult.Ok vals { state with perms := perms2 }
         | .error msg => RhsResult.Err msg
     | _ => RhsResult.Err "Load expects Ptr"
  | .Alloc lay => allocPtr M state lay.sizeB lay.alignB
  | .AllocN lay n => allocPtr M state (n * lay.sizeB) lay.alignB
  | .AllocDyn lay lenReg =>
     match state.reg.lookup lenReg with
     | some [Val.Dat n] => allocPtr M state (n * lay.sizeB) lay.alignB
     | _ => RhsResult.Err "AllocDyn expects a concrete word"
  | .ExposeAddr k srcPtr =>
     match readCellThrough M state srcPtr k with
     | .error msg => RhsResult.Err msg
     | .ok (Val.Ptr pBase pOff _ _ pTag, perms2) =>
         match M.expose perms2 pTag with
         | .ok perms3 => RhsResult.Ok [Val.Dat (pBase + pOff)] { state with perms := perms3 }
         | .error msg => RhsResult.Err msg
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
  | .PtrOffset k srcPtr deltaB inbounds =>
     match readCellThrough M state srcPtr k with
     | .error msg => RhsResult.Err msg
     | .ok (Val.Ptr pBase pOff pExt pSize pTag, perms2) =>
         match state.mem.offsetPtr inbounds pBase pOff pSize deltaB with
         | .error msg => RhsResult.Err msg
         | .ok newOff =>
             RhsResult.Ok [Val.Ptr pBase newOff pExt pSize pTag] { state with perms := perms2 }
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
  | .PtrOffsetBy t esz rp ri inbounds =>
     match state.reg.lookup rp, state.reg.lookup ri with
     | some [Val.Ptr base offset extent size tag], some [Val.Dat w] =>
         match state.mem.offsetPtr inbounds base offset size (t.toInt w * (esz : Int)) with
         | .error msg => RhsResult.Err msg
         | .ok newOff => RhsResult.Ok [Val.Ptr base newOff extent size tag] state
     | _, _ => RhsResult.Err "PtrOffsetBy expects a pointer and a word"
  | .PlaceAddr r offB extB =>
     match state.reg.lookup r with
     | some [Val.Ptr base offset _ size tag] =>
         RhsResult.Ok [Val.Ptr base (offset + offB) extB size tag] state
     | _ => RhsResult.Err "PlaceAddr expects a pointer"
  | .BinOp op r1 r2 =>
     match state.reg.lookup r1, state.reg.lookup r2 with
     | some [Val.Dat x], some [Val.Dat y] =>
         match binOpUB op x y with
         | some e => RhsResult.Err e
         | none => RhsResult.Ok [Val.Dat (evalBinOp op x y)] state
     | _, _ => RhsResult.Err "BinOp expects two concrete words"
  | .Borrow kind prot mask lenB baseReg offsetB =>
     match state.reg.lookup baseReg with
     | some [Val.Ptr base baseOff extent size tag] =>
       let addr := base + baseOff + offsetB
       match lenB with
       | some n =>
         -- a zero-byte retag needs no live, in-bounds memory (as the source)
         if n != 0 && state.mem.isFreed base then RhsResult.Err freedMsg
         else if n != 0 && addr + n > base + size then RhsResult.Err "OOB"
         else
           match M.ref state.perms addr n tag kind prot mask with
           | .ok (perms2, newTag) =>
             RhsResult.Ok [Val.Ptr base (baseOff + offsetB) n size newTag]
               { state with perms := perms2 }
           | .error msg => RhsResult.Err msg
       | none =>
         if state.mem.isFreed base then RhsResult.Err freedMsg else
         match M.ref state.perms addr extent tag kind prot mask with
         | .ok (perms2, newTag) =>
           RhsResult.Ok [Val.Ptr base (baseOff + offsetB) extent size newTag]
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
     else if addr + lay.sizeB > base + size then Result.Err "write out of bounds"
     else
       match M.useMut state.perms addr lay.sizeB tag with
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
    | .Die reg lenB =>
       match state.reg.lookup reg with
       | some [Val.Ptr base offset _ _ tag] =>
          match M.die state.perms (base + offset) lenB tag with
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
    | .Check discr vals member =>
       match state.reg.lookup discr with
       | some [Val.Dat v] =>
          if vals.contains v == member then Result.Ok { state with pc := state.pc + 1 }
          else Result.Err "check failed"
       | _ => Result.Err "Check expects a concrete word"
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
