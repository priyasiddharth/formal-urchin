import obseq2.types
import obseq2.allocator
import obseq2.runtime

namespace obseq2.oseair

open obseq2 (Word Tag TyVal typeSize AccessPerms sb_read sb_own sb_ref sb_use_mb sb_die)

inductive Register
| R (idx : Nat)
deriving Repr, Inhabited, DecidableEq, BEq

inductive Val
| Undef
| Dat (value : Word)
| Ptr (base : Word) (offset : Word) (size : Word) (tag : Tag)
deriving Repr, BEq, Inhabited

abbrev RegMap := List (Register × (TyVal × List Val))

def RegMap.lookup (r : RegMap) (reg : Register) : Option (TyVal × List Val) :=
  List.lookup reg r

def RegMap.insert (r : RegMap) (reg : Register) (val : TyVal × List Val) : RegMap :=
  (reg, val) :: r.filter (fun (rg, _) => rg != reg)

abbrev MemMap := List (Word × Val)

structure Mem where
  mMap : MemMap
  addrStart : Word
deriving Repr, Inhabited

namespace Mem

def find? (m : Mem) (addr : Word) : Option Val :=
  List.lookup addr m.mMap

def write (m : Mem) (addr : Word) (v : Val) : Mem :=
  { m with mMap := (addr, v) :: m.mMap.filter (fun (a, _) => a != addr) }

end Mem

def readWordSeq (m : Mem) (addr : Word) (sz : Nat) : List Val :=
  match sz with
  | 0 => []
  | n + 1 =>
    match m.find? addr with
    | some v => v :: readWordSeq m (addr + 1) n
    | none => Val.Undef :: readWordSeq m (addr + 1) n

def writeWordSeq (m : Mem) (addr : Word) (vals : List Val) : Mem :=
  match vals with
  | [] => m
  | v :: vs => writeWordSeq (m.write addr v) (addr + 1) vs

def allocate (m : Mem) (sz : Nat) : Word × Mem :=
  (m.addrStart, { m with addrStart := m.addrStart + sz })

structure AllocatorSpec extends obseq2.AllocatorSpec Mem where
  alloc_mMap : ∀ m sz, (alloc m sz).2.mMap = m.mMap

structure AllocatorProofSpec extends toRuntimeAllocator : AllocatorSpec where
  alloc_fresh : ∀ m sz i, i < sz →
    Mem.find? m (((toRuntimeAllocator.alloc) m sz).1 + i) = none

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

theorem AllocatorProofSpec.alloc_fresh_eq
  (A : AllocatorProofSpec)
  (m : Mem)
  (sz : Nat)
  (i : Nat)
  (h_lt : i < sz) :
  Mem.find? m ((((AllocatorProofSpec.toRuntimeAllocator A).alloc) m sz).1 + i) = none := by
  exact A.alloc_fresh m sz i h_lt

inductive Rhs
| Load (ty : TyVal) (reg : Register)
| Alloc (ty : TyVal)
| BorOffset (base : Register) (offset : Word)
| MutBorOffset (base : Register) (offset : Word)
| CopyOffset (base : Register) (offset : Word)
| BinOp (lhs : Register) (rhs : Register)
deriving Repr, Inhabited

inductive Instr
| Assgn (reg : Register) (rhs : Rhs)
| RStore (ty : TyVal) (src : Register) (ptr : Register)
| CStore (ty : TyVal) (val : List Val) (ptr : Register)
| Memcpy (dst : Register) (src : Register) (ty : TyVal)
| Die (reg : Register)
| Halt
deriving Repr, Inhabited

abbrev Prog := List Instr

structure State where
  pc : Nat
  reg : RegMap
  mem : Mem
  ap : AccessPerms
deriving Repr, Inhabited

inductive Result
| Ok (state : State)
| Err (msg : String)
deriving Repr, Inhabited

inductive RhsResult
| Ok (vals : List Val) (ty : TyVal) (state : State)
| Err (msg : String)
deriving Repr, Inhabited

def evalRhsWith (A : AllocatorSpec) (state : State) (rhs : Rhs) : RhsResult :=
  match rhs with
  | Rhs.Load ty reg =>
     match state.reg.lookup reg with
     | some (_, [Val.Ptr base offset size tag]) =>
       let addr := base + offset
       if addr < base || addr >= base + size then RhsResult.Err "OOB"
       else
         match sb_read state.ap addr tag with
         | obseq.SBResult.Ok ap2 =>
           let s2 := { state with ap := ap2 }
           let vals := readWordSeq s2.mem addr (typeSize ty)
           RhsResult.Ok vals ty s2
         | obseq.SBResult.Err msg => RhsResult.Err msg
     | _ => RhsResult.Err "Load expects Ptr"

  | Rhs.Alloc ty =>
     let size := typeSize ty
     let (base, mem2) := A.alloc state.mem size
     let (sbRes, tag) := sb_own state.ap base
     match sbRes with
     | obseq.SBResult.Ok ap2 =>
       let s2 := { state with mem := mem2, ap := ap2 }
       RhsResult.Ok [Val.Ptr base 0 size tag] obseq.TyVal.PTy s2
     | obseq.SBResult.Err msg => RhsResult.Err msg

  | Rhs.BorOffset baseReg offset =>
     match state.reg.lookup baseReg with
     | some (_, [Val.Ptr base baseOff size tag]) =>
       let addr := base + baseOff + offset
       if addr >= base + size then RhsResult.Err "OOB"
       else
           match sb_ref state.ap addr tag obseq.RefOpKind.Shared with
           | (obseq.SBResult.Ok ap2, newTag) =>
             let s2 := { state with ap := ap2 }
             RhsResult.Ok [Val.Ptr base (baseOff + offset) size newTag] obseq.TyVal.PTy s2
           | (obseq.SBResult.Err msg, _) => RhsResult.Err msg
     | _ => RhsResult.Err "BorOffset expects Ptr"

  | Rhs.MutBorOffset baseReg offset =>
     match state.reg.lookup baseReg with
     | some (_, [Val.Ptr base baseOff size tag]) =>
       let addr := base + baseOff + offset
       if addr >= base + size then RhsResult.Err "OOB"
       else
           match sb_ref state.ap addr tag obseq.RefOpKind.Mut with
           | (obseq.SBResult.Ok ap2, newTag) =>
             let s2 := { state with ap := ap2 }
             RhsResult.Ok [Val.Ptr base (baseOff + offset) size newTag] obseq.TyVal.PTy s2
           | (obseq.SBResult.Err msg, _) => RhsResult.Err msg
     | _ => RhsResult.Err "MutBorOffset expects Ptr"

  | Rhs.CopyOffset baseReg offset =>
     match state.reg.lookup baseReg with
     | some (_, [Val.Ptr base baseOff size tag]) =>
       let addr := base + baseOff + offset
       if addr >= base + size then RhsResult.Err "OOB"
       else
           match sb_ref state.ap addr tag obseq.RefOpKind.Raw with
           | (obseq.SBResult.Ok ap2, newTag) =>
             let s2 := { state with ap := ap2 }
             RhsResult.Ok [Val.Ptr base (baseOff + offset) size newTag] obseq.TyVal.PTy s2
           | (obseq.SBResult.Err msg, _) => RhsResult.Err msg
     | _ => RhsResult.Err "CopyOffset expects Ptr"

  | Rhs.BinOp lhs rhs =>
     match state.reg.lookup lhs, state.reg.lookup rhs with
     | some (_, [Val.Dat v1]), some (_, [Val.Dat v2]) =>
      RhsResult.Ok [Val.Dat (v1 + v2)] obseq.TyVal.NatTy state
     | _, _ => RhsResult.Err "BinOp expects Nat"

def evalRhs : State → Rhs → RhsResult :=
  evalRhsWith bumpAllocator

def writeThroughPtr (state : State) (ptr : Register) (vals : List Val) (invalidMsg : String) : Result :=
  match state.reg.lookup ptr with
  | some (_, [Val.Ptr base offset size tag]) =>
     let addr := base + offset
     if addr >= base + size then Result.Err "OOB"
     else
       match sb_use_mb state.ap addr tag with
       | obseq.SBResult.Ok ap2 =>
          let mem2 := writeWordSeq state.mem addr vals
          Result.Ok { state with ap := ap2, mem := mem2, pc := state.pc + 1 }
       | obseq.SBResult.Err msg => Result.Err msg
  | _ => Result.Err invalidMsg

def stepWith (A : AllocatorSpec) (state : State) (prog : Prog) : Result :=
  if h : state.pc < prog.length then
    let instr := prog.get ⟨state.pc, h⟩
    match instr with
    | Instr.Halt => Result.Ok state
    | Instr.Assgn reg rhs =>
      match evalRhsWith A state rhs with
      | RhsResult.Ok vals ty s1 =>
        let reg2 := s1.reg.insert reg (ty, vals)
        Result.Ok { s1 with reg := reg2, pc := state.pc + 1 }
      | RhsResult.Err msg => Result.Err msg
    | Instr.RStore _ty src ptr =>
      match state.reg.lookup src, state.reg.lookup ptr with
      | some (_, vals), some _ =>
         writeThroughPtr state ptr vals "RStore Invalid Regs"
      | _, _ => Result.Err "RStore Invalid Regs"
    | Instr.CStore _ty vals ptr =>
      writeThroughPtr state ptr vals "CStore Invalid Ptr"
    | Instr.Die reg =>
       match state.reg.lookup reg with
       | some (_, [Val.Ptr base offset _ tag]) =>
          match sb_die state.ap (base + offset) tag with
          | obseq.SBResult.Ok ap2 =>
            Result.Ok { state with ap := ap2, pc := state.pc + 1 }
          | obseq.SBResult.Err msg => Result.Err msg
       | _ => Result.Err "Die expects Ptr"
    | Instr.Memcpy dst src ty =>
       match state.reg.lookup dst, state.reg.lookup src with
       | some (_, [Val.Ptr dBase dOff dSize dTag]), some (_, [Val.Ptr sBase sOff sSize sTag]) =>
          let dAddr := dBase + dOff
          let sAddr := sBase + sOff
          let sz := typeSize ty
          if dAddr + sz > dBase + dSize || sAddr + sz > sBase + sSize then Result.Err "OOB"
          else
            match sb_read state.ap sAddr sTag with
            | obseq.SBResult.Ok ap2 =>
              match sb_use_mb ap2 dAddr dTag with
              | obseq.SBResult.Ok ap3 =>
                  let vals := readWordSeq state.mem sAddr sz
                  let mem2 := writeWordSeq state.mem dAddr vals
                  Result.Ok { state with ap := ap3, mem := mem2, pc := state.pc + 1 }
              | obseq.SBResult.Err msg => Result.Err msg
            | obseq.SBResult.Err msg => Result.Err msg
       | _, _ => Result.Err "Memcpy invalid regs"
  else Result.Ok state

def step : State → Prog → Result :=
  stepWith bumpAllocator

def runNWith (A : AllocatorSpec) : Nat → State → Prog → Result
  | 0, state, _prog => Result.Ok state
  | n + 1, state, prog =>
      match stepWith A state prog with
      | Result.Ok state' => runNWith A n state' prog
      | Result.Err msg => Result.Err msg

def runN : Nat → State → Prog → Result :=
  runNWith bumpAllocator

@[simp] theorem runNWith_zero
  (A : AllocatorSpec)
  (state : State)
  (prog : Prog) :
  runNWith A 0 state prog = Result.Ok state := rfl

@[simp] theorem runNWith_succ
  (A : AllocatorSpec)
  (n : Nat)
  (state : State)
  (prog : Prog) :
  runNWith A (n + 1) state prog =
    match stepWith A state prog with
    | Result.Ok state' => runNWith A n state' prog
    | Result.Err msg => Result.Err msg := rfl

@[simp] theorem runN_zero
  (state : State)
  (prog : Prog) :
  runN 0 state prog = Result.Ok state := rfl

@[simp] theorem runN_succ
  (n : Nat)
  (state : State)
  (prog : Prog) :
  runN (n + 1) state prog =
    match step state prog with
    | Result.Ok state' => runN n state' prog
    | Result.Err msg => Result.Err msg := rfl

end obseq2.oseair
