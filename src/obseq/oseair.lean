import obseq.types
import obseq.sb

namespace obseq.oseair

open obseq

inductive Register
| R (idx : Nat)
deriving Repr, Inhabited

def registerBEq : Register → Register → Bool
| Register.R idx1, Register.R idx2 => idx1 == idx2

instance : BEq Register where
  beq := registerBEq

instance : LawfulBEq Register where
  eq_of_beq := by
    intro a b h
    cases a with
    | R idx1 =>
      cases b with
      | R idx2 =>
        simp [instBEqRegister, registerBEq] at h
        exact congrArg Register.R h
  rfl := by
    intro a
    cases a with
    | R idx =>
      simp [instBEqRegister, registerBEq]

@[simp] theorem registerBEq_self (reg : Register) : (reg == reg) = true := by
  cases reg with
  | R idx =>
    simp [registerBEq]

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

def Mem.find? (m : Mem) (addr : Word) : Option Val :=
  List.lookup addr m.mMap

def Mem.write (m : Mem) (addr : Word) (v : Val) : Mem :=
  { m with mMap := (addr, v) :: m.mMap.filter (fun (a, _) => a != addr) }

-- Helpers
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

-- Syntax
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

-- Interpreter State
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

def evalRhs (state : State) (rhs : Rhs) : RhsResult :=
  match rhs with
  | Rhs.Load ty reg =>
     match state.reg.lookup reg with
     | some (_, [Val.Ptr base offset size tag]) =>
       let addr := base + offset
       if addr < base || addr >= base + size then RhsResult.Err "OOB"
       else
         match sb_read state.ap base tag with -- Read using base tag
         | SBResult.Ok ap2 =>
           let s2 := { state with ap := ap2 }
           let vals := readWordSeq s2.mem addr (typeSize ty)
           RhsResult.Ok vals ty s2
         | SBResult.Err msg => RhsResult.Err msg
     | _ => RhsResult.Err "Load expects Ptr"

  | Rhs.Alloc ty =>
     let size := typeSize ty
     let (base, mem2) := allocate state.mem size
     let (sbRes, tag) := sb_own state.ap base
     match sbRes with
     | SBResult.Ok ap2 =>
       let s2 := { state with mem := mem2, ap := ap2 }
       RhsResult.Ok [Val.Ptr base 0 size tag] TyVal.PTy s2
     | SBResult.Err msg => RhsResult.Err msg

  | Rhs.BorOffset baseReg offset =>
     match state.reg.lookup baseReg with
     | some (_, [Val.Ptr base baseOff size tag]) =>
       let addr := base + baseOff + offset
       if addr >= base + size then RhsResult.Err "OOB"
       else
          match sb_ref state.ap base tag RefOpKind.Shared with
          | (SBResult.Ok ap2, newTag) =>
             let s2 := { state with ap := ap2 }
             RhsResult.Ok [Val.Ptr base (baseOff + offset) size newTag] TyVal.PTy s2
          | (SBResult.Err msg, _) => RhsResult.Err msg
     | _ => RhsResult.Err "BorOffset expects Ptr"

  | Rhs.MutBorOffset baseReg offset =>
     match state.reg.lookup baseReg with
     | some (_, [Val.Ptr base baseOff size tag]) =>
       let addr := base + baseOff + offset
       if addr >= base + size then RhsResult.Err "OOB"
       else
          match sb_ref state.ap base tag RefOpKind.Mut with
          | (SBResult.Ok ap2, newTag) =>
             let s2 := { state with ap := ap2 }
             RhsResult.Ok [Val.Ptr base (baseOff + offset) size newTag] TyVal.PTy s2
          | (SBResult.Err msg, _) => RhsResult.Err msg
     | _ => RhsResult.Err "MutBorOffset expects Ptr"

  | Rhs.CopyOffset baseReg offset =>
     match state.reg.lookup baseReg with
     | some (_, [Val.Ptr base baseOff size tag]) =>
       let addr := base + baseOff + offset
       if addr >= base + size then RhsResult.Err "OOB"
       else
          match sb_ref state.ap base tag RefOpKind.Raw with
          | (SBResult.Ok ap2, newTag) =>
             let s2 := { state with ap := ap2 }
             RhsResult.Ok [Val.Ptr base (baseOff + offset) size newTag] TyVal.PTy s2
          | (SBResult.Err msg, _) => RhsResult.Err msg
     | _ => RhsResult.Err "CopyOffset expects Ptr"

  | Rhs.BinOp lhs rhs =>
     match state.reg.lookup lhs, state.reg.lookup rhs with
     | some (_, [Val.Dat v1]), some (_, [Val.Dat v2]) =>
       RhsResult.Ok [Val.Dat (v1 + v2)] TyVal.NatTy state
     | _, _ => RhsResult.Err "BinOp expects Nat"

def writeThroughPtr (state : State) (ptr : Register) (vals : List Val) (invalidMsg : String) : Result :=
  match state.reg.lookup ptr with
  | some (_, [Val.Ptr base offset size tag]) =>
     let addr := base + offset
     if addr >= base + size then Result.Err "OOB"
     else
       match sb_use_mb state.ap base tag with
       | SBResult.Ok ap2 =>
          let mem2 := writeWordSeq state.mem addr vals
          Result.Ok { state with ap := ap2, mem := mem2, pc := state.pc + 1 }
       | SBResult.Err msg => Result.Err msg
  | _ => Result.Err invalidMsg

def step (state : State) (prog : Prog) : Result :=
  if h : state.pc < prog.length then
    let instr := prog.get ⟨state.pc, h⟩
    match instr with
    | Instr.Halt => Result.Ok state
    | Instr.Assgn reg rhs =>
      match evalRhs state rhs with
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
       | some (_, [Val.Ptr base _ _ tag]) =>
          match sb_die state.ap base tag with
          | SBResult.Ok ap2 =>
            Result.Ok { state with ap := ap2, pc := state.pc + 1 }
          | SBResult.Err msg => Result.Err msg
       | _ => Result.Err "Die expects Ptr"

    | Instr.Memcpy dst src ty =>
       match state.reg.lookup dst, state.reg.lookup src with
       | some (_, [Val.Ptr dBase dOff dSize dTag]), some (_, [Val.Ptr sBase sOff sSize sTag]) =>
          let dAddr := dBase + dOff
          let sAddr := sBase + sOff
          let sz := typeSize ty
          if dAddr + sz > dBase + dSize || sAddr + sz > sBase + sSize then Result.Err "OOB"
          else
            match sb_read state.ap sBase sTag with
            | SBResult.Ok ap2 =>
               match sb_use_mb ap2 dBase dTag with
               | SBResult.Ok ap3 =>
                  let vals := readWordSeq state.mem sAddr sz
                  let mem2 := writeWordSeq state.mem dAddr vals
                  Result.Ok { state with ap := ap3, mem := mem2, pc := state.pc + 1 }
               | SBResult.Err msg => Result.Err msg
            | SBResult.Err msg => Result.Err msg
       | _, _ => Result.Err "Memcpy invalid regs"
  else Result.Ok state

end obseq.oseair
