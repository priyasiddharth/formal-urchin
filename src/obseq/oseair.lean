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
         match sb_read state.ap addr tag with
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
          match sb_ref state.ap addr tag RefOpKind.Shared with
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
          match sb_ref state.ap addr tag RefOpKind.Mut with
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
          match sb_ref state.ap addr tag RefOpKind.Raw with
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
       match sb_use_mb state.ap addr tag with
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
       | some (_, [Val.Ptr base offset _ tag]) =>
          match sb_die state.ap (base + offset) tag with
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
            match sb_read state.ap sAddr sTag with
            | SBResult.Ok ap2 =>
               match sb_use_mb ap2 dAddr dTag with
               | SBResult.Ok ap3 =>
                  let vals := readWordSeq state.mem sAddr sz
                  let mem2 := writeWordSeq state.mem dAddr vals
                  Result.Ok { state with ap := ap3, mem := mem2, pc := state.pc + 1 }
               | SBResult.Err msg => Result.Err msg
            | SBResult.Err msg => Result.Err msg
       | _, _ => Result.Err "Memcpy invalid regs"
  else Result.Ok state

def runN : Nat → State → Prog → Result
  | 0, state, _prog => Result.Ok state
  | n + 1, state, prog =>
      match step state prog with
      | Result.Ok state' => runN n state' prog
      | Result.Err msg => Result.Err msg

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

/-! ## Per-Instruction Step Lemmas -/

theorem step_Assgn_MutBorOffset
  (s : State) (prog : Prog) (tmpReg baseReg : Register) (off : Word)
  (addr baseOff size tag : Word) (ap' : AccessPerms) (newTag : Tag)
  (h_pc : s.pc < prog.length)
  (h_get : prog.get ⟨s.pc, h_pc⟩ = Instr.Assgn tmpReg (Rhs.MutBorOffset baseReg off))
  (h_base_reg : s.reg.lookup baseReg = some (TyVal.PTy, [Val.Ptr addr baseOff size tag]))
  (h_off : addr + baseOff + off < addr + size)
  (h_ref : sb_ref s.ap (addr + baseOff + off) tag RefOpKind.Mut = (SBResult.Ok ap', newTag)) :
  step s prog = Result.Ok {
    reg := s.reg.insert tmpReg (TyVal.PTy, [Val.Ptr addr (baseOff + off) size newTag]),
    ap := ap', mem := s.mem, pc := s.pc + 1 } := by
  unfold step; rw [dif_pos h_pc, h_get]; simp only [evalRhs, h_base_reg]
  have : ¬(addr + baseOff + off ≥ addr + size) := Nat.not_le_of_lt h_off
  simp [this, h_ref]

theorem step_CStore
  (s : State) (prog : Prog) (ty : TyVal) (vals : List Val) (ptrReg : Register)
  (base off size tag : Word) (ap' : AccessPerms)
  (h_pc : s.pc < prog.length)
  (h_get : prog.get ⟨s.pc, h_pc⟩ = Instr.CStore ty vals ptrReg)
  (h_ptr_reg : s.reg.lookup ptrReg = some (TyVal.PTy, [Val.Ptr base off size tag]))
  (h_off : base + off < base + size)
  (h_use : sb_use_mb s.ap (base + off) tag = SBResult.Ok ap') :
  step s prog = Result.Ok {
    reg := s.reg, ap := ap',
    mem := writeWordSeq s.mem (base + off) vals, pc := s.pc + 1 } := by
  unfold step; rw [dif_pos h_pc, h_get]; simp only [writeThroughPtr, h_ptr_reg]
  have : ¬(base + off ≥ base + size) := Nat.not_le_of_lt h_off
  simp [this, h_use]

theorem step_Die
  (s : State) (prog : Prog) (reg : Register)
  (base off size tag : Word) (ap' : AccessPerms)
  (h_pc : s.pc < prog.length)
  (h_get : prog.get ⟨s.pc, h_pc⟩ = Instr.Die reg)
  (h_ptr_reg : s.reg.lookup reg = some (TyVal.PTy, [Val.Ptr base off size tag]))
  (h_die : sb_die s.ap (base + off) tag = SBResult.Ok ap') :
  step s prog = Result.Ok {
    reg := s.reg, ap := ap', mem := s.mem, pc := s.pc + 1 } := by
  unfold step; rw [dif_pos h_pc, h_get]; simp only [h_ptr_reg, h_die]

theorem step_Assgn_Alloc
  (s : State) (prog : Prog) (reg : Register) (ty : TyVal)
  (ap' : AccessPerms) (newTag : Tag) (size : Nat)
  (h_pc : s.pc < prog.length)
  (h_get : prog.get ⟨s.pc, h_pc⟩ = Instr.Assgn reg (Rhs.Alloc ty))
  (h_size : typeSize ty = size)
  (h_alloc : sb_own s.ap s.mem.addrStart = (SBResult.Ok ap', newTag)) :
  step s prog = Result.Ok {
    reg := s.reg.insert reg (TyVal.PTy, [Val.Ptr s.mem.addrStart 0 size newTag]),
    ap := ap', mem := { s.mem with addrStart := s.mem.addrStart + size },
    pc := s.pc + 1 } := by
  unfold step; rw [dif_pos h_pc, h_get]; simp only [evalRhs, h_size, allocate, h_alloc]

theorem step_Memcpy
  (s : State) (prog : Prog) (dstReg srcReg : Register) (ty : TyVal)
  (dBase dOff dSize dTag sBase sOff sSize sTag : Word)
  (apRead apWrite : AccessPerms)
  (h_pc : s.pc < prog.length)
  (h_get : prog.get ⟨s.pc, h_pc⟩ = Instr.Memcpy dstReg srcReg ty)
  (h_dst_reg : s.reg.lookup dstReg = some (TyVal.PTy, [Val.Ptr dBase dOff dSize dTag]))
  (h_src_reg : s.reg.lookup srcReg = some (TyVal.PTy, [Val.Ptr sBase sOff sSize sTag]))
  (h_dst_fit : dBase + dOff + typeSize ty ≤ dBase + dSize)
  (h_src_fit : sBase + sOff + typeSize ty ≤ sBase + sSize)
  (h_read : sb_read s.ap (sBase + sOff) sTag = SBResult.Ok apRead)
  (h_write : sb_use_mb apRead (dBase + dOff) dTag = SBResult.Ok apWrite) :
  step s prog = Result.Ok {
    reg := s.reg, ap := apWrite,
    mem := writeWordSeq s.mem (dBase + dOff) (readWordSeq s.mem (sBase + sOff) (typeSize ty)),
    pc := s.pc + 1 } := by
  unfold step; rw [dif_pos h_pc, h_get]; simp only [h_dst_reg, h_src_reg]
  have : ¬(dBase + dOff + typeSize ty > dBase + dSize) := Nat.not_lt_of_le h_dst_fit
  have : ¬(sBase + sOff + typeSize ty > sBase + sSize) := Nat.not_lt_of_le h_src_fit
  simp [*, h_read, h_write]

end obseq.oseair
