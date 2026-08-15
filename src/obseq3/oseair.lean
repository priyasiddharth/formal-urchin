import obseq3.types
import obseq3.permission

/-!
OSEA-IR v3: the compilation target for obseq3's mirlite. Fork of
`src/obseq2/oseair.lean` with three changes:
- the machine is parameterized by an `obseq3.PermissionModel` (symmetric
  with the mirlite semantics, so a compiler invariant can state
  `s_osea.perms = s_mir.perms` with both sides at `stackedBorrows`);
- every permission call is range-based (`len` cells), matching the v3
  model's per-cell stacks;
- the three v2 borrow forms (`BorOffset`/`MutBorOffset`/`CopyOffset`)
  collapse into one `Rhs.Borrow` carrying the full retag parameters
  (kind, protector flag, freeze mask, length), and `Die` carries the
  static length of the borrow it retires.
-/

namespace obseq3.oseair

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

/-- Same base address as `mirlite.Mem.empty`, so source and target
    machines allocate at identical addresses in identical order. -/
def empty : Mem := { mMap := [], addrStart := 0 }

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

structure AllocatorSpec where
  alloc : Mem → Nat → Word × Mem
  alloc_mMap : ∀ m sz, (alloc m sz).2.mMap = m.mMap

def bumpAllocator : AllocatorSpec where
  alloc := allocate
  alloc_mMap := by
    intro m sz
    rfl

inductive Rhs
| Load (ty : TyVal) (reg : Register)
| Alloc (ty : TyVal)
| Borrow (kind : RefKind) (prot : Bool) (mask : List Bool) (len : Nat)
    (base : Register) (offset : Word)
deriving Repr, Inhabited, BEq

inductive Instr
| Assgn (reg : Register) (rhs : Rhs)
| RStore (ty : TyVal) (src : Register) (ptr : Register)
| CStore (ty : TyVal) (val : List Val) (ptr : Register)
| Memcpy (dst : Register) (src : Register) (ty : TyVal)
| Die (reg : Register) (len : Nat)
| Halt
deriving Repr, Inhabited, BEq

abbrev Prog := Nat → Option Instr

structure State (M : PermissionModel) where
  pc : Nat
  reg : RegMap
  mem : Mem
  perms : M.State

def State.initial (M : PermissionModel) : State M :=
  { pc := 0, reg := [], mem := Mem.empty, perms := M.init }

inductive Result (M : PermissionModel)
| Ok (state : State M)
| Err (msg : String)

inductive RhsResult (M : PermissionModel)
| Ok (vals : List Val) (ty : TyVal) (state : State M)
| Err (msg : String)

def evalRhsWith (M : PermissionModel) (A : AllocatorSpec)
    (state : State M) (rhs : Rhs) : RhsResult M :=
  match rhs with
  | Rhs.Load ty reg =>
     match state.reg.lookup reg with
     | some (_, [Val.Ptr base offset size tag]) =>
       let addr := base + offset
       if addr < base || addr >= base + size then RhsResult.Err "OOB"
       else
         match M.read state.perms addr (typeSize ty) tag with
         | .ok perms2 =>
           let s2 := { state with perms := perms2 }
           let vals := readWordSeq s2.mem addr (typeSize ty)
           RhsResult.Ok vals ty s2
         | .error msg => RhsResult.Err msg
     | _ => RhsResult.Err "Load expects Ptr"

  | Rhs.Alloc ty =>
     let size := typeSize ty
     let (base, mem2) := A.alloc state.mem size
     match M.own state.perms base size with
     | .ok (perms2, tag) =>
       let s2 := { state with mem := mem2, perms := perms2 }
       RhsResult.Ok [Val.Ptr base 0 size tag] obseq.TyVal.PTy s2
     | .error msg => RhsResult.Err msg

  | Rhs.Borrow kind prot mask len baseReg offset =>
     match state.reg.lookup baseReg with
     | some (_, [Val.Ptr base baseOff size tag]) =>
       let addr := base + baseOff + offset
       if addr >= base + size then RhsResult.Err "OOB"
       else
         match M.ref state.perms addr len tag kind prot mask with
         | .ok (perms2, newTag) =>
           let s2 := { state with perms := perms2 }
           RhsResult.Ok [Val.Ptr base (baseOff + offset) size newTag] obseq.TyVal.PTy s2
         | .error msg => RhsResult.Err msg
     | _ => RhsResult.Err "Borrow expects Ptr"

def evalRhs (M : PermissionModel) : State M → Rhs → RhsResult M :=
  evalRhsWith M bumpAllocator

def writeThroughPtr (M : PermissionModel) (state : State M) (ptr : Register)
    (vals : List Val) (invalidMsg : String) : Result M :=
  match state.reg.lookup ptr with
  | some (_, [Val.Ptr base offset size tag]) =>
     let addr := base + offset
     if addr + vals.length > base + size then Result.Err "OOB"
     else
       match M.useMut state.perms addr vals.length tag with
       | .ok perms2 =>
          let mem2 := writeWordSeq state.mem addr vals
          Result.Ok { state with perms := perms2, mem := mem2, pc := state.pc + 1 }
       | .error msg => Result.Err msg
  | _ => Result.Err invalidMsg

def stepWith (M : PermissionModel) (A : AllocatorSpec)
    (state : State M) (prog : Prog) : Result M :=
  match prog state.pc with
  | none => Result.Ok state
  | some instr => match instr with
    | Instr.Halt => Result.Ok state
    | Instr.Assgn reg rhs =>
      match evalRhsWith M A state rhs with
      | RhsResult.Ok vals ty s1 =>
        let reg2 := s1.reg.insert reg (ty, vals)
        Result.Ok { s1 with reg := reg2, pc := state.pc + 1 }
      | RhsResult.Err msg => Result.Err msg
    | Instr.RStore ty src ptr =>
      match state.reg.lookup src, state.reg.lookup ptr with
      | some (srcTy, vals), some _ =>
        if srcTy != ty then Result.Err "RStore type mismatch"
        else writeThroughPtr M state ptr vals "RStore Invalid Regs"
      | _, _ => Result.Err "RStore Invalid Regs"
    | Instr.CStore ty vals ptr =>
      if vals.length != typeSize ty then Result.Err "CStore size mismatch"
      else writeThroughPtr M state ptr vals "CStore Invalid Ptr"
    | Instr.Die reg len =>
       match state.reg.lookup reg with
       | some (_, [Val.Ptr base offset _ tag]) =>
          match M.die state.perms (base + offset) len tag with
          | .ok perms2 =>
            Result.Ok { state with perms := perms2, pc := state.pc + 1 }
          | .error msg => Result.Err msg
       | _ => Result.Err "Die expects Ptr"
    | Instr.Memcpy dst src ty =>
       match state.reg.lookup dst, state.reg.lookup src with
       | some (_, [Val.Ptr dBase dOff dSize dTag]), some (_, [Val.Ptr sBase sOff sSize sTag]) =>
          let dAddr := dBase + dOff
          let sAddr := sBase + sOff
          let sz := typeSize ty
          if dAddr + sz > dBase + dSize || sAddr + sz > sBase + sSize then Result.Err "OOB"
          else
            match M.read state.perms sAddr sz sTag with
            | .ok perms2 =>
              match M.useMut perms2 dAddr sz dTag with
              | .ok perms3 =>
                  let vals := readWordSeq state.mem sAddr sz
                  let mem2 := writeWordSeq state.mem dAddr vals
                  Result.Ok { state with perms := perms3, mem := mem2, pc := state.pc + 1 }
              | .error msg => Result.Err msg
            | .error msg => Result.Err msg
       | _, _ => Result.Err "Memcpy invalid regs"

def step (M : PermissionModel) : State M → Prog → Result M :=
  stepWith M bumpAllocator

def runNWith (M : PermissionModel) (A : AllocatorSpec) : Nat → State M → Prog → Result M
  | 0, state, _prog => Result.Ok state
  | n + 1, state, prog =>
      match stepWith M A state prog with
      | Result.Ok state' =>
          -- `Halt`/off-the-end leave pc unchanged; stop instead of idling
          if state'.pc == state.pc then Result.Ok state'
          else runNWith M A n state' prog
      | Result.Err msg => Result.Err msg

def runN (M : PermissionModel) : Nat → State M → Prog → Result M :=
  runNWith M bumpAllocator

@[simp] theorem runNWith_zero
  (M : PermissionModel)
  (A : AllocatorSpec)
  (state : State M)
  (prog : Prog) :
  runNWith M A 0 state prog = Result.Ok state := rfl

@[simp] theorem runNWith_succ
  (M : PermissionModel)
  (A : AllocatorSpec)
  (n : Nat)
  (state : State M)
  (prog : Prog) :
  runNWith M A (n + 1) state prog =
    match stepWith M A state prog with
    | Result.Ok state' =>
        if state'.pc == state.pc then Result.Ok state'
        else runNWith M A n state' prog
    | Result.Err msg => Result.Err msg := rfl

@[simp] theorem runN_zero
  (M : PermissionModel)
  (state : State M)
  (prog : Prog) :
  runN M 0 state prog = Result.Ok state := rfl

@[simp] theorem runN_succ
  (M : PermissionModel)
  (n : Nat)
  (state : State M)
  (prog : Prog) :
  runN M (n + 1) state prog =
    match step M state prog with
    | Result.Ok state' =>
        if state'.pc == state.pc then Result.Ok state'
        else runN M n state' prog
    | Result.Err msg => Result.Err msg := rfl

end obseq3.oseair
