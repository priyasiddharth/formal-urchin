import FormalUrchin.accessperm
import FormalUrchin.units

import Lean.Data.AssocList

namespace oseair

inductive Register
| R (idx : Nat)
| P (idx: Nat)
| M (idx: Nat)

instance : BEq Register where
  beq
  | Register.R idx1, Register.R idx2 => idx1 == idx2
  | Register.P idx1, Register.P idx2 => idx1 == idx2
  | Register.M idx1, Register.M idx2 => idx1 == idx2
  | _, _ => false

instance : ToString Register where
  toString
  | Register.R idx => s!"R{idx}"
  | Register.P idx => s!"P{idx}"
  | Register.M idx => s!"M{idx}"

inductive Val
| Undef
| Dat (value : Word)         -- data value
| Ptr (val : Word) (tag : Word) -- ptr value

instance : ToString Val where
  toString
  | .Undef => "⊥"
  | .Dat value => s!"Val({value})"
  | .Ptr val tag => s!"*({val}, {tag})"


instance : Inhabited Val where
  default := Val.Dat 0xDEADBEEF

abbrev RegMap := Lean.AssocList Register (TyVal × (List Val))

instance : ToString RegMap where
  toString regMap :=
    let entries := regMap.toList.map (fun (reg, (ty, rval)) => s!"{reg} -> ({ty}, {rval})")
    String.intercalate ", " entries

abbrev MemMap := Lean.AssocList Word Val

instance : ToString MemMap where
  toString memMap := toString (memMap.toList.map (fun (addr, value) => s!"({addr} -> {value})"))

def Val.beq : Val → Val → Bool
  | .Dat v1, .Dat v2 => v1 == v2
  | Ptr a1 t1, Ptr a2 t2 => a1 == a2 && t1 == t2
  | _, _ => false

instance : BEq Val where
    beq := Val.beq

structure Mem where
  mMap: MemMap
  addrStart: Word
deriving Inhabited

partial def MemMap.beq : MemMap → MemMap → Bool
  | Lean.AssocList.nil, Lean.AssocList.nil => true
  | Lean.AssocList.cons k1 v1 rest1, Lean.AssocList.cons k2 v2 rest2 =>
    let _ : BEq MemMap := ⟨MemMap.beq⟩
    k1 == k2 && v1 == v2 && rest1 == rest2
  | _, _ => false

instance : BEq MemMap where
  beq := MemMap.beq

partial def Mem.beq : Mem → Mem → Bool
  | ⟨m1, a1⟩, ⟨m2, a2⟩ =>
    m1 == m2 && a1 == a2

instance : BEq Mem where
  beq := Mem.beq

instance : ToString Mem where
  toString mem := s!"{toString mem.mMap}, addr_start: {mem.addrStart}"

-- Helper function for structural recursion
def typeSizeAux : List TyVal → Word → Word
| [], acc => acc
| TyVal.NatTy :: rest, acc | TyVal.PTy :: rest,acc  => typeSizeAux rest (acc + 1)
| TyVal.TupTy nested :: rest, acc =>
    let nestedSize := typeSizeAux nested 0 -- Process the nested tuple first
    typeSizeAux rest (acc + nestedSize)    -- Add its size to the accumulator

-- Main `typeSize` function
def typeSize (ty : TyVal) : Nat :=
  match ty with
  | TyVal.NatTy | TyVal.PTy => 1
  | TyVal.TupTy tys => typeSizeAux tys 0

def ReadWordSeq (mem : Mem) (addr : Word) (ty : TyVal) : List Val :=
  match ty with
  | TyVal.NatTy | TyVal.PTy =>
      -- Single value at the given address
      match mem.mMap.find? addr with
      | some (v) => [v]
      | _ => [] -- Return an empty list if the value is not found
  | TyVal.TupTy tys =>
      -- Process the list of types explicitly
      let rec process (addr : Nat) (tys : List TyVal) : List Val :=
        match tys with
        | [] => []
        | ty :: rest =>
            let values := ReadWordSeq mem addr ty -- Recursive call for individual `ty`
            let newAddr := addr + typeSize ty
            values ++ process newAddr rest    -- Continue with the rest of the types
      process addr tys

def WriteWordSeq (mem : Mem) (addr : Word) (values : List Val) : Mem :=
  let rec process (addr : Nat) (values : List Val) (mMap : MemMap) : MemMap :=
    match values with
    | [] => mMap
    | value :: rest =>
        let newMap := mMap.insert addr value
        process (addr + 1) rest newMap
  let newMap := process addr values mem.mMap
  { mem with mMap := newMap }

def allocate (mem : Mem) (size : Word) : Word × Mem :=
  let newAddrStart := mem.addrStart + size
  let newMem := { mem with addrStart := newAddrStart }
  (mem.addrStart, newMem)

def freshTag (ap : accessperm.AccessPerms) : Tag × accessperm.AccessPerms :=
  let newTag := ap.NextTag
  let newAP := { ap with NextTag := ap.NextTag + 1 }
  (newTag, newAP)

inductive Rhs
| load (ty : TyVal) (reg: Register)
| alloc (ty: TyVal)
| bor_offset (base: Register) (offset: Word) -- ptradd

inductive Stmt
| assgn (l : Register) (r : Rhs)
| store (ty : TyVal) (src: Register) (ptr: Register)
| memcpy (dst: Register) (src: Register) (dstTy: TyVal)
| halt

instance : ToString Rhs where
  toString
  | Rhs.load ty reg => s!"load {ty} {reg}"
  | Rhs.alloc ty => s!"alloc {ty}"
  | Rhs.bor_offset base offset => s!"bor_offset {base} {offset}"


-- Result type for RHS expr to val
inductive RhsResult
| Ok (values : List Val) (ty : TyVal) (mem : Mem)  (ap : accessperm.AccessPerms)
| Err (message : String)

-- Machine config is given by PC × Prog × RegMap × Mem × AccessPerms

def RhsToValues : Rhs → RegMap → Mem → accessperm.AccessPerms → RhsResult
  | Rhs.load ty reg, regMap, mem, ap =>
    match regMap.find? reg with
      | some (_ty', [Val.Ptr addr _tag]) =>
        -- check that ty == ty'
        let values := ReadWordSeq mem addr ty
        RhsResult.Ok values ty mem ap
      | _ => RhsResult.Err s!"Register type of {reg} is not pointer."
  | Rhs.alloc ty, _regMap, mem, ap =>
    let size := typeSize ty
    let (addr, newMem) := allocate mem size
    let (tag, newAP) := freshTag ap
    RhsResult.Ok [Val.Ptr addr tag] ty newMem newAP
  | Rhs.bor_offset base offset, regMap, mem, ap =>
    match regMap.find? base with
      | some (_ty, [Val.Ptr addr _tag]) =>
        -- TODO: add borrow logic
        let newAddr := addr + offset
        -- freshtag
        let (tag, newAP) := freshTag ap
        RhsResult.Ok [Val.Ptr newAddr tag] (TyVal.PTy) mem newAP
      | _ => RhsResult.Err s!"Register type of {base} is not pointer."

abbrev Prog := Lean.AssocList BB (List Stmt)
instance : ToString Stmt where
  toString
  | Stmt.assgn l r => s!"{l}={r}"
  | Stmt.store ty src ptr => s!"store {ty} {src} {ptr}"
  | Stmt.memcpy dst src dty => s!"memcpy {dst} {src} {dty}"
  | Stmt.halt => "halt"

instance : ToString Prog where
  toString prog :=
    let entries := prog.toList.map (fun (bb, stmts) =>
      let stmtStrs := stmts.map (fun stmt => toString stmt)
      s!"BB {bb}:\n{String.intercalate "\n" stmtStrs}")
    String.intercalate "\n" entries

inductive Eval : BB × PC × Prog × RegMap × Mem × accessperm.AccessPerms →
                    BB × PC × Prog × RegMap × Mem × accessperm.AccessPerms → Prop
| evalAssgn :  ∀ (bb: BB)  (pc: PC) (regMap: RegMap) (mem : Mem)
    (ap : accessperm.AccessPerms) (val : List Val) (ty : TyVal)
    (newRegMap: RegMap) (newAp : accessperm.AccessPerms)
    (prog: Prog) (stmt_list: List Stmt),
    prog.find? bb = some stmt_list →
    (h : pc < stmt_list.length) →
    stmt_list.get ⟨pc, h⟩ = Stmt.assgn lreg rval →
    RhsResult.Ok val ty mem newAp = RhsToValues r regMap mem ap →
    regMap.insert lreg (ty, val) = newRegMap →
    Eval (bb, pc, prog, regMap, mem, ap)
        (bb, pc + 1, prog, newRegMap, mem, ap)

| evalStore : ∀ (bb: BB)  (pc: PC) (prog: Prog) (regMap: RegMap) (mem : Mem) (newMem: Mem),
    prog.find? bb = some stmt_list →
    (h : pc < stmt_list.length) →
    stmt_list.get ⟨pc, h⟩ = Stmt.store ty reg ptr →
    regMap.find? reg = some (_ty, values) →
    regMap.find? ptr = some (_ty, [Val.Ptr addr _tag]) →
    WriteWordSeq mem addr values = newMem →
    -- TODO: change ap
    Eval (bb, pc, prog, regMap, mem, ap)
          (bb, pc + 1, prog, regMap, newMem, ap)

| evalMemcpy : ∀ (bb: BB)  (pc: PC) (prog: Prog) (regMap: RegMap) (mem : Mem) (newMem: Mem),
    prog.find? bb = some stmt_list →
    (h : pc < stmt_list.length) →
    stmt_list.get ⟨pc, h⟩ = Stmt.memcpy dst src dty →
    regMap.find? dst = some (_ty1, [Val.Ptr dstAddr _tag1]) →
    regMap.find? src = some (_ty2, [Val.Ptr srcAddr _tag2]) →
    -- TODO: check that ty1 == ty2 == dty (or sizes are the same)
    -- TODO: change ap
    ReadWordSeq mem srcAddr ty = values →
    WriteWordSeq mem dstAddr values = newMem →
    Eval (bb, pc, prog, regMap, mem, ap)
          (bb, pc + 1, prog, regMap, newMem, ap)

| evalHalt : ∀ (bb: BB) (pc: PC) (prog: Prog) (regMap: RegMap) (mem : Mem) (ap : accessperm.AccessPerms),
    prog.find? bb = some stmt_list →
    (h : pc < stmt_list.length) →
    stmt_list.get ⟨pc, h⟩ = Stmt.halt →
    Eval (bb, pc, prog, regMap, mem, ap)
          (bb, pc, prog, regMap, mem, ap)


theorem step_pc_stays_same_iff_halt2
    {bb: BB} {pc : PC} {prog : Prog} {regMap : RegMap} {mem : Mem} {ap : accessperm.AccessPerms}
    (h_bb : prog.find? bb = some stmt_list)
    (h_stmt: pc < stmt_list.length):
      (stmt_list.get ⟨pc, h_stmt⟩ = Stmt.halt) ↔
    Eval (bb, pc, prog, regMap, mem, ap) (bb, pc, prog, regMap, mem, ap) := by
  apply Iff.intro
  { intros h_stmt_eq
    apply Eval.evalHalt
    exact h_bb
    exact h_stmt_eq
  }
  {
    intros h
    cases h
    case mpr.evalHalt s1 s2 s3 s4 =>
     -- Unify stmt_list and s1
      have : stmt_list = s1 := by
        rw [s4] at h_bb
        injection h_bb with h_eq
        symm
        exact h_eq
      subst this
      exact s3
}
end oseair
