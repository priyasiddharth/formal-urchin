import interp.accessperm
import interp.units

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
| Ptr (base: Word) (offset : Word) (size : Word) (tag : Word) -- ptr value

def Val.beq : Val → Val → Bool
  | Val.Undef, Val.Undef => true
  | Val.Dat v1, Val.Dat v2 => v1 == v2
  | Val.Ptr b1 o1 s1 t1, Val.Ptr b2 o2 s2 t2 => b1 == b2 && o1 == o2 && s1 == s2 && t1 == t2
  | _, _ => false

instance : BEq Val where
    beq := Val.beq

instance : ToString Val where
  toString
  | .Undef => "⊥"
  | .Dat value => s!"Val({value})"
  | .Ptr base offset size tag => s!"*(B:{base}, O:{offset}, Sz:{size}, {tag})"


instance : Inhabited Val where
  default := Val.Dat 0xDEADBEEF

abbrev RegMap := Lean.AssocList Register (TyVal × (List Val))
def RegMap.beq : RegMap → RegMap → Bool
  | env1, env2 =>
    let l1 := env1.toList
    let l2 := env2.toList
    l1.all (fun (reg, val) => env2.find? reg == some val) &&
    l2.all (fun (reg, val) => env1.find? reg == some val)

instance : BEq RegMap where
  beq := RegMap.beq

instance : ToString RegMap where
  toString regMap :=
    let entries := regMap.toList.map (fun (reg, (ty, rval)) => s!"{reg} -> ({ty}, {rval})")
    String.intercalate "\n" entries

abbrev MemMap := Lean.AssocList Word Val

instance : ToString MemMap where
  toString memMap :=
    let entries := memMap.toList.map (fun (addr, value) => s!"{addr} -> {value}")
    String.intercalate "\n" entries

structure Mem where
  mMap: MemMap
  addrStart: Word
deriving Inhabited
def MemMap.beq : MemMap → MemMap → Bool
  | env1, env2 =>
    let l1 := env1.toList
    let l2 := env2.toList
    l1.all (fun (addr, val) => env2.find? addr == some val) &&
    l2.all (fun (addr, val) => env1.find? addr == some val)

instance : BEq MemMap where
  beq := MemMap.beq

partial def Mem.beq : Mem → Mem → Bool
  | ⟨m1, a1⟩, ⟨m2, a2⟩ =>
    m1 == m2 && a1 == a2

instance : BEq Mem where
  beq := Mem.beq

instance : ToString Mem where
  toString mem := s!"{toString mem.mMap}, addr_start: {mem.addrStart}"

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
| bor_offset (base: Register) (offset: Word)
| mutbor_offset (base: Register) (offset: Word)
| copy_offset (base: Register) (offset: Word)
| binop (lhs: Register) (rhs: Register) -- binary operation + for now

def Rhs.beq : Rhs → Rhs → Bool
  | Rhs.load ty1 reg1, Rhs.load ty2 reg2 => ty1 == ty2 && reg1 == reg2
  | Rhs.alloc ty1, Rhs.alloc ty2 => ty1 == ty2
  | Rhs.bor_offset base1 off1, Rhs.bor_offset base2 off2 => base1 == base2 && off1 == off2
  | Rhs.mutbor_offset base1 off1, Rhs.mutbor_offset base2 off2 => base1 == base2 && off1 == off2
  | Rhs.copy_offset base1 off1, Rhs.copy_offset base2 off2 => base1 == base2 && off1 == off2
  | Rhs.binop lhs1 rhs1, Rhs.binop lhs2 rhs2 => lhs1 == lhs2 && rhs1 == rhs2
  | _, _ => false

instance : BEq Rhs where
  beq := Rhs.beq

inductive Stmt
| assgn (l : Register) (r : Rhs)
| rstore (ty : TyVal) (src: Register) (ptr: Register)
| cstore (ty : TyVal) (src: List Val) (ptr: Register)
| memcpy (dst: Register) (src: Register) (srcTy: TyVal)
| halt

def Stmt.beq : Stmt → Stmt → Bool
  | Stmt.assgn l1 r1, Stmt.assgn l2 r2 => l1 == l2 && r1 == r2
  | Stmt.rstore ty1 src1 ptr1, Stmt.rstore ty2 src2 ptr2 => ty1 == ty2 && src1 == src2 && ptr1 == ptr2
  | Stmt.cstore ty1 src1 ptr1, Stmt.cstore ty2 src2 ptr2 => ty1 == ty2 && src1 == src2 && ptr1 == ptr2
  | Stmt.memcpy dst1 src1 dty1, Stmt.memcpy dst2 src2 dty2 => dst1 == dst2 && src1 == src2 && dty1 == dty2
  | Stmt.halt, Stmt.halt => true
  | _, _ => false

instance : BEq Stmt where
  beq := Stmt.beq

instance : ToString Rhs where
  toString
  | Rhs.load ty reg => s!"load {ty} {reg}"
  | Rhs.alloc ty => s!"alloc {ty}"
  | Rhs.bor_offset base offset => s!"bor_offset {base} {offset}"
  | Rhs.mutbor_offset base offset => s!"mutbor_offset {base} {offset}"
  | Rhs.copy_offset base offset => s!"copy_offset {base} {offset}"
  | Rhs.binop lhs rhs => s!"{lhs} + {rhs}"


inductive RhsResult
| Ok (values : List Val) (ty : TyVal) (mem : Mem)  (ap : accessperm.AccessPerms)
| Err (message : String)

-- change all gep logic into one function that takes a predicate for borrow ok compute
def RhsToValues : Rhs → RegMap → Mem → accessperm.AccessPerms → RhsResult
  | Rhs.load ty reg, regMap, mem, ap =>
    match regMap.find? reg with
      | some (_ty', [Val.Ptr base offset size _tag]) =>
        -- check that ty == ty'
        let addr := base + offset
        if addr < base || addr ≥ base + size then
          RhsResult.Err s!"OOB1: Pointer out of bounds {reg}: addr={addr}, base={base}, size={size}"
        else
          let values := ReadWordSeq mem addr ty
          RhsResult.Ok values ty mem ap
      | _ => RhsResult.Err s!"Register type of {reg} is not pointer."
  | Rhs.alloc ty, _regMap, mem, ap =>
    let size := typeSize ty
    let (base, newMem) := allocate mem size
    let (tag, newAP) := freshTag ap
    RhsResult.Ok [Val.Ptr base 0 /- offset -/ size tag] (TyVal.PTy) newMem newAP
  | Rhs.bor_offset base offset2, regMap, mem, ap =>
    match regMap.find? base with
      | some (_ty, [Val.Ptr baase offset size _tag]) =>
        -- TODO: add borrow logic
        let addr := baase + offset
        let newAddr := addr + offset2
        if newAddr < baase || newAddr ≥ baase + size then
          RhsResult.Err s!"OOB2: Pointer out of bounds {base}: newAddr={newAddr}, base={baase}, size={size}"
        else
          -- freshtag
          let (tag, newAP) := freshTag ap
          RhsResult.Ok [Val.Ptr baase (offset + offset2) size tag] (TyVal.PTy) mem newAP
      | _ => RhsResult.Err s!"Register type of {base} is not pointer."
  | Rhs.mutbor_offset base offset2, regMap, mem, ap =>
    match regMap.find? base with
      | some (_ty, [Val.Ptr base offset size _tag]) =>
        -- TODO: add mutable borrow logic
        let addr := base + offset
        let newAddr := addr + offset2
        if newAddr < base || newAddr ≥ base + size then
          RhsResult.Err s!"OOB3: Pointer out of bounds {base}: newAddr={newAddr}, base={base}, size={size}"
        else
          -- freshtag
          let (tag, newAP) := freshTag ap
          RhsResult.Ok [Val.Ptr base (offset + offset2) size tag] (TyVal.PTy) mem newAP
      | _ => RhsResult.Err s!"Register type of {base} is not pointer."
  | Rhs.copy_offset base offset2, regMap, mem, ap =>
    match regMap.find? base with
      | some (_ty, [Val.Ptr base offset size _tag]) =>
        -- TODO: add copy logic
        let addr := base + offset
        let newAddr := addr + offset2
        if newAddr < base || newAddr ≥ base + size then
          RhsResult.Err s!"Pointer out of bounds {base}: newAddr={newAddr}, base={base}, size={size}"
        else
          -- freshtag
          let (tag, newAP) := freshTag ap
          RhsResult.Ok [Val.Ptr base (offset + offset2) size tag] (TyVal.PTy) mem newAP
      | _ => RhsResult.Err s!"Register type of {base} is not pointer."
  | Rhs.binop lhs rhs, regMap, mem, ap =>
    match regMap.find? lhs, regMap.find? rhs with
      | some (TyVal.NatTy, [Val.Dat v1]), some (TyVal.NatTy, [Val.Dat v2]) =>
        let result := v1 + v2
        RhsResult.Ok [Val.Dat result] TyVal.NatTy mem ap
      | _, _ =>
        match regMap.find? lhs, regMap.find? rhs with
        | some (ty1, _), some (ty2, _) =>
          RhsResult.Err s!"Invalid types for arithmetic operation: lhs has type {ty1}, rhs has type {ty2}"
        | some (ty1, _), none =>
          RhsResult.Err s!"Invalid rhs register {rhs}: lhs has type {ty1}, rhs not found"
        | none, some (ty2, _) =>
          RhsResult.Err s!"Invalid lhs register {lhs}: lhs not found, rhs has type {ty2}"
        | none, none =>
          RhsResult.Err s!"Invalid lhs and rhs registers: {lhs}, {rhs}"

-- Result type for statements
inductive LhsResult
| Ok (R : RegMap) (ap : accessperm.AccessPerms) (mem : Mem)
| Err (message : String)

partial def EvalStmt : Stmt → RegMap → Mem → accessperm.AccessPerms → LhsResult :=
  fun stmt regMap mem ap =>
  match stmt with
  | Stmt.assgn lreg rval =>
    match RhsToValues rval regMap mem ap with
    | RhsResult.Ok val ty newMem newAp =>
      let newRegMap := regMap.insert lreg (ty, val)
      LhsResult.Ok newRegMap newAp newMem
    | RhsResult.Err msg => LhsResult.Err msg
  | Stmt.cstore ty src ptr =>
    match regMap.find? ptr with
    | some (pty, [(Val.Ptr base offset size _tag)]) =>
      let addr := base + offset
      if addr < base || addr ≥ base + size then
        LhsResult.Err s!"OOB4: Pointer out of bounds {ptr}: addr={addr}, base={base}, size={size}"
      else
        let tySize := typeSize ty
        if tySize > size - offset then
          LhsResult.Err s!"Type size {tySize} exceeds available memory: size={size}, addr={addr}, base={base}"
        else
          let newMem := WriteWordSeq mem addr src
          LhsResult.Ok regMap ap newMem
    | _ => LhsResult.Err "Invalid pointer register in cstore"
  | Stmt.rstore ty src ptr =>
    match regMap.find? src, regMap.find? ptr with
    | some (_rhsTy, values), some (_pty, [Val.Ptr base offset size _tag]) =>
      let addr := base + offset
      let tySize := typeSize ty
      if tySize > size - offset then
        LhsResult.Err s!"Type size {tySize} exceeds available memory: size={size}, addr={addr}, base={base}"
      else
        let newMem := WriteWordSeq mem addr values
        LhsResult.Ok regMap ap newMem
    | _, _ => LhsResult.Err "Invalid src or ptr register in rstore"
  | Stmt.memcpy dst src srcTy =>
    match regMap.find? dst, regMap.find? src with
    | some (_ty1, [Val.Ptr base offset size _tag1]), some (_ty2, [Val.Ptr srcbase srcoffset srcsize _tag2]) =>
    let addr := base + offset
    let srcaddr := srcbase + srcoffset
    let tySize := typeSize srcTy
    if tySize > size - offset then
      LhsResult.Err s!"Type size {tySize} exceeds available memory in memcpy: size={size}, addr={addr}, base={base}"
    else if addr < base || addr + tySize > base + size then
      LhsResult.Err s!"OOB5: Destination pointer out of bounds {dst}: addr={addr}, size={size}, base={base}, tySize={tySize}"
    else if srcaddr < srcbase || srcaddr + tySize > srcbase + srcsize then
      LhsResult.Err s!"OOB6: Source pointer out of bounds {src}: srcaddr={srcaddr}, srcsize={srcsize}, srcbase={srcbase}, tySize={tySize}"
    else
      let values := ReadWordSeq mem srcaddr srcTy
      let newMem := WriteWordSeq mem addr values
      LhsResult.Ok regMap ap newMem
    | _, _ => LhsResult.Err "Invalid dst or src register in memcpy"
  | Stmt.halt => LhsResult.Ok regMap ap mem

structure ProgCount where
  bb: Word
  stmt: Word
deriving Inhabited, Repr

abbrev BasicBlock := Word

def ProgCount.beq : ProgCount → ProgCount → Bool
  | ⟨bb1, stmt1⟩, ⟨bb2, stmt2⟩ =>
    bb1 == bb2 && stmt1 == stmt2

instance : BEq ProgCount where
  beq := ProgCount.beq

abbrev Prog := Lean.AssocList BB (List Stmt)

def Prog.beq : Prog → Prog → Bool
  | p1, p2 =>
    let l1 := p1.toList
    let l2 := p2.toList
    l1.all (fun (bb, stmts) => p2.find? bb == some stmts) &&
    l2.all (fun (bb, stmts) => p1.find? bb == some stmts)

instance : BEq Prog where
  beq := Prog.beq

instance : ToString Stmt where
  toString
  | Stmt.assgn l r => s!"{l}={r}"
  | Stmt.rstore ty src ptr => s!"rstore {ty} {src} {ptr}"
  | Stmt.cstore ty src ptr => s!"cstore {ty} {src} {ptr}"
  | Stmt.memcpy dst src dty => s!"memcpy {dst} {src} {dty}"
  | Stmt.halt => "halt"

instance : ToString Prog where
  toString prog :=
    let entries := prog.toList.map (fun (bb, stmts) =>
      let stmtStrs := stmts.map (fun stmt => toString stmt)
      s!"BB {bb}:\n{String.intercalate "\n" stmtStrs}")
    String.intercalate "\n" entries



instance : Inhabited RegMap where
  default := Lean.AssocList.nil

instance : Inhabited Mem where
  default := { mMap := Lean.AssocList.nil, addrStart := 0 }

instance : Inhabited LhsResult where
  default := LhsResult.Err "Default error"

partial def EvalProg : ProgCount → Prog → RegMap → Mem → accessperm.AccessPerms → LhsResult :=
  fun pc prog regMap mem ap =>
    match prog.find? pc.bb with
    | none => LhsResult.Err s!"Basic block {pc.bb} not found"
    | some stmts =>
      if pc.stmt < stmts.length then
        match stmts.get? pc.stmt with
        | some Stmt.halt => LhsResult.Ok regMap ap mem
        | some stmt =>
          match EvalStmt stmt regMap mem ap with
          | LhsResult.Ok newRegMap newAp newMem =>
            -- Increment statement counter
            let newPc := { pc with stmt := pc.stmt + 1 }
            EvalProg newPc prog newRegMap newMem newAp
          | LhsResult.Err msg => LhsResult.Err msg
        | none => LhsResult.Err s!"No statement at pc {pc.stmt}"
      else
        LhsResult.Ok regMap ap mem

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
    stmt_list.get ⟨pc, h⟩ = Stmt.rstore ty reg ptr →
    regMap.find? reg = some (_ty, values) →
    regMap.find? ptr = some (_ty, [Val.Ptr base offset size _tag]) →
    addr = base + offset →
    ReadWordSeq mem addr _ty = values →
    WriteWordSeq mem addr values = newMem →
    -- TODO: change ap
    Eval (bb, pc, prog, regMap, mem, ap)
          (bb, pc + 1, prog, regMap, newMem, ap)

| evalMemcpy : ∀ (bb: BB)  (pc: PC) (prog: Prog) (regMap: RegMap) (mem : Mem) (newMem: Mem),
    prog.find? bb = some stmt_list →
    (h : pc < stmt_list.length) →
    stmt_list.get ⟨pc, h⟩ = Stmt.memcpy dst src srcTy →
    regMap.find? dst = some (_ty1, [Val.Ptr dstbase dstoffset dstsize _tag1]) →
    regMap.find? src = some (_ty2, [Val.Ptr srcbase srcoffset srcsize _tag2]) →
    -- TODO: check that ty1 == ty2 == dty (or sizes are the same)
    -- TODO: change ap
    srcbase + srcoffset = srcAddr →
    dstbase + dstoffset = dstAddr →
    ReadWordSeq mem srcAddr srcTy = values →
    WriteWordSeq mem dstAddr values = newMem →
    Eval (bb, pc, prog, regMap, mem, ap)
          (bb, pc + 1, prog, regMap, newMem, ap)

| evalHalt : ∀ (bb: BB) (pc: PC) (prog: Prog) (regMap: RegMap) (mem : Mem) (ap : accessperm.AccessPerms),
    prog.find? bb = some stmt_list →
    (h : pc < stmt_list.length) →
    stmt_list.get ⟨pc, h⟩ = Stmt.halt →
    Eval (bb, pc, prog, regMap, mem, ap)
          (bb, pc, prog, regMap, mem, ap)

end oseair
