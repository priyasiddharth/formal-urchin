import obseq3.oseair
import obseq3.mirlite_bytes

/-!
# OSEA-IR on byte-addressed memory — stage 3

The compilation target, run on `bytes.Mem` — the target-side twin of
`mirlite_bytes.lean`. It executes the SAME compiled programs
(`oseair.Prog`, `compileProg` unchanged) and, like the byte source, reads
the compiler's cell-unit immediates as `B = 8` bytes per cell: `Borrow`
offsets and lengths, `Die` lengths, `PtrOffset` deltas, allocation sizes,
freeze masks (one bit per cell, expanded per byte). Values in registers
stay `List Val`, one per cell; memory encodes and decodes them at their
leaf type exactly as `mirliteB` does (`mirliteB.encodeV`/`decodeV`
through the `Val` ↔ `MemValue` correspondence below).

It runs alongside the cell target: the compiler-correctness proof is
about the cell machines. The checks are differential — the byte source
and the byte target must agree on every compiled test program
(`compile_tests`) and every conformance program (`--bytes`), as the cell
pair does.
-/

namespace obseq3.oseairB

open obseq3 obseq3.bytes
open obseq3.oseair (Register Val Rhs Instr RegMap)
open obseq3.mirlite (MemValue)
open obseq3.mirliteB (B readOne encodeV expandMask)

/-! ## Values ↔ the byte source's values -/

def Val.toMem : Val → MemValue
  | .Undef => .undef
  | .Dat w => .word w
  | .Ptr b o e s t => .ptrVal b o e s t

def ofMem : MemValue → Val
  | .undef => .Undef
  | .word w => .Dat w
  | .ptrVal b o e s t => .Ptr b o e s t

mutual
/-- The scalar type of each cell of a `TyVal` (a word is a `usize`). -/
def tyLeafKinds : TyVal → List Scalar
  | .NatTy => [.int B]
  | .PTy => [.ptr]
  | .TupTy tys => tyLeafKindsList tys

def tyLeafKindsList : List TyVal → List Scalar
  | [] => []
  | t :: ts => tyLeafKinds t ++ tyLeafKindsList ts
end

def readValsT (m : bytes.Mem) (addr : Nat) (ty : TyVal) : List Val :=
  (tyLeafKinds ty).zipIdx.map fun (k, i) => ofMem (readOne m (addr + B * i) k)

def writeValsT (m : bytes.Mem) (addr : Nat) (vals : List Val) : Except String bytes.Mem := do
  let bss ← vals.mapM (encodeV ∘ Val.toMem)
  pure (m.write addr bss.flatten)

/-- A one-cell read at `addr` decoded at scalar `k`. -/
def readOneT (m : bytes.Mem) (addr : Nat) (k : Scalar) : Val := ofMem (readOne m addr k)

/-- Size in bytes of a `TyVal`. -/
def tbytes (ty : TyVal) : Nat := B * typeSize ty

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
  | Ok (vals : List Val) (ty : TyVal) (state : State M)
  | Err (msg : String)

def allocPtr (M : PermissionModel) (state : State M) (size : Nat) : RhsResult M :=
  let (base, mem2) := state.mem.allocate size B
  match M.own state.perms base size with
  | .ok (perms2, tag) =>
      RhsResult.Ok [Val.Ptr base 0 size size tag] obseq.TyVal.PTy
        { state with mem := mem2, perms := perms2 }
  | .error msg => RhsResult.Err msg

/-- Read one pointer-cell through the pointer in `reg` (bounds, SB read),
    decoded at `k`: the shared head of `ExposeAddr`/`FromExposed`/
    `PtrOffset`. -/
def readCellThrough (M : PermissionModel) (state : State M) (reg : Register) (k : Scalar)
    (what : String) : Except String (Val × M.State) :=
  match state.reg.lookup reg with
  | some (_, [Val.Ptr base offset _ size tag]) =>
      let addr := base + offset
      if addr < base || addr + B > base + size then .error "OOB"
      else
        match M.read state.perms addr B tag with
        | .error msg => .error msg
        | .ok perms2 => .ok (readOneT state.mem addr k, perms2)
  | _ => .error s!"{what} expects Ptr"

def evalRhs (M : PermissionModel) (state : State M) (rhs : Rhs) : RhsResult M :=
  match rhs with
  | .Load ty reg =>
     match state.reg.lookup reg with
     | some (_, [Val.Ptr base offset _ size tag]) =>
       let addr := base + offset
       if addr < base || addr + tbytes ty > base + size then RhsResult.Err "OOB"
       else
         match M.read state.perms addr (tbytes ty) tag with
         | .ok perms2 =>
           let vals := readValsT state.mem addr ty
           if vals.any (fun v => v == Val.Undef) then RhsResult.Err "read of uninitialized memory"
           else RhsResult.Ok vals ty { state with perms := perms2 }
         | .error msg => RhsResult.Err msg
     | _ => RhsResult.Err "Load expects Ptr"
  | .Alloc ty => allocPtr M state (tbytes ty)
  | .ExposeAddr srcPtr =>
     match readCellThrough M state srcPtr .ptr "ExposeAddr" with
     | .error msg => RhsResult.Err msg
     | .ok (Val.Ptr pBase pOff _ _ pTag, perms2) =>
         RhsResult.Ok [Val.Dat (pBase + pOff)] obseq.TyVal.NatTy
           { state with perms := M.expose perms2 pTag }
     | .ok _ => RhsResult.Err "ptr-to-int cast of a non-pointer value"
  | .FromExposed srcPtr =>
     match readCellThrough M state srcPtr (.int B) "FromExposed" with
     | .error msg => RhsResult.Err msg
     | .ok (Val.Dat n, perms2) =>
         let (rBase, rSize) := (state.mem.allocOf n).getD (n, 0)
         let rOff := n - rBase
         RhsResult.Ok [Val.Ptr rBase rOff (rSize - rOff) rSize wildcardTag] obseq.TyVal.PTy
           { state with perms := perms2 }
     | .ok _ => RhsResult.Err "int-to-ptr cast of a non-integer value"
  | .PtrOffset srcPtr deltaCells =>
     match readCellThrough M state srcPtr .ptr "PtrOffset" with
     | .error msg => RhsResult.Err msg
     | .ok (Val.Ptr pBase pOff pExt pSize pTag, perms2) =>
         let newOff : Int := (pOff : Int) + (B : Int) * deltaCells
         if newOff < 0 then RhsResult.Err "pointer offset before the allocation base"
         else RhsResult.Ok [Val.Ptr pBase newOff.toNat pExt pSize pTag] obseq.TyVal.PTy
                { state with perms := perms2 }
     | .ok _ => RhsResult.Err "pointer offset of a non-pointer value"
  | .SliceLen ty r =>
     match state.reg.lookup r with
     | some (_, [Val.Ptr _ _ extent _ _]) =>
         RhsResult.Ok [Val.Dat (extent / tbytes ty)] obseq.TyVal.NatTy state
     | _ => RhsResult.Err "SliceLen expects a pointer value"
  | .SubSlice ty rp rLo rHi =>
     match state.reg.lookup rp, state.reg.lookup rLo, state.reg.lookup rHi with
     | some (_, [Val.Ptr base offset extent size tag]),
       some (_, [Val.Dat l]), some (_, [Val.Dat h]) =>
         if h < l || h * tbytes ty > extent then RhsResult.Err "sub-slice range out of bounds"
         else RhsResult.Ok [Val.Ptr base (offset + l * tbytes ty) ((h - l) * tbytes ty) size tag]
                obseq.TyVal.PTy state
     | _, _, _ => RhsResult.Err "SubSlice expects a pointer and two words"
  | .BinOp op r1 r2 =>
     match state.reg.lookup r1, state.reg.lookup r2 with
     | some (_, [Val.Dat x]), some (_, [Val.Dat y]) =>
         match binOpUB op x y with
         | some e => RhsResult.Err e
         | none => RhsResult.Ok [Val.Dat (evalBinOp op x y)] obseq.TyVal.NatTy state
     | _, _ => RhsResult.Err "BinOp expects two concrete words"
  | .AllocN ty n => allocPtr M state (n * tbytes ty)
  | .AllocDyn ty lenReg =>
     match state.reg.lookup lenReg with
     | some (_, [Val.Dat n]) => allocPtr M state (n * tbytes ty)
     | _ => RhsResult.Err "AllocDyn expects a concrete word"
  | .Borrow kind prot mask len baseReg offset =>
     match state.reg.lookup baseReg with
     | some (_, [Val.Ptr base baseOff extent size tag]) =>
       let addr := base + baseOff + B * offset
       match len with
       | some n =>
         if addr + B * n > base + size then RhsResult.Err "OOB"
         else
           match M.ref state.perms addr (B * n) tag kind prot (expandMask mask) with
           | .ok (perms2, newTag) =>
             RhsResult.Ok [Val.Ptr base (baseOff + B * offset) (B * n) size newTag]
               obseq.TyVal.PTy { state with perms := perms2 }
           | .error msg => RhsResult.Err msg
       | none =>
         match M.ref state.perms addr extent tag kind prot (expandMask mask) with
         | .ok (perms2, newTag) =>
           RhsResult.Ok [Val.Ptr base (baseOff + B * offset) extent size newTag]
             obseq.TyVal.PTy { state with perms := perms2 }
         | .error msg => RhsResult.Err msg
     | _ => RhsResult.Err "Borrow expects Ptr"

def writeThroughPtr (M : PermissionModel) (state : State M) (ptr : Register)
    (vals : List Val) (invalidMsg : String) : Result M :=
  match state.reg.lookup ptr with
  | some (_, [Val.Ptr base offset _ size tag]) =>
     let addr := base + offset
     if addr + B * vals.length > base + size then Result.Err "OOB"
     else
       match M.useMut state.perms addr (B * vals.length) tag with
       | .ok perms2 =>
          match writeValsT state.mem addr vals with
          | .ok mem2 => Result.Ok { state with perms := perms2, mem := mem2, pc := state.pc + 1 }
          | .error e => Result.Err e
       | .error msg => Result.Err msg
  | _ => Result.Err invalidMsg

def step (M : PermissionModel) (state : State M) (prog : oseair.Prog) : Result M :=
  match prog state.pc with
  | none => Result.Ok state
  | some instr => match instr with
    | .Halt => Result.Ok state
    | .Assgn reg rhs =>
      match evalRhs M state rhs with
      | RhsResult.Ok vals ty s1 =>
        Result.Ok { s1 with reg := s1.reg.insert reg (ty, vals), pc := state.pc + 1 }
      | RhsResult.Err msg => Result.Err msg
    | .RStore ty src ptr =>
      match state.reg.lookup src, state.reg.lookup ptr with
      | some (srcTy, vals), some _ =>
        if srcTy != ty then Result.Err "RStore type mismatch"
        else writeThroughPtr M state ptr vals "RStore Invalid Regs"
      | _, _ => Result.Err "RStore Invalid Regs"
    | .CStore ty vals ptr =>
      if vals.length != typeSize ty then Result.Err "CStore size mismatch"
      else writeThroughPtr M state ptr vals "CStore Invalid Ptr"
    | .Die reg len =>
       match state.reg.lookup reg with
       | some (_, [Val.Ptr base offset _ _ tag]) =>
          match M.die state.perms (base + offset) (B * len) tag with
          | .ok perms2 => Result.Ok { state with perms := perms2, pc := state.pc + 1 }
          | .error msg => Result.Err msg
       | _ => Result.Err "Die expects Ptr"
    | .Dealloc ptr =>
       match state.reg.lookup ptr with
       | some (_, [Val.Ptr base offset _ size tag]) =>
          if offset != 0 then
            Result.Err "deallocation of a pointer that is not the beginning of its allocation"
          else
            match M.dealloc state.perms base size tag with
            | .ok perms2 =>
              Result.Ok { state with perms := perms2,
                                     mem := state.mem.write base (List.replicate size .uninit),
                                     pc := state.pc + 1 }
            | .error msg => Result.Err msg
       | _ => Result.Err "Dealloc expects Ptr"
    | .SkipIf discr val skip =>
       match state.reg.lookup discr with
       | some (_, [Val.Dat v]) =>
          if v == val then Result.Ok { state with pc := state.pc + 1 }
          else Result.Ok { state with pc := state.pc + 1 + skip }
       | _ => Result.Err "SkipIf expects a concrete word"
    | .PushProt => Result.Ok { state with perms := M.pushFrame state.perms, pc := state.pc + 1 }
    | .PopProt =>
       match M.popFrame state.perms with
       | .ok perms2 => Result.Ok { state with perms := perms2, pc := state.pc + 1 }
       | .error msg => Result.Err msg
    | .Memcpy dst src ty =>
       match state.reg.lookup dst, state.reg.lookup src with
       | some (_, [Val.Ptr dBase dOff _ dSize dTag]), some (_, [Val.Ptr sBase sOff _ sSize sTag]) =>
          let dAddr := dBase + dOff
          let sAddr := sBase + sOff
          let sz := tbytes ty
          if dAddr + sz > dBase + dSize || sAddr + sz > sBase + sSize then Result.Err "OOB"
          else if dAddr < sAddr + sz && sAddr < dAddr + sz then Result.Err "Memcpy overlapping ranges"
          else
            match M.read state.perms sAddr sz sTag with
            | .ok perms2 =>
              match M.useMut perms2 dAddr sz dTag with
              | .ok perms3 =>
                  -- a raw byte copy: provenance travels with the bytes
                  Result.Ok { state with perms := perms3,
                                         mem := state.mem.copyBytes dAddr sAddr sz,
                                         pc := state.pc + 1 }
              | .error msg => Result.Err msg
            | .error msg => Result.Err msg
       | _, _ => Result.Err "Memcpy invalid regs"

end obseq3.oseairB
