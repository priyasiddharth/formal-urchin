import obseq2.syntax
import obseq2.permission

namespace obseq2.mirlite

open obseq2

structure Binding where
  addr : Word
  tag : Tag
deriving Repr, Inhabited

/-
Fresh-base allocation is represented concretely by leaving locals unallocated in
the environment until the first direct assignment to that base place.
-/
abbrev Env (Γ : Ctx) := Fin Γ.length → Option Binding

namespace Env

def empty : Env Γ :=
  fun _ => none

def lookup (env : Env Γ) (loc : Local Γ τ) : Option Binding :=
  env loc.idx

def set (env : Env Γ) (loc : Local Γ τ) (binding : Binding) : Env Γ :=
  fun idx => if idx = loc.idx then some binding else env idx

end Env

namespace PathTo

def offset : PathTo src dst → Nat
  | .nil => 0
  | .field (tys := tys) idx tail =>
  layoutSizeList (tys.take idx.1) + offset tail

end PathTo

/-- Pointer values in memory are concrete (base, offset, size, tag) — matching OSEA-IR's
    Val.Ptr exactly. This removes Γ from MemValue and eliminates the symbolic placeTag
    representation, making MemValSim trivial and allowing Γ to be dropped from Mem and
    the memory portion of State. -/
inductive MemValue where
| undef
| word  (value : Word)
| ptrVal (base : Word) (offset : Word) (size : Word) (tag : Tag)

abbrev MemMap := List (Word × MemValue)

structure Mem where
  mMap : MemMap
  addrStart : Word

namespace Mem

def find? (m : Mem) (addr : Word) : Option MemValue :=
  List.lookup addr m.mMap

def write (m : Mem) (addr : Word) (value : MemValue) : Mem :=
  { m with mMap := (addr, value) :: m.mMap.filter (fun (a, _) => a != addr) }

end Mem

def readWordSeq (m : Mem) (addr : Word) : Nat → List MemValue
  | 0 => []
  | n + 1 =>
      match m.find? addr with
      | some value => value :: readWordSeq m (addr + 1) n
      | none => MemValue.undef :: readWordSeq m (addr + 1) n

@[simp] theorem readWordSeq_length
  (m : Mem)
  (addr : Word)
  (n : Nat) :
  (readWordSeq m addr n).length = n := by
  induction n generalizing addr with
  | zero => simp [readWordSeq]
  | succ n ih =>
  cases h : m.find? addr <;> simp [readWordSeq, h, ih]

def writeWordSeq (m : Mem) (addr : Word) : List MemValue → Mem
  | [] => m
  | value :: values => writeWordSeq (m.write addr value) (addr + 1) values

def allocate (m : Mem) (sz : Nat) : Word × Mem :=
  let base := m.addrStart
  (base, { m with addrStart := base + sz })

/-- State no longer carries Γ in the memory — Γ is only needed for Env. -/
structure State (M : PermissionModel) (Γ : Ctx) where
  pc : Nat
  env : Env Γ
  mem : Mem
  perms : M.State

/-- Resolved place: concrete address, tag, and allocation bounds.
    No Γ or τ parameter — all fields are concrete words. -/
structure PlaceRes where
  addr     : Word
  tag      : Tag
  allocBase : Word
  allocSize : Word

inductive Result (M : PermissionModel) (Γ : Ctx) where
| ok (state : State M Γ)
| err (msg : String)

structure EvalOutput (M : PermissionModel) (Γ : Ctx) (τ : LayoutTy) where
  values     : List MemValue
  values_len : values.length = blockSize τ
  state      : State M Γ

inductive EvalResult (M : PermissionModel) (Γ : Ctx) (τ : LayoutTy) where
| ok (output : EvalOutput M Γ τ)
| err (msg : String)

/-- Resolve a place to a concrete address and allocation bounds.
    Handles local, proj, and deref by recursion on the place structure.
    For deref, follows the ptrVal stored in memory at the pointer place — no
    intermediate permission check (that is the caller's responsibility via useMut/read). -/
def resolvePlace? (state : State M Γ) : Place Γ τ → Option PlaceRes
  | .local loc =>
      match state.env.lookup loc with
      | some binding =>
          some { addr := binding.addr, tag := binding.tag,
                 allocBase := binding.addr, allocSize := blockSize τ }
      | none => none
  | .proj base path =>
      match resolvePlace? state base with
      | none => none
      | some res =>
          some { res with addr := res.addr + PathTo.offset path }
  | .deref ptrPlace =>
      match resolvePlace? state ptrPlace with
      | none => none
      | some ptrRes =>
          match state.mem.find? ptrRes.addr with
          | some (.ptrVal base offset size tag) =>
              some { addr := base + offset, tag := tag,
                     allocBase := base, allocSize := size }
          | _ => none

def writeResolvedPlace
  (M : PermissionModel)
  (state : State M Γ)
  (dst : PlaceRes)
  (values : List MemValue)
  (_valuesLen : values.length = blockSize τ) : Result M Γ :=
  if dst.addr + values.length > dst.allocBase + dst.allocSize then
    .err "write out of bounds"
  else
    match M.useMut state.perms dst.addr dst.tag with
    | some perms' =>
        let mem' := writeWordSeq state.mem dst.addr values
        .ok { state with perms := perms', mem := mem', pc := state.pc + 1 }
    | none =>
        .err "destination write permission failed"

def allocateBaseAndWrite
  (M : PermissionModel)
  (state : State M Γ)
  (loc : Local Γ τ)
  (values : List MemValue)
  (_valuesLen : values.length = blockSize τ) : Result M Γ :=
  let (addr, mem') := allocate state.mem (blockSize τ)
  match M.own state.perms addr with
  | none =>
    .err "allocation permission initialization failed"
  | some (permsOwned, tag) =>
    match M.useMut permsOwned addr tag with
    | none =>
      .err "fresh allocation write permission failed"
    | some perms' =>
      let env' := state.env.set loc { addr := addr, tag := tag }
      let mem'' := writeWordSeq mem' addr values
      .ok { state with env := env', mem := mem'', perms := perms', pc := state.pc + 1 }

def finishPlaceAssign
  (M : PermissionModel)
  (state : State M Γ)
  (dst : Place Γ τ)
  (values : List MemValue)
  (valuesLen : values.length = blockSize τ) : Result M Γ :=
  match resolvePlace? state dst with
  | some resolvedDst =>
    writeResolvedPlace M state resolvedDst values valuesLen
  | none =>
    match dst with
    | .local loc => allocateBaseAndWrite M state loc values valuesLen
    | .proj _ _ => .err "destination base place not allocated"
    | .deref _ => .err "destination pointer place not allocated or not a pointer"

def evalRExpr
  (M : PermissionModel)
  (state : State M Γ)
  {τ : LayoutTy}
  (expr : RExpr Γ τ) : EvalResult M Γ τ :=
  match expr with
  | .constInit value =>
      .ok {
        values := [MemValue.word value]
        values_len := rfl
        state := state
      }
  | .copy (τ := τ) src =>
      match resolvePlace? state src with
      | none => .err "copy source place not allocated"
      | some resolved =>
          match M.read state.perms resolved.addr resolved.tag with
          | none => .err "copy read permission failed"
          | some perms' =>
              let state' := { state with perms := perms' }
              .ok {
                values := readWordSeq state'.mem resolved.addr (blockSize τ)
                values_len := readWordSeq_length state'.mem resolved.addr (blockSize τ)
                state := state'
              }
  | .ref kind src =>
      match resolvePlace? state src with
      | none => .err "reference source place not allocated"
      | some resolved =>
          match M.ref state.perms resolved.addr resolved.tag kind with
          | some (perms', freshTag) =>
              .ok {
                values := [MemValue.ptrVal resolved.allocBase
                             (resolved.addr - resolved.allocBase)
                             resolved.allocSize
                             freshTag]
                values_len := rfl
                state := { state with perms := perms' }
              }
          | none => .err "reference creation permission failed"

def stepStmt
  (M : PermissionModel)
  (state : State M Γ) :
  Stmt Γ → Result M Γ
  | .halt => .ok state
  | .assign dst rhs =>
      match evalRExpr M state rhs with
      | .err msg => .err msg
      | .ok output =>
        finishPlaceAssign M output.state dst output.values output.values_len

def step
  (M : PermissionModel)
  (state : State M Γ)
  (prog : Prog Γ) : Result M Γ :=
  match prog.get? state.pc with
  | some stmt => stepStmt M state stmt
  | none => .ok state

def runN
  (M : PermissionModel) : Nat → State M Γ → Prog Γ → Result M Γ
  | 0, state, _ => .ok state
  | n + 1, state, prog =>
      match prog.get? state.pc with
      | some .halt => .ok state
      | none => .ok state
      | some stmt =>
          match stepStmt M state stmt with
          | .ok state' => runN M n state' prog
          | .err msg => .err msg

end obseq2.mirlite
