import obseq3.syntax
import obseq3.permission

/-!
Forked from `obseq2.mirlite` with the v3 permission surface:
- every permission op takes the length of the accessed range
  (per-cell borrow stacks in the model);
- permission failures carry messages (`Except String`) which are
  propagated into `Result.err` for the conformance harness.
-/

namespace obseq3.mirlite

open obseq3

structure Binding where
  addr : Word
  tag : Tag
deriving Repr, Inhabited

abbrev Env (Γ : Ctx) := Fin Γ.length → Option Binding

namespace Env

def empty : Env Γ := fun _ => none

def lookup (env : Env Γ) (loc : Local Γ τ) : Option Binding :=
  env loc.idx

def set (env : Env Γ) (loc : Local Γ τ) (binding : Binding) : Env Γ :=
  fun idx => if idx = loc.idx then some binding else env idx

end Env

inductive MemValue where
| undef
| word  (value : Word)
| ptrVal (base : Word) (offset : Word) (size : Word) (tag : Tag)
deriving Repr, BEq, Inhabited

abbrev MemMap := List (Word × MemValue)

structure Mem where
  mMap : MemMap
  addrStart : Word
deriving Repr

namespace Mem

def empty : Mem := { mMap := [], addrStart := 0 }

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
  (m : Mem) (addr : Word) (n : Nat) :
  (readWordSeq m addr n).length = n := by
  induction n generalizing addr with
  | zero => simp [readWordSeq]
  | succ n ih => cases h : m.find? addr <;> simp [readWordSeq, h, ih]

def writeWordSeq (m : Mem) (addr : Word) : List MemValue → Mem
  | [] => m
  | value :: values => writeWordSeq (m.write addr value) (addr + 1) values

def allocate (m : Mem) (sz : Nat) : Word × Mem :=
  let base := m.addrStart
  (base, { m with addrStart := base + sz })

structure State (M : PermissionModel) (Γ : Ctx) where
  pc : Nat
  env : Env Γ
  mem : Mem
  perms : M.State

def State.initial (M : PermissionModel) (Γ : Ctx) : State M Γ :=
  { pc := 0, env := Env.empty, mem := Mem.empty, perms := M.init }

structure PlaceRes where
  addr      : Word
  tag       : Tag
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
      | some res => some { res with addr := res.addr + PathTo.offset path }
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
    match M.useMut state.perms dst.addr values.length dst.tag with
    | .ok perms' =>
        let mem' := writeWordSeq state.mem dst.addr values
        .ok { state with perms := perms', mem := mem', pc := state.pc + 1 }
    | .error e => .err s!"write access failed: {e}"

def allocateBase
  (M : PermissionModel)
  (state : State M Γ)
  (loc : Local Γ τ) : Result M Γ :=
  let (addr, mem') := allocate state.mem (blockSize τ)
  match M.own state.perms addr (blockSize τ) with
  | .error e => .err s!"allocation failed: {e}"
  | .ok (permsOwned, tag) =>
      let env' := state.env.set loc { addr := addr, tag := tag }
      .ok { state with env := env', mem := mem', perms := permsOwned }

def allocateBaseAndWrite
  (M : PermissionModel)
  (state : State M Γ)
  (loc : Local Γ τ)
  (values : List MemValue)
  (_valuesLen : values.length = blockSize τ) : Result M Γ :=
  let (addr, mem') := allocate state.mem (blockSize τ)
  match M.own state.perms addr (blockSize τ) with
  | .error e => .err s!"allocation failed: {e}"
  | .ok (permsOwned, tag) =>
    match M.useMut permsOwned addr values.length tag with
    | .error e => .err s!"fresh allocation write failed: {e}"
    | .ok perms' =>
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
  | some resolvedDst => writeResolvedPlace M state resolvedDst values valuesLen
  | none =>
    match dst with
    | .local loc => allocateBaseAndWrite M state loc values valuesLen
    | .proj _ _ => .err "destination base place not allocated"
    | .deref _ => .err "destination pointer place not allocated or not a pointer"

/-- Allocate the root local underlying a (possibly projected) place.
    Deref roots are never allocated implicitly — the pointer must exist. -/
def allocateRoot
  (M : PermissionModel)
  (state : State M Γ) : Place Γ τ → Result M Γ
  | .local loc => allocateBase M state loc
  | .proj base _ => allocateRoot M state base
  | .deref _ => .err "destination pointer place not allocated or not a pointer"

def preparePlaceAssign
  (M : PermissionModel)
  (state : State M Γ)
  (dst : Place Γ τ) : Result M Γ :=
  match resolvePlace? state dst with
  | some _ => .ok state
  | none => allocateRoot M state dst

def evalRExpr
  (M : PermissionModel)
  (state : State M Γ)
  {τ : LayoutTy}
  (expr : RExpr Γ τ) : EvalResult M Γ τ :=
  match expr with
  | .constInit value =>
      .ok { values := [MemValue.word value], values_len := rfl, state := state }
  | .copy (τ := τ) src =>
      match resolvePlace? state src with
      | none => .err "copy source place not allocated"
      | some resolved =>
          match M.read state.perms resolved.addr (blockSize τ) resolved.tag with
          | .error e => .err s!"read access failed: {e}"
          | .ok perms' =>
              let state' := { state with perms := perms' }
              .ok {
                values := readWordSeq state'.mem resolved.addr (blockSize τ)
                values_len := readWordSeq_length state'.mem resolved.addr (blockSize τ)
                state := state'
              }
  | .ref (τ := σ) kind src =>
      match resolvePlace? state src with
      | none => .err "reference source place not allocated"
      | some resolved =>
          match M.ref state.perms resolved.addr (blockSize σ) resolved.tag kind with
          | .ok (perms', freshTag) =>
              .ok {
                values := [MemValue.ptrVal resolved.allocBase
                             (resolved.addr - resolved.allocBase)
                             resolved.allocSize
                             freshTag]
                values_len := rfl
                state := { state with perms := perms' }
              }
          | .error e => .err s!"retag failed: {e}"

def stepStmt
  (M : PermissionModel)
  (state : State M Γ) :
  Stmt Γ → Result M Γ
  | .halt => .ok state
  | .assign dst rhs =>
      match preparePlaceAssign M state dst with
      | .err msg => .err msg
      | .ok stateForRhs =>
      match evalRExpr M stateForRhs rhs with
      | .err msg => .err msg
      | .ok output =>
        finishPlaceAssign M output.state dst output.values output.values_len

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

end obseq3.mirlite
