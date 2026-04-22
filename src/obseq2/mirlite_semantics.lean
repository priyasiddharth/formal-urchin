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

namespace Place

def baseLocal : Place Γ τ → Σ σ, Local Γ σ
  | .local loc => ⟨τ, loc⟩
  | .proj base _ => Place.baseLocal base

def offset : Place Γ τ → Nat
  | .local _ => 0
  | .proj base path => Place.offset base + PathTo.offset path

end Place

inductive MemValue (Γ : Ctx) where
| undef
| word (value : Word)
| placeTag {τ : LayoutTy} (place : Place Γ τ) (tag : Tag)

abbrev MemMap (Γ : Ctx) := List (Word × MemValue Γ)

structure Mem (Γ : Ctx) where
  mMap : MemMap Γ
  addrStart : Word

namespace Mem

def find? (m : Mem Γ) (addr : Word) : Option (MemValue Γ) :=
  List.lookup addr m.mMap

def write (m : Mem Γ) (addr : Word) (value : MemValue Γ) : Mem Γ :=
  { m with mMap := (addr, value) :: m.mMap.filter (fun (a, _) => a != addr) }

end Mem

def readWordSeq (m : Mem Γ) (addr : Word) : Nat → List (MemValue Γ)
  | 0 => []
  | n + 1 =>
      match m.find? addr with
      | some value => value :: readWordSeq m (addr + 1) n
      | none => MemValue.undef :: readWordSeq m (addr + 1) n

@[simp] theorem readWordSeq_length
  (m : Mem Γ)
  (addr : Word)
  (n : Nat) :
  (readWordSeq m addr n).length = n := by
  induction n generalizing addr with
  | zero => simp [readWordSeq]
  | succ n ih =>
  cases h : m.find? addr <;> simp [readWordSeq, h, ih]

def writeWordSeq (m : Mem Γ) (addr : Word) : List (MemValue Γ) → Mem Γ
  | [] => m
  | value :: values => writeWordSeq (m.write addr value) (addr + 1) values

def allocate (m : Mem Γ) (sz : Nat) : Word × Mem Γ :=
  let base := m.addrStart
  (base, { m with addrStart := base + sz })

structure State (M : PermissionModel) (Γ : Ctx) where
  pc : Nat
  env : Env Γ
  mem : Mem Γ
  perms : M.State

structure PlaceRes (Γ : Ctx) (τ : LayoutTy) where
  addr : Word
  tag : Tag

inductive Result (M : PermissionModel) (Γ : Ctx) where
| ok (state : State M Γ)
| err (msg : String)

structure EvalOutput (M : PermissionModel) (Γ : Ctx) (τ : LayoutTy) where
  values : List (MemValue Γ)
  values_len : values.length = blockSize τ
  state : State M Γ

inductive EvalResult (M : PermissionModel) (Γ : Ctx) (τ : LayoutTy) where
| ok (output : EvalOutput M Γ τ)
| err (msg : String)

def resolveDirectPlace? (state : State M Γ) (place : Place Γ τ) : Option (PlaceRes Γ τ) :=
  let base := Place.baseLocal place
  match state.env.lookup base.2 with
  | some binding =>
      some { addr := binding.addr + Place.offset place, tag := binding.tag }
  | none => none

def writeResolvedPlace
  (M : PermissionModel)
  (state : State M Γ)
  (dst : PlaceRes Γ τ)
  (values : List (MemValue Γ))
  (_valuesLen : values.length = blockSize τ) : Result M Γ :=
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
    (values : List (MemValue Γ))
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
    (values : List (MemValue Γ))
    (valuesLen : values.length = blockSize τ) : Result M Γ :=
    match resolveDirectPlace? state dst with
    | some resolvedDst =>
      writeResolvedPlace M state resolvedDst values valuesLen
    | none =>
      match dst with
      | .local loc => allocateBaseAndWrite M state loc values valuesLen
      | .proj _ _ => .err "destination base place not allocated"

def evalDerefAddr
  (M : PermissionModel)
  (state : State M Γ)
  {τ : LayoutTy}
  (addr : Word)
  (guardTag : Tag) : EvalResult M Γ τ :=
  match M.read state.perms addr guardTag with
  | none =>
      .err "pointee read permission failed"
  | some perms' =>
      let state' := { state with perms := perms' }
      .ok {
        values := readWordSeq state'.mem addr (blockSize τ)
        values_len := by
          exact readWordSeq_length state'.mem addr (blockSize τ)
        state := state'
      }

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
  | .copy _ =>
      .err "copy is not part of the initial obseq2 MIRLite fragment"
  | .ref kind src =>
        match resolveDirectPlace? state src with
        | none =>
          .err "reference source place not allocated"
        | some resolved =>
          match M.ref state.perms resolved.addr resolved.tag kind with
          | some (perms', freshTag) =>
            .ok {
            values := [MemValue.placeTag src freshTag]
            values_len := rfl
            state := { state with perms := perms' }
            }
          | none =>
            .err "reference creation permission failed"
  | .deref (τ := τ) src =>
        match resolveDirectPlace? state src with
        | none =>
          .err "pointer source place not allocated"
        | some resolvedPtr =>
          match M.read state.perms resolvedPtr.addr resolvedPtr.tag with
          | none =>
            .err "pointer read permission failed"
          | some perms' =>
            let state' := { state with perms := perms' }
            match state'.mem.find? resolvedPtr.addr with
            | some (@MemValue.placeTag _ τ' pointee guardTag) =>
              if τ' == τ then
              match resolveDirectPlace? state' pointee with
              | some resolvedPointee =>
                evalDerefAddr M state' resolvedPointee.addr guardTag
              | none =>
                .err "pointee place not allocated"
              else
              .err "deref type mismatch"
            | _ =>
              .err "deref expected a pointer cell"

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
