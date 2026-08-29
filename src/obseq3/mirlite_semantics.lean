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
  allocs : List (Word × Nat) := []   -- (base, size), for int-to-ptr resolution
deriving Repr

namespace Mem

def empty : Mem := { mMap := [], addrStart := 0 }

/-- Resolve a concrete integer address to its allocation, for int-to-ptr
    casts. Unknown addresses yield a degenerate (dangling) allocation. -/
def resolveAddr (m : Mem) (n : Word) : Word × Word × Nat :=
  match m.allocs.find? (fun (b, s) => decide (b ≤ n) && decide (n < b + s)) with
  | some (b, s) => (b, n - b, s)
  | none => (n, 0, 0)

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
  (base, { m with addrStart := base + sz, allocs := (base, sz) :: m.allocs })

/-- Remove the cells of a deallocated range. The bump allocator never
    reuses addresses, so dangling pointers into the range keep failing. -/
def Mem.removeRange (m : Mem) (base : Word) (sz : Nat) : Mem :=
  { m with mMap := m.mMap.filter (fun (a, _) => decide (a < base) || decide (base + sz ≤ a)) }

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

/-- Resolve a place FOR AN ACCESS: like `resolvePlace?`, but each `deref`
    level performs a real SB read of the pointer cell — Miri's behavior
    (evaluating `*p` reads `p` as an operand), and what the compiled code
    does (`Rhs.Load`). The pure `resolvePlace?` remains for genuine raw
    peeks: `assignIf` discriminants, matching the target's event-free
    `SkipIf`. Threads the permission state; memory is read-only here. -/
def resolvePlaceAcc (M : PermissionModel) (state : State M Γ) :
    Place Γ τ → Except String (PlaceRes × M.State)
  | .local loc =>
      match state.env.lookup loc with
      | some binding =>
          .ok ({ addr := binding.addr, tag := binding.tag,
                 allocBase := binding.addr, allocSize := blockSize τ }, state.perms)
      | none => .error "place root local not allocated"
  | .proj base path =>
      match resolvePlaceAcc M state base with
      | .error e => .error e
      | .ok (res, perms') =>
          .ok ({ res with addr := res.addr + PathTo.offset path }, perms')
  | .deref ptrPlace =>
      match resolvePlaceAcc M state ptrPlace with
      | .error e => .error e
      | .ok (ptrRes, perms') =>
          -- the pointer being dereferenced must itself be in bounds of its
          -- slice — Miri's dereferenceable requirement, and the read-side
          -- mirror of `writeResolvedPlace`'s bounds check (the compiled
          -- `Rhs.Load` performs the identical check)
          if ptrRes.addr < ptrRes.allocBase ∨
             ptrRes.addr ≥ ptrRes.allocBase + ptrRes.allocSize then
            .error "deref of an out-of-bounds pointer"
          else
          match M.read perms' ptrRes.addr 1 ptrRes.tag with
          | .error e => .error s!"read access failed: {e}"
          | .ok perms'' =>
              match state.mem.find? ptrRes.addr with
              | some (.ptrVal base offset size tag) =>
                  .ok ({ addr := base + offset, tag := tag,
                         allocBase := base, allocSize := size }, perms'')
              | _ => .error "deref of a non-pointer value"

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
      match resolvePlaceAcc M state src with
      | .error e => .err e
      | .ok (resolved, permsR) =>
          -- Miri requires a typed access's WHOLE RANGE to be
          -- dereferenceable; through a LOADED pointer the SB read alone
          -- checks only per-cell stacks. The read-side mirror of the
          -- retag event fix (2026-08-28); for local/proj sources the
          -- check is discharged by construction/typing. What makes the
          -- copy-through-a-pointer regime provable: the target Memcpy
          -- checks the same bound against the loaded pointer's extent.
          if resolved.addr + blockSize τ > resolved.allocBase + resolved.allocSize then
            .err "copy of an out-of-bounds range"
          else
          match M.read permsR resolved.addr (blockSize τ) resolved.tag with
          | .error e => .err s!"read access failed: {e}"
          | .ok perms' =>
              let state' := { state with perms := perms' }
              .ok {
                values := readWordSeq state'.mem resolved.addr (blockSize τ)
                values_len := readWordSeq_length state'.mem resolved.addr (blockSize τ)
                state := state'
              }
  | .uninit =>
      .ok { values := List.replicate (blockSize τ) MemValue.undef
            values_len := List.length_replicate
            state := state }
  | .ptrCast src =>
      -- pointer type-punning cast: a tag-preserving one-cell copy
      match resolvePlaceAcc M state src with
      | .error e => .err e
      | .ok (resolved, permsR) =>
          match M.read permsR resolved.addr 1 resolved.tag with
          | .error e => .err s!"read access failed: {e}"
          | .ok perms' =>
              let state' := { state with perms := perms' }
              .ok {
                values := readWordSeq state'.mem resolved.addr 1
                values_len := readWordSeq_length state'.mem resolved.addr 1
                state := state'
              }
  | .ptrOffset (σ := σ) src delta =>
      -- pointer arithmetic: move the offset by delta pointees; the tag
      -- (provenance) is preserved
      match resolvePlaceAcc M state src with
      | .error e => .err e
      | .ok (resolved, permsR) =>
          match M.read permsR resolved.addr 1 resolved.tag with
          | .error e => .err s!"read access failed: {e}"
          | .ok perms' =>
              match state.mem.find? resolved.addr with
              | some (.ptrVal base offset size tag) =>
                  let newOff : Int := (offset : Int) + delta * (blockSize σ : Int)
                  if newOff < 0 then
                    .err "pointer offset before the allocation base"
                  else
                    .ok { values := [MemValue.ptrVal base newOff.toNat size tag]
                          values_len := rfl
                          state := { state with perms := perms' } }
              | _ => .err "pointer offset of a non-pointer value"
  | .refSlice kind prot src =>
      -- retag of slice data: the fat value's length is the rest of its
      -- allocation (size - offset); a fresh tag over that runtime range
      match resolvePlaceAcc M state src with
      | .error e => .err e
      | .ok (resolved, permsR) =>
          match M.read permsR resolved.addr 1 resolved.tag with
          | .error e => .err s!"read access failed: {e}"
          | .ok perms' =>
              match state.mem.find? resolved.addr with
              | some (.ptrVal base offset size tag) =>
                  let len := size - offset
                  match M.ref perms' (base + offset) len tag kind prot [] with
                  | .error e => .err s!"retag failed: {e}"
                  | .ok (perms'', newTag) =>
                      .ok { values := [MemValue.ptrVal base offset size newTag]
                            values_len := rfl
                            state := { state with perms := perms'' } }
              | _ => .err "slice value is not a pointer"
  | .exposeAddr src =>
      -- ptr-to-int cast: expose the tag, yield the concrete address
      match resolvePlaceAcc M state src with
      | .error e => .err e
      | .ok (resolved, permsR) =>
          match M.read permsR resolved.addr 1 resolved.tag with
          | .error e => .err s!"read access failed: {e}"
          | .ok perms' =>
              match state.mem.find? resolved.addr with
              | some (.ptrVal base offset _ tag) =>
                  .ok { values := [MemValue.word (base + offset)]
                        values_len := rfl
                        state := { state with perms := M.expose perms' tag } }
              | _ => .err "ptr-to-int cast of a non-pointer value"
  | .fromExposed src =>
      -- int-to-ptr cast: a wildcard pointer into the containing allocation
      match resolvePlaceAcc M state src with
      | .error e => .err e
      | .ok (resolved, permsR) =>
          match M.read permsR resolved.addr 1 resolved.tag with
          | .error e => .err s!"read access failed: {e}"
          | .ok perms' =>
              match state.mem.find? resolved.addr with
              | some (.word n) =>
                  let (base, off, size) := state.mem.resolveAddr n
                  .ok { values := [MemValue.ptrVal base off size wildcardTag]
                        values_len := rfl
                        state := { state with perms := perms' } }
              | _ => .err "int-to-ptr cast of a non-integer value"
  | .ref (τ := σ) kind prot mask src =>
      match resolvePlaceAcc M state src with
      | .error e => .err e
      | .ok (resolved, permsR) =>
          -- Miri requires a retag's WHOLE RANGE to be dereferenceable; the
          -- SB fold alone only guarantees the granting tag per cell. The
          -- range form admits zero-sized referents at one-past-the-end
          -- (`&mut ()` on a tail field). Added 2026-08-28: it is the
          -- retag-side mirror of `writeResolvedPlace`'s check, and it is
          -- what makes the reborrow-through-a-loaded-pointer regime
          -- provable — the target's `Rhs.Borrow` performs the identical
          -- check against the loaded pointer's extent, and only THIS
          -- event carries the pointee type needed to state the bound
          -- (memory cells are untyped; see the ZST-vs-u64 example in
          -- journal 2026-08-27-ref-proj-closed.md).
          if resolved.addr + blockSize σ > resolved.allocBase + resolved.allocSize then
            .err "retag of an out-of-bounds range"
          else
          match M.ref permsR resolved.addr (blockSize σ) resolved.tag kind prot mask with
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

/-- The tail of `doAssign` after the destination is resolved (split out
    2026-08-28 so the overlapping-assignment guard exists ONLY in the
    `.copy` branch; every other rhs reduces to this directly). -/
def doAssignCont
  (M : PermissionModel)
  (s1 : State M Γ)
  (resolved : PlaceRes)
  (permsD : M.State)
  {τ : LayoutTy}
  (rhs : RExpr Γ τ) : Result M Γ :=
  match evalRExpr M { s1 with perms := permsD } rhs with
  | .err msg => .err msg
  | .ok output =>
    writeResolvedPlace M output.state resolved output.values output.values_len

def doAssign
  (M : PermissionModel)
  (state : State M Γ)
  (dst : Place Γ τ)
  (rhs : RExpr Γ τ) : Result M Γ :=
  match preparePlaceAssign M state dst with
  | .err msg => .err msg
  | .ok s1 =>
  -- Rust's documented evaluation order for assignment: the RHS first,
  -- then the place. Reordered 2026-08-30 (the source-side completion of
  -- the d34 lowering-order fix): with an event-ful rhs AND an event-ful
  -- destination resolution (deref levels read their pointer cells), the
  -- two orders genuinely differ — a retag can pop the tag a later spine
  -- read needs — and the compiled code performs the rhs first.
  match evalRExpr M s1 rhs with
  | .err msg => .err msg
  | .ok output =>
  match resolvePlaceAcc M output.state dst with
  | .error e => .err e
  | .ok (resolved, permsD) =>
  -- MIR forbids overlapping place-to-place assignment (Miri lowers it
  -- to a NONOVERLAPPING copy and flags overlap as UB): the guard exists
  -- only in the `.copy` branch, checked with the ACCESS-FREE resolver
  -- so no SB event is duplicated (the d33 countermodel class).
  match rhs with
  | .copy src =>
      match resolvePlace? s1 src with
      | some rs =>
          if rs.addr < resolved.addr + blockSize τ ∧
             resolved.addr < rs.addr + blockSize τ then
            .err "copy of overlapping ranges"
          else
            writeResolvedPlace M { output.state with perms := permsD }
              resolved output.values output.values_len
      | none =>
          writeResolvedPlace M { output.state with perms := permsD }
            resolved output.values output.values_len
  | _ =>
      writeResolvedPlace M { output.state with perms := permsD }
        resolved output.values output.values_len

/-- Read a runtime word for an `AllocLen`. A `fromPlace` read is a real
    SB read access through the place's tag. -/
def readAllocLen
  (M : PermissionModel)
  (state : State M Γ) : AllocLen Γ → Except String (Nat × State M Γ)
  | .const n => .ok (n, state)
  | .fromPlace p =>
      match resolvePlaceAcc M state p with
      | .error e => .error e
      | .ok (res, permsR) =>
          match M.read permsR res.addr 1 res.tag with
          | .error e => .error s!"allocation size read failed: {e}"
          | .ok perms' =>
              match state.mem.find? res.addr with
              | some (.word n) => .ok (n, { state with perms := perms' })
              | _ => .error "allocation size is not a concrete word"

def stepStmt
  (M : PermissionModel)
  (state : State M Γ) :
  Stmt Γ → Result M Γ
  | .halt => .ok state
  | .pushProtectors =>
      .ok { state with perms := M.pushFrame state.perms, pc := state.pc + 1 }
  | .popProtectors =>
      match M.popFrame state.perms with
      | .ok perms' => .ok { state with perms := perms', pc := state.pc + 1 }
      | .error e => .err s!"popProtectors failed: {e}"
  | .assign dst rhs => doAssign M state dst rhs
  | .assignIf discr val dst rhs =>
      match resolvePlace? state discr with
      | none => .err "assignIf discriminant place not allocated"
      | some res =>
          match state.mem.find? res.addr with
          | some (.word v) =>
              if v == val then doAssign M state dst rhs
              else .ok { state with pc := state.pc + 1 }
          | _ => .err "assignIf discriminant is not a concrete word"
  | .alloc (τ := τ) dst len =>
      match preparePlaceAssign M state dst with
      | .err msg => .err msg
      | .ok s1 =>
      match resolvePlaceAcc M s1 dst with
      | .error e => .err e
      | .ok (resolved, permsD) =>
      match readAllocLen M { s1 with perms := permsD } len with
      | .error e => .err e
      | .ok (n, state) =>
          let units := n * blockSize τ
          let (base, mem') := allocate state.mem units
          match M.own state.perms base units with
          | .error e => .err s!"heap allocation failed: {e}"
          | .ok (perms', tag) =>
              let state := { state with mem := mem', perms := perms' }
              writeResolvedPlace (τ := obseq.LayoutTy.PtrL τ) M state resolved
                [MemValue.ptrVal base 0 units tag] rfl
  | .dealloc dst =>
      match resolvePlaceAcc M state dst with
      | .error e => .err e
      | .ok (res, permsR) =>
          match M.read permsR res.addr 1 res.tag with
          | .error e => .err s!"dealloc pointer read failed: {e}"
          | .ok perms' =>
              match state.mem.find? res.addr with
              | some (.ptrVal base offset size tag) =>
                  if offset != 0 then
                    .err "deallocation of a pointer that is not the beginning of its allocation"
                  else
                    match M.dealloc perms' base size tag with
                    | .error e => .err s!"deallocation failed: {e}"
                    | .ok permsD =>
                        let mem' := state.mem.removeRange base size
                        .ok { state with perms := permsD, mem := mem', pc := state.pc + 1 }
              | _ => .err "dealloc argument is not a pointer value"

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
