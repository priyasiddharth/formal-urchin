import obseq3.mirlite_semantics
import obseq3.bytelayout

/-!
# mirlite on byte-addressed memory — stage 2

The same language, permission model and evaluation order as
`mirlite_semantics.lean`, with the memory replaced by `bytes.Mem`
(MiniRust-style abstract bytes, provenance on every pointer byte). It runs
ALONGSIDE the cell semantics: the compiler-correctness proof is still
about the cell semantics, and the conformance harness's `--bytes` mode
runs both on every program and requires the same verdict. When oseair and
the proof have moved too (stages 3–4), this file replaces the cell one.

Values are still `List MemValue` (one per cell of the layout), so the
evaluation code is the cell code with memory access swapped; what changes:

- a cell of layout `τ` is an 8-byte LEAF of `bytes.ofLayoutTy τ` (a word
  is a `usize`; `ofLayoutTy_leaves_length`: one leaf per cell), so every
  address, offset, size and permission range is in BYTES (`B * cells`);
- a write ENCODES each value (a word little-endian without provenance, a
  pointer with its provenance on all 8 bytes, `undef` as uninit bytes);
- a read DECODES each leaf at the leaf's scalar type: an integer leaf
  strips provenance (reading a pointer's bytes as a word yields its
  address — the cell model handed back the pointer itself), a pointer
  leaf keeps provenance only if all its bytes agree, and any uninit byte
  makes the leaf `undef`;
- a pointer value's fields (`base`, `offset`, `extent`, `size`) are in
  bytes; its `extent` travels in the stored provenance until fat pointers
  are two words (see `bytes.Prov.extent`);
- a pointer without provenance (decoded from integer bytes) becomes a
  degenerate pointer over a zero-sized allocation at its address: any
  non-zero-sized access through it is out of bounds, as in Miri;
- words must fit in 64 bits (a larger one is an error at the store).
-/

namespace obseq3.mirliteB

open obseq3 obseq3.bytes
open obseq3.mirlite (Binding Env MemValue PlaceRes)

/-- Bytes per cell: every cell (word or pointer) is an 8-byte leaf. -/
def B : Nat := ptrSize

/-- A layout's size in bytes. -/
def bsize (τ : LayoutTy) : Nat := B * blockSize τ

/-- The scalar type of each cell of `τ`, in order. -/
def leafKinds (τ : LayoutTy) : List Scalar := (ofLayoutTy τ).leaves.map (·.2)

theorem leafKinds_length (τ : LayoutTy) : (leafKinds τ).length = blockSize τ := by
  simp [leafKinds, ofLayoutTy_leaves_length, blockSize]

/-- A value's 8 bytes. -/
def encodeV : MemValue → Except String (List AbstractByte)
  | .undef => .ok (List.replicate B .uninit)
  | .word w =>
      if w < 256 ^ B then .ok (encodeInt B w)
      else .error "word does not fit in 64 bits"
  | .ptrVal b o e s t =>
      if b + o < 256 ^ B then
        .ok (encodePtr ⟨b + o, some { base := b, size := s, tag := t, extent := e }⟩)
      else .error "address does not fit in 64 bits"

/-- Read one leaf at its scalar type. -/
def decodeV (k : Scalar) (bs : List AbstractByte) : MemValue :=
  match k with
  | .int _ =>
      match decodeInt bs with
      | some w => .word w
      | none => .undef
  | .ptr =>
      match decodePtr bs with
      | some ⟨a, some p⟩ => .ptrVal p.base (a - p.base) p.extent p.size p.tag
      | some ⟨a, none⟩ => .ptrVal a 0 0 0 wildcardTag
      | none => .undef

def readOne (m : bytes.Mem) (addr : Nat) (k : Scalar) : MemValue :=
  decodeV k (m.read addr B)

def readVals (m : bytes.Mem) (addr : Nat) (ks : List Scalar) : List MemValue :=
  ks.zipIdx.map fun (k, i) => readOne m (addr + B * i) k

@[simp] theorem readVals_length (m : bytes.Mem) (addr : Nat) (ks : List Scalar) :
    (readVals m addr ks).length = ks.length := by
  simp [readVals]

/-- Read the cells of a value of layout `τ`. -/
def readAt (m : bytes.Mem) (addr : Nat) (τ : LayoutTy) : List MemValue :=
  readVals m addr (leafKinds τ)

theorem readAt_length (m : bytes.Mem) (addr : Nat) (τ : LayoutTy) :
    (readAt m addr τ).length = blockSize τ := by
  simp [readAt, leafKinds_length]

def writeVals (m : bytes.Mem) (addr : Nat) (vs : List MemValue) :
    Except String bytes.Mem := do
  let bss ← vs.mapM encodeV
  pure (m.write addr bss.flatten)

/-- A per-cell UnsafeCell mask, per byte. -/
def expandMask (mask : List Bool) : List Bool := mask.flatMap fun b => List.replicate B b

structure State (M : PermissionModel) (Γ : Ctx) where
  pc : Nat
  env : Env Γ
  mem : bytes.Mem
  perms : M.State

def State.initial (M : PermissionModel) (Γ : Ctx) : State M Γ :=
  { pc := 0, env := Env.empty, mem := {}, perms := M.init }

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
                 allocBase := binding.addr, allocSize := bsize τ }
      | none => none
  | .proj base path =>
      match resolvePlace? state base with
      | none => none
      | some res => some { res with addr := res.addr + B * PathTo.offset path }
  | .deref ptrPlace =>
      match resolvePlace? state ptrPlace with
      | none => none
      | some ptrRes =>
          match readOne state.mem ptrRes.addr .ptr with
          | .ptrVal base offset _ size tag =>
              some { addr := base + offset, tag := tag, allocBase := base, allocSize := size }
          | _ => none

def resolvePlaceAcc (M : PermissionModel) (state : State M Γ) :
    Place Γ τ → Except String (PlaceRes × M.State)
  | .local loc =>
      match state.env.lookup loc with
      | some binding =>
          .ok ({ addr := binding.addr, tag := binding.tag,
                 allocBase := binding.addr, allocSize := bsize τ }, state.perms)
      | none => .error "place root local not allocated"
  | .proj base path =>
      match resolvePlaceAcc M state base with
      | .error e => .error e
      | .ok (res, perms') => .ok ({ res with addr := res.addr + B * PathTo.offset path }, perms')
  | .deref ptrPlace =>
      match resolvePlaceAcc M state ptrPlace with
      | .error e => .error e
      | .ok (ptrRes, perms') =>
          if ptrRes.addr < ptrRes.allocBase ∨
             ptrRes.addr ≥ ptrRes.allocBase + ptrRes.allocSize then
            .error "deref of an out-of-bounds pointer"
          else
          match M.read perms' ptrRes.addr B ptrRes.tag with
          | .error e => .error s!"read access failed: {e}"
          | .ok perms'' =>
              match readOne state.mem ptrRes.addr .ptr with
              | .ptrVal base offset _ size tag =>
                  .ok ({ addr := base + offset, tag := tag,
                         allocBase := base, allocSize := size }, perms'')
              | _ => .error "deref of a non-pointer value"

def writeResolvedPlace (M : PermissionModel) (state : State M Γ) (dst : PlaceRes)
    (values : List MemValue) : Result M Γ :=
  if dst.addr + B * values.length > dst.allocBase + dst.allocSize then
    .err "write out of bounds"
  else
    match M.useMut state.perms dst.addr (B * values.length) dst.tag with
    | .ok perms' =>
        match writeVals state.mem dst.addr values with
        | .ok mem' => .ok { state with perms := perms', mem := mem', pc := state.pc + 1 }
        | .error e => .err e
    | .error e => .err s!"write access failed: {e}"

def allocateBase (M : PermissionModel) (state : State M Γ) (loc : Local Γ τ) : Result M Γ :=
  let (addr, mem') := state.mem.allocate (bsize τ) B
  match M.own state.perms addr (bsize τ) with
  | .error e => .err s!"allocation failed: {e}"
  | .ok (permsOwned, tag) =>
      let env' := state.env.set loc { addr := addr, tag := tag }
      .ok { state with env := env', mem := mem', perms := permsOwned }

def allocateRoot (M : PermissionModel) (state : State M Γ) : Place Γ τ → Result M Γ
  | .local loc => allocateBase M state loc
  | .proj base _ => allocateRoot M state base
  | .deref _ => .err "destination pointer place not allocated or not a pointer"

def preparePlaceAssign (M : PermissionModel) (state : State M Γ) (dst : Place Γ τ) :
    Result M Γ :=
  match resolvePlace? state dst with
  | some _ => .ok state
  | none => allocateRoot M state dst

def ensureRoot (M : PermissionModel) (state : State M Γ) : Place Γ τ → Result M Γ
  | .local loc =>
      match state.env.lookup loc with
      | some _ => .ok state
      | none => allocateBase M state loc
  | .proj base _ => ensureRoot M state base
  | .deref ptrPlace => ensureRoot M state ptrPlace

def evalCopy (M : PermissionModel) (state : State M Γ) {τ : LayoutTy} (src : Place Γ τ) :
    EvalResult M Γ τ :=
  match resolvePlaceAcc M state src with
  | .error e => .err e
  | .ok (resolved, permsR) =>
      if resolved.addr + bsize τ > resolved.allocBase + resolved.allocSize then
        .err "copy of an out-of-bounds range"
      else
      match M.read permsR resolved.addr (bsize τ) resolved.tag with
      | .error e => .err s!"read access failed: {e}"
      | .ok perms' =>
          let state' := { state with perms := perms' }
          if (readAt state'.mem resolved.addr τ).any (fun v => v == .undef) then
            .err "read of uninitialized memory"
          else
          .ok { values := readAt state'.mem resolved.addr τ
                values_len := readAt_length _ _ _
                state := state' }

def evalAllocLen (M : PermissionModel) (state : State M Γ) :
    AllocLen Γ → Except String (Nat × State M Γ)
  | .const n => .ok (n, state)
  | .fromPlace p =>
      match evalCopy M state p with
      | .err e => .error e
      | .ok out =>
          match out.values with
          | [.word n] => .ok (n, out.state)
          | _ => .error "allocation size is not a concrete word"

/-- A one-cell read through a place, for the pointer/integer rvalues:
    resolve for access, bounds, SB read, the leaf decoded at `k`. -/
def readCell (M : PermissionModel) (state : State M Γ) (src : Place Γ τ) (k : Scalar)
    (what : String) : Except String (MemValue × M.State) :=
  match resolvePlaceAcc M state src with
  | .error e => .error e
  | .ok (resolved, permsR) =>
      if resolved.addr + B > resolved.allocBase + resolved.allocSize then
        .error s!"{what} of an out-of-bounds place"
      else
      match M.read permsR resolved.addr B resolved.tag with
      | .error e => .error s!"read access failed: {e}"
      | .ok perms' => .ok (readOne state.mem resolved.addr k, perms')

def evalRExpr (M : PermissionModel) (state : State M Γ) {τ : LayoutTy} (expr : RExpr Γ τ) :
    EvalResult M Γ τ :=
  match expr with
  | .constInit value => .ok { values := [MemValue.word value], values_len := rfl, state := state }
  | .copy src => evalCopy M state src
  | .move (τ := τ) src =>
      match resolvePlaceAcc M state src with
      | .error e => .err e
      | .ok (resolved, permsR) =>
          if resolved.addr + bsize τ > resolved.allocBase + resolved.allocSize then
            .err "move of an out-of-bounds range"
          else
          match M.ref permsR resolved.addr (bsize τ) resolved.tag .Mut false [] with
          | .error e => .err s!"move retag failed: {e}"
          | .ok (permsM, tmpTag) =>
          match M.read permsM resolved.addr (bsize τ) tmpTag with
          | .error e => .err s!"read access failed: {e}"
          | .ok permsRd =>
          match M.die permsRd resolved.addr (bsize τ) tmpTag with
          | .error e => .err s!"move retire failed: {e}"
          | .ok perms' =>
              let state' := { state with perms := perms' }
              if (readAt state'.mem resolved.addr τ).any (fun v => v == .undef) then
                .err "read of uninitialized memory"
              else
              .ok { values := readAt state'.mem resolved.addr τ
                    values_len := readAt_length _ _ _
                    state := state' }
  | .alloc (τ := τ) len =>
      match evalAllocLen M state len with
      | .error e => .err e
      | .ok (n, state) =>
          let units := n * bsize τ
          let (base, mem') := state.mem.allocate units B
          match M.own state.perms base units with
          | .error e => .err s!"heap allocation failed: {e}"
          | .ok (perms', tag) =>
              .ok { values := [MemValue.ptrVal base 0 units units tag]
                    values_len := rfl
                    state := { state with mem := mem', perms := perms' } }
  | .sliceLen (σ := σ) src =>
      match evalCopy M state src with
      | .err e => .err e
      | .ok out =>
          match out.values with
          | [.ptrVal _ _ extent _ _] =>
              .ok { values := [MemValue.word (extent / bsize σ)], values_len := rfl,
                    state := out.state }
          | _ => .err "slice length of a non-pointer value"
  | .subSlice (σ := σ) src lo hi =>
      match evalCopy M state src with
      | .err e => .err e
      | .ok out1 =>
          match out1.values with
          | [.ptrVal base offset extent size tag] =>
              match evalCopy M out1.state lo with
              | .err e => .err e
              | .ok out2 =>
                  match out2.values with
                  | [.word l] =>
                      match evalCopy M out2.state hi with
                      | .err e => .err e
                      | .ok out3 =>
                          match out3.values with
                          | [.word h] =>
                              if h < l || h * bsize σ > extent then
                                .err "sub-slice range out of bounds"
                              else
                                .ok { values := [MemValue.ptrVal base (offset + l * bsize σ)
                                        ((h - l) * bsize σ) size tag]
                                      values_len := rfl
                                      state := out3.state }
                          | _ => .err "sub-slice bound is not a concrete word"
                  | _ => .err "sub-slice bound is not a concrete word"
          | _ => .err "sub-slice of a non-pointer value"
  | .binOp op a b =>
      match evalCopy M state a with
      | .err e => .err e
      | .ok out1 =>
          match out1.values with
          | [.word x] =>
              match evalCopy M out1.state b with
              | .err e => .err e
              | .ok out2 =>
                  match out2.values with
                  | [.word y] =>
                      .ok { values := [MemValue.word (evalBinOp op x y)], values_len := rfl,
                            state := out2.state }
                  | _ => .err "binOp operand is not a concrete word"
          | _ => .err "binOp operand is not a concrete word"
  | .uninit =>
      .ok { values := List.replicate (blockSize τ) MemValue.undef
            values_len := List.length_replicate
            state := state }
  | .ptrCast src =>
      match readCell M state src .ptr "ptr-to-ptr cast" with
      | .error e => .err e
      | .ok (v, perms') =>
          if v == .undef then .err "read of uninitialized memory"
          else .ok { values := [v], values_len := rfl, state := { state with perms := perms' } }
  | .ptrOffset (σ := σ) src delta =>
      match readCell M state src .ptr "pointer offset" with
      | .error e => .err e
      | .ok (.ptrVal base offset extent size tag, perms') =>
          let newOff : Int := (offset : Int) + delta * (bsize σ : Int)
          if newOff < 0 then .err "pointer offset before the allocation base"
          else .ok { values := [MemValue.ptrVal base newOff.toNat extent size tag]
                     values_len := rfl
                     state := { state with perms := perms' } }
      | .ok _ => .err "pointer offset of a non-pointer value"
  | .refSlice kind prot src =>
      match readCell M state src .ptr "slice retag" with
      | .error e => .err e
      | .ok (.ptrVal base offset extent size tag, perms') =>
          match M.ref perms' (base + offset) extent tag kind prot [] with
          | .error e => .err s!"retag failed: {e}"
          | .ok (perms'', newTag) =>
              .ok { values := [MemValue.ptrVal base offset extent size newTag]
                    values_len := rfl
                    state := { state with perms := perms'' } }
      | .ok _ => .err "slice value is not a pointer"
  | .exposeAddr src =>
      match readCell M state src .ptr "ptr-to-int cast" with
      | .error e => .err e
      | .ok (.ptrVal base offset _ _ tag, perms') =>
          .ok { values := [MemValue.word (base + offset)], values_len := rfl
                state := { state with perms := M.expose perms' tag } }
      | .ok _ => .err "ptr-to-int cast of a non-pointer value"
  | .fromExposed src =>
      match readCell M state src (.int B) "int-to-ptr cast" with
      | .error e => .err e
      | .ok (.word n, perms') =>
          let (base, size) := (state.mem.allocOf n).getD (n, 0)
          let off := n - base
          .ok { values := [MemValue.ptrVal base off (size - off) size wildcardTag]
                values_len := rfl
                state := { state with perms := perms' } }
      | .ok _ => .err "int-to-ptr cast of a non-integer value"
  | .ref (τ := σ) kind prot mask src =>
      match resolvePlaceAcc M state src with
      | .error e => .err e
      | .ok (resolved, permsR) =>
          if resolved.addr + bsize σ > resolved.allocBase + resolved.allocSize then
            .err "retag of an out-of-bounds range"
          else
          match M.ref permsR resolved.addr (bsize σ) resolved.tag kind prot (expandMask mask) with
          | .ok (perms', freshTag) =>
              .ok { values := [MemValue.ptrVal resolved.allocBase
                                 (resolved.addr - resolved.allocBase)
                                 (bsize σ) resolved.allocSize freshTag]
                    values_len := rfl
                    state := { state with perms := perms' } }
          | .error e => .err s!"retag failed: {e}"

def doAssign (M : PermissionModel) (state : State M Γ) (dst : Place Γ τ) (rhs : RExpr Γ τ) :
    Result M Γ :=
  match preparePlaceAssign M state dst with
  | .err msg => .err msg
  | .ok s1 =>
  match evalRExpr M s1 rhs with
  | .err msg => .err msg
  | .ok output =>
  match resolvePlaceAcc M output.state dst with
  | .error e => .err e
  | .ok (resolved, permsD) =>
  writeResolvedPlace M { output.state with perms := permsD } resolved output.values

def stepStmt (M : PermissionModel) (state : State M Γ) : Stmt Γ → Result M Γ
  | .halt => .ok state
  | .pushProtectors => .ok { state with perms := M.pushFrame state.perms, pc := state.pc + 1 }
  | .popProtectors =>
      match M.popFrame state.perms with
      | .ok perms' => .ok { state with perms := perms', pc := state.pc + 1 }
      | .error e => .err s!"popProtectors failed: {e}"
  | .assign dst rhs => doAssign M state dst rhs
  | .assignIf discr val dst rhs =>
      match ensureRoot M state dst with
      | .err msg => .err msg
      | .ok s0 =>
      match evalRExpr M s0 (.copy discr) with
      | .err e => .err e
      | .ok output =>
          match output.values with
          | [.word v] =>
              if v == val then doAssign M output.state dst rhs
              else .ok { output.state with pc := output.state.pc + 1 }
          | _ => .err "assignIf discriminant is not a concrete word"
  | .dealloc dst =>
      match evalCopy M state dst with
      | .err e => .err s!"dealloc pointer read failed: {e}"
      | .ok out =>
          match out.values with
          | [.ptrVal base offset _ size tag] =>
              if offset != 0 then
                .err "deallocation of a pointer that is not the beginning of its allocation"
              else
                match M.dealloc out.state.perms base size tag with
                | .error e => .err s!"deallocation failed: {e}"
                | .ok permsD =>
                    -- the bytes become uninit; the bump allocator never
                    -- reuses the range, so dangling pointers keep failing
                    .ok { out.state with perms := permsD,
                                         mem := out.state.mem.write base
                                           (List.replicate size .uninit),
                                         pc := out.state.pc + 1 }
          | _ => .err "dealloc argument is not a pointer value"

def runN (M : PermissionModel) : Nat → State M Γ → Prog Γ → Result M Γ
  | 0, state, _ => .ok state
  | n + 1, state, prog =>
      match prog.get? state.pc with
      | some .halt => .ok state
      | none => .ok state
      | some stmt =>
          match stepStmt M state stmt with
          | .ok state' => runN M n state' prog
          | .err msg => .err msg

end obseq3.mirliteB
