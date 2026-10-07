import obseq3.values
import obseq3.bytelayout

/-!
# mirlite on byte-addressed memory

The source semantics: mirlite's statements and rvalues, the Stacked
Borrows permission model on per-byte stacks, and memory as `bytes.Mem`
(MiniRust-style abstract bytes, provenance on every pointer byte).

Values are `List MemValue`, one per LEAF (scalar or pointer) of the
value's layout. Every size, offset and range comes from a per-local BYTE
LAYOUT (`LayEnv`): integers at their width, 8-byte pointers, aggregates
with padding. The loader supplies the real layouts
(`conformance.toBLayout`); `uniformEnv` gives every integer 8 bytes. A
place's layout is computed statically: a local's from the environment, a
field's by its index path, a deref's from the pointer's pointee.

- a WRITE encodes each value at its leaf's width (a word little-endian
  without provenance — it must fit; a pointer with its provenance on all
  its bytes; `undef` as uninit bytes) and makes the PADDING uninit, as a
  typed copy does in MiniRust;
- a READ decodes each leaf at its scalar type: an integer leaf strips
  provenance, a pointer leaf keeps it only if all its bytes agree, and any
  uninit byte makes the leaf `undef`;
- a pointer value's fields (`base`, `offset`, `extent`, `size`) are in
  bytes; its `extent` travels in the stored provenance until fat pointers
  are two words (see `bytes.Prov.extentB`);
- a pointer without provenance (decoded from integer bytes) becomes a
  degenerate pointer over a zero-sized allocation at its address.
-/

namespace obseq3.mirlite

open obseq3 obseq3.bytes
open obseq3.mirlite (Binding Env MemValue PlaceRes)

/-- The uniform layout's integer width, and a pointer's: 8 bytes. -/
def B : Nat := ptrSizeB

/-- Read one leaf at its scalar type. -/
def decodeV (k : Scalar) (bs : List AbstractByte) : MemValue :=
  match k with
  | .int _ =>
      match decodeInt bs with
      | some w => .word w
      | none => .undef
  | .ptr =>
      match decodePtr bs with
      | some ⟨a, some p⟩ => .ptrVal p.base (a - p.base) p.extentB p.sizeB p.tag
      | some ⟨a, none⟩ => .ptrVal a 0 0 0 wildcardTag
      | none => .undef

/-- Read an 8-byte leaf at `addr`. -/
def readOne (m : bytes.Mem) (addr : Nat) (k : Scalar) : MemValue :=
  decodeV k (m.read addr B)

/-- An 8-byte-leaf UnsafeCell mask, per byte (the uniform layout's). -/
def expandMask (mask : List Bool) : List Bool := mask.flatMap fun b => List.replicate B b

abbrev LayEnv (Γ : Ctx) := Fin Γ.length → BLayout

/-- The uniform layout: every integer and pointer an 8-byte leaf, tuples
    in C layout. -/
def uniformEnv (Γ : Ctx) : LayEnv Γ := fun i => ofLayoutTy (Γ.get i)

/-- The layout reached by a path of field indices. -/
def fieldLayout : BLayout → List Nat → BLayout
  | b, [] => b
  | .tup fs _ _ _, i :: is => fieldLayout (fs.getD i default) is
  | b, _ :: _ => b

/-- The byte offset of a path of field indices. -/
def fieldOffsetB : BLayout → List Nat → Nat
  | _, [] => 0
  | .tup fs os _ _, i :: is => os.getD i 0 + fieldOffsetB (fs.getD i default) is
  | _, _ :: _ => 0

/-- A place's layout, statically: a local's from the environment, a
    field's by its path, a deref's from the pointer's pointee. -/
def placeLayout (L : LayEnv Γ) {τ : LayoutTy} : Place Γ τ → BLayout
  | .local loc => L loc.idx
  | .proj base path => fieldLayout (placeLayout L base) path.indices
  | .deref p =>
      match placeLayout L p with
      | .ptr q => q
      | _ => ofLayoutTy τ

/-- The scalar a one-leaf layout holds (a pointer's own leaf, a word's). -/
def leafKind (l : BLayout) : Scalar := ((l.leaves.head?).map (·.2)).getD (.int B)

/-- A value's bytes at a scalar of `k.sizeB` bytes. -/
def encodeAt (k : Scalar) : MemValue → Except String (List AbstractByte)
  | .undef => .ok (List.replicate k.sizeB .uninit)
  | .word w =>
      if w < 256 ^ k.sizeB then .ok (encodeInt k.sizeB w)
      else .error s!"value {w} does not fit in {k.sizeB} bytes"
  | .ptrVal b o e s t =>
      if b + o < 256 ^ ptrSizeB then
        .ok ((encodePtr ⟨b + o, some { base := b, sizeB := s, tag := t, extentB := e }⟩).take k.sizeB)
      else .error "address does not fit in 64 bits"

/-- Read every leaf of layout `lay` at `addr`. -/
def readL (m : bytes.Mem) (addr : Nat) (lay : BLayout) : List MemValue :=
  lay.leaves.map fun (o, k) => decodeV k (m.read (addr + o) k.sizeB)

/-- Write `vals` to the leaves of `lay` at `addr`: the padding becomes
    uninit. -/
def writeL (m : bytes.Mem) (addr : Nat) (lay : BLayout) (vals : List MemValue) :
    Except String bytes.Mem := do
  if vals.length != lay.leaves.length then
    throw s!"layout mismatch: {vals.length} values for {lay.leaves.length} leaves"
  let buf ← (lay.leaves.zip vals).foldlM (init := List.replicate lay.sizeB AbstractByte.uninit)
    fun buf ((o, k), v) => do
      let bs ← encodeAt k v
      pure (buf.take o ++ bs ++ buf.drop (o + bs.length))
  pure (m.write addr buf)

/-- A per-leaf UnsafeCell mask, per byte: byte `i` takes the bit of the
    leaf starting closest at or below it (padding takes the leaf before
    it). Leaves are in FIELD order, which a reordered `repr(Rust)` struct
    does not keep in address order. -/
def maskBytes (lay : BLayout) (mask : List Bool) : List Bool :=
  (List.range lay.sizeB).map fun i =>
    let below := lay.leaves.zipIdx.filter fun ((o, _), _) => o ≤ i
    match below.foldl (fun best c => match best with
        | none => some c
        | some b => if c.1.1 ≥ b.1.1 then some c else some b) none with
    | some (_, j) => mask.getD j false
    | none => false

/-- An `alloc`'s element layout: the destination pointer's pointee (the
    type's own layout when the destination is not a pointer). Shared with
    the compiler (`compile.lean`). -/
def allocPointee (dstL : BLayout) (σ : LayoutTy) : BLayout :=
  match dstL with
  | .ptr q => q
  | _ => ofLayoutTy σ

/-- Miri checks that an allocation is still live BEFORE any borrow-stack
    check, and reports a use-after-free as such. -/
def freedMsg : String := "memory access failed: the allocation has been freed, so this pointer is dangling"

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

structure EvalOutput (M : PermissionModel) (Γ : Ctx) where
  values : List MemValue
  state  : State M Γ

inductive EvalResult (M : PermissionModel) (Γ : Ctx) where
  | ok (output : EvalOutput M Γ)
  | err (msg : String)

section
variable (M : PermissionModel) (L : LayEnv Γ)

def resolvePlace? (state : State M Γ) {τ : LayoutTy} : Place Γ τ → Option PlaceRes
  | .local loc =>
      match state.env.lookup loc with
      | some binding =>
          some { addr := binding.addr, tag := binding.tag,
                 allocBase := binding.addr, allocSizeB := (L loc.idx).sizeB }
      | none => none
  | .proj base path =>
      match resolvePlace? state base with
      | none => none
      | some res =>
          some { res with addr := res.addr + fieldOffsetB (placeLayout L base) path.indices }
  | .deref ptrPlace =>
      match resolvePlace? state ptrPlace with
      | none => none
      | some ptrRes =>
          match readOne state.mem ptrRes.addr .ptr with
          | .ptrVal base offset _ size tag =>
              some { addr := base + offset, tag := tag, allocBase := base, allocSizeB := size }
          | _ => none

def resolvePlaceAcc (state : State M Γ) {τ : LayoutTy} :
    Place Γ τ → Except String (PlaceRes × M.State)
  | .local loc =>
      match state.env.lookup loc with
      | some binding =>
          .ok ({ addr := binding.addr, tag := binding.tag,
                 allocBase := binding.addr, allocSizeB := (L loc.idx).sizeB }, state.perms)
      | none => .error "place root local not allocated"
  | .proj base path =>
      match resolvePlaceAcc state base with
      | .error e => .error e
      | .ok (res, perms') =>
          .ok ({ res with addr := res.addr + fieldOffsetB (placeLayout L base) path.indices }, perms')
  | .deref ptrPlace =>
      match resolvePlaceAcc state ptrPlace with
      | .error e => .error e
      | .ok (ptrRes, perms') =>
          if state.mem.isFreed ptrRes.allocBase then .error freedMsg
          -- the WHOLE pointer must be in bounds, as for every other typed
          -- read (and the compiled `Load`): a pointer read straddling the
          -- allocation's end is out of bounds
          else if ptrRes.addr < ptrRes.allocBase ∨
             ptrRes.addr + ptrSizeB > ptrRes.allocBase + ptrRes.allocSizeB then
            .error "deref of an out-of-bounds pointer"
          else
          match M.read perms' ptrRes.addr ptrSizeB ptrRes.tag with
          | .error e => .error s!"read access failed: {e}"
          | .ok perms'' =>
              match readOne state.mem ptrRes.addr .ptr with
              | .ptrVal base offset _ size tag =>
                  .ok ({ addr := base + offset, tag := tag,
                         allocBase := base, allocSizeB := size }, perms'')
              | _ => .error "deref of a non-pointer value"

def writeResolvedPlace (state : State M Γ) (dst : PlaceRes) (lay : BLayout)
    (values : List MemValue) : Result M Γ :=
  if state.mem.isFreed dst.allocBase then .err freedMsg
  else if dst.addr + lay.sizeB > dst.allocBase + dst.allocSizeB then
    .err "write out of bounds"
  else
    match M.useMut state.perms dst.addr lay.sizeB dst.tag with
    | .ok perms' =>
        match writeL state.mem dst.addr lay values with
        | .ok mem' => .ok { state with perms := perms', mem := mem', pc := state.pc + 1 }
        | .error e => .err e
    | .error e => .err s!"write access failed: {e}"

def allocateBase (state : State M Γ) {τ : LayoutTy} (loc : Local Γ τ) : Result M Γ :=
  let lay := L loc.idx
  let (addr, mem') := state.mem.allocate lay.sizeB (max 1 lay.alignB)
  match M.own state.perms addr lay.sizeB with
  | .error e => .err s!"allocation failed: {e}"
  | .ok (permsOwned, tag) =>
      let env' := state.env.set loc { addr := addr, tag := tag }
      .ok { state with env := env', mem := mem', perms := permsOwned }

def allocateRoot (state : State M Γ) {τ : LayoutTy} : Place Γ τ → Result M Γ
  | .local loc => allocateBase M L state loc
  | .proj base _ => allocateRoot state base
  | .deref _ => .err "destination pointer place not allocated or not a pointer"

def preparePlaceAssign (state : State M Γ) {τ : LayoutTy} (dst : Place Γ τ) : Result M Γ :=
  match resolvePlace? M L state dst with
  | some _ => .ok state
  | none => allocateRoot M L state dst

def ensureRoot (state : State M Γ) {τ : LayoutTy} : Place Γ τ → Result M Γ
  | .local loc =>
      match state.env.lookup loc with
      | some _ => .ok state
      | none => allocateBase M L state loc
  | .proj base _ => ensureRoot state base
  | .deref ptrPlace => ensureRoot state ptrPlace

def evalCopy (state : State M Γ) {τ : LayoutTy} (src : Place Γ τ) : EvalResult M Γ :=
  let lay := placeLayout L src
  match resolvePlaceAcc M L state src with
  | .error e => .err e
  | .ok (resolved, permsR) =>
      if state.mem.isFreed resolved.allocBase then .err freedMsg
      else if resolved.addr + lay.sizeB > resolved.allocBase + resolved.allocSizeB then
        .err "copy of an out-of-bounds range"
      else
      match M.read permsR resolved.addr lay.sizeB resolved.tag with
      | .error e => .err s!"read access failed: {e}"
      | .ok perms' =>
          let vals := readL state.mem resolved.addr lay
          if vals.any (fun v => v == .undef) then .err "read of uninitialized memory"
          else .ok { values := vals, state := { state with perms := perms' } }

def evalAllocLen (state : State M Γ) : AllocLen Γ → Except String (Nat × State M Γ)
  | .const n => .ok (n, state)
  | .fromPlace p =>
      match evalCopy M L state p with
      | .err e => .error e
      | .ok out =>
          match out.values with
          | [.word n] => .ok (n, out.state)
          | _ => .error "allocation size is not a concrete word"

/-- One leaf read through a place, for the pointer/integer rvalues:
    resolve for access, bounds, SB read, the leaf decoded at its kind. -/
def readCell (state : State M Γ) {τ : LayoutTy} (src : Place Γ τ) (what : String) :
    Except String (MemValue × M.State) :=
  let k := leafKind (placeLayout L src)
  match resolvePlaceAcc M L state src with
  | .error e => .error e
  | .ok (resolved, permsR) =>
      if state.mem.isFreed resolved.allocBase then .error freedMsg
      else if resolved.addr + k.sizeB > resolved.allocBase + resolved.allocSizeB then
        .error s!"{what} of an out-of-bounds place"
      else
      match M.read permsR resolved.addr k.sizeB resolved.tag with
      | .error e => .error s!"read access failed: {e}"
      -- exactly the leaf's bytes (a narrow integer is not 8 bytes wide)
      | .ok perms' => .ok (decodeV k (state.mem.read resolved.addr k.sizeB), perms')

/-- `readCell` decoding at a given scalar `k` instead of the place's own
    leaf kind (a pointer's bytes read as an integer). -/
def readCellAs (state : State M Γ) {τ : LayoutTy} (src : Place Γ τ) (k : Scalar) (what : String) :
    Except String (MemValue × M.State) :=
  match resolvePlaceAcc M L state src with
  | .error e => .error e
  | .ok (resolved, permsR) =>
      if state.mem.isFreed resolved.allocBase then .error freedMsg
      else if resolved.addr + k.sizeB > resolved.allocBase + resolved.allocSizeB then
        .error s!"{what} of an out-of-bounds place"
      else
      match M.read permsR resolved.addr k.sizeB resolved.tag with
      | .error e => .error s!"read access failed: {e}"
      | .ok perms' => .ok (decodeV k (state.mem.read resolved.addr k.sizeB), perms')

/-- The pointee layout of a pointer place. -/
def pointeeLayout {σ : LayoutTy} (p : Place Γ (LayoutTy.PtrL σ)) : BLayout :=
  match placeLayout L p with
  | .ptr q => q
  | _ => ofLayoutTy σ

/-- Evaluate an rvalue; `dstL` is the destination's layout (an `alloc`'s
    pointee, an `uninit`'s leaves). -/
def evalRExpr (state : State M Γ) (dstL : BLayout) {τ : LayoutTy} (expr : RExpr Γ τ) :
    EvalResult M Γ :=
  match expr with
  | .constInit value => .ok { values := [MemValue.word value], state := state }
  | .copy src => evalCopy M L state src
  | .move src =>
      let lay := placeLayout L src
      match resolvePlaceAcc M L state src with
      | .error e => .err e
      | .ok (resolved, permsR) =>
          if state.mem.isFreed resolved.allocBase then .err freedMsg
          else if resolved.addr + lay.sizeB > resolved.allocBase + resolved.allocSizeB then
            .err "move of an out-of-bounds range"
          else
          match M.ref permsR resolved.addr lay.sizeB resolved.tag .Mut false [] with
          | .error e => .err s!"move retag failed: {e}"
          | .ok (permsM, tmpTag) =>
          match M.read permsM resolved.addr lay.sizeB tmpTag with
          | .error e => .err s!"read access failed: {e}"
          | .ok permsRd =>
          match M.die permsRd resolved.addr lay.sizeB tmpTag with
          | .error e => .err s!"move retire failed: {e}"
          | .ok perms' =>
              let vals := readL state.mem resolved.addr lay
              if vals.any (fun v => v == .undef) then .err "read of uninitialized memory"
              else .ok { values := vals, state := { state with perms := perms' } }
  | .alloc (τ := σ) len =>
      let pointee := allocPointee dstL σ
      match evalAllocLen M L state len with
      | .error e => .err e
      | .ok (n, state) =>
          let units := n * pointee.sizeB
          let (base, mem') := state.mem.allocate units (max 1 pointee.alignB)
          match M.own state.perms base units with
          | .error e => .err s!"heap allocation failed: {e}"
          | .ok (perms', tag) =>
              .ok { values := [MemValue.ptrVal base 0 units units tag],
                    state := { state with mem := mem', perms := perms' } }
  | .sliceLen src =>
      let elem := pointeeLayout L src
      match evalCopy M L state src with
      | .err e => .err e
      | .ok out =>
          match out.values with
          | [.ptrVal _ _ extent _ _] =>
              .ok { values := [MemValue.word (extent / elem.sizeB)], state := out.state }
          | _ => .err "slice length of a non-pointer value"
  | .subSlice src lo hi =>
      let esz := (pointeeLayout L src).sizeB
      match evalCopy M L state src with
      | .err e => .err e
      | .ok out1 =>
          match out1.values with
          | [.ptrVal base offset extent size tag] =>
              match evalCopy M L out1.state lo with
              | .err e => .err e
              | .ok out2 =>
                  match out2.values with
                  | [.word l] =>
                      match evalCopy M L out2.state hi with
                      | .err e => .err e
                      | .ok out3 =>
                          match out3.values with
                          | [.word h] =>
                              if h < l || h * esz > extent then
                                .err "sub-slice range out of bounds"
                              else
                                .ok { values := [MemValue.ptrVal base (offset + l * esz)
                                        ((h - l) * esz) size tag],
                                      state := out3.state }
                          | _ => .err "sub-slice bound is not a concrete word"
                  | _ => .err "sub-slice bound is not a concrete word"
          | _ => .err "sub-slice of a non-pointer value"
  | .addrOf loc path =>
      match state.env.lookup loc with
      | none => .err "place root local not allocated"
      | some b =>
          .ok { values := [MemValue.ptrVal b.addr
                  (fieldOffsetB (placeLayout L (.local loc)) path.indices)
                  (placeLayout L (.proj (.local loc) path)).sizeB (L loc.idx).sizeB b.tag],
                state := state }
  | .ptrOffsetBy (t := t) src idx inbounds =>
      let stride := (pointeeLayout L src).sizeB
      match evalCopy M L state src with
      | .err e => .err e
      | .ok out1 =>
          match out1.values with
          | [.ptrVal base offset extent size tag] =>
              match evalCopy M L out1.state idx with
              | .err e => .err e
              | .ok out2 =>
                  match out2.values with
                  | [.word w] =>
                      match out2.state.mem.offsetPtr inbounds base offset size
                          (t.toInt w * (stride : Int)) with
                      | .error e => .err e
                      | .ok newOff =>
                          .ok { values := [MemValue.ptrVal base newOff extent size tag],
                                state := out2.state }
                  | _ => .err "pointer offset by a non-word"
          | _ => .err "pointer offset of a non-pointer value"
  | .binOp op a b =>
      match evalCopy M L state a with
      | .err e => .err e
      | .ok out1 =>
          match out1.values with
          | [.word x] =>
              match evalCopy M L out1.state b with
              | .err e => .err e
              | .ok out2 =>
                  match out2.values with
                  | [.word y] =>
                      match binOpUB op x y with
                      | some e => .err e
                      | none =>
                      .ok { values := [MemValue.word (evalBinOp op x y)], state := out2.state }
                  | _ => .err "binOp operand is not a concrete word"
          | _ => .err "binOp operand is not a concrete word"
  | .uninit => .ok { values := List.replicate dstL.leaves.length MemValue.undef, state := state }
  | .ptrCast src =>
      match readCell M L state src "ptr-to-ptr cast" with
      | .error e => .err e
      | .ok (v, perms') =>
          if v == .undef then .err "read of uninitialized memory"
          else .ok { values := [v], state := { state with perms := perms' } }
  | .ptrOffset src delta inbounds =>
      let stride := (pointeeLayout L src).sizeB
      match readCell M L state src "pointer offset" with
      | .error e => .err e
      | .ok (.ptrVal base offset extent size tag, perms') =>
          match state.mem.offsetPtr inbounds base offset size (delta * (stride : Int)) with
          | .error e => .err e
          | .ok newOff =>
              .ok { values := [MemValue.ptrVal base newOff extent size tag],
                    state := { state with perms := perms' } }
      | .ok _ => .err "pointer offset of a non-pointer value"
  | .refSlice kind prot src =>
      match readCell M L state src "slice retag" with
      | .error e => .err e
      | .ok (.ptrVal base offset extent size tag, perms') =>
          if state.mem.isFreed base then .err freedMsg else
          match M.ref perms' (base + offset) extent tag kind prot [] with
          | .error e => .err s!"retag failed: {e}"
          | .ok (perms'', newTag) =>
              .ok { values := [MemValue.ptrVal base offset extent size newTag],
                    state := { state with perms := perms'' } }
      | .ok _ => .err "slice value is not a pointer"
  | .addr src =>
      -- the pointer's bytes decoded as an integer of the same width
      match readCellAs M L state src (.int (leafKind (placeLayout L src)).sizeB)
          "ptr-to-int transmute" with
      | .error e => .err e
      | .ok (v, perms') =>
          if v == .undef then .err "read of uninitialized memory"
          else .ok { values := [v], state := { state with perms := perms' } }
  | .exposeAddr src =>
      match readCell M L state src "ptr-to-int cast" with
      | .error e => .err e
      | .ok (.ptrVal base offset _ _ tag, perms') =>
          match M.expose perms' tag with
          | .error e => .err s!"ptr-to-int cast failed: {e}"
          | .ok perms'' =>
              .ok { values := [MemValue.word (base + offset)],
                    state := { state with perms := perms'' } }
      | .ok _ => .err "ptr-to-int cast of a non-pointer value"
  | .fromExposed src =>
      match readCell M L state src "int-to-ptr cast" with
      | .error e => .err e
      | .ok (.word n, perms') =>
          let (base, size) := (state.mem.allocOf n).getD (n, 0)
          let off := n - base
          .ok { values := [MemValue.ptrVal base off (size - off) size wildcardTag],
                state := { state with perms := perms' } }
      | .ok _ => .err "int-to-ptr cast of a non-integer value"
  | .ref kind prot mask src =>
      let lay := placeLayout L src
      match resolvePlaceAcc M L state src with
      | .error e => .err e
      | .ok (resolved, permsR) =>
          -- a retag of zero bytes performs no access, so it needs no live,
          -- in-bounds memory (Miri: zero-sized accesses are always allowed)
          if lay.sizeB != 0 && state.mem.isFreed resolved.allocBase then .err freedMsg
          else if lay.sizeB != 0 &&
              resolved.addr + lay.sizeB > resolved.allocBase + resolved.allocSizeB then
            .err "retag of an out-of-bounds range"
          else
          match M.ref permsR resolved.addr lay.sizeB resolved.tag kind prot (maskBytes lay mask) with
          | .ok (perms', freshTag) =>
              .ok { values := [MemValue.ptrVal resolved.allocBase
                                 (resolved.addr - resolved.allocBase)
                                 lay.sizeB resolved.allocSizeB freshTag],
                    state := { state with perms := perms' } }
          | .error e => .err s!"retag failed: {e}"

def doAssign (state : State M Γ) {τ : LayoutTy} (dst : Place Γ τ) (rhs : RExpr Γ τ) :
    Result M Γ :=
  let dstL := placeLayout L dst
  match preparePlaceAssign M L state dst with
  | .err msg => .err msg
  | .ok s1 =>
  match evalRExpr M L s1 dstL rhs with
  | .err msg => .err msg
  | .ok output =>
  match resolvePlaceAcc M L output.state dst with
  | .error e => .err e
  | .ok (resolved, permsD) =>
  writeResolvedPlace M { output.state with perms := permsD } resolved dstL output.values

def stepStmt (state : State M Γ) : Stmt Γ → Result M Γ
  | .halt => .ok state
  | .pushProtectors => .ok { state with perms := M.pushFrame state.perms, pc := state.pc + 1 }
  | .popProtectors =>
      match M.popFrame state.perms with
      | .ok perms' => .ok { state with perms := perms', pc := state.pc + 1 }
      | .error e => .err s!"popProtectors failed: {e}"
  | .assign dst rhs => doAssign M L state dst rhs
  | .assignIf discr val dst rhs =>
      match ensureRoot M L state dst with
      | .err msg => .err msg
      | .ok s0 =>
      match evalCopy M L s0 discr with
      | .err e => .err e
      | .ok output =>
          match output.values with
          | [.word v] =>
              if v == val then doAssign M L output.state dst rhs
              else .ok { output.state with pc := output.state.pc + 1 }
          | _ => .err "assignIf discriminant is not a concrete word"
  | .check discr vals member =>
      match evalCopy M L state discr with
      | .err e => .err e
      | .ok output =>
          match output.values with
          | [.word v] =>
              if vals.contains v == member then .ok { output.state with pc := output.state.pc + 1 }
              else .err "check failed"
          | _ => .err "check: the place is not a concrete word"
  | .dealloc dst =>
      match evalCopy M L state dst with
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
                    let mem := out.state.mem.write base (List.replicate size .uninit)
                    .ok { out.state with perms := permsD,
                                         mem := { mem with freed := base :: mem.freed },
                                         pc := out.state.pc + 1 }
          | _ => .err "dealloc argument is not a pointer value"

def runN : Nat → State M Γ → Prog Γ → Result M Γ
  | 0, state, _ => .ok state
  | n + 1, state, prog =>
      match prog.get? state.pc with
      | some .halt => .ok state
      | none => .ok state
      | some stmt =>
          match stepStmt M L state stmt with
          | .ok state' => runN n state' prog
          | .err msg => .err msg

end

end obseq3.mirlite
