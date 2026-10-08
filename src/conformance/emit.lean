import conformance.ullbc_ast
import conformance.certificate
import obseq3.types
import obseq3.bytelayout

/-!
The lowering state and its statement emitters: `LowerSt`, `emitAssign`,
the seam retags (`emitSeamCopy`, `emitSeamBind`) and their helpers. The
std shims (`stdlite.lean`) and the block walker (`lowering.lean`) build
on these; the design notes for the whole lowering are in `lowering.lean`.
-/

namespace conformance


/-- One part of a parsed `format_args!` template: a literal piece (its
    bytes), or a placeholder with default options formatting argument
    `arg`, of type `ty`, with Debug (`debug`) or Display; `target` is the
    tracker's root key of the place the argument points at, when known. -/
inductive FmtPart
| lit (bytes : List Nat)
| hole (arg : Nat) (ty : UTy) (debug : Bool) (target : Option (Nat × List Nat))
deriving Repr, BEq, Inhabited

/-- A lowered program: one global local space, straight-line statements.
    `pushProt`/`popProt` bracket an inlined call's protector frame;
    `check` is a runtime check (a certificate's arm or variant, an
    assumption): stuck unless the word at `discr` is in `vals` exactly
    when `member`;
    `alloc`/`dealloc` come from the heap shims; `alloc`'s `n` counts
    POINTEES of `dst` (bytes for a `*mut u8`), `none` meaning one
    (`Box::new`). -/
inductive LStmt
| assign (dst : UPlace) (rv : URvalue) (line : Nat)
| alloc (dst : UPlace) (n : Option UOperand) (line : Nat)
| dealloc (ptr : UPlace) (line : Nat)
| check (discr : UPlace) (vals : List Nat) (member : Bool) (line : Nat)
| pushProt (line : Nat)
| popProt (line : Nat)
deriving Repr, BEq, Inhabited

def LStmt.line : LStmt → Nat
  | .assign _ _ l => l
  | .alloc _ _ l => l
  | .dealloc _ l => l
  | .check _ _ _ l => l
  | .pushProt l => l
  | .popProt l => l

structure LProg where
  locals : List UTy
  stmts : List LStmt
  stats : CertStats := {}
deriving Repr, Inhabited

/-- A constant-tracking key: a rebased local and a path of tuple fields
    into it (`[]` = the whole local, which is then a word). -/
abbrev ConstKey := Nat × List Nat

structure LowerSt where
  locals : List UTy
  out : List LStmt   -- reversed
  fnPtrs : List (Nat × Nat) := []   -- rebased local ↦ fun defId (reified fn ptrs)
  constVals : List (ConstKey × Nat) := []  -- known constant words (index resolution, T1 folding)
  refOf : List (ConstKey × UPlace) := []   -- a pointer-holding place ↦ the place it was taken from
  -- places holding a pointer into a HEAP block (a fresh allocation's, or
  -- copied from one): a write through one lands in no local, so it
  -- changes no tracked constant (`trackAssign`)
  heapPtrs : List ConstKey := []
  -- `format!` (stdlite): the static meaning of the words the model stores
  -- in an `fmt::rt::Argument` (an index into `fmtArgTys`: the argument's
  -- type and Debug or Display) and in an `fmt::Arguments` (an index into
  -- `fmtSpecs`: the parsed template, each placeholder resolved)
  fmtArgTys : List (UTy × Bool × Option ConstKey) := []
  fmtSpecs : List (List FmtPart) := []
  -- certificate-guided lowering (none = the straight-line-only seam)
  cert : Option CertCursor := none
  certBad : Nat := 0     -- scratch usize local the checks poison
  certTmp : Nat := 0     -- scratch usize local the checks read into
  halted : Bool := false -- the certificate's UB/panic prefix ended here
  -- places MOVED OUT (local, field path): a `Drop` of such a place, or of
  -- a place inside it, does nothing; assigning a place re-initialises it
  moved : List ConstKey := []

/-- The place an operand reads, when it reads one. -/
def operandPlace? : UOperand → Option UPlace
  | .copy p => some p
  | .move p => some p
  | _ => none

/-- The local and tuple-field path of a projection-free-of-deref place. -/
def fieldPath? (p : UPlace) : Option ConstKey :=
  match p.root with
  | .global _ => none
  | .local l =>
      let path? : Option (List Nat) := p.projs.mapM fun pr =>
        match pr with
        | .field i => some i
        | _ => none
      path?.map (l, ·)

def constLookup (st : LowerSt) (k : ConstKey) : Option Nat :=
  st.constVals.lookup k

/-- Forget every constant that an assignment to `(l, path)` may change:
    the key itself, its sub-fields, and the aggregates containing it. -/
def killConst (st : LowerSt) (k : ConstKey) : LowerSt :=
  { st with constVals := st.constVals.filter fun (k', _) =>
      !(k'.1 == k.1 && (k.2.isPrefixOf k'.2 || k'.2.isPrefixOf k.2)) }

/-- Forget the constants AND the tracked references an assignment to
    `(l, path)` may change. -/
def killKey (st : LowerSt) (k : ConstKey) : LowerSt :=
  let rel : ConstKey → Bool := fun k' => k'.1 == k.1 && (k.2.isPrefixOf k'.2 || k'.2.isPrefixOf k.2)
  { st with constVals := st.constVals.filter (fun (k', _) => !rel k'),
            refOf := st.refOf.filter (fun (k', _) => !rel k'),
            heapPtrs := st.heapPtrs.filter (fun k' => !rel k') }

def killAllConsts (st : LowerSt) : LowerSt :=
  { st with constVals := [], refOf := [], heapPtrs := [] }

/-- The root-local key a place denotes, following tracked references
    through its derefs (`*r` where `r := &p` denotes `p`). `none` when a
    deref goes through an untracked pointer. -/
partial def resolveKey (st : LowerSt) (fuel : Nat) (p : UPlace) : Option ConstKey :=
  match fuel, p.root with
  | 0, _ => none
  | _, .global _ => none
  | fuel + 1, .local l =>
      let rec go (k : ConstKey) : List UProj → Option ConstKey
        | [] => some k
        | .field i :: rest => go (k.1, k.2 ++ [i]) rest
        | .deref :: rest =>
            match st.refOf.lookup k with
            | some target =>
                match resolveKey st fuel target with
                | some k' => go k' rest
                | none => none
            | none => none
        | .index _ :: _ => none
        | .ptrMetadata :: _ => none   -- metadata is not a tracked word
      go (l, []) p.projs

def rebaseProj (off : Nat) : UProj → UProj
  | .index (.fromLocal n) => .index (.fromLocal (n + off))
  | pr => pr

def rebasePlace (off : Nat) (p : UPlace) : UPlace :=
  let projs := p.projs.map (rebaseProj off)
  match p.root with
  | .local n => { p with root := .local (n + off), projs }
  | .global _ => { p with projs }

def rebaseOperand (off : Nat) : UOperand → UOperand
  | .copy p => .copy (rebasePlace off p)
  | .move p => .move (rebasePlace off p)
  | op => op

def rebaseRvalue (off : Nat) : URvalue → URvalue
  | .use op => .use (rebaseOperand off op)
  | .move p => .move (rebasePlace off p)
  | .ref kind prot p => .ref kind prot (rebasePlace off p)
  | .aggregate v ops => .aggregate v (ops.map (rebaseOperand off))
  | .exposeAddr p => .exposeAddr (rebasePlace off p)
  | .addr p => .addr (rebasePlace off p)
  | .fromExposed p => .fromExposed (rebasePlace off p)
  | .ptrOffset p d ib => .ptrOffset (rebasePlace off p) d ib
  | .ptrOffsetBy p i ib => .ptrOffsetBy (rebasePlace off p) (rebasePlace off i) ib
  | .addrOf p => .addrOf (rebasePlace off p)
  | .rawField p steps => .rawField (rebasePlace off p) steps
  | .refSlice kind prot p => .refSlice kind prot (rebasePlace off p)
  | .sliceLen p => .sliceLen (rebasePlace off p)
  | .subSlice p lo hi =>
      .subSlice (rebasePlace off p) (rebaseOperand off lo) (rebaseOperand off hi)
  | .binOp op t a b => .binOp op t (rebaseOperand off a) (rebaseOperand off b)
  | .discriminant p => .discriminant (rebasePlace off p)
  | .fnRef fid => .fnRef fid
  | .uninit => .uninit
  | .unsupported d => .unsupported d

/-- The pointee place of a pointer-holding place. -/
def pointee (p : UPlace) : UPlace :=
  { p with projs := p.projs ++ [.deref] }

def checkOperand (line : Nat) : UOperand → Except String Unit
  | .unsupported d => .error s!"unsupported: {d} (line {line})"
  | _ => .ok ()

def fld (p : UPlace) (i : Nat) : UPlace :=
  { p with projs := p.projs ++ [.field i] }

def pushOut (st : LowerSt) (s : LStmt) : LowerSt :=
  { st with out := s :: st.out }

/-- Lines ≥ this mark certificate checks; ≥ 2× mark the poison at the end
    of a UB/panic prefix; ≥ 3× a lowering ASSUMPTION (`emitAssume`). -/
def certLineBase : Nat := 1000000

/-- The tracker's pseudo-field holding a slice's length (in elements) when
    the lowering knows it: a string literal's (`materialiseStr`), carried
    by copies and reborrows. A key `(l, path ++ [lenField])`: being below
    the slice's own key, it is killed with it. -/
def lenField : Nat := 1000000

def natLocal (i : Nat) : UPlace := { root := .local i, projs := [], ty := .nat }

/-- A lowering assumption, checked when the program runs: the word at `ok`
    must be 1 (a shim chose its output's shape from it — `format!`'s digit
    counts, its unescaped strings). A `check ok ∈ [1]`, on a line the
    harness reports as a failed assumption, never as a program verdict. -/
def emitAssume (st : LowerSt) (line : Nat) (ok : UPlace) : LowerSt :=
  pushOut st (.check ok [1] true (3 * certLineBase + line))

/-- The end of a UB/panic certificate prefix: mirlite must have failed
    before reaching this; reaching it is the distinct verdict
    `certExhausted`. -/
def emitPoison (st : LowerSt) (line : Nat) : LowerSt :=
  let bad := natLocal st.certBad
  let tmp := natLocal st.certTmp
  let l := 2 * certLineBase + line
  let st := pushOut st (.assign bad .uninit l)
  { pushOut st (.assign tmp (.use (.copy bad)) l) with halted := true }

/-! ## Initialisation tracking and Box drop glue (2026-10-01)

Built MIR emits a `Drop` for every place with drop glue that goes out of
scope or is overwritten, and leaves it to drop elaboration to skip the
moved-out ones. The lowering walks ONE path, so whether a place is still
initialised there is static: a `move` operand of a whole local or field
path moves it out, an assignment (or a call writing its destination)
re-initialises it. -/

def keyPrefix (k k' : ConstKey) : Bool := k.1 == k'.1 && k.2.isPrefixOf k'.2

/-- Moved out: the place itself or a place enclosing it was moved. -/
def isMoved (st : LowerSt) (p : UPlace) : Bool :=
  match fieldPath? p with
  | some k => st.moved.any (keyPrefix · k)
  | none => false

def markMoved (st : LowerSt) (p : UPlace) : LowerSt :=
  match fieldPath? p with
  | some k => { st with moved := k :: st.moved }
  | none => st

/-- Writing `p` initialises it and everything inside it. -/
def markInit (st : LowerSt) (p : UPlace) : LowerSt :=
  match fieldPath? p with
  | some k => { st with moved := st.moved.filter (fun k' => !keyPrefix k k') }
  | none => st

/-- The places an rvalue moves out of. -/
def URvalue.movedPlaces : URvalue → List UPlace
  | .use (.move p) | .move p => [p]
  | .aggregate _ ops => ops.filterMap fun o => match o with | .move p => some p | _ => none
  | _ => []

def markMovedOps (st : LowerSt) (ops : List UOperand) : LowerSt :=
  ops.foldl (fun st o => match o with | .move p => markMoved st p | _ => st) st

/-- A Box or a Vec somewhere in the value itself (not behind a pointer):
    heap memory its drop glue frees. -/
partial def containsBox : UTy → Bool
  | .boxT _ | .vecT _ => true
  | .tup tys | .structT tys _ => tys.any containsBox
  | .enum vs => vs.any (·.any containsBox)
  | .cell t => containsBox t
  | _ => false

/-- Resolve array-index projections to static field indices using the
    tracked constant values of index locals. -/
def resolveIdxPlace (st : LowerSt) (line : Nat) (p : UPlace) : Except String UPlace := do
  let projs ← p.projs.mapM fun pr =>
    match pr with
    | .index (.const n) => pure (UProj.field n)
    | .index (.fromLocal l) =>
        match constLookup st (l, []) with
        | some n => pure (UProj.field n)
        | none => throw s!"unsupported: runtime array index (line {line})"
    | .index (.unsupported d) => throw s!"unsupported: array index: {d} (line {line})"
    | pr => pure pr
  return { p with projs }

def resolveIdxOperand (st : LowerSt) (line : Nat) : UOperand → Except String UOperand
  | .copy p => do return .copy (← resolveIdxPlace st line p)
  | .move p => do return .move (← resolveIdxPlace st line p)
  | op => pure op

/-- Statically-known integer value of an operand (consts, or const-tracked
    plain locals). -/
def constOfPlace (st : LowerSt) (p : UPlace) : Option Int :=
  match resolveKey st 32 p with
  | some k => (constLookup st k).map Int.ofNat
  | none => none

def constOf (st : LowerSt) : UOperand → Option Int
  | .const n => some (Int.ofNat n)
  | .constNeg n _ => some (-(Int.ofNat n))
  | .copy p => constOfPlace st p
  | .move p => constOfPlace st p
  | _ => none

/-- A type's BYTE layout (x86_64): an integer at its width (`bool` 1,
    `char` 4), a model word 8, every pointer 8 (pointee kept for strides
    and extents), a struct at rustc's own field offsets when Charon reports
    its layout (2026-10-02; `repr(Rust)` may reorder fields), a tuple — a
    builtin, which Charon gives no layout — and a layout-less struct in C
    layout (rustc may reorder a tuple: documented deviation), and an enum as the MODEL lays it out: an
    8-byte discriminant, then the longest variant's fields (the cell
    layout's shape, so values line up leaf for leaf). -/
partial def toBLayout : UTy → obseq3.bytes.BLayout
  | .nat => .int 8
  | .int t => .int (max 1 (t.bits / 8))
  | .ref _ i | .raw _ i | .boxT i => .ptr (toBLayout i)
  | .vecT e => toBLayout (vecHeader e)
  | .slice _ _ e => .ptr (toBLayout e)
  | .sliceData e => toBLayout e
  | .cell t => toBLayout t
  | .structT tys (some l) =>
      -- rustc's own layout (Charon): `repr(Rust)` fields reordered/packed
      .tup (tys.map toBLayout) l.offsetsB l.sizeB (max 1 l.alignB)
  | .tup tys | .structT tys none => obseq3.bytes.reprC (tys.map toBLayout)
  | .enum vs => obseq3.bytes.reprC (.int 8 :: (longestVariant vs).map toBLayout)
  | .unsupported _ => .int 8

/-- A type's size in BYTES (`size_of`, `Layout::new`, `Layout::for_value`). -/
def sizeB (t : UTy) : Nat := (toBLayout t).sizeB

/-- Drop the value at `p`, as far as Boxes and Vecs go: a Box drops its contents and
    then frees its allocation through its own pointer (std's
    `<Box as Drop>::drop`: `if layout.size() != 0 { deallocate }`); a tuple
    or struct drops its fields in order; everything else has no drop glue
    the model needs. With a certificate, each Box drop must be the one
    Miri made next in this frame (`consumeDrop`). -/
partial def emitDropGlue (st : LowerSt) (line : Nat) (p : UPlace) : Except String LowerSt := do
  if st.halted || isMoved st p || !containsBox p.ty then return st
  match p.ty with
  | .boxT inner =>
      let st ← emitDropGlue st line { pointee p with ty := inner }
      match st.cert with
      | some c =>
          -- past the end of a UB/panic certificate (nothing left of it at
          -- all): Miri never got here, and mirlite must fail first
          if c.cert.outcome != .ok && c.allConsumed then
            return emitPoison st line
          let c ← c.consumeDrop s!"the frame at line {line}"
          let st := { st with cert := some c }
          let st := if uSize inner == 0 then st else pushOut st (.dealloc p line)
          return markMoved st p
      | none =>
          let st := if uSize inner == 0 then st else pushOut st (.dealloc p line)
          return markMoved st p
  | .tup tys | .structT tys _ =>
      tys.zipIdx.foldlM (fun st (t, i) => emitDropGlue st line { fld p i with ty := t }) st
  | .cell t => emitDropGlue st line { p with ty := t }
  | .vecT elem =>
      -- std's drop glue: a protected `&mut` retag of the header (the glue's
      -- and `Drop::drop`'s fn-entry retags), `<Vec as Drop>::drop` dropping
      -- the elements (`drop_in_place` of `[T]`: no glue, no retag, for an
      -- element without one), then `RawVec`'s drop freeing the buffer
      -- through the stored pointer when it holds bytes. The capacity must
      -- be known statically.
      if containsBox elem then
        throw s!"unsupported: drop of a Vec whose elements have drop glue (line {line})"
      let some cap := constOfPlace st { fld p 1 with ty := .nat }
        | -- unlowerable; but past the end of a UB/panic certificate
          -- (nothing left of it) Miri may never have got here, so the
          -- model must fail first (`emitPoison` reports it otherwise).
          -- Not a test for EVERY Vec drop: unlike a Box's, a Vec's drop
          -- is no certificate event, so the certificate does not say
          -- whether Miri reached it
          match st.cert with
          | some c =>
              if c.cert.outcome != .ok && c.allConsumed then return emitPoison st line
              else throw s!"unsupported: drop of a Vec with a runtime capacity (line {line})"
          | none => throw s!"unsupported: drop of a Vec with a runtime capacity (line {line})"
      let t := st.locals.length
      let st := { st with locals := st.locals ++ [.ref true (.vecT elem)] }
      let tmp : UPlace := { root := .local t, projs := [], ty := .ref true (.vecT elem) }
      let st := pushOut st (.pushProt line)
      let st := pushOut st (.assign tmp (.ref .mut true p) line)
      let st := if cap.toNat * sizeB elem == 0 then st
        else pushOut st (.dealloc { fld (pointee tmp) 0 with ty := .raw true elem } line)
      return markMoved (pushOut st (.popProt line)) p
  | .enum _ => .error s!"unsupported: drop of an enum holding a Box (line {line})"
  | _ => return st

/-- The byte offset of the field path `steps` in a value of type `t`, at
    the offsets `toBLayout` gives (cells are transparent). -/
partial def fieldStepsOffsetB (t : UTy) : List Nat → Option Nat
  | [] => some 0
  | i :: rest =>
      match t, toBLayout t with
      | .cell u, _ => fieldStepsOffsetB u (i :: rest)
      | .tup tys, .tup _ offs _ _ | .structT tys _, .tup _ offs _ _ => do
          let o ← offs[i]?
          let f ← tys[i]?
          let r ← fieldStepsOffsetB f rest
          pure (o + r)
      | _, _ => none

def UIntTy.toIntTy (t : UIntTy) : obseq3.IntTy := ⟨t.bits, t.signed⟩

/-- The obseq3 operation an ULLBC op denotes at integer type `t`, as MIR
    defines it (Charon keeps MIR's ops one to one; an op with an overflow
    mode renders `Add.Wrap`/`Add.UB`). `AddChecked` (MIR `AddWithOverflow`)
    denotes its WRAPPED result here; its flag is `overflowOpOf`. `Panic`
    modes only exist under Charon's `--reconstruct-fallible-operations`,
    which the corpus does not use. -/
def binOpOf (op : String) (t : obseq3.IntTy) : Option obseq3.BinOp :=
  match op with
  | "Add.Wrap" | "AddChecked" => some (.add t)
  | "Sub.Wrap" | "SubChecked" => some (.sub t)
  | "Mul.Wrap" | "MulChecked" => some (.mul t)
  | "Add.UB" => some (.addUB t) | "Sub.UB" => some (.subUB t) | "Mul.UB" => some (.mulUB t)
  | "Div.UB" | "Div.Wrap" => some (.div t)
  | "Rem.UB" | "Rem.Wrap" => some (.rem t)
  | "BitAnd" => some (.bitAnd t) | "BitOr" => some (.bitOr t) | "BitXor" => some (.bitXor t)
  | "Shl.Wrap" => some (.shl t) | "Shl.UB" => some (.shlUB t)
  | "Shr.Wrap" => some (.shr t) | "Shr.UB" => some (.shrUB t)
  | "Lt" => some (.lt t) | "Le" => some (.le t) | "Gt" => some (.gt t) | "Ge" => some (.ge t)
  | "Eq" => some .eq | "Ne" => some .ne
  -- internal: the overflow flag of a checked op (see `overflowOpOf`)
  | "AddOv" => some (.addOv t) | "SubOv" => some (.subOv t) | "MulOv" => some (.mulOv t)
  | _ => none

/-- For a checked op (`AddWithOverflow`…), the op string of its overflow
    flag. -/
def overflowOpOf (op : String) : Option String :=
  match op with
  | "AddChecked" => some "AddOv"
  | "SubChecked" => some "SubOv"
  | "MulChecked" => some "MulOv"
  | _ => none

/-- A constant operand as a bit pattern of `t` (a negative constant in
    two's complement). -/
def constWord (t : obseq3.IntTy) : UOperand → UOperand
  | .constNeg n _ => .const (t.ofInt (-(Int.ofNat n)))
  | .const n => .const (t.ofInt n)
  | op => op

def resolveIdxRvalue (st : LowerSt) (line : Nat) : URvalue → Except String URvalue
  | .use op => do return .use (← resolveIdxOperand st line op)
  | .move p => do return .move (← resolveIdxPlace st line p)
  | .ref kind prot p => do return .ref kind prot (← resolveIdxPlace st line p)
  | .aggregate v ops => do return .aggregate v (← ops.mapM (resolveIdxOperand st line))
  | .exposeAddr p => do return .exposeAddr (← resolveIdxPlace st line p)
  | .addr p => do return .addr (← resolveIdxPlace st line p)
  | .fromExposed p => do return .fromExposed (← resolveIdxPlace st line p)
  | .ptrOffset p d ib => do return .ptrOffset (← resolveIdxPlace st line p) d ib
  | .ptrOffsetBy p i ib => do
      return .ptrOffsetBy (← resolveIdxPlace st line p) (← resolveIdxPlace st line i) ib
  | .addrOf p => do return .addrOf (← resolveIdxPlace st line p)
  | .rawField p steps => do return .rawField (← resolveIdxPlace st line p) steps
  | .refSlice kind prot p => do return .refSlice kind prot (← resolveIdxPlace st line p)
  | .discriminant p => do return .discriminant (← resolveIdxPlace st line p)
  | .sliceLen p => do return .sliceLen (← resolveIdxPlace st line p)
  | .subSlice p lo hi => do
      return .subSlice (← resolveIdxPlace st line p) (← resolveIdxOperand st line lo)
        (← resolveIdxOperand st line hi)
  | .binOp op t a b => do
      return .binOp op t (← resolveIdxOperand st line a) (← resolveIdxOperand st line b)
  | rv => pure rv

/-- Does this type contain a reference (transitively through tuples,
    structs and enum payloads)? Raw pointers don't count — not retagged at seams.
    UnsafeCell contents don't count either: Miri's retag visitor does
    not descend into interior-mutable regions. -/
partial def containsRef : UTy → Bool
  | .ref _ _ => true
  | .boxT _ => true            -- Box: unique-retagged at seams (miri box retag)
  | .slice false _ _ => true   -- reference-to-slice: seam-retagged (runtime length)
  -- a tuple or struct VALUE: its fields (Miri's retag visitor walks
  -- every aggregate the same way; newtype_retagging). Behind a pointer
  -- nothing is retagged — the `.ref` case stops there, which is what
  -- fnentry_invalidation2 (`inner(t: &mut Thing)`) pins.
  | .tup tys | .structT tys _ => tys.any containsRef
  | .enum variants => variants.any (·.any containsRef)
  | .cell _ => false
  | _ => false

/-- The pointee of a pointer type. -/
def pointeeTy? : UTy → Option UTy
  | .ref _ i | .raw _ i | .boxT i => some i
  | _ => none

/-- Does the place `p` lie in a heap block: is its last dereference
    through a pointer the tracker knows points into the heap (or at a
    place that itself lies in one), with only field projections after it? -/
def inHeap (st : LowerSt) : Nat → UPlace → Bool
  | 0, _ => false
  | fuel + 1, p =>
      match p.projs.reverse.dropWhile (· matches .field _) with
      | .deref :: before =>
          match resolveKey st 32 { p with projs := before.reverse } with
          | some k =>
              st.heapPtrs.contains k ||
                (match st.refOf.lookup k with
                 | some t => inHeap st fuel t
                 | none => false)
          | none => false
      | _ => false

def writesHeap (st : LowerSt) (dst : UPlace) : Bool := inHeap st 8 dst

/-- `dst := alloc(n)`, `n` pointees of `dst` (one, a Box's, when `n` is
    none): the new pointer points into the heap. -/
def emitAlloc (st : LowerSt) (line : Nat) (dst : UPlace) (n : Option UOperand) : LowerSt :=
  let st := match fieldPath? dst <|> resolveKey st 32 dst with
    | some k => let st := killKey st k; { st with heapPtrs := k :: st.heapPtrs }
    | none => st
  pushOut st (.alloc dst n line)

/-- A copy of a pointer that changes its POINTEE type (a type-punning cast,
    `&mut s.b as *mut u32 as *mut u8`) does not carry "points at that
    place" (2026-10-02): through the new type an access covers different
    bytes — a `u8` write is not a write of the whole `u32` — so the
    tracker must forget, not fold, what such a write changes. -/
def punsPointee (src dst : UTy) : Bool :=
  match pointeeTy? src, pointeeTy? dst with
  | some a, some b => a != b
  | _, _ => false

/-- The static trackers, updated for one assignment `dst := rv` (already
    rebased and index-resolved): constants and tracked references per
    (local, field path). A write through a pointer resolves to the place
    it names when the pointer is tracked (`*r` for `r := &p`), and
    forgets everything otherwise. Sound only because the lowering walks
    the ONE path that executes; under a certificate that path is Miri's.
    A `binOp` result is simply unknown — the key is killed and nothing is
    learned (the WORD is computed at runtime, 2026-09-24). -/
def trackAssign (st : LowerSt) (dst : UPlace) (rv : URvalue) : LowerSt :=
  -- where the write lands, as a root-local key
  let key? : Option ConstKey :=
    if dst.projs.contains .deref then resolveKey st 32 dst else fieldPath? dst
  match key? with
  | none => if writesHeap st dst then st else killAllConsts st
  | some (d, path) =>
      let st := killKey st (d, path)
      let copyUnder (sk : ConstKey) : LowerSt :=
        -- every constant and reference known under the source lands under
        -- the destination
        let cs := st.constVals.filterMap fun (k, v) =>
          if k.1 == sk.1 && sk.2.isPrefixOf k.2 then some ((d, path ++ k.2.drop sk.2.length), v) else none
        let rs := st.refOf.filterMap fun (k, tgt) =>
          if k.1 == sk.1 && sk.2.isPrefixOf k.2 then some ((d, path ++ k.2.drop sk.2.length), tgt) else none
        let hs := st.heapPtrs.filterMap fun k =>
          if k.1 == sk.1 && sk.2.isPrefixOf k.2 then some (d, path ++ k.2.drop sk.2.length) else none
        { st with constVals := cs ++ st.constVals, refOf := rs ++ st.refOf, heapPtrs := hs ++ st.heapPtrs }
      match rv with
      | .use (.const n) => { st with constVals := ((d, path), n) :: st.constVals }
      | .use (.copy sp) | .use (.move sp) | .move sp =>
          if punsPointee sp.ty dst.ty then
            -- a cast pointer still points where it pointed
            if (resolveKey st 32 sp).any st.heapPtrs.contains then
              { st with heapPtrs := (d, path) :: st.heapPtrs }
            else st
          else
          match resolveKey st 32 sp with
          | some sk => copyUnder sk
          | none => st
      | .aggregate none ops =>
          ops.zipIdx.foldl (fun st (op, i) =>
            match op with
            | .const v => { st with constVals := ((d, path ++ [i]), v) :: st.constVals }
            | .copy sp | .move sp =>
                match resolveKey st 32 sp with
                | some sk =>
                    let cs := st.constVals.filterMap fun (k, v) =>
                      if k.1 == sk.1 && sk.2.isPrefixOf k.2 then some ((d, path ++ [i] ++ k.2.drop sk.2.length), v) else none
                    let rs := st.refOf.filterMap fun (k, tgt) =>
                      if k.1 == sk.1 && sk.2.isPrefixOf k.2 then some ((d, path ++ [i] ++ k.2.drop sk.2.length), tgt) else none
                    { st with constVals := cs ++ st.constVals, refOf := rs ++ st.refOf }
                | none => st
            | _ => st) st
      | .aggregate (some v) _ => { st with constVals := ((d, path ++ [0]), v) :: st.constVals }
      | .ref _ _ p => { st with refOf := ((d, path), p) :: st.refOf }
      | .refSlice _ _ sp =>
          -- a reborrow keeps the slice's length
          match resolveKey st 32 sp >>= fun k => constLookup st (k.1, k.2 ++ [lenField]) with
          | some n => { st with constVals := ((d, path ++ [lenField]), n) :: st.constVals }
          | none => st
      | .ptrOffset sp _ _ | .ptrOffsetBy sp _ _ =>
          if (resolveKey st 32 sp).any st.heapPtrs.contains then
            { st with heapPtrs := (d, path) :: st.heapPtrs }
          else st
      | _ => st

/-- A string literal's value: Miri keeps it in a global allocation of its
    own and the `&str` constant points at it with that allocation's tag,
    no retag. Here: a heap block of the bytes, written once, and a fresh
    local holding the slice pointer over it (its extent is the length).
    Writes to the block, UB in Miri (read-only memory), are not rejected. -/
def materialiseStr (st : LowerSt) (line : Nat) (bs : List Nat) : LowerSt × UPlace :=
  let u8 := UTy.int { bits := 8 }
  let arr := UTy.tup (List.replicate bs.length u8)
  let b := st.locals.length
  let st := { st with locals := st.locals ++ [.raw true arr, .slice false false u8] }
  let buf : UPlace := { root := .local b, projs := [], ty := .raw true arr }
  let r : UPlace := { root := .local (b + 1), projs := [], ty := .slice false false u8 }
  let st := emitAlloc st line buf none
  let st := bs.zipIdx.foldl (fun st (v, i) =>
    pushOut st (.assign { fld { buf with projs := [.deref], ty := arr } i with ty := u8 }
      (.use (.const v)) line)) st
  let rv : URvalue := .use (.copy buf)
  let st := pushOut (trackAssign st r rv) (.assign r rv line)
  ({ st with constVals := ((b + 1, [lenField]), bs.length) :: st.constVals }, r)

/-- The length of the slice at `p`, when the tracker knows it. -/
def sliceLenOf (st : LowerSt) (p : UPlace) : Option Nat :=
  resolveKey st 32 p >>= fun k => constLookup st (k.1, k.2 ++ [lenField])

/-- Call arguments that are string literals, materialised. -/
def materialiseStrArgs (st : LowerSt) (line : Nat) (args : List UOperand) : LowerSt × List UOperand :=
  args.foldl (fun (st, acc) op =>
    match op with
    | .str bs => let (st, r) := materialiseStr st line bs; (st, acc ++ [.copy r])
    | op => (st, acc ++ [op])) (st, [])

/-- Count one checked branch. `pinned` — a branch followed on Miri's
    word alone — has no lowering path left since `binOp` (2026-09-24):
    the counter stays in the report as the standing witness that it is
    0. -/
def certBump (st : LowerSt) (checked : Nat) (runtime : Nat := 0) : LowerSt :=
  { st with cert := st.cert.map fun c =>
      { c with checked := c.checked + checked, runtime := c.runtime + runtime } }

/-- Stuck unless `discr == v` (a `check`). -/
def emitCheckEq (st : LowerSt) (line : Nat) (discr : UPlace) (v : Nat) : LowerSt :=
  certBump (pushOut st (.check discr [v] true (certLineBase + line))) 1 1

/-- Retag/copy `src` into `dst` at a retag point (inline seam or a
    reference-typed load through a deref): every reference — including
    refs inside tuples and enum payloads — is retagged; for an enum, those
    of the variant it holds (recorded or known statically, checked at run
    time). Non-ref components are plain copies. -/
partial def emitSeamCopy (st : LowerSt) (line : Nat) (prot : Bool) (dst : UPlace)
    (ty : UTy) (src : UPlace) (vk : Option (Nat × List Nat) := none) :
    Except String LowerSt := do
  match ty with
  | .ref mutbl inner =>
      -- pointee ty drives the UnsafeCell freeze mask at elaboration. An
      -- IN-PLACE retag (dst == src) points where the old pointer pointed:
      -- the tracker keeps that target instead of a self-reference.
      let rv : URvalue := .ref (if mutbl then .mut else .shared) prot { pointee src with ty := inner }
      return pushOut (if dst == src then st else trackAssign st dst rv) (.assign dst rv line)
  | .boxT inner =>
      -- miri's box retag: a Unique reborrow of the pointee, and at a
      -- fn-entry seam a WEAK protector (`BoxMut`, 2026-10-01): pops are
      -- blocked as for `&mut`, but the Box may be deallocated during the
      -- call (`sb_dealloc`), as Miri's `from_box_ty` allows.
      let rv : URvalue := .ref .boxMut prot { pointee src with ty := inner }
      return pushOut (if dst == src then st else trackAssign st dst rv) (.assign dst rv line)
  | .slice false mutbl _ =>
      -- reference-to-slice: runtime-length retag via the fat value
      return pushOut st (.assign dst
        (.refSlice (if mutbl then .mut else .shared) prot src) line)
  | .tup tys | .structT tys _ => do
      let mut st := st
      for h : i in [0:tys.length] do
        st ← emitSeamCopy st line prot (fld dst i) tys[i] (fld src i)
          (vk.map fun (a, p) => (a, p ++ [i]))
      return st
  | .enum variants => do
      -- Retag the references of the variant the value HOLDS (Miri reads
      -- the discriminant and walks the active variant only). The variant
      -- is the one Miri recorded at a fn-entry seam (`CertVariant`), or the
      -- discriminant the lowering knows statically; either way the program
      -- CHECKS it when it runs. With neither, the seam is unsupported.
      let recorded? : Option Nat := do
        let (a, path) ← vk
        let c ← st.cert
        c.variantOf? a path
      let static? : Option Nat := (constOfPlace st (fld src 0)).bind fun i =>
        if i ≥ 0 then some i.toNat else none
      let some v := recorded? <|> static?
        | throw s!"unsupported: enum retag of an unknown variant (line {line})"
      if v ≥ variants.length then
        throw s!"unsupported: enum variant {v} out of range (line {line})"
      let mut st := if dst == src then st
        else pushOut st (.assign (fld dst 0) (.use (.copy (fld src 0))) line)
      st := emitCheckEq st line (fld src 0) v
      let fields := variants[v]!
      for h2 : i in [0:fields.length] do
        let dstF := fld dst (1 + i)
        let srcF := fld src (1 + i)
        match fields[i] with
        | .ref mutbl finner =>
            st := pushOut st (.assign dstF
              (.ref (if mutbl then .mut else .shared) prot
                { pointee srcF with ty := finner }) line)
        | fty =>
            if containsRef fty then
              throw s!"unsupported: nested references in enum payload (line {line})"
            else if dst == src then
              pure ()
            else
              st := pushOut st (.assign dstF (.use (.copy srcF)) line)
      return st
  | _ => return if dst == src then st else pushOut st (.assign dst (.use (.copy src)) line)

/-- A `binOp` operand as a word PLACE. A place passes through; a constant
    is written into a FRESH word local first — mirlite's `binOp` takes two
    places, and one write to a local nobody aliases is SB-neutral (Miri's
    own MIR materialises `const 2` into a local the same way). -/
def materialiseWord (st : LowerSt) (line : Nat) (op : UOperand) :
    Except String (LowerSt × UPlace) :=
  match op with
  | .copy p | .move p => .ok (st, p)
  | .const n =>
      let p : UPlace := { root := .local st.locals.length, projs := [], ty := .nat }
      .ok (pushOut { st with locals := st.locals ++ [UTy.nat] }
        (.assign p (.use (.const n)) line), p)
  | .constNeg n bits =>
      -- two's complement at the constant's own width
      let p : UPlace := { root := .local st.locals.length, projs := [], ty := .nat }
      .ok (pushOut { st with locals := st.locals ++ [UTy.nat] }
        (.assign p (.use (.const ((⟨bits, true⟩ : obseq3.IntTy).ofInt (-(Int.ofNat n))))) line), p)
  | .constUnit => .error s!"unsupported: unit arithmetic operand (line {line})"
  | .str _ => .error s!"unsupported: string arithmetic operand (line {line})"
  | .unsupported d => .error s!"unsupported: {d} (line {line})"

/-- Static fn-pointer tracking follows a whole-local copy or move: `dst`
    holds the function `src` held. -/
def propagateFnPtr (st : LowerSt) (src dst : UPlace) : LowerSt :=
  match src, dst with
  | { root := .local s, projs := [], .. }, { root := .local d, projs := [], .. } =>
      match st.fnPtrs.lookup s with
      | some fid => { st with fnPtrs := (d, fid) :: st.fnPtrs }
      | none => st
  | _, _ => st

/-- The type at a projection prefix of a place rooted at local `n`. -/
def projTy (st : LowerSt) (n : Nat) (projs : List UProj) : Option UTy := do
  let t0 ← st.locals[n]?
  projs.foldlM (fun t pr =>
    match pr, t with
    | .deref, .ref _ u | .deref, .raw _ u | .deref, .boxT u => some u
    | .field i, .tup ts | .field i, .structT ts _ => ts[i]?
    | .field i, .cell u => (match u with
        | .tup ts | .structT ts _ => ts[i]?
        | _ => none)
    | .index _, .tup ts => ts.head?
    | _, _ => none) t0

/-- An element of an ARRAY (a tuple in the loader) at an index known only
    when the program runs: `t := ` the address of element 0, then
    `t := ptrOffsetBy t i`, then the place `(*t)…`. For `ℓ.q[i]…` (no
    dereference) element 0 is `addrOf(ℓ.q.0)`, the local's own tag; for
    `(*q)[i]…` it is the pointer `q` itself, reinterpreted as a pointer to
    the element. Either way, no retag: that is Miri's place projection, an
    address computed from the place and the access made with the place's
    tag. An index after a field of a dereference, `(*q).f[i]`, is not
    covered (no address-of through a pointer); `emitAssign` rejects it. -/
def arrayElemPlace (st : LowerSt) (line : Nat) (p : UPlace) :
    Except String (LowerSt × UPlace) := do
  let .local n := p.root | return (st, p)
  let rec split (pre : List UProj) : List UProj → Option (List UProj × Nat × List UProj)
    | [] => none
    | .index (.fromLocal l) :: rest =>
        if (constLookup st (l, [])).isNone then some (pre.reverse, l, rest)
        else split (.index (.fromLocal l) :: pre) rest
    | pr :: rest => split (pr :: pre) rest
  let some (pre, l, rest) := split [] p.projs | return (st, p)
  if pre.any (· matches .index _) then return (st, p)
  let some (.tup (elem :: _)) := projTy st n pre | return (st, p)
  let raw := UTy.raw true elem
  let t := st.locals.length
  let tP : UPlace := { root := .local t, projs := [], ty := raw }
  -- the address of element 0, with the tag of the place's provenance
  let start? : Option URvalue :=
    if !pre.any (· matches .deref) then
      -- a local's array: its own pointer register (`addrOf`, no retag)
      some (.addrOf { root := .local n, projs := pre ++ [.field 0], ty := elem })
    else match pre.reverse with
      | .deref :: baseRev =>
          -- `(*q)[i]`: the pointer `q` itself, reinterpreted as a pointer to
          -- the element (a tag-preserving `ptrCast` at elaboration)
          let base := baseRev.reverse
          (projTy st n base).map fun qty =>
            .use (.copy { root := .local n, projs := base, ty := qty })
      | _ => none
  let some start := start? | return (st, p)
  let st := { st with locals := st.locals ++ [raw] }
  let st := pushOut st (.assign tP start line)
  let iP : UPlace := { root := .local l, projs := [], ty := st.locals[l]?.getD .nat }
  let st := pushOut st (.assign tP (.ptrOffsetBy tP iP true) line)
  return (st, { p with root := .local t, projs := .deref :: rest })

/-- An element of a SLICE's data, `(*s)[k]…` with `s` a slice-pointer
    local: the data has the element's layout (the pointer's extent covers
    the rest), so the index is not a field. Miri reaches element `k`
    through `s` itself at an offset — same tag, no retag — so `k = 0`
    drops the index and `k > 0` goes through `tmp := ptrOffset s k`; an
    index known only when the program runs, through `ptrOffsetBy s i`
    (the bounds check before it is MIR's own `assert`). -/
def sliceElemPlace (st : LowerSt) (line : Nat) (p : UPlace) :
    Except String (LowerSt × UPlace) := do
  match p.root, p.projs with
  | .local n, .deref :: .index ix :: rest =>
      match st.locals[n]? with
      | some (.slice isRaw mutbl elem) =>
          let k? : Option Nat ← match ix with
            | .const k => pure (some k)
            | .fromLocal l => pure (constLookup st (l, []))
            | .unsupported d => throw s!"unsupported: slice index: {d} (line {line})"
          if k? == some 0 then return (st, { p with projs := .deref :: rest })
          let sty := UTy.slice isRaw mutbl elem
          let t := st.locals.length
          let tmp : UPlace := { root := .local t, projs := [], ty := sty }
          let st := { st with locals := st.locals ++ [sty] }
          let sp : UPlace := { root := .local n, projs := [], ty := sty }
          let rv : URvalue ← match k?, ix with
            | some k, _ => pure (.ptrOffset sp (Int.ofNat k) false)
            | none, .fromLocal l =>
                pure (.ptrOffsetBy sp { root := .local l, projs := [], ty := st.locals[l]?.getD .nat } false)
            | none, _ => throw s!"unsupported: slice index (line {line})"
          let st := pushOut st (.assign tmp rv line)
          return (st, { p with root := .local t, projs := .deref :: rest })
      | _ => arrayElemPlace st line p
  | _, _ => arrayElemPlace st line p

def sliceElemRvalue (st : LowerSt) (line : Nat) : URvalue → Except String (LowerSt × URvalue)
  | .use (.copy p) => do let (st, p) ← sliceElemPlace st line p; return (st, .use (.copy p))
  | .use (.move p) => do let (st, p) ← sliceElemPlace st line p; return (st, .use (.move p))
  | .move p => do let (st, p) ← sliceElemPlace st line p; return (st, .move p)
  | .ref kind prot p => do let (st, p) ← sliceElemPlace st line p; return (st, .ref kind prot p)
  | rv => return (st, rv)

/-- The first index projection of `p` by a local whose value the lowering
    does not know: (that local, the place's projections before it). -/
def runtimeIndexOf (st : LowerSt) (p : UPlace) : Option (Nat × List UProj) :=
  let rec go (pre : List UProj) : List UProj → Option (Nat × List UProj)
    | [] => none
    | .index (.fromLocal l) :: rest =>
        if (constLookup st (l, [])).isNone then some (l, pre.reverse) else go (.index (.fromLocal l) :: pre) rest
    | pr :: rest => go (pr :: pre) rest
  go [] p.projs

/-- Append one lowered assignment, desugaring aggregates, applying the
    reference-load retag rule, and rejecting unsupported payloads.
    Places/rvalues must already be rebased. -/
partial def emitAssign (st : LowerSt) (line : Nat) (dst : UPlace) (rv : URvalue) :
    Except String LowerSt := do
  let (st, dst) ← sliceElemPlace st line dst
  let (st, rv) ← sliceElemRvalue st line rv
  -- an array index the element lowering could not reach (see `arrayElemPlace`)
  if (dst :: rv.places).any (fun q => (runtimeIndexOf st q).isSome) then
    throw s!"unsupported: run-time array index after a field of a dereference (line {line})"
  let dst ← resolveIdxPlace st line dst
  let rv ← resolveIdxRvalue st line rv
  let st := trackAssign st dst rv
  match rv with
  | .unsupported d => .error s!"unsupported: {d} (line {line})"
  | .use (.str bs) =>
      let (st, r) := materialiseStr st line bs
      emitAssign st line dst (.use (.copy r))
  | .use .constUnit =>
      return st  -- unit value: no memory access
  | .use (.constNeg n bits) =>
      -- a negative constant is stored as its two's-complement bit pattern
      -- at its own width (was: clamped to 0)
      emitAssign st line dst (.use (.const ((⟨bits, true⟩ : obseq3.IntTy).ofInt (-(Int.ofNat n)))))
  | .ptrOffset _ _ _ | .ptrOffsetBy _ _ _ | .addrOf _ | .refSlice _ _ _ | .sliceLen _ =>
      return pushOut st (.assign dst rv line)
  | .rawField p steps =>
      -- `&raw (*p).f`: `p` as a `*u8`, moved in bounds by the field's byte
      -- offset, retyped by the store into `dst`
      match p.ty with
      | .raw m inner =>
          let some k := fieldStepsOffsetB inner steps
            | .error s!"unsupported: raw field path {steps} (line {line})"
          if k == 0 then emitAssign st line dst (.use (.copy p)) else
          let bty := UTy.raw m (.int { bits := 8 })
          let tmp : UPlace := { root := .local st.locals.length, projs := [], ty := bty }
          let st := { st with locals := st.locals ++ [bty] }
          let st ← emitAssign st line tmp (.use (.copy p))
          emitAssign st line dst (.ptrOffset tmp (Int.ofNat k) true)
      | _ => .error s!"unsupported: raw field through a non-raw pointer (line {line})"
  | .subSlice p lo hi => do
      -- mirlite's `subSlice` takes two word PLACES; a constant bound is
      -- materialised into a fresh local exactly as `binOp`'s are
      let (st, pLo) ← materialiseWord st line lo
      let (st, pHi) ← materialiseWord st line hi
      return pushOut st (.assign dst (.subSlice p (.copy pLo) (.copy pHi)) line)
  | .binOp op ity a b =>
      -- arithmetic is FOLDED when both operands are known (T1: the static
      -- value is what indices, offsets and sizes need), with the machines'
      -- own `evalBinOp` at the operand's integer type — so a fold wraps
      -- exactly as the run would. Otherwise, and whenever the folded
      -- operation would be UB (`binOpUB`: the run must raise it at this
      -- statement), it is EMITTED: mirlite's `binOp` reads two word places
      -- and computes the word at runtime (2026-09-24).
      let t := ity.toIntTy
      if op.startsWith "SExt." then
        -- sign extension of a `srcBits`-wide pattern to `t`: flip the
        -- source sign bit, then subtract it (wrapping at `t`)
        let srcBits := (op.drop 5).toNat!
        let s := 2 ^ (srcBits - 1)
        let tmpIdx := st.locals.length
        let tmp : UPlace := { root := .local tmpIdx, projs := [], ty := .nat }
        let st := { st with locals := st.locals ++ [UTy.nat] }
        let st ← emitAssign st line tmp (.binOp "BitXor" ity a (.const s))
        emitAssign st line dst (.binOp "Sub.Wrap" ity (.copy tmp) (.const s))
      else
      let some bop := binOpOf op t
        | .error s!"unsupported: binary op {op} (line {line})"
      let a := constWord t a
      let b := constWord t b
      let flag? := (overflowOpOf op).bind (binOpOf · t)
      let folded : Option (Nat × Option Nat) :=
        match constOf st a, constOf st b with
        | some x, some y =>
            let (xw, yw) := (t.ofInt x, t.ofInt y)
            if (obseq3.binOpUB bop xw yw).isSome then none
            else some (obseq3.evalBinOp bop xw yw, flag?.map (obseq3.evalBinOp · xw yw))
        | _, _ => none
      -- a fold still READS its place operands: Miri's operation reads them
      -- (a Stacked Borrows access, UB through an invalidated pointer), so
      -- each is copied into a fresh local before the folded value is
      -- written (2026-10-08: `*pb += 1` after a write popped `pb` was
      -- folded and its UB missed)
      let readPlaces (st : LowerSt) : Except String LowerSt :=
        [a, b].foldlM (init := st) fun st op =>
          match op with
          | .copy p | .move p =>
              let tmp : UPlace := { root := .local st.locals.length, projs := [], ty := p.ty }
              emitAssign { st with locals := st.locals ++ [p.ty] } line tmp (.use (.copy p))
          | _ => pure st
      match folded with
      | some (v, some f) =>
          -- `(wrapped value, overflowed)`: a real flag; an overflowing
          -- checked op then fails the `Assert` that follows, as in Miri
          emitAssign (← readPlaces st) line dst (.aggregate none [.const v, .const f])
      | some (v, none) => emitAssign (← readPlaces st) line dst (.use (.const v))
      | none => do
          -- both operands must be word PLACES: a constant is materialised
          -- into a fresh word local (one write nobody aliases)
          let (st, pa) ← materialiseWord st line a
          let (st, pb) ← materialiseWord st line b
          match overflowOpOf op with
          | some fop =>
              let st := pushOut st (.assign (fld dst 0) (.binOp op ity (.copy pa) (.copy pb)) line)
              return pushOut st (.assign (fld dst 1) (.binOp fop ity (.copy pa) (.copy pb)) line)
          | none =>
              return pushOut st (.assign dst (.binOp op ity (.copy pa) (.copy pb)) line)
  | .use (.copy p) | .use (.move p) =>
      -- `_p.PtrMetadata` in a read position is the fat pointer's length
      -- (rustc lowers `a[i]`'s bounds check through it)
      if p.projs.getLast? == some .ptrMetadata then
        return pushOut st
          (.assign dst (.sliceLen { p with projs := p.projs.dropLast }) line)
      else
      -- Miri retags reference-typed values loaded through a pointer
      -- indirection (see load_invalid_mut/shr)
      if p.projs.contains .deref && containsRef p.ty then
        emitSeamCopy st line false dst p.ty p
      else
        return pushOut (propagateFnPtr st p dst) (.assign dst rv line)
  | .use op => do
      checkOperand line op
      return pushOut st (.assign dst rv line)
  | .move p =>
      -- a seam-bound moved call argument (`emitSeamBind`): the callee's
      -- parameter holds the same fn pointer the caller's local did
      return pushOut (propagateFnPtr st p dst) (.assign dst rv line)
  | .ref _ _ _ | .uninit | .exposeAddr _ | .addr _ | .fromExposed _ =>
      return pushOut st (.assign dst rv line)
  | .discriminant p =>
      -- the variant index lives in payload slot 0 and is always exact
      return pushOut st (.assign dst (.use (.copy (fld p 0))) line)
  | .fnRef fid =>
      -- reified fn pointer: track statically, store a placeholder word
      match dst with
      | { root := .local n, projs := [], .. } =>
          return { pushOut st (.assign dst (.use (.const 0)) line)
                   with fnPtrs := (n, fid) :: st.fnPtrs }
      | _ => .error s!"unsupported: fn pointer stored into a projection (line {line})"
  | .aggregate none [] =>
      -- unit value: no memory ACCESS (Miri performs none either), but the
      -- assignment still binds/allocates its destination — a ZST local is
      -- a real (zero-sized) allocation that can be borrowed. Lowered as an
      -- access-free `uninit` init: a zero-length write is a no-op on both
      -- machines, and `preparePlaceAssign` allocates the root. (Before
      -- 2026-08-22 this was dropped outright, so `&mut z` for `z : ()`
      -- failed at resolution — `local/zst_ref`.)
      return pushOut st (.assign dst .uninit line)
  | .aggregate none ops => do
      let mut st := st
      for h : i in [0:ops.length] do
        checkOperand line ops[i]
        st := pushOut st (.assign (fld dst i) (.use ops[i]) line)
      return st
  | .aggregate (some v) ops => do
      -- enum variant: write the discriminant, then payload fields at 1+i
      let mut st := pushOut st (.assign (fld dst 0) (.use (.const v)) line)
      for h : i in [0:ops.length] do
        checkOperand line ops[i]
        st := pushOut st (.assign (fld dst (1 + i)) (.use ops[i]) line)
      return st

def isUnitTy : UTy → Bool
  | .tup [] => true
  | _ => false

/-- Miri's in-place protection of a caller-side slot for the duration of
    a call: a fresh protected `&mut` reborrow of the place, then uninit
    written through it. The reborrow is registered in the innermost
    (callee's) protector frame, so it is protected until `popProtectors`;
    the temporary local is never used again. -/
def protectInPlace (st : LowerSt) (line : Nat) (p : UPlace) (ty : UTy) :
    Except String LowerSt := do
  let tmpIdx := st.locals.length
  let st := { st with locals := st.locals ++ [.ref true ty] }
  let tmp : UPlace := { root := .local tmpIdx, projs := [], ty := .ref true ty }
  let st ← emitAssign st line tmp (.ref .mut true { p with ty := ty })
  emitAssign st line { pointee tmp with ty := ty } .uninit

/-- Bind one call argument into the callee's arg local, retagging if the
    type contains references. A MOVED argument is passed IN PLACE, as Miri
    does (2026-09-21, `protect_in_place_function_argument`): after the
    callee's local is filled, the caller's place is reborrowed with a
    fresh PROTECTED `&mut` — registered in the callee's frame, so any
    access to the place through another tag during the call is UB — and
    uninit is written through it, so the former contents cannot be
    observed after the call either; the temporary is never used again.
    That is what licenses codegen to pass a pointer to the slot instead of
    copying (notes/durable/move-deinits-its-source-at-calls.md). Since
    rustc moves a named place into a call through a temporary, this is
    observable only from custom MIR — Miri's own `arg_inplace_*` tests,
    now in the corpus. The copy step is mirlite's `move` (the temporary
    unique reborrow it mints is subsumed by the protected one; the two
    are the same final state), then the fn-entry retags on the callee
    local in place. Shims get none of this (real MIR frames only). -/
def emitSeamBind (st : LowerSt) (line : Nat) (prot : Bool) (dstLocal : UPlace)
    (ty : UTy) (op : UOperand) (arg? : Option Nat := none) : Except String LowerSt := do
  let vk := arg?.map fun a => (a, ([] : List Nat))
  match op with
  | .move p =>
      let st ← emitAssign st line dstLocal (.move p)
      let st ← if containsRef ty then emitSeamCopy st line prot dstLocal ty dstLocal vk
        else pure st
      protectInPlace st line p ty
  | _ =>
    if containsRef ty then
      match op with
      | .copy p => emitSeamCopy st line prot dstLocal ty p vk
      | _ => .error s!"unsupported: reference-typed argument is not a place (line {line})"
    else
      emitAssign st line dstLocal (.use op)

end conformance
