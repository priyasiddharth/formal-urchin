import Lean.Data.Json

/-!
Untyped mirror of the slice of Charon's ULLBC JSON that the SB conformance
suite consumes (charon 0.1.232, `--ullbc --mir built --monomorphize`,
see conformance/PIN). Unknown constructs parse into `unsupported` markers
carrying a description, so the harness can report *which* construct made a
test unsupported instead of failing the whole parse.

Charon's JSON hash-conses types: the first occurrence of a type is
`{"HashConsedValue": [id, value]}` and later occurrences are
`{"Deduplicated": id}`. We pre-walk the document to build the id table,
then resolve during parsing.

ADT handling (everything is monomorphized):
- tuples → `UTy.tup`;
- struct decls → `UTy.tup` of their field types;
- enum decls → `UTy.enum` (lowered to a discriminant word + payload cells);
- `Box` decls are opaque — the pointee type is inferred from use sites
  (deref projections / `Box::new` calls) in a prescan, and the type maps
  to a mutable raw pointer (Miri's "implicit raw" reading of Box);
- `Layout` maps to a plain word carrying the size (its constructor is
  shimmed by the lowering).
-/

namespace conformance

open Lean (Json)

/-- An integer operation's type: width in bits and signedness, from the
    operand's Charon type (pointers and anything non-integer: `u64`). -/
structure UIntTy where
  bits : Nat := 64
  signed : Bool := false
deriving Repr, BEq, Inhabited

/-- Untyped types. `ref`/`raw` both erase to a pointer layout, but the
    distinction drives inline-seam retag synthesis (refs are retagged at
    function boundaries, raws are not). `enum` lowers to a discriminant
    word followed by payload cells. -/
inductive UTy
| nat                  -- a model word (`usize`-wide): sizes, fn placeholders, …
| int (t : UIntTy)     -- a Rust integer, `bool` or `char`, at its width (2026-10-02)
| ref (mutbl : Bool) (inner : UTy)
| raw (mutbl : Bool) (inner : UTy)
| tup (tys : List UTy)
| structT (tys : List UTy)   -- named struct: fields are NOT retagged at seams
| enum (variants : List (List UTy))
| cell (inner : UTy)     -- UnsafeCell/Cell/Atomic*: interior-mutable region
| boxT (inner : UTy)     -- Box<T>: unique-retagged at seams (miri's box retag)
| slice (isRaw mutbl : Bool) (elem : UTy)  -- pointer-to-slice: one-cell fat value
| sliceData (elem : UTy)                   -- the unsized [T] itself (place types only)
| unsupported (desc : String)
deriving Repr, BEq, Inhabited

/-- Does a reference (or Box, or reference-to-slice) occur ANYWHERE in the
    type, struct fields and cells included? A conservative guard, unlike
    the seam-retag rule `containsRef`. -/
partial def containsRefTy : UTy → Bool
  | .ref _ _ | .boxT _ | .slice false _ _ => true
  | .tup tys | .structT tys => tys.any containsRefTy
  | .enum variants => variants.any (·.any containsRefTy)
  | .cell t => containsRefTy t
  | _ => false  -- a raw pointer is not retagged, whatever it points to

/-- Cell count of a type (mirrors `blockSize ∘ toLayout`). -/
partial def uSize : UTy → Nat
  | .nat | .int _ | .ref _ _ | .raw _ _ | .slice _ _ _ | .boxT _ => 1
  | .sliceData _ => 0
  | .cell inner => uSize inner
  | .tup tys | .structT tys => (tys.map uSize).foldl (· + ·) 0
  | .enum variants =>
      1 + (variants.map (fun fs => (fs.map uSize).foldl (· + ·) 0)).foldl Nat.max 0
  | .unsupported _ => 1

/-- Is there an interior-mutable region in the value itself (not behind a
    pointer)? The model's analogue of "not `Freeze`". -/
partial def containsCell : UTy → Bool
  | .cell _ => true
  | .tup tys | .structT tys => tys.any containsCell
  | .enum variants => variants.any (·.any containsCell)
  | _ => false

/-- UnsafeCell freeze mask: true for cells inside an interior-mutable
    region. Shared/raw-const retags give masked cells SharedReadWrite. -/
partial def freezeMask : UTy → List Bool
  | .nat | .int _ | .ref _ _ | .raw _ _ | .slice _ _ _ | .boxT _ => [false]
  | .sliceData _ => []
  | .cell inner => List.replicate (uSize inner) true
  | .tup tys | .structT tys => tys.flatMap freezeMask
  -- A multi-variant enum that is not `Freeze` is treated like a union by
  -- Miri's `visit_freeze_sensitive` (vendor/miri/src/helpers.rs): the whole
  -- value, discriminant included, is UnsafeCell, WITHOUT reading which
  -- variant is active (that read would itself be subject to SB). So: all
  -- cells interior-mutable if any variant holds a cell, else all frozen.
  | .enum e => List.replicate (uSize (.enum e)) (containsCell (.enum e))
  | .unsupported _ => []

/-- Array index resolution: constant, or a local whose (constant) value
    the lowering tracks; anything else is unsupported. -/
inductive UIdx
| const (n : Nat)
| fromLocal (n : Nat)
| unsupported (desc : String)
deriving Repr, BEq, Inhabited

inductive UProj
| deref
| field (idx : Nat)
| index (i : UIdx)
-- the METADATA half of a fat pointer place (`_p.PtrMetadata`): for a
-- slice pointer, its length in elements. Only legal as the last
-- projection of a read operand, where the lowering turns the whole
-- place into `URvalue.sliceLen`
| ptrMetadata
deriving Repr, BEq, Inhabited

/-- Place roots: a local, or a global (static) — the latter is rewritten
    to a hoisted local by the lowering pass. -/
inductive URoot
| local (n : Nat)
| global (gid : Nat)
deriving Repr, BEq, Inhabited

/-- A place: root + projections, outermost-first application order.
    `ty` is the type of the whole place as recorded by Charon; it is
    trustworthy on parser-produced places and advisory on places the
    lowering synthesizes (which never consult it). -/
structure UPlace where
  root : URoot
  projs : List UProj
  ty : UTy := .unsupported "synthetic place"
deriving Repr, BEq, Inhabited

inductive UOperand
| copy (p : UPlace)
| move (p : UPlace)
| const (v : Nat)
| constNeg (n : Nat) (bits : Nat := 64)  -- negative scalar constant, magnitude n, of a `bits`-wide type
| constUnit
| unsupported (desc : String)
deriving Repr, BEq, Inhabited

inductive URefKind
| shared
| mut
| twoPhase
| rawMut
| rawConst
| boxMut   -- a Box's retag: `mut` per cell, WEAK protector when protected
deriving Repr, BEq, Inhabited

/-- `ref`'s `prot` marks a protected (inline-seam) retag; the parser
    always produces `false`, the lowering sets it. `aggregate`'s
    `variant?` is `some v` for enum-variant aggregates (tuples: `none`).
    `uninit` is emitted only by the lowering (hoisted statics).
    `exposeAddr`/`fromExposed` are ptr↔int casts (exposed provenance);
    `fnRef` is a reified function pointer (tracked statically). -/
inductive URvalue
| use (op : UOperand)
| move (p : UPlace)   -- mirlite `move`: the value, and the source's stacks cleared (seam-emitted at moved call args)
| ref (kind : URefKind) (prot : Bool) (p : UPlace)
| aggregate (variant? : Option Nat) (ops : List UOperand)
| exposeAddr (p : UPlace)
| fromExposed (p : UPlace)
| ptrOffset (p : UPlace) (delta : Int)
| refSlice (kind : URefKind) (prot : Bool) (p : UPlace)  -- retag of slice data, runtime length
| sliceLen (p : UPlace)   -- a fat pointer's length in elements (`.len()`, `PtrMetadata`)
| subSlice (p : UPlace) (lo hi : UOperand)  -- narrow a fat pointer to elements `lo..hi`
| binOp (op : String) (ity : UIntTy) (a b : UOperand)
| discriminant (p : UPlace)   -- an enum's variant index (payload slot 0)
| fnRef (funId : Nat)
| uninit
| unsupported (desc : String)
deriving Repr, BEq, Inhabited

inductive UStmtKind
| assign (dst : UPlace) (rv : URvalue)
| storage          -- StorageLive/Dead, Borrowck/FakeRead, Nop, PlaceMention
| unsupported (desc : String)
deriving Repr, BEq, Inhabited

structure UStmt where
  kind : UStmtKind
  line : Nat
deriving Repr, BEq, Inhabited

inductive UTerm
| call (funIdx : Nat) (args : List UOperand) (dest : UPlace) (target : Nat)
| callDyn (func : UPlace) (args : List UOperand) (dest : UPlace) (target : Nat)
| assert (cond : UOperand) (expected : Bool) (target : Nat) (kind : String)
-- `switch discr cases otherwise`: charon's `If [then, else]` is
-- `cases := [(0, else)], otherwise := then`; `SwitchInt` keeps its cases
| switch (discr : UOperand) (cases : List (Nat × Nat)) (otherwise : Nat)
| goto (target : Nat)
-- `Drop` (built MIR emits one for every place with drop glue going out of
-- scope or being overwritten; whether it runs depends on whether the place
-- is still initialised, which the lowering tracks)
| drop (place : UPlace) (target : Nat)
| ret
| unwindResume
| abort
| unsupported (desc : String)
deriving Repr, BEq, Inhabited

structure UBlock where
  stmts : List UStmt
  term : UTerm
  termLine : Nat
deriving Repr, BEq, Inhabited

structure UFun where
  defId : Nat
  name : String            -- last path ident
  path : List String       -- path segments, impl blocks rendered (`nameSegs`)
  argCount : Nat
  locals : List UTy
  blocks : List UBlock
  hasBody : Bool
  -- the monomorphised instantiation (`Instantiated` in the item name):
  -- what a bodyless generic like `Layout::new::<T>()` is ABOUT
  tyArgs : List UTy := []
deriving Repr, Inhabited

structure UGlobal where
  gid : Nat
  name : String
  ty : UTy
deriving Repr, Inhabited

structure UCrate where
  funs : List UFun
  globals : List UGlobal
deriving Repr, Inhabited

/-! ## JSON helpers -/

def getK (j : Json) (k : String) : Option Json :=
  (j.getObjVal? k).toOption

def asArr (j : Json) : List Json :=
  match j.getArr? with
  | .ok a => a.toList
  | .error _ => []

def asNat (j : Json) : Option Nat :=
  j.getNat?.toOption

def asStr (j : Json) : Option String :=
  j.getStr?.toOption

/-- The single key of a one-key object (Charon encodes sums this way). -/
def sumKey (j : Json) : Option (String × Json) :=
  match j with
  | .obj m =>
      match m.toList with
      | [(k, v)] => some (k, v)
      | _ => none
  | .str s => some (s, Json.null)
  | _ => none

/-- All `Ident` components of an item_meta name. -/
def nameIdents (nameJ : Json) : List String :=
  (asArr nameJ).filterMap fun e =>
    match getK e "Ident" with
    | some identJ =>
        match asArr identJ with
        | Json.str s :: _ => some s
        | _ => none
    | none => none

def itemName (j : Json) : List String :=
  ((getK j "item_meta" >>= (getK · "name")).map nameIdents).getD []

/-! ## Parse context: hash-cons table, type decls, box-pointee map -/

abbrev TyTable := List (Nat × Json)

inductive DeclKind
| struct (fields : List Json)      -- field type Jsons
| enum (variants : List (List Json))
| opaque
deriving Inhabited

structure DeclInfo where
  path : List String
  kind : DeclKind
  -- the monomorphised instantiation (`Instantiated` in the item name):
  -- `UnsafeCell<i32>`'s `[i32]`, for opaque std types whose inner type no
  -- constructor call reveals
  tyArgs : List Json := []
deriving Inhabited

structure ParseCtx where
  tbl : TyTable
  decls : List (Nat × DeclInfo)
  boxPointee : List (Nat × Json)    -- Box/NonNull/ManuallyDrop decl id ↦ inner type Json
  cellPointee : List (Nat × Json)   -- UnsafeCell/Cell decl id ↦ inner type Json
  funPaths : List (Nat × List String) -- fun decl id ↦ path segments (`funName`)

partial def collectTable (j : Json) (acc : TyTable) : TyTable :=
  match j with
  | .obj m =>
      let acc :=
        match getK j "HashConsedValue" with
        | some hv =>
            match asArr hv with
            | [idJ, v] =>
                match asNat idJ with
                | some i => (i, v) :: acc
                | none => acc
            | _ => acc
        | none => acc
      m.foldl (fun acc _ v => collectTable v acc) acc
  | .arr a => a.foldl (fun acc v => collectTable v acc) acc
  | _ => acc

def resolveTyJson (tbl : TyTable) (j : Json) : Json :=
  match getK j "Deduplicated" >>= asNat with
  | some i => (tbl.lookup i).getD j
  | none =>
      match getK j "HashConsedValue" with
      | some hv =>
          match asArr hv with
          | [_, v] => v
          | _ => j
      | none => j

/-- The Adt decl id of a type Json, if it is a plain Adt reference. -/
def adtDeclId (tbl : TyTable) (j : Json) : Option Nat :=
  match sumKey (resolveTyJson tbl j) with
  | some ("Adt", adt) =>
      match getK adt "id" with
      | some idJ => getK idJ "Adt" >>= asNat
      | none => none
  | _ => none

/-! ## Function names: impl blocks are path segments

Charon names a method by its module path with an `Impl` element where the
impl block sits: `core::cell::{impl Cell<T>}::get`. Dropping that element
makes distinct functions collide (`Cell::get` and `UnsafeCell::get` are
both `core::cell::get`), so it is rendered, the way Rust writes the
qualified path:

  inherent `impl T`        ↦ `T`                 (`core::cell::Cell::get`)
  trait `impl Tr for T`    ↦ `<T as Tr>`         (`core::cell::<Ref as Deref>::deref`)

`T` is the self type's head only (monomorphised arguments are dropped):
an ADT's name, `*const T`/`*mut T`, `&T`/`&mut T`, `[T]`, `[T; N]`,
`(..)`, or a primitive (`i32`). -/

structure NameCtx where
  tbl : TyTable
  typeNames : List (Nat × String)           -- type decl id ↦ its name
  traitImpls : List (Nat × (String × Json)) -- trait impl id ↦ (trait, Self type)
deriving Inhabited

def renderSelfTy (nc : NameCtx) (j : Json) : String :=
  match sumKey (resolveTyJson nc.tbl j) with
  | some ("Adt", adt) =>
      match (getK adt "id").bind sumKey with
      | some ("Adt", n) => ((asNat n).bind (nc.typeNames.lookup ·)).getD "?"
      | some ("Tuple", _) => "(..)"
      | some ("Builtin", b) =>
          match sumKey b with
          | some ("Slice", _) => "[T]"
          | some ("Array", _) => "[T; N]"
          | some ("Str", _) => "str"
          | some (k, _) => k
          | none => "?"
      | _ => "?"
  | some ("RawPtr", args) =>
      if (asArr args).getLast? == some (Json.str "Mut") then "*mut T" else "*const T"
  | some ("Ref", args) =>
      if (asArr args).getLast? == some (Json.str "Mut") then "&mut T" else "&T"
  | some ("Literal", lit) =>
      match sumKey lit with
      | some ("Int", k) | some ("UInt", k) | some ("Float", k) => ((asStr k).getD "?").toLower
      | some (k, _) => k.toLower
      | none => "?"
  | some ("Slice", _) => "[T]"
  | some ("Array", _) => "[T; N]"
  | some (k, _) => k
  | none => "?"

/-- The segments of an item_meta name: idents, and impl blocks rendered
    as above; generic instantiations are dropped. -/
def nameSegs (nc : NameCtx) (nameJ : Json) : List String :=
  (asArr nameJ).filterMap fun e =>
    match sumKey e with
    | some ("Ident", identJ) =>
        match asArr identJ with
        | Json.str s :: _ => some s
        | _ => none
    | some ("Impl", implJ) =>
        match sumKey implJ with
        | some ("Ty", b) => some (renderSelfTy nc ((getK b "skip_binder").getD Json.null))
        | some ("Trait", idJ) => do
            let (tr, selfJ) ← (asNat idJ).bind (nc.traitImpls.lookup ·)
            pure s!"<{renderSelfTy nc selfJ} as {tr}>"
        | _ => none
    | _ => none

def funName (nc : NameCtx) (j : Json) : List String :=
  ((getK j "item_meta" >>= (getK · "name")).map (nameSegs nc)).getD []

def parseDecls (j : Json) : List (Nat × DeclInfo) :=
  match getK j "translated" >>= (getK · "type_decls") with
  | none => []
  | some declsJ =>
      (asArr declsJ).filterMap fun td => do
        let did ← getK td "def_id" >>= asNat
        let path := itemName td
        let tyArgs :=
          (((getK td "item_meta" >>= (getK · "name")).map asArr).getD []).foldl
            (fun acc e =>
              match getK e "Instantiated" >>= (getK · "skip_binder") >>= (getK · "types") with
              | some ts => acc ++ asArr ts
              | none => acc) []
        let kind :=
          match getK td "kind" >>= sumKey with
          | some ("Struct", fieldsJ) =>
              DeclKind.struct ((asArr fieldsJ).filterMap (getK · "ty"))
          | some ("Enum", variantsJ) =>
              DeclKind.enum ((asArr variantsJ).map fun v =>
                ((getK v "fields").map asArr).getD [] |>.filterMap (getK · "ty"))
          | _ => DeclKind.opaque
        pure (did, { path, kind, tyArgs })

/-- The type Json of an operand (place ty or const ty). -/
def operandTyJson (op : Json) : Option Json :=
  match sumKey op with
  | some ("Copy", p) | some ("Move", p) => getK p "ty"
  | some ("Const", c) => getK c "ty"
  | _ => none

/-- The integer type of a Charon type: `I8`…`I128`/`Isize` signed,
    `U8`…`U128`/`Usize` unsigned (x86_64: size types are 64-bit), `bool` a
    `u8`, `char` a `u32`; anything else `u64`. -/
def intWidth : Option String → Nat
  | some "I8" | some "U8" => 8
  | some "I16" | some "U16" => 16
  | some "I32" | some "U32" => 32
  | some "I128" | some "U128" => 128
  | _ => 64

/-- The integer type of a Charon `LiteralTy` (`{"Int": "I32"}`,
    `{"UInt": "Usize"}`, `"Bool"`, `"Char"`); `none` for floats. -/
def intTyOfLiteral (lit : Json) : Option UIntTy :=
  match sumKey lit with
  | some ("Int", k) => some { bits := intWidth (asStr k), signed := true }
  | some ("UInt", k) => some { bits := intWidth (asStr k), signed := false }
  | _ =>
      if lit == Json.str "Bool" then some { bits := 8 }
      else if lit == Json.str "Char" then some { bits := 32 }
      else none

def intTyOfJson (tbl : TyTable) (j : Json) : UIntTy :=
  match sumKey (resolveTyJson tbl j) with
  | some ("Literal", lit) => (intTyOfLiteral lit).getD {}
  | _ => {}

/-- Is a Charon type `bool`? (`!b` flips one bit, not eight.) -/
def isBoolTy (tbl : TyTable) (j : Json) : Bool :=
  match sumKey (resolveTyJson tbl j) with
  | some ("Literal", lit) => lit == Json.str "Bool"
  | _ => false

/-- The mathematical value of an integer constant operand, read at the
    type it has (a `const` is a bit pattern of `t`; a `constNeg` is its
    negative magnitude). -/
def constIntValue (t : UIntTy) : UOperand → Option Int
  | .constNeg n _ => some (-(Int.ofNat n))
  | .const k =>
      let m := 2 ^ t.bits
      let k := k % m
      some (if t.signed && 2 * k ≥ m then (k : Int) - m else k)
  | _ => none

/-- The bit pattern of `v` at type `t`, as a constant operand. -/
def constOfInt (t : UIntTy) (v : Int) : UOperand :=
  .const (v % ((2 ^ t.bits : Nat) : Int)).toNat

/-- An integer cast `x as dst` from `src` (MIR `IntToInt`): a constant is
    converted while loading; otherwise narrowing keeps the low `dst.bits`
    (a `BitAnd`), widening a SIGNED source sign-extends (`SExt.<bits>`,
    lowered as `(x ^ s) - s` with `s` the source's sign bit), and every
    other cast keeps the bit pattern. -/
def intCast (src dst : UIntTy) (a : UOperand) : URvalue :=
  match constIntValue src a with
  | some v => .use (constOfInt dst v)
  | none =>
      if dst.bits < src.bits then
        .binOp "BitAnd" dst a (.const (2 ^ dst.bits - 1))
      else if src.signed && src.bits < dst.bits then
        .binOp s!"SExt.{src.bits}" dst a (.const 0)
      else .use a

/-- The decl id of a type Json when it is a (monomorphised, opaque)
    wrapper named `name` (`Box`, `NonNull`, `ManuallyDrop`). -/
def wrapperDeclId (name : String) (tbl : TyTable) (decls : List (Nat × DeclInfo))
    (j : Json) : Option Nat := do
  let did ← adtDeclId tbl j
  let info ← decls.lookup did
  if info.path.getLast? == some name then some did else none

def boxDeclId := wrapperDeclId "Box"

/-- The pointee type Json of a raw pointer or reference type Json. -/
def ptrPointeeJson (tbl : TyTable) (j : Json) : Option Json :=
  match sumKey (resolveTyJson tbl j) with
  | some ("RawPtr", args) => (asArr args).head?
  | some ("Ref", args) =>
      match asArr args with
      | [_, inner, _] => some inner
      | _ => none
  | _ => none

/-- Prescan: infer the `T` of the opaque wrappers `Box<T>`, `NonNull<T>`
    and `ManuallyDrop<T>` (one map, decl ids are distinct). Charon
    monomorphises each into an OPAQUE decl per `T`, so `T` has to be read
    off a use. For NonNull: `new_unchecked(p: *mut T)`, `From::from(r: &mut
    T)`, `as_ptr(self) -> *mut T`, `as_mut(&mut self) -> &mut T`. For
    ManuallyDrop: `new(v: T)`, `Deref::deref(&self) -> &T`,
    `DerefMut::deref_mut`. For Box:
    - a deref projection `{kind: {Projection: [boxPlace, "Deref"]}, ty: T}`;
    - `Box::new(v: T) -> Box`;
    - `Box::from_raw(p: *mut T) -> Box`;
    - `Box::into_raw(b: Box) -> *mut T` and `Box::leak(b: Box) -> &mut T`.
    The first use found wins (all uses of one decl agree on `T`). On the
    corpus the constructors alone suffice (2026-09-29: dropping the deref
    rule changes no lowering); the deref rule stays as the fallback for a
    Box made by something not listed here (`new_uninit`, `clone`,
    `into_boxed_slice`, std code). -/
partial def collectBoxPointees (tbl : TyTable) (decls : List (Nat × DeclInfo))
    (paths : List (Nat × List String)) (j : Json) (acc : List (Nat × Json)) :
    List (Nat × Json) :=
  let add (acc : List (Nat × Json)) : Option Nat → Option Json → List (Nat × Json)
    | some did, some t => if (acc.lookup did).isNone then (did, t) :: acc else acc
    | _, _ => acc
  let acc :=
    match getK j "kind" >>= sumKey with
    | some ("Projection", payload) =>
        match asArr payload, getK j "ty" with
        | [inner, proj], some outerTy =>
            if (sumKey proj).map (·.1 == "Deref") |>.getD false then
              add acc (getK inner "ty" >>= boxDeclId tbl decls) (some outerTy)
            else acc
        | _, _ => acc
    | _ => acc
  let acc :=
    match getK j "Call" >>= (getK · "call") with
    | some callJ =>
        let funIdx? :=
          (getK callJ "func" >>= (getK · "Regular") >>= (getK · "kind")
            >>= (getK · "Fun") >>= (getK · "Regular")) >>= asNat
        let argTy? := (((getK callJ "args").map asArr).getD []).head? >>= operandTyJson
        let destTy? := getK callJ "dest" >>= (getK · "ty")
        match funIdx? >>= (paths.lookup ·) with
        | some ["alloc", "boxed", "Box", "new"] =>
            add acc (destTy? >>= boxDeclId tbl decls) argTy?
        | some ["alloc", "boxed", "Box", "from_raw"] =>
            add acc (destTy? >>= boxDeclId tbl decls) (argTy? >>= ptrPointeeJson tbl)
        | some ["alloc", "boxed", "Box", "into_raw"] | some ["alloc", "boxed", "Box", "leak"] =>
            add acc (argTy? >>= boxDeclId tbl decls) (destTy? >>= ptrPointeeJson tbl)
        | some ["core", "ptr", "non_null", "NonNull", "new_unchecked"]
        | some ["core", "ptr", "non_null", "<NonNull as From>", "from"] =>
            add acc (destTy? >>= wrapperDeclId "NonNull" tbl decls) (argTy? >>= ptrPointeeJson tbl)
        | some ["core", "ptr", "non_null", "NonNull", "as_ptr"] =>
            add acc (argTy? >>= wrapperDeclId "NonNull" tbl decls) (destTy? >>= ptrPointeeJson tbl)
        | some ["core", "ptr", "non_null", "NonNull", "as_mut"] =>
            add acc (argTy? >>= ptrPointeeJson tbl >>= wrapperDeclId "NonNull" tbl decls)
              (destTy? >>= ptrPointeeJson tbl)
        | some ["core", "mem", "manually_drop", "ManuallyDrop", "new"] =>
            add acc (destTy? >>= wrapperDeclId "ManuallyDrop" tbl decls) argTy?
        | some ["core", "mem", "manually_drop", "<ManuallyDrop as Deref>", "deref"]
        | some ["core", "mem", "manually_drop", "<ManuallyDrop as DerefMut>", "deref_mut"] =>
            add acc (argTy? >>= ptrPointeeJson tbl >>= wrapperDeclId "ManuallyDrop" tbl decls)
              (destTy? >>= ptrPointeeJson tbl)
        | _ => acc
    | none => acc
  match j with
  | .obj m => m.foldl (fun acc _ v => collectBoxPointees tbl decls paths v acc) acc
  | .arr a => a.foldl (fun acc v => collectBoxPointees tbl decls paths v acc) acc
  | _ => acc

def mkNameCtx (root : Json) (tbl : TyTable) (decls : List (Nat × DeclInfo)) : NameCtx :=
  let listOf (k : String) : List Json :=
    ((getK root "translated" >>= (getK · k)).map asArr).getD []
  let traitNames : List (Nat × String) := (listOf "trait_decls").filterMap fun t => do
    pure (← getK t "def_id" >>= asNat, ← (itemName t).getLast?)
  let traitImpls := (listOf "trait_impls").filterMap fun ti => do
    let did ← getK ti "def_id" >>= asNat
    let it ← getK ti "impl_trait"
    let tr ← (getK it "id" >>= asNat).bind (traitNames.lookup ·)
    let selfJ ← ((getK it "generics" >>= (getK · "types")).map asArr).getD [] |>.head?
    pure (did, (tr, selfJ))
  { tbl, typeNames := decls.filterMap (fun (d, i) => i.path.getLast?.map ((d, ·))), traitImpls }

/-- Light pass: def_id ↦ path segments for every fun decl. -/
def funPaths (nc : NameCtx) (root : Json) : List (Nat × List String) :=
  match getK root "translated" >>= (getK · "fun_decls") with
  | none => []
  | some funsJ =>
      (asArr funsJ).filterMap fun f => do
        let did ← getK f "def_id" >>= asNat
        pure (did, funName nc f)

/-- Prescan: infer UnsafeCell/Cell inner types from calls to their
    (bodyless) constructors and accessors:
    `new(v) -> CellTy` gives CellTy ↦ ty(v);
    `UnsafeCell::get(&CellTy) -> *mut T` and `Cell::get(&CellTy) -> T`
    give CellTy ↦ T. -/
partial def collectCellPointees (tbl : TyTable) (paths : List (Nat × List String))
    (j : Json) (acc : List (Nat × Json)) : List (Nat × Json) :=
  let acc :=
    match getK j "Call" >>= (getK · "call") with
    | some callJ =>
        let funIdx? :=
          (getK callJ "func" >>= (getK · "Regular") >>= (getK · "kind")
            >>= (getK · "Fun") >>= (getK · "Regular")) >>= asNat
        match funIdx? >>= (paths.lookup ·) with
        | some ["core", "cell", "Cell", "new"] | some ["core", "cell", "UnsafeCell", "new"]
        | some ["core", "cell", "RefCell", "new"] =>
            let did? := (getK callJ "dest" >>= (getK · "ty")) >>= (adtDeclId tbl ·)
            let argTy? := (((getK callJ "args").map asArr).getD []).head? >>= operandTyJson
            match did?, argTy? with
            | some did, some t => if (acc.lookup did).isNone then (did, t) :: acc else acc
            | _, _ => acc
        | some ["core", "cell", "<Ref as Deref>", "deref"]
        | some ["core", "cell", "<RefMut as Deref>", "deref"]
        | some ["core", "cell", "<RefMut as DerefMut>", "deref_mut"] =>
            -- Ref/RefMut deref: arg is &Guard, dest is &T ⇒ Guard ↦ T
            let argTy? := (((getK callJ "args").map asArr).getD []).head? >>= operandTyJson
            let did? := argTy?.bind fun t =>
              match sumKey (resolveTyJson tbl t) with
              | some ("Ref", args) =>
                  match asArr args with
                  | [_, inner, _] => adtDeclId tbl inner
                  | _ => none
              | _ => none
            let retTy? := (getK callJ "dest" >>= (getK · "ty")).bind fun t =>
              match sumKey (resolveTyJson tbl t) with
              | some ("Ref", args) =>
                  match asArr args with
                  | [_, inner, _] => some inner
                  | _ => none
              | _ => none
            match did?, retTy? with
            | some did, some t => if (acc.lookup did).isNone then (did, t) :: acc else acc
            | _, _ => acc
        | some ["core", "cell", "Cell", "get"] =>
            -- Cell::get(&CellTy) -> T gives CellTy ↦ T
            let argTy? := (((getK callJ "args").map asArr).getD []).head? >>= operandTyJson
            let did? := argTy?.bind fun t =>
              match sumKey (resolveTyJson tbl t) with
              | some ("Ref", args) =>
                  match asArr args with
                  | [_, inner, _] => adtDeclId tbl inner
                  | _ => none
              | _ => none
            match did?, getK callJ "dest" >>= (getK · "ty") with
            | some did, some t => if (acc.lookup did).isNone then (did, t) :: acc else acc
            | _, _ => acc
        | some ["core", "cell", "UnsafeCell", "get"] =>
            let argTy? := (((getK callJ "args").map asArr).getD []).head? >>= operandTyJson
            let did? := argTy?.bind fun t =>
              match sumKey (resolveTyJson tbl t) with
              | some ("Ref", args) =>
                  match asArr args with
                  | [_, inner, _] => adtDeclId tbl inner
                  | _ => none
              | _ => none
            let retTy? := (getK callJ "dest" >>= (getK · "ty")).bind fun t =>
              match sumKey (resolveTyJson tbl t) with
              | some ("RawPtr", args) =>
                  match asArr args with
                  | [inner, _] => some inner
                  | _ => none
              | _ => none
            match did?, retTy? with
            | some did, some t => if (acc.lookup did).isNone then (did, t) :: acc else acc
            | _, _ => acc
        | _ => acc
    | none => acc
  match j with
  | .obj m => m.foldl (fun acc _ v => collectCellPointees tbl paths v acc) acc
  | .arr a => a.foldl (fun acc v => collectCellPointees tbl paths v acc) acc
  | _ => acc

/-! ## Type parsing -/

def parseScalarInt (j : Json) : Option Int :=
  match sumKey j with
  | some (_, payload) =>
      match (asArr payload).reverse.head? with
      | some (Json.str s) => s.toInt?
      | some v => (asNat v).map Int.ofNat
      | none => none
  | none => none

def parseScalarValue (j : Json) : Option Nat :=
  (parseScalarInt j).map Int.toNat


partial def parseTy (ctx : ParseCtx) (fuel : Nat := 16) (j : Json) : UTy :=
  if fuel == 0 then .unsupported "type recursion depth exceeded" else
  let j := resolveTyJson ctx.tbl j
  match sumKey j with
  | some ("Literal", lit) =>
      match sumKey lit with
      | some ("Float", _) => .unsupported s!"literal type {lit.compress}"
      | _ =>
          match intTyOfLiteral lit with
          | some t => .int t
          | none => .unsupported s!"literal type {lit.compress}"
  | some ("Ref", args) =>
      match asArr args with
      | [_region, inner, mutbl] =>
          match parseTy ctx (fuel - 1) inner with
          | .sliceData elem => .slice false (mutbl == Json.str "Mut") elem
          | t => .ref (mutbl == Json.str "Mut") t
      | _ => .unsupported "malformed Ref type"
  | some ("RawPtr", args) =>
      match asArr args with
      | [inner, mutbl] =>
          match parseTy ctx (fuel - 1) inner with
          | .sliceData elem => .slice true (mutbl == Json.str "Mut") elem
          | t => .raw (mutbl == Json.str "Mut") t
      | _ => .unsupported "malformed RawPtr type"
  | some ("Slice", elemJ) =>
      .sliceData (parseTy ctx (fuel - 1) elemJ)
  | some ("Adt", adt) =>
      match getK adt "id" with
      | some (Json.str "Tuple") =>
          let tys := (getK adt "generics" >>= (getK · "types")).map asArr |>.getD []
          .tup (tys.map (parseTy ctx (fuel - 1)))
      | some idJ =>
          match getK idJ "Adt" >>= asNat with
          | some did =>
              match ctx.decls.lookup did with
              | none => .unsupported s!"unknown adt decl {did}"
              | some info =>
                  let last := info.path.getLast?.getD "?"
                  if last == "Box" then
                    match ctx.boxPointee.lookup did with
                    | some pointee => .boxT (parseTy ctx (fuel - 1) pointee)
                    | none => .unsupported "Box with uninferred pointee"
                  else if last == "NonNull" then
                    -- repr(transparent) over `*const T`: a raw pointer
                    match ctx.boxPointee.lookup did with
                    | some pointee => .raw true (parseTy ctx (fuel - 1) pointee)
                    | none => .unsupported "NonNull with uninferred pointee"
                  else if last == "ManuallyDrop" then
                    -- transparent over `T` (through `MaybeDangling`, whose
                    -- inner references Miri does NOT retag): only a `T`
                    -- without references is the same thing as `T`
                    match ctx.boxPointee.lookup did with
                    | some inner =>
                        let t := parseTy ctx (fuel - 1) inner
                        if containsRefTy t then .unsupported "ManuallyDrop around a reference (MaybeDangling)"
                        else t
                    | none => .unsupported "ManuallyDrop with uninferred inner type"
                  else if last == "Layout" then
                    .nat  -- Layout carries only its size (constructor is shimmed)
                  else if last == "UnsafeCell" || last == "Cell" || last == "RefCell" then
                    -- RefCell is flag-elided: modeled as its value region
                    -- (the borrow-flag discipline is orthogonal to SB)
                    match ctx.cellPointee.lookup did, info.tyArgs with
                    | some inner, _ => .cell (parseTy ctx (fuel - 1) inner)
                    -- no constructor call reveals it: the instantiation does
                    | none, [inner] => .cell (parseTy ctx (fuel - 1) inner)
                    | none, _ => .cell .nat  -- fallback: one interior-mutable word
                  else if info.path == ["core", "cell", "Ref"] ||
                          info.path == ["core", "cell", "RefMut"] then
                    -- RefCell guards: a raw-layout pointer to the value region
                    -- (raw, not ref: guards are NOT protected/retagged at
                    -- seams — see the ref_protector pass test)
                    let mutbl := info.path.getLast? == some "RefMut"
                    match ctx.cellPointee.lookup did with
                    | some inner => .raw mutbl (parseTy ctx (fuel - 1) inner)
                    | none => .raw mutbl .nat
                  else if last.startsWith "Atomic" then
                    -- Atomic* = UnsafeCell around its integer
                    match info.tyArgs with
                    | [inner] => .cell (parseTy ctx (fuel - 1) inner)
                    | _ => .cell .nat
                  else
                    match info.kind with
                    | .struct fields => .structT (fields.map (parseTy ctx (fuel - 1)))
                    | .enum variants =>
                        .enum (variants.map (·.map (parseTy ctx (fuel - 1))))
                    | .opaque => .unsupported s!"opaque adt {String.intercalate "::" info.path}"
          | none =>
              match getK idJ "Builtin" >>= asStr with
              | some "Box" => .unsupported "builtin Box without decl"
              | some b => .unsupported s!"builtin adt {b}"
              | none => .unsupported s!"adt id {idJ.compress}"
      | none => .unsupported "adt without id"
  | some ("Array", args) =>
      -- [T; N] is a homogeneous tuple of N elements
      match asArr args with
      | [elemJ, lenJ] =>
          match getK lenJ "kind" >>= sumKey with
          | some ("Literal", lit) =>
              match sumKey lit with
              | some ("Scalar", sc) =>
                  match parseScalarValue sc with
                  | some n => .tup (List.replicate n (parseTy ctx (fuel - 1) elemJ))
                  | none => .unsupported "array length not a scalar"
              | _ => .unsupported "array length not a literal"
          | _ => .unsupported "array length not a const"
      | _ => .unsupported "malformed Array type"
  | some ("FnPtr", _) | some ("FnDef", _) =>
      .nat  -- fn values are one-word placeholders, tracked statically
  | some (k, _) => .unsupported s!"type constructor {k}"
  | none => .unsupported s!"type {j.compress}"

/-! ## Place / operand / rvalue parsing -/

partial def parsePlace (ctx : ParseCtx) (j : Json) : Except String UPlace := do
  let ty := match getK j "ty" with
    | some tyJ => parseTy ctx 16 tyJ
    | none => .unsupported "place without type"
  match getK j "kind" with
  | none => .error s!"place without kind: {j.compress}"
  | some kind =>
    match sumKey kind with
    | some ("Local", n) =>
        match asNat n with
        | some i => return { root := .local i, projs := [], ty }
        | none => .error "non-numeric local index"
    | some ("Global", g) =>
        match getK g "id" >>= asNat with
        | some gid => return { root := .global gid, projs := [], ty }
        | none => .error "global place without id"
    | some ("Projection", args) =>
        match asArr args with
        | [sub, proj] => do
            let base ← parsePlace ctx sub
            let p ←
              match sumKey proj with
              | some ("Deref", _) => pure UProj.deref
              | some ("PtrMetadata", _) => pure UProj.ptrMetadata
              | some ("Field", fargs) =>
                  -- `[kind, i]`: kind is `{"Tuple": n}`, a struct's
                  -- `{"Adt": [decl, null]}`, or an enum VARIANT's
                  -- `{"Adt": [decl, v]}`. An enum is laid out as its
                  -- discriminant then the payload, so variant field i is
                  -- cell 1+i (as the aggregate and the seam retags write it).
                  match asArr fargs with
                  | [kind, iJ] =>
                      match asNat iJ with
                      | some i =>
                          let variant? := (getK kind "Adt").bind fun a =>
                            match asArr a with
                            | [_, v] => asNat v
                            | _ => none
                          pure (UProj.field (if variant?.isSome then 1 + i else i))
                      | none => .error s!"field projection without index: {proj.compress}"
                  | _ => .error s!"malformed field projection: {proj.compress}"
              | some ("Index", payload) =>
                  if (getK payload "from_end") == some (Json.bool true) then
                    pure (UProj.index (.unsupported "from-end index"))
                  else
                    match getK payload "offset" >>= sumKey with
                    | some ("Const", c) =>
                        match (getK c "kind" >>= sumKey).bind
                              (fun kv => match kv with
                                | ("Literal", lit) =>
                                    (sumKey lit).bind (fun lv => match lv with
                                      | ("Scalar", sc) => parseScalarValue sc
                                      | _ => none)
                                | _ => none) with
                        | some n => pure (UProj.index (.const n))
                        | none => pure (UProj.index (.unsupported "non-nat index const"))
                    | some ("Copy", pj) | some ("Move", pj) =>
                        match (parsePlace ctx pj).toOption with
                        | some { root := .local n, projs := [], .. } =>
                            pure (UProj.index (.fromLocal n))
                        | _ => pure (UProj.index (.unsupported "projected index operand"))
                    | _ => pure (UProj.index (.unsupported "malformed index operand"))
              | some (k, _) => .error s!"unsupported projection {k}"
              | none => .error s!"malformed projection {proj.compress}"
            return { base with projs := base.projs ++ [p], ty }
        | _ => .error "malformed Projection"
    | some (k, _) => .error s!"unsupported place kind {k}"
    | none => .error s!"malformed place kind"

def parseConst (j : Json) : UOperand :=
  match getK j "kind" with
  | none => .unsupported s!"const without kind"
  | some kind =>
    match sumKey kind with
    | some ("Literal", lit) =>
        match sumKey lit with
        | some ("Scalar", sc) =>
            match parseScalarInt sc with
            | some v =>
                if v < 0 then
                  -- the width is the scalar's own type: `{"Signed": ["I32", "-1"]}`
                  let bits := match sumKey sc with
                    | some (_, payload) => intWidth ((asArr payload).head? >>= asStr)
                    | none => 64
                  .constNeg v.natAbs bits
                else .const v.toNat
            | none => .unsupported s!"scalar constant {sc.compress}"
        | some ("Bool", b) => .const (if b == Json.bool true then 1 else 0)
        | _ => .unsupported s!"literal constant {lit.compress}"
    | some ("Adt", payload) =>
        match asArr payload with
        | [_, Json.arr fields] =>
            if fields.isEmpty then .constUnit
            else .unsupported "non-unit adt constant"
        | _ => .unsupported "malformed adt constant"
    | some (k, _) => .unsupported s!"constant kind {k}"
    | none => .unsupported "malformed constant"

def parseOperand (ctx : ParseCtx) (j : Json) : UOperand :=
  match sumKey j with
  | some ("Copy", p) =>
      match parsePlace ctx p with
      | .ok pl => .copy pl
      | .error e => .unsupported e
  | some ("Move", p) =>
      match parsePlace ctx p with
      | .ok pl => .move pl
      | .error e => .unsupported e
  | some ("Const", c) => parseConst c
  | some (k, _) => .unsupported s!"operand {k}"
  | none => .unsupported s!"malformed operand"

def parseRefRvalueKind (kindJ : Json) (isRaw : Bool) : Except String URefKind :=
  match kindJ with
  | Json.str "Mut" => .ok (if isRaw then .rawMut else .mut)
  | Json.str "Shared" => .ok (if isRaw then .rawConst else .shared)
  | Json.str "TwoPhaseMut" => .ok .twoPhase
  | _ =>
      match sumKey kindJ with
      | some (k, _) => .error s!"borrow kind {k}"
      | none => .error s!"borrow kind {kindJ.compress}"

def parseRvalue (ctx : ParseCtx) (j : Json) : URvalue :=
  match sumKey j with
  | some ("Use", payload) =>
      match asArr payload with
      | op :: _ => .use (parseOperand ctx op)
      | [] => .use (parseOperand ctx payload)
  | some ("Ref", r) | some ("RawPtr", r) =>
      let isRaw := (sumKey j).map (·.1 == "RawPtr") |>.getD false
      match getK r "place", getK r "kind" with
      | some pJ, some kJ =>
          match parsePlace ctx pJ, parseRefRvalueKind kJ isRaw with
          | .ok pl, .ok kind =>
              match pl.ty with
              | .sliceData _ =>
                  -- a (re)borrow of slice data: runtime-length retag via
                  -- the place holding the fat pointer (strip the deref)
                  match pl.projs.getLast? with
                  | some .deref =>
                      .refSlice kind false { pl with projs := pl.projs.dropLast }
                  | _ => .unsupported "slice borrow of a non-deref place"
              | _ => .ref kind false pl
          | .error e, _ => .unsupported e
          | _, .error e => .unsupported e
      | _, _ => .unsupported "malformed Ref/RawPtr rvalue"
  | some ("UnaryOp", payload) =>
      match asArr payload with
      | [opJ, operand] =>
          if opJ == Json.str "Not" then
            -- MIR `Not`: flip every bit of the type (one bit for `bool`)
            let tyJ := (operandTyJson operand).getD Json.null
            let t := intTyOfJson ctx.tbl tyJ
            let mask := if isBoolTy ctx.tbl tyJ then 1 else 2 ^ t.bits - 1
            .binOp "BitXor" t (parseOperand ctx operand) (.const mask)
          else
          match sumKey opJ with
          | some ("Cast", castJ) =>
              match sumKey castJ with
              | some ("RawPtr", tys) =>
                  -- charon uses one cast kind for ptr↔ptr AND ptr↔int:
                  -- disambiguate by the source/target types
                  let isPtr : UTy → Bool := fun t =>
                    match t with
                    | .ref _ _ | .raw _ _ => true
                    | _ => false
                  match asArr tys with
                  | [srcJ, dstJ] =>
                      let srcT := parseTy ctx 16 srcJ
                      let dstT := parseTy ctx 16 dstJ
                      match isPtr srcT, isPtr dstT, parseOperand ctx operand with
                      | true, true, op => .use op            -- tag-preserving
                      | true, false, .copy p => .exposeAddr p -- ptr as usize
                      | true, false, .move p => .exposeAddr p
                      | false, true, .copy p => .fromExposed p -- usize as ptr
                      | false, true, .move p => .fromExposed p
                      | false, false, op => .use op           -- int-to-int
                      | _, _, _ => .unsupported "ptr/int cast of a non-place"
                  | _ => .unsupported "malformed RawPtr cast"
              | some ("Unsize", _) =>
                  -- array-to-slice coercion: our slice values are the
                  -- same one-cell pointer (length = rest of allocation)
                  .use (parseOperand ctx operand)
              | some ("FnPtr", _) =>
                  -- fn item reified to a fn pointer: track the target
                  match sumKey operand with
                  | some ("Const", c) =>
                      match (getK c "kind" >>= (getK · "FnDef") >>= (getK · "kind")
                              >>= (getK · "Fun") >>= (getK · "Regular")) >>= asNat with
                      | some fid => .fnRef fid
                      | none => .unsupported "reify of unknown fn"
                  | _ => .unsupported "reify of non-const fn"
              | some ("Scalar", tys) =>
                  match asArr tys with
                  | [srcJ, dstJ] =>
                      match intTyOfLiteral srcJ, intTyOfLiteral dstJ with
                      | some src, some dst => intCast src dst (parseOperand ctx operand)
                      | _, _ => .unsupported "non-integer scalar cast"
                  | _ => .unsupported "malformed scalar cast"
              | some (k, _) => .unsupported s!"cast {k}"
              | none => .unsupported "malformed cast"
          | some ("Neg", mode) =>
              -- MIR `Neg`: `0 - x`, wrapping (`-i32::MIN` wraps; a debug
              -- build asserts `x != MIN` before it, as for `Sub`)
              let t := intTyOfJson ctx.tbl ((operandTyJson operand).getD Json.null)
              match asStr mode with
              | some m => .binOp s!"Sub.{m}" t (.const 0) (parseOperand ctx operand)
              | none => .unsupported "malformed Neg"
          | some (k, _) => .unsupported s!"unary op {k}"
          | none => .unsupported "malformed unary op"
      | _ => .unsupported "malformed UnaryOp"
  | some ("BinaryOp", payload) =>
      match asArr payload with
      | [opJ, aJ, bJ] =>
          -- `"Eq"`, `"AddChecked"`, … or `{"Add": "Wrap"}` (an op with an
          -- overflow mode: Wrap / UB / Panic), rendered `Add.Wrap`
          let op? : Option String := match asStr opJ with
            | some s => some s
            | none => match sumKey opJ with
              | some (k, m) => (asStr m).map (s!"{k}." ++ ·)
              | none => none
          match op? with
          | some op =>
              .binOp op (intTyOfJson ctx.tbl ((operandTyJson aJ).getD Json.null))
                (parseOperand ctx aJ) (parseOperand ctx bJ)
          | none => .unsupported "malformed binary op"
      | _ => .unsupported "malformed BinaryOp"
  | some ("Discriminant", payload) =>
      -- charon 0.1.232: `Discriminant(place)`; older releases: `[place, tyId]`
      let placeJ := match asArr payload with
        | pj :: _ => pj
        | [] => payload
      match parsePlace ctx placeJ with
      | .ok pl => .discriminant pl
      | .error e => .unsupported e
  | some ("Repeat", payload) =>
      -- [v; N] desugars to a homogeneous aggregate
      match asArr payload with
      | [opJ, _elemTy, lenJ] =>
          match (getK lenJ "kind" >>= sumKey).bind
                (fun kv => match kv with
                  | ("Literal", lit) =>
                      (sumKey lit).bind (fun lv => match lv with
                        | ("Scalar", sc) => parseScalarValue sc
                        | _ => none)
                  | _ => none) with
          | some n => .aggregate none (List.replicate n (parseOperand ctx opJ))
          | none => .unsupported "repeat length not a constant"
      | _ => .unsupported "malformed Repeat"
  | some ("Aggregate", payload) =>
      match asArr payload with
      | [kindJ, Json.arr ops] =>
          match sumKey kindJ with
          | some ("Array", _) =>
              .aggregate none (ops.toList.map (parseOperand ctx))
          | some ("Adt", adtPayload) =>
              match asArr adtPayload with
              | adtId :: rest =>
                  if (getK adtId "id") == some (Json.str "Tuple") then
                    .aggregate none (ops.toList.map (parseOperand ctx))
                  else
                    -- enum/struct aggregate: variant index (if any) is the
                    -- next payload element
                    let variant? := rest.head? >>= asNat
                    match getK adtId "id" >>= (fun idJ => getK idJ "Adt") >>= asNat with
                    | some did =>
                        match ctx.decls.lookup did with
                        | some info =>
                            match info.kind with
                            | .enum _ =>
                                .aggregate (some (variant?.getD 0)) (ops.toList.map (parseOperand ctx))
                            | .struct _ =>
                                .aggregate none (ops.toList.map (parseOperand ctx))
                            | .opaque => .unsupported "aggregate of opaque adt"
                        | none => .unsupported "aggregate of unknown adt"
                    | none => .unsupported "non-tuple aggregate"
              | _ => .unsupported "malformed aggregate kind"
          | _ => .unsupported "non-adt aggregate"
      | _ => .unsupported "malformed aggregate"
  | some (k, _) => .unsupported s!"rvalue {k}"
  | none => .unsupported s!"malformed rvalue"

/-! ## Statements / terminators / functions -/

def spanLine (j : Json) : Nat :=
  ((getK j "span" >>= (getK · "data") >>= (getK · "beg") >>= (getK · "line")) >>= asNat).getD 0

def parseStmt (ctx : ParseCtx) (j : Json) : UStmt :=
  let line := spanLine j
  let kind :=
    match getK j "kind" with
    | none => UStmtKind.unsupported "statement without kind"
    | some k =>
      match sumKey k with
      | some ("Assign", payload) =>
          match asArr payload with
          | [dstJ, rvJ] =>
              match parsePlace ctx dstJ with
              | .ok dst => .assign dst (parseRvalue ctx rvJ)
              | .error e => .unsupported e
          | _ => .unsupported "malformed Assign"
      | some ("StorageLive", _) | some ("StorageDead", _)
      | some ("Borrowck", _) | some ("PlaceMention", _)
      | some ("Nop", _) => .storage
      | some (k, _) => .unsupported s!"statement {k}"
      | none => .unsupported "malformed statement kind"
  { kind, line }

def parseTerm (ctx : ParseCtx) (j : Json) : UTerm :=
  match getK j "kind" with
  | none => .unsupported "terminator without kind"
  | some k =>
    match sumKey k with
    | some ("Return", _) => .ret
    | some ("UnwindResume", _) => .unwindResume
    | some ("Abort", _) => .abort
    | some ("Goto", payload) =>
        match getK payload "target" >>= asNat with
        | some t => .goto t
        | none =>
            match asNat payload with
            | some t => .goto t
            | none => .unsupported "malformed Goto"
    | some ("Assert", payload) =>
        let condOp? := (getK payload "assert" >>= (getK · "cond")).map (parseOperand ctx)
        let expected := ((getK payload "assert" >>= (getK · "expected")) == some (Json.bool true))
        let kind := ((getK payload "assert" >>= (getK · "check_kind") >>= sumKey).map (·.1)).getD "?"
        match condOp?, getK payload "target" >>= asNat with
        | some cond, some t => .assert cond expected t kind
        | _, _ => .unsupported "malformed Assert"
    | some ("Switch", payload) =>
        let discr := parseOperand ctx ((getK payload "discr").getD Json.null)
        match getK payload "targets" >>= sumKey with
        | some ("If", tj) =>
            match asArr tj with
            | [t, e] =>
                match asNat t, asNat e with
                | some t, some e => .switch discr [(0, e)] t
                | _, _ => .unsupported "malformed If targets"
            | _ => .unsupported "malformed If targets"
        | some ("SwitchInt", sj) =>
            match asArr sj with
            | [_intTy, casesJ, otherJ] =>
                let cases? : Option (List (Nat × Nat)) :=
                  (asArr casesJ).mapM fun c =>
                    match asArr c with
                    | [vJ, bJ] =>
                        match (getK vJ "Scalar").bind parseScalarInt, asNat bJ with
                        | some v, some b => if v < 0 then none else some (v.toNat, b)
                        | _, _ => none
                    | _ => none
                match cases?, asNat otherJ with
                | some cases, some o => .switch discr cases o
                | _, _ => .unsupported "malformed SwitchInt targets (negative or non-scalar case?)"
            | _ => .unsupported "malformed SwitchInt"
        | _ => .unsupported "malformed Switch targets"
    | some ("Drop", payload) =>
        match getK payload "target" >>= asNat,
              (getK payload "place").map (parsePlace ctx) with
        | some t, some (.ok p) => .drop p t
        | some t, _ => .goto t   -- an unparsable place: not a Box we model
        | none, _ => .unsupported "Drop without target"
    | some ("Call", payload) =>
        let callJ := (getK payload "call").getD Json.null
        let target? := getK payload "target" >>= asNat
        let funIdx? :=
          (getK callJ "func" >>= (getK · "Regular") >>= (getK · "kind")
            >>= (getK · "Fun") >>= (getK · "Regular")) >>= asNat
        let args := ((getK callJ "args").map asArr).getD [] |>.map (parseOperand ctx)
        let dest? := (getK callJ "dest").map (parsePlace ctx)
        let dynFunc? :=
          (getK callJ "func" >>= (getK · "Dynamic")).bind fun opJ =>
            match sumKey opJ with
            | some ("Move", p) | some ("Copy", p) => (parsePlace ctx p).toOption
            | _ => none
        match funIdx?, dynFunc?, dest?, target? with
        | some fi, _, some (.ok dst), some t => .call fi args dst t
        | none, some fp, some (.ok dst), some t => .callDyn fp args dst t
        | none, none, _, _ => .unsupported "call to non-static function"
        | _, _, _, none => .unsupported "call without return target"
        | _, _, some (.error e), _ => .unsupported s!"call dest: {e}"
        | _, _, none, _ => .unsupported "call without dest"
    | some (k, _) => .unsupported s!"terminator {k}"
    | none => .unsupported "malformed terminator kind"

def parseBlock (ctx : ParseCtx) (j : Json) : UBlock :=
  let stmts := ((getK j "statements").map asArr).getD [] |>.map (parseStmt ctx)
  let termJ := (getK j "terminator").getD Json.null
  { stmts, term := parseTerm ctx termJ, termLine := spanLine termJ }

def parseFun (ctx : ParseCtx) (j : Json) : UFun :=
  let defId := ((getK j "def_id") >>= asNat).getD 0
  let path := (ctx.funPaths.lookup defId).getD (itemName j)
  let name := path.getLast?.getD "?"
  let tyArgs :=
    (((getK j "item_meta" >>= (getK · "name")).map asArr).getD []).foldl
      (fun acc e =>
        match getK e "Instantiated" >>= (getK · "skip_binder") >>= (getK · "types") with
        | some ts => acc ++ ((asArr ts).map (parseTy ctx 16))
        | none => acc) []
  match getK j "body" >>= (getK · "Unstructured") with
  | none => { defId, name, path, argCount := 0, locals := [], blocks := [], hasBody := false, tyArgs }
  | some bodyJ =>
      let localsJ := getK bodyJ "locals"
      let argCount := (localsJ >>= (getK · "arg_count") >>= asNat).getD 0
      let locals :=
        ((localsJ >>= (getK · "locals")).map asArr).getD []
          |>.map (fun l => parseTy ctx 16 ((getK l "ty").getD Json.null))
      let blocks := ((getK bodyJ "body").map asArr).getD [] |>.map (parseBlock ctx)
      { defId, name, path, argCount, locals, blocks, hasBody := true }

def parseGlobal (ctx : ParseCtx) (j : Json) : UGlobal :=
  let gid := ((getK j "def_id") >>= asNat).getD 0
  let name := (itemName j).getLast?.getD "?"
  { gid, name, ty := parseTy ctx 16 ((getK j "ty").getD Json.null) }

def parseCrate (root : Json) : Except String UCrate := do
  let tbl := collectTable root []
  let decls := parseDecls root
  let paths := funPaths (mkNameCtx root tbl decls) root
  let boxPointee := collectBoxPointees tbl decls paths root []
  let cellPointee := collectCellPointees tbl paths root []
  let ctx : ParseCtx := { tbl, decls, boxPointee, cellPointee, funPaths := paths }
  let globals :=
    match getK root "translated" >>= (getK · "global_decls") with
    | some gJ =>
        -- stripped decls appear as literal nulls in the list
        ((asArr gJ).filter (fun g => (getK g "def_id").isSome)).map (parseGlobal ctx)
    | none => []
  match getK root "translated" >>= (getK · "fun_decls") with
  | none => .error "no translated.fun_decls in JSON"
  | some funsJ => return { funs := (asArr funsJ).map (parseFun ctx), globals }

end conformance
