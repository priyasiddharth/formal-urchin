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
-/

namespace conformance

open Lean (Json)

/-- Untyped types. `ref`/`raw` both erase to a pointer layout, but the
    distinction drives inline-seam retag synthesis (refs are retagged at
    function boundaries, raws are not). -/
inductive UTy
| nat
| ref (mutbl : Bool) (inner : UTy)
| raw (mutbl : Bool) (inner : UTy)
| tup (tys : List UTy)
| unsupported (desc : String)
deriving Repr, BEq, Inhabited

inductive UProj
| deref
| field (idx : Nat)
deriving Repr, BEq, Inhabited

/-- A place: root local + projections, outermost-first application order. -/
structure UPlace where
  root : Nat
  projs : List UProj
deriving Repr, BEq, Inhabited

inductive UOperand
| copy (p : UPlace)
| move (p : UPlace)
| const (v : Nat)
| constUnit
| unsupported (desc : String)
deriving Repr, BEq, Inhabited

inductive URefKind
| shared
| mut
| twoPhase
| rawMut
| rawConst
deriving Repr, BEq, Inhabited

inductive URvalue
| use (op : UOperand)
| ref (kind : URefKind) (p : UPlace)
| aggregate (ops : List UOperand)
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
| goto (target : Nat)
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
  name : String
  argCount : Nat
  locals : List UTy
  blocks : List UBlock
  hasBody : Bool
deriving Repr, Inhabited

structure UCrate where
  funs : List UFun
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

/-! ## Hash-consed type table -/

abbrev TyTable := List (Nat × Json)

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

/-! ## Type parsing -/

partial def parseTy (tbl : TyTable) (j : Json) : UTy :=
  match getK j "Deduplicated" with
  | some idJ =>
      match asNat idJ >>= (tbl.lookup ·) with
      | some v => parseTy tbl v
      | none => .unsupported "dangling Deduplicated type id"
  | none =>
  match getK j "HashConsedValue" with
  | some hv =>
      match asArr hv with
      | [_, v] => parseTy tbl v
      | _ => .unsupported "malformed HashConsedValue"
  | none =>
  match sumKey j with
  | some ("Literal", lit) =>
      match sumKey lit with
      | some ("Int", _) | some ("UInt", _) => .nat
      | some ("Bool", _) | some ("Char", _) => .nat
      | _ =>
          if lit == Json.str "Bool" || lit == Json.str "Char" then .nat
          else .unsupported s!"literal type {lit.compress}"
  | some ("Ref", args) =>
      match asArr args with
      | [_region, inner, mutbl] => .ref (mutbl == Json.str "Mut") (parseTy tbl inner)
      | _ => .unsupported "malformed Ref type"
  | some ("RawPtr", args) =>
      match asArr args with
      | [inner, mutbl] => .raw (mutbl == Json.str "Mut") (parseTy tbl inner)
      | _ => .unsupported "malformed RawPtr type"
  | some ("Adt", adt) =>
      match getK adt "id" with
      | some (Json.str "Tuple") =>
          let tys := (getK adt "generics" >>= (getK · "types")).map asArr |>.getD []
          .tup (tys.map (parseTy tbl))
      | _ => .unsupported s!"adt type {(getK adt "id").getD Json.null |>.compress}"
  | some (k, _) => .unsupported s!"type constructor {k}"
  | none => .unsupported s!"type {j.compress}"

/-! ## Place / operand / rvalue parsing -/

partial def parsePlace (j : Json) : Except String UPlace := do
  match getK j "kind" with
  | none => .error s!"place without kind: {j.compress}"
  | some kind =>
    match sumKey kind with
    | some ("Local", n) =>
        match asNat n with
        | some i => return { root := i, projs := [] }
        | none => .error "non-numeric local index"
    | some ("Projection", args) =>
        match asArr args with
        | [sub, proj] => do
            let base ← parsePlace sub
            let p ←
              match sumKey proj with
              | some ("Deref", _) => pure UProj.deref
              | some ("Field", fargs) =>
                  -- Field payload ends with the field index
                  match (asArr fargs).reverse.findSome? asNat with
                  | some i => pure (UProj.field i)
                  | none => .error s!"field projection without index: {proj.compress}"
              | some (k, _) => .error s!"unsupported projection {k}"
              | none => .error s!"malformed projection {proj.compress}"
            return { base with projs := base.projs ++ [p] }
        | _ => .error "malformed Projection"
    | some (k, _) => .error s!"unsupported place kind {k}"
    | none => .error s!"malformed place kind"

def parseScalarValue (j : Json) : Option Nat :=
  -- {"Scalar": {"Signed": ["I32", "15"]}} / {"Unsigned": ["U8", "3"]}
  match sumKey j with
  | some (_, payload) =>
      match (asArr payload).reverse.head? with
      | some (Json.str s) =>
          match s.toInt? with
          | some i => some i.toNat   -- negatives clamp to 0: values are SB-irrelevant
          | none => none
      | some v => asNat v
      | none => none
  | none => none

def parseConst (j : Json) : UOperand :=
  match getK j "kind" with
  | none => .unsupported s!"const without kind"
  | some kind =>
    match sumKey kind with
    | some ("Literal", lit) =>
        match sumKey lit with
        | some ("Scalar", sc) =>
            match parseScalarValue sc with
            | some v => .const v
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

def parseOperand (j : Json) : UOperand :=
  match sumKey j with
  | some ("Copy", p) =>
      match parsePlace p with
      | .ok pl => .copy pl
      | .error e => .unsupported e
  | some ("Move", p) =>
      match parsePlace p with
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

def parseRvalue (j : Json) : URvalue :=
  match sumKey j with
  | some ("Use", payload) =>
      -- {"Use": [operand, "Yes"]} (charon 0.1.232) or {"Use": operand}
      match asArr payload with
      | op :: _ => .use (parseOperand op)
      | [] => .use (parseOperand payload)
  | some ("Ref", r) | some ("RawPtr", r) =>
      let isRaw := (sumKey j).map (·.1 == "RawPtr") |>.getD false
      match getK r "place", getK r "kind" with
      | some pJ, some kJ =>
          match parsePlace pJ, parseRefRvalueKind kJ isRaw with
          | .ok pl, .ok kind => .ref kind pl
          | .error e, _ => .unsupported e
          | _, .error e => .unsupported e
      | _, _ => .unsupported "malformed Ref/RawPtr rvalue"
  | some ("UnaryOp", payload) =>
      -- ptr-to-ptr casts (`p as *mut T`) are tag-preserving: lower as a copy
      match asArr payload with
      | [opJ, operand] =>
          match sumKey opJ with
          | some ("Cast", castJ) =>
              match sumKey castJ with
              | some ("RawPtr", _) => .use (parseOperand operand)
              | some (k, _) => .unsupported s!"cast {k}"
              | none => .unsupported "malformed cast"
          | some (k, _) => .unsupported s!"unary op {k}"
          | none => .unsupported "malformed unary op"
      | _ => .unsupported "malformed UnaryOp"
  | some ("Aggregate", payload) =>
      match asArr payload with
      | [kindJ, Json.arr ops] =>
          match sumKey kindJ with
          | some ("Adt", adtPayload) =>
              match asArr adtPayload with
              | adtId :: _ =>
                  if (getK adtId "id") == some (Json.str "Tuple") then
                    .aggregate (ops.toList.map parseOperand)
                  else .unsupported "non-tuple aggregate"
              | _ => .unsupported "malformed aggregate kind"
          | _ => .unsupported "non-adt aggregate"
      | _ => .unsupported "malformed aggregate"
  | some (k, _) => .unsupported s!"rvalue {k}"
  | none => .unsupported s!"malformed rvalue"

/-! ## Statements / terminators / functions -/

def spanLine (j : Json) : Nat :=
  ((getK j "span" >>= (getK · "data") >>= (getK · "beg") >>= (getK · "line")) >>= asNat).getD 0

def parseStmt (j : Json) : UStmt :=
  let line := spanLine j
  let kind :=
    match getK j "kind" with
    | none => UStmtKind.unsupported "statement without kind"
    | some k =>
      match sumKey k with
      | some ("Assign", payload) =>
          match asArr payload with
          | [dstJ, rvJ] =>
              match parsePlace dstJ with
              | .ok dst => .assign dst (parseRvalue rvJ)
              | .error e => .unsupported e
          | _ => .unsupported "malformed Assign"
      | some ("StorageLive", _) | some ("StorageDead", _)
      | some ("Borrowck", _) | some ("PlaceMention", _)
      | some ("Nop", _) => .storage
      | some (k, _) => .unsupported s!"statement {k}"
      | none => .unsupported "malformed statement kind"
  { kind, line }

def parseTerm (j : Json) : UTerm :=
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
    | some ("Call", payload) =>
        let callJ := (getK payload "call").getD Json.null
        let target? := getK payload "target" >>= asNat
        let funIdx? :=
          (getK callJ "func" >>= (getK · "Regular") >>= (getK · "kind")
            >>= (getK · "Fun") >>= (getK · "Regular")) >>= asNat
        let args := ((getK callJ "args").map asArr).getD [] |>.map parseOperand
        let dest? := (getK callJ "dest").map parsePlace
        match funIdx?, dest?, target? with
        | some fi, some (.ok dst), some t => .call fi args dst t
        | none, _, _ => .unsupported "call to non-static function"
        | _, _, none => .unsupported "call without return target"
        | _, some (.error e), _ => .unsupported s!"call dest: {e}"
        | _, none, _ => .unsupported "call without dest"
    | some (k, _) => .unsupported s!"terminator {k}"
    | none => .unsupported "malformed terminator kind"

def parseBlock (j : Json) : UBlock :=
  let stmts := ((getK j "statements").map asArr).getD [] |>.map parseStmt
  let termJ := (getK j "terminator").getD Json.null
  { stmts, term := parseTerm termJ, termLine := spanLine termJ }

def parseFun (tbl : TyTable) (j : Json) : UFun :=
  let defId := ((getK j "def_id") >>= asNat).getD 0
  let name :=
    match (getK j "item_meta" >>= (getK · "name")) with
    | some nameJ =>
        match (asArr nameJ).reverse.head? with
        | some elem =>
            match getK elem "Ident" with
            | some identJ =>
                match asArr identJ with
                | Json.str s :: _ => s
                | _ => "?"
            | none => "?"
        | none => "?"
    | none => "?"
  match getK j "body" >>= (getK · "Unstructured") with
  | none => { defId, name, argCount := 0, locals := [], blocks := [], hasBody := false }
  | some bodyJ =>
      let localsJ := getK bodyJ "locals"
      let argCount := (localsJ >>= (getK · "arg_count") >>= asNat).getD 0
      let locals :=
        ((localsJ >>= (getK · "locals")).map asArr).getD []
          |>.map (fun l => parseTy tbl ((getK l "ty").getD Json.null))
      let blocks := ((getK bodyJ "body").map asArr).getD [] |>.map parseBlock
      { defId, name, argCount, locals, blocks, hasBody := true }

def parseCrate (root : Json) : Except String UCrate := do
  let tbl := collectTable root []
  match getK root "translated" >>= (getK · "fun_decls") with
  | none => .error "no translated.fun_decls in JSON"
  | some funsJ => return { funs := (asArr funsJ).map (parseFun tbl) }

end conformance
