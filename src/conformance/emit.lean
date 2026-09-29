import conformance.ullbc_ast
import conformance.certificate

/-!
The lowering state and its statement emitters: `LowerSt`, `emitAssign`,
the seam retags (`emitSeamCopy`, `emitSeamBind`) and their helpers. The
std shims (`stdlite.lean`) and the block walker (`lowering.lean`) build
on these; the design notes for the whole lowering are in `lowering.lean`.
-/

namespace conformance


/-- A lowered program: one global local space, straight-line statements.
    `pushProt`/`popProt` bracket an inlined call's protector frame;
    `assignIf` is a variant-guarded assignment (enum seam retags);
    `alloc`/`dealloc` come from the heap shims (`sz = none` means one
    pointee: `Box::new`). -/
inductive LStmt
| assign (dst : UPlace) (rv : URvalue) (line : Nat)
| assignIf (discr : UPlace) (val : Nat) (dst : UPlace) (rv : URvalue) (line : Nat)
| alloc (dst : UPlace) (sz : Option UOperand) (line : Nat)
| dealloc (ptr : UPlace) (line : Nat)
| pushProt (line : Nat)
| popProt (line : Nat)
deriving Repr, BEq, Inhabited

def LStmt.line : LStmt → Nat
  | .assign _ _ l => l
  | .assignIf _ _ _ _ l => l
  | .alloc _ _ l => l
  | .dealloc _ l => l
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
  -- certificate-guided lowering (none = the straight-line-only seam)
  cert : Option CertCursor := none
  certBad : Nat := 0     -- scratch NatL local the checks poison
  certTmp : Nat := 0     -- scratch NatL local the checks read into
  halted : Bool := false -- the certificate's UB/panic prefix ended here

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
            refOf := st.refOf.filter (fun (k', _) => !rel k') }

def killAllConsts (st : LowerSt) : LowerSt :=
  { st with constVals := [], refOf := [] }

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
  | .fromExposed p => .fromExposed (rebasePlace off p)
  | .ptrOffset p d => .ptrOffset (rebasePlace off p) d
  | .refSlice kind prot p => .refSlice kind prot (rebasePlace off p)
  | .sliceLen p => .sliceLen (rebasePlace off p)
  | .subSlice p lo hi =>
      .subSlice (rebasePlace off p) (rebaseOperand off lo) (rebaseOperand off hi)
  | .binOp op a b => .binOp op (rebaseOperand off a) (rebaseOperand off b)
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
  match resolveKey st 8 p with
  | some k => (constLookup st k).map Int.ofNat
  | none => none

def constOf (st : LowerSt) : UOperand → Option Int
  | .const n => some (Int.ofNat n)
  | .constNeg n => some (-(Int.ofNat n))
  | .copy p => constOfPlace st p
  | .move p => constOfPlace st p
  | _ => none

def isCheckedOp (op : String) : Bool :=
  op == "AddChecked" || op == "SubChecked" || op == "MulChecked"

def foldBinOp (op : String) (a b : Int) : Option Int :=
  match op with
  | "Add" | "AddChecked" | "WrappingAdd" => some (a + b)
  | "Sub" | "SubChecked" | "WrappingSub" => some (a - b)
  | "Mul" | "MulChecked" | "WrappingMul" => some (a * b)
  | "Lt" => some (if a < b then 1 else 0)
  | "Le" => some (if a ≤ b then 1 else 0)
  | "Gt" => some (if a > b then 1 else 0)
  | "Ge" => some (if a ≥ b then 1 else 0)
  | "Eq" => some (if a == b then 1 else 0)
  | "Ne" => some (if a != b then 1 else 0)
  | _ => none

def resolveIdxRvalue (st : LowerSt) (line : Nat) : URvalue → Except String URvalue
  | .use op => do return .use (← resolveIdxOperand st line op)
  | .move p => do return .move (← resolveIdxPlace st line p)
  | .ref kind prot p => do return .ref kind prot (← resolveIdxPlace st line p)
  | .aggregate v ops => do return .aggregate v (← ops.mapM (resolveIdxOperand st line))
  | .exposeAddr p => do return .exposeAddr (← resolveIdxPlace st line p)
  | .fromExposed p => do return .fromExposed (← resolveIdxPlace st line p)
  | .ptrOffset p d => do return .ptrOffset (← resolveIdxPlace st line p) d
  | .refSlice kind prot p => do return .refSlice kind prot (← resolveIdxPlace st line p)
  | .discriminant p => do return .discriminant (← resolveIdxPlace st line p)
  | .sliceLen p => do return .sliceLen (← resolveIdxPlace st line p)
  | .subSlice p lo hi => do
      return .subSlice (← resolveIdxPlace st line p) (← resolveIdxOperand st line lo)
        (← resolveIdxOperand st line hi)
  | .binOp op a b => do
      return .binOp op (← resolveIdxOperand st line a) (← resolveIdxOperand st line b)
  | rv => pure rv

/-- Does this type contain a reference (transitively through tuples and
    enum payloads)? Raw pointers don't count — not retagged at seams.
    UnsafeCell contents don't count either: Miri's retag visitor does
    not descend into interior-mutable regions. -/
partial def containsRef : UTy → Bool
  | .ref _ _ => true
  | .boxT _ => true            -- Box: unique-retagged at seams (miri box retag)
  | .slice false _ _ => true   -- reference-to-slice: seam-retagged (runtime length)
  | .tup tys => tys.any containsRef
  | .structT _ => false  -- miri does NOT fn-entry-retag named-struct fields
                         -- (fnentry_invalidation2's point); tuples ARE retagged
  | .enum variants => variants.any (·.any containsRef)
  | .cell _ => false
  | _ => false

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
    if dst.projs.contains .deref then resolveKey st 8 dst else fieldPath? dst
  match key? with
  | none => killAllConsts st
  | some (d, path) =>
      let st := killKey st (d, path)
      let copyUnder (sk : ConstKey) : LowerSt :=
        -- every constant and reference known under the source lands under
        -- the destination
        let cs := st.constVals.filterMap fun (k, v) =>
          if k.1 == sk.1 && sk.2.isPrefixOf k.2 then some ((d, path ++ k.2.drop sk.2.length), v) else none
        let rs := st.refOf.filterMap fun (k, tgt) =>
          if k.1 == sk.1 && sk.2.isPrefixOf k.2 then some ((d, path ++ k.2.drop sk.2.length), tgt) else none
        { st with constVals := cs ++ st.constVals, refOf := rs ++ st.refOf }
      match rv with
      | .use (.const n) => { st with constVals := ((d, path), n) :: st.constVals }
      | .use (.copy sp) | .use (.move sp) | .move sp =>
          match resolveKey st 8 sp with
          | some sk => copyUnder sk
          | none => st
      | .aggregate none ops =>
          ops.zipIdx.foldl (fun st (op, i) =>
            match op with
            | .const v => { st with constVals := ((d, path ++ [i]), v) :: st.constVals }
            | .copy sp | .move sp =>
                match resolveKey st 8 sp with
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
      | _ => st

/-- Retag/copy `src` into `dst` at a retag point (inline seam or a
    reference-typed load through a deref): every reference — including
    refs inside tuples and enum payloads — is retagged; enum payload
    accesses are guarded on the discriminant (`assignIf`). Non-ref
    components are plain copies. -/
partial def emitSeamCopy (st : LowerSt) (line : Nat) (prot : Bool) (dst : UPlace)
    (ty : UTy) (src : UPlace) : Except String LowerSt := do
  match ty with
  | .ref mutbl inner =>
      -- pointee ty drives the UnsafeCell freeze mask at elaboration. An
      -- IN-PLACE retag (dst == src) points where the old pointer pointed:
      -- the tracker keeps that target instead of a self-reference.
      let rv : URvalue := .ref (if mutbl then .mut else .shared) prot { pointee src with ty := inner }
      return pushOut (if dst == src then st else trackAssign st dst rv) (.assign dst rv line)
  | .boxT inner =>
      -- miri's box retag: a Unique reborrow of the pointee. Protection is
      -- weak in miri (dealloc allowed during the call) — our protector
      -- blocks pops identically; the dealloc difference is unexercised.
      let rv : URvalue := .ref .mut prot { pointee src with ty := inner }
      return pushOut (if dst == src then st else trackAssign st dst rv) (.assign dst rv line)
  | .slice false mutbl _ =>
      -- reference-to-slice: runtime-length retag via the fat value
      return pushOut st (.assign dst
        (.refSlice (if mutbl then .mut else .shared) prot src) line)
  | .tup tys => do
      let mut st := st
      for h : i in [0:tys.length] do
        st ← emitSeamCopy st line prot (fld dst i) tys[i] (fld src i)
      return st
  | .enum variants => do
      -- discriminant is payload slot 0; variant v's field i lives at 1+i.
      -- IN-PLACE retags (dst == src, a moved argument already bound):
      -- no plain copies, only the guarded reborrows
      let mut st := if dst == src then st
        else pushOut st (.assign (fld dst 0) (.use (.copy (fld src 0))) line)
      for h : v in [0:variants.length] do
        let fields := variants[v]
        for h2 : i in [0:fields.length] do
          let dstF := fld dst (1 + i)
          let srcF := fld src (1 + i)
          match fields[i] with
          | .ref mutbl finner =>
              st := pushOut st (.assignIf (fld src 0) v dstF
                (.ref (if mutbl then .mut else .shared) prot
                  { pointee srcF with ty := finner }) line)
          | fty =>
              if containsRef fty then
                throw s!"unsupported: nested references in enum payload (line {line})"
              else if dst == src then
                pure ()
              else
                st := pushOut st (.assignIf (fld src 0) v dstF (.use (.copy srcF)) line)
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
  | .constNeg _ => .error s!"unsupported: negative arithmetic operand (line {line})"
  | .constUnit => .error s!"unsupported: unit arithmetic operand (line {line})"
  | .unsupported d => .error s!"unsupported: {d} (line {line})"

/-- The mirlite `binOp` an ULLBC op string lowers to, when it has one.
    Checked ops carry the same arithmetic (the overflow flag is emitted
    separately); comparisons yield 0/1. Division, remainder, shifts and
    bit operations have no mirlite form (none is in the corpus). -/
def toBinOp (op : String) : Option String :=
  match op with
  | "Add" | "AddChecked" | "WrappingAdd" => some "add"
  | "Sub" | "SubChecked" | "WrappingSub" => some "sub"
  | "Mul" | "MulChecked" | "WrappingMul" => some "mul"
  | "Lt" => some "lt" | "Le" => some "le"
  | "Gt" => some "gt" | "Ge" => some "ge"
  | "Eq" => some "eq" | "Ne" => some "ne"
  | _ => none

/-- Static fn-pointer tracking follows a whole-local copy or move: `dst`
    holds the function `src` held. -/
def propagateFnPtr (st : LowerSt) (src dst : UPlace) : LowerSt :=
  match src, dst with
  | { root := .local s, projs := [], .. }, { root := .local d, projs := [], .. } =>
      match st.fnPtrs.lookup s with
      | some fid => { st with fnPtrs := (d, fid) :: st.fnPtrs }
      | none => st
  | _, _ => st

/-- Append one lowered assignment, desugaring aggregates, applying the
    reference-load retag rule, and rejecting unsupported payloads.
    Places/rvalues must already be rebased. -/
partial def emitAssign (st : LowerSt) (line : Nat) (dst : UPlace) (rv : URvalue) :
    Except String LowerSt := do
  let dst ← resolveIdxPlace st line dst
  let rv ← resolveIdxRvalue st line rv
  let st := trackAssign st dst rv
  match rv with
  | .unsupported d => .error s!"unsupported: {d} (line {line})"
  | .use .constUnit =>
      return st  -- unit value: no memory access
  | .use (.constNeg _) =>
      -- negative constants clamp to 0 in value positions (SB-irrelevant)
      return pushOut st (.assign dst (.use (.const 0)) line)
  | .ptrOffset _ _ | .refSlice _ _ _ | .sliceLen _ =>
      return pushOut st (.assign dst rv line)
  | .subSlice p lo hi => do
      -- mirlite's `subSlice` takes two word PLACES; a constant bound is
      -- materialised into a fresh local exactly as `binOp`'s are
      let (st, pLo) ← materialiseWord st line lo
      let (st, pHi) ← materialiseWord st line hi
      return pushOut st (.assign dst (.subSlice p (.copy pLo) (.copy pHi)) line)
  | .binOp op a b =>
      -- arithmetic is FOLDED when both operands are known (T1: the static
      -- value is what indices, offsets and sizes need). Otherwise it is
      -- EMITTED: mirlite's `binOp` reads two word places and computes the
      -- word at runtime, so the result is a real value the checks can
      -- read (2026-09-24 — this is what retired the placeholder words).
      match constOf st a, constOf st b with
      | some x, some y =>
          match foldBinOp op x y with
          | some v =>
              if v < 0 then
                .error s!"unsupported: negative arithmetic result (line {line})"
              else if isCheckedOp op then
                -- `(value, overflowed)`: mirlite words are unbounded, so the
                -- flag is 0; a Miri overflow panic surfaces as a certificate
                -- disagreement at the following assert
                emitAssign st line dst (.aggregate none [.const v.toNat, .const 0])
              else
                emitAssign st line dst (.use (.const v.toNat))
          | none => .error s!"unsupported: binary op {op} (line {line})"
      | _, _ => do
          if (toBinOp op).isNone then
            .error s!"unsupported: binary op {op} (line {line})"
          -- both operands must be word PLACES: a constant is materialised
          -- into a fresh word local (one write nobody aliases)
          let (st, pa) ← materialiseWord st line a
          let (st, pb) ← materialiseWord st line b
          if isCheckedOp op then
            -- `(value, overflowed)`: the flag is 0 on every non-panicking
            -- path, and a panicking one is rejected by the certificate
            let st := pushOut st (.assign (fld dst 0) (.binOp op (.copy pa) (.copy pb)) line)
            return pushOut st (.assign (fld dst 1) (.use (.const 0)) line)
          else
            return pushOut st (.assign dst (.binOp op (.copy pa) (.copy pb)) line)
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
  | .ref _ _ _ | .uninit | .exposeAddr _ | .fromExposed _ =>
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
    (ty : UTy) (op : UOperand) : Except String LowerSt := do
  match op with
  | .move p =>
      let st ← emitAssign st line dstLocal (.move p)
      let st ← if containsRef ty then emitSeamCopy st line prot dstLocal ty dstLocal
        else pure st
      protectInPlace st line p ty
  | _ =>
    if containsRef ty then
      match op with
      | .copy p => emitSeamCopy st line prot dstLocal ty p
      | _ => .error s!"unsupported: reference-typed argument is not a place (line {line})"
    else
      emitAssign st line dstLocal (.use op)

end conformance
