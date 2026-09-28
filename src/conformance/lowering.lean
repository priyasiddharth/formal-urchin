import conformance.ullbc_ast
import conformance.certificate

/-!
ULLBC → flat statement list, in the obseq3-expressible fragment.

Passes (fused into one walk):
1. **Inline** all calls in `main` (callee locals renumbered into one global
   local space; recursion/indirect calls rejected).
2. **Linearize**: follow `goto`/call-target edges from bb0; a revisited
   block means a loop → unsupported. Unwind edges are never followed.
3. **Drop** StorageLive/Dead, Borrowck/FakeRead, Nop, PlaceMention.
   Unit-aggregate assignments are kept as access-free `uninit` inits:
   no memory access in Miri either, but the ZST destination still gets
   allocated, so it can be borrowed.
4. **Desugar** non-empty tuple aggregates into per-field assignments.
5. **Seam retags**: reference-typed arguments and return values are
   re-tagged at inline seams (`arg := &mut *callerPtr`), mirroring Miri's
   Retag-on-function-entry/exit. Raw-typed args are copied untagged.

Any construct outside the fragment yields `.error "unsupported: …"`,
which the harness reports as the test's unsupported-reason.

## Coverage: what is and isn't interpreted, and why

The fragment is deliberately small: the suite's purpose is to score the
*Stacked Borrows rule set* against Miri, so it covers exactly the language
surface the corpus needs to exercise every SB mechanism (granting, pops,
protectors, retags, UnsafeCell masks, exposed provenance, dealloc, …).
Everything else is rejected — not because it is uninteresting, but because
it adds *language* complexity (control flow, drop glue, threads, …)
without exercising any *additional* SB rule. The conformance claim in
`conformance/README.md` spells this out: remaining unsupported tests use
unimplemented language/std features, not un-modeled SB rules.

Covered (interpreted):
- straight-line assignments: copies/moves, `ref` retags (all kinds,
  with seam protection), aggregates (tuple desugaring + enum
  discriminant/payload writes), `uninit`;
- pointer/provenance ops: `exposeAddr`/`fromExposed`, constant
  `ptrOffset`, runtime-length `refSlice` retags;
- slice metadata: `<[T]>::len` and `_p.PtrMetadata` become mirlite's
  `sliceLen` — the extent the fat pointer carries, in elements
  (2026-09-24), so a bounds check on a runtime length is a real check;
- range SUB-SLICING (`&s[lo..hi]`, `&a[..]`): the std `Index`/`array`
  chain is shimmed into the two retags it performs — the receiver's,
  then the mint over the narrowed range — with mirlite's `subSlice`
  (pure pointer arithmetic) between them (2026-09-25);
- heap: `alloc`/`dealloc` via the std shims (`Box::new`, `alloc::alloc`,
  `Layout::*`), incl. `Box` unique retags at seams;
- interior mutability: `UnsafeCell`/`Cell`/`RefCell` shims with freeze
  masks (RefCell flag elided — SB-irrelevant);
- calls: inlined up to depth 8, with fn-entry/exit seam retags;
  statically-resolved indirect calls;
- statics: hoisted to locals, materialized `uninit` (initializers NOT
  run — documented divergence);
- arithmetic: folded when both operands are known (the static value is
  what indices, offsets and sizes need), otherwise EMITTED as mirlite's
  `binOp` on two word places (2026-09-24); statically-true asserts
  (bounds checks);
- **certificate-guided control flow** (2026-09-23, `certificate.lean`):
  with a `<name>.cert.json` recording Miri's branch outcomes, `switch`
  terminators follow the recorded arm (loops unroll), asserts follow
  the recorded outcome, and each is either cross-checked against the
  folded value (T1) or CHECKED AT RUNTIME (T2, with
  `uninit`/`assignIf`/`copy`) against the word the program computed —
  the same word Miri's own `switchInt`/`assert` read. Since `binOp`
  landed there is no third tier: every recorded branch is checked.

Not covered (rejected as `unsupported`), with the reason:
- **loops / `switchInt` / real branches WITHOUT a certificate** — the
  target has only forward-only `SkipIf`; general CFGs are language
  complexity, and no SB rule needs them;
- **unwind paths / `abort` / certified panic paths** — exception
  machinery, no SB content;
- **runtime array indices / pointer offsets / allocation sizes whose
  VALUE the lowering cannot fold** — an index PROJECTION needs a static
  field, and neither `sliceLen`'s nor `subSlice`'s word is one (lengths
  and sub-slices are real; a runtime `ptr::add` is the next gap);
- **recursion & deep (>8) call chains, unknown/bodyless callees,
  unresolved indirect calls** — inlining must terminate statically;
- **drop glue, closures, containers, threads, unions** (as they arise in
  the corpus) — std/language machinery beyond the fragment; the SB rules
  they would exercise are already witnessed by simpler tests;
- **nested references in enum payloads** — would need per-variant
  recursive retag emission; not exercised by the corpus;
- **fn pointers stored into projections** — fn-pointer tracking is a
  flat local↦defId map, sufficient for the corpus's call patterns.

The consolidated inventory of blockers/approximations lives in
`notes/loose-ends/parked.md`; per-test reasons in `conformance/manifest.json`.
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
        -- propagate static fn-pointer tracking through plain copies
        let st :=
          match p, dst with
          | { root := .local s, projs := [], .. }, { root := .local d, projs := [], .. } =>
              match st.fnPtrs.lookup s with
              | some fid => { st with fnPtrs := (d, fid) :: st.fnPtrs }
              | none => st
          | _, _ => st
        return pushOut st (.assign dst rv line)
  | .use op => do
      checkOperand line op
      return pushOut st (.assign dst rv line)
  | .ref _ _ _ | .move _ | .uninit | .exposeAddr _ | .fromExposed _ =>
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

/-- Heap shims: bodyless std allocator entry points lowered to dedicated
    statements instead of inlining.
    - `Box::new(v)` → alloc one pointee + store `v` through the box;
    - `std::alloc::alloc(layout)` → alloc `layout` cells (Layout is
      modeled as its size word, see `from_size_align_unchecked`);
    - `std::alloc::dealloc(ptr, _)` → dealloc (size from the allocation);
    - `Layout::from_size_align_unchecked(sz, _align)` → the size word. -/
def shimCall (crate : UCrate) (funIdx : Nat) :
    Option (LowerSt → List UOperand → UPlace → Nat → Except String LowerSt) := do
  let f ← crate.funs.find? (·.defId == funIdx)
  if f.path == ["alloc", "boxed", "Box", "new"] then
    some fun st args dest line => do
      match args with
      | [valOp] => do
          let st := pushOut st (.alloc dest none line)
          emitAssign st line (pointee dest) (.use valOp)
      | _ => .error s!"unsupported: Box::new arity (line {line})"
  else if f.path == ["alloc", "alloc", "alloc"] then
    some fun st args dest line => do
      match args with
      | [layoutOp] => return pushOut st (.alloc dest (some layoutOp) line)
      | _ => .error s!"unsupported: alloc arity (line {line})"
  else if f.path == ["alloc", "alloc", "dealloc"] then
    some fun st args _dest line => do
      match args with
      | .copy p :: _ | .move p :: _ => return pushOut st (.dealloc p line)
      | _ => .error s!"unsupported: dealloc argument is not a place (line {line})"
  else if f.path == ["core", "alloc", "layout", "Layout", "for_value"] then
    -- Layout::for_value(&T): the size word, statically from the pointee
    some fun st args dest line => do
      match args with
      | [.copy p] | [.move p] =>
          let sz := match p.ty with
            | .ref _ i | .raw _ i => uSize i
            | _ => 1
          emitAssign st line dest (.use (.const sz))
      | _ => .error s!"unsupported: for_value argument is not a place (line {line})"
  else if f.path == ["core", "alloc", "layout", "Layout", "from_size_align_unchecked"] then
    some fun st args dest line => do
      match args with
      | szOp :: _ => emitAssign st line dest (.use szOp)
      | _ => .error s!"unsupported: from_size_align_unchecked arity (line {line})"
  else if f.path == ["core", "cell", "Cell", "new"] ||
          f.path == ["core", "cell", "UnsafeCell", "new"] ||
          f.path == ["core", "cell", "RefCell", "new"] then
    -- UnsafeCell/Cell are layout-transparent: the constructor is identity
    some fun st args dest line => do
      match dest.ty, args with
      | .cell _, [valOp] => emitAssign st line dest (.use valOp)
      | _, [_] => .error s!"unsupported: non-Cell core::cell constructor (line {line})"
      | _, _ => .error s!"unsupported: cell constructor arity (line {line})"
  else if f.path == ["core", "cell", "Cell", "get"] then
    -- Cell::get(&self) -> T: a masked shared reborrow of the cell region
    -- (the `UnsafeCell::get` inside it), then a read through it
    some fun st args dest line => do
      match args with
      | [.copy p] | [.move p] =>
          let inner := match p.ty with
            | .ref _ i => i
            | .raw _ i => i
            | _ => .unsupported "Cell::get on non-pointer"
          let tmpIdx := st.locals.length
          let st := { st with locals := st.locals ++ [.raw true inner] }
          let tmp : UPlace := { root := .local tmpIdx, projs := [] }
          let st := pushOut st (.assign tmp
            (.ref .shared false { pointee p with ty := inner }) line)
          emitAssign st line dest (.use (.copy (pointee tmp)))
      | _ => .error s!"unsupported: Cell::get argument is not a place (line {line})"
  else if f.path == ["core", "cell", "UnsafeCell", "get"] then
    -- UnsafeCell::get(&self) -> *mut T: a raw reborrow of the cell region;
    -- the pointee type carries the freeze mask (all-cell → SharedReadWrite)
    some fun st args dest line => do
      match args with
      | [.copy p] | [.move p] =>
          let inner := match p.ty with
            | .ref _ i => i
            | .raw _ i => i
            | _ => .unsupported "cell get on non-pointer"
          return pushOut st (.assign dest
            (.ref .shared false { pointee p with ty := inner }) line)
      | _ => .error s!"unsupported: cell get argument is not a place (line {line})"
  else if f.path == ["core", "ptr", "read"] ||
          f.path == ["core", "ptr", "const_ptr", "*const T", "read"] ||
          f.path == ["core", "ptr", "mut_ptr", "*mut T", "read"] then
    -- ptr::read(p): a plain read of *p (with the reference-load retag
    -- rule applied by emitAssign when the value contains refs)
    some fun st args dest line => do
      match args with
      | [.copy p] | [.move p] =>
          let inner := match p.ty with
            | .ref _ i => i
            | .raw _ i => i
            | _ => .unsupported "ptr::read on non-pointer"
          emitAssign st line dest (.use (.copy { pointee p with ty := inner }))
      | _ => .error s!"unsupported: ptr::read argument is not a place (line {line})"
  else if f.path == ["core", "intrinsics", "transmute"] then
    -- transmute by value: fn ptrs are tracked statically; a transmute to a
    -- reference type is a real retag (miri retags such lets); a transmute
    -- to a raw type is a tag-preserving reinterpret (ptrCast at elab)
    some fun st args dest line => do
      match args with
      | [.copy p] | [.move p] =>
          match p, st.fnPtrs.lookup (match p.root with | .local n => n | _ => 0) with
          | { root := .local _, projs := [], .. }, some fid =>
              match dest with
              | { root := .local d, projs := [], .. } =>
                  return { pushOut st (.assign dest (.use (.const 0)) line)
                           with fnPtrs := (d, fid) :: st.fnPtrs }
              | _ => .error s!"unsupported: fn transmute into projection (line {line})"
          | _, _ =>
            match dest.ty with
            | .ref mutbl inner =>
                return pushOut st (.assign dest
                  (.ref (if mutbl then .mut else .shared) false
                    { pointee p with ty := inner }) line)
            | .raw _ _ =>
                return pushOut st (.assign dest (.use (.copy p)) line)
            | _ => .error s!"unsupported: transmute to non-pointer type (line {line})"
      | _ => .error s!"unsupported: transmute argument is not a place (line {line})"
  else if f.path == ["core", "mem", "transmute_copy"] then
    -- transmute_copy(&src) -> D: read *src at type D (load retags apply
    -- when D contains references; raw destinations keep the tag)
    some fun st args dest line => do
      match args with
      | [.copy p] | [.move p] =>
          emitAssign st line dest (.use (.copy { pointee p with ty := dest.ty }))
      | _ => .error s!"unsupported: transmute_copy argument is not a place (line {line})"
  else if f.path == ["core", "ptr", "const_ptr", "*const T", "expose_provenance"] ||
          f.path == ["core", "ptr", "mut_ptr", "*mut T", "expose_provenance"] then
    some fun st args dest line => do
      match args with
      | [.copy p] | [.move p] =>
          return pushOut st (.assign dest (.exposeAddr p) line)
      | _ => .error s!"unsupported: expose_provenance argument is not a place (line {line})"
  else if f.path == ["core", "ptr", "with_exposed_provenance_mut"] ||
          f.path == ["core", "ptr", "with_exposed_provenance"] then
    some fun st args dest line => do
      match args with
      | [.copy p] | [.move p] =>
          return pushOut st (.assign dest (.fromExposed p) line)
      | _ => .error s!"unsupported: with_exposed_provenance argument is not a place (line {line})"
  else if f.path == ["core", "cell", "Cell", "set"] then
    -- Cell::set(&self, v): a masked shared reborrow of the cell region,
    -- then a write through it
    some fun st args _dest line => do
      match args with
      | [.copy p, valOp] | [.move p, valOp] =>
          let inner := match p.ty with
            | .ref _ i => i
            | .raw _ i => i
            | _ => .unsupported "cell set on non-pointer"
          let tmpIdx := st.locals.length
          let st := { st with locals := st.locals ++ [.raw true inner] }
          let tmp : UPlace := { root := .local tmpIdx, projs := [] }
          let st := pushOut st (.assign tmp
            (.ref .shared false { pointee p with ty := inner }) line)
          emitAssign st line (pointee tmp) (.use valOp)
      | _ => .error s!"unsupported: Cell::set arguments (line {line})"
  else if f.path == ["core", "cell", "RefCell", "borrow"] then
    -- RefCell::borrow (flag-elided): a masked shared reborrow of the
    -- value region; the guard holds the resulting pointer
    some fun st args dest line => do
      match args with
      | [.copy p] | [.move p] =>
          let inner := match p.ty with
            | .ref _ i => i
            | .raw _ i => i
            | _ => .unsupported "borrow on non-pointer"
          return pushOut st (.assign dest
            (.ref .shared false { pointee p with ty := inner }) line)
      | _ => .error s!"unsupported: borrow argument is not a place (line {line})"
  else if f.path == ["core", "cell", "RefCell", "borrow_mut"] then
    -- RefCell::borrow_mut (flag-elided): a unique reborrow of the value
    -- region (the parent's SharedReadWrite cell items grant the write)
    some fun st args dest line => do
      match args with
      | [.copy p] | [.move p] =>
          let inner := match p.ty with
            | .ref _ i => i
            | .raw _ i => i
            | _ => .unsupported "borrow_mut on non-pointer"
          return pushOut st (.assign dest
            (.ref .mut false { pointee p with ty := inner }) line)
      | _ => .error s!"unsupported: borrow_mut argument is not a place (line {line})"
  else if f.path == ["core", "cell", "<Ref as Deref>", "deref"] ||
          f.path == ["core", "cell", "<RefMut as Deref>", "deref"] ||
          f.path == ["core", "cell", "<RefMut as DerefMut>", "deref_mut"] then
    -- Ref/RefMut deref: a typed load of the guard's pointer at the
    -- destination's reference type — the load-retag rule then produces
    -- the fresh (re)borrow, matching miri's deref reborrow
    some fun st args dest line => do
      match args with
      | [.copy p] | [.move p] =>
          emitAssign st line dest (.use (.copy { pointee p with ty := dest.ty }))
      | _ => .error s!"unsupported: guard deref argument is not a place (line {line})"
  else if f.path == ["core", "cell", "Cell", "replace"] ||
          f.path == ["core", "cell", "RefCell", "replace"] then
    -- Cell/RefCell::replace(&self, v) -> T (flag-elided): masked shared
    -- reborrow, read the old value, write the new one
    some fun st args dest line => do
      match args with
      | [.copy p, valOp] | [.move p, valOp] =>
          let inner := match p.ty with
            | .ref _ i => i
            | .raw _ i => i
            | _ => .unsupported "replace on non-pointer"
          let tmpIdx := st.locals.length
          let st := { st with locals := st.locals ++ [.raw true inner] }
          let tmp : UPlace := { root := .local tmpIdx, projs := [] }
          let st := pushOut st (.assign tmp
            (.ref .shared false { pointee p with ty := inner }) line)
          let st ← emitAssign st line dest (.use (.copy (pointee tmp)))
          emitAssign st line (pointee tmp) (.use valOp)
      | _ => .error s!"unsupported: replace arguments (line {line})"
  else if (f.path == ["core", "ptr", "mut_ptr", "*mut T", "add"] ||
           f.path == ["core", "ptr", "const_ptr", "*const T", "add"] ||
           f.path == ["core", "ptr", "mut_ptr", "*mut T", "offset"] ||
           f.path == ["core", "ptr", "const_ptr", "*const T", "offset"] ||
           f.path == ["core", "ptr", "mut_ptr", "*mut T", "wrapping_add"] ||
           f.path == ["core", "ptr", "const_ptr", "*const T", "wrapping_add"] ||
           f.path == ["core", "ptr", "mut_ptr", "*mut T", "wrapping_offset"] ||
           f.path == ["core", "ptr", "const_ptr", "*const T", "wrapping_offset"]) then
    -- pointer arithmetic with a constant delta (scaled by the pointee
    -- size at elaboration); provenance/tag is preserved
    some fun st args dest line => do
      match args with
      | [.copy p, d] | [.move p, d] =>
          let delta ← match d with
            | .const n => pure (Int.ofNat n)
            | .constNeg n => pure (-(Int.ofNat n))
            | _ => throw s!"unsupported: runtime pointer offset (line {line})"
          return pushOut st (.assign dest (.ptrOffset p delta) line)
      | _ => .error s!"unsupported: pointer offset arguments (line {line})"
  else if f.path == ["core", "slice", "index", "<[T] as Index>", "index"] ||
          f.path == ["core", "slice", "index", "<[T] as IndexMut>", "index_mut"] ||
          f.path == ["core", "slice", "[T]", "get_unchecked"] ||
          f.path == ["core", "slice", "[T]", "get_unchecked_mut"] ||
          f.path == ["core", "array", "<[T; N] as Index>", "index"] ||
          f.path == ["core", "array", "<[T; N] as IndexMut>", "index_mut"] then
    -- `&s[lo..hi]` / `&mut s[lo..hi]`: the std chain bottoms out in
    -- `from_raw_parts_mut(ptr.add(lo), hi - lo)`, i.e. a retag over the
    -- NARROWED range. The shim replaces the whole call and reproduces
    -- the two retags it performs: the fn-entry retag of the receiver
    -- (over its whole extent) and the mint over the sub-range. The
    -- narrowing between them is pure pointer arithmetic (`subSlice`).
    --
    -- The range argument is a `Range { start, end }` aggregate: a place
    -- whose two fields are the bounds. A full range (`..`) has no
    -- fields, and is the identity narrowing `0 .. len`.
    some fun st args dest line => do
      let mutbl := f.path == ["core", "slice", "index", "<[T] as IndexMut>", "index_mut"] ||
                   f.path == ["core", "slice", "[T]", "get_unchecked_mut"] ||
                   f.path == ["core", "array", "<[T; N] as IndexMut>", "index_mut"]
      let kind : URefKind := if mutbl then .mut else .shared
      match args with
      | [sliceOp, rangeOp] =>
          let some sp := operandPlace? sliceOp
            | .error s!"unsupported: slice index receiver is not a place (line {line})"
          -- the receiver's fn-entry retag, over its own extent
          let tmpIdx := st.locals.length
          let st := { st with locals := st.locals ++ [sp.ty] }
          let tmp : UPlace := { root := .local tmpIdx, projs := [], ty := sp.ty }
          let st := pushOut st (.assign tmp (.refSlice kind false sp) line)
          -- the bounds: a `Range`'s two fields, or `0 .. len` for `..`
          let (lo, hi) ←
            match operandPlace? rangeOp with
            | none => .error s!"unsupported: slice index argument is not a place (line {line})"
            | some rp =>
                match rp.ty with
                | .tup [] | .structT [] =>
                    -- RangeFull: the whole slice, so `0 .. len`
                    let lenIdx := st.locals.length
                    pure (UOperand.const 0, UOperand.copy
                      { root := .local lenIdx, projs := [], ty := .nat })
                | .tup [_, _] | .structT [_, _] =>
                    pure (UOperand.copy (fld rp 0), UOperand.copy (fld rp 1))
                | _ => .error s!"unsupported: slice index by {reprStr rp.ty} (line {line})"
          -- a RangeFull needs the length materialised first
          let st ←
            match rangeOp with
            | .copy rp | .move rp =>
                match rp.ty with
                | .tup [] | .structT [] =>
                    let lenIdx := st.locals.length
                    let st := { st with locals := st.locals ++ [UTy.nat] }
                    pure (pushOut st (.assign
                      { root := .local lenIdx, projs := [], ty := .nat }
                      (.sliceLen tmp) line))
                | _ => pure st
            | _ => pure st
          -- move the retagged receiver into the destination first: when
          -- the receiver is an ARRAY reference (`&a[0..0]`) the copy is
          -- the tag-preserving reinterpret that gives the pointer the
          -- slice's element type, which is the type the narrowing scales
          -- its bounds by
          let st ← emitAssign st line dest (.use (.copy tmp))
          let st ← emitAssign st line dest (.subSlice dest lo hi)
          -- the mint over the narrowed range
          return pushOut st (.assign dest (.refSlice kind false dest) line)
      | _ => .error s!"unsupported: slice index arity (line {line})"
  else if f.path == ["core", "slice", "[T]", "len"] then
    -- `<[T]>::len(&self)`: the metadata of the fat pointer argument. The
    -- shim replaces the whole call, and the length read is not an access
    -- to the slice DATA — only to the local holding the pointer, which
    -- is what `sliceLen` performs (copy's read of that cell).
    some fun st args dest line => do
      match args with
      | [.copy p] | [.move p] =>
          return pushOut st (.assign dest (.sliceLen p) line)
      | _ => .error s!"unsupported: slice len argument is not a place (line {line})"
  else if f.path == ["core", "slice", "[T]", "as_ptr"] ||
          f.path == ["core", "slice", "[T]", "as_mut_ptr"] then
    -- slice data pointer. The shim replaces the whole call, so it must
    -- reproduce the fn-entry retag of the &[T]/&mut [T] receiver (that
    -- retag's write access is the invalidation fnentry_invalidation2
    -- tests), then the raw retag of the data the body performs.
    some fun st args dest line => do
      let mutbl := f.path == ["core", "slice", "[T]", "as_mut_ptr"]
      match args with
      | [.copy p] | [.move p] =>
          let tmpIdx := st.locals.length
          let st := { st with locals := st.locals ++ [p.ty] }
          let tmp : UPlace := { root := .local tmpIdx, projs := [], ty := p.ty }
          let st := pushOut st (.assign tmp
            (.refSlice (if mutbl then .mut else .shared) false p) line)
          return pushOut st (.assign dest
            (.refSlice (if mutbl then .rawMut else .rawConst) false tmp) line)
      | _ => .error s!"unsupported: as_ptr argument is not a place (line {line})"
  else if f.path == ["alloc", "boxed", "Box", "from_raw"] then
    -- Box::from_raw: adopts the raw pointer's tag (a plain value copy;
    -- the box retag happens at the next seam)
    some fun st args dest line => do
      match args with
      | [.copy p] | [.move p] =>
          return pushOut st (.assign dest (.use (.copy p)) line)
      | _ => .error s!"unsupported: from_raw argument is not a place (line {line})"
  else if f.path == ["core", "mem", "forget"] then
    -- mem::forget: no drop, no access; protectors end at fn return anyway
    some fun st _args _dest _line => return st
  else if f.path == ["core", "mem", "drop"] then
    -- mem::drop: consumes the value; drop glue for modeled types is
    -- either nothing or elided flag maintenance (RefCell guards)
    some fun st _args _dest _line => return st
  else if f.path == ["core", "cell", "Cell", "get_mut"] ||
          f.path == ["core", "cell", "UnsafeCell", "get_mut"] ||
          f.path == ["core", "cell", "RefCell", "get_mut"] then
    -- Cell::get_mut(&mut self) -> &mut T: a unique reborrow of the cell
    some fun st args dest line => do
      match args with
      | [.copy p] | [.move p] =>
          let inner := match p.ty with
            | .ref _ i => i
            | .raw _ i => i
            | _ => .unsupported "cell get_mut on non-pointer"
          return pushOut st (.assign dest
            (.ref .mut false { pointee p with ty := inner }) line)
      | _ => .error s!"unsupported: Cell::get_mut argument is not a place (line {line})"
  else
    none

/-! ## Certificate checks, from existing statements only

Every recorded branch outcome the lowering cannot fold is CHECKED at
runtime with `uninit`/`assignIf`/
`copy` alone: "UB unless `d == v`" is `bad := uninit; assignIf d v (bad :=
0); tmp := copy bad` — the copy reads an uninitialised cell exactly when
the pin is wrong. The check statements carry a SENTINEL line so the
harness reports a failure as "certificate rejected", not as a program
verdict. -/

/-- Lines ≥ this mark certificate checks; ≥ 2× mark the poison at the end
    of a UB/panic prefix. -/
def certLineBase : Nat := 1000000

def natLocal (i : Nat) : UPlace := { root := .local i, projs := [], ty := .nat }

/-- Count one checked branch. `pinned` — a branch followed on Miri's
    word alone — has no lowering path left since `binOp` (2026-09-24):
    the counter stays in the report as the standing witness that it is
    0. -/
def certBump (st : LowerSt) (checked : Nat) (runtime : Nat := 0) : LowerSt :=
  { st with cert := st.cert.map fun c =>
      { c with checked := c.checked + checked, runtime := c.runtime + runtime } }

/-- UB unless `discr == v`. -/
def emitCheckEq (st : LowerSt) (line : Nat) (discr : UPlace) (v : Nat) : LowerSt :=
  let bad := natLocal st.certBad
  let tmp := natLocal st.certTmp
  let l := certLineBase + line
  let st := pushOut st (.assign bad .uninit l)
  let st := pushOut st (.assignIf discr v bad (.use (.const 0)) l)
  certBump (pushOut st (.assign tmp (.use (.copy bad)) l)) 1 1

/-- UB unless `discr ∉ vs` (the `otherwise` arm of a switch). -/
def emitCheckNotIn (st : LowerSt) (line : Nat) (discr : UPlace) (vs : List Nat) : LowerSt :=
  -- an `otherwise` arm with NO cases to exclude is vacuous: nothing to
  -- check at runtime, and nothing the certificate could get wrong
  if vs.isEmpty then certBump st 1 else
  let bad := natLocal st.certBad
  let tmp := natLocal st.certTmp
  let l := certLineBase + line
  let st := pushOut st (.assign bad .uninit l)
  let st := vs.foldl (fun st v => pushOut st (.assignIf discr v tmp (.use (.copy bad)) l)) st
  certBump st 1 1

/-- The end of a UB/panic certificate prefix: mirlite must have failed
    before reaching this; reaching it is the distinct verdict
    `certExhausted`. -/
def emitPoison (st : LowerSt) (line : Nat) : LowerSt :=
  let bad := natLocal st.certBad
  let tmp := natLocal st.certTmp
  let l := 2 * certLineBase + line
  let st := pushOut st (.assign bad .uninit l)
  { pushOut st (.assign tmp (.use (.copy bad)) l) with halted := true }

/-- Take the next recorded event. `none` with `halted` set means the
    certificate's UB/panic prefix ended here. -/
def consumeEvent (st : LowerSt) (line : Nat) : Except String (Option CertEvent × LowerSt) :=
  match st.cert with
  | none => .ok (none, st)
  | some c =>
      match c.nextEvent with
      | some (e, c') => .ok (some e, { st with cert := some c' })
      | none =>
          match c.cert.outcome with
          | .ok => .error s!"certificate exhausted at line {line}: the lowering needs more branch events than Miri recorded"
          | _ => .ok (none, emitPoison st line)

/-- The block a recorded switch arm selects among charon's targets. -/
def switchTarget (cases : List (Nat × Nat)) (otherwise : Nat) : Option Nat → Nat
  | some v => (cases.lookup v).getD otherwise
  | none => otherwise

mutual

/-- Walk fn body blocks from `bb`, appending lowered statements.
    Returns the state at the fn's `Return`. -/
partial def walkBlock (crate : UCrate) (depth : Nat) (st : LowerSt)
    (f : UFun) (offset : Nat) (bb : Nat) (visited : List Nat) :
    Except String LowerSt := do
  if st.halted then return st else
  -- without a certificate a revisited block is a loop and the fragment
  -- is straight-line only; with one, loops UNROLL along the recorded
  -- branches, and only a branch-free cycle (which Miri would not have
  -- finished either) is rejected, by a visit budget
  if st.cert.isNone && visited.contains bb then
    .error s!"unsupported: control-flow loop in {f.name}"
  else if st.cert.isSome &&
      visited.length > ((st.cert.map (·.remaining)).getD 0 + 2) * (f.blocks.length + 1) then
    .error s!"unsupported: loop without a certified branch in {f.name}"
  else
  match f.blocks[bb]? with
  | none => .error s!"unsupported: dangling block bb{bb} in {f.name}"
  | some blk => do
    let mut st := st
    for s in blk.stmts do
      match s.kind with
      | .storage => pure ()
      | .unsupported d => throw s!"unsupported: {d} (line {s.line})"
      | .assign dst rv =>
          st ← emitAssign st s.line (rebasePlace offset dst) (rebaseRvalue offset rv)
    let line := blk.termLine
    match blk.term with
    | .ret => return st
    | .goto t => walkBlock crate depth st f offset t (bb :: visited)
    | .assert cond expected t kind =>
        let c := rebaseOperand offset cond
        let expectedW : Nat := if expected then 1 else 0
        match st.cert with
        | none =>
            -- no certificate: asserts must be statically satisfied
            match constOf st c with
            | some v =>
                if (v != 0) == expected then
                  walkBlock crate depth st f offset t (bb :: visited)
                else
                  .error s!"unsupported: statically failing assert (line {line})"
            | none => .error s!"unsupported: dynamic assert condition (line {line})"
        | some _ => do
            let (ev?, stE) ← consumeEvent st line
            st := stE
            match ev? with
            | none => return st   -- the certificate's UB prefix ended here
            | some ev =>
              match ev.kind with
              | .switch _ =>
                  .error s!"certificate: expected an assert ({kind}) at line {line}, Miri recorded a switch — event order mismatch ({ev.descr})"
              | .assert success =>
                if !success then
                  .error s!"unsupported: certified panic path ({kind}) at line {line}"
                else
                  match constOf st c with
                  | some v =>
                      -- T1: the lowering knows the condition; Miri must agree
                      if (v != 0) == expected then
                        walkBlock crate depth (certBump st 1) f offset t (bb :: visited)
                      else
                        .error s!"certificate disagrees with lowering at line {line}: assert ({kind}) condition folds to {v}, Miri passed it"
                  | none =>
                      match operandPlace? c with
                      | none => .error s!"certificate: assert condition is not a place (line {line})"
                      | some cp =>
                          -- T2: the condition is a runtime word — the same
                          -- word Miri's assert read — so CHECK it
                          walkBlock crate depth (emitCheckEq st line cp expectedW) f offset t (bb :: visited)
    | .switch discr cases otherwise =>
        let d := rebaseOperand offset discr
        match st.cert with
        | none => .error s!"unsupported: dynamic branch without a certificate (line {line})"
        | some _ => do
            let (ev?, stE) ← consumeEvent st line
            st := stE
            match ev? with
            | none => return st
            | some ev =>
              match ev.kind with
              | .assert _ =>
                  .error s!"certificate: expected a switch at line {line}, Miri recorded an assert — event order mismatch ({ev.descr})"
              | .switch arm =>
                let target := switchTarget cases otherwise arm
                match constOf st d with
                | some v =>
                    -- T1: cross-check the folded discriminant against Miri's arm
                    let mine := switchTarget cases otherwise (if v < 0 then none else some v.toNat)
                    if mine == target then
                      walkBlock crate depth (certBump st 1) f offset target (bb :: visited)
                    else
                      .error s!"certificate disagrees with lowering at line {line}: discriminant folds to {v}, Miri took arm {reprStr arm}"
                | none =>
                    match operandPlace? d with
                    | none => .error s!"certificate: switch on a non-place operand (line {line})"
                    | some dp =>
                      -- T2: the discriminant is a runtime word — the word
                      -- Miri's own `switchInt` read — so CHECK Miri's arm
                      -- against it before following the branch
                      st := match arm with
                        | some v => emitCheckEq st line dp v
                        | none => emitCheckNotIn st line dp (cases.map (·.1))
                      walkBlock crate depth st f offset target (bb :: visited)
    -- unwinding and aborts are exception machinery with no SB content
    | .unwindResume => .error s!"unsupported: reached unwind path in {f.name}"
    | .abort => .error s!"unsupported: reached abort in {f.name}"
    | .unsupported d => .error s!"unsupported: {d} (line {blk.termLine})"
    | .call funIdx args dest target => do
        let args := args.map (rebaseOperand offset)
        let dest := rebasePlace offset dest
        let st' ←
          match shimCall crate funIdx with
          | some shim => shim st args dest blk.termLine
          | none => inlineCall crate depth st funIdx args dest blk.termLine
        walkBlock crate depth st' f offset target (bb :: visited)
    | .callDyn fp args dest target => do
        -- indirect call: resolve the statically-tracked fn pointer
        let fp := rebasePlace offset fp
        let args := args.map (rebaseOperand offset)
        let dest := rebasePlace offset dest
        match fp with
        | { root := .local n, projs := [], .. } =>
            match st.fnPtrs.lookup n with
            | some funIdx => do
                let st' ←
                  match shimCall crate funIdx with
                  | some shim => shim st args dest blk.termLine
                  | none => inlineCall crate depth st funIdx args dest blk.termLine
                walkBlock crate depth st' f offset target (bb :: visited)
            | none => .error s!"unsupported: indirect call with unknown target (line {blk.termLine})"
        | _ => .error s!"unsupported: indirect call through a projection (line {blk.termLine})"

/-- Inline a call: extend the local space with the callee's locals, bind
    arguments (with seam retags), walk the body, bind the return value. -/
partial def inlineCall (crate : UCrate) (depth : Nat) (st : LowerSt)
    (funIdx : Nat) (args : List UOperand) (dest : UPlace) (line : Nat) :
    Except String LowerSt := do
  -- bounded depth guarantees static termination of inlining
  -- (recursion is rejected, not modeled)
  if depth == 0 then
    .error "unsupported: call inlining depth exceeded (recursion?)"
  else
  match crate.funs.find? (·.defId == funIdx) with
  | none => .error s!"unsupported: call to unknown function id {funIdx} (line {line})"
  | some f =>
    if !f.hasBody then
      .error s!"unsupported: call to bodyless function {f.name} (line {line})"
    else if args.length != f.argCount then
      .error s!"unsupported: arg count mismatch calling {f.name}"
    else do
      let offset := st.locals.length
      let mut st := { st with locals := st.locals ++ f.locals }
      -- enter the call's protector frame
      st := { st with out := .pushProt line :: st.out }
      -- bind args into callee arg locals (indices 1..argCount), with
      -- protected fn-entry retags for reference-typed components
      for h : i in [0:args.length] do
        let argLocal : UPlace := { root := .local (offset + 1 + i), projs := [] }
        let ty := f.locals[1 + i]? |>.getD (.unsupported "missing arg local")
        st ← emitSeamBind st line true argLocal ty args[i]
      -- the RETURN PLACE is passed in place too (Miri: "Protect return
      -- place for in-place return value passing"): the caller's
      -- destination is deinit'd and protected for the call, and receives
      -- the value after the frame pops. A unit destination has nothing to
      -- protect. `dest := uninit` first also roots an as-yet-unbound
      -- destination, which Miri, having no lazy allocation, never sees.
      let retTy := f.locals[0]? |>.getD (.unsupported "missing return local")
      if !(isUnitTy retTy) then
        st ← emitAssign st line dest .uninit
        st ← protectInPlace st line dest retTy
      -- open the callee's certificate frame (shims never do: they are
      -- std frames on Miri's side, which the extractor drops)
      match st.cert with
      | some c =>
          let c ← c.openFrame f.name
          st := { st with cert := some c }
      | none => pure ()
      -- walk the body
      st ← walkBlock crate (depth - 1) st f offset 0 []
      if st.halted then return st
      match st.cert with
      | some c =>
          let c ← c.closeFrame f.name
          st := { st with cert := some c }
      | none => pure ()
      -- leave the call: protectors end before the return value flows back
      st := { st with out := .popProt line :: st.out }
      -- bind the return value (callee local 0) into dest
      let retTy := f.locals[0]? |>.getD (.unsupported "missing return local")
      if isUnitTy retTy then
        return st
      else
        let retLocal : UPlace := { root := .local offset, projs := [] }
        if containsRef retTy then
          emitSeamCopy st line false dest retTy retLocal
        else
          emitAssign st line dest (.use (.copy retLocal))

end

/-- Rewrite hoisted-global place roots to their assigned locals. -/
def resolveGlobalRoot (gmap : List (Nat × Nat)) (p : UPlace) : Except String UPlace :=
  match p.root with
  | .local _ => .ok p
  | .global gid =>
      match gmap.lookup gid with
      | some idx => .ok { p with root := .local idx }
      | none => .error s!"unsupported: reference to unhoisted global {gid}"

def resolveGlobalsOp (gmap : List (Nat × Nat)) : UOperand → Except String UOperand
  | .copy p => do return .copy (← resolveGlobalRoot gmap p)
  | .move p => do return .move (← resolveGlobalRoot gmap p)
  | op => .ok op

def resolveGlobalsRv (gmap : List (Nat × Nat)) : URvalue → Except String URvalue
  | .use op => do return .use (← resolveGlobalsOp gmap op)
  | .move p => do return .move (← resolveGlobalRoot gmap p)
  | .ref kind prot p => do return .ref kind prot (← resolveGlobalRoot gmap p)
  | .aggregate v ops => do return .aggregate v (← ops.mapM (resolveGlobalsOp gmap))
  | .exposeAddr p => do return .exposeAddr (← resolveGlobalRoot gmap p)
  | .fromExposed p => do return .fromExposed (← resolveGlobalRoot gmap p)
  | .ptrOffset p d => do return .ptrOffset (← resolveGlobalRoot gmap p) d
  | .refSlice kind prot p => do return .refSlice kind prot (← resolveGlobalRoot gmap p)
  | .discriminant p => do return .discriminant (← resolveGlobalRoot gmap p)
  | .sliceLen p => do return .sliceLen (← resolveGlobalRoot gmap p)
  | .subSlice p lo hi => do
      return .subSlice (← resolveGlobalRoot gmap p) (← resolveGlobalsOp gmap lo)
        (← resolveGlobalsOp gmap hi)
  | .binOp op a b => do
      return .binOp op (← resolveGlobalsOp gmap a) (← resolveGlobalsOp gmap b)
  | rv => .ok rv

def resolveGlobalsStmt (gmap : List (Nat × Nat)) : LStmt → Except String LStmt
  | .assign dst rv line => do
      return .assign (← resolveGlobalRoot gmap dst) (← resolveGlobalsRv gmap rv) line
  | .assignIf discr v dst rv line => do
      return .assignIf (← resolveGlobalRoot gmap discr) v
        (← resolveGlobalRoot gmap dst) (← resolveGlobalsRv gmap rv) line
  | .alloc dst sz line => do
      let sz ← match sz with
        | some op => pure (some (← resolveGlobalsOp gmap op))
        | none => pure none
      return .alloc (← resolveGlobalRoot gmap dst) sz line
  | .dealloc p line => do
      return .dealloc (← resolveGlobalRoot gmap p) line
  | s => .ok s

/-- Lower a crate's `main` into a flat program.

    Statics hoisting: every global becomes a fresh local appended after
    main's locals, materialized `uninit` at pc 0; `Global` place roots are
    rewritten to those locals. Initializer bodies are NOT run — hoisted
    statics start undef, which is fine for SB purposes as long as the
    program writes them before any value-dependent use (documented
    divergence: real statics have interned, initialized allocations). -/
def lowerCrate (crate : UCrate) (cert? : Option Cert := none) : Except String LProg := do
  match crate.funs.find? (·.name == "main") with
  | none => .error "no main function in crate"
  | some main =>
    if !main.hasBody then .error "main has no body"
    else do
      let base := main.locals.length
      let gmap := crate.globals.zipIdx.map (fun (g, i) => (g.gid, base + i))
      let hoistInit : List LStmt :=
        (crate.globals.zipIdx.map (fun (_, i) =>
          LStmt.assign { root := .local (base + i), projs := [] } .uninit 0)).reverse
      -- with a certificate: two scratch words for the checks, and main's
      -- frame opened
      let nGlob := crate.globals.length
      let st0 : LowerSt ← match cert? with
        | none => pure { locals := main.locals ++ crate.globals.map (·.ty), out := hoistInit }
        | some cert => do
            let c ← ({ cert } : CertCursor).openFrame main.name
            pure { locals := main.locals ++ crate.globals.map (·.ty) ++ [.nat, .nat],
                   out := hoistInit, cert := some c,
                   certBad := base + nGlob, certTmp := base + nGlob + 1 }
      let st ← walkBlock crate 8 st0 main 0 0 []
      let st ← match st.cert with
        | some c => if st.halted then pure st else do
            let c ← c.closeFrame main.name
            pure { st with cert := some c }
        | none => pure st
      let stmts ← st.out.reverse.mapM (resolveGlobalsStmt gmap)
      let stats : CertStats := match st.cert with
        | some c => { used := true, checked := c.checked, runtime := c.runtime, pinned := c.pinned }
        | none => {}
      return { locals := st.locals, stmts, stats }

end conformance
