import conformance.ullbc_ast

/-!
ULLBC → flat statement list, in the obseq3-expressible fragment.

Passes (fused into one walk):
1. **Inline** all calls in `main` (callee locals renumbered into one global
   local space; recursion/indirect calls rejected).
2. **Linearize**: follow `goto`/call-target edges from bb0; a revisited
   block means a loop → unsupported. Unwind edges are never followed.
3. **Drop** StorageLive/Dead, Borrowck/FakeRead, Nop, PlaceMention, and
   unit-aggregate assignments (no memory access in Miri either).
4. **Desugar** non-empty tuple aggregates into per-field assignments.
5. **Seam retags**: reference-typed arguments and return values are
   re-tagged at inline seams (`arg := &mut *callerPtr`), mirroring Miri's
   Retag-on-function-entry/exit. Raw-typed args are copied untagged.

Any construct outside the fragment yields `.error "unsupported: …"`,
which the harness reports as the test's unsupported-reason.
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
deriving Repr, Inhabited

structure LowerSt where
  locals : List UTy
  out : List LStmt   -- reversed
  fnPtrs : List (Nat × Nat) := []   -- rebased local ↦ fun defId (reified fn ptrs)
  constVals : List (Nat × Nat) := []  -- rebased local ↦ known constant word (index resolution)

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
  | .ref kind prot p => .ref kind prot (rebasePlace off p)
  | .aggregate v ops => .aggregate v (ops.map (rebaseOperand off))
  | .exposeAddr p => .exposeAddr (rebasePlace off p)
  | .fromExposed p => .fromExposed (rebasePlace off p)
  | .ptrOffset p d => .ptrOffset (rebasePlace off p) d
  | .refSlice kind prot p => .refSlice kind prot (rebasePlace off p)
  | .binOp op a b => .binOp op (rebaseOperand off a) (rebaseOperand off b)
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
        match st.constVals.lookup l with
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
def constOf (st : LowerSt) : UOperand → Option Int
  | .const n => some (Int.ofNat n)
  | .constNeg n => some (-(Int.ofNat n))
  | .copy { root := .local l, projs := [], .. } => (st.constVals.lookup l).map Int.ofNat
  | .move { root := .local l, projs := [], .. } => (st.constVals.lookup l).map Int.ofNat
  | _ => none

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
  | .ref kind prot p => do return .ref kind prot (← resolveIdxPlace st line p)
  | .aggregate v ops => do return .aggregate v (← ops.mapM (resolveIdxOperand st line))
  | .exposeAddr p => do return .exposeAddr (← resolveIdxPlace st line p)
  | .fromExposed p => do return .fromExposed (← resolveIdxPlace st line p)
  | .ptrOffset p d => do return .ptrOffset (← resolveIdxPlace st line p) d
  | .refSlice kind prot p => do return .refSlice kind prot (← resolveIdxPlace st line p)
  | rv => pure rv

/-- Does this type contain a reference (transitively through tuples and
    enum payloads)? Raw pointers don't count — not retagged at seams.
    UnsafeCell contents don't count either: Miri's retag visitor does
    not descend into interior-mutable regions. -/
partial def containsRef : UTy → Bool
  | .ref _ _ => true
  | .slice false _ _ => true   -- reference-to-slice: seam-retagged (runtime length)
  | .tup tys => tys.any containsRef
  | .structT _ => false  -- miri does NOT fn-entry-retag named-struct fields
                         -- (fnentry_invalidation2's point); tuples ARE retagged
  | .enum variants => variants.any (·.any containsRef)
  | .cell _ => false
  | _ => false

/-- Retag/copy `src` into `dst` at a retag point (inline seam or a
    reference-typed load through a deref): every reference — including
    refs inside tuples and enum payloads — is retagged; enum payload
    accesses are guarded on the discriminant (`assignIf`). Non-ref
    components are plain copies. -/
partial def emitSeamCopy (st : LowerSt) (line : Nat) (prot : Bool) (dst : UPlace)
    (ty : UTy) (src : UPlace) : Except String LowerSt := do
  match ty with
  | .ref mutbl inner =>
      -- pointee ty drives the UnsafeCell freeze mask at elaboration
      return pushOut st (.assign dst
        (.ref (if mutbl then .mut else .shared) prot
          { pointee src with ty := inner }) line)
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
      -- discriminant is payload slot 0; variant v's field i lives at 1+i
      let mut st := pushOut st (.assign (fld dst 0) (.use (.copy (fld src 0))) line)
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
              else
                st := pushOut st (.assignIf (fld src 0) v dstF (.use (.copy srcF)) line)
      return st
  | _ => return pushOut st (.assign dst (.use (.copy src)) line)

/-- Append one lowered assignment, desugaring aggregates, applying the
    reference-load retag rule, and rejecting unsupported payloads.
    Places/rvalues must already be rebased. -/
partial def emitAssign (st : LowerSt) (line : Nat) (dst : UPlace) (rv : URvalue) :
    Except String LowerSt := do
  let dst ← resolveIdxPlace st line dst
  let rv ← resolveIdxRvalue st line rv
  -- track constant-valued plain locals (array-index resolution)
  let st :=
    match dst, rv with
    | { root := .local d, projs := [], .. }, .use (.const n) =>
        { st with constVals := (d, n) :: st.constVals }
    | { root := .local d, projs := [], .. }, _ =>
        { st with constVals := st.constVals.filter (·.1 != d) }
    | _, _ => st
  match rv with
  | .unsupported d => .error s!"unsupported: {d} (line {line})"
  | .use .constUnit =>
      return st  -- unit value: no memory access
  | .use (.constNeg _) =>
      -- negative constants clamp to 0 in value positions (SB-irrelevant)
      return pushOut st (.assign dst (.use (.const 0)) line)
  | .ptrOffset _ _ | .refSlice _ _ _ =>
      return pushOut st (.assign dst rv line)
  | .binOp op a b =>
      -- arithmetic exists only in statically-foldable positions (array
      -- bounds checks and the like); dynamic arithmetic is unsupported
      match constOf st a, constOf st b with
      | some x, some y =>
          match foldBinOp op x y with
          | some v =>
              if v < 0 then
                .error s!"unsupported: negative arithmetic result (line {line})"
              else
                emitAssign st line dst (.use (.const v.toNat))
          | none => .error s!"unsupported: binary op {op} (line {line})"
      | _, _ => .error s!"unsupported: non-constant arithmetic (line {line})"
  | .use (.copy p) | .use (.move p) =>
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
  | .ref _ _ _ | .uninit | .exposeAddr _ | .fromExposed _ =>
      return pushOut st (.assign dst rv line)
  | .fnRef fid =>
      -- reified fn pointer: track statically, store a placeholder word
      match dst with
      | { root := .local n, projs := [], .. } =>
          return { pushOut st (.assign dst (.use (.const 0)) line)
                   with fnPtrs := (n, fid) :: st.fnPtrs }
      | _ => .error s!"unsupported: fn pointer stored into a projection (line {line})"
  | .aggregate none [] =>
      return st  -- unit value: no memory access
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

/-- Bind one value into a fresh local at an inline seam, retagging if the
    type contains references. -/
def emitSeamBind (st : LowerSt) (line : Nat) (prot : Bool) (dstLocal : UPlace)
    (ty : UTy) (op : UOperand) : Except String LowerSt := do
  if containsRef ty then
    match op with
    | .copy p | .move p => emitSeamCopy st line prot dstLocal ty p
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
  if f.path == ["alloc", "boxed", "new"] then
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
  else if f.path == ["core", "alloc", "layout", "from_size_align_unchecked"] then
    some fun st args dest line => do
      match args with
      | szOp :: _ => emitAssign st line dest (.use szOp)
      | _ => .error s!"unsupported: from_size_align_unchecked arity (line {line})"
  else if f.path == ["core", "cell", "new"] then
    -- UnsafeCell/Cell are layout-transparent: the constructor is identity
    some fun st args dest line => do
      match dest.ty, args with
      | .cell _, [valOp] => emitAssign st line dest (.use valOp)
      | _, [_] => .error s!"unsupported: non-Cell core::cell constructor (line {line})"
      | _, _ => .error s!"unsupported: cell constructor arity (line {line})"
  else if f.path == ["core", "cell", "get"] then
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
          f.path == ["core", "ptr", "const_ptr", "read"] ||
          f.path == ["core", "ptr", "mut_ptr", "read"] then
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
  else if f.path == ["core", "ptr", "const_ptr", "expose_provenance"] ||
          f.path == ["core", "ptr", "mut_ptr", "expose_provenance"] then
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
  else if f.path == ["core", "cell", "set"] then
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
  else if f.path == ["core", "cell", "borrow"] then
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
  else if f.path == ["core", "cell", "borrow_mut"] then
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
  else if f.path == ["core", "cell", "deref"] || f.path == ["core", "cell", "deref_mut"] then
    -- Ref/RefMut deref: a typed load of the guard's pointer at the
    -- destination's reference type — the load-retag rule then produces
    -- the fresh (re)borrow, matching miri's deref reborrow
    some fun st args dest line => do
      match args with
      | [.copy p] | [.move p] =>
          emitAssign st line dest (.use (.copy { pointee p with ty := dest.ty }))
      | _ => .error s!"unsupported: guard deref argument is not a place (line {line})"
  else if f.path == ["core", "cell", "replace"] then
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
  else if (f.path == ["core", "ptr", "mut_ptr", "add"] ||
           f.path == ["core", "ptr", "const_ptr", "add"] ||
           f.path == ["core", "ptr", "mut_ptr", "offset"] ||
           f.path == ["core", "ptr", "const_ptr", "offset"] ||
           f.path == ["core", "ptr", "mut_ptr", "wrapping_add"] ||
           f.path == ["core", "ptr", "const_ptr", "wrapping_add"] ||
           f.path == ["core", "ptr", "mut_ptr", "wrapping_offset"] ||
           f.path == ["core", "ptr", "const_ptr", "wrapping_offset"]) then
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
  else if f.path == ["core", "slice", "as_ptr"] ||
          f.path == ["core", "slice", "as_mut_ptr"] then
    -- slice data pointer. The shim replaces the whole call, so it must
    -- reproduce the fn-entry retag of the &[T]/&mut [T] receiver (that
    -- retag's write access is the invalidation fnentry_invalidation2
    -- tests), then the raw retag of the data the body performs.
    some fun st args dest line => do
      let mutbl := f.path == ["core", "slice", "as_mut_ptr"]
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
  else if f.path == ["core", "mem", "drop"] then
    -- mem::drop: consumes the value; drop glue for modeled types is
    -- either nothing or elided flag maintenance (RefCell guards)
    some fun st _args _dest _line => return st
  else if f.path == ["core", "cell", "get_mut"] then
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

mutual

/-- Walk fn body blocks from `bb`, appending lowered statements.
    Returns the state at the fn's `Return`. -/
partial def walkBlock (crate : UCrate) (depth : Nat) (st : LowerSt)
    (f : UFun) (offset : Nat) (bb : Nat) (visited : List Nat) :
    Except String LowerSt := do
  if visited.contains bb then
    .error s!"unsupported: control-flow loop in {f.name}"
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
    match blk.term with
    | .ret => return st
    | .goto t => walkBlock crate depth st f offset t (bb :: visited)
    | .assert cond expected t =>
        -- asserts must be statically satisfied (bounds checks on
        -- constant indices); a failing or dynamic assert is unsupported
        match constOf st (rebaseOperand offset cond) with
        | some v =>
            if (v != 0) == expected then
              walkBlock crate depth st f offset t (bb :: visited)
            else
              .error s!"unsupported: statically failing assert (line {blk.termLine})"
        | none => .error s!"unsupported: dynamic assert condition (line {blk.termLine})"
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
      -- walk the body
      st ← walkBlock crate (depth - 1) st f offset 0 []
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
  | .ref kind prot p => do return .ref kind prot (← resolveGlobalRoot gmap p)
  | .aggregate v ops => do return .aggregate v (← ops.mapM (resolveGlobalsOp gmap))
  | .exposeAddr p => do return .exposeAddr (← resolveGlobalRoot gmap p)
  | .fromExposed p => do return .fromExposed (← resolveGlobalRoot gmap p)
  | .ptrOffset p d => do return .ptrOffset (← resolveGlobalRoot gmap p) d
  | .refSlice kind prot p => do return .refSlice kind prot (← resolveGlobalRoot gmap p)
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
def lowerCrate (crate : UCrate) : Except String LProg := do
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
      let st0 : LowerSt :=
        { locals := main.locals ++ crate.globals.map (·.ty), out := hoistInit }
      let st ← walkBlock crate 8 st0 main 0 0 []
      let stmts ← st.out.reverse.mapM (resolveGlobalsStmt gmap)
      return { locals := st.locals, stmts }

end conformance
