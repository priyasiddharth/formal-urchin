import conformance.emit

/-!
# stdlite: models of the std functions the corpus calls

A call to a bodyless std function is lowered by the SHIM registered for its
path (rendered with impl segments, `nameSegs` in `ullbc_ast.lean`): a
handler that emits what the function does to memory and the borrow
stacks, instead of inlining a body. One definition per shim; `table` maps
each modelled path to its handler. A path absent from `table` is not
modelled, and the call is rejected as a call to a bodyless function.

Heap: `Box::new(v)` allocates one pointee and stores `v` through it;
`std::alloc::alloc(layout)` allocates `layout` cells (a Layout is modelled
as its size word, see `layoutFromSizeAlignUnchecked`); `dealloc(ptr, _)`
frees (size from the allocation).
-/

namespace conformance.stdlite

open conformance

/-- A shim: lower one call, given its arguments, destination and line. -/
abbrev Shim := LowerSt → List UOperand → UPlace → Nat → Except String LowerSt

def boxNew : Shim := fun st args dest line => do
  match args with
  | [valOp] => do
      let st := pushOut st (.alloc dest none line)
      emitAssign st line (pointee dest) (.use valOp)
  | _ => .error s!"unsupported: Box::new arity (line {line})"

def alloc : Shim := fun st args dest line => do
  match args with
  | [layoutOp] => return pushOut st (.alloc dest (some layoutOp) line)
  | _ => .error s!"unsupported: alloc arity (line {line})"

def dealloc : Shim := fun st args _dest line => do
  match args with
  | .copy p :: _ | .move p :: _ => return pushOut st (.dealloc p line)
  | _ => .error s!"unsupported: dealloc argument is not a place (line {line})"

/-- Layout::for_value(&T): the size word, statically from the pointee -/
def layoutForValue : Shim := fun st args dest line => do
  match args with
  | [.copy p] | [.move p] =>
      let sz := match p.ty with
        | .ref _ i | .raw _ i => uSize i
        | _ => 1
      emitAssign st line dest (.use (.const sz))
  | _ => .error s!"unsupported: for_value argument is not a place (line {line})"

def layoutFromSizeAlignUnchecked : Shim := fun st args dest line => do
  match args with
  | szOp :: _ => emitAssign st line dest (.use szOp)
  | _ => .error s!"unsupported: from_size_align_unchecked arity (line {line})"

/-- UnsafeCell/Cell are layout-transparent: the constructor is identity -/
def cellNew : Shim := fun st args dest line => do
  match dest.ty, args with
  | .cell _, [valOp] => emitAssign st line dest (.use valOp)
  | _, [_] => .error s!"unsupported: non-Cell core::cell constructor (line {line})"
  | _, _ => .error s!"unsupported: cell constructor arity (line {line})"

/-- Cell::get(&self) -> T: a masked shared reborrow of the cell region
    (the `UnsafeCell::get` inside it), then a read through it -/
def cellGet : Shim := fun st args dest line => do
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

/-- UnsafeCell::get(&self) -> *mut T: a raw reborrow of the cell region;
    the pointee type carries the freeze mask (all-cell → SharedReadWrite) -/
def unsafeCellGet : Shim := fun st args dest line => do
  match args with
  | [.copy p] | [.move p] =>
      let inner := match p.ty with
        | .ref _ i => i
        | .raw _ i => i
        | _ => .unsupported "cell get on non-pointer"
      return pushOut st (.assign dest
        (.ref .shared false { pointee p with ty := inner }) line)
  | _ => .error s!"unsupported: cell get argument is not a place (line {line})"

/-- ptr::read(p): a plain read of *p (with the reference-load retag
    rule applied by emitAssign when the value contains refs) -/
def ptrRead : Shim := fun st args dest line => do
  match args with
  | [.copy p] | [.move p] =>
      let inner := match p.ty with
        | .ref _ i => i
        | .raw _ i => i
        | _ => .unsupported "ptr::read on non-pointer"
      emitAssign st line dest (.use (.copy { pointee p with ty := inner }))
  | _ => .error s!"unsupported: ptr::read argument is not a place (line {line})"

/-- transmute by value: fn ptrs are tracked statically; a transmute to a
    reference type is a real retag (miri retags such lets); a transmute
    to a raw type is a tag-preserving reinterpret (ptrCast at elab) -/
def transmute : Shim := fun st args dest line => do
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

/-- transmute_copy(&src) -> D: read *src at type D (load retags apply
    when D contains references; raw destinations keep the tag) -/
def transmuteCopy : Shim := fun st args dest line => do
  match args with
  | [.copy p] | [.move p] =>
      emitAssign st line dest (.use (.copy { pointee p with ty := dest.ty }))
  | _ => .error s!"unsupported: transmute_copy argument is not a place (line {line})"

def exposeProvenance : Shim := fun st args dest line => do
  match args with
  | [.copy p] | [.move p] =>
      return pushOut st (.assign dest (.exposeAddr p) line)
  | _ => .error s!"unsupported: expose_provenance argument is not a place (line {line})"

def withExposedProvenance : Shim := fun st args dest line => do
  match args with
  | [.copy p] | [.move p] =>
      return pushOut st (.assign dest (.fromExposed p) line)
  | _ => .error s!"unsupported: with_exposed_provenance argument is not a place (line {line})"

/-- Cell::set(&self, v): a masked shared reborrow of the cell region,
    then a write through it -/
def cellSet : Shim := fun st args _dest line => do
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

/-- RefCell::borrow (flag-elided): a masked shared reborrow of the
    value region; the guard holds the resulting pointer -/
def refCellBorrow : Shim := fun st args dest line => do
  match args with
  | [.copy p] | [.move p] =>
      let inner := match p.ty with
        | .ref _ i => i
        | .raw _ i => i
        | _ => .unsupported "borrow on non-pointer"
      return pushOut st (.assign dest
        (.ref .shared false { pointee p with ty := inner }) line)
  | _ => .error s!"unsupported: borrow argument is not a place (line {line})"

/-- RefCell::borrow_mut (flag-elided): a unique reborrow of the value
    region (the parent's SharedReadWrite cell items grant the write) -/
def refCellBorrowMut : Shim := fun st args dest line => do
  match args with
  | [.copy p] | [.move p] =>
      let inner := match p.ty with
        | .ref _ i => i
        | .raw _ i => i
        | _ => .unsupported "borrow_mut on non-pointer"
      return pushOut st (.assign dest
        (.ref .mut false { pointee p with ty := inner }) line)
  | _ => .error s!"unsupported: borrow_mut argument is not a place (line {line})"

/-- Ref/RefMut deref: a typed load of the guard's pointer at the
    destination's reference type — the load-retag rule then produces
    the fresh (re)borrow, matching miri's deref reborrow -/
def guardDeref : Shim := fun st args dest line => do
  match args with
  | [.copy p] | [.move p] =>
      emitAssign st line dest (.use (.copy { pointee p with ty := dest.ty }))
  | _ => .error s!"unsupported: guard deref argument is not a place (line {line})"

/-- Cell/RefCell::replace(&self, v) -> T (flag-elided): masked shared
    reborrow, read the old value, write the new one -/
def cellReplace : Shim := fun st args dest line => do
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

/-- pointer arithmetic with a constant delta (scaled by the pointee
    size at elaboration); provenance/tag is preserved -/
def ptrOffset : Shim := fun st args dest line => do
  match args with
  | [.copy p, d] | [.move p, d] =>
      let delta ← match d with
        | .const n => pure (Int.ofNat n)
        | .constNeg n => pure (-(Int.ofNat n))
        | _ => throw s!"unsupported: runtime pointer offset (line {line})"
      return pushOut st (.assign dest (.ptrOffset p delta) line)
  | _ => .error s!"unsupported: pointer offset arguments (line {line})"

/-- `&s[lo..hi]` / `&mut s[lo..hi]`: the std chain bottoms out in
    `from_raw_parts_mut(ptr.add(lo), hi - lo)`, i.e. a retag over the
    NARROWED range. The shim replaces the whole call and reproduces
    the two retags it performs: the fn-entry retag of the receiver
    (over its whole extent) and the mint over the sub-range. The
    narrowing between them is pure pointer arithmetic (`subSlice`).
    
    The range argument is a `Range { start, end }` aggregate: a place
    whose two fields are the bounds. A full range (`..`) has no
    fields, and is the identity narrowing `0 .. len`. -/
def sliceIndex (mutbl : Bool) : Shim := fun st args dest line => do
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

/-- `<[T]>::len(&self)`: the metadata of the fat pointer argument. The
    shim replaces the whole call, and the length read is not an access
    to the slice DATA — only to the local holding the pointer, which
    is what `sliceLen` performs (copy's read of that cell). -/
def sliceLen : Shim := fun st args dest line => do
  match args with
  | [.copy p] | [.move p] =>
      return pushOut st (.assign dest (.sliceLen p) line)
  | _ => .error s!"unsupported: slice len argument is not a place (line {line})"

/-- slice data pointer. The shim replaces the whole call, so it must
    reproduce the fn-entry retag of the &[T]/&mut [T] receiver (that
    retag's write access is the invalidation fnentry_invalidation2
    tests), then the raw retag of the data the body performs. -/
def sliceAsPtr (mutbl : Bool) : Shim := fun st args dest line => do
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

/-- Box::from_raw: adopts the raw pointer's tag (a plain value copy;
    the box retag happens at the next seam) -/
def boxFromRaw : Shim := fun st args dest line => do
  match args with
  | [.copy p] | [.move p] =>
      return pushOut st (.assign dest (.use (.copy p)) line)
  | _ => .error s!"unsupported: from_raw argument is not a place (line {line})"

/-- Box::into_raw(b) -> *mut T. The std body is
    `let mut b = ManuallyDrop::new(b); (&mut **b) as *mut T`, written so
    that Stacked Borrows sees a retag; under SB that is three retags of
    the pointee: the fn-entry Unique retag of the Box argument, the
    `&mut **b` Unique reborrow, and the raw retag that is the result.
    The argument's protector is omitted: it ends when `into_raw` returns,
    and the only accesses meanwhile are these reborrows of its own tag,
    which it cannot fail. -/
def boxIntoRaw : Shim := fun st args dest line => do
  match args with
  | [.copy b] | [.move b] =>
      let inner ← match b.ty with
        | .boxT i => pure i
        | _ => throw s!"unsupported: Box::into_raw on a non-Box argument (line {line})"
      let t1 := st.locals.length
      let st := { st with locals := st.locals ++ [.ref true inner, .ref true inner] }
      let tmp1 : UPlace := { root := .local t1, projs := [], ty := .ref true inner }
      let tmp2 : UPlace := { root := .local (t1 + 1), projs := [], ty := .ref true inner }
      -- the fn-entry retag of the Box argument
      let st := pushOut st (.assign tmp1 (.ref .mut false { pointee b with ty := inner }) line)
      -- `&mut **b`
      let st := pushOut st (.assign tmp2 (.ref .mut false { pointee tmp1 with ty := inner }) line)
      -- `as *mut T`
      return pushOut st (.assign dest (.ref .rawMut false { pointee tmp2 with ty := inner }) line)
  | _ => .error s!"unsupported: Box::into_raw argument is not a place (line {line})"

/-- mem::forget: no drop, no access; protectors end at fn return anyway -/
def memForget : Shim := fun st _args _dest _line => return st

/-- mem::drop: consumes the value; drop glue for modeled types is
    either nothing or elided flag maintenance (RefCell guards) -/
def memDrop : Shim := fun st _args _dest _line => return st

/-- Cell::get_mut(&mut self) -> &mut T: a unique reborrow of the cell -/
def cellGetMut : Shim := fun st args dest line => do
  match args with
  | [.copy p] | [.move p] =>
      let inner := match p.ty with
        | .ref _ i => i
        | .raw _ i => i
        | _ => .unsupported "cell get_mut on non-pointer"
      return pushOut st (.assign dest
        (.ref .mut false { pointee p with ty := inner }) line)
  | _ => .error s!"unsupported: Cell::get_mut argument is not a place (line {line})"

/-- Every modelled std path and its shim. Paths are distinct, so the
    order is immaterial; grouped as the shims above. -/
def table : List (List String × Shim) :=
  [ (["alloc", "boxed", "Box", "new"], boxNew)
  , (["alloc", "alloc", "alloc"], alloc)
  , (["alloc", "alloc", "dealloc"], dealloc)
  , (["core", "alloc", "layout", "Layout", "for_value"], layoutForValue)
  , (["core", "alloc", "layout", "Layout", "from_size_align_unchecked"], layoutFromSizeAlignUnchecked)
  , (["core", "cell", "Cell", "new"], cellNew)
  , (["core", "cell", "UnsafeCell", "new"], cellNew)
  , (["core", "cell", "RefCell", "new"], cellNew)
  , (["core", "cell", "Cell", "get"], cellGet)
  , (["core", "cell", "UnsafeCell", "get"], unsafeCellGet)
  , (["core", "ptr", "read"], ptrRead)
  , (["core", "ptr", "const_ptr", "*const T", "read"], ptrRead)
  , (["core", "ptr", "mut_ptr", "*mut T", "read"], ptrRead)
  , (["core", "intrinsics", "transmute"], transmute)
  , (["core", "mem", "transmute_copy"], transmuteCopy)
  , (["core", "ptr", "const_ptr", "*const T", "expose_provenance"], exposeProvenance)
  , (["core", "ptr", "mut_ptr", "*mut T", "expose_provenance"], exposeProvenance)
  , (["core", "ptr", "with_exposed_provenance_mut"], withExposedProvenance)
  , (["core", "ptr", "with_exposed_provenance"], withExposedProvenance)
  , (["core", "cell", "Cell", "set"], cellSet)
  , (["core", "cell", "RefCell", "borrow"], refCellBorrow)
  , (["core", "cell", "RefCell", "borrow_mut"], refCellBorrowMut)
  , (["core", "cell", "<Ref as Deref>", "deref"], guardDeref)
  , (["core", "cell", "<RefMut as Deref>", "deref"], guardDeref)
  , (["core", "cell", "<RefMut as DerefMut>", "deref_mut"], guardDeref)
  , (["core", "cell", "Cell", "replace"], cellReplace)
  , (["core", "cell", "RefCell", "replace"], cellReplace)
  , (["core", "ptr", "mut_ptr", "*mut T", "add"], ptrOffset)
  , (["core", "ptr", "const_ptr", "*const T", "add"], ptrOffset)
  , (["core", "ptr", "mut_ptr", "*mut T", "offset"], ptrOffset)
  , (["core", "ptr", "const_ptr", "*const T", "offset"], ptrOffset)
  , (["core", "ptr", "mut_ptr", "*mut T", "wrapping_add"], ptrOffset)
  , (["core", "ptr", "const_ptr", "*const T", "wrapping_add"], ptrOffset)
  , (["core", "ptr", "mut_ptr", "*mut T", "wrapping_offset"], ptrOffset)
  , (["core", "ptr", "const_ptr", "*const T", "wrapping_offset"], ptrOffset)
  , (["core", "slice", "index", "<[T] as Index>", "index"], (sliceIndex false))
  , (["core", "slice", "index", "<[T] as IndexMut>", "index_mut"], (sliceIndex true))
  , (["core", "slice", "[T]", "get_unchecked"], (sliceIndex false))
  , (["core", "slice", "[T]", "get_unchecked_mut"], (sliceIndex true))
  , (["core", "array", "<[T; N] as Index>", "index"], (sliceIndex false))
  , (["core", "array", "<[T; N] as IndexMut>", "index_mut"], (sliceIndex true))
  , (["core", "slice", "[T]", "len"], sliceLen)
  , (["core", "slice", "[T]", "as_ptr"], (sliceAsPtr false))
  , (["core", "slice", "[T]", "as_mut_ptr"], (sliceAsPtr true))
  , (["alloc", "boxed", "Box", "from_raw"], boxFromRaw)
  , (["alloc", "boxed", "Box", "into_raw"], boxIntoRaw)
  , (["core", "mem", "forget"], memForget)
  , (["core", "mem", "drop"], memDrop)
  , (["core", "cell", "Cell", "get_mut"], cellGetMut)
  , (["core", "cell", "UnsafeCell", "get_mut"], cellGetMut)
  , (["core", "cell", "RefCell", "get_mut"], cellGetMut)
  ]

end conformance.stdlite

namespace conformance

/-- The shim for a call to fun `funIdx`, if its path is modelled. -/
def shimCall (crate : UCrate) (funIdx : Nat) : Option stdlite.Shim := do
  let f ← crate.funs.find? (·.defId == funIdx)
  stdlite.table.lookup f.path

end conformance
