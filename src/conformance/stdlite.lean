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
`std::alloc::alloc(layout)` allocates `layout` bytes (a Layout is modelled
as its size in bytes, see `layoutFromSizeAlignUnchecked`; the result is a
`*mut u8`, whose pointee is one byte); `dealloc(ptr, _)`
frees (size from the allocation).
-/

namespace conformance.stdlite

open conformance

/-- A shim: lower one call, given its arguments, destination and line. -/
abbrev Shim := LowerSt → List UOperand → UPlace → Nat → Except String LowerSt

def boxNew : Shim := fun st args dest line => do
  match args with
  | [valOp] => do
      let st := emitAlloc st line dest none
      emitAssign st line (pointee dest) (.use valOp)
  | _ => .error s!"unsupported: Box::new arity (line {line})"

def alloc : Shim := fun st args dest line => do
  match args with
  | [layoutOp] => return emitAlloc st line dest (some layoutOp)
  | _ => .error s!"unsupported: alloc arity (line {line})"

def dealloc : Shim := fun st args _dest line => do
  match args with
  | .copy p :: _ | .move p :: _ => return pushOut st (.dealloc p line)
  | _ => .error s!"unsupported: dealloc argument is not a place (line {line})"

/-- Layout::for_value(&T): the size word in BYTES, statically from the
    pointee. -/
def layoutForValue : Shim := fun st args dest line => do
  match args with
  | [.copy p] | [.move p] =>
      let sz := match p.ty with
        | .ref _ i | .raw _ i => sizeB i
        | _ => 8
      emitAssign st line dest (.use (.const sz))
  | _ => .error s!"unsupported: for_value argument is not a place (line {line})"

def layoutFromSizeAlignUnchecked : Shim := fun st args dest line => do
  match args with
  | szOp :: _ => emitAssign st line dest (.use szOp)
  | _ => .error s!"unsupported: from_size_align_unchecked arity (line {line})"

/-- UnsafeCell/Cell are layout-transparent: the constructor is identity.
    `Atomic<T>::new` too: an `Atomic*` is modelled as a cell around one
    word (`parseTy`). -/
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
      let rv : URvalue := .ref .shared false { pointee p with ty := inner }
      return pushOut (trackAssign st dest rv) (.assign dest rv line)
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
        | .int _ | .nat =>
            -- pointer → integer: the address, provenance stripped
            match p.ty with
            | .raw _ _ | .ref _ _ => return pushOut st (.assign dest (.addr p) line)
            | _ => .error s!"unsupported: transmute to non-pointer type (line {line})"
        | _ => .error s!"unsupported: transmute to non-pointer type (line {line})"
  | _ => .error s!"unsupported: transmute argument is not a place (line {line})"

/-- transmute_copy(&src) -> D: read *src at type D (load retags apply
    when D contains references; raw destinations keep the tag) -/
def transmuteCopy : Shim := fun st args dest line => do
  match args with
  | [.copy p] | [.move p] =>
      emitAssign st line dest (.use (.copy { pointee p with ty := dest.ty }))
  | _ => .error s!"unsupported: transmute_copy argument is not a place (line {line})"

/-- `ptr::without_provenance(addr)`: a pointer with NO provenance. Its bytes
    are the integer's, read back at pointer type — a scratch `usize` holding
    `addr`, read through a raw pointer retyped to `*const *T`. The byte
    decode gives a pointer over zero bytes that may only be used for
    zero-sized accesses (MiniRust's int-to-ptr transmute). -/
def withoutProvenance : Shim := fun st args dest line => do
  match args with
  | [op] =>
      let t := st.locals.length
      let st := { st with locals := st.locals ++ [.nat, .raw false .nat, .raw false dest.ty] }
      let tmpInt : UPlace := { root := .local t, projs := [], ty := .nat }
      let tmpR : UPlace := { root := .local (t + 1), projs := [], ty := .raw false .nat }
      let tmpPP : UPlace := { root := .local (t + 2), projs := [], ty := .raw false dest.ty }
      let st := pushOut st (.assign tmpInt (.use op) line)
      let st := pushOut st (.assign tmpR (.ref .rawConst false tmpInt) line)
      let st := pushOut st (.assign tmpPP (.use (.copy tmpR)) line)
      return pushOut st (.assign dest (.use (.copy { pointee tmpPP with ty := dest.ty })) line)
  | _ => .error s!"unsupported: without_provenance with {args.length} arguments (line {line})"

/-- `ptr.addr()`: the address, provenance stripped, nothing exposed. -/
def ptrAddr : Shim := fun st args dest line => do
  match args with
  | [.copy p] | [.move p] =>
      return pushOut st (.assign dest (.addr p) line)
  | _ => .error s!"unsupported: addr argument is not a place (line {line})"

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
    size at elaboration); provenance/tag is preserved. `inbounds`:
    `add`/`offset` must stay in the allocation (Miri's in-bounds
    arithmetic); `wrapping_add`/`wrapping_offset` need not. -/
def ptrOffset (inbounds : Bool) : Shim := fun st args dest line => do
  match args with
  | [.copy p, d] | [.move p, d] =>
      let delta ← match d with
        | .const n => pure (Int.ofNat n)
        | .constNeg n _ => pure (-(Int.ofNat n))
        | _ => throw s!"unsupported: runtime pointer offset (line {line})"
      return pushOut st (.assign dest (.ptrOffset p delta inbounds) line)
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
            | .tup [] | .structT [] _ =>
                -- RangeFull: the whole slice, so `0 .. len`
                let lenIdx := st.locals.length
                pure (UOperand.const 0, UOperand.copy
                  { root := .local lenIdx, projs := [], ty := .nat })
            | .tup [_, _] | .structT [_, _] _ =>
                pure (UOperand.copy (fld rp 0), UOperand.copy (fld rp 1))
            | _ => .error s!"unsupported: slice index by {reprStr rp.ty} (line {line})"
      -- the RangeFull length's local is reserved now (its index is in
      -- `hi`) and filled below
      let st ←
        match rangeOp with
        | .copy rp | .move rp =>
            match rp.ty with
            | .tup [] | .structT [] _ => pure { st with locals := st.locals ++ [UTy.nat] }
            | _ => pure st
        | _ => pure st
      -- move the retagged receiver into the destination first: when
      -- the receiver is an ARRAY reference (`&a[0..0]`) the copy is
      -- the tag-preserving reinterpret that gives the pointer the
      -- slice's element type, which is the type the narrowing scales
      -- its bounds by
      let st ← emitAssign st line dest (.use (.copy tmp))
      -- a RangeFull's length is read from the DESTINATION, i.e. in slice
      -- elements (2026-10-02; read from an array receiver it was the
      -- array's extent in ARRAYS — 1 — on both machines)
      let st :=
        match rangeOp with
        | .copy rp | .move rp =>
            match rp.ty, hi with
            | .tup [], .copy lenP | .structT [] _, .copy lenP =>
                pushOut st (.assign lenP (.sliceLen dest) line)
            | _, _ => st
        | _ => st
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

/-- Box::leak(b) -> &mut T. The std body is
    `let (ptr, alloc) = Box::into_raw_with_allocator(b); mem::forget(alloc);
    &mut *ptr`, and `into_raw_with_allocator` does `&raw mut **b`: under SB
    the fn-entry Unique retags of the Box, the raw retag, then a Unique
    reborrow of the raw pointer — `boxIntoRaw`'s three retags followed by
    `&mut *`. (Any further layer, like the caller's retag of the returned
    reference, derives from the shim's own fresh tags and cannot affect
    any other pointer.) -/
def boxLeak : Shim := fun st args dest line => do
  match args with
  | [.copy b] | [.move b] =>
      let inner ← match b.ty with
        | .boxT i => pure i
        | _ => throw s!"unsupported: Box::leak on a non-Box argument (line {line})"
      let r := st.locals.length
      let raw : UPlace := { root := .local r, projs := [], ty := .raw true inner }
      let st := { st with locals := st.locals ++ [.raw true inner] }
      let st ← boxIntoRaw st args raw line
      return pushOut st (.assign dest (.ref .mut false { pointee raw with ty := inner }) line)
  | _ => .error s!"unsupported: Box::leak argument is not a place (line {line})"

/-- `<*T>::cast`, `cast_mut`, `cast_const`: std's bodies are `self as _`,
    a raw-to-raw cast, which performs no retag (and a raw argument is not
    retagged at fn entry). A tag-preserving copy at the destination's
    pointer type (a `ptrCast` at elaboration when the pointee differs). -/
def ptrCast : Shim := fun st args dest line => do
  match args with
  | [.copy p] | [.move p] => emitAssign st line dest (.use (.copy p))
  | _ => .error s!"unsupported: pointer cast argument is not a place (line {line})"

/-- `ptr::write(dst, src)` / `<*mut T>::write(self, val)`: std checks
    alignment and non-null (no memory access) and then `write_via_move`:
    a plain store of `src` through `dst`, which neither reads nor drops
    the old value and does not retag the raw `dst`. -/
def ptrWrite : Shim := fun st args _dest line => do
  match args with
  | [.copy p, valOp] | [.move p, valOp] =>
      let inner ← match p.ty with
        | .raw _ i | .ref _ i => pure i
        | _ => throw s!"unsupported: ptr::write through a non-pointer (line {line})"
      emitAssign st line { pointee p with ty := inner } (.use valOp)
  | _ => .error s!"unsupported: ptr::write arguments (line {line})"

/-- `NonNull::from(r)`: std is `from_mut(r)` = `transmute(r as *mut T)`
    (or `from_ref`/`*const T` for a shared `r`; both impls render as
    `<NonNull as From>::from`, so the argument's type decides): the
    fn-entry retags of `r` in `from` and `from_mut`, then the raw retag of
    the cast — `boxIntoRaw`'s shape, from a reference. Protectors omitted
    as there: the only accesses during the calls are these reborrows. -/
def nonNullFrom : Shim := fun st args dest line => do
  match args with
  | [.copy r] | [.move r] =>
      let (mutbl, inner) ← match r.ty with
        | .ref m i => pure (m, i)
        | _ => throw s!"unsupported: NonNull::from of a non-reference (line {line})"
      let (kind, rawKind) : URefKind × URefKind :=
        if mutbl then (.mut, .rawMut) else (.shared, .rawConst)
      let t1 := st.locals.length
      let st := { st with locals := st.locals ++ [.ref mutbl inner, .ref mutbl inner] }
      let tmp1 : UPlace := { root := .local t1, projs := [], ty := .ref mutbl inner }
      let tmp2 : UPlace := { root := .local (t1 + 1), projs := [], ty := .ref mutbl inner }
      let st := pushOut st (.assign tmp1 (.ref kind false { pointee r with ty := inner }) line)
      let st := pushOut st (.assign tmp2 (.ref kind false { pointee tmp1 with ty := inner }) line)
      return pushOut st (.assign dest (.ref rawKind false { pointee tmp2 with ty := inner }) line)
  | _ => .error s!"unsupported: NonNull::from argument is not a place (line {line})"

/-- `<NonNull as Clone>::clone(&self)`: `*self`, a copy of the pointer. -/
def nonNullClone : Shim := fun st args dest line => do
  match args with
  | [.copy p] | [.move p] => emitAssign st line dest (.use (.copy { pointee p with ty := dest.ty }))
  | _ => .error s!"unsupported: NonNull::clone argument is not a place (line {line})"

/-- `NonNull::as_mut(&mut self)`: `&mut *self.as_ptr()`, a Unique reborrow
    through the stored pointer. -/
def nonNullAsMut : Shim := fun st args dest line => do
  match args with
  | [.copy p] | [.move p] =>
      let (nn, inner) ← match p.ty with
        | .ref _ (.raw m i) => pure (UTy.raw m i, i)
        | _ => throw s!"unsupported: NonNull::as_mut receiver (line {line})"
      return pushOut st (.assign dest
        (.ref .mut false { pointee { pointee p with ty := nn } with ty := inner }) line)
  | _ => .error s!"unsupported: NonNull::as_mut argument is not a place (line {line})"

/-- `ManuallyDrop::new(v)`: the value itself (ManuallyDrop<T> is `T` in the
    model, for a `T` without references; see `parseTy`). -/
def manuallyDropNew : Shim := fun st args dest line => do
  match args with
  | [v] => emitAssign st line dest (.use v)
  | _ => .error s!"unsupported: ManuallyDrop::new arity (line {line})"

/-- `<ManuallyDrop as Deref>::deref` / `DerefMut::deref_mut`: std is
    `self.value.as_ref()` / `as_mut()`, a shared / unique reborrow of the
    value. -/
def manuallyDropDeref (mutbl : Bool) : Shim := fun st args dest line => do
  match args with
  | [.copy p] | [.move p] =>
      let inner ← match p.ty with
        | .ref _ i => pure i
        | _ => throw s!"unsupported: ManuallyDrop deref receiver (line {line})"
      return pushOut st (.assign dest
        (.ref (if mutbl then .mut else .shared) false { pointee p with ty := inner }) line)
  | _ => .error s!"unsupported: ManuallyDrop deref argument is not a place (line {line})"

/-- mem::forget: no drop, no access; protectors end at fn return anyway -/
def memForget : Shim := fun st _args _dest _line => return st

/-- mem::drop: consumes the value and drops it — real for Boxes
    (`emitDropGlue`); for the other modelled types drop glue is nothing or
    elided flag maintenance (RefCell guards). -/
def memDrop : Shim := fun st args _dest line => do
  -- `fn drop<T>(_x: T) {}`: the argument is moved in and dropped when the
  -- call returns — for a Box, its drop glue (the caller then counts it
  -- moved out)
  match args with
  | [.move p] | [.copy p] => emitDropGlue st line p
  | _ => return st

/-- `ptr::drop_in_place(p)`: Miri retags the drop shim's raw argument as
    if it were `&mut T` at fn entry — a PROTECTED Unique retag of `*p`
    over the whole place, even for a `T` with no drop glue (so `*p` must
    be writeable through `p`) — and the protector lasts while the glue
    runs. The glue is `emitDropGlue`'s (Boxes only; a user `Drop` impl is
    not run). -/
def dropInPlace : Shim := fun st args _dest line => do
  match args with
  | [.copy p] | [.move p] =>
      let inner ← match p.ty with
        | .raw _ i | .ref _ i => pure i
        | _ => throw s!"unsupported: drop_in_place of a non-pointer (line {line})"
      let tmpIdx := st.locals.length
      let st := { st with locals := st.locals ++ [.ref true inner] }
      let tmp : UPlace := { root := .local tmpIdx, projs := [], ty := .ref true inner }
      let st := pushOut st (.pushProt line)
      let st ← emitAssign st line tmp (.ref .mut true { pointee p with ty := inner })
      let st ← emitDropGlue st line { pointee tmp with ty := inner }
      return pushOut st (.popProt line)
  | _ => .error s!"unsupported: drop_in_place argument is not a place (line {line})"

/-- `mem::swap(x, y)`: the fn-entry retags of the two `&mut T` arguments
    (protected for the call), then std's typed swap through them: read
    both, write both. -/
def memSwap : Shim := fun st args _dest line => do
  match args with
  | [a, b] =>
      let some pa := operandPlace? a
        | .error s!"unsupported: mem::swap argument is not a place (line {line})"
      let some pb := operandPlace? b
        | .error s!"unsupported: mem::swap argument is not a place (line {line})"
      let inner ← match pa.ty with
        | .ref true i => pure i
        | _ => throw s!"unsupported: mem::swap of a non-&mut (line {line})"
      let t := st.locals.length
      let st := { st with locals := st.locals ++ [.ref true inner, .ref true inner, inner] }
      let ta : UPlace := { root := .local t, projs := [], ty := .ref true inner }
      let tb : UPlace := { root := .local (t + 1), projs := [], ty := .ref true inner }
      let tmp : UPlace := { root := .local (t + 2), projs := [], ty := inner }
      let st := pushOut st (.pushProt line)
      let st ← emitAssign st line ta (.ref .mut true { pointee pa with ty := inner })
      let st ← emitAssign st line tb (.ref .mut true { pointee pb with ty := inner })
      let st ← emitAssign st line tmp (.use (.copy { pointee ta with ty := inner }))
      let st ← emitAssign st line { pointee ta with ty := inner } (.use (.copy { pointee tb with ty := inner }))
      let st ← emitAssign st line { pointee tb with ty := inner } (.use (.copy tmp))
      return pushOut st (.popProt line)
  | _ => .error s!"unsupported: mem::swap arity (line {line})"

/-- A value `Default::default` gives as all-zero words: integers, cells and
    tuples of them. -/
partial def zeroDefault : UTy → Bool
  | .nat | .int _ => true
  | .cell t => zeroDefault t
  | .tup tys | .structT tys _ => tys.all zeroDefault
  | _ => false

partial def emitZeros (line : Nat) (st : LowerSt) (p : UPlace) : UTy → Except String LowerSt
  | .nat => emitAssign st line { p with ty := .nat } (.use (.const 0))
  | .int t => emitAssign st line { p with ty := .int t } (.use (.const 0))
  | .cell t => emitZeros line st p t
  | .tup tys | .structT tys _ => tys.zipIdx.foldlM (fun st (t, i) => emitZeros line st { fld p i with ty := t } t) st
  | _ => pure st

/-- `Default::default()` for integers and cells of integers (`UnsafeCell`'s
    `default` is `UnsafeCell::new(T::default())`): zero in every word. -/
def defaultZero : Shim := fun st _args dest line => do
  if !zeroDefault dest.ty then
    throw s!"unsupported: Default::default for {reprStr dest.ty} (line {line})"
  emitZeros line st dest dest.ty

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

/-- `Layout::new::<T>()`: the size of `T` in BYTES (a Layout is modelled
    as its size, as in `layoutForValue`); `T` is the call's instantiation. -/
def layoutNew (tyArgs : List UTy) : Shim := fun st _args dest line => do
  match tyArgs with
  | [t] => emitAssign st line dest (.use (.const (sizeB t)))
  | _ => .error s!"unsupported: Layout::new instantiation {reprStr tyArgs} (line {line})"

/-- `mem::size_of::<T>()`: `T`'s size in BYTES, as Rust reports it (for a
    C-layout aggregate). -/
def sizeOf (tyArgs : List UTy) : Shim := fun st _args dest line => do
  match tyArgs with
  | [t] => emitAssign st line dest (.use (.const (sizeB t)))
  | _ => .error s!"unsupported: size_of instantiation {reprStr tyArgs} (line {line})"

/-! ## Vec

`Vec<T>` is the loader type `vecT T`: std's header `(ptr, cap, len)`
(`vecHeader`). Each shim performs what the std body at the pinned Miri's
toolchain does to memory and the borrow stacks; nested std calls retag
only from the outer call's fresh tag and are not observable, so only the
outermost fn-entry retag is emitted. Growth is decided here from the
length and capacity, which must be known statically. The buffer is a heap
allocation of its own, so a write into it cannot change a tracked
constant: it is emitted untracked (`bufWrite`), where a write through an
untracked pointer would otherwise forget every constant. -/

def vecPtrF (h : UPlace) (e : UTy) : UPlace := { fld h 0 with ty := .raw true e }
def vecCapF (h : UPlace) : UPlace := { fld h 1 with ty := .nat }
def vecLenF (h : UPlace) : UPlace := { fld h 2 with ty := .nat }

/-- `dst := rv` for a `dst` in a Vec's buffer: untracked (see above). -/
def bufWrite (st : LowerSt) (line : Nat) (dst : UPlace) (rv : URvalue) : Except String LowerSt :=
  match rv with
  | .use (.copy _) | .use (.move _) | .use (.const _) => return pushOut st (.assign dst rv line)
  | _ => throw s!"unsupported: Vec element value {reprStr rv} (line {line})"

/-- A fresh local of type `t`. -/
def freshLocal (st : LowerSt) (t : UTy) : LowerSt × UPlace :=
  ({ st with locals := st.locals ++ [t] }, { root := .local st.locals.length, projs := [], ty := t })

/-- The fn-entry retag of a `&Vec<T>` / `&mut Vec<T>` receiver: protected
    (the caller brackets the shim with `pushProt`/`popProt`). The header
    place through the fresh reference, and `T`. -/
def vecEntry (st : LowerSt) (line : Nat) (recv : UOperand) (what : String) :
    Except String (LowerSt × UPlace × UTy) := do
  let some r := operandPlace? recv
    | throw s!"unsupported: {what} receiver is not a place (line {line})"
  let (m, e) ← match r.ty with
    | .ref m (.vecT e) => pure (m, e)
    | t => throw s!"unsupported: {what} receiver {reprStr t} (line {line})"
  let (st, tmp) := freshLocal st (.ref m (.vecT e))
  let st ← emitAssign st line tmp
    (.ref (if m then .mut else .shared) true { pointee r with ty := .vecT e })
  return (st, { pointee tmp with ty := .vecT e }, e)

/-- `Vec::new()`: `RawVec::new` stores a dangling pointer without
    provenance at `T`'s alignment and capacity 0; nothing is allocated. -/
def vecNew : Shim := fun st args dest line => do
  let e ← match dest.ty, args with
    | .vecT e, [] => pure e
    | t, _ => throw s!"unsupported: Vec::new into {reprStr t} (line {line})"
  let st ← withoutProvenance st [.const (toBLayout e).alignB] (vecPtrF dest e) line
  let st ← emitAssign st line (vecCapF dest) (.use (.const 0))
  emitAssign st line (vecLenF dest) (.use (.const 0))

/-- `Vec::len(&self)`: reads `self.len`. -/
def vecLen : Shim := fun st args dest line => do
  match args with
  | [recv] =>
      let st := pushOut st (.pushProt line)
      let (st, h, _) ← vecEntry st line recv "Vec::len"
      let st ← emitAssign st line dest (.use (.copy (vecLenF h)))
      return pushOut st (.popProt line)
  | _ => .error s!"unsupported: Vec::len arity (line {line})"

/-- `Vec::as_ptr(&self)` / `as_mut_ptr(&mut self)`: `self.buf.ptr()`, the
    stored pointer as is — std avoids `deref` precisely so that no
    intermediate reference is made. -/
def vecAsPtr : Shim := fun st args dest line => do
  match args with
  | [recv] =>
      let st := pushOut st (.pushProt line)
      let (st, h, e) ← vecEntry st line recv "Vec::as_ptr"
      let st ← emitAssign st line dest (.use (.copy (vecPtrF h e)))
      return pushOut st (.popProt line)
  | _ => .error s!"unsupported: Vec::as_ptr arity (line {line})"

/-- `RawVecInner::grow_amortized` for one more element: the new capacity
    is `max(cap * 2, need, min_non_zero_cap)`; `finish_grow` allocates
    (capacity 0) or reallocates, which Miri does as allocate, copy the
    old bytes (a read through the stored pointer, a write through the new
    one), deallocate through the stored pointer. -/
def vecGrow (st : LowerSt) (line : Nat) (h : UPlace) (e : UTy) (cap need : Nat) :
    Except String LowerSt := do
  let sz := sizeB e
  let minCap := if sz == 1 then 8 else if sz ≤ 1024 then 4 else 1
  let newCap := max (max (cap * 2) need) minCap
  let (st, np) := freshLocal st (.raw true e)
  let st := emitAlloc st line np (some (.const newCap))
  let st ←
    if cap == 0 then pure st else do
      let arr := UTy.tup (List.replicate cap e)
      let (st, oldA) := freshLocal st (.raw true arr)
      let (st, newA) := freshLocal st (.raw true arr)
      let st ← emitAssign st line oldA (.use (.copy (vecPtrF h e)))
      let st ← emitAssign st line newA (.use (.copy np))
      let st ← bufWrite st line { pointee newA with ty := arr }
        (.use (.copy { pointee oldA with ty := arr }))
      pure (pushOut st (.dealloc (vecPtrF h e) line))
  let st ← emitAssign st line (vecPtrF h e) (.use (.copy np))
  emitAssign st line (vecCapF h) (.use (.const newCap))

/-- `Vec::push(&mut self, value)` (`push_mut`): grow when `len == cap`;
    `end = self.as_mut_ptr().add(len)` (in-bounds arithmetic);
    `ptr::write(end, value)`; `self.len = len + 1`; `&mut *end`. -/
def vecPush : Shim := fun st args _dest line => do
  match args with
  | [recv, valOp] =>
      let st := pushOut st (.pushProt line)
      let (st, h, e) ← vecEntry st line recv "Vec::push"
      if containsRefTy e || sizeB e == 0 then
        throw s!"unsupported: Vec::push of {reprStr e} (line {line})"
      let some len := constOfPlace st (vecLenF h)
        | throw s!"unsupported: Vec::push with a runtime length (line {line})"
      let some cap := constOfPlace st (vecCapF h)
        | throw s!"unsupported: Vec::push with a runtime capacity (line {line})"
      let st ← if len == cap then vecGrow st line h e cap.toNat (len.toNat + 1) else pure st
      let (st, endP) := freshLocal st (.raw true e)
      let st ← emitAssign st line endP (.ptrOffset (vecPtrF h e) len true)
      let st ← bufWrite st line { pointee endP with ty := e } (.use valOp)
      let st ← emitAssign st line (vecLenF h) (.use (.const (len.toNat + 1)))
      let (st, r) := freshLocal st (.ref true e)
      let st ← emitAssign st line r (.ref .mut false { pointee endP with ty := e })
      return pushOut st (.popProt line)
  | _ => .error s!"unsupported: Vec::push arity (line {line})"

/-- A slice pointer over `len` elements at `data` (a raw pointer, its tag
    kept): the pointer, narrowed to `0 .. len` (`subSlice`), then `kind`'s
    retag of the slice (`&*` / `&mut *`). -/
def sliceFromParts (st : LowerSt) (line : Nat) (data : UPlace) (e : UTy) (len : UOperand)
    (kind : URefKind) (dest : UPlace) : Except String LowerSt := do
  let (st, sp) := freshLocal st (.slice true true e)
  let st ← emitAssign st line sp (.use (.copy data))
  let st ← emitAssign st line sp (.subSlice sp (.const 0) len)
  return pushOut st (.assign dest (.refSlice kind false sp) line)

/-- The `n` bytes a `&[u8]`/`&str` at `s` points to, read through it in
    one access into a fresh local array. -/
def readBytes (st : LowerSt) (line : Nat) (s : UPlace) (n : Nat) :
    Except String (LowerSt × UPlace) := do
  let arr := UTy.tup (List.replicate n (.int { bits := 8 }))
  let (st, ap) := freshLocal st (.raw false arr)
  let st ← emitAssign st line ap (.use (.copy s))
  let (st, b) := freshLocal st arr
  let st ← emitAssign st line b (.use (.copy { pointee ap with ty := arr }))
  return (st, b)

/-- `<Vec as Deref>::deref(&self)` (`as_slice`):
    `&*aggregate_raw_ptr(self.as_ptr(), self.len)`; `DerefMut::deref_mut`
    (`as_mut_slice`) the same through `&mut self` with `&mut *`. -/
def vecDeref (mutbl : Bool) : Shim := fun st args dest line => do
  match args with
  | [recv] =>
      let st := pushOut st (.pushProt line)
      let (st, h, e) ← vecEntry st line recv "Vec::deref"
      let st ← sliceFromParts st line (vecPtrF h e) e (.copy (vecLenF h))
        (if mutbl then .mut else .shared) dest
      return pushOut st (.popProt line)
  | _ => .error s!"unsupported: Vec::deref arity (line {line})"

/-- `slice::from_raw_parts(_mut)(data, len)`: `&(mut) *slice_from_raw_parts(data, len)`
    (the precondition checks access no memory). -/
def sliceFromRawParts (mutbl : Bool) : Shim := fun st args dest line => do
  match args with
  | [dataOp, lenOp] =>
      let some data := operandPlace? dataOp
        | throw s!"unsupported: from_raw_parts data is not a place (line {line})"
      let e ← match data.ty with
        | .raw _ e => pure e
        | t => throw s!"unsupported: from_raw_parts of {reprStr t} (line {line})"
      sliceFromParts st line data e lenOp (if mutbl then .mut else .shared) dest
  | _ => .error s!"unsupported: from_raw_parts arity (line {line})"

/-- `<[T]>::get(&self, i) -> Option<&T>`, at a static index: the receiver's
    fn-entry retag, then `Some(&(*self)[i])`. Only the in-bounds case is
    modelled: an index past the end (std: `None`) fails the narrowing. -/
def sliceGet : Shim := fun st args dest line => do
  match args with
  | [sOp, idxOp] =>
      let some s := operandPlace? sOp
        | throw s!"unsupported: slice get receiver is not a place (line {line})"
      let e ← match s.ty with
        | .slice false false e => pure e
        | t => throw s!"unsupported: slice get on {reprStr t} (line {line})"
      let some i := constOf st idxOp
        | throw s!"unsupported: slice get at a runtime index (line {line})"
      let st := pushOut st (.pushProt line)
      let (st, tmp) := freshLocal st s.ty
      let st := pushOut st (.assign tmp (.refSlice .shared true s) line)
      let (st, sp) := freshLocal st (.slice true false e)
      let st ← emitAssign st line sp (.use (.copy tmp))
      let st ← emitAssign st line sp (.subSlice sp (.const i.toNat) (.const (i.toNat + 1)))
      let (st, r1) := freshLocal st (.slice false false e)
      let st := pushOut st (.assign r1 (.refSlice .shared false sp) line)
      let (st, r) := freshLocal st (.ref false e)
      let st ← emitAssign st line r (.use (.copy r1))
      let st ← emitAssign st line dest (.aggregate (some 1) [.copy r])
      return pushOut st (.popProt line)
  | _ => .error s!"unsupported: slice get arity (line {line})"

/-- `Box::new_uninit()`: one uninitialized pointee. -/
def boxNewUninit : Shim := fun st args dest line => do
  match args with
  | [] => return emitAlloc st line dest none
  | _ => .error s!"unsupported: Box::new_uninit arity (line {line})"

/-- `vec![a, …]`'s `box_assume_init_into_vec_unsafe(b)`:
    `(b.assume_init() as Box<[T]>).into_vec()`, which ends in
    `Box::into_raw_with_allocator` (`&raw mut **b`) and
    `Vec::from_raw_parts_in(ptr, N, N)`: `boxIntoRaw`'s retags, the
    capacity and length `N`. -/
def boxIntoVec : Shim := fun st args dest line => do
  match args, dest.ty with
  | [b], .vecT e =>
      let some bp := operandPlace? b
        | throw s!"unsupported: into_vec argument is not a place (line {line})"
      let n ← match bp.ty with
        | .boxT (.tup tys) => pure tys.length
        | t => throw s!"unsupported: into_vec of {reprStr t} (line {line})"
      let (st, raw) := freshLocal st (.raw true (.tup (List.replicate n e)))
      let st ← boxIntoRaw st args raw line
      let st ← emitAssign st line (vecPtrF dest e) (.use (.copy raw))
      let st ← emitAssign st line (vecCapF dest) (.use (.const n))
      emitAssign st line (vecLenF dest) (.use (.const n))
  | _, t => .error s!"unsupported: into_vec into {reprStr t} (line {line})"

/-- `String::from(&str)` (`str::to_owned` → `<[u8]>::to_vec`; also
    `<&str as Into<String>>::into`, which is `String::from`): the fn-entry
    retag of the `&str`, `Vec::with_capacity(len)` (exactly `len` bytes;
    nothing for an empty string), `copy_nonoverlapping` of the bytes (a
    read through the argument, a write into the new buffer), `set_len`. A
    `String` is its `Vec<u8>`. The `&str`'s length must be known
    statically (a literal's is: `lenField`): it is the capacity. -/
def stringFromStr : Shim := fun st args dest line => do
  match args, dest.ty with
  | [op], .vecT e => do
      let (st, s) ← match op with
        | .str bs => pure (materialiseStr st line bs)
        | .copy p | .move p => pure (st, p)
        | _ => throw s!"unsupported: String::from argument (line {line})"
      let some n := sliceLenOf st s
        | throw s!"unsupported: String::from of a &str of unknown length (line {line})"
      let st := pushOut st (.pushProt line)
      let (st, tmp) := freshLocal st s.ty
      let st := pushOut st (.assign tmp (.refSlice .shared true s) line)
      let st ←
        if n == 0 then vecNew st [] dest line else do
          let arr := UTy.tup (List.replicate n e)
          let (st, buf) := freshLocal st (.raw true arr)
          let st := emitAlloc st line buf none
          let (st, src) := freshLocal st (.raw false arr)
          let st ← emitAssign st line src (.use (.copy tmp))
          let st ← bufWrite st line { pointee buf with ty := arr }
            (.use (.copy { pointee src with ty := arr }))
          let st ← emitAssign st line (vecPtrF dest e) (.use (.copy buf))
          let st ← emitAssign st line (vecCapF dest) (.use (.const n))
          emitAssign st line (vecLenF dest) (.use (.const n))
      return pushOut st (.popProt line)
  | _, t => .error s!"unsupported: String::from into {reprStr t} (line {line})"

/-- `String::push_str(&mut self, string: &str)` (`vec.extend_from_slice` →
    `append_elements`): the two fn-entry retags; `reserve(n)`, which grows
    as `push` does (`grow_amortized(len, n)`) when `cap - len < n`;
    `copy_nonoverlapping` of the `n` bytes to `as_mut_ptr().add(len)` (a
    read through the argument, a write into the buffer); `len += n`. -/
def stringPushStr : Shim := fun st args _dest line => do
  match args with
  | [recv, sOp] =>
      let some sp := operandPlace? sOp
        | throw s!"unsupported: push_str argument is not a place (line {line})"
      let st := pushOut st (.pushProt line)
      let (st, h, e) ← vecEntry st line recv "String::push_str"
      let (st, s) := freshLocal st sp.ty
      let st := pushOut (trackAssign st s (.refSlice .shared true sp)) (.assign s (.refSlice .shared true sp) line)
      let some n := sliceLenOf st s
        | throw s!"unsupported: push_str of a &str of unknown length (line {line})"
      let some len := constOfPlace st (vecLenF h)
        | throw s!"unsupported: push_str with a runtime length (line {line})"
      let some cap := constOfPlace st (vecCapF h)
        | throw s!"unsupported: push_str with a runtime capacity (line {line})"
      let st ← if cap.toNat - len.toNat < n then vecGrow st line h e cap.toNat (len.toNat + n) else pure st
      let st ←
        if n == 0 then pure st else do
          let arr := UTy.tup (List.replicate n e)
          let (st, endP) := freshLocal st (.raw true e)
          let st ← emitAssign st line endP (.ptrOffset (vecPtrF h e) len true)
          let (st, src) := freshLocal st (.raw false arr)
          let st ← emitAssign st line src (.use (.copy s))
          let (st, dst) := freshLocal st (.raw true arr)
          let st ← emitAssign st line dst (.use (.copy endP))
          bufWrite st line { pointee dst with ty := arr } (.use (.copy { pointee src with ty := arr }))
      let st ← emitAssign st line (vecLenF h) (.use (.const (len.toNat + n)))
      return pushOut st (.popProt line)
  | _ => .error s!"unsupported: push_str arity (line {line})"

/-- `<String as PartialEq<&str>>::eq(&self, other: &&str)`:
    `PartialEq::eq(&self[..], &other[..])` — the two fn-entry retags, the
    two slice reborrows, then `<[u8]>::eq`: unequal lengths are `false`
    with nothing read; equal ones compare every byte (both read). Both
    lengths must be known statically; the bytes are compared when the
    program runs. -/
def stringEqStr : Shim := fun st args dest line => do
  match args with
  | [lOp, rOp] =>
      let some lp := operandPlace? lOp
        | throw s!"unsupported: String == &str receiver is not a place (line {line})"
      let some rp := operandPlace? rOp
        | throw s!"unsupported: String == &str argument is not a place (line {line})"
      let u8 := UTy.int { bits := 8 }
      let strTy := UTy.slice false false u8
      let st := pushOut st (.pushProt line)
      let (st, l) := freshLocal st lp.ty
      let st ← emitAssign st line l (.ref .shared true { pointee lp with ty := .vecT u8 })
      let (st, r) := freshLocal st rp.ty
      let st ← emitAssign st line r (.ref .shared true { pointee rp with ty := strTy })
      let h := { pointee l with ty := .vecT u8 }
      let some lenL := constOfPlace st (vecLenF h)
        | throw s!"unsupported: String == &str with a runtime length (line {line})"
      let some lenR := sliceLenOf st { pointee r with ty := strTy }
        | throw s!"unsupported: String == &str of unknown length (line {line})"
      let (st, ls) := freshLocal st strTy
      let st ← sliceFromParts st line (vecPtrF h u8) u8 (.const lenL.toNat) .shared ls
      let (st, rs) := freshLocal st strTy
      let st := pushOut st (.assign rs (.refSlice .shared false { pointee r with ty := strTy }) line)
      let st ←
        if lenL.toNat != lenR then emitAssign st line dest (.use (.const 0)) else do
          let n := lenL.toNat
          let (st, lb) ← readBytes st line ls n
          let (st, rb) ← readBytes st line rs n
          let (st, acc) := freshLocal st u8
          let st ← emitAssign st line acc (.use (.const 1))
          let st ← (List.range n).foldlM (fun st i => do
            let (st, eqi) := freshLocal st u8
            let st ← emitAssign st line eqi (.binOp "Eq" { bits := 8 } (.copy { fld lb i with ty := u8 })
              (.copy { fld rb i with ty := u8 }))
            emitAssign st line acc (.binOp "BitAnd" { bits := 8 } (.copy acc) (.copy eqi))) st
          emitAssign st line dest (.use (.copy acc))
      return pushOut st (.popProt line)
  | _ => .error s!"unsupported: String == &str arity (line {line})"

/-! ## `format!`

`format!(…)` is `alloc::fmt::format(Arguments::new(&TEMPLATE, &[Argument;
M]))`, each `Argument` made by `Argument::new_debug`/`new_display` from a
`&T`. The model keeps what the formatting reads and writes:
- an `Argument` is the value's pointer and a word naming `(T, Debug?)`
  (`LowerSt.fmtArgTys`);
- an `Arguments` is a word naming the template, parsed when loading with
  each placeholder's argument resolved (`LowerSt.fmtSpecs`), and the
  pointer to the arguments;
- `format` performs the retags and reads Debug/Display perform on each
  argument and writes the output bytes into a fresh `String`.

Covered: placeholders without options (`{}`, `{:?}`) of integers,
`String`, `&str`, `Vec<integer>`, and references to them. The output's
SHAPE is chosen when loading and checked when the program runs
(`emitAssume`): a Debug-formatted string has no byte that needs escaping
(only printable ASCII other than `"` and `\`), and an integer whose value
the lowering does not know has one digit. A failed check is reported as a
failed assumption, never as a verdict. The output's allocation is exactly
its length (Miri: `estimated_capacity`, then growth — a private buffer,
so only its size differs). -/

/-- `x`'s index in `xs`, appending it when absent. -/
def regIdx {α} [BEq α] (xs : List α) (x : α) : List α × Nat :=
  match xs.findIdx? (· == x) with
  | some i => (xs, i)
  | none => (xs ++ [x], xs.length)

/-- `Argument::new_debug`/`new_display(x: &T)`: the fn-entry retag of `x`,
    then `NonNull::from_ref(x)` (a raw retag) and the formatter's word. -/
def fmtArgNew (debug : Bool) : Shim := fun st args dest line => do
  match args with
  | [xOp] =>
      let some x := operandPlace? xOp
        | throw s!"unsupported: format argument is not a place (line {line})"
      let ty ← match x.ty with
        | .ref false t => pure t
        | t => throw s!"unsupported: format argument of type {reprStr t} (line {line})"
      let st := pushOut st (.pushProt line)
      let (st, r) := freshLocal st x.ty
      let st ← emitAssign st line r (.ref .shared true { pointee x with ty })
      let (st, raw) := freshLocal st (.raw false ty)
      let st ← emitAssign st line raw (.ref .rawConst false { pointee r with ty })
      let st ← emitAssign st line { fld dest 0 with ty := .raw false (.tup []) } (.use (.copy raw))
      -- where it points, for `fmtFormat` (the field is private: only these
      -- shims write an `Argument`)
      let (tys, i) := regIdx st.fmtArgTys (ty, debug, resolveKey st 32 { pointee x with ty })
      let st := { st with fmtArgTys := tys }
      let st ← emitAssign st line { fld dest 1 with ty := .nat } (.use (.const i))
      return pushOut st (.popProt line)
  | _ => .error s!"unsupported: format argument arity (line {line})"

/-- A `format_args!` template (`core::fmt::Arguments`' encoding): literal
    pieces (a length byte below 0x80, or 0x80 and a 16-bit length) and
    placeholders (a byte 0b11xxxxxx; only a default placeholder, `0xC0`,
    is supported: it formats the next argument), up to the end byte 0.
    Placeholders are numbered in order. -/
partial def parseTemplate (line : Nat) (bs : List Nat) (next : Nat := 0) :
    Except String (List (Sum (List Nat) Nat)) :=
  match bs with
  | [] => .error s!"unsupported: unterminated format template (line {line})"
  | 0 :: _ => .ok []
  | b :: rest =>
      if b < 0x80 then do
        let tl ← parseTemplate line (rest.drop b) next
        return .inl (rest.take b) :: tl
      else if b == 0x80 then
        match rest with
        | lo :: hi :: rest' => do
            let n := lo + 256 * hi
            let tl ← parseTemplate line (rest'.drop n) next
            return .inl (rest'.take n) :: tl
        | _ => .error s!"unsupported: malformed format template (line {line})"
      else if b == 0xC0 then do
        let tl ← parseTemplate line rest (next + 1)
        return .inr next :: tl
      else .error s!"unsupported: format placeholder with options (byte {b}) (line {line})"

/-- `Arguments::new(template: &[u8; N], args: &[Argument; M])`: the two
    fn-entry retags; the template (constant bytes) parsed now, each
    placeholder's argument type read from its formatter word. -/
def fmtArgumentsNew : Shim := fun st args dest line => do
  match args with
  | [tOp, aOp] =>
      let some tp := operandPlace? tOp
        | throw s!"unsupported: format template is not a place (line {line})"
      let some ap := operandPlace? aOp
        | throw s!"unsupported: format arguments are not a place (line {line})"
      let (tTy, n) ← match tp.ty with
        | .ref _ (.tup bs) => pure (UTy.tup bs, bs.length)
        | t => throw s!"unsupported: format template of type {reprStr t} (line {line})"
      let (aTy, m) ← match ap.ty with
        | .ref _ (.tup as) => pure (UTy.tup as, as.length)
        | t => throw s!"unsupported: format arguments of type {reprStr t} (line {line})"
      let st := pushOut st (.pushProt line)
      let (st, t) := freshLocal st tp.ty
      let st ← emitAssign st line t (.ref .shared true { pointee tp with ty := tTy })
      let (st, a) := freshLocal st ap.ty
      let st ← emitAssign st line a (.ref .shared true { pointee ap with ty := aTy })
      let bytes ← (List.range n).mapM fun i =>
        match constOfPlace st { fld (pointee t) i with ty := .int { bits := 8 } } with
        | some b => pure b.toNat
        | none => throw s!"unsupported: format template not known statically (line {line})"
      let parts ← parseTemplate line bytes
      let spec ← parts.mapM fun part =>
        match part with
        | .inl piece => pure (FmtPart.lit piece)
        | .inr k => do
            if k ≥ m then throw s!"unsupported: format placeholder {k} without an argument (line {line})"
            match constOfPlace st { fld (fld (pointee a) k) 1 with ty := .nat } with
            | some i =>
                match st.fmtArgTys[i.toNat]? with
                | some (ty, debug, target) => pure (FmtPart.hole k ty debug target)
                | none => throw s!"unsupported: format argument {k} not made by new_debug/new_display (line {line})"
            | none => throw s!"unsupported: format argument {k}'s formatter not known statically (line {line})"
      let (specs, si) := regIdx st.fmtSpecs spec
      let st := { st with fmtSpecs := specs }
      let st ← emitAssign st line { fld dest 0 with ty := .nat } (.use (.const si))
      let st ← emitAssign st line { fld dest 1 with ty := .raw false (.tup []) } (.use (.copy a))
      return pushOut st (.popProt line)
  | _ => .error s!"unsupported: Arguments::new arity (line {line})"

/-- The decimal digits of the integer at `v` (an `int t` place), as output
    bytes: the value's own when the lowering knows it, otherwise one digit
    with the assumption `v < 10` (unsigned at `t`'s width: a negative
    signed value fails it too). -/
def fmtDigits (st : LowerSt) (line : Nat) (v : UPlace) (t : UIntTy) :
    Except String (LowerSt × List URvalue) := do
  match constOfPlace st v with
  | some k =>
      let i := t.toIntTy.toInt k.toNat
      let ds := (toString i.natAbs).toList.map fun c => URvalue.use (.const c.toNat)
      return (st, (if i < 0 then [URvalue.use (.const '-'.toNat)] else []) ++ ds)
  | none =>
      let (st, ok) := freshLocal st (.int { bits := 8 })
      let st ← emitAssign st line ok (.binOp "Lt" { t with signed := false } (.copy v) (.const 10))
      let st := emitAssume st line ok
      return (st, [.binOp "Add.Wrap" { bits := 8 } (.copy v) (.const '0'.toNat)])

/-- The `n` bytes of the string at `s` (a `&str`), as output bytes: quoted
    for Debug, with the assumption that none needs escaping. -/
def fmtStrBytes (st : LowerSt) (line : Nat) (s : UPlace) (n : Nat) (debug : Bool) :
    Except String (LowerSt × List URvalue) := do
  let (st, b) ← readBytes st line s n
  let u8 : UIntTy := { bits := 8 }
  let byteAt (i : Nat) : UPlace := { fld b i with ty := .int u8 }
  let st ←
    if !debug || n == 0 then pure st else do
      let (st, ok) := freshLocal st (.int u8)
      let st ← emitAssign st line ok (.use (.const 1))
      let st ← (List.range n).foldlM (fun st i => do
        let tests : List (String × Nat) := [("Ge", 0x20), ("Le", 0x7e), ("Ne", 0x22), ("Ne", 0x5c)]
        tests.foldlM (fun st (op, c) => do
          let (st, ti) := freshLocal st (.int u8)
          let st ← emitAssign st line ti (.binOp op u8 (.copy (byteAt i)) (.const c))
          emitAssign st line ok (.binOp "BitAnd" u8 (.copy ok) (.copy ti))) st) st
      pure (emitAssume st line ok)
  let body := (List.range n).map fun i => URvalue.use (.copy (byteAt i))
  let q := URvalue.use (.const '"'.toNat)
  return (st, if debug then q :: body ++ [q] else body)

/-- What formatting the value behind `r : &T` reads, retags and outputs
    (`<T as Debug>::fmt` / `Display::fmt`). -/
partial def fmtValue (st : LowerSt) (line : Nat) (ty : UTy) (r : UPlace) (debug : Bool) :
    Except String (LowerSt × List URvalue) := do
  let u8 := UTy.int { bits := 8 }
  match ty with
  | .ref _ x =>
      -- `<&X as Debug>::fmt(&self, f)` is `Debug::fmt(&**self, f)`
      let (st, r2) := freshLocal st (.ref false x)
      let st ← emitAssign st line r2 (.ref .shared false { pointee { pointee r with ty } with ty := x })
      fmtValue st line x r2 debug
  | .slice false _ (.int ⟨8, false⟩) =>
      -- `&str`: `Debug::fmt(&**self, f)`, a reborrow of the bytes
      let some n := sliceLenOf st { pointee r with ty }
        | throw s!"unsupported: format of a &str of unknown length (line {line})"
      let (st, s) := freshLocal st (.slice false false u8)
      let rv : URvalue := .refSlice .shared false { pointee r with ty }
      let st := pushOut (trackAssign st s rv) (.assign s rv line)
      fmtStrBytes st line s n debug
  | .vecT (.int ⟨8, false⟩) =>
      -- `String`: `Debug::fmt(self.as_str(), f)`
      let h := { pointee r with ty }
      let some n := constOfPlace st (vecLenF h)
        | throw s!"unsupported: format of a String with a runtime length (line {line})"
      let (st, s) := freshLocal st (.slice false false u8)
      let st ← sliceFromParts st line (vecPtrF h u8) u8 (.const n.toNat) .shared s
      fmtStrBytes st line s n.toNat debug
  | .vecT e@(.int t) | .vecT e@.nat =>
      if !debug then throw s!"unsupported: Display of a Vec (line {line})"
      -- `<Vec as Debug>`: `Debug::fmt(&**self, f)`, then `debug_list` over
      -- `iter()`: a `&T` per element
      let h := { pointee r with ty }
      let some n := constOfPlace st (vecLenF h)
        | throw s!"unsupported: format of a Vec with a runtime length (line {line})"
      let (st, s) := freshLocal st (.slice false false e)
      let st ← sliceFromParts st line (vecPtrF h e) e (.const n.toNat) .shared s
      let (st, outs) ← (List.range n.toNat).foldlM (fun (st, acc) i => do
        let (st, sp) := freshLocal st (.slice true false e)
        let st ← emitAssign st line sp (.use (.copy s))
        let st ← emitAssign st line sp (.subSlice sp (.const i) (.const (i + 1)))
        let (st, er) := freshLocal st (.slice false false e)
        let st := pushOut st (.assign er (.refSlice .shared false sp) line)
        let (st, eref) := freshLocal st (.ref false e)
        let st ← emitAssign st line eref (.use (.copy er))
        let (st, ds) ← fmtValue st line e eref true
        let sep := if i == 0 then [] else [URvalue.use (.const ','.toNat), .use (.const ' '.toNat)]
        pure (st, acc ++ sep ++ ds)) (st, [])
      return (st, [URvalue.use (.const '['.toNat)] ++ outs ++ [.use (.const ']'.toNat)])
  | .int t =>
      let (st, v) := freshLocal st ty
      let st ← emitAssign st line v (.use (.copy { pointee r with ty }))
      fmtDigits st line v t
  | .nat =>
      let (st, v) := freshLocal st ty
      let st ← emitAssign st line v (.use (.copy { pointee r with ty }))
      fmtDigits st line v {}
  | t => throw s!"unsupported: format of {reprStr t} (line {line})"

/-- `alloc::fmt::format(args)`: each placeholder's formatter call (its
    fn-entry retag of `&T`, then `fmtValue`), and the output `String`. -/
def fmtFormat : Shim := fun st args dest line => do
  match args, dest.ty with
  | [aOp], .vecT e => do
      let some ap := operandPlace? aOp
        | throw s!"unsupported: format arguments are not a place (line {line})"
      let some si := constOfPlace st { fld ap 0 with ty := .nat }
        | throw s!"unsupported: format arguments not made by Arguments::new (line {line})"
      let some spec := st.fmtSpecs[si.toNat]?
        | throw s!"unsupported: unknown format template (line {line})"
      let m := spec.foldl (fun m p => match p with | .hole k _ _ _ => max m (k + 1) | _ => m) 0
      let argTy := UTy.structT [.raw false (.tup []), .nat] none
      let (st, arr) := freshLocal st (.raw false (.tup (List.replicate m argTy)))
      let st ← emitAssign st line arr (.use (.copy { fld ap 1 with ty := .raw false (.tup []) }))
      let (st, outs) ← spec.foldlM (fun (st, acc) part => do
        match part with
        | .lit bs => pure (st, acc ++ bs.map fun b => URvalue.use (.const b))
        | .hole k ty debug target =>
            let vpIdx := st.locals.length
            let (st, vp) := freshLocal st (.raw false ty)
            let st ← emitAssign st line vp
              (.use (.copy { fld { fld { pointee arr with ty := .tup (List.replicate m argTy) } k with ty := argTy } 0
                with ty := .raw false (.tup []) }))
            -- the pointer `new_debug` stored points where its argument did
            let st := match target with
              | some (l, path) =>
                  { st with refOf := ((vpIdx, []),
                      { root := .local l, projs := path.map UProj.field, ty }) :: st.refOf }
              | none => st
            let st := pushOut st (.pushProt line)
            let (st, r) := freshLocal st (.ref false ty)
            let st ← emitAssign st line r (.ref .shared true { pointee vp with ty })
            let (st, bs) ← fmtValue st line ty r debug
            pure (pushOut st (.popProt line), acc ++ bs)) (st, [])
      let n := outs.length
      if n == 0 then return (← vecNew st [] dest line)
      let arrTy := UTy.tup (List.replicate n e)
      let (st, buf) := freshLocal st (.raw true arrTy)
      let st := emitAlloc st line buf none
      let st ← outs.zipIdx.foldlM (fun st (rv, i) =>
        let d : UPlace := { fld { pointee buf with ty := arrTy } i with ty := e }
        match rv with
        | .binOp .. => emitAssign st line d rv
        | _ => bufWrite st line d rv) st
      let st ← emitAssign st line (vecPtrF dest e) (.use (.copy buf))
      let st ← emitAssign st line (vecCapF dest) (.use (.const n))
      emitAssign st line (vecLenF dest) (.use (.const n))
  | _, t => .error s!"unsupported: format into {reprStr t} (line {line})"

/-- `core::hint::must_use(x)`: `x`. -/
def mustUse : Shim := fun st args dest line => do
  match args with
  | [x] => emitAssign st line dest (.use x)
  | _ => .error s!"unsupported: must_use arity (line {line})"

/-- `<iN as AddAssign>::add_assign(&mut self, other)`: the fn-entry retag,
    then `*self = *self + other`. Overflow (a panic under Miri's debug
    build) stops the model as UB. -/
def addAssign : Shim := fun st args _dest line => do
  match args with
  | [selfOp, other] =>
      let some sp := operandPlace? selfOp
        | throw s!"unsupported: add_assign receiver is not a place (line {line})"
      let t ← match sp.ty with
        | .ref true (.int t) => pure t
        | ty => throw s!"unsupported: add_assign on {reprStr ty} (line {line})"
      let st := pushOut st (.pushProt line)
      let (st, tmp) := freshLocal st sp.ty
      let st ← emitAssign st line tmp (.ref .mut true { pointee sp with ty := .int t })
      let st ← emitAssign st line { pointee tmp with ty := .int t }
        (.binOp "Add.UB" t (.copy { pointee tmp with ty := .int t }) other)
      return pushOut st (.popProt line)
  | _ => .error s!"unsupported: add_assign arity (line {line})"

/-- Shims that need the call's monomorphised type arguments (`UFun.tyArgs`),
    for bodyless generics whose meaning is the type itself. -/
def tyArgTable : List (List String × (List UTy → Shim)) :=
  [ (["core", "alloc", "layout", "Layout", "new"], layoutNew)
  , (["core", "mem", "size_of"], sizeOf)
  ]

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
  , (["core", "sync", "atomic", "Atomic", "new"], cellNew)
  , (["core", "cell", "Cell", "get"], cellGet)
  , (["core", "cell", "UnsafeCell", "get"], unsafeCellGet)
  , (["core", "ptr", "read"], ptrRead)
  , (["core", "ptr", "const_ptr", "*const T", "read"], ptrRead)
  , (["core", "ptr", "mut_ptr", "*mut T", "read"], ptrRead)
  , (["core", "intrinsics", "transmute"], transmute)
  , (["core", "mem", "transmute_copy"], transmuteCopy)
  , (["core", "ptr", "without_provenance"], withoutProvenance)
  , (["core", "ptr", "without_provenance_mut"], withoutProvenance)
  , (["core", "ptr", "const_ptr", "*const T", "addr"], ptrAddr)
  , (["core", "ptr", "mut_ptr", "*mut T", "addr"], ptrAddr)
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
  , (["core", "ptr", "mut_ptr", "*mut T", "add"], ptrOffset true)
  , (["core", "ptr", "const_ptr", "*const T", "add"], ptrOffset true)
  , (["core", "ptr", "mut_ptr", "*mut T", "offset"], ptrOffset true)
  , (["core", "ptr", "const_ptr", "*const T", "offset"], ptrOffset true)
  , (["core", "ptr", "mut_ptr", "*mut T", "wrapping_add"], ptrOffset false)
  , (["core", "ptr", "const_ptr", "*const T", "wrapping_add"], ptrOffset false)
  , (["core", "ptr", "mut_ptr", "*mut T", "wrapping_offset"], ptrOffset false)
  , (["core", "ptr", "const_ptr", "*const T", "wrapping_offset"], ptrOffset false)
  , (["core", "ptr", "mut_ptr", "*mut T", "cast"], ptrCast)
  , (["core", "ptr", "const_ptr", "*const T", "cast"], ptrCast)
  , (["core", "ptr", "const_ptr", "*const T", "cast_mut"], ptrCast)
  , (["core", "ptr", "mut_ptr", "*mut T", "cast_const"], ptrCast)
  , (["core", "ptr", "write"], ptrWrite)
  , (["core", "ptr", "mut_ptr", "*mut T", "write"], ptrWrite)
  , (["core", "cell", "UnsafeCell", "raw_get"], ptrCast)
  , (["core", "ptr", "non_null", "NonNull", "new_unchecked"], ptrCast)
  , (["core", "ptr", "non_null", "NonNull", "as_ptr"], ptrCast)
  , (["core", "ptr", "non_null", "NonNull", "cast"], ptrCast)
  , (["core", "ptr", "non_null", "<NonNull as From>", "from"], nonNullFrom)
  , (["core", "ptr", "non_null", "<NonNull as Clone>", "clone"], nonNullClone)
  , (["core", "ptr", "non_null", "NonNull", "as_mut"], nonNullAsMut)
  , (["core", "mem", "manually_drop", "ManuallyDrop", "new"], manuallyDropNew)
  , (["core", "mem", "manually_drop", "<ManuallyDrop as Deref>", "deref"], (manuallyDropDeref false))
  , (["core", "mem", "manually_drop", "<ManuallyDrop as DerefMut>", "deref_mut"], (manuallyDropDeref true))
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
  , (["alloc", "boxed", "Box", "leak"], boxLeak)
  , (["core", "mem", "forget"], memForget)
  , (["core", "mem", "drop"], memDrop)
  , (["core", "mem", "swap"], memSwap)
  , (["core", "cell", "<UnsafeCell as Default>", "default"], defaultZero)
  , (["core", "cell", "<Cell as Default>", "default"], defaultZero)
  , (["core", "default", "<usize as Default>", "default"], defaultZero)
  , (["core", "default", "<u8 as Default>", "default"], defaultZero)
  , (["core", "default", "<u32 as Default>", "default"], defaultZero)
  , (["core", "default", "<u64 as Default>", "default"], defaultZero)
  , (["core", "default", "<i32 as Default>", "default"], defaultZero)
  , (["core", "default", "<i64 as Default>", "default"], defaultZero)
  , (["core", "ptr", "drop_in_place"], dropInPlace)
  , (["core", "cell", "Cell", "get_mut"], cellGetMut)
  , (["core", "cell", "UnsafeCell", "get_mut"], cellGetMut)
  , (["core", "cell", "RefCell", "get_mut"], cellGetMut)
  , (["alloc", "vec", "Vec", "new"], vecNew)
  , (["alloc", "vec", "Vec", "len"], vecLen)
  , (["alloc", "string", "String", "len"], vecLen)
  , (["alloc", "string", "<String as Deref>", "deref"], vecDeref false)
  , (["core", "str", "str", "as_ptr"], (sliceAsPtr false))
  , (["alloc", "string", "<String as From>", "from"], stringFromStr)
  , (["core", "convert", "<&T as Into>", "into"], stringFromStr)
  , (["alloc", "string", "String", "push_str"], stringPushStr)
  , (["alloc", "string", "<String as PartialEq>", "eq"], stringEqStr)
  , (["core", "fmt", "rt", "Argument", "new_debug"], fmtArgNew true)
  , (["core", "fmt", "rt", "Argument", "new_display"], fmtArgNew false)
  , (["core", "fmt", "Arguments", "new"], fmtArgumentsNew)
  , (["alloc", "fmt", "format"], fmtFormat)
  , (["core", "hint", "must_use"], mustUse)
  , (["alloc", "vec", "Vec", "push"], vecPush)
  , (["alloc", "vec", "Vec", "as_ptr"], vecAsPtr)
  , (["alloc", "vec", "Vec", "as_mut_ptr"], vecAsPtr)
  , (["alloc", "vec", "<Vec as Deref>", "deref"], vecDeref false)
  , (["alloc", "vec", "<Vec as DerefMut>", "deref_mut"], vecDeref true)
  , (["core", "slice", "raw", "from_raw_parts"], sliceFromRawParts false)
  , (["core", "slice", "raw", "from_raw_parts_mut"], sliceFromRawParts true)
  , (["core", "slice", "[T]", "get"], sliceGet)
  , (["alloc", "boxed", "Box", "new_uninit"], boxNewUninit)
  , (["alloc", "boxed", "box_assume_init_into_vec_unsafe"], boxIntoVec)
  , (["core", "ops", "arith", "<i32 as AddAssign>", "add_assign"], addAssign)
  ]

end conformance.stdlite

namespace conformance

/-- The shim for a call to fun `funIdx`, if its path is modelled. -/
def shimCall (crate : UCrate) (funIdx : Nat) : Option stdlite.Shim := do
  let f ← crate.funs.find? (·.defId == funIdx)
  stdlite.table.lookup f.path <|> (stdlite.tyArgTable.lookup f.path).map (· f.tyArgs)

end conformance
