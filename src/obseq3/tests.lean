import obseq3.bytemem
import obseq3.bytelayout
import obseq3.mirlite

/-!
Unit tests for the obseq3 SB model and mirlite semantics (on bytes, at
the uniform layout unless a test gives its own), following the
assert pattern of `src/interp/test_mirlight.lean`, extended with negative
(`expectErr`) checks. Aggregated into the `interp_tests`/`sb_conformance`
executables via `InterpTests.lean` / the conformance harness.
-/

namespace obseq3.Tests

open obseq3 obseq3.mirlite
open obseq3.mirlite (MemValue)

def assert (cond : Bool) (msg : String) : IO Unit :=
  if cond then pure () else throw (IO.userError s!"Assertion failed: {msg}")

/-- Assert an `Except` succeeded, returning the value. -/
def expectOkE (r : Except String α) (label : String) : IO α :=
  match r with
  | .ok a => pure a
  | .error e => throw (IO.userError s!"{label}: expected Ok, got Err: {e}")

/-- Assert an `Except` failed, optionally requiring a substring of the message. -/
def expectErrE (r : Except String α) (label : String) (substr : String := "") : IO Unit :=
  match r with
  | .ok _ => throw (IO.userError s!"{label}: expected Err, got Ok")
  | .error e =>
      if substr.isEmpty || (e.splitOn substr).length > 1 then pure ()
      else throw (IO.userError s!"{label}: error message ⟨{e}⟩ does not mention ⟨{substr}⟩")

/-- Assert a semantics `Result` succeeded, returning the state. -/
def expectOk (r : Result M Γ) (label : String) : IO (State M Γ) :=
  match r with
  | .ok s => pure s
  | .err e => throw (IO.userError s!"{label}: expected ok, got err: {e}")

/-- Assert a semantics `Result` failed. -/
def expectErr (r : Result M Γ) (label : String) (substr : String := "") : IO Unit :=
  match r with
  | .ok _ => throw (IO.userError s!"{label}: expected err, got ok")
  | .err e =>
      if substr.isEmpty || (e.splitOn substr).length > 1 then pure ()
      else throw (IO.userError s!"{label}: error ⟨{e}⟩ does not mention ⟨{substr}⟩")

/-! ## Direct SB-op tests -/

/-- Write through a `&mut` child works; a read through the parent pops the
    child; using the child afterwards is UB. -/
def t1_child_popped_by_parent_read : IO Unit := do
  let ap := AccessPerms.init
  let (ap, root) ← expectOkE (sb_own ap 100 1) "t1 own"
  let (ap, m) ← expectOkE (sb_ref ap 100 1 root .Mut) "t1 ref mut"
  let ap ← expectOkE (sb_write ap 100 1 m) "t1 write via child"
  let ap ← expectOkE (sb_read ap 100 1 root) "t1 read via root"
  expectErrE (sb_write ap 100 1 m) "t1 write via popped child" "does not exist"

/-- A const raw derived from a shared ref is readable but not writable. -/
def t2_raw_const_is_read_only : IO Unit := do
  let ap := AccessPerms.init
  let (ap, root) ← expectOkE (sb_own ap 100 1) "t2 own"
  let (ap, s) ← expectOkE (sb_ref ap 100 1 root .Shared) "t2 ref shared"
  let (ap, r) ← expectOkE (sb_ref ap 100 1 s (.Raw false)) "t2 raw const from shared"
  let ap ← expectOkE (sb_read ap 100 1 r) "t2 read via raw const"
  expectErrE (sb_write ap 100 1 r) "t2 write via raw const" "does not grant write"

/-- A mut raw grants writes and survives a parent read (SharedReadWrite-like).
    This is the v1/v2 divergence being fixed: v1 rejected all raw writes. -/
def t3_raw_mut_writable_and_survives_read : IO Unit := do
  let ap := AccessPerms.init
  let (ap, root) ← expectOkE (sb_own ap 100 1) "t3 own"
  let (ap, r) ← expectOkE (sb_ref ap 100 1 root (.Raw true)) "t3 raw mut from root"
  let ap ← expectOkE (sb_read ap 100 1 root) "t3 read via root"
  let ap ← expectOkE (sb_write ap 100 1 r) "t3 write via raw mut after root read"
  let _ := ap
  pure ()

/-- Per-cell stacks: a `&mut` to cell 1 only affects cell 1; a whole-range
    write through the root pops it; the error names the offending cell. -/
def t4_per_cell_stacks : IO Unit := do
  let ap := AccessPerms.init
  let (ap, root) ← expectOkE (sb_own ap 200 2) "t4 own 2 cells"
  let (ap, m) ← expectOkE (sb_ref ap 201 1 root .Mut) "t4 ref mut on cell 1"
  let ap ← expectOkE (sb_write ap 201 1 m) "t4 write cell 1 via child"
  let ap ← expectOkE (sb_write ap 200 2 root) "t4 write both cells via root"
  expectErrE (sb_read ap 201 1 m) "t4 read popped child" "does not exist"

/-- Shared refs survive reads but are popped by writes. -/
def t5_shared_popped_by_write : IO Unit := do
  let ap := AccessPerms.init
  let (ap, root) ← expectOkE (sb_own ap 300 1) "t5 own"
  let (ap, s) ← expectOkE (sb_ref ap 300 1 root .Shared) "t5 ref shared"
  let ap ← expectOkE (sb_read ap 300 1 root) "t5 root read keeps shared"
  let ap ← expectOkE (sb_read ap 300 1 s) "t5 shared still readable"
  let ap ← expectOkE (sb_write ap 300 1 root) "t5 root write"
  expectErrE (sb_read ap 300 1 s) "t5 shared popped by write" "does not exist"

/-- Protectors: popping a protected item via a parent access is UB;
    after the frame is popped, the same access is fine. -/
def t11_protected_item_blocks_pop : IO Unit := do
  let ap := AccessPerms.init
  let (ap, root) ← expectOkE (sb_own ap 400 1) "t11 own"
  let ap := sb_push_frame ap
  let (ap, _m) ← expectOkE (sb_ref ap 400 1 root .Mut true) "t11 protected ref mut"
  expectErrE (sb_read ap 400 1 root) "t11 read popping protected" "strongly protected"
  expectErrE (sb_write ap 400 1 root) "t11 write popping protected" "strongly protected"
  let ap ← expectOkE (sb_pop_frame ap) "t11 pop frame"
  let _ ← expectOkE (sb_read ap 400 1 root) "t11 read after frame pop"
  pure ()

/-- Protected shared items are popped only by writes — and that is UB
    while the frame is active. -/
def t12_protected_shared_blocks_write : IO Unit := do
  let ap := AccessPerms.init
  let (ap, root) ← expectOkE (sb_own ap 500 1) "t12 own"
  let ap := sb_push_frame ap
  let (ap, s) ← expectOkE (sb_ref ap 500 1 root .Shared true) "t12 protected ref shared"
  let ap ← expectOkE (sb_read ap 500 1 root) "t12 root read keeps protected shared"
  let ap ← expectOkE (sb_read ap 500 1 s) "t12 protected shared readable"
  expectErrE (sb_write ap 500 1 root) "t12 write popping protected shared" "strongly protected"
  let ap ← expectOkE (sb_pop_frame ap) "t12 pop frame"
  let _ ← expectOkE (sb_write ap 500 1 root) "t12 write after frame pop"
  pure ()

/-- UnsafeCell freeze mask: a shared retag with a masked (interior-
    mutable) cell yields a writable SRW item there that survives parent
    reads, while unmasked cells stay frozen; and popping a protected SRW
    is allowed (weak protection). -/
def t13_freeze_mask_and_weak_protection : IO Unit := do
  let ap := AccessPerms.init
  let (ap, root) ← expectOkE (sb_own ap 600 2) "t13 own 2 cells"
  -- shared retag over both cells: cell 0 frozen, cell 1 interior-mutable
  let (ap, s) ← expectOkE (sb_ref ap 600 2 root .Shared false [false, true]) "t13 masked shared"
  let ap ← expectOkE (sb_read ap 600 2 s) "t13 read whole range via shared"
  expectErrE (sb_write ap 600 1 s) "t13 write frozen cell" "does not grant write"
  let ap ← expectOkE (sb_write ap 601 1 s) "t13 write cell part (SRW)"
  -- weak protection: a protected masked (SRW) item may be popped
  let ap := sb_push_frame ap
  let (ap, _c) ← expectOkE (sb_ref ap 601 1 root .Shared true [true]) "t13 protected cell retag"
  let ap ← expectOkE (sb_write ap 601 1 root) "t13 root write pops protected SRW (weak)"
  let _ ← expectOkE (sb_pop_frame ap) "t13 pop frame"
  pure ()

/-! ## Program-level tests (mirlite semantics) -/

abbrev M := PermissionModel.stackedBorrows

abbrev natL := LayoutTy.usize
def ptrNat := LayoutTy.PtrL natL
def pairL := LayoutTy.TupL [natL, natL]

def run (Γ : Ctx) (prog : Prog Γ) : Result M Γ :=
  runN M (uniformEnv Γ) (prog.length + 1) (State.initial M Γ) prog


/-- Weak (Box) vs strong protectors, as Miri's `Stack::dealloc`: a Box
    passed to a function (`BoxMut`, protected) may be deallocated through
    its own tag or a tag derived from it; a protected `&mut` may not; and
    deallocating through a PARENT pops the Box item, which is UB even for
    a weak protector. Ordinary accesses popping the Box item stay UB. -/
def t19_weak_box_protector : IO Unit := do
  -- dealloc through the weakly protected Box tag itself
  let (ap, root) ← expectOkE (sb_own AccessPerms.init 700 1) "t19 own"
  let ap := sb_push_frame ap
  let (ap, b) ← expectOkE (sb_ref ap 700 1 root .BoxMut true) "t19 protected box retag"
  expectErrE (sb_read ap 700 1 root) "t19 read popping the box" "protected"
  let _ ← expectOkE (sb_dealloc ap 700 1 b) "t19 dealloc through the weak box"
  -- ... and through a raw pointer derived from it
  let (ap, r) ← expectOkE (sb_ref ap 700 1 b (.Raw true)) "t19 raw from box"
  let _ ← expectOkE (sb_dealloc ap 700 1 r) "t19 dealloc through a raw below-weak"
  -- through the PARENT: the box item is popped by the write — UB
  expectErrE (sb_dealloc ap 700 1 root) "t19 dealloc popping the weak box" "is protected"
  -- a protected &mut is STRONG: no dealloc through it
  let (ap, root2) ← expectOkE (sb_own AccessPerms.init 800 1) "t19 own 2"
  let ap := sb_push_frame ap
  let (ap, m) ← expectOkE (sb_ref ap 800 1 root2 .Mut true) "t19 protected ref mut"
  expectErrE (sb_dealloc ap 800 1 m) "t19 dealloc through strong" "strongly protected"
  let ap ← expectOkE (sb_pop_frame ap) "t19 pop frame"
  let _ ← expectOkE (sb_dealloc ap 800 1 m) "t19 dealloc after the frame"
  pure ()

/-- outdated-local shape: x = 7; p = &mut x; *p = 8; read x via owner;
    then *p again is UB. -/
def ΓA : Ctx := [natL, ptrNat, natL]

def xA : Place ΓA natL := .local ⟨⟨0, by decide⟩, rfl⟩
def pA : Place ΓA ptrNat := .local ⟨⟨1, by decide⟩, rfl⟩
def tA : Place ΓA natL := .local ⟨⟨2, by decide⟩, rfl⟩

def t6_deref_write_then_owner_read : IO Unit := do
  let prog : Prog ΓA := [
    .assign xA (.constInit 7),
    .assign pA (.ref .Mut false [] xA),
    .assign (.deref pA) (.constInit 8),
    .assign tA (.copy xA),          -- read via owner pops the &mut
    .assign (.deref pA) (.constInit 9)  -- UB
  ]
  expectErr (run ΓA prog) "t6 deref write after owner read" "does not exist"

def t7_deref_write_ok : IO Unit := do
  let prog : Prog ΓA := [
    .assign xA (.constInit 7),
    .assign pA (.ref .Mut false [] xA),
    .assign (.deref pA) (.constInit 8),
    .assign (.deref pA) (.constInit 9)
  ]
  let s ← expectOk (run ΓA prog) "t7 repeated deref writes"
  match resolvePlace? M (uniformEnv ΓA) s xA with
  | some res =>
      assert (readOne s.mem res.addr (.int 8) == .word 9) "t7 final value is 9"
  | none => throw (IO.userError "t7: x not allocated")

/-- Field of a tuple at offset > 0: per-byte stacks, so field-1
    borrows work (v1/v2 failed here with "address not found"). -/
def ΓB : Ctx := [pairL, ptrNat, natL]

def tupB : Place ΓB pairL := .local ⟨⟨0, by decide⟩, rfl⟩
def fld0B : Place ΓB natL := .proj tupB (.field ⟨0, by decide⟩ .nil)
def fld1B : Place ΓB natL := .proj tupB (.field ⟨1, by decide⟩ .nil)
def pB : Place ΓB ptrNat := .local ⟨⟨1, by decide⟩, rfl⟩
def tB : Place ΓB natL := .local ⟨⟨2, by decide⟩, rfl⟩

def t8_field_borrow_at_offset : IO Unit := do
  let prog : Prog ΓB := [
    .assign fld0B (.constInit 1),
    .assign fld1B (.constInit 2),
    .assign pB (.ref .Mut false [] fld1B),
    .assign (.deref pB) (.constInit 5),
    .assign tB (.copy (.deref pB))
  ]
  let s ← expectOk (run ΓB prog) "t8 field-1 borrow"
  match resolvePlace? M (uniformEnv ΓB) s tB with
  | some res => assert (readOne s.mem res.addr (.int 8) == .word 5) "t8 read back 5"
  | none => throw (IO.userError "t8: t not allocated")

def t9_field_borrow_invalidated_by_direct_write : IO Unit := do
  let prog : Prog ΓB := [
    .assign fld0B (.constInit 1),
    .assign fld1B (.constInit 2),
    .assign pB (.ref .Mut false [] fld1B),
    .assign fld1B (.constInit 9),   -- direct write via owner pops the borrow
    .assign tB (.copy (.deref pB))  -- UB
  ]
  expectErr (run ΓB prog) "t9 field borrow popped" "does not exist"

/-- Disjoint field borrows don't interfere (per-cell independence). -/
def ΓC : Ctx := [pairL, ptrNat, ptrNat]

def tupC : Place ΓC pairL := .local ⟨⟨0, by decide⟩, rfl⟩
def fld0C : Place ΓC natL := .proj tupC (.field ⟨0, by decide⟩ .nil)
def fld1C : Place ΓC natL := .proj tupC (.field ⟨1, by decide⟩ .nil)
def p0C : Place ΓC ptrNat := .local ⟨⟨1, by decide⟩, rfl⟩
def p1C : Place ΓC ptrNat := .local ⟨⟨2, by decide⟩, rfl⟩

def t10_disjoint_field_borrows : IO Unit := do
  let prog : Prog ΓC := [
    .assign fld0C (.constInit 1),
    .assign fld1C (.constInit 2),
    .assign p0C (.ref .Mut false [] fld0C),
    .assign p1C (.ref .Mut false [] fld1C),
    .assign (.deref p0C) (.constInit 10),
    .assign (.deref p1C) (.constInit 20)
  ]
  let _ ← expectOk (run ΓC prog) "t10 disjoint field borrows"
  pure ()

/-- Deref resolution is a real SB read (Miri-faithful): evaluating `*p`
    reads `p`'s cell, disabling a `&mut` reborrow of the pointer variable
    itself. Before the 2026-08-21 change mirlite resolved derefs
    access-free and this program was (wrongly) accepted. -/
def ΓE' : Ctx := [natL, ptrNat, LayoutTy.PtrL ptrNat, natL]
def xE' : Place ΓE' natL := .local ⟨⟨0, by decide⟩, rfl⟩
def pE' : Place ΓE' ptrNat := .local ⟨⟨1, by decide⟩, rfl⟩
def qE' : Place ΓE' (LayoutTy.PtrL ptrNat) := .local ⟨⟨2, by decide⟩, rfl⟩
def tE' : Place ΓE' natL := .local ⟨⟨3, by decide⟩, rfl⟩

def t14_deref_read_disables_sibling : IO Unit := do
  let prog : Prog ΓE' := [
    .assign xE' (.constInit 1),
    .assign pE' (.ref .Mut false [] xE'),
    .assign qE' (.ref .Mut false [] pE'),
    .assign (.deref pE') (.constInit 5),      -- resolving *p READS p: disables q
    .assign tE' (.copy (.deref (.deref qE')))  -- via q: UB
  ]
  expectErr (run ΓE' prog) "t14 deref read disables sibling" "does not exist"

/-- Dereferencing a pointer that has been offset out of its slice bounds
    is UB at the deref itself (the dereferenceable check, mirroring the
    compiled `Load`'s bounds check), even before any SB stack consultation
    of the pointee. -/
def t15_deref_oob_pointer : IO Unit := do
  let prog : Prog ΓE' := [
    .assign xE' (.constInit 1),
    .assign pE' (.ref .Mut false [] xE'),
    .assign qE' (.ref .Mut false [] pE'),
    .assign qE' (.ptrOffset qE' 7 false),
    .assign tE' (.copy (.deref (.deref qE')))
  ]
  expectErr (run ΓE' prog) "t15 deref oob pointer" "out-of-bounds"

/-! t16: the invariant-gap example, encoded as a STATE (journal
    2026-08-27-ref-proj-closed / the event-fix discussion). No program
    reaches a memory cell holding `ptrVal (0, 0, 1, 0, t)` at a `PtrL usize`
    use site — every mint site stores the allocation's size — but
    `mirlite.State` is just data, so the junk state is constructible
    here. Before 2026-08-28 mirlite's `.ref` accepted the reborrow
    `L := &mut *p` from this state (no bounds check) while the compiled
    `Rhs.Borrow` rejected it: the unprovable corner of the simulation.
    The event fix (Miri's retag-dereferenceable check) makes the source
    err too. The same VALUE with pointee `()` stays legal — the bound is
    typed, which is why it lives at the event and not in `MemValSim`. -/
def ΓJ : Ctx := [natL, ptrNat, ptrNat]
def xJ : Place ΓJ natL := .local ⟨⟨0, by decide⟩, rfl⟩
def pJ : Place ΓJ ptrNat := .local ⟨⟨1, by decide⟩, rfl⟩
def LJ : Place ΓJ ptrNat := .local ⟨⟨2, by decide⟩, rfl⟩

def t16_junk_sized_pointer_retag : IO Unit := do
  -- reach a legitimate state first: x bound at 0, p bound at 1 holding &mut x
  let s0 ← expectOk (run ΓJ [
    .assign xJ (.constInit 1),
    .assign pJ (.ref .Mut false [] xJ)]) "t16 setup"
  -- forge the junk: shrink the STORED pointer's size to 0 (unreachable by
  -- any program; every mint site stores the allocation's size)
  let some bp := s0.env ⟨1, by decide⟩ | throw (IO.userError "t16: p unbound")
  let .ptrVal b o e _ t := readOne s0.mem bp.addr .ptr
    | throw (IO.userError "t16: p should hold a pointer")
  let .ok bs := encodeAt .ptr (.ptrVal b o e 0 t)
    | throw (IO.userError "t16: junk pointer does not encode")
  let junk : State M ΓJ := { s0 with mem := s0.mem.write bp.addr bs }
  -- the reborrow through the junk-sized pointer must now be UB at the
  -- retag event (pre-fix it succeeded: sb_ref has the granting tag on
  -- cell 0 and never looked at the size)
  expectErr (stepStmt M (uniformEnv ΓJ) junk (.assign LJ (.ref .Mut false [] (.deref pJ))))
    "t16 junk-sized reborrow" "out-of-bounds range"


/-- The read-side twin of t16: the same forged junk-SIZED pointer
    (`ptrVal b o e 0 t` at a u64 pointee), but consumed by a COPY instead
    of a retag. The copy-range dereferenceability check (2026-08-28)
    must reject it — pre-check, the wide SB read succeeded cell-wise
    and the target Memcpy diverged. -/
def ΓK : Ctx := [natL, ptrNat, natL]
def xK : Place ΓK natL := .local ⟨⟨0, by decide⟩, rfl⟩
def pK : Place ΓK ptrNat := .local ⟨⟨1, by decide⟩, rfl⟩
def yK : Place ΓK natL := .local ⟨⟨2, by decide⟩, rfl⟩

def t17_junk_sized_pointer_copy : IO Unit := do
  let s0 ← expectOk (run ΓK [
    .assign xK (.constInit 1),
    .assign pK (.ref .Mut false [] xK),
    .assign yK (.constInit 0)]) "t17 setup"
  let some bp := s0.env ⟨1, by decide⟩ | throw (IO.userError "t17: p unbound")
  let .ptrVal b o e _ t := readOne s0.mem bp.addr .ptr
    | throw (IO.userError "t17: p should hold a pointer")
  let .ok bs := encodeAt .ptr (.ptrVal b o e 0 t)
    | throw (IO.userError "t17: junk pointer does not encode")
  let junk : State M ΓK := { s0 with mem := s0.mem.write bp.addr bs }
  expectErr (stepStmt M (uniformEnv ΓK) junk (.assign yK (.copy (.deref pK))))
    "t17 junk-sized copy" "out-of-bounds range"


/-- `binOp`: two copy reads then the word; `sub` WRAPS at the width (MIR
    `Sub`): `3 - 5` at `u64` is `2^64 - 2`, which is not below 5. -/
def t18_binop_words : IO Unit := do
  let s0 ← expectOk (run ΓK [
    .assign xK (.constInit 3),
    .assign yK (.constInit 5),
    .assign xK (.binOp (.sub .u64) xK yK),
    .assign yK (.binOp (.lt .u64) xK yK)]) "t18 binOp"
  let some bx := s0.env ⟨0, by decide⟩ | throw (IO.userError "t18: x unbound")
  let some byy := s0.env ⟨2, by decide⟩ | throw (IO.userError "t18: y unbound")
  match readOne s0.mem bx.addr (.int 8), readOne s0.mem byy.addr (.int 8) with
  | .word 18446744073709551614, .word 0 => pure ()
  | a, b => throw (IO.userError s!"t18: expected x = 2^64 - 2, y = 0, got {reprStr a} {reprStr b}")

/-! ## Byte-addressed memory (`bytemem.lean`, standalone layer) -/

section bytes
open obseq3.bytes

/-- A fresh pointer-sized allocation holding a pointer with provenance. -/
private def bytesSetup : IO (bytes.Mem × Nat × Pointer) := do
  let (target, m) := (({} : bytes.Mem)).allocate 4 4          -- an i32
  let (slot, m) := m.allocate ptrSize ptrSize           -- a *const i32 slot
  let p : Pointer := ⟨target, some { base := target, sizeB := 4, tag := 7 }⟩
  let some m := m.store slot .ptr (.ptr p)
    | throw (IO.userError "bytes setup: pointer store failed")
  pure (m, slot, p)

/-- Allocation is aligned and never at 0; a stored pointer reads back with
    its provenance. -/
def t20_bytes_alloc_and_pointer_roundtrip : IO Unit := do
  let (m, slot, p) ← bytesSetup
  assert (p.addr % 4 == 0 && p.addr != 0) s!"t20 i32 base {p.addr} aligned, non-null"
  assert (slot % 8 == 0) s!"t20 pointer slot {slot} 8-aligned"
  assert (m.load slot .ptr == some (SVal.ptr p)) "t20 pointer round trip keeps provenance"

/-- `ptr_int_transmute::ptr_partial_read`: one byte of a pointer read as a
    `u8` is the low address byte, without provenance. -/
def t21_bytes_partial_pointer_read : IO Unit := do
  let (m, slot, p) ← bytesSetup
  assert (m.load slot (.int 1) == some (SVal.int (p.addr % 256))) "t21 low address byte"
  assert (m.load slot (.int 8) == some (SVal.int p.addr)) "t21 whole pointer read as usize = address"

/-- `provenance::bytewise_custom_memcpy`: copying a pointer one RAW byte at
    a time (`MaybeUninit<u8>`) preserves its provenance. -/
def t22_bytes_bytewise_copy_keeps_provenance : IO Unit := do
  let (m, slot, p) ← bytesSetup
  let (dst, m) := m.allocate ptrSize ptrSize
  let m := (List.range ptrSize).foldl (fun m i => m.copyBytes (dst + i) (slot + i) 1) m
  assert (m.load dst .ptr == some (SVal.ptr p)) "t22 bytewise raw copy keeps provenance"

/-- Copying a pointer through INTEGERS strips provenance: the copy has the
    address and no provenance (`transmute_strip_provenance`). -/
def t23_bytes_int_copy_strips_provenance : IO Unit := do
  let (m, slot, p) ← bytesSetup
  let (dst, m) := m.allocate ptrSize ptrSize
  let some (SVal.int a) := m.load slot (.int ptrSize)
    | throw (IO.userError "t23 int read of a pointer failed")
  let some m := m.store dst (.int ptrSize) (.int a)
    | throw (IO.userError "t23 int store failed")
  assert (m.load dst .ptr == some (SVal.ptr ⟨p.addr, none⟩)) "t23 copy via usize has no provenance"

/-- Mixing the bytes of two pointers: the address is the byte mix, the
    provenance is gone (the bytes disagree); an uninit byte makes the read
    fail. -/
def t24_bytes_mixed_and_uninit : IO Unit := do
  let (m, slot, _) ← bytesSetup
  let (slot2, m) := m.allocate ptrSize ptrSize
  let some m := m.store slot2 .ptr (.ptr ⟨slot, some { base := slot, sizeB := 8, tag := 9 }⟩)
    | throw (IO.userError "t24 store failed")
  let m := m.copyBytes slot slot2 1                      -- one byte from the other pointer
  match m.load slot .ptr with
  | some (SVal.ptr q) => assert (q.prov == none) "t24 mixed bytes lose provenance"
  | _ => throw (IO.userError "t24 mixed pointer read failed")
  let (fresh, m) := m.allocate ptrSize ptrSize
  assert (m.load fresh .ptr == none) "t24 uninit pointer read fails"

/-- `repr(C)` layouts: `(u8, u32, u8)` puts the fields at 0, 4, 8 with
    size 12, align 4; `(i32, u8)` is 8 bytes (3 of tail padding). -/
def t25_bytes_reprC_layout : IO Unit := do
  let L := reprC [.int 1, .int 4, .int 1]
  assert (L.leaves.map (·.1) == [0, 4, 8]) s!"t25 offsets {L.leaves.map (·.1)}"
  assert (L.size == 12 && L.align == 4) s!"t25 size {L.size} align {L.align}"
  let L2 := reprC [.int 4, .int 1]
  assert (L2.size == 8) s!"t25 (i32, u8) size {L2.size}"

/-- The uniform layout of `(usize, *usize, (usize, usize))`: four 8-byte
    leaves at 0, 8, 16, 24. -/
def t26_bytes_uniform_layout : IO Unit := do
  let τ : LayoutTy := .TupL [.usize, .PtrL .usize, .TupL [.usize, .usize]]
  let L := ofLayoutTy τ
  assert (L.leaves.map (·.1) == [0, 8, 16, 24]) s!"t26 offsets {L.leaves.map (·.1)}"
  assert (L.leaves.length == 4) "t26 four leaves"
  assert (L.size == 32) s!"t26 size {L.size}"

/-- A whole `(u8, *const i32, u16)` value stored and loaded back; the
    padding bytes stay uninit. -/
def t27_bytes_tuple_roundtrip : IO Unit := do
  let L := reprC [.int 1, .ptr (.int 4), .int 2]
  let (base, m) := (({} : bytes.Mem)).allocate L.size L.align
  let p : Pointer := ⟨base, some { base := base, sizeB := L.size, tag := 3 }⟩
  let vs := [SVal.int 200, SVal.ptr p, SVal.int 65000]
  let some m := m.storeL base L vs
    | throw (IO.userError "t27 store failed")
  assert (m.loadL base L == some vs) "t27 tuple round trip"
  assert (m.read (base + 1) 7 == List.replicate 7 .uninit) "t27 padding after the u8 is uninit"

end bytes

/-! ## mirlite on bytes (`mirlite.lean`) -/

def ΓR : Ctx := [natL, ptrNat, LayoutTy.PtrL ptrNat, ptrNat, natL]
def xR : Place ΓR natL := .local ⟨⟨0, by decide⟩, rfl⟩
def pR : Place ΓR ptrNat := .local ⟨⟨1, by decide⟩, rfl⟩
def qR : Place ΓR (LayoutTy.PtrL ptrNat) := .local ⟨⟨2, by decide⟩, rfl⟩
def rR : Place ΓR ptrNat := .local ⟨⟨3, by decide⟩, rfl⟩
def yR : Place ΓR natL := .local ⟨⟨4, by decide⟩, rfl⟩

/-- Reading a pointer's bytes at integer type (`*(&raw const p as *const
    usize)`): on bytes the result is the ADDRESS, provenance stripped (Miri,
    MiniRust). `x` (the first local) sits at a nonzero, 8-aligned
    address. -/
def t29_bytes_pointer_read_as_word : IO Unit := do
  let prog : Prog ΓR := [
    .assign xR (.constInit 7),
    .assign pR (.ref .Mut false [] xR),
    .assign qR (.ref (.Raw false) false [] pR),
    .assign rR (.ptrCast qR),
    .assign yR (.copy (.deref rR))]
  let sB ← expectOk (run ΓR prog) "t29"
  let some bx := sB.env ⟨0, by decide⟩ | throw (IO.userError "t29: x unbound")
  let some byB := sB.env ⟨4, by decide⟩ | throw (IO.userError "t29: y unbound")
  match readOne sB.mem byB.addr (.int 8) with
  | .word a =>
      assert (a == bx.addr && a % 8 == 0 && a != 0) s!"t29 bytes: y = {a}, x at {bx.addr}"
  | v => throw (IO.userError s!"t29 bytes: y should be a word, got {reprStr v}")

def ΓN : Ctx := [natL, natL, ptrNat]
def xN : Place ΓN natL := .local ⟨⟨0, by decide⟩, rfl⟩
def yN : Place ΓN natL := .local ⟨⟨1, by decide⟩, rfl⟩
def pN : Place ΓN ptrNat := .local ⟨⟨2, by decide⟩, rfl⟩

/-- An int-to-pointer cast reads its integer at the integer's OWN width
    (2026-10-02 fix: it read 8 bytes whatever the width, running past a
    `u8` into the next local and the uninitialised bytes after it). -/
def t31_narrow_int_to_ptr : IO Unit := do
  let L : mirlite.LayEnv ΓN := fun i =>
    match i.val with
    | 2 => .ptr (.int 1)
    | _ => .int 1
  let prog : Prog ΓN := [
    .assign xN (.constInit 5),
    .assign yN (.constInit 7),
    .assign pN (.fromExposed xN)]
  match mirlite.runN M L (prog.length + 1) (mirlite.State.initial M ΓN) prog with
  | .ok _ => pure ()
  | .err e => throw (IO.userError s!"t31 narrow int-to-ptr: expected ok, got {e}")

/-- MIR integer arithmetic at a type (`evalBinOp`, `binOpUB`): wrapping at
    the width, two's complement, signed comparison and arithmetic shift,
    real overflow flags, and the UB cases. -/
def t30_typed_arithmetic : IO Unit := do
  let u8 : IntTy := ⟨8, false⟩
  let i8 : IntTy := ⟨8, true⟩
  let i32 : IntTy := ⟨32, true⟩
  assert (evalBinOp (.add u8) 250 10 == 4) "t30 u8 250 + 10 wraps to 4"
  assert (evalBinOp (.addOv u8) 250 10 == 1) "t30 u8 add overflow flag"
  assert (evalBinOp (.addOv u8) 250 5 == 0) "t30 u8 add no overflow"
  assert (evalBinOp (.sub u8) 3 5 == 254) "t30 u8 3 - 5 wraps to 254"
  assert (evalBinOp (.subOv i8) 3 5 == 0) "t30 i8 3 - 5 = -2 does not overflow"
  assert (evalBinOp (.sub i8) 3 5 == 254) "t30 i8 -2 is the pattern 254"
  assert (evalBinOp (.lt i8) 255 1 == 1) "t30 i8 -1 < 1"
  assert (evalBinOp (.lt u8) 255 1 == 0) "t30 u8 255 < 1 is false"
  assert (evalBinOp (.mulOv i32) 65536 65536 == 1) "t30 i32 2^16 * 2^16 overflows"
  assert (evalBinOp (.div i8) 249 2 == 253) "t30 i8 -7 / 2 = -3 (truncating)"
  assert (evalBinOp (.rem i8) 249 2 == 255) "t30 i8 -7 % 2 = -1"
  assert (evalBinOp (.shr i8) 240 2 == 252) "t30 i8 -16 >> 2 = -4 (arithmetic)"
  assert (evalBinOp (.shr u8) 240 2 == 60) "t30 u8 240 >> 2 = 60"
  assert (evalBinOp (.shl u8) 1 9 == 2) "t30 u8 shl amount masked: 1 << (9 % 8)"
  assert (evalBinOp (.bitAnd u8) 0x1F3 0x0F == 3) "t30 u8 bitand on the low byte"
  assert ((binOpUB (.addUB u8) 250 10).isSome) "t30 unchecked overflow is UB"
  assert ((binOpUB (.addUB u8) 250 5).isNone) "t30 unchecked in range is fine"
  assert ((binOpUB (.rem u8) 7 0).isSome) "t30 remainder by zero is UB"
  assert ((binOpUB (.div i8) 128 255).isSome) "t30 i8::MIN / -1 is UB"
  assert ((binOpUB (.shlUB u8) 1 8).isSome) "t30 unchecked shift by the width is UB"
  assert ((binOpUB (.add u8) 250 10).isNone) "t30 wrapping add is never UB"

def ΓX : Ctx := [natL, ptrNat, natL, ptrNat]
def xX : Place ΓX natL := .local ⟨⟨0, by decide⟩, rfl⟩
def pX : Place ΓX ptrNat := .local ⟨⟨1, by decide⟩, rfl⟩
def yX : Place ΓX natL := .local ⟨⟨2, by decide⟩, rfl⟩
def qX : Place ΓX ptrNat := .local ⟨⟨3, by decide⟩, rfl⟩

/-- `addr` (`ptr.addr()`, a pointer-to-integer `transmute`) reads the
    pointer's bytes as an integer: the address, provenance stripped,
    nothing exposed. A pointer rebuilt from it may not access `x`; the same
    program with `exposeAddr` may. -/
def t32_addr_strips_provenance : IO Unit := do
  let s ← expectOk (run ΓX [
    .assign xX (.constInit 7),
    .assign pX (.ref (.Raw true) false [] xX),
    .assign yX (.addr pX)]) "t32 addr"
  let some bx := s.env ⟨0, by decide⟩ | throw (IO.userError "t32: x unbound")
  let some byy := s.env ⟨2, by decide⟩ | throw (IO.userError "t32: y unbound")
  match readOne s.mem byy.addr (.int 8) with
  | .word a => assert (a == bx.addr) s!"t32: y = {a}, x at {bx.addr}"
  | v => throw (IO.userError s!"t32: y should be a word, got {reprStr v}")
  expectErr (run ΓX [
    .assign xX (.constInit 7),
    .assign pX (.ref (.Raw true) false [] xX),
    .assign yX (.addr pX),
    .assign qX (.fromExposed yX),
    .assign (.deref qX) (.constInit 9)]) "t32 rebuilt pointer writes" "exposed"
  let _ ← expectOk (run ΓX [
    .assign xX (.constInit 7),
    .assign pX (.ref (.Raw true) false [] xX),
    .assign yX (.exposeAddr pX),
    .assign qX (.fromExposed yX),
    .assign (.deref qX) (.constInit 9)]) "t32 exposed: the rebuilt pointer writes"

/-- In-bounds pointer arithmetic (`add`/`offset`; Miri: "in-bounds pointer
    arithmetic failed"): a nonzero move must stay within a live allocation,
    one past the end allowed. `wrapping_*` moves anywhere at or above the
    base; a zero move never fails. -/
def t33_inbounds_offset : IO Unit := do
  let xp : List (Stmt ΓX) := [
    .assign xX (.constInit 7),
    .assign pX (.ref (.Raw true) false [] xX)]
  let _ ← expectOk (run ΓX (xp ++ [.assign qX (.ptrOffset pX 1 true)])) "t33 one past the end"
  expectErr (run ΓX (xp ++ [.assign qX (.ptrOffset pX 2 true)])) "t33 past the end"
    "in-bounds pointer arithmetic"
  let _ ← expectOk (run ΓX (xp ++ [.assign qX (.ptrOffset pX 2 false)])) "t33 wrapping"
  let np : List (Stmt ΓX) := [
    .assign yX (.constInit 0),
    .assign qX (.fromExposed yX)]
  let _ ← expectOk (run ΓX (np ++ [.assign qX (.ptrOffset qX 0 true)])) "t33 no provenance, 0"
  expectErr (run ΓX (np ++ [.assign qX (.ptrOffset qX 1 true)])) "t33 no provenance"
    "in-bounds pointer arithmetic"
  expectErr (run ΓX [
    .assign pX (.alloc (.const 1)),
    .dealloc pX,
    .assign qX (.ptrOffset pX 1 true)]) "t33 freed" "in-bounds pointer arithmetic"

def allTests : List (IO Unit) := [
  t1_child_popped_by_parent_read,
  t2_raw_const_is_read_only,
  t3_raw_mut_writable_and_survives_read,
  t4_per_cell_stacks,
  t5_shared_popped_by_write,
  t6_deref_write_then_owner_read,
  t7_deref_write_ok,
  t8_field_borrow_at_offset,
  t9_field_borrow_invalidated_by_direct_write,
  t10_disjoint_field_borrows,
  t11_protected_item_blocks_pop,
  t12_protected_shared_blocks_write,
  t13_freeze_mask_and_weak_protection,
  t19_weak_box_protector,
  t14_deref_read_disables_sibling,
  t15_deref_oob_pointer,
  t16_junk_sized_pointer_retag,
  t17_junk_sized_pointer_copy,
  t18_binop_words,
  t20_bytes_alloc_and_pointer_roundtrip,
  t21_bytes_partial_pointer_read,
  t22_bytes_bytewise_copy_keeps_provenance,
  t23_bytes_int_copy_strips_provenance,
  t24_bytes_mixed_and_uninit,
  t25_bytes_reprC_layout,
  t26_bytes_uniform_layout,
  t27_bytes_tuple_roundtrip,
  t29_bytes_pointer_read_as_word,
  t30_typed_arithmetic,
  t31_narrow_int_to_ptr,
  t32_addr_strips_provenance,
  t33_inbounds_offset]

def runAll : IO Unit := do
  allTests.forM id
  IO.println s!"obseq3 tests passed ({allTests.length}/{allTests.length})"

end obseq3.Tests
