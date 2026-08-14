import obseq3.mirlite_semantics

/-!
Unit tests for the obseq3 SB model and mirlite semantics, following the
assert pattern of `src/interp/test_mirlight.lean`, extended with negative
(`expectErr`) checks. Aggregated into the `interp_tests`/`sb_conformance`
executables via `InterpTests.lean` / the conformance harness.
-/

namespace obseq3.Tests

open obseq3 obseq3.mirlite

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

/-! ## Program-level tests (mirlite semantics) -/

abbrev M := PermissionModel.stackedBorrows

def natL := obseq.LayoutTy.NatL
def ptrNat := obseq.LayoutTy.PtrL natL
def pairL := obseq.LayoutTy.TupL [natL, natL]

def run (Γ : Ctx) (prog : Prog Γ) : Result M Γ :=
  runN M (prog.length + 1) (State.initial M Γ) prog

/-- outdated-local shape: x = 7; p = &mut x; *p = 8; read x via owner;
    then *p again is UB. -/
def ΓA : Ctx := [natL, ptrNat, natL]

def xA : Place ΓA natL := .local ⟨⟨0, by decide⟩, rfl⟩
def pA : Place ΓA ptrNat := .local ⟨⟨1, by decide⟩, rfl⟩
def tA : Place ΓA natL := .local ⟨⟨2, by decide⟩, rfl⟩

def t6_deref_write_then_owner_read : IO Unit := do
  let prog : Prog ΓA := [
    .assign xA (.constInit 7),
    .assign pA (.ref .Mut false xA),
    .assign (.deref pA) (.constInit 8),
    .assign tA (.copy xA),          -- read via owner pops the &mut
    .assign (.deref pA) (.constInit 9)  -- UB
  ]
  expectErr (run ΓA prog) "t6 deref write after owner read" "does not exist"

def t7_deref_write_ok : IO Unit := do
  let prog : Prog ΓA := [
    .assign xA (.constInit 7),
    .assign pA (.ref .Mut false xA),
    .assign (.deref pA) (.constInit 8),
    .assign (.deref pA) (.constInit 9)
  ]
  let s ← expectOk (run ΓA prog) "t7 repeated deref writes"
  match resolvePlace? s xA with
  | some res =>
      assert (s.mem.find? res.addr == some (.word 9)) "t7 final value is 9"
  | none => throw (IO.userError "t7: x not allocated")

/-- Field of a tuple at offset > 0: allocation is per-cell, so field-1
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
    .assign pB (.ref .Mut false fld1B),
    .assign (.deref pB) (.constInit 5),
    .assign tB (.copy (.deref pB))
  ]
  let s ← expectOk (run ΓB prog) "t8 field-1 borrow"
  match resolvePlace? s tB with
  | some res => assert (s.mem.find? res.addr == some (.word 5)) "t8 read back 5"
  | none => throw (IO.userError "t8: t not allocated")

def t9_field_borrow_invalidated_by_direct_write : IO Unit := do
  let prog : Prog ΓB := [
    .assign fld0B (.constInit 1),
    .assign fld1B (.constInit 2),
    .assign pB (.ref .Mut false fld1B),
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
    .assign p0C (.ref .Mut false fld0C),
    .assign p1C (.ref .Mut false fld1C),
    .assign (.deref p0C) (.constInit 10),
    .assign (.deref p1C) (.constInit 20)
  ]
  let _ ← expectOk (run ΓC prog) "t10 disjoint field borrows"
  pure ()

def runAll : IO Unit := do
  t1_child_popped_by_parent_read
  t2_raw_const_is_read_only
  t3_raw_mut_writable_and_survives_read
  t4_per_cell_stacks
  t5_shared_popped_by_write
  t6_deref_write_then_owner_read
  t7_deref_write_ok
  t8_field_borrow_at_offset
  t9_field_borrow_invalidated_by_direct_write
  t10_disjoint_field_borrows
  t11_protected_item_blocks_pop
  t12_protected_shared_blocks_write
  IO.println "obseq3 tests passed (12/12)"

end obseq3.Tests
