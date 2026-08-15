import obseq3.compile
import obseq3.tests

/-!
Unit tests for the mirlite-v3 → OSEA-IR-v3 compiler:
- golden fragments: compiled code maps compared against hand-written
  instruction lists (const-init with fresh/mapped locals, ref with
  protector+mask carried into `Borrow`, deref destinations, field
  offsets with `Die` cleanup);
- differential execution: source (mirlite) and target (OSEA) must
  produce the same verdict — ok, or UB attributed to the same source
  statement — on positive AND negative programs.
-/

namespace obseq3.CompileTests

open obseq3 obseq3.mirlite obseq3.compile
open obseq3.oseair (Register Instr Rhs Val)
open obseq3.Tests (assert natL ptrNat pairL M)

/-! ## Golden fragments -/

def codeList (Γ : Ctx) (prog : Prog Γ) : Except CompilerError (List (Option Instr)) := do
  let tp ← compileProg prog
  return (List.range (emittedLabels prog)).map tp

def expectCode (Γ : Ctx) (prog : Prog Γ) (expected : List Instr) (label : String) : IO Unit := do
  match codeList Γ prog with
  | .error e => throw (IO.userError s!"{label}: compile error: {reprStr e}")
  | .ok actual =>
      let exp := expected.map some
      if actual == exp then pure ()
      else throw (IO.userError
        s!"{label}: code mismatch\n  expected {reprStr exp}\n  actual   {reprStr actual}")

def natTy := obseq.TyVal.NatTy
def pTy := obseq.TyVal.PTy

def Γ1 : Ctx := [natL]
def x1 : Place Γ1 natL := .local ⟨⟨0, by decide⟩, rfl⟩

/-- const into a fresh local: Alloc + CStore. -/
def g1_const_fresh_local : IO Unit :=
  expectCode Γ1 [.assign x1 (.constInit 5), .halt]
    [Instr.Assgn (Register.R 0) (Rhs.Alloc natTy),
     Instr.CStore natTy [Val.Dat 5] (Register.R 0),
     Instr.Halt]
    "g1 const to fresh local"

def Γ2 : Ctx := [natL, ptrNat]
def x2 : Place Γ2 natL := .local ⟨⟨0, by decide⟩, rfl⟩
def p2 : Place Γ2 ptrNat := .local ⟨⟨1, by decide⟩, rfl⟩

/-- `p = &mut x` with protector and freeze mask: both must land verbatim
    in the emitted `Borrow`; the borrow register is NOT died (it is the
    stored reference). -/
def g2_protected_masked_ref : IO Unit :=
  expectCode Γ2 [.assign x2 (.constInit 7), .assign p2 (.ref .Mut true [true] x2), .halt]
    [Instr.Assgn (Register.R 0) (Rhs.Alloc natTy),
     Instr.CStore natTy [Val.Dat 7] (Register.R 0),
     Instr.Assgn (Register.R 1) (Rhs.Alloc pTy),
     Instr.Assgn (Register.R 2) (Rhs.Borrow .Mut true [true] 1 (Register.R 0) 0),
     Instr.RStore pTy (Register.R 2) (Register.R 1),
     Instr.Halt]
    "g2 protected masked ref"

/-- `*p = 2`: the loaded pointer register is used as the store target and
    is NOT died (its tag was loaded, not minted — dying it would pop the
    source program's own reference). -/
def g3_deref_destination : IO Unit :=
  expectCode Γ2
    [.assign x2 (.constInit 1),
     .assign p2 (.ref .Mut false [] x2),
     .assign (.deref p2) (.constInit 2),
     .halt]
    [Instr.Assgn (Register.R 0) (Rhs.Alloc natTy),
     Instr.CStore natTy [Val.Dat 1] (Register.R 0),
     Instr.Assgn (Register.R 1) (Rhs.Alloc pTy),
     Instr.Assgn (Register.R 2) (Rhs.Borrow .Mut false [] 1 (Register.R 0) 0),
     Instr.RStore pTy (Register.R 2) (Register.R 1),
     Instr.Assgn (Register.R 3) (Rhs.Load pTy (Register.R 1)),
     Instr.CStore natTy [Val.Dat 2] (Register.R 3),
     Instr.Halt]
    "g3 deref destination"

def pairTy := obseq.TyVal.TupTy [natTy, natTy]

def ΓB : Ctx := [pairL, ptrNat, natL]
def tupB : Place ΓB pairL := .local ⟨⟨0, by decide⟩, rfl⟩
def fld0B : Place ΓB natL := .proj tupB (.field ⟨0, by decide⟩ .nil)
def fld1B : Place ΓB natL := .proj tupB (.field ⟨1, by decide⟩ .nil)
def pB : Place ΓB ptrNat := .local ⟨⟨1, by decide⟩, rfl⟩
def tB : Place ΓB natL := .local ⟨⟨2, by decide⟩, rfl⟩

/-- Field destinations: offset-0 writes go through the base register
    directly (projZero); offset-1 writes mint a Mut borrow and `Die` it
    after the store. The root local is auto-allocated on first (field)
    assignment, mirroring mirlite's `preparePlaceAssign`. -/
def g4_field_offsets_and_die : IO Unit :=
  expectCode ΓB [.assign fld0B (.constInit 1), .assign fld1B (.constInit 2), .halt]
    [Instr.Assgn (Register.R 0) (Rhs.Alloc pairTy),
     Instr.CStore natTy [Val.Dat 1] (Register.R 0),
     Instr.Assgn (Register.R 1) (Rhs.Borrow .Mut false [] 1 (Register.R 0) 1),
     Instr.CStore natTy [Val.Dat 2] (Register.R 1),
     Instr.Die (Register.R 1) 1,
     Instr.Halt]
    "g4 field offsets and die"

/-- Non-core statements are rejected with `unsupported`, not miscompiled. -/
def g5_unsupported_stmt : IO Unit := do
  match compileProg (Γ := Γ2) [.assign x2 (.exposeAddr p2), .halt] with
  | .error (.unsupported _) => pure ()
  | .error e => throw (IO.userError s!"g5: expected unsupported, got {reprStr e}")
  | .ok _ => throw (IO.userError "g5: expected unsupported, got ok")

/-- Protector frames compile to `PushProt`/`PopProt` around the
    protected borrow. -/
def g6_protector_frame : IO Unit :=
  expectCode Γ2
    [.assign x2 (.constInit 7),
     .pushProtectors,
     .assign p2 (.ref .Mut true [] x2),
     .popProtectors,
     .halt]
    [Instr.Assgn (Register.R 0) (Rhs.Alloc natTy),
     Instr.CStore natTy [Val.Dat 7] (Register.R 0),
     Instr.PushProt,
     Instr.Assgn (Register.R 1) (Rhs.Alloc pTy),
     Instr.Assgn (Register.R 2) (Rhs.Borrow .Mut true [] 1 (Register.R 0) 0),
     Instr.RStore pTy (Register.R 2) (Register.R 1),
     Instr.PopProt,
     Instr.Halt]
    "g6 protector frame"

/-- `uninit` (statics hoisting) compiles to a CStore of undef cells —
    same useMut event as mirlite's undef fill, no new instruction. -/
def g7_uninit_undef_store : IO Unit :=
  expectCode Γ1 [.assign x1 .uninit, .halt]
    [Instr.Assgn (Register.R 0) (Rhs.Alloc natTy),
     Instr.CStore natTy [Val.Undef] (Register.R 0),
     Instr.Halt]
    "g7 uninit undef store"

/-- Heap allocation: dst-root Alloc first (mirlite's prepare order), then
    `AllocN`, then the pointer RStore. -/
def g8_heap_alloc : IO Unit :=
  expectCode Γ2 [.alloc p2 (.const 1), .halt]
    [Instr.Assgn (Register.R 0) (Rhs.Alloc pTy),
     Instr.Assgn (Register.R 1) (Rhs.AllocN natTy 1),
     Instr.RStore pTy (Register.R 1) (Register.R 0),
     Instr.Halt]
    "g8 heap alloc"

/-- Deallocation: Load of the pointer cell (mirlite's read), then Dealloc. -/
def g9_dealloc : IO Unit :=
  expectCode Γ2 [.alloc p2 (.const 1), .dealloc p2, .halt]
    [Instr.Assgn (Register.R 0) (Rhs.Alloc pTy),
     Instr.Assgn (Register.R 1) (Rhs.AllocN natTy 1),
     Instr.RStore pTy (Register.R 1) (Register.R 0),
     Instr.Assgn (Register.R 2) (Rhs.Load pTy (Register.R 0)),
     Instr.Dealloc (Register.R 2),
     Instr.Halt]
    "g9 dealloc"

/-! ## Differential execution -/

inductive DiffOut
| ok
| ub (stmt : Nat)
| stuck
deriving BEq, Repr

def srcRun (Γ : Ctx) (prog : Prog Γ) : DiffOut :=
  go (prog.length + 2) (State.initial M Γ)
where
  go : Nat → State M Γ → DiffOut
    | 0, _ => .stuck
    | n + 1, st =>
        match prog[st.pc]? with
        | none => .ok
        | some .halt => .ok
        | some stmt =>
            match stepStmt M st stmt with
            | .ok st' => go n st'
            | .err _ => .ub st.pc

def tgtRun (Γ : Ctx) (prog : Prog Γ) : Except String DiffOut :=
  match compileProg prog with
  | .error e => .error s!"compile error: {reprStr e}"
  | .ok tp =>
      .ok (go tp (stmtLabelRanges prog) (emittedLabels prog + 2) (oseair.State.initial M))
where
  go (tp : oseair.Prog) (ranges : List (Nat × Nat)) :
      Nat → oseair.State M → DiffOut
    | 0, _ => .stuck
    | n + 1, st =>
        match tp st.pc with
        | none => .ok
        | some .Halt => .ok
        | some _ =>
            match oseair.step M st tp with
            | .Ok st' => go tp ranges n st'
            | .Err _ =>
                match ranges.findIdx? (fun r => r.1 ≤ st.pc && st.pc < r.2) with
                | some i => .ub i
                | none => .ub 999999

def expectDiff (Γ : Ctx) (prog : Prog Γ) (expected : DiffOut) (label : String) : IO Unit := do
  let src := srcRun Γ prog
  assert (src == expected) s!"{label}: source verdict {reprStr src}, expected {reprStr expected}"
  match tgtRun Γ prog with
  | .error e => throw (IO.userError s!"{label}: {e}")
  | .ok tgt =>
      assert (tgt == expected)
        s!"{label}: target verdict {reprStr tgt}, expected {reprStr expected} (source agrees)"

def ΓA : Ctx := [natL, ptrNat, natL]
def xA : Place ΓA natL := .local ⟨⟨0, by decide⟩, rfl⟩
def pA : Place ΓA ptrNat := .local ⟨⟨1, by decide⟩, rfl⟩
def tA : Place ΓA natL := .local ⟨⟨2, by decide⟩, rfl⟩

/-- Negative: owner read pops the `&mut`; the next deref write is UB at
    the SAME statement on both machines. -/
def d1_owner_read_pops_mut : IO Unit :=
  expectDiff ΓA
    [.assign xA (.constInit 7),
     .assign pA (.ref .Mut false [] xA),
     .assign (.deref pA) (.constInit 8),
     .assign tA (.copy xA),
     .assign (.deref pA) (.constInit 9)]
    (.ub 4) "d1 owner read pops mut"

/-- Positive: write and read back through a `&mut`. -/
def d2_deref_roundtrip : IO Unit :=
  expectDiff ΓA
    [.assign xA (.constInit 7),
     .assign pA (.ref .Mut false [] xA),
     .assign (.deref pA) (.constInit 8),
     .assign tA (.copy (.deref pA))]
    .ok "d2 deref roundtrip"

/-- Positive: field borrow at offset 1, written through and copied out. -/
def d3_field_borrow : IO Unit :=
  expectDiff ΓB
    [.assign fld0B (.constInit 1),
     .assign fld1B (.constInit 2),
     .assign pB (.ref .Mut false [] fld1B),
     .assign (.deref pB) (.constInit 5),
     .assign tB (.copy (.deref pB))]
    .ok "d3 field borrow"

/-- Negative: a direct owner write to the borrowed field pops the borrow;
    the later deref copy is UB at the same statement on both machines
    (the compiled write is Borrow-Mut + CStore + Die — the Die must not
    resurrect anything). -/
def d4_owner_field_write_pops : IO Unit :=
  expectDiff ΓB
    [.assign fld0B (.constInit 1),
     .assign fld1B (.constInit 2),
     .assign pB (.ref .Mut false [] fld1B),
     .assign fld1B (.constInit 9),
     .assign tB (.copy (.deref pB))]
    (.ub 4) "d4 owner field write pops"

def ΓC : Ctx := [pairL, ptrNat, ptrNat]
def tupC : Place ΓC pairL := .local ⟨⟨0, by decide⟩, rfl⟩
def fld0C : Place ΓC natL := .proj tupC (.field ⟨0, by decide⟩ .nil)
def fld1C : Place ΓC natL := .proj tupC (.field ⟨1, by decide⟩ .nil)
def p0C : Place ΓC ptrNat := .local ⟨⟨1, by decide⟩, rfl⟩
def p1C : Place ΓC ptrNat := .local ⟨⟨2, by decide⟩, rfl⟩

/-- Positive: disjoint field borrows stay independent (per-cell stacks)
    through compilation. -/
def d5_disjoint_field_borrows : IO Unit :=
  expectDiff ΓC
    [.assign fld0C (.constInit 1),
     .assign fld1C (.constInit 2),
     .assign p0C (.ref .Mut false [] fld0C),
     .assign p1C (.ref .Mut false [] fld1C),
     .assign (.deref p0C) (.constInit 10),
     .assign (.deref p1C) (.constInit 20)]
    .ok "d5 disjoint field borrows"

/-- Positive: whole-tuple copy through `Memcpy` (multi-cell read/write). -/
def ΓD : Ctx := [pairL, pairL]
def tupD : Place ΓD pairL := .local ⟨⟨0, by decide⟩, rfl⟩
def fld0D : Place ΓD natL := .proj tupD (.field ⟨0, by decide⟩ .nil)
def fld1D : Place ΓD natL := .proj tupD (.field ⟨1, by decide⟩ .nil)
def cpyD : Place ΓD pairL := .local ⟨⟨1, by decide⟩, rfl⟩

def d6_tuple_copy : IO Unit :=
  expectDiff ΓD
    [.assign fld0D (.constInit 3),
     .assign fld1D (.constInit 4),
     .assign cpyD (.copy tupD)]
    .ok "d6 tuple copy"

/-- Negative: a write through the owner while the `&mut` is protected is
    UB at the same statement on both machines. -/
def d7_protected_pop_is_ub : IO Unit :=
  expectDiff ΓA
    [.assign xA (.constInit 7),
     .pushProtectors,
     .assign pA (.ref .Mut true [] xA),
     .assign xA (.constInit 9)]
    (.ub 3) "d7 protected pop is ub"

/-- Positive: after `popProtectors` the protection ends; the owner write
    pops the (now unprotected) borrow without UB. -/
def d8_pop_after_frame_ok : IO Unit :=
  expectDiff ΓA
    [.assign xA (.constInit 7),
     .pushProtectors,
     .assign pA (.ref .Mut true [] xA),
     .assign (.deref pA) (.constInit 8),
     .popProtectors,
     .assign xA (.constInit 9)]
    .ok "d8 pop after frame ok"

/-- Positive: the statics-hoisting shape — materialize uninit, overwrite,
    read back; plus a whole-tuple uninit copied out with one field still
    undef (undef cells flow through Memcpy without a verdict). -/
def d9_uninit_materialize : IO Unit := do
  expectDiff ΓA
    [.assign xA .uninit,
     .assign xA (.constInit 5),
     .assign tA (.copy xA)]
    .ok "d9a uninit materialize scalar"
  expectDiff ΓD
    [.assign tupD .uninit,
     .assign fld0D (.constInit 1),
     .assign cpyD (.copy tupD)]
    .ok "d9b uninit tuple partial init copy"

/-- Positive: Box-like lifecycle — alloc, write through the deref, read
    back, dealloc. -/
def d10_heap_lifecycle : IO Unit :=
  expectDiff ΓA
    [.alloc pA (.const 1),
     .assign (.deref pA) (.constInit 5),
     .assign tA (.copy (.deref pA)),
     .dealloc pA]
    .ok "d10 heap lifecycle"

/-- Negative: use-after-free is UB at the same statement on both machines. -/
def d11_use_after_free : IO Unit :=
  expectDiff ΓA
    [.alloc pA (.const 1),
     .assign (.deref pA) (.constInit 5),
     .dealloc pA,
     .assign tA (.copy (.deref pA))]
    (.ub 3) "d11 use after free"

/-- Negative: double free is UB at the second dealloc. -/
def d12_double_free : IO Unit :=
  expectDiff ΓA
    [.alloc pA (.const 1),
     .dealloc pA,
     .dealloc pA]
    (.ub 2) "d12 double free"

/-- Positive: runtime allocation length read from a place (`AllocDyn`'s
    in-instruction SB read of the length cell). -/
def d13_dynamic_alloc_len : IO Unit :=
  expectDiff ΓA
    [.assign xA (.constInit 3),
     .alloc pA (.fromPlace xA),
     .assign (.deref pA) (.constInit 7),
     .dealloc pA]
    .ok "d13 dynamic alloc len"

def runAll : IO Unit := do
  g1_const_fresh_local
  g2_protected_masked_ref
  g3_deref_destination
  g4_field_offsets_and_die
  g5_unsupported_stmt
  g6_protector_frame
  g7_uninit_undef_store
  g8_heap_alloc
  g9_dealloc
  d1_owner_read_pops_mut
  d2_deref_roundtrip
  d3_field_borrow
  d4_owner_field_write_pops
  d5_disjoint_field_borrows
  d6_tuple_copy
  d7_protected_pop_is_ub
  d8_pop_after_frame_ok
  d9_uninit_materialize
  d10_heap_lifecycle
  d11_use_after_free
  d12_double_free
  d13_dynamic_alloc_len
  IO.println "obseq3 compiler tests passed (22/22)"

end obseq3.CompileTests
