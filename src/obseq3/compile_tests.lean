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

/-- The compiler is total on the source surface: a program using every
    statement/rvalue family compiles. (Replaces the retired
    unsupported-witness test — no unsupported construct remains.) -/
def g5_compiler_total : IO Unit := do
  match compileProg (Γ := Γ2)
      [.assign x2 (.constInit 1),
       .pushProtectors,
       .assign p2 (.ref .Mut true [] x2),
       .popProtectors,
       .assignIf x2 1 (.deref p2) (.constInit 2),
       .assign p2 (.ptrCast p2),
       .assign p2 (.refSlice (.Raw true) false p2),
       .assign x2 (.exposeAddr p2),
       .assign p2 (.fromExposed x2),
       .assign p2 (.ptrOffset p2 0),
       .assign x2 .uninit,
       .dealloc p2,
       .halt] with
  | .ok _ => pure ()
  | .error e => throw (IO.userError s!"g5: total compiler rejected: {reprStr e}")

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

/-- `assignIf` compiles to an event-free `SkipIf` whose skip count is the
    measured length of the guarded block (Borrow + CStore + Die here). -/
def g11_assign_if_skip : IO Unit :=
  expectCode ΓB
    [.assign fld0B (.constInit 1),
     .assignIf fld0B 1 fld1B (.constInit 7),
     .halt]
    [Instr.Assgn (Register.R 0) (Rhs.Alloc pairTy),
     Instr.CStore natTy [Val.Dat 1] (Register.R 0),
     Instr.SkipIf (Register.R 0) 1 3,
     Instr.Assgn (Register.R 1) (Rhs.Borrow .Mut false [] 1 (Register.R 0) 1),
     Instr.CStore natTy [Val.Dat 7] (Register.R 1),
     Instr.Die (Register.R 1) 1,
     Instr.Halt]
    "g11 assignIf skip"

def ΓA' : Ctx := [natL, ptrNat, natL]
def xA' : Place ΓA' natL := .local ⟨⟨0, by decide⟩, rfl⟩
def pA' : Place ΓA' ptrNat := .local ⟨⟨1, by decide⟩, rfl⟩
def tA' : Place ΓA' natL := .local ⟨⟨2, by decide⟩, rfl⟩

/-- `expose_provenance`: an `ExposeAddr` of the pointer cell followed by
    an `RStore` of the numeric address. -/
def g10_expose_addr : IO Unit :=
  expectCode ΓA'
    [.assign xA' (.constInit 1),
     .assign pA' (.ref (.Raw true) false [] xA'),
     .assign tA' (.exposeAddr pA'),
     .halt]
    [Instr.Assgn (Register.R 0) (Rhs.Alloc natTy),
     Instr.CStore natTy [Val.Dat 1] (Register.R 0),
     Instr.Assgn (Register.R 1) (Rhs.Alloc pTy),
     Instr.Assgn (Register.R 2) (Rhs.Borrow (.Raw true) false [] 1 (Register.R 0) 0),
     Instr.RStore pTy (Register.R 2) (Register.R 1),
     Instr.Assgn (Register.R 3) (Rhs.Alloc natTy),
     Instr.Assgn (Register.R 4) (Rhs.ExposeAddr (Register.R 1)),
     Instr.RStore natTy (Register.R 4) (Register.R 3),
     Instr.Halt]
    "g10 expose addr"

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

def ΓE : Ctx := [natL, ptrNat, natL, ptrNat, natL]
def xE : Place ΓE natL := .local ⟨⟨0, by decide⟩, rfl⟩
def pE : Place ΓE ptrNat := .local ⟨⟨1, by decide⟩, rfl⟩
def aE : Place ΓE natL := .local ⟨⟨2, by decide⟩, rfl⟩
def qE : Place ΓE ptrNat := .local ⟨⟨3, by decide⟩, rfl⟩
def tE : Place ΓE natL := .local ⟨⟨4, by decide⟩, rfl⟩

/-- Positive: full exposed-provenance round trip — expose a raw's address,
    reconstruct a wildcard pointer, write through it, read back. -/
def d14_expose_roundtrip : IO Unit :=
  expectDiff ΓE
    [.assign xE (.constInit 1),
     .assign pE (.ref (.Raw true) false [] xE),
     .assign aE (.exposeAddr pE),
     .assign qE (.fromExposed aE),
     .assign (.deref qE) (.constInit 5),
     .assign tE (.copy xE)]
    .ok "d14 expose roundtrip"

/-- Negative: the exposed raw is popped by an owner write before the
    wildcard write; wildcard resolution finds no exposed granting item —
    UB at the same statement on both machines. -/
def d15_exposed_then_invalidated : IO Unit :=
  expectDiff ΓE
    [.assign xE (.constInit 1),
     .assign pE (.ref (.Raw true) false [] xE),
     .assign aE (.exposeAddr pE),
     .assign xE (.constInit 2),
     .assign qE (.fromExposed aE),
     .assign (.deref qE) (.constInit 5)]
    (.ub 5) "d15 exposed then invalidated"

/-- Positive: guard true — the guarded write happens on both machines. -/
def d16_assign_if_taken : IO Unit :=
  expectDiff ΓB
    [.assign fld0B (.constInit 1),
     .assignIf fld0B 1 fld1B (.constInit 7),
     .assign tB (.copy fld1B)]
    .ok "d16 assignIf taken"

/-- Positive: guard false — the skip must suppress the block's SB events,
    not just its store: if the guarded Borrow executed, it would pop the
    `&mut` and the final deref copy would be UB. -/
def d17_assign_if_skipped_suppresses_events : IO Unit :=
  expectDiff ΓB
    [.assign fld0B (.constInit 0),
     .assign fld1B (.constInit 2),
     .assign pB (.ref .Mut false [] fld1B),
     .assignIf fld0B 1 fld1B (.constInit 9),
     .assign tB (.copy (.deref pB))]
    .ok "d17 assignIf skipped suppresses events"

/-- Negative: guard true and the guarded assignment itself is UB (write
    through a popped borrow) — attributed to the assignIf statement on
    both machines. -/
def d18_assign_if_body_ub : IO Unit :=
  expectDiff ΓA'
    [.assign xA' (.constInit 1),
     .assign pA' (.ref .Mut false [] xA'),
     .assign xA' (.constInit 2),
     .assign tA' (.constInit 1),
     .assignIf tA' 1 (.deref pA') (.constInit 5)]
    (.ub 4) "d18 assignIf body ub"

def ptrPair := obseq.LayoutTy.PtrL pairL
def ΓF : Ctx := [pairL, ptrPair, ptrNat, natL]
def tupF : Place ΓF pairL := .local ⟨⟨0, by decide⟩, rfl⟩
def fld0F : Place ΓF natL := .proj tupF (.field ⟨0, by decide⟩ .nil)
def fld1F : Place ΓF natL := .proj tupF (.field ⟨1, by decide⟩ .nil)
def rF : Place ΓF ptrPair := .local ⟨⟨1, by decide⟩, rfl⟩
def qF : Place ΓF ptrNat := .local ⟨⟨2, by decide⟩, rfl⟩
def tF : Place ΓF natL := .local ⟨⟨3, by decide⟩, rfl⟩

/-- `ptrOffset` deltas are pre-scaled by the source pointee's blockSize:
    `.ptrOffset r 1` on a `*mut (u64,u64)` emits `PtrOffset _ 2`. -/
def g12_ptr_offset_prescaled : IO Unit :=
  expectCode ΓF
    [.assign fld0F (.constInit 1),
     .assign rF (.ref (.Raw true) false [] tupF),
     .assign qF (.ptrOffset rF 1),
     .halt]
    [Instr.Assgn (Register.R 0) (Rhs.Alloc pairTy),
     Instr.CStore natTy [Val.Dat 1] (Register.R 0),
     Instr.Assgn (Register.R 1) (Rhs.Alloc pTy),
     Instr.Assgn (Register.R 2) (Rhs.Borrow (.Raw true) false [] 2 (Register.R 0) 0),
     Instr.RStore pTy (Register.R 2) (Register.R 1),
     Instr.Assgn (Register.R 3) (Rhs.Alloc pTy),
     Instr.Assgn (Register.R 4) (Rhs.PtrOffset (Register.R 1) 2),
     Instr.RStore pTy (Register.R 4) (Register.R 3),
     Instr.Halt]
    "g12 ptrOffset prescaled"

/-- Positive: tag-preserving cast round trip — the cast copy keeps the
    raw's provenance, so the write through the casted pointer is fine. -/
def d19_ptr_cast_roundtrip : IO Unit :=
  expectDiff ΓE
    [.assign xE (.constInit 1),
     .assign pE (.ref (.Raw true) false [] xE),
     .assign qE (.ptrCast pE),
     .assign (.deref qE) (.constInit 5),
     .assign tE (.copy xE)]
    .ok "d19 ptrCast roundtrip"

/-- Positive: the `(&raw mut tup) as *mut u64` + `.add(1)` idiom — cast
    to the element type, offset one cell into the pair, write through
    the raw's whole-range provenance. -/
def d20_cast_then_offset_into_pair : IO Unit :=
  expectDiff ΓF
    [.assign fld0F (.constInit 1),
     .assign fld1F (.constInit 2),
     .assign rF (.ref (.Raw true) false [] tupF),
     .assign qF (.ptrCast rF),
     .assign qF (.ptrOffset qF 1),
     .assign (.deref qF) (.constInit 9),
     .assign tF (.copy fld1F)]
    .ok "d20 cast then offset into pair"

/-- Negative: offsetting before the allocation base is UB at the
    ptrOffset statement on both machines. -/
def d21_offset_before_base : IO Unit :=
  expectDiff ΓE
    [.assign xE (.constInit 1),
     .assign pE (.ref (.Raw true) false [] xE),
     .assign qE (.ptrOffset pE (-1))]
    (.ub 2) "d21 offset before base"

/-- `refSlice` emits a runtime-length `BorrowRest` carrying kind/prot. -/
def g13_ref_slice : IO Unit :=
  expectCode ΓF
    [.assign fld0F (.constInit 1),
     .assign rF (.ref (.Raw true) false [] tupF),
     .assign qF (.refSlice .Mut false rF),
     .halt]
    [Instr.Assgn (Register.R 0) (Rhs.Alloc pairTy),
     Instr.CStore natTy [Val.Dat 1] (Register.R 0),
     Instr.Assgn (Register.R 1) (Rhs.Alloc pTy),
     Instr.Assgn (Register.R 2) (Rhs.Borrow (.Raw true) false [] 2 (Register.R 0) 0),
     Instr.RStore pTy (Register.R 2) (Register.R 1),
     Instr.Assgn (Register.R 3) (Rhs.Alloc pTy),
     Instr.Assgn (Register.R 4) (Rhs.BorrowRest .Mut false (Register.R 1)),
     Instr.RStore pTy (Register.R 4) (Register.R 3),
     Instr.Halt]
    "g13 refSlice"

/-- Positive: a Mut slice retag over the runtime rest-of-allocation
    (2 cells), written through and read back via the owner. -/
def d22_ref_slice_write : IO Unit :=
  expectDiff ΓF
    [.assign fld0F (.constInit 1),
     .assign fld1F (.constInit 2),
     .assign rF (.ref (.Raw true) false [] tupF),
     .assign qF (.refSlice .Mut false rF),
     .assign (.deref qF) (.constInit 9),
     .assign tF (.copy fld0F)]
    .ok "d22 refSlice write"

/-- Negative: the slice retag's write access pops a shared ref sitting
    above the raw; using it afterwards is UB at the same statement on
    both machines (the fnentry_invalidation2 mechanism). -/
def d23_ref_slice_pops : IO Unit :=
  expectDiff ΓF
    [.assign fld0F (.constInit 1),
     .assign rF (.ref (.Raw true) false [] tupF),
     .assign qF (.ref .Shared false [] fld0F),
     .assign rF (.refSlice .Mut false rF),
     .assign tF (.copy (.deref qF))]
    (.ub 4) "d23 refSlice pops"

/-- Negative: the deref-read alignment witness. Resolving `*p` reads
    `p`'s cell on BOTH machines (source: `resolvePlaceAcc`; target:
    `Rhs.Load`), disabling the `&mut p` reborrow — using it afterwards is
    UB at the same statement. Before the mirlite deref-read change this
    program MISMATCHED (source ok, target UB): the risk-register item (a)
    divergence, where Miri sides with the target. -/
def ΓG : Ctx := [natL, ptrNat, obseq.LayoutTy.PtrL ptrNat, natL]
def xG : Place ΓG natL := .local ⟨⟨0, by decide⟩, rfl⟩
def pG : Place ΓG ptrNat := .local ⟨⟨1, by decide⟩, rfl⟩
def qG : Place ΓG (obseq.LayoutTy.PtrL ptrNat) := .local ⟨⟨2, by decide⟩, rfl⟩
def tG : Place ΓG natL := .local ⟨⟨3, by decide⟩, rfl⟩

def d24_deref_read_alignment : IO Unit :=
  expectDiff ΓG
    [.assign xG (.constInit 1),
     .assign pG (.ref .Mut false [] xG),
     .assign qG (.ref .Mut false [] pG),
     .assign (.deref pG) (.constInit 5),
     .assign tG (.copy (.deref (.deref qG)))]
    (.ub 4) "d24 deref read alignment"

/-- The OOB-deref alignment: both machines flag dereferencing an
    out-of-slice pointer at the same statement (mirlite's dereferenceable
    check vs the compiled `Load`'s bounds check). -/
def d25_deref_oob_alignment : IO Unit :=
  expectDiff ΓG
    [.assign xG (.constInit 1),
     .assign pG (.ref .Mut false [] xG),
     .assign qG (.ref .Mut false [] pG),
     .assign qG (.ptrOffset qG 7),
     .assign tG (.copy (.deref (.deref qG)))]
    (.ub 4) "d25 deref oob alignment"

/-! d26: the nested-projection witness (`local/nested_proj_borrow`), as an
    in-repo differential test. Writing `s.1.1` must not invalidate a live
    `&mut s.1.0` — disjoint field borrows, legal Rust. Before the
    reassociating lowering (2026-08-27) the compiler retagged the whole
    intermediate place `s.1` and the target reported spurious UB here. -/
def ΓH : Ctx :=
  [obseq.LayoutTy.TupL [natL, obseq.LayoutTy.TupL [natL, natL]], ptrNat, natL]
def sH : Place ΓH (obseq.LayoutTy.TupL [natL, obseq.LayoutTy.TupL [natL, natL]]) :=
  .local ⟨⟨0, by decide⟩, rfl⟩
def qH : Place ΓH ptrNat := .local ⟨⟨1, by decide⟩, rfl⟩
def tH : Place ΓH natL := .local ⟨⟨2, by decide⟩, rfl⟩
/-- `s.1.0` as nested projections (the elaborator's shape). -/
def s10H : Place ΓH natL :=
  .proj (.proj sH (.field ⟨1, by decide⟩ .nil)) (.field ⟨0, by decide⟩ .nil)
/-- `s.1.1` as nested projections. -/
def s11H : Place ΓH natL :=
  .proj (.proj sH (.field ⟨1, by decide⟩ .nil)) (.field ⟨1, by decide⟩ .nil)

def d26_nested_proj_sibling : IO Unit :=
  expectDiff ΓH
    [.assign (.proj sH (.field ⟨0, by decide⟩ .nil)) (.constInit 1),
     .assign s10H (.constInit 2),
     .assign s11H (.constInit 3),
     .assign qH (.ref .Mut false [] s10H),
     .assign s11H (.constInit 9),
     .assign (.deref qH) (.constInit 8),
     .assign tH (.copy s11H)]
    .ok "d26 nested proj write keeps sibling borrow alive"

/-! d27–d29: split borrows (`local/split_field_borrows`) and its cell-wise
    boundary. d27: all three fields of a 3-tuple mutably borrowed AT ONCE,
    writes interleaved — Rust's split-borrow idiom, OK because retags are
    per cell (disjoint ranges, disjoint stacks). d28/d29: a parent write
    through the root is ALSO cell-wise — it kills only the child covering
    the written cells (d29: using that child is UB) and leaves siblings
    alive (d28). d28/d29 are not expressible in safe Rust (borrowck
    rejects using the borrow across the parent write), so they live only
    here. -/
def ΓY : Ctx :=
  [obseq.LayoutTy.TupL [natL, natL, natL], ptrNat, ptrNat, ptrNat, natL]
def sY : Place ΓY (obseq.LayoutTy.TupL [natL, natL, natL]) :=
  .local ⟨⟨0, by decide⟩, rfl⟩
def p0Y : Place ΓY ptrNat := .local ⟨⟨1, by decide⟩, rfl⟩
def p1Y : Place ΓY ptrNat := .local ⟨⟨2, by decide⟩, rfl⟩
def p2Y : Place ΓY ptrNat := .local ⟨⟨3, by decide⟩, rfl⟩
def tY : Place ΓY natL := .local ⟨⟨4, by decide⟩, rfl⟩
def f0Y : Place ΓY natL := .proj sY (.field (tys := [natL, natL, natL]) ⟨0, by decide⟩ .nil)
def f1Y : Place ΓY natL := .proj sY (.field (tys := [natL, natL, natL]) ⟨1, by decide⟩ .nil)
def f2Y : Place ΓY natL := .proj sY (.field (tys := [natL, natL, natL]) ⟨2, by decide⟩ .nil)

def d27_split_field_borrows : IO Unit :=
  expectDiff ΓY
    [.assign f0Y (.constInit 1),
     .assign f1Y (.constInit 2),
     .assign f2Y (.constInit 3),
     .assign p0Y (.ref .Mut false [] f0Y),
     .assign p1Y (.ref .Mut false [] f1Y),
     .assign p2Y (.ref .Mut false [] f2Y),
     .assign (.deref p1Y) (.constInit 20),
     .assign (.deref p0Y) (.constInit 10),
     .assign (.deref p2Y) (.constInit 30),
     .assign (.deref p1Y) (.constInit 21),
     .assign tY (.copy (.deref p2Y))]
    .ok "d27 three simultaneous &mut field borrows, interleaved mutation"

def d28_parent_write_cellwise : IO Unit :=
  expectDiff ΓY
    [.assign f0Y (.constInit 1),
     .assign f1Y (.constInit 2),
     .assign p0Y (.ref .Mut false [] f0Y),
     .assign p1Y (.ref .Mut false [] f1Y),
     .assign f0Y (.constInit 7),
     .assign (.deref p1Y) (.constInit 20)]
    .ok "d28 parent write to s.0 leaves &mut s.1 alive"

def d29_parent_write_kills_overlap : IO Unit :=
  expectDiff ΓY
    [.assign f0Y (.constInit 1),
     .assign p0Y (.ref .Mut false [] f0Y),
     .assign f0Y (.constInit 7),
     .assign (.deref p0Y) (.constInit 10)]
    (.ub 3) "d29 the parent write invalidated p0 itself"

/-! d30/d31: the reachable side of the invariant-gap example. d30 is the
    canonical reborrow `L := &mut *p` — well-sized by construction, so
    the new retag-dereferenceable check must NOT fire on either machine.
    d31 is the ZST twist: the SAME shape with a zero-sized pointee —
    `pz := &mut z; L := &mut *pz` — where the stored pointer legitimately
    has size 0 and the range-form checks admit it. Together with unit
    t16 (the forged size-0 pointer at pointee u64, which must err) they
    pin all three corners of the example. -/
def ΓZ : Ctx := [natL, ptrNat, ptrNat, natL]
def xZ : Place ΓZ natL := .local ⟨⟨0, by decide⟩, rfl⟩
def pZ : Place ΓZ ptrNat := .local ⟨⟨1, by decide⟩, rfl⟩
def LZ : Place ΓZ ptrNat := .local ⟨⟨2, by decide⟩, rfl⟩
def tZ : Place ΓZ natL := .local ⟨⟨3, by decide⟩, rfl⟩

def d30_reborrow_through_pointer : IO Unit :=
  expectDiff ΓZ
    [.assign xZ (.constInit 1),
     .assign pZ (.ref .Mut false [] xZ),
     .assign LZ (.ref .Mut false [] (.deref pZ)),
     .assign (.deref LZ) (.constInit 2),
     .assign tZ (.copy xZ)]
    .ok "d30 reborrow &mut *p, write through it"

abbrev unitL := obseq.LayoutTy.TupL ([] : List obseq.LayoutTy)
def ΓZ2 : Ctx := [unitL, .PtrL unitL, .PtrL unitL, natL]
def zZ : Place ΓZ2 unitL := .local ⟨⟨0, by decide⟩, rfl⟩
def pzZ : Place ΓZ2 (.PtrL unitL) := .local ⟨⟨1, by decide⟩, rfl⟩
def LzZ : Place ΓZ2 (.PtrL unitL) := .local ⟨⟨2, by decide⟩, rfl⟩
def tZ2 : Place ΓZ2 natL := .local ⟨⟨3, by decide⟩, rfl⟩

def d31_zst_reborrow : IO Unit :=
  expectDiff ΓZ2
    [.assign zZ .uninit,
     .assign pzZ (.ref .Mut false [] zZ),
     .assign LzZ (.ref .Mut false [] (.deref pzZ)),
     .assign tZ2 (.constInit 5)]
    .ok "d31 reborrow through a zero-sized pointee"


/-- Differential: `y := copy s.0` — a ZERO-offset field copy is a bare
    `Memcpy` off the base register (no Borrow, no Die); the source reads
    the field range through the base tag. Covers regime P0→L
    (`copy_proj_zero_simulation`). -/
def ΓD32 : Ctx := [pairL, natL]
def tupD32 : Place ΓD32 pairL := .local ⟨⟨0, by decide⟩, rfl⟩
def yD32 : Place ΓD32 natL := .local ⟨⟨1, by decide⟩, rfl⟩

def d32_field_copy_zero_offset : IO Unit :=
  expectDiff ΓD32
    [.assign (.proj tupD32 (.field ⟨0, by decide⟩ .nil)) (.constInit 3),
     .assign (.proj tupD32 (.field ⟨1, by decide⟩ .nil)) (.constInit 4),
     .assign yD32 (.copy (.proj tupD32 (.field ⟨0, by decide⟩ .nil)))]
    .ok "d32 field copy zero offset"

/-- FIXED-BUG witness, REWRITTEN 2026-08-30 (the temp-assignment
    lowering). This hand-forged state — `y : natL` re-bound INSIDE
    `tup : pairL`'s block, cell 1's stack `[Ref 4, MutRef 3, Own 1]`,
    `tup.tag := 4`, `y.tag := 3` — used to make `y := copy tup.1`
    DIVERGE: the old lowering was `Borrow; Memcpy; Die`, and the
    `Memcpy`'s dst write popped the fresh borrow tag that the following
    `Die` needed, so the target erred where mirlite succeeded. The
    overlapping-assignment guard papered over it by making BOTH refuse.

    The copy now lowers to `Borrow; Load; Die; RStore` — the value is
    read into a register and the temporary borrow retires BEFORE the
    write — so the countermodel dissolves in the good direction: both
    machines SUCCEED and end with the same cell-1 stack. Teeth: putting
    the write back before the `Die` resurrects the one-sided error. -/
def ΓD33 : Ctx := [pairL, natL]
def tupD33 : Place ΓD33 pairL := .local ⟨⟨0, by decide⟩, rfl⟩
def yLocD33 : Local ΓD33 natL := ⟨⟨1, by decide⟩, rfl⟩

def d33_overlap_junk_copy_agrees : IO Unit := do
  -- the shared permission state (rename = identity on both machines)
  let perms : AccessPerms :=
    { StackMap := [(0, [.Own 1]),
                   (1, [.Ref 4, .MutRef 3, .Own 1]),
                   (2, [.Own 2])],
      NextTag := 5 }
  -- SOURCE: y forged INSIDE tup's block, tags picked from cell 1's stack
  let env : mirlite.Env ΓD33 :=
    ((mirlite.Env.empty.set ⟨⟨0, by decide⟩, rfl⟩ { addr := 0, tag := 4 }).set
      yLocD33 { addr := 1, tag := 3 })
  let junkSrc : mirlite.State M ΓD33 :=
    { pc := 0, env := env,
      mem := { mMap := [(0, .word 7), (1, .word 8), (2, .word 9)],
               addrStart := 3, allocs := [(0, 2), (2, 1)] },
      perms := perms }
  let stmt : Stmt ΓD33 :=
    .assign (.local yLocD33) (.copy (.proj tupD33 (.field ⟨1, by decide⟩ .nil)))
  let srcPerms ←
    match mirlite.stepStmt M junkSrc stmt with
    | .err e => throw (IO.userError s!"d33: source should now SUCCEED, got: {e}")
    | .ok st => pure st.perms
  -- TARGET: same stacks, registers holding the forged pointers; the
  -- program is exactly what the compiler emits for the statement
  let junkTgt : oseair.State M :=
    { pc := 0,
      reg := [(.R 0, (.PTy, [.Ptr 0 0 2 4])),    -- tup: base 0, size 2, tag 4
              (.R 1, (.PTy, [.Ptr 1 0 1 3]))],   -- y (forged): base 1, size 1, tag 3
      mem := { mMap := [(0, .Dat 7), (1, .Dat 8), (2, .Dat 9)],
               addrStart := 3, allocs := [(0, 2), (2, 1)] },
      perms := perms }
  let instrs : List oseair.Instr :=
    [.Assgn (.R 2) (borrowRhs .Shared 1 (.R 0) 1),   -- Borrow(Shared) of tup.1
     .Assgn (.R 3) (.Load .NatTy (.R 2)),            -- the READ, into a register
     .Die (.R 2) 1,                                  -- the temporary retires
     .RStore .NatTy (.R 3) (.R 1)]                   -- then the write
  let prog : oseair.Prog := fun n => instrs.get? n
  let tgtPerms ←
    match oseair.runN M 4 junkTgt prog with
    | .Err e => throw (IO.userError s!"d33: target should now SUCCEED, got: {e}")
    | .Ok st => pure st.perms
  assert (srcPerms.StackMap.lookup 1 == tgtPerms.StackMap.lookup 1)
    s!"d33: cell-1 stacks disagree: {reprStr (srcPerms.StackMap.lookup 1)} vs {reprStr (tgtPerms.StackMap.lookup 1)}"

/-- FIXED-BUG witness (was the KNOWN-COMPILER-BUG pin, flipped
    2026-08-28 when the lowering-order fix landed): the assign-place
    lowering used to mint its dst temporary `Borrow(Mut)` BEFORE the
    rhs ran, and the rhs's deref spine legitimately READS the guarded
    cell (a pointer cell on its own path) — with raw pointers this is
    legal aliasing on both machines, so the target erred where mirlite
    succeeded (a REACHABLE divergence: `t : (u64, *mut u64)`,
    `p = &raw mut t`, `w = &raw mut t.1`, `(*p).1 := &mut **w`).
    `compileStmtChecked`'s assign-place arm now uses MIR's order — rhs
    source code first, then the destination lowering, then the store —
    and both machines agree. Teeth: reverting the arm to the old order
    makes this test report `.ub 5` again. -/
def tPairL := obseq.LayoutTy.TupL [natL, ptrNat]
def ΓD34 : Ctx := [tPairL, .PtrL tPairL, .PtrL ptrNat, natL]
def tD34 : Place ΓD34 tPairL := .local ⟨⟨0, by decide⟩, rfl⟩
def pD34 : Place ΓD34 (.PtrL tPairL) := .local ⟨⟨1, by decide⟩, rfl⟩
def wD34 : Place ΓD34 (.PtrL ptrNat) := .local ⟨⟨2, by decide⟩, rfl⟩
def xD34 : Place ΓD34 natL := .local ⟨⟨3, by decide⟩, rfl⟩

def d34_deref_dst_temp_killed_by_rhs_spine : IO Unit := do
  let prog : Prog ΓD34 :=
    [.assign xD34 (.constInit 5),
     .assign (.proj tD34 (.field ⟨0, by decide⟩ .nil)) (.constInit 1),
     .assign (.proj tD34 (.field ⟨1, by decide⟩ .nil)) (.ref (.Raw true) false [] xD34),
     .assign pD34 (.ref (.Raw true) false [] tD34),
     .assign wD34 (.ref (.Raw true) false [] (.proj tD34 (.field ⟨1, by decide⟩ .nil))),
     .assign (.proj (.deref pD34) (.field ⟨1, by decide⟩ .nil))
       (.ref .Mut false [] (.deref (.deref wD34)))]
  expectDiff ΓD34 prog .ok "d34 deref dst temp survives rhs spine"

/-- Differential: the exact self-copy `x := copy x` — REWRITTEN
    2026-08-30. It used to be UB on both machines (mirlite's overlap
    guard, oseair's `Memcpy` nonoverlapping check). Rust permits it:
    rustc reads into a temporary first (`_5 = (*_2); (*_2) = move _5`,
    checked on rustc 1.91.0), and Miri runs it clean. Both machines now
    do the same — the value goes into a register, then back out — so an
    overlapping assignment is WELL DEFINED here too. -/
def d35_self_copy_is_ok : IO Unit :=
  expectDiff ΓA
    [.assign xA (.constInit 7),
     .assign xA (.copy xA)]
    .ok "d35 self copy is ok"

/-- Differential: a NONZERO-offset field copy `y := copy s.1` — the
    `[Borrow(Shared); Memcpy; Die]` fragment whose interleaved die is
    slid past the dst write by the disjoint-range commutation. Covers
    regime P→L (`copy_proj_offset_simulation`). -/
def d36_field_copy_nonzero_offset : IO Unit :=
  expectDiff ΓD32
    [.assign (.proj tupD32 (.field ⟨0, by decide⟩ .nil)) (.constInit 3),
     .assign (.proj tupD32 (.field ⟨1, by decide⟩ .nil)) (.constInit 4),
     .assign yD32 (.copy (.proj tupD32 (.field ⟨1, by decide⟩ .nil)))]
    .ok "d36 field copy nonzero offset"

/-- Differential: copy THROUGH a pointer — `y := copy *p` with
    `p = &mut x` — the `[Load; Memcpy]` fragment reading through the
    loaded tag. Covers regime D→L (`copy_deref_local_simulation`). -/
def d37_copy_through_pointer : IO Unit :=
  expectDiff ΓA
    [.assign xA (.constInit 7),
     .assign pA (.ref .Mut false [] xA),
     .assign tA (.copy (.deref pA))]
    .ok "d37 copy through pointer"

/-- Differential: a NESTED projection tower write — `s.1.0 := v` over a
    pair-of-pairs — exercising the flattening recursion (the lowering
    reassociates; the source composes offsets). -/
def nestL := obseq.LayoutTy.TupL [pairL, pairL]
def ΓD38 : Ctx := [nestL]
def sD38 : Place ΓD38 nestL := .local ⟨⟨0, by decide⟩, rfl⟩

def d38_nested_proj_write : IO Unit :=
  expectDiff ΓD38
    [.assign (.proj (.proj sD38 (.field ⟨1, by decide⟩ .nil))
        (.field ⟨0, by decide⟩ .nil)) (.constInit 9)]
    .ok "d38 nested proj write"

/-- Differential: a ZERO-offset field write through a pointer —
    `(*p).0 := v` — the `[Load; CStore]` fragment
    (`const_write_proj_deref_zero_simulation`). -/
def ΓD39 : Ctx := [pairL, .PtrL pairL]
def tD39 : Place ΓD39 pairL := .local ⟨⟨0, by decide⟩, rfl⟩
def pD39 : Place ΓD39 (.PtrL pairL) := .local ⟨⟨1, by decide⟩, rfl⟩

def d39_deref_field_zero_write : IO Unit :=
  expectDiff ΓD39
    [.assign (.proj tD39 (.field ⟨0, by decide⟩ .nil)) (.constInit 1),
     .assign (.proj tD39 (.field ⟨1, by decide⟩ .nil)) (.constInit 2),
     .assign pD39 (.ref .Mut false [] tD39),
     .assign (.proj (.deref pD39) (.field ⟨0, by decide⟩ .nil)) (.constInit 7)]
    .ok "d39 deref field zero write"

/-- Differential: a reference stored INTO A FIELD at zero offset —
    `t.0 := &x` with `t : (*mut u64, u64)`-ish — the first non-local
    DESTINATION regime (`ref_local_projzero_simulation`): the RStore
    goes through the dst BASE register into the field. -/
def refFieldL := obseq.LayoutTy.TupL [ptrNat, natL]
def ΓD40 : Ctx := [refFieldL, natL]
def tD40 : Place ΓD40 refFieldL := .local ⟨⟨0, by decide⟩, rfl⟩
def xD40 : Place ΓD40 natL := .local ⟨⟨1, by decide⟩, rfl⟩

def d40_ref_into_field_zero : IO Unit :=
  expectDiff ΓD40
    [.assign xD40 (.constInit 5),
     .assign (.proj tD40 (.field ⟨1, by decide⟩ .nil)) (.constInit 1),
     .assign (.proj tD40 (.field ⟨0, by decide⟩ .nil)) (.ref .Mut false [] xD40),
     .assign (.deref (.proj tD40 (.field ⟨0, by decide⟩ .nil))) (.constInit 9)]
    .ok "d40 ref into field zero"

/-- Differential: a reference stored into a NONZERO-offset field —
    `t.1 := &mut x` with the pointer field second — the
    `[BorrowS; BorrowM; RStore; Die]` fragment (BRIDGE 1 around the
    store), then a write THROUGH the stored reference. -/
def refField2L := obseq.LayoutTy.TupL [natL, ptrNat]
def ΓD41 : Ctx := [refField2L, natL]
def tD41 : Place ΓD41 refField2L := .local ⟨⟨0, by decide⟩, rfl⟩
def xD41 : Place ΓD41 natL := .local ⟨⟨1, by decide⟩, rfl⟩

def d41_ref_into_field_offset : IO Unit :=
  expectDiff ΓD41
    [.assign xD41 (.constInit 5),
     .assign (.proj tD41 (.field ⟨0, by decide⟩ .nil)) (.constInit 1),
     .assign (.proj tD41 (.field ⟨1, by decide⟩ .nil)) (.ref .Mut false [] xD41),
     .assign (.deref (.proj tD41 (.field ⟨1, by decide⟩ .nil))) (.constInit 9)]
    .ok "d41 ref into field offset"

/-- Differential: a reference stored into a NESTED field — `s.1.1 :=
    &mut x` over a pair-of-(nat,ptr) — the dst-flattening recursion for
    ref (the lowering reassociates to one field borrow), then a write
    through the stored reference. -/
def nestRefL := obseq.LayoutTy.TupL [natL, refField2L]
def ΓD42 : Ctx := [nestRefL, natL]
def sD42 : Place ΓD42 nestRefL := .local ⟨⟨0, by decide⟩, rfl⟩
def xD42 : Place ΓD42 natL := .local ⟨⟨1, by decide⟩, rfl⟩

def d42_ref_into_nested_field : IO Unit :=
  expectDiff ΓD42
    [.assign xD42 (.constInit 5),
     .assign (.proj (.proj sD42 (.field ⟨1, by decide⟩ .nil))
        (.field ⟨1, by decide⟩ .nil)) (.ref .Mut false [] xD42),
     .assign (.deref (.proj (.proj sD42 (.field ⟨1, by decide⟩ .nil))
        (.field ⟨1, by decide⟩ .nil))) (.constInit 9)]
    .ok "d42 ref into nested field"

def ptrPtrNat := obseq.LayoutTy.PtrL ptrNat
def ΓD43 : Ctx := [ptrPtrNat, ptrNat, natL, natL]
def qD43 : Place ΓD43 ptrPtrNat := .local ⟨⟨0, by decide⟩, rfl⟩
def rD43 : Place ΓD43 ptrNat := .local ⟨⟨1, by decide⟩, rfl⟩
def xD43 : Place ΓD43 natL := .local ⟨⟨2, by decide⟩, rfl⟩
def yD43 : Place ΓD43 natL := .local ⟨⟨3, by decide⟩, rfl⟩

/-- Positive: a reference stored THROUGH a loaded pointer (`*q := &mut x`,
    the deref-dst ref regime, closed 2026-08-29), then written through the
    stored reference by a double-deref. Exercises the MIR order on both
    machines: the `Borrow` runs BEFORE the dst spine's `Load`s. -/
def d43_ref_through_loaded_ptr : IO Unit :=
  expectDiff ΓD43
    [.assign xD43 (.constInit 5),
     .assign yD43 (.constInit 6),
     .assign rD43 (.ref .Mut false [] yD43),
     .assign qD43 (.ref .Mut false [] rD43),
     .assign (.deref qD43) (.ref .Mut false [] xD43),
     .assign (.deref (.deref qD43)) (.constInit 9)]
    .ok "d43 ref through loaded ptr"

def sD44L := obseq.LayoutTy.TupL [natL, ptrPtrNat]
def ΓD44 : Ctx := [sD44L, ptrNat, natL]
def sD44 : Place ΓD44 sD44L := .local ⟨⟨0, by decide⟩, rfl⟩
def rD44 : Place ΓD44 ptrNat := .local ⟨⟨1, by decide⟩, rfl⟩
def xD44 : Place ΓD44 natL := .local ⟨⟨2, by decide⟩, rfl⟩

/-- Positive: a double-deref THROUGH a pointer-to-pointer FIELD —
    `*(*(s.f)) := v`. The dst's pointer place is a `PtrChain` with an
    interior projection (`.deref (.proj s f)`), the first shape the
    pending-cleanup spine generalization routes to a closed leaf
    (2026-08-29): its lowering is `Borrow(Shared); Load; Die; Load;
    CStore`, the triple cancelled by BRIDGE 1S. -/
def d44_write_through_ptr_field_chain : IO Unit :=
  expectDiff ΓD44
    [.assign xD44 (.constInit 5),
     .assign rD44 (.ref .Mut false [] xD44),
     .assign (.proj sD44 (.field ⟨1, by decide⟩ .nil)) (.ref .Mut false [] rD44),
     .assign (.deref (.deref (.proj sD44 (.field ⟨1, by decide⟩ .nil))))
       (.constInit 9)]
    .ok "d44 write through ptr-field chain"

/-- Positive: the ref sibling — a reference stored through the same
    interior-projection chain (`*(*(s.f)) := &mut y`), then written
    through. Exercises `ref_derefdst_local_simulation` over a
    `PtrChain` with a proj level. -/
def ptrPtrPtrNat := obseq.LayoutTy.PtrL ptrPtrNat
def sD45L := obseq.LayoutTy.TupL [natL, ptrPtrPtrNat]
def ΓD45 : Ctx := [sD45L, ptrPtrNat, ptrNat, natL, natL]
def sD45 : Place ΓD45 sD45L := .local ⟨⟨0, by decide⟩, rfl⟩
def qD45 : Place ΓD45 ptrPtrNat := .local ⟨⟨1, by decide⟩, rfl⟩
def rD45 : Place ΓD45 ptrNat := .local ⟨⟨2, by decide⟩, rfl⟩
def xD45 : Place ΓD45 natL := .local ⟨⟨3, by decide⟩, rfl⟩
def yD45 : Place ΓD45 natL := .local ⟨⟨4, by decide⟩, rfl⟩

def d45_ref_through_ptr_field_chain : IO Unit :=
  expectDiff ΓD45
    [.assign xD45 (.constInit 5),
     .assign yD45 (.constInit 6),
     .assign rD45 (.ref .Mut false [] xD45),
     .assign qD45 (.ref .Mut false [] rD45),
     .assign (.proj sD45 (.field ⟨1, by decide⟩ .nil)) (.ref .Mut false [] qD45),
     .assign (.deref (.deref (.proj sD45 (.field ⟨1, by decide⟩ .nil))))
       (.ref .Mut false [] yD45),
     .assign (.deref (.deref (.deref (.proj sD45 (.field ⟨1, by decide⟩ .nil)))))
       (.constInit 9)]
    .ok "d45 ref through ptr-field chain"

def tD46L := obseq.LayoutTy.TupL [natL, ptrNat]
def ΓD46 : Ctx := [tD46L, obseq.LayoutTy.PtrL tD46L, natL]
def tD46 : Place ΓD46 tD46L := .local ⟨⟨0, by decide⟩, rfl⟩
def qD46 : Place ΓD46 (obseq.LayoutTy.PtrL tD46L) := .local ⟨⟨1, by decide⟩, rfl⟩
def xD46 : Place ΓD46 natL := .local ⟨⟨2, by decide⟩, rfl⟩

/-- Positive: write through the pointer FIELD of a DEREFERENCED struct —
    `*((*q).f) := v`. The dst is a `PtrChain` whose projection sits over
    a code-emitting base (`.deref q`), the shape the chain-dst leaf
    (`const_write_deref_chain_simulation`, 2026-08-29) closed when it
    subsumed the depth-1 `*(s.f) := v` leaf. -/
def d46_write_through_deref_struct_field : IO Unit :=
  expectDiff ΓD46
    [.assign xD46 (.constInit 5),
     .assign (.proj tD46 (.field ⟨1, by decide⟩ .nil)) (.ref .Mut false [] xD46),
     .assign qD46 (.ref .Mut false [] tD46),
     .assign (.deref (.proj (.deref qD46) (.field ⟨1, by decide⟩ .nil)))
       (.constInit 9)]
    .ok "d46 write through deref-struct field"

def ΓD47 : Ctx := [refField2L, natL, natL]
def sD47 : Place ΓD47 refField2L := .local ⟨⟨0, by decide⟩, rfl⟩
def xD47 : Place ΓD47 natL := .local ⟨⟨1, by decide⟩, rfl⟩
def yD47 : Place ΓD47 natL := .local ⟨⟨2, by decide⟩, rfl⟩

/-- Positive: copy THROUGH a pointer field — `y := copy *(s.f)`. The
    src is a proj-topped `PtrChain`, the shape the collapsed copy leaf
    (mother lemma on the WHOLE source place, 2026-08-29) serves. -/
def d47_copy_through_ptr_field : IO Unit :=
  expectDiff ΓD47
    [.assign xD47 (.constInit 5),
     .assign (.proj sD47 (.field ⟨1, by decide⟩ .nil)) (.ref .Mut false [] xD47),
     .assign yD47 (.copy (.deref (.proj sD47 (.field ⟨1, by decide⟩ .nil))))]
    .ok "d47 copy through ptr field"

def tD48L := obseq.LayoutTy.TupL [natL, ptrPtrNat]
def ΓD48 : Ctx := [tD48L, ptrNat, natL, natL]
def tD48 : Place ΓD48 tD48L := .local ⟨⟨0, by decide⟩, rfl⟩
def rD48 : Place ΓD48 ptrNat := .local ⟨⟨1, by decide⟩, rfl⟩
def xD48 : Place ΓD48 natL := .local ⟨⟨2, by decide⟩, rfl⟩
def yD48 : Place ΓD48 natL := .local ⟨⟨3, by decide⟩, rfl⟩

/-- Positive: a reference stored THROUGH a pointer-to-pointer FIELD —
    `*(t.f) := &mut y`, then written through double-deref. The dst is a
    proj-topped `PtrChain`, the shape the collapsed ref deref-dst leaf
    (mother lemma at `Mut` on the WHOLE dst, 2026-08-29) serves. -/
def d48_ref_through_ptr_field_dst : IO Unit :=
  expectDiff ΓD48
    [.assign xD48 (.constInit 5),
     .assign yD48 (.constInit 6),
     .assign rD48 (.ref .Mut false [] xD48),
     .assign (.proj tD48 (.field ⟨1, by decide⟩ .nil)) (.ref .Mut false [] rD48),
     .assign (.deref (.proj tD48 (.field ⟨1, by decide⟩ .nil)))
       (.ref .Mut false [] yD48),
     .assign (.deref (.deref (.proj tD48 (.field ⟨1, by decide⟩ .nil))))
       (.constInit 9)]
    .ok "d48 ref through ptr field dst"

def ΓD49 : Ctx := [refField2L, natL, ptrNat, natL]
def sD49 : Place ΓD49 refField2L := .local ⟨⟨0, by decide⟩, rfl⟩
def xD49 : Place ΓD49 natL := .local ⟨⟨1, by decide⟩, rfl⟩
def qD49 : Place ΓD49 ptrNat := .local ⟨⟨2, by decide⟩, rfl⟩
def yD49 : Place ΓD49 natL := .local ⟨⟨3, by decide⟩, rfl⟩

/-- Positive: a reference TO the pointee of a pointer field —
    `q := &mut *(s.f)`, then written through. The rhs's source place is
    a proj-topped `PtrChain`, the shape the collapsed ref deref-src
    leaf (mother lemma at `Shared` on the WHOLE source place,
    2026-08-29) serves. -/
def d49_ref_of_deref_ptr_field : IO Unit :=
  expectDiff ΓD49
    [.assign xD49 (.constInit 5),
     .assign (.proj sD49 (.field ⟨1, by decide⟩ .nil)) (.ref .Mut false [] xD49),
     .assign qD49 (.ref .Mut false []
       (.deref (.proj sD49 (.field ⟨1, by decide⟩ .nil)))),
     .assign (.deref qD49) (.constInit 9),
     .assign yD49 (.copy (.deref qD49))]
    .ok "d49 ref of deref ptr field"

def innerD50L := obseq.LayoutTy.TupL [natL, ptrNat]
def sD50L := obseq.LayoutTy.TupL [natL, innerD50L]
def ΓD50 : Ctx := [sD50L, natL, natL]
def sD50 : Place ΓD50 sD50L := .local ⟨⟨0, by decide⟩, rfl⟩
def xD50 : Place ΓD50 natL := .local ⟨⟨1, by decide⟩, rfl⟩
def yD50 : Place ΓD50 natL := .local ⟨⟨2, by decide⟩, rfl⟩

/-- Positive: write through a DOUBLY-nested pointer field —
    `*(s.f.g) := v`. The dst's pointer place is a proj-of-proj
    spelling, normalized by `flattenPlace` into the chain grammar
    (2026-08-29, the increment that retired the deep residual). -/
def d50_write_through_nested_ptr_field : IO Unit :=
  expectDiff ΓD50
    [.assign xD50 (.constInit 5),
     .assign (.proj (.proj sD50 (.field ⟨1, by decide⟩ .nil))
        (.field ⟨1, by decide⟩ .nil)) (.ref .Mut false [] xD50),
     .assign (.deref (.proj (.proj sD50 (.field ⟨1, by decide⟩ .nil))
        (.field ⟨1, by decide⟩ .nil))) (.constInit 9),
     .assign yD50 (.copy (.deref (.proj (.proj sD50 (.field ⟨1, by decide⟩ .nil))
        (.field ⟨1, by decide⟩ .nil))))]
    .ok "d50 write through nested ptr field"

def ΓD51 : Ctx := [sD50L, natL, natL, ptrNat]
def sD51 : Place ΓD51 sD50L := .local ⟨⟨0, by decide⟩, rfl⟩
def xD51 : Place ΓD51 natL := .local ⟨⟨1, by decide⟩, rfl⟩
def yD51 : Place ΓD51 natL := .local ⟨⟨2, by decide⟩, rfl⟩
def qD51 : Place ΓD51 ptrNat := .local ⟨⟨3, by decide⟩, rfl⟩

/-- Positive: copy AND ref through a doubly-nested pointer field —
    `y := copy *(s.f.g)` and `q := &mut *(s.f.g)`. The proj-of-proj
    src spellings are flatten-normalized (2026-08-29 flatten transfer
    across the copy/ref dispatchers, which made the deref arms TOTAL). -/
def d51_copy_ref_through_nested_ptr_field : IO Unit :=
  expectDiff ΓD51
    [.assign xD51 (.constInit 5),
     .assign (.proj (.proj sD51 (.field ⟨1, by decide⟩ .nil))
        (.field ⟨1, by decide⟩ .nil)) (.ref .Mut false [] xD51),
     .assign yD51 (.copy (.deref (.proj (.proj sD51 (.field ⟨1, by decide⟩ .nil))
        (.field ⟨1, by decide⟩ .nil)))),
     .assign qD51 (.ref .Mut false []
       (.deref (.proj (.proj sD51 (.field ⟨1, by decide⟩ .nil))
          (.field ⟨1, by decide⟩ .nil)))),
     .assign (.deref qD51) (.constInit 9)]
    .ok "d51 copy and ref through nested ptr field"

def pairD52L := obseq.LayoutTy.TupL [natL, natL]
def ΓD52 : Ctx := [obseq.LayoutTy.PtrL (obseq.LayoutTy.PtrL pairD52L),
  obseq.LayoutTy.PtrL pairD52L, pairD52L, natL]
def qD52 : Place ΓD52 (obseq.LayoutTy.PtrL (obseq.LayoutTy.PtrL pairD52L)) :=
  .local ⟨⟨0, by decide⟩, rfl⟩
def rD52 : Place ΓD52 (obseq.LayoutTy.PtrL pairD52L) := .local ⟨⟨1, by decide⟩, rfl⟩
def sD52 : Place ΓD52 pairD52L := .local ⟨⟨2, by decide⟩, rfl⟩
def yD52 : Place ΓD52 natL := .local ⟨⟨3, by decide⟩, rfl⟩

/-- Positive: projected writes through a DEPTH-2 chain — `(**q).0 := v`
    (zero offset) and `(**q).1 := w` (nonzero, BRIDGE 1). The C-deref
    leaves collapsed onto the mother lemma (2026-08-29) gate the WHOLE
    pointer place `*q` as a `PtrChain`, so interior `Load`s stack under
    the projection's `Borrow`/`CStore`/`Die`. -/
def d52_proj_write_through_chain : IO Unit :=
  expectDiff ΓD52
    [.assign (.proj sD52 (.field ⟨0, by decide⟩ .nil)) (.constInit 1),
     .assign (.proj sD52 (.field ⟨1, by decide⟩ .nil)) (.constInit 2),
     .assign rD52 (.ref .Mut false [] sD52),
     .assign qD52 (.ref .Mut false [] rD52),
     .assign (.proj (.deref (.deref qD52)) (.field ⟨0, by decide⟩ .nil))
       (.constInit 7),
     .assign (.proj (.deref (.deref qD52)) (.field ⟨1, by decide⟩ .nil))
       (.constInit 9),
     .assign yD52 (.copy (.proj sD52 (.field ⟨1, by decide⟩ .nil)))]
    .ok "d52 proj write through chain"

def pD53L := obseq.LayoutTy.PtrL pairD52L
def innerD53L := obseq.LayoutTy.TupL [natL, pD53L]
def sD53L := obseq.LayoutTy.TupL [natL, innerD53L]
def ΓD53 : Ctx := [sD53L, pairD52L, natL]
def sD53 : Place ΓD53 sD53L := .local ⟨⟨0, by decide⟩, rfl⟩
def tD53 : Place ΓD53 pairD52L := .local ⟨⟨1, by decide⟩, rfl⟩
def yD53 : Place ΓD53 natL := .local ⟨⟨2, by decide⟩, rfl⟩

/-- Positive: projected write through a NON-chain pointer place —
    `(*(s.f.g)).1 := v`, whose base is a proj-of-proj the dispatcher
    can only reach through the flatten transfer (2026-08-29: the
    proj-dst deref arm made TOTAL). -/
def d53_proj_write_through_flattened_ptr : IO Unit :=
  expectDiff ΓD53
    [.assign (.proj tD53 (.field ⟨1, by decide⟩ .nil)) (.constInit 3),
     .assign (.proj (.proj sD53 (.field ⟨1, by decide⟩ .nil))
        (.field ⟨1, by decide⟩ .nil)) (.ref .Mut false [] tD53),
     .assign (.proj (.deref (.proj (.proj sD53 (.field ⟨1, by decide⟩ .nil))
        (.field ⟨1, by decide⟩ .nil))) (.field ⟨1, by decide⟩ .nil))
       (.constInit 9),
     .assign yD53 (.copy (.proj tD53 (.field ⟨1, by decide⟩ .nil)))]
    .ok "d53 proj write through flattened ptr"

def ΓD54 : Ctx := [pairD52L, pairD52L, natL, natL]
def sD54 : Place ΓD54 pairD52L := .local ⟨⟨0, by decide⟩, rfl⟩
def tD54 : Place ΓD54 pairD52L := .local ⟨⟨1, by decide⟩, rfl⟩
def xD54 : Place ΓD54 natL := .local ⟨⟨2, by decide⟩, rfl⟩
def yD54 : Place ΓD54 natL := .local ⟨⟨3, by decide⟩, rfl⟩

/-- Positive: projected writes whose FIRST touch allocates the root —
    `s.1 := v` with `s` unbound (regime B-proj, nonzero offset: the
    root `Alloc` must size the WHOLE tuple, then `Borrow; CStore; Die`
    lands inside it) and `t.0 := w` with `t` unbound (zero offset:
    `Alloc; CStore` at the block base). Closed 2026-08-29, the
    increment that killed `const_write_proj_nonlocal_residual`. -/
def d54_fresh_root_proj_writes : IO Unit :=
  expectDiff ΓD54
    [.assign (.proj sD54 (.field ⟨1, by decide⟩ .nil)) (.constInit 9),
     .assign (.proj sD54 (.field ⟨0, by decide⟩ .nil)) (.constInit 4),
     .assign (.proj tD54 (.field ⟨0, by decide⟩ .nil)) (.constInit 5),
     .assign xD54 (.copy (.proj sD54 (.field ⟨1, by decide⟩ .nil))),
     .assign yD54 (.copy (.proj tD54 (.field ⟨0, by decide⟩ .nil)))]
    .ok "d54 fresh root proj writes"

def ΓD55 : Ctx := [obseq.LayoutTy.PtrL pairD52L, pairD52L, natL, natL]
def pD55 : Place ΓD55 (obseq.LayoutTy.PtrL pairD52L) := .local ⟨⟨0, by decide⟩, rfl⟩
def sD55 : Place ΓD55 pairD52L := .local ⟨⟨1, by decide⟩, rfl⟩
def xD55 : Place ΓD55 natL := .local ⟨⟨2, by decide⟩, rfl⟩
def yD55 : Place ΓD55 natL := .local ⟨⟨3, by decide⟩, rfl⟩

/-- Positive: copies out of a projection over a POINTER chain —
    `x := copy (*p).0` (zero offset) and `y := copy (*p).1` (nonzero:
    `Borrow(Shared); Memcpy; Die`, the dst write sliding between
    BRIDGE 1S's phases). Closed 2026-08-29 by collapsing the P0/P→L
    leaves onto the mother lemma at the chain base. -/
def d55_copy_from_proj_over_chain : IO Unit :=
  expectDiff ΓD55
    [.assign (.proj sD55 (.field ⟨0, by decide⟩ .nil)) (.constInit 3),
     .assign (.proj sD55 (.field ⟨1, by decide⟩ .nil)) (.constInit 4),
     .assign pD55 (.ref .Mut false [] sD55),
     .assign xD55 (.copy (.proj (.deref pD55) (.field ⟨0, by decide⟩ .nil))),
     .assign yD55 (.copy (.proj (.deref pD55) (.field ⟨1, by decide⟩ .nil)))]
    .ok "d55 copy from proj over chain"

def innerD56L := obseq.LayoutTy.TupL [natL, natL]
def sD56L := obseq.LayoutTy.TupL [natL, innerD56L]
def ΓD56 : Ctx := [sD56L, natL, natL]
def sD56 : Place ΓD56 sD56L := .local ⟨⟨0, by decide⟩, rfl⟩
def xD56 : Place ΓD56 natL := .local ⟨⟨1, by decide⟩, rfl⟩
def yD56 : Place ΓD56 natL := .local ⟨⟨2, by decide⟩, rfl⟩

/-- Positive: copies out of a PROJ-OF-PROJ source — `x := copy s.1.0`
    and `y := copy s.1.1`. The nested spelling is flatten-normalized
    into one projection over the chain base before the leaves see it
    (the src flatten transfer, 2026-08-29). -/
def d56_copy_from_nested_proj : IO Unit :=
  expectDiff ΓD56
    [.assign (.proj (.proj sD56 (.field ⟨1, by decide⟩ .nil))
        (.field ⟨0, by decide⟩ .nil)) (.constInit 7),
     .assign (.proj (.proj sD56 (.field ⟨1, by decide⟩ .nil))
        (.field ⟨1, by decide⟩ .nil)) (.constInit 8),
     .assign xD56 (.copy (.proj (.proj sD56 (.field ⟨1, by decide⟩ .nil))
        (.field ⟨0, by decide⟩ .nil))),
     .assign yD56 (.copy (.proj (.proj sD56 (.field ⟨1, by decide⟩ .nil))
        (.field ⟨1, by decide⟩ .nil)))]
    .ok "d56 copy from nested proj"

def ΓD57 : Ctx := [pairD52L, pairD52L, natL, natL, obseq.LayoutTy.PtrL pairD52L]
def sD57 : Place ΓD57 pairD52L := .local ⟨⟨0, by decide⟩, rfl⟩
def tD57 : Place ΓD57 pairD52L := .local ⟨⟨1, by decide⟩, rfl⟩
def xD57 : Place ΓD57 natL := .local ⟨⟨2, by decide⟩, rfl⟩
def yD57 : Place ΓD57 natL := .local ⟨⟨3, by decide⟩, rfl⟩
def pD57 : Place ΓD57 (obseq.LayoutTy.PtrL pairD52L) := .local ⟨⟨4, by decide⟩, rfl⟩

/-- Positive: copies whose DESTINATION is unbound — the statement's own
    execution allocates it (`Alloc` then `Memcpy`), for a local source
    and for a source read through a pointer chain. Regime B for copy,
    closed 2026-08-29; the address rename extends over the whole fresh
    block. -/
def d57_copy_into_fresh_local : IO Unit :=
  expectDiff ΓD57
    [.assign (.proj sD57 (.field ⟨0, by decide⟩ .nil)) (.constInit 3),
     .assign (.proj sD57 (.field ⟨1, by decide⟩ .nil)) (.constInit 4),
     .assign tD57 (.copy sD57),
     .assign pD57 (.ref .Mut false [] sD57),
     .assign xD57 (.copy (.proj tD57 (.field ⟨1, by decide⟩ .nil))),
     .assign yD57 (.copy (.proj (.deref pD57) (.field ⟨0, by decide⟩ .nil)))]
    .ok "d57 copy into fresh local"

def ΓD58 : Ctx := [pairD52L, natL, natL]
def sD58 : Place ΓD58 pairD52L := .local ⟨⟨0, by decide⟩, rfl⟩
def xD58 : Place ΓD58 natL := .local ⟨⟨1, by decide⟩, rfl⟩
def yD58 : Place ΓD58 natL := .local ⟨⟨2, by decide⟩, rfl⟩

/-- Positive: copies from a FIELD into a destination that the statement
    itself allocates — at zero offset (`Alloc; Memcpy`) and at nonzero
    offset (`Alloc; Borrow(Shared); Memcpy; Die`). Regime B for copy
    with a projected source, closed 2026-08-29. -/
def d58_copy_field_into_fresh_local : IO Unit :=
  expectDiff ΓD58
    [.assign (.proj sD58 (.field ⟨0, by decide⟩ .nil)) (.constInit 3),
     .assign (.proj sD58 (.field ⟨1, by decide⟩ .nil)) (.constInit 4),
     .assign xD58 (.copy (.proj sD58 (.field ⟨0, by decide⟩ .nil))),
     .assign yD58 (.copy (.proj sD58 (.field ⟨1, by decide⟩ .nil)))]
    .ok "d58 copy field into fresh local"

def ppNatD59 := obseq.LayoutTy.PtrL ptrNat
def ΓD59 : Ctx := [natL, ptrNat, ppNatD59, ppNatD59, ptrNat]
def xD59 : Place ΓD59 natL := .local ⟨⟨0, by decide⟩, rfl⟩
def pD59 : Place ΓD59 ptrNat := .local ⟨⟨1, by decide⟩, rfl⟩
def qD59 : Place ΓD59 ppNatD59 := .local ⟨⟨2, by decide⟩, rfl⟩
def q2D59 : Place ΓD59 ppNatD59 := .local ⟨⟨3, by decide⟩, rfl⟩
def rD59 : Place ΓD59 ptrNat := .local ⟨⟨4, by decide⟩, rfl⟩

/-- REGRESSION (the temp-assignment lowering, 2026-08-30): the copy's
    source cell is ALSO a pointer cell that the destination chain must
    read, and the source's tag is a reborrow ABOVE the chain's on that
    cell. Under the old `Memcpy` lowering the chain's read ran FIRST and
    popped the source's tag, so the target trapped where mirlite (and
    Miri) succeed. Now the value is read into a register before the
    destination is lowered, and both machines agree. Teeth: moving the
    read back into the store resurrects the one-sided trap. -/
def d59_copy_read_precedes_dst_chain : IO Unit :=
  expectDiff ΓD59
    [.assign xD59 (.constInit 5),
     .assign pD59 (.ref .Mut false [] xD59),
     .assign qD59 (.ref .Mut false [] pD59),
     .assign q2D59 (.ref .Mut false [] (.deref qD59)),
     .assign rD59 (.ptrCast q2D59),
     .assign (.deref (.deref qD59)) (.copy (.deref rD59))]
    .ok "d59 copy read precedes dst chain"

def ΓD60 : Ctx := [natL, natL, ptrNat, ptrNat]
def xD60 : Place ΓD60 natL := .local ⟨⟨0, by decide⟩, rfl⟩
def yD60 : Place ΓD60 natL := .local ⟨⟨1, by decide⟩, rfl⟩
def pD60 : Place ΓD60 ptrNat := .local ⟨⟨2, by decide⟩, rfl⟩
def qD60 : Place ΓD60 ptrNat := .local ⟨⟨3, by decide⟩, rfl⟩

/-- Positive: a copy whose DESTINATION is non-local — `*p := copy y`
    and `*p := copy *q`, the two-mother-lemma leaf
    (`copy_chaindst_chainsrc_simulation`, 2026-08-30): the source is
    lowered and READ, then the destination chain is lowered, then the
    store. -/
def d60_copy_into_deref_dst : IO Unit :=
  expectDiff ΓD60
    [.assign xD60 (.constInit 4),
     .assign yD60 (.constInit 7),
     .assign pD60 (.ref .Mut false [] xD60),
     .assign qD60 (.ref .Shared false [] yD60),
     .assign (.deref pD60) (.copy yD60),
     .assign (.deref pD60) (.copy (.deref qD60))]
    .ok "d60 copy into deref dst"

def sD61L := obseq.LayoutTy.TupL [natL, innerD50L]
def ΓD61 : Ctx := [sD61L, natL, natL, pairD52L]
def sD61 : Place ΓD61 sD61L := .local ⟨⟨0, by decide⟩, rfl⟩
def xD61 : Place ΓD61 natL := .local ⟨⟨1, by decide⟩, rfl⟩
def yD61 : Place ΓD61 natL := .local ⟨⟨2, by decide⟩, rfl⟩
def tD61 : Place ΓD61 pairD52L := .local ⟨⟨3, by decide⟩, rfl⟩

/-- Positive: a copy into a deref destination whose pointer place is a
    PROJ-OF-PROJ (`*(s.f.g) := copy x`) and out of a nested source —
    both places are flatten-normalized before the two-mother leaf sees
    them (the deref-dst flatten transfer, 2026-08-30). -/
def d61_copy_into_flattened_deref_dst : IO Unit :=
  expectDiff ΓD61
    [.assign xD61 (.constInit 5),
     .assign yD61 (.constInit 6),
     .assign (.proj (.proj sD61 (.field ⟨1, by decide⟩ .nil))
        (.field ⟨1, by decide⟩ .nil)) (.ref .Mut false [] xD61),
     .assign (.deref (.proj (.proj sD61 (.field ⟨1, by decide⟩ .nil))
        (.field ⟨1, by decide⟩ .nil))) (.copy yD61),
     .assign xD61 (.copy (.deref (.proj (.proj sD61 (.field ⟨1, by decide⟩ .nil))
        (.field ⟨1, by decide⟩ .nil))))]
    .ok "d61 copy into flattened deref dst"

def ΓD62 : Ctx := [obseq.LayoutTy.PtrL pairD52L, pairD52L, natL, natL]
def pD62 : Place ΓD62 (obseq.LayoutTy.PtrL pairD52L) := .local ⟨⟨0, by decide⟩, rfl⟩
def tD62 : Place ΓD62 pairD52L := .local ⟨⟨1, by decide⟩, rfl⟩
def yD62 : Place ΓD62 natL := .local ⟨⟨2, by decide⟩, rfl⟩
def zD62 : Place ΓD62 natL := .local ⟨⟨3, by decide⟩, rfl⟩

/-- Positive: a copy into a PROJECTED deref destination at ZERO offset
    (`(*p).0 := copy y`), then the read back. Closed 2026-08-30 by
    `copy_projdst_zero_chainsrc_simulation` through the recursive
    proj-dst dispatcher (`copy_projdst_simulation`). -/
def d62_copy_into_proj_deref_dst : IO Unit :=
  expectDiff ΓD62
    [.assign (.proj tD62 (.field ⟨0, by decide⟩ .nil)) (.constInit 1),
     .assign (.proj tD62 (.field ⟨1, by decide⟩ .nil)) (.constInit 2),
     .assign yD62 (.constInit 7),
     .assign pD62 (.ref .Mut false [] tD62),
     .assign (.proj (.deref pD62) (.field ⟨0, by decide⟩ .nil)) (.copy yD62),
     .assign zD62 (.copy (.proj tD62 (.field ⟨0, by decide⟩ .nil)))]
    .ok "d62 copy into proj deref dst"

/-- Positive: a copy into a PROJECTED deref destination at NONZERO
    offset (`(*p).1 := copy y`) — the projection's own `Borrow(Mut)`
    before the `RStore` and its `Die` after (the BRIDGE 1 endgame).
    Closed 2026-08-30 by `copy_projdst_offset_chainsrc_simulation`. -/
def d63_copy_into_proj_deref_dst_offset : IO Unit :=
  expectDiff ΓD62
    [.assign (.proj tD62 (.field ⟨0, by decide⟩ .nil)) (.constInit 1),
     .assign (.proj tD62 (.field ⟨1, by decide⟩ .nil)) (.constInit 2),
     .assign yD62 (.constInit 8),
     .assign pD62 (.ref .Mut false [] tD62),
     .assign (.proj (.deref pD62) (.field ⟨1, by decide⟩ .nil)) (.copy yD62),
     .assign zD62 (.copy (.proj tD62 (.field ⟨1, by decide⟩ .nil)))]
    .ok "d63 copy into proj deref dst at offset"

def ΓD64 : Ctx := [obseq.LayoutTy.PtrL natL, pairD52L, natL, natL]
def pD64 : Place ΓD64 (obseq.LayoutTy.PtrL natL) := .local ⟨⟨0, by decide⟩, rfl⟩
def tD64 : Place ΓD64 pairD52L := .local ⟨⟨1, by decide⟩, rfl⟩
def xD64 : Place ΓD64 natL := .local ⟨⟨2, by decide⟩, rfl⟩
def zD64 : Place ΓD64 natL := .local ⟨⟨3, by decide⟩, rfl⟩

/-- Positive: a copy whose SOURCE is proj-topped at ZERO offset under a
    deref destination (`*p := copy t.0`). Closed 2026-08-30 by
    `copy_chaindst_projsrc_zero_simulation` — the two-mother skeleton
    with the READ one projection layer deeper. -/
def d64_copy_projsrc_into_deref_dst : IO Unit :=
  expectDiff ΓD64
    [.assign (.proj tD64 (.field ⟨0, by decide⟩ .nil)) (.constInit 3),
     .assign (.proj tD64 (.field ⟨1, by decide⟩ .nil)) (.constInit 4),
     .assign xD64 (.constInit 0),
     .assign pD64 (.ref .Mut false [] xD64),
     .assign (.deref pD64) (.copy (.proj tD64 (.field ⟨0, by decide⟩ .nil))),
     .assign zD64 (.copy xD64)]
    .ok "d64 copy proj src into deref dst"

/-- Positive: a copy whose SOURCE is proj-topped at NONZERO offset
    under a deref destination (`*p := copy t.1`). The projection mints
    its own `Borrow(Shared)`, the copy loads through it, and the
    projection's cleanup `Die` retires it — all before the destination
    lowers, so BRIDGE 1S is contiguous. Closed 2026-08-30 by
    `copy_chaindst_projsrc_offset_simulation`. -/
def d65_copy_projsrc_offset_into_deref_dst : IO Unit :=
  expectDiff ΓD64
    [.assign (.proj tD64 (.field ⟨0, by decide⟩ .nil)) (.constInit 5),
     .assign (.proj tD64 (.field ⟨1, by decide⟩ .nil)) (.constInit 6),
     .assign xD64 (.constInit 0),
     .assign pD64 (.ref .Mut false [] xD64),
     .assign (.deref pD64) (.copy (.proj tD64 (.field ⟨1, by decide⟩ .nil))),
     .assign zD64 (.copy xD64)]
    .ok "d65 copy proj src at offset into deref dst"

/-- Positive: a copy into a PROJECTED destination over a BOUND LOCAL
    base, at ZERO offset (`t.0 := copy y`). Closed 2026-08-30 by
    generalizing `copy_projdst_zero_chainsrc_simulation` from a deref
    base to any canonical chain base — a bound local IS one
    (`PtrChain.base`). -/
def d66_copy_into_proj_local_dst : IO Unit :=
  expectDiff ΓD62
    [.assign (.proj tD62 (.field ⟨0, by decide⟩ .nil)) (.constInit 1),
     .assign (.proj tD62 (.field ⟨1, by decide⟩ .nil)) (.constInit 2),
     .assign yD62 (.constInit 7),
     .assign (.proj tD62 (.field ⟨0, by decide⟩ .nil)) (.copy yD62),
     .assign zD62 (.copy (.proj tD62 (.field ⟨0, by decide⟩ .nil)))]
    .ok "d66 copy into proj local dst"

/-- Positive: the same at NONZERO offset (`t.1 := copy y`) — the
    destination projection mints its own `Borrow(Mut)` before the
    `RStore` and kills it after. -/
def d67_copy_into_proj_local_dst_offset : IO Unit :=
  expectDiff ΓD62
    [.assign (.proj tD62 (.field ⟨0, by decide⟩ .nil)) (.constInit 1),
     .assign (.proj tD62 (.field ⟨1, by decide⟩ .nil)) (.constInit 2),
     .assign yD62 (.constInit 9),
     .assign (.proj tD62 (.field ⟨1, by decide⟩ .nil)) (.copy yD62),
     .assign zD62 (.copy (.proj tD62 (.field ⟨1, by decide⟩ .nil)))]
    .ok "d67 copy into proj local dst at offset"

def ΓD68 : Ctx := [pairD52L, natL, natL]
def tD68 : Place ΓD68 pairD52L := .local ⟨⟨0, by decide⟩, rfl⟩
def yD68 : Place ΓD68 natL := .local ⟨⟨1, by decide⟩, rfl⟩
def zD68 : Place ΓD68 natL := .local ⟨⟨2, by decide⟩, rfl⟩

/-- Positive: a copy into a PROJECTED destination whose LOCAL root is
    UNBOUND, at ZERO offset (`t.0 := copy y` with `t` fresh) — regime
    B-proj for copy. `ensurePlaceRoot` allocates the whole σ-sized root
    before the rhs pre-phase runs. Closed 2026-08-30 by
    `copy_projlocal_fresh_zero_simulation`. -/
def d68_copy_into_fresh_proj_local : IO Unit :=
  expectDiff ΓD68
    [.assign yD68 (.constInit 7),
     .assign (.proj tD68 (.field ⟨0, by decide⟩ .nil)) (.copy yD68),
     .assign zD68 (.copy (.proj tD68 (.field ⟨0, by decide⟩ .nil)))]
    .ok "d68 copy into fresh proj local"

/-- Positive: the same at NONZERO offset (`t.1 := copy y` with `t`
    fresh) — the root `Alloc`, the source read, then the fresh root
    register's own `Borrow(Mut)`/`RStore`/`Die` (BRIDGE 1). Closed
    2026-08-30 by `copy_projlocal_fresh_offset_simulation`. -/
def d69_copy_into_fresh_proj_local_offset : IO Unit :=
  expectDiff ΓD68
    [.assign yD68 (.constInit 8),
     .assign (.proj tD68 (.field ⟨1, by decide⟩ .nil)) (.copy yD68),
     .assign zD68 (.copy (.proj tD68 (.field ⟨1, by decide⟩ .nil)))]
    .ok "d69 copy into fresh proj local at offset"

/-- Positive: a PROJ-TOPPED source at ZERO offset under a PROJECTED
    destination (`(*p).1 := copy t.0`). Closed 2026-08-30 by the
    `LoweringSim` package: a zero-offset projection over a chain
    supplies the same source-lowering package a chain does
    (`LoweringSimAny.projZero`), so the projected-destination leaves
    accept it unchanged. -/
def d70_projsrc_zero_into_proj_dst : IO Unit :=
  expectDiff ΓD62
    [.assign (.proj tD62 (.field ⟨0, by decide⟩ .nil)) (.constInit 4),
     .assign (.proj tD62 (.field ⟨1, by decide⟩ .nil)) (.constInit 5),
     .assign pD62 (.ref .Mut false [] tD62),
     .assign (.proj (.deref pD62) (.field ⟨1, by decide⟩ .nil))
       (.copy (.proj tD62 (.field ⟨0, by decide⟩ .nil))),
     .assign zD62 (.copy (.proj tD62 (.field ⟨1, by decide⟩ .nil)))]
    .ok "d70 proj src at zero into proj dst"

/-- The same over a LOCAL destination base (`t.0 := copy s.0`), which
    goes through the bound-root branch of the same dispatcher. -/
def d71_projsrc_zero_into_proj_local : IO Unit :=
  expectDiff ΓD64
    [.assign (.proj tD64 (.field ⟨0, by decide⟩ .nil)) (.constInit 6),
     .assign (.proj tD64 (.field ⟨1, by decide⟩ .nil)) (.constInit 7),
     .assign (.proj tD64 (.field ⟨1, by decide⟩ .nil))
       (.copy (.proj tD64 (.field ⟨0, by decide⟩ .nil))),
     .assign zD64 (.copy (.proj tD64 (.field ⟨1, by decide⟩ .nil)))]
    .ok "d71 proj src at zero into proj local"

def ΓD72 : Ctx := [pairD52L, pairD52L, natL]
def tD72 : Place ΓD72 pairD52L := .local ⟨⟨0, by decide⟩, rfl⟩
def sD72 : Place ΓD72 pairD52L := .local ⟨⟨1, by decide⟩, rfl⟩
def zD72 : Place ΓD72 natL := .local ⟨⟨2, by decide⟩, rfl⟩

/-- Positive: a PROJ-TOPPED source at NONZERO offset into a PROJECTED
    destination over a BOUND local base, itself at nonzero offset
    (`t.1 := copy s.1`). Both projections mint their own borrow: the
    source's `Borrow(Shared)` retires in the rhs pre-phase (BRIDGE 1S)
    before the destination's `Borrow(Mut)` is taken (BRIDGE 1), so the
    two never interleave. Closed 2026-08-31 by
    `copy_projdst_offset_projsrc_offset_simulation`. -/
def d72_projsrc_offset_into_proj_dst_offset : IO Unit :=
  expectDiff ΓD72
    [.assign (.proj sD72 (.field ⟨0, by decide⟩ .nil)) (.constInit 3),
     .assign (.proj sD72 (.field ⟨1, by decide⟩ .nil)) (.constInit 4),
     .assign (.proj tD72 (.field ⟨0, by decide⟩ .nil)) (.constInit 0),
     .assign (.proj tD72 (.field ⟨1, by decide⟩ .nil))
       (.copy (.proj sD72 (.field ⟨1, by decide⟩ .nil))),
     .assign zD72 (.copy (.proj tD72 (.field ⟨1, by decide⟩ .nil)))]
    .ok "d72 proj src at offset into proj dst at offset"

/-- Positive: the same with an UNBOUND destination root at ZERO
    destination offset (`t.0 := copy s.1`, `t` fresh) — regime B-proj
    with a BRIDGE 1S source. Closed 2026-08-31 by
    `copy_projlocal_fresh_projsrc_offset_zero_simulation`. -/
def d73_projsrc_offset_into_fresh_proj_zero : IO Unit :=
  expectDiff ΓD72
    [.assign (.proj sD72 (.field ⟨0, by decide⟩ .nil)) (.constInit 5),
     .assign (.proj sD72 (.field ⟨1, by decide⟩ .nil)) (.constInit 6),
     .assign (.proj tD72 (.field ⟨0, by decide⟩ .nil))
       (.copy (.proj sD72 (.field ⟨1, by decide⟩ .nil))),
     .assign zD72 (.copy (.proj tD72 (.field ⟨0, by decide⟩ .nil)))]
    .ok "d73 proj src at offset into fresh proj dst at zero"

/-- Positive: and with an UNBOUND root at NONZERO destination offset
    (`t.1 := copy s.1`, `t` fresh) — the root `Alloc`, BRIDGE 1S on the
    source, then BRIDGE 1 through the fresh root register. Closed
    2026-08-31 by
    `copy_projlocal_fresh_projsrc_offset_offset_simulation`; with it
    `copy_place_residual` is deleted. -/
def d74_projsrc_offset_into_fresh_proj_offset : IO Unit :=
  expectDiff ΓD72
    [.assign (.proj sD72 (.field ⟨0, by decide⟩ .nil)) (.constInit 7),
     .assign (.proj sD72 (.field ⟨1, by decide⟩ .nil)) (.constInit 8),
     .assign (.proj tD72 (.field ⟨1, by decide⟩ .nil))
       (.copy (.proj sD72 (.field ⟨1, by decide⟩ .nil))),
     .assign zD72 (.copy (.proj tD72 (.field ⟨1, by decide⟩ .nil)))]
    .ok "d74 proj src at offset into fresh proj dst at offset"

def ΓD75 : Ctx :=
  [pairD52L, obseq.LayoutTy.PtrL (obseq.LayoutTy.PtrL natL),
   obseq.LayoutTy.PtrL natL, obseq.LayoutTy.PtrL natL, natL, natL]
def tD75 : Place ΓD75 pairD52L := .local ⟨⟨0, by decide⟩, rfl⟩
def pD75 : Place ΓD75 (obseq.LayoutTy.PtrL (obseq.LayoutTy.PtrL natL)) :=
  .local ⟨⟨1, by decide⟩, rfl⟩
def qD75 : Place ΓD75 (obseq.LayoutTy.PtrL natL) := .local ⟨⟨2, by decide⟩, rfl⟩
def rD75 : Place ΓD75 (obseq.LayoutTy.PtrL natL) := .local ⟨⟨3, by decide⟩, rfl⟩
def xD75 : Place ΓD75 natL := .local ⟨⟨4, by decide⟩, rfl⟩
def zD75 : Place ΓD75 natL := .local ⟨⟨5, by decide⟩, rfl⟩

/-- Positive: a REF whose source is proj-topped at NONZERO offset under
    a DEREF destination (`*p := &mut t.1`). The projection is folded
    into the `Borrow`'s offset operand rather than minting its own
    borrow, so the whole rhs is one instruction and the destination
    chain lowers after it. `r := &mut t.0` stays live across the
    statement: the two fields are disjoint ranges, so the new borrow
    must not pop `r`, and `*r := 9` afterwards is well-defined exactly
    when the compiler used offset `1`. Closed 2026-08-31 by
    `ref_derefdst_projsrc_simulation`. -/
def d75_ref_projsrc_offset_into_deref_dst : IO Unit :=
  expectDiff ΓD75
    [.assign (.proj tD75 (.field ⟨0, by decide⟩ .nil)) (.constInit 3),
     .assign (.proj tD75 (.field ⟨1, by decide⟩ .nil)) (.constInit 4),
     .assign xD75 (.constInit 0),
     .assign qD75 (.ref .Mut false [] xD75),
     .assign pD75 (.ref .Mut false [] qD75),
     .assign rD75 (.ref .Mut false [] (.proj tD75 (.field ⟨0, by decide⟩ .nil))),
     .assign (.deref pD75)
       (.ref .Mut false [] (.proj tD75 (.field ⟨1, by decide⟩ .nil))),
     .assign (.deref rD75) (.constInit 9),
     .assign zD75 (.copy (.proj tD75 (.field ⟨0, by decide⟩ .nil)))]
    .ok "d75 ref proj src at offset into deref dst"

def ΓD76 : Ctx :=
  [pairD52L, obseq.LayoutTy.PtrL natL, obseq.LayoutTy.PtrL natL, natL]
def sD76 : Place ΓD76 pairD52L := .local ⟨⟨0, by decide⟩, rfl⟩
def tD76 : Place ΓD76 (obseq.LayoutTy.PtrL natL) := .local ⟨⟨1, by decide⟩, rfl⟩
def rD76 : Place ΓD76 (obseq.LayoutTy.PtrL natL) := .local ⟨⟨2, by decide⟩, rfl⟩
def zD76 : Place ΓD76 natL := .local ⟨⟨3, by decide⟩, rfl⟩

/-- Positive: REGIME B-proj of ref — a reference to a FIELD stored into
    an UNBOUND destination root (`t := &mut s.1`, `t` never assigned
    before). `preparePlaceAssign` allocates on the mirlite side and
    `ensureLocalRegE` emits the matching `Alloc`, so the fragment is
    `Alloc; Borrow; RStore` and the borrow's OFFSET operand carries the
    projection. `r := &mut s.0` stays live across the statement: the
    fields are disjoint ranges, so `*r := 9` afterwards is defined
    exactly when the borrow used offset `1`. Closed 2026-08-31 by
    `ref_fresh_projsrc_simulation`. -/
def d76_ref_projsrc_into_fresh_dst : IO Unit :=
  expectDiff ΓD76
    [.assign (.proj sD76 (.field ⟨0, by decide⟩ .nil)) (.constInit 3),
     .assign (.proj sD76 (.field ⟨1, by decide⟩ .nil)) (.constInit 4),
     .assign rD76 (.ref .Mut false [] (.proj sD76 (.field ⟨0, by decide⟩ .nil))),
     .assign tD76 (.ref .Mut false [] (.proj sD76 (.field ⟨1, by decide⟩ .nil))),
     .assign (.deref rD76) (.constInit 9),
     .assign (.deref tD76) (.constInit 7),
     .assign zD76 (.copy (.proj sD76 (.field ⟨1, by decide⟩ .nil)))]
    .ok "d76 ref proj src into fresh dst"

def ptrPairD77L := obseq.LayoutTy.TupL [ptrNat, ptrNat]
def ΓD77 : Ctx := [ptrPairD77L, natL, natL, natL]
def tD77 : Place ΓD77 ptrPairD77L := .local ⟨⟨0, by decide⟩, rfl⟩
def xD77 : Place ΓD77 natL := .local ⟨⟨1, by decide⟩, rfl⟩
def yD77 : Place ΓD77 natL := .local ⟨⟨2, by decide⟩, rfl⟩
def zD77 : Place ΓD77 natL := .local ⟨⟨3, by decide⟩, rfl⟩

/-- Positive: REGIME B-proj for the DESTINATION — a reference stored
    into a FIELD of an UNBOUND root at ZERO offset (`t.0 := &mut x`,
    `t` never assigned before). `preparePlaceAssign` runs `allocateRoot`
    for the WHOLE tuple and `ensurePlaceRoot` emits the matching
    σ-sized `Alloc`; ρa extends by the identity over that entire block,
    not at a single cell. `t.1 := &mut y` afterwards exercises the
    second field, which is in bounds only if the root really was
    allocated at the tuple's size. Retargeting the first borrow to `y`
    makes the two fields alias, and `*(t.0) := 9` then reads a popped
    tag. Closed 2026-08-31 by `ref_projzero_fresh_simulation`. -/
def d77_ref_into_fresh_proj_zero : IO Unit :=
  expectDiff ΓD77
    [.assign xD77 (.constInit 5),
     .assign yD77 (.constInit 6),
     .assign (.proj tD77 (.field ⟨0, by decide⟩ .nil)) (.ref .Mut false [] xD77),
     .assign (.proj tD77 (.field ⟨1, by decide⟩ .nil)) (.ref .Mut false [] yD77),
     .assign (.deref (.proj tD77 (.field ⟨0, by decide⟩ .nil))) (.constInit 9),
     .assign (.deref (.proj tD77 (.field ⟨1, by decide⟩ .nil))) (.constInit 8),
     .assign zD77 (.copy xD77)]
    .ok "d77 ref into fresh proj dst at zero"

/-- Positive: the same regime at NONZERO offset (`t.1 := &mut x`, `t`
    never assigned before). The projection now mints its own interior
    `Borrow(Mut)` into the freshly allocated root register and retires
    it with a `Die` — BRIDGE 1 collapses that triple to mirlite's single
    parent write, so the fragment is five instructions. `t.0 := &mut y`
    afterwards is in bounds only if the root was allocated at the
    tuple's size. Closed 2026-08-31 by
    `ref_projoffset_fresh_simulation`. -/
def d78_ref_into_fresh_proj_offset : IO Unit :=
  expectDiff ΓD77
    [.assign xD77 (.constInit 5),
     .assign yD77 (.constInit 6),
     .assign (.proj tD77 (.field ⟨1, by decide⟩ .nil)) (.ref .Mut false [] xD77),
     .assign (.proj tD77 (.field ⟨0, by decide⟩ .nil)) (.ref .Mut false [] yD77),
     .assign (.deref (.proj tD77 (.field ⟨1, by decide⟩ .nil))) (.constInit 9),
     .assign (.deref (.proj tD77 (.field ⟨0, by decide⟩ .nil))) (.constInit 8),
     .assign zD77 (.copy xD77)]
    .ok "d78 ref into fresh proj dst at offset"

def ΓD79 : Ctx := [ptrNat, ptrNat, ptrNat, natL, natL, natL]
def tD79 : Place ΓD79 ptrNat := .local ⟨⟨0, by decide⟩, rfl⟩
def rD79 : Place ΓD79 ptrNat := .local ⟨⟨1, by decide⟩, rfl⟩
def sD79 : Place ΓD79 ptrNat := .local ⟨⟨2, by decide⟩, rfl⟩
def xD79 : Place ΓD79 natL := .local ⟨⟨3, by decide⟩, rfl⟩
def yD79 : Place ΓD79 natL := .local ⟨⟨4, by decide⟩, rfl⟩
def zD79 : Place ΓD79 natL := .local ⟨⟨5, by decide⟩, rfl⟩

/-- Positive: REGIME B of ref with a DEREF SOURCE — a reborrow through
    a pointer chain stored into an UNBOUND destination
    (`t := &mut *r`, `t` never assigned before). The root `Alloc` comes
    FIRST, so the source spine lowers from the post-`Alloc` states and
    the mother lemma's whole hypothesis bundle has to hold there.
    `s := &mut y` stays live across the statement: reborrowing through
    `r` touches only `x`, so `*s := 8` afterwards is defined. Point the
    reborrow at `*s` instead and it becomes a child of `s`, which the
    later write through `s` pops — then `*t := 9` is UB. Closed
    2026-08-31 by `ref_fresh_derefsrc_simulation`. -/
def d79_ref_derefsrc_into_fresh_dst : IO Unit :=
  expectDiff ΓD79
    [.assign xD79 (.constInit 5),
     .assign yD79 (.constInit 6),
     .assign rD79 (.ref .Mut false [] xD79),
     .assign sD79 (.ref .Mut false [] yD79),
     .assign tD79 (.ref .Mut false [] (.deref rD79)),
     .assign (.deref sD79) (.constInit 8),
     .assign (.deref tD79) (.constInit 9),
     .assign zD79 (.copy xD79)]
    .ok "d79 ref deref src into fresh dst"

def allTests : List (IO Unit) := [
  g1_const_fresh_local,
  g2_protected_masked_ref,
  g3_deref_destination,
  g4_field_offsets_and_die,
  g5_compiler_total,
  g6_protector_frame,
  g7_uninit_undef_store,
  g8_heap_alloc,
  g9_dealloc,
  g10_expose_addr,
  g11_assign_if_skip,
  g12_ptr_offset_prescaled,
  g13_ref_slice,
  d1_owner_read_pops_mut,
  d2_deref_roundtrip,
  d3_field_borrow,
  d4_owner_field_write_pops,
  d5_disjoint_field_borrows,
  d6_tuple_copy,
  d7_protected_pop_is_ub,
  d8_pop_after_frame_ok,
  d9_uninit_materialize,
  d10_heap_lifecycle,
  d11_use_after_free,
  d12_double_free,
  d13_dynamic_alloc_len,
  d14_expose_roundtrip,
  d15_exposed_then_invalidated,
  d16_assign_if_taken,
  d17_assign_if_skipped_suppresses_events,
  d18_assign_if_body_ub,
  d19_ptr_cast_roundtrip,
  d20_cast_then_offset_into_pair,
  d21_offset_before_base,
  d22_ref_slice_write,
  d23_ref_slice_pops,
  d24_deref_read_alignment,
  d25_deref_oob_alignment,
  d26_nested_proj_sibling,
  d27_split_field_borrows,
  d28_parent_write_cellwise,
  d29_parent_write_kills_overlap,
  d30_reborrow_through_pointer,
  d31_zst_reborrow,
  d32_field_copy_zero_offset,
  d33_overlap_junk_copy_agrees,
  d34_deref_dst_temp_killed_by_rhs_spine,
  d35_self_copy_is_ok,
  d36_field_copy_nonzero_offset,
  d37_copy_through_pointer,
  d38_nested_proj_write,
  d39_deref_field_zero_write,
  d40_ref_into_field_zero,
  d41_ref_into_field_offset,
  d42_ref_into_nested_field,
  d43_ref_through_loaded_ptr,
  d44_write_through_ptr_field_chain,
  d45_ref_through_ptr_field_chain,
  d46_write_through_deref_struct_field,
  d47_copy_through_ptr_field,
  d48_ref_through_ptr_field_dst,
  d49_ref_of_deref_ptr_field,
  d50_write_through_nested_ptr_field,
  d51_copy_ref_through_nested_ptr_field,
  d52_proj_write_through_chain,
  d53_proj_write_through_flattened_ptr,
  d54_fresh_root_proj_writes,
  d55_copy_from_proj_over_chain,
  d56_copy_from_nested_proj,
  d57_copy_into_fresh_local,
  d58_copy_field_into_fresh_local,
  d59_copy_read_precedes_dst_chain,
  d60_copy_into_deref_dst,
  d61_copy_into_flattened_deref_dst,
  d62_copy_into_proj_deref_dst,
  d63_copy_into_proj_deref_dst_offset,
  d64_copy_projsrc_into_deref_dst,
  d65_copy_projsrc_offset_into_deref_dst,
  d66_copy_into_proj_local_dst,
  d67_copy_into_proj_local_dst_offset,
  d68_copy_into_fresh_proj_local,
  d69_copy_into_fresh_proj_local_offset,
  d70_projsrc_zero_into_proj_dst,
  d71_projsrc_zero_into_proj_local,
  d72_projsrc_offset_into_proj_dst_offset,
  d73_projsrc_offset_into_fresh_proj_zero,
  d74_projsrc_offset_into_fresh_proj_offset,
  d75_ref_projsrc_offset_into_deref_dst,
  d76_ref_projsrc_into_fresh_dst,
  d77_ref_into_fresh_proj_zero,
  d78_ref_into_fresh_proj_offset,
  d79_ref_derefsrc_into_fresh_dst]

def runAll : IO Unit := do
  allTests.forM id
  IO.println s!"obseq3 compiler tests passed ({allTests.length}/{allTests.length})"

end obseq3.CompileTests
