import obseq3.syntax
import obseq3.oseair
import obseq3.mirlite

/-!
# The compiler: mirlite → OSEA-IR

Parameterized by the layout table `L : mirlite.LayEnv Γ` the source
(`mirlite.lean`) runs on; every unit in the emitted code is a byte:

- a local's `Alloc` carries its byte layout `L loc.idx`;
- a projection's `Borrow` offset is the field's byte offset
  (`fieldOffset (placeLayout L base) path.indices`, the source's
  `resolvePlace`), and every borrow and `Die` length is the place's byte
  size `(placeLayout L p).size`;
- loads carry the source place's layout, stores the DESTINATION's (the
  source's `evalRExpr` gets `dstL`): a copy between different
  layouts fails at the store's leaf check in both machines;
- a `ref`'s freeze mask is expanded to bytes (`maskBytes`); a `move`'s
  is `[]`, as in the source;
- `ptrOffset`'s stride, `sliceLen`'s and `subSlice`'s element size are
  the pointee layout's byte size, and the one-leaf reads
  (`exposeAddr`/`fromExposed`/`ptrOffset`/`ptrCast`/`refSlice`) carry the
  source's `leafKind`.
-/

namespace obseq3.compile

open obseq3.oseair (Register Val)
open obseq3.oseair (Instr Rhs)
open obseq3.bytes (BLayout Scalar)
open obseq3.mirlite (LayEnv placeLayout fieldOffset leafKind maskBytes pointeeLayout)

abbrev TargetProg := obseq3.oseair.Prog
abbrev PlaceInfo := Register × LayoutTy
abbrev PlaceRegMap := List (Nat × PlaceInfo)

structure CompilerState where
  nextReg   : Nat
  nextLabel : Nat
  code      : Nat → Option Instr
  placeRegMap : PlaceRegMap
deriving Inhabited

/-- The compiler state only grows: counters are monotone, and generated code below the
    old `nextLabel` is preserved. This is the CompCert-style `state_incr` witness. -/
structure StateIncr (s1 s2 : CompilerState) : Prop where
  nextLabel_le : s1.nextLabel ≤ s2.nextLabel
  nextReg_le   : s1.nextReg ≤ s2.nextReg
  code_eq      : ∀ label, label < s1.nextLabel → s2.code label = s1.code label
  placeRegMap_mono :
    ∀ idx info, (idx, info) ∈ s1.placeRegMap → (idx, info) ∈ s2.placeRegMap

namespace StateIncr

theorem refl (cs : CompilerState) : StateIncr cs cs :=
  ⟨Nat.le_refl _, Nat.le_refl _, fun _ _ => rfl, fun _ _ h => h⟩

theorem trans {s1 s2 s3 : CompilerState}
    (h12 : StateIncr s1 s2) (h23 : StateIncr s2 s3) : StateIncr s1 s3 :=
  ⟨Nat.le_trans h12.nextLabel_le h23.nextLabel_le,
   Nat.le_trans h12.nextReg_le h23.nextReg_le,
   fun label h_label =>
     (h23.code_eq label (Nat.lt_of_lt_of_le h_label h12.nextLabel_le)).trans
       (h12.code_eq label h_label),
   fun idx info h_idx =>
     h23.placeRegMap_mono idx info (h12.placeRegMap_mono idx info h_idx)⟩

end StateIncr

/-- Compiler computations thread `CompilerState` and carry a proof that state only grows. -/
abbrev CompilerM (α : Type) : Type :=
  (cs : CompilerState) → α × { cs' : CompilerState // StateIncr cs cs' }

instance : Monad CompilerM where
  pure a := fun cs => (a, ⟨cs, StateIncr.refl cs⟩)
  bind m f := fun cs =>
    let r1 := m cs
    let r2 := f r1.1 r1.2.1
    (r2.1, ⟨r2.2.1, StateIncr.trans r1.2.2 r2.2.2⟩)

namespace CompilerM

/-- Extract the value produced by a `CompilerM` computation. -/
def value (m : CompilerM α) (cs : CompilerState) : α :=
  (m cs).1

/-- Extract the resulting `CompilerState` from a `CompilerM` computation. -/
def run (m : CompilerM α) (cs : CompilerState) : CompilerState :=
  (m cs).2.1

theorem incr (m : CompilerM α) (cs : CompilerState) :
    StateIncr cs (run m cs) :=
  (m cs).2.2

@[simp] theorem run_pure (a : α) (cs : CompilerState) :
    run (pure a : CompilerM α) cs = cs :=
  rfl

@[simp] theorem value_pure (a : α) (cs : CompilerState) :
    value (pure a : CompilerM α) cs = a :=
  rfl

@[simp] theorem run_bind (m : CompilerM α) (f : α → CompilerM β) (cs : CompilerState) :
    run (m >>= f) cs = run (f (value m cs)) (run m cs) :=
  rfl

@[simp] theorem value_bind (m : CompilerM α) (f : α → CompilerM β) (cs : CompilerState) :
    value (m >>= f) cs = value (f (value m cs)) (run m cs) :=
  rfl

end CompilerM

/-- Result of an address computation. `cleanup` pairs each compiler-minted
    borrow register with the static length of its borrow, for `Die`. -/
structure PtrResult where
  reg : Register
  cleanup : List (Register × Nat)
deriving Inhabited

structure RExprResult where
  reg : Register
deriving Inhabited

/-- Result of a compiler computation paired with proof evidence indexed by the
    exact returned value. -/
structure ResultWithEvidence (α : Type) (Ev : α → Type) where
  result : α
  evidence : Ev result

inductive CompilerError where
  | missingLocal (idx : Nat)
  | unsupported (what : String)
deriving Inhabited, Repr, DecidableEq

/-- Checked compiler computations may reject invalid lowering cases while still
    threading monotone compiler state. -/
structure CheckedCompilerM (α : Type) where
  toCompilerM : CompilerM (Except CompilerError α)

namespace CheckedCompilerM

def value (m : CheckedCompilerM α) (cs : CompilerState) : Except CompilerError α :=
  CompilerM.value m.toCompilerM cs

def run (m : CheckedCompilerM α) (cs : CompilerState) : CompilerState :=
  CompilerM.run m.toCompilerM cs

theorem incr (m : CheckedCompilerM α) (cs : CompilerState) :
    StateIncr cs (run m cs) :=
  CompilerM.incr m.toCompilerM cs

instance : Monad CheckedCompilerM where
  pure a := ⟨pure (.ok a)⟩
  bind m f := ⟨do
    match ← m.toCompilerM with
    | .error err =>
        pure (.error err)
    | .ok a =>
        (f a).toCompilerM
  ⟩

def throw (err : CompilerError) : CheckedCompilerM α :=
  ⟨pure (.error err)⟩

def lift (m : CompilerM α) : CheckedCompilerM α :=
  ⟨do
    let a ← m
    pure (.ok a)
  ⟩

@[simp] theorem value_pure (a : α) (cs : CompilerState) :
    value (pure a : CheckedCompilerM α) cs = Except.ok a :=
  rfl

@[simp] theorem run_pure (a : α) (cs : CompilerState) :
    run (pure a : CheckedCompilerM α) cs = cs :=
  rfl

@[simp] theorem value_bind (m : CheckedCompilerM α) (f : α → CheckedCompilerM β)
    (cs : CompilerState) :
    value (m >>= f) cs =
      match value m cs with
      | .ok a => value (f a) (run m cs)
      | .error err => .error err := by
  change CompilerM.value
      (do
        match ← m.toCompilerM with
        | .error err => pure (.error err)
        | .ok a => (f a).toCompilerM) cs = _
  rw [CompilerM.value_bind]
  cases h : CompilerM.value m.toCompilerM cs <;> simp [CheckedCompilerM.value, CheckedCompilerM.run, h]

@[simp] theorem run_bind (m : CheckedCompilerM α) (f : α → CheckedCompilerM β)
    (cs : CompilerState) :
    run (m >>= f) cs =
      match value m cs with
      | .ok a => run (f a) (run m cs)
      | .error _ => run m cs := by
  change CompilerM.run
      (do
        match ← m.toCompilerM with
        | .error err => pure (.error err)
        | .ok a => (f a).toCompilerM) cs = _
  rw [CompilerM.run_bind]
  cases h : CompilerM.value m.toCompilerM cs <;> simp [CheckedCompilerM.value, CheckedCompilerM.run, h]

@[simp] theorem value_lift (m : CompilerM α) (cs : CompilerState) :
    value (lift m) cs = Except.ok (CompilerM.value m cs) := by
  simp [lift, CheckedCompilerM.value, CompilerM.value_bind]

@[simp] theorem run_lift (m : CompilerM α) (cs : CompilerState) :
    run (lift m) cs = CompilerM.run m cs := by
  simp [lift, CheckedCompilerM.run, CompilerM.run_bind]

end CheckedCompilerM

abbrev CheckedEvidenceM (α : Type) (Ev : α → Type) : Type :=
  CheckedCompilerM (ResultWithEvidence α Ev)

def emit (cs : CompilerState) (instrs : List Instr) : CompilerState :=
  let n := instrs.length
  { cs with
    nextLabel := cs.nextLabel + n,
    code      := fun label =>
      if cs.nextLabel ≤ label ∧ label < cs.nextLabel + n then
        instrs.get? (label - cs.nextLabel)
      else
        cs.code label }

theorem emit_code_lt_nextLabel
    (cs : CompilerState) (instrs : List Instr) {label : Nat}
    (h : label < cs.nextLabel) :
    (emit cs instrs).code label = cs.code label := by
  simp [emit, Nat.not_le_of_gt h]

theorem emit_code_at_new
    (cs : CompilerState) (instrs : List Instr) {k : Nat}
    (h : k < instrs.length) :
    (emit cs instrs).code (cs.nextLabel + k) = instrs.get? k := by
  simp [emit, Nat.le_add_right, Nat.add_lt_add_left h]

/-- Emitting MORE at the same point only extends: everything the shorter
    emission laid down is still at the same label. This is what lets a
    fragment lemma written for `[…]` be applied when the compiler in fact
    emitted `[…] ++ post` — the `refSlice` split's extra mint instruction
    sits strictly above the bracket the lemma reasons about. -/
theorem emit_append_state_incr (cs : CompilerState) (l1 l2 : List Instr) :
    StateIncr (emit cs l1) (emit cs (l1 ++ l2)) := by
  refine ⟨by simp [emit], by simp [emit], ?_, fun _ _ h => h⟩
  intro label h_label
  simp only [emit] at h_label ⊢
  by_cases h_lo : cs.nextLabel ≤ label
  · have h_hi : label - cs.nextLabel < l1.length := by omega
    rw [if_pos ⟨h_lo, by simp only [List.length_append]; omega⟩,
      if_pos ⟨h_lo, by omega⟩]
    exact List.getElem?_append_left h_hi
  · rw [if_neg (by omega), if_neg (by omega)]

theorem emit_nextLabel_ge
    (cs : CompilerState) (instrs : List Instr) :
    cs.nextLabel ≤ (emit cs instrs).nextLabel := by
  simp [emit]

theorem emit_state_incr (cs : CompilerState) (instrs : List Instr) :
    StateIncr cs (emit cs instrs) :=
  ⟨emit_nextLabel_ge cs instrs, Nat.le_refl _,
   fun label h_label => @emit_code_lt_nextLabel cs instrs label h_label,
   fun _ _ h => h⟩

def emitM (instrs : List Instr) : CompilerM Unit :=
  fun cs => ((), ⟨emit cs instrs, emit_state_incr cs instrs⟩)

def freshReg (cs : CompilerState) : Register × CompilerState :=
  (Register.R cs.nextReg, { cs with nextReg := cs.nextReg + 1 })

theorem freshReg_state_incr (cs : CompilerState) :
    StateIncr cs (freshReg cs).2 :=
  ⟨Nat.le_refl _, Nat.le_succ _, fun _ _ => rfl, fun _ _ h => h⟩

def freshRegM : CompilerM Register :=
  fun cs =>
    let r := freshReg cs
    (r.1, ⟨r.2, freshReg_state_incr cs⟩)

def cleanupInstrs (regs : List (Register × Nat)) : List Instr :=
  regs.reverse.map (fun (r, len) => Instr.Die r len)

def getPlaceInfo (cs : CompilerState) (idx : Nat) : Option PlaceInfo :=
  cs.placeRegMap.lookup idx

def setPlaceInfo (cs : CompilerState) (idx : Nat) (info : PlaceInfo) : CompilerState :=
  { cs with placeRegMap := (idx, info) :: cs.placeRegMap }

theorem setPlaceInfo_state_incr (cs : CompilerState) (idx : Nat) (info : PlaceInfo) :
    StateIncr cs (setPlaceInfo cs idx info) :=
  ⟨Nat.le_refl _, Nat.le_refl _, fun _ _ => rfl,
   fun _ _ h => List.mem_cons_of_mem (idx, info) h⟩


/-- The layout of a one-leaf read at scalar `k`: what the source's
    `readCell` reads. -/
def leafLayout : Scalar → BLayout
  | .int n => .int n
  | .ptr => .ptr default

inductive EnsureLocalEvidence {Γ : Ctx} {τ : LayoutTy}
    (loc : Local Γ τ) : PtrResult → Type where
  | existing
      (cs : CompilerState) (reg : Register) (layout : LayoutTy)
      (h_lookup : getPlaceInfo cs loc.idx.1 = some (reg, layout)) :
      EnsureLocalEvidence loc { reg := reg, cleanup := [] }
  | fresh
      (cs : CompilerState) (reg : Register)
      (h_lookup : getPlaceInfo cs loc.idx.1 = none)
      (h_reg : reg = Register.R cs.nextReg) :
      EnsureLocalEvidence loc { reg := reg, cleanup := [] }

def ensureLocalRegE {Γ : Ctx} (L : LayEnv Γ) {τ : LayoutTy}
    (loc : Local Γ τ) :
    CompilerM (ResultWithEvidence PtrResult (EnsureLocalEvidence loc)) :=
  fun cs =>
    match h_lookup : getPlaceInfo cs loc.idx.1 with
    | some (reg, _) =>
        ({ result := { reg := reg, cleanup := [] },
           evidence := EnsureLocalEvidence.existing cs reg _ h_lookup },
          ⟨cs, StateIncr.refl cs⟩)
    | none =>
        let fr := freshReg cs
        let reg := fr.1
        let cs1 := fr.2
        let cs2 := emit cs1 [Instr.Assgn reg (Rhs.Alloc (L loc.idx))]
        let cs3 := setPlaceInfo cs2 loc.idx.1 (reg, τ)
        ({ result := { reg := reg, cleanup := [] },
           evidence := EnsureLocalEvidence.fresh cs reg h_lookup rfl },
          ⟨cs3,
            (freshReg_state_incr cs).trans
              ((emit_state_incr cs1 [Instr.Assgn reg (Rhs.Alloc (L loc.idx))]).trans
                (setPlaceInfo_state_incr cs2 loc.idx.1 (reg, τ)))⟩)

/-- A projection's byte offset: the source's `resolvePlace`. -/
abbrev pathOffset {Γ : Ctx} (L : LayEnv Γ) {σ τ : LayoutTy} (base : Place Γ σ)
    (p : PathTo σ τ) : Nat :=
  fieldOffset (placeLayout L base) p.indices

/-- A place's byte size: every borrow's and `Die`'s length. -/
abbrev placeSize {Γ : Ctx} (L : LayEnv Γ) {τ : LayoutTy} (p : Place Γ τ) : Nat :=
  (placeLayout L p).size

def ensurePlaceRoot {Γ : Ctx} (L : LayEnv Γ) : {τ : LayoutTy} → Place Γ τ → CompilerM Unit
  | _, .local loc => do
      let _ ← ensureLocalRegE L loc
      pure ()
  | _, .proj base _ => ensurePlaceRoot L base
  | _, .deref ptrPlace => ensurePlaceRoot L ptrPlace

def borrowRhs (kind : RefKind) (lenB : Nat) (base : Register) (offsetB : Nat) : Rhs :=
  Rhs.Borrow kind false [] (some lenB) base offsetB

/-- The pointer a deref place loads: one pointer leaf. -/
abbrev derefLoad {Γ : Ctx} (L : LayEnv Γ) {σ : LayoutTy}
    (ptrPlace : Place Γ (LayoutTy.PtrL σ)) : BLayout :=
  .ptr (placeLayout L (.deref ptrPlace))

inductive PlaceToRegEvidence {Γ : Ctx} (L : LayEnv Γ) :
    RefKind → {τ : LayoutTy} → Place Γ τ → PtrResult → Type where
  | local
      {τ : LayoutTy} (loc : Local Γ τ) (cs : CompilerState)
      (reg : Register) (layout : LayoutTy)
      (h_lookup : getPlaceInfo cs loc.idx.1 = some (reg, layout)) :
      PlaceToRegEvidence L kind (.local loc) { reg := reg, cleanup := [] }
  | projAssoc
      {ρ σ τ : LayoutTy} (b : Place Γ ρ) (q : PathTo ρ σ) (p : PathTo σ τ)
      (res : PtrResult)
      (ev : PlaceToRegEvidence L kind (.proj b (q.append p)) res) :
      PlaceToRegEvidence L kind (.proj (.proj b q) p) res
  | projZero
      {σ τ : LayoutTy} (base : Place Γ σ) (path : PathTo σ τ)
      (baseRes : PtrResult)
      (baseEv : PlaceToRegEvidence L kind base baseRes)
      (h_offset : pathOffset L base path = 0) :
      PlaceToRegEvidence L kind (.proj base path) baseRes
  | projOffset
      {σ τ : LayoutTy} (base : Place Γ σ) (path : PathTo σ τ)
      (baseRes : PtrResult) (tmpReg : Register)
      (baseEv : PlaceToRegEvidence L kind base baseRes)
      (h_offset : pathOffset L base path ≠ 0) :
      PlaceToRegEvidence L kind (.proj base path)
        { reg := tmpReg, cleanup := baseRes.cleanup ++ [(tmpReg, placeSize L (.proj base path))] }
  | deref
      {σ : LayoutTy} (ptrPlace : Place Γ (LayoutTy.PtrL σ))
      (ptrRes : PtrResult) (loadedReg : Register)
      (ptrEv : PlaceToRegEvidence L RefKind.Shared ptrPlace ptrRes) :
      PlaceToRegEvidence L kind (.deref ptrPlace)
        { reg := loadedReg, cleanup := [] }

inductive PlaceToBorrowRegEvidence {Γ : Ctx} (L : LayEnv Γ) :
    RefKind → {τ : LayoutTy} → Place Γ τ → PtrResult → Type where
  | local
      {τ : LayoutTy} (loc : Local Γ τ) (baseRes : PtrResult) (tmpReg : Register)
      (baseEv : PlaceToRegEvidence L kind (.local loc) baseRes) :
      PlaceToBorrowRegEvidence L kind (.local loc)
        { reg := tmpReg, cleanup := [(tmpReg, placeSize L (.local loc))] }
  | projAssoc
      {ρ σ τ : LayoutTy} (b : Place Γ ρ) (q : PathTo ρ σ) (p : PathTo σ τ)
      (res : PtrResult)
      (ev : PlaceToBorrowRegEvidence L kind (.proj b (q.append p)) res) :
      PlaceToBorrowRegEvidence L kind (.proj (.proj b q) p) res
  | proj
      {σ τ : LayoutTy} (base : Place Γ σ) (path : PathTo σ τ)
      (baseRes : PtrResult) (tmpReg : Register)
      (baseEv : PlaceToRegEvidence L kind base baseRes) :
      PlaceToBorrowRegEvidence L kind (.proj base path)
        { reg := tmpReg, cleanup := baseRes.cleanup ++ [(tmpReg, placeSize L (.proj base path))] }
  | deref
      {σ : LayoutTy} (ptrPlace : Place Γ (LayoutTy.PtrL σ))
      (ptrRes : PtrResult) (loadedReg tmpReg : Register)
      (ptrEv : PlaceToRegEvidence L RefKind.Shared ptrPlace ptrRes) :
      PlaceToBorrowRegEvidence L kind (.deref ptrPlace)
        { reg := tmpReg, cleanup := [(tmpReg, placeSize L (.deref ptrPlace))] }

def placeToRegChecked {Γ : Ctx} (L : LayEnv Γ) {τ : LayoutTy}
    (kind : RefKind) :
    (p : Place Γ τ) → CheckedEvidenceM PtrResult (PlaceToRegEvidence L kind p)
  | .local loc =>
      ⟨fun cs =>
        match h_lookup : getPlaceInfo cs loc.idx.1 with
        | some (reg, layout) =>
            (Except.ok { result := { reg := reg, cleanup := [] },
                         evidence := PlaceToRegEvidence.local loc cs reg layout h_lookup },
              ⟨cs, StateIncr.refl cs⟩)
        | none =>
            (Except.error (.missingLocal loc.idx.1),
              ⟨cs, StateIncr.refl cs⟩)
      ⟩
  -- REASSOCIATE nested projections, as `compile.lean` (one borrow at the
  -- composed byte offset, with the final field's byte length)
  | .proj (.proj b q) p => do
      let out ← placeToRegChecked L kind (.proj b (q.append p))
      pure {
        result := out.result,
        evidence := PlaceToRegEvidence.projAssoc b q p out.result out.evidence
      }
  | .proj base path => do
      let baseOut ← placeToRegChecked L kind base
      let baseRes := baseOut.result
      let offset := pathOffset L base path
      if h_offset : offset = 0 then
        pure {
          result := baseRes,
          evidence := PlaceToRegEvidence.projZero base path baseRes baseOut.evidence h_offset
        }
      else
        let tmpReg ← CheckedCompilerM.lift freshRegM
        let _ ← CheckedCompilerM.lift
          (emitM [Instr.Assgn tmpReg
            (borrowRhs kind (placeSize L (.proj base path)) baseRes.reg offset)])
        pure {
          result := { reg := tmpReg,
                      cleanup := baseRes.cleanup ++ [(tmpReg, placeSize L (.proj base path))] },
          evidence := PlaceToRegEvidence.projOffset base path baseRes tmpReg baseOut.evidence h_offset
        }
  | .deref ptrPlace => do
      let ptrOut ← placeToRegChecked L RefKind.Shared ptrPlace
      let ptrRes := ptrOut.result
      let loadedReg ← CheckedCompilerM.lift freshRegM
      let _ ← CheckedCompilerM.lift
        (emitM [Instr.Assgn loadedReg (Rhs.Load (derefLoad L ptrPlace) ptrRes.reg)])
      let _ ← CheckedCompilerM.lift (emitM (cleanupInstrs ptrRes.cleanup))
      pure {
        result := { reg := loadedReg, cleanup := [] },
        evidence := PlaceToRegEvidence.deref ptrPlace ptrRes loadedReg ptrOut.evidence
      }
  termination_by p => p.depth
  decreasing_by all_goals (simp [Place.depth]; try omega)

/-- `mask` is already per BYTE of the place (`maskBytes`, or `[]`). -/
def placeToBorrowRegChecked {Γ : Ctx} (L : LayEnv Γ) {τ : LayoutTy}
    (kind : RefKind) (prot : Bool) (mask : List Bool) :
    (p : Place Γ τ) → CheckedEvidenceM PtrResult (PlaceToBorrowRegEvidence L kind p)
  | .local loc => do
      let baseOut ← placeToRegChecked L kind (.local loc)
      let baseRes := baseOut.result
      let tmpReg ← CheckedCompilerM.lift freshRegM
      let _ ← CheckedCompilerM.lift
        (emitM [Instr.Assgn tmpReg
          (Rhs.Borrow kind prot mask (some (placeSize L (.local loc))) baseRes.reg 0)])
      pure {
        result := { reg := tmpReg, cleanup := [(tmpReg, placeSize L (.local loc))] },
        evidence := PlaceToBorrowRegEvidence.local loc baseRes tmpReg baseOut.evidence
      }
  | .proj (.proj b q) p => do
      let out ← placeToBorrowRegChecked L kind prot mask (.proj b (q.append p))
      pure {
        result := out.result,
        evidence := PlaceToBorrowRegEvidence.projAssoc b q p out.result out.evidence
      }
  | .proj base path => do
      let baseOut ← placeToRegChecked L kind base
      let baseRes := baseOut.result
      let offset := pathOffset L base path
      let tmpReg ← CheckedCompilerM.lift freshRegM
      let _ ← CheckedCompilerM.lift
        (emitM [Instr.Assgn tmpReg
          (Rhs.Borrow kind prot mask (some (placeSize L (.proj base path))) baseRes.reg offset)])
      pure {
        result := { reg := tmpReg,
                    cleanup := baseRes.cleanup ++ [(tmpReg, placeSize L (.proj base path))] },
        evidence := PlaceToBorrowRegEvidence.proj base path baseRes tmpReg baseOut.evidence
      }
  | .deref ptrPlace => do
      let ptrOut ← placeToRegChecked L RefKind.Shared ptrPlace
      let ptrRes := ptrOut.result
      let loadedReg ← CheckedCompilerM.lift freshRegM
      let _ ← CheckedCompilerM.lift
        (emitM [Instr.Assgn loadedReg (Rhs.Load (derefLoad L ptrPlace) ptrRes.reg)])
      let _ ← CheckedCompilerM.lift (emitM (cleanupInstrs ptrRes.cleanup))
      let tmpReg ← CheckedCompilerM.lift freshRegM
      let _ ← CheckedCompilerM.lift
        (emitM [Instr.Assgn tmpReg
          (Rhs.Borrow kind prot mask (some (placeSize L (.deref ptrPlace))) loadedReg 0)])
      pure {
        result := { reg := tmpReg, cleanup := [(tmpReg, placeSize L (.deref ptrPlace))] },
        evidence := PlaceToBorrowRegEvidence.deref ptrPlace ptrRes loadedReg tmpReg ptrOut.evidence
      }
  termination_by p => p.depth
  decreasing_by all_goals (simp [Place.depth]; try omega)

inductive RExprToEvidence {Γ : Ctx} (L : LayEnv Γ)
    (dstPtr : Register) : {τ : LayoutTy} → RExpr Γ τ → Type where
  | constInit {t : IntTy} (value : Word) :
      RExprToEvidence L dstPtr (.constInit (t := t) value)
  | copy
      {τ : LayoutTy} (src : Place Γ τ) (srcRes : PtrResult)
      (srcEv : PlaceToRegEvidence L RefKind.Shared src srcRes) :
      RExprToEvidence L dstPtr (.copy src)
  | ref
      {σ : LayoutTy} (kind : RefKind) (prot : Bool) (mask : List Bool)
      (src : Place Γ σ) (srcRes : PtrResult)
      (srcEv : PlaceToBorrowRegEvidence L kind src srcRes) :
      RExprToEvidence L dstPtr (.ref kind prot mask src)
  | move
      {τ : LayoutTy} (src : Place Γ τ) (srcRes : PtrResult)
      (srcEv : PlaceToBorrowRegEvidence L RefKind.Mut src srcRes) :
      RExprToEvidence L dstPtr (.move src)
  | uninit {τ : LayoutTy} :
      RExprToEvidence L dstPtr (.uninit (τ := τ))
  | alloc {τ : LayoutTy} (len : AllocLen Γ) (reg : Register) :
      RExprToEvidence L dstPtr (.alloc (τ := τ) len)
  | binOp (op : BinOp) {ta tb tr : IntTy} (a : Place Γ (LayoutTy.IntL ta))
      (b : Place Γ (LayoutTy.IntL tb)) (r1 r2 tmp : Register) :
      RExprToEvidence L dstPtr (.binOp (tr := tr) op a b)
  | sliceLen {σ : LayoutTy} {t : IntTy} (src : Place Γ (LayoutTy.PtrL σ)) (r tmp : Register) :
      RExprToEvidence L dstPtr (.sliceLen (t := t) src)
  | subSlice {σ : LayoutTy} (src : Place Γ (LayoutTy.PtrL σ))
      {tl th : IntTy} (lo : Place Γ (LayoutTy.IntL tl)) (hi : Place Γ (LayoutTy.IntL th))
      (rp rLo rHi tmp : Register) :
      RExprToEvidence L dstPtr (.subSlice src lo hi)
  | exposeAddr
      {σ : LayoutTy} {t : IntTy} (src : Place Γ (LayoutTy.PtrL σ)) (srcRes : PtrResult)
      (srcEv : PlaceToRegEvidence L RefKind.Shared src srcRes) :
      RExprToEvidence L dstPtr (.exposeAddr (t := t) src)
  | addr
      {σ : LayoutTy} {t : IntTy} (src : Place Γ (LayoutTy.PtrL σ)) (srcRes : PtrResult)
      (srcEv : PlaceToRegEvidence L RefKind.Shared src srcRes) :
      RExprToEvidence L dstPtr (.addr (t := t) src)
  | fromExposed
      {τ : LayoutTy} {t : IntTy} (src : Place Γ (LayoutTy.IntL t)) (srcRes : PtrResult)
      (srcEv : PlaceToRegEvidence L RefKind.Shared src srcRes) :
      RExprToEvidence L dstPtr (.fromExposed (τ := τ) src)
  | ptrCast
      {σ τ : LayoutTy} (src : Place Γ (LayoutTy.PtrL σ)) (srcRes : PtrResult)
      (srcEv : PlaceToRegEvidence L RefKind.Shared src srcRes) :
      RExprToEvidence L dstPtr (.ptrCast (τ := τ) src)
  | ptrOffset
      {σ τ : LayoutTy} (src : Place Γ (LayoutTy.PtrL σ)) (delta : Int) (inbounds : Bool)
      (srcRes : PtrResult)
      (srcEv : PlaceToRegEvidence L RefKind.Shared src srcRes) :
      RExprToEvidence L dstPtr (.ptrOffset (τ := τ) src delta inbounds)
  | refSlice
      {σ τ : LayoutTy} (kind : RefKind) (prot : Bool)
      (src : Place Γ (LayoutTy.PtrL σ)) (srcRes : PtrResult)
      (srcEv : PlaceToRegEvidence L RefKind.Shared src srcRes) :
      RExprToEvidence L dstPtr (.refSlice (τ := τ) kind prot src)

/-- As `compile.lean`'s `RhsPre`: the rhs code before the store, the
    store as a function of the destination register. -/
structure RhsPre {Γ : Ctx} (L : LayEnv Γ) (τ : LayoutTy) (expr : RExpr Γ τ) where
  store : Register → List Instr
  postCleanup : List (Register × Nat)
  ev : (dstPtr : Register) → RExprToEvidence L dstPtr expr

/-- The read-then-store family (`compile.lean`'s `readRhsPre`); the store
    is at the destination's layout `dstL`. -/
def readRhsPre {Γ : Ctx} (L : LayEnv Γ) (dstL : BLayout) {σ τ : LayoutTy}
    (rhs : RExpr Γ τ) (src : Place Γ σ)
    (mk : Register → Rhs) (post : Register → List Instr)
    (ev : (srcRes : PtrResult) → PlaceToRegEvidence L RefKind.Shared src srcRes →
      (dstPtr : Register) → RExprToEvidence L dstPtr rhs) :
    CheckedCompilerM (RhsPre L τ rhs) := do
  let srcOut ← placeToRegChecked L RefKind.Shared src
  let srcRes := srcOut.result
  let tmpReg ← CheckedCompilerM.lift freshRegM
  let _ ← CheckedCompilerM.lift
    (emitM ([Instr.Assgn tmpReg (mk srcRes.reg)] ++ cleanupInstrs srcRes.cleanup
      ++ post tmpReg))
  pure {
    store := fun dstPtr => [Instr.RStore dstL tmpReg dstPtr],
    postCleanup := [],
    ev := fun dstPtr => ev srcRes srcOut.evidence dstPtr
  }

/-- Copy's read of a place into a value register, at the place's layout. -/
def readToReg {Γ : Ctx} (L : LayEnv Γ) {τ : LayoutTy} (p : Place Γ τ) :
    CheckedCompilerM Register := do
  let pOut ← placeToRegChecked L RefKind.Shared p
  let reg ← CheckedCompilerM.lift freshRegM
  let _ ← CheckedCompilerM.lift
    (emitM ([Instr.Assgn reg (Rhs.Load (placeLayout L p) pOut.result.reg)]
      ++ cleanupInstrs pOut.result.cleanup))
  pure reg

def guardRead {Γ : Ctx} (L : LayEnv Γ) {t : IntTy} (discr : Place Γ (LayoutTy.IntL t)) :
    CheckedCompilerM Register :=
  readToReg L discr

/-- `alloc`'s heap pointer, `pointee` being the element layout. -/
def compileAllocLenChecked {Γ : Ctx} (L : LayEnv Γ) (pointee : BLayout) :
    AllocLen Γ → CheckedCompilerM Register
  | .const n => do
      let tmpReg ← CheckedCompilerM.lift freshRegM
      let _ ← CheckedCompilerM.lift (emitM [Instr.Assgn tmpReg (Rhs.AllocN pointee n)])
      pure tmpReg
  | .fromPlace p => do
      let lenReg ← guardRead L p
      let tmpReg ← CheckedCompilerM.lift freshRegM
      let _ ← CheckedCompilerM.lift (emitM [Instr.Assgn tmpReg (Rhs.AllocDyn pointee lenReg)])
      pure tmpReg

/-- `dstL` is the destination's layout, as the source's `evalRExpr`. -/
def compileRExprPreChecked {Γ : Ctx} (L : LayEnv Γ) (dstL : BLayout) {τ : LayoutTy} :
    (expr : RExpr Γ τ) → CheckedCompilerM (RhsPre L τ expr)
  | .constInit value =>
      pure {
        store := fun dstPtr => [Instr.CStore dstL [Val.Dat value] dstPtr],
        postCleanup := [],
        ev := fun _ => RExprToEvidence.constInit value
      }
  | .copy src => do
      readRhsPre L dstL (RExpr.copy src) src (Rhs.Load (placeLayout L src)) (fun _ => [])
        (fun srcRes evd _ => RExprToEvidence.copy src srcRes evd)
  | .ref kind prot mask src => do
      let srcOut ← placeToBorrowRegChecked L kind prot (maskBytes (placeLayout L src) mask) src
      let srcRes := srcOut.result
      pure {
        store := fun dstPtr => [Instr.RStore dstL srcRes.reg dstPtr],
        postCleanup := [],
        ev := fun _ => RExprToEvidence.ref kind prot mask src srcRes srcOut.evidence
      }
  | .move src => do
      let srcOut ← placeToBorrowRegChecked L RefKind.Mut false [] src
      let srcRes := srcOut.result
      let tmpReg ← CheckedCompilerM.lift freshRegM
      let _ ← CheckedCompilerM.lift
        (emitM ([Instr.Assgn tmpReg (Rhs.Load (placeLayout L src) srcRes.reg)]
          ++ cleanupInstrs srcRes.cleanup))
      pure {
        store := fun dstPtr => [Instr.RStore dstL tmpReg dstPtr],
        postCleanup := [],
        ev := fun _ => RExprToEvidence.move src srcRes srcOut.evidence
      }
  | .alloc (τ := σ) len => do
      let r ← compileAllocLenChecked L (mirlite.allocPointee dstL σ) len
      pure {
        store := fun dstPtr => [Instr.RStore dstL r dstPtr],
        postCleanup := [],
        ev := fun _ => RExprToEvidence.alloc len r
      }
  | .binOp op a b => do
      let r1 ← readToReg L a
      let r2 ← readToReg L b
      let tmp ← CheckedCompilerM.lift freshRegM
      let _ ← CheckedCompilerM.lift (emitM [Instr.Assgn tmp (Rhs.BinOp op r1 r2)])
      pure {
        store := fun dstPtr => [Instr.RStore dstL tmp dstPtr],
        postCleanup := [],
        ev := fun _ => RExprToEvidence.binOp op a b r1 r2 tmp
      }
  | .sliceLen src => do
      let r ← readToReg L src
      let tmp ← CheckedCompilerM.lift freshRegM
      let _ ← CheckedCompilerM.lift
        (emitM [Instr.Assgn tmp (Rhs.SliceLen (pointeeLayout L src).size r)])
      pure {
        store := fun dstPtr => [Instr.RStore dstL tmp dstPtr],
        postCleanup := [],
        ev := fun _ => RExprToEvidence.sliceLen src r tmp
      }
  | .subSlice src lo hi => do
      let rp ← readToReg L src
      let rLo ← readToReg L lo
      let rHi ← readToReg L hi
      let tmp ← CheckedCompilerM.lift freshRegM
      let _ ← CheckedCompilerM.lift
        (emitM [Instr.Assgn tmp (Rhs.SubSlice (pointeeLayout L src).size rp rLo rHi)])
      pure {
        store := fun dstPtr => [Instr.RStore dstL tmp dstPtr],
        postCleanup := [],
        ev := fun _ => RExprToEvidence.subSlice src lo hi rp rLo rHi tmp
      }
  | .uninit =>
      -- the source writes one undef per destination leaf
      pure {
        store := fun dstPtr =>
          [Instr.CStore dstL (List.replicate dstL.leaves.length Val.Undef) dstPtr],
        postCleanup := [],
        ev := fun _ => RExprToEvidence.uninit
      }
  | .exposeAddr src =>
      readRhsPre L dstL (RExpr.exposeAddr src) src
        (Rhs.ExposeAddr (leafKind (placeLayout L src))) (fun _ => [])
        (fun srcRes evd _ => RExprToEvidence.exposeAddr src srcRes evd)
  | .addr src =>
      -- a load of the pointer's bytes at integer layout: the same decode
      readRhsPre L dstL (RExpr.addr src) src
        (Rhs.Load (.int (leafKind (placeLayout L src)).size)) (fun _ => [])
        (fun srcRes evd _ => RExprToEvidence.addr src srcRes evd)
  | .fromExposed (τ := τ) src =>
      readRhsPre L dstL (RExpr.fromExposed (τ := τ) src) src
        (Rhs.FromExposed (leafKind (placeLayout L src))) (fun _ => [])
        (fun srcRes evd _ => RExprToEvidence.fromExposed src srcRes evd)
  | .ptrCast (τ := τ) src => do
      readRhsPre L dstL (RExpr.ptrCast (τ := τ) src) src
        (Rhs.Load (leafLayout (leafKind (placeLayout L src)))) (fun _ => [])
        (fun srcRes evd _ => RExprToEvidence.ptrCast src srcRes evd)
  | .ptrOffset src delta inbounds => do
      -- delta is in pointees of the SOURCE type; pre-scale to bytes
      readRhsPre L dstL (RExpr.ptrOffset src delta inbounds) src
        (fun r => Rhs.PtrOffset (leafKind (placeLayout L src)) r
          (delta * ((pointeeLayout L src).size : Int)) inbounds) (fun _ => [])
        (fun srcRes evd _ => RExprToEvidence.ptrOffset src delta inbounds srcRes evd)
  | .refSlice (τ := τ) kind prot src =>
      readRhsPre L dstL (RExpr.refSlice (τ := τ) kind prot src) src
        (Rhs.Load (leafLayout (leafKind (placeLayout L src))))
        (fun tmp => [Instr.Assgn tmp (Rhs.Borrow kind prot [] none tmp 0)])
        (fun srcRes evd _ => RExprToEvidence.refSlice kind prot src srcRes evd)

def compileRExprToChecked {Γ : Ctx} (L : LayEnv Γ) (dstL : BLayout)
  (dstPtr : Register) {τ : LayoutTy}
  (expr : RExpr Γ τ) :
    CheckedEvidenceM Unit (fun _ => RExprToEvidence L dstPtr expr) := do
  let pre ← compileRExprPreChecked L dstL expr
  let _ ← CheckedCompilerM.lift (emitM (pre.store dstPtr))
  let _ ← CheckedCompilerM.lift (emitM (cleanupInstrs pre.postCleanup))
  pure { result := (), evidence := pre.ev dstPtr }

inductive StmtEvidence {Γ : Ctx} (L : LayEnv Γ) : Stmt Γ → Type where
  | halt :
      StmtEvidence L .halt
  | assignPlace
      {τ : LayoutTy} (dst : Place Γ τ) (rhs : RExpr Γ τ)
      (dstRes : PtrResult)
      (dstEv : PlaceToRegEvidence L RefKind.Mut dst dstRes)
      (rhsEv : RExprToEvidence L dstRes.reg rhs) :
      StmtEvidence L (.assign dst rhs)
  | pushProtectors :
      StmtEvidence L .pushProtectors
  | popProtectors :
      StmtEvidence L .popProtectors
  | assignIf
      {τ : LayoutTy} {t : IntTy} (discr : Place Γ (LayoutTy.IntL t)) (val : Word)
      (dst : Place Γ τ) (rhs : RExpr Γ τ) :
      StmtEvidence L (.assignIf discr val dst rhs)
  | dealloc
      {τ : LayoutTy} (dst : Place Γ (LayoutTy.PtrL τ)) :
      StmtEvidence L (.dealloc dst)

def compileAssignChecked {Γ : Ctx} (L : LayEnv Γ) {τ : LayoutTy}
    (dst : Place Γ τ) (rhs : RExpr Γ τ) :
    CheckedEvidenceM Unit (fun _ => StmtEvidence L (.assign dst rhs)) := do
  let _ ← CheckedCompilerM.lift (ensurePlaceRoot L dst)
  let pre ← compileRExprPreChecked L (placeLayout L dst) rhs
  let dstOut ← placeToRegChecked L RefKind.Mut dst
  let dstRes := dstOut.result
  let _ ← CheckedCompilerM.lift (emitM (pre.store dstRes.reg))
  let _ ← CheckedCompilerM.lift (emitM (cleanupInstrs pre.postCleanup))
  let _ ← CheckedCompilerM.lift (emitM (cleanupInstrs dstRes.cleanup))
  pure {
    result := (),
    evidence := StmtEvidence.assignPlace dst rhs dstRes dstOut.evidence
      (pre.ev dstRes.reg)
  }

def patchLabel (cs : CompilerState) (label : Nat) (i : Instr) : CompilerState :=
  { cs with code := fun l => if l = label then some i else cs.code l }

def reserveLabel (cs : CompilerState) : CompilerState :=
  { cs with nextLabel := cs.nextLabel + 1,
            code := fun l => if l = cs.nextLabel then none else cs.code l }

theorem reserveLabel_state_incr (cs : CompilerState) :
    StateIncr cs (reserveLabel cs) :=
  ⟨Nat.le_succ _, Nat.le_refl _,
   fun l h_l => by
     show (if l = cs.nextLabel then none else cs.code l) = cs.code l
     rw [if_neg (by omega)],
   fun _ _ h => h⟩

theorem StateIncr.patchLabel {cs cs' : CompilerState} (h : StateIncr cs cs')
    {label : Nat} (h_label : cs.nextLabel ≤ label) (i : Instr) :
    StateIncr cs (patchLabel cs' label i) :=
  ⟨h.nextLabel_le, h.nextReg_le,
   fun l h_l => by
     show (if l = label then some i else cs'.code l) = cs.code l
     rw [if_neg (by omega)]
     exact h.code_eq l h_l,
   h.placeRegMap_mono⟩

def emitSkipIfAround (discrReg : Register) (val : Word)
    (body : CheckedCompilerM α) : CheckedCompilerM Unit :=
  ⟨fun cs =>
    let cs1 := reserveLabel cs
    let real := body.toCompilerM cs1
    match real.1 with
    | .error err => (.error err, ⟨cs, StateIncr.refl cs⟩)
    | .ok _ =>
      let bodyLen := real.2.1.nextLabel - cs1.nextLabel
      (.ok (), ⟨patchLabel real.2.1 cs.nextLabel (Instr.SkipIf discrReg val bodyLen),
        StateIncr.patchLabel ((reserveLabel_state_incr cs).trans real.2.2)
          (Nat.le_refl _) _⟩)⟩

def compileStmtChecked {Γ : Ctx} (L : LayEnv Γ) :
    (stmt : Stmt Γ) → CheckedEvidenceM Unit (fun _ => StmtEvidence L stmt)
  | .halt => do
      let _ ← CheckedCompilerM.lift (emitM [Instr.Halt])
      pure { result := (), evidence := StmtEvidence.halt }
  | .assign dst rhs => compileAssignChecked L dst rhs
  | .pushProtectors => do
      let _ ← CheckedCompilerM.lift (emitM [Instr.PushProt])
      pure { result := (), evidence := StmtEvidence.pushProtectors }
  | .popProtectors => do
      let _ ← CheckedCompilerM.lift (emitM [Instr.PopProt])
      pure { result := (), evidence := StmtEvidence.popProtectors }
  | .dealloc dst => do
      let loadedReg ← readToReg L dst
      let _ ← CheckedCompilerM.lift (emitM [Instr.Dealloc loadedReg])
      pure { result := (), evidence := StmtEvidence.dealloc dst }
  | .assignIf discr val dst rhs => do
      let _ ← CheckedCompilerM.lift (ensurePlaceRoot L dst)
      let discrReg ← guardRead L discr
      emitSkipIfAround discrReg val (compileAssignChecked L dst rhs)
      pure { result := (), evidence := StmtEvidence.assignIf discr val dst rhs }

def compileStmtsChecked {Γ : Ctx} (L : LayEnv Γ) : Prog Γ → CheckedCompilerM Unit
  | [] => pure ()
  | stmt :: rest => do
  let _ ← compileStmtChecked L stmt
  compileStmtsChecked L rest

def initialState (_Γ : Ctx) : CompilerState :=
  { nextReg := 0, nextLabel := 0, code := fun _ => none, placeRegMap := [] }

def compileProg {Γ : Ctx} (L : LayEnv Γ) (prog : Prog Γ) : Except CompilerError TargetProg :=
  match CheckedCompilerM.value (compileStmtsChecked L prog) (initialState Γ) with
  | .ok _ => .ok (CheckedCompilerM.run (compileStmtsChecked L prog) (initialState Γ)).code
  | .error err => .error err

/-- Per-source-statement label ranges, as `compile.stmtLabelRanges`. -/
def stmtLabelRanges {Γ : Ctx} (L : LayEnv Γ) (prog : Prog Γ) : List (Nat × Nat) :=
  (prog.foldl
    (fun (acc : List (Nat × Nat) × CompilerState) stmt =>
      let cs' := CheckedCompilerM.run (compileStmtChecked L stmt) acc.2
      (acc.1 ++ [(acc.2.nextLabel, cs'.nextLabel)], cs'))
    ([], initialState Γ)).1

def emittedLabels {Γ : Ctx} (L : LayEnv Γ) (prog : Prog Γ) : Nat :=
  (CheckedCompilerM.run (compileStmtsChecked L prog) (initialState Γ)).nextLabel

end obseq3.compile
