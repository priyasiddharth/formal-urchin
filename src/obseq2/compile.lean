import obseq2.syntax
import obseq2.oseair

namespace obseq2.compile

open obseq2
open obseq2.oseair (Register Instr Rhs Val)

abbrev TargetProg := obseq2.oseair.Prog
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

/-- Result of an address computation. -/
structure PtrResult where
  /-- The register holding the computed address. -/
  reg : Register
  /-- Temporary registers that need to be cleaned up after use. -/
  cleanup : List Register
deriving Inhabited

structure RExprResult where
  reg : Register
deriving Inhabited

/-- Result of a compiler computation paired with proof evidence indexed by the
    exact returned value. Use this when the compiler path is expected to be
    valid by construction and must always produce evidence. -/
structure ResultWithEvidence (α : Type) (Ev : α → Type) where
  result : α
  evidence : Ev result

/-- Result of a compiler computation whose proof evidence may be absent.
    This is used for total erased compiler paths that still have an invalid
    fallback, such as `placeToReg` on an unallocated local: the runtime-shaped
    result is preserved for compatibility, but proofs cannot consume evidence
    unless the lowering was actually well-formed. -/
structure ResultWithOptEvidence (α : Type) (Ev : α → Type) where
  result : α
  evidence : Option (Ev result)

inductive CompilerError where
  | missingLocal (idx : Nat)
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

def toCheckedEvidenceWithFallback
    (m : CheckedCompilerM (ResultWithEvidence α Ev))
    (fallback : CompilerM α) :
    CompilerM (ResultWithOptEvidence α Ev) :=
  fun cs =>
    let checked := m.toCompilerM cs
    match checked.1 with
    | .ok out =>
        ({ result := out.result, evidence := some out.evidence },
         ⟨checked.2.1, checked.2.2⟩)
    | .error _ =>
        let fb := fallback cs
        ({ result := fb.1, evidence := none },
         ⟨fb.2.1, fb.2.2⟩)

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

def cleanupInstrs (regs : List Register) : List Instr :=
  regs.reverse.map Instr.Die

def getPlaceInfo (cs : CompilerState) (idx : Nat) : Option PlaceInfo :=
  cs.placeRegMap.lookup idx

def setPlaceInfo (cs : CompilerState) (idx : Nat) (info : PlaceInfo) : CompilerState :=
  { cs with placeRegMap := (idx, info) :: cs.placeRegMap }

theorem setPlaceInfo_state_incr (cs : CompilerState) (idx : Nat) (info : PlaceInfo) :
    StateIncr cs (setPlaceInfo cs idx info) :=
  ⟨Nat.le_refl _, Nat.le_refl _, fun _ _ => rfl,
   fun _ _ h => List.mem_cons_of_mem (idx, info) h⟩

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

def ensureLocalRegE {Γ : Ctx} {τ : LayoutTy}
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
        let cs2 := emit cs1 [Instr.Assgn reg (Rhs.Alloc (layoutToTyVal τ))]
        let cs3 := setPlaceInfo cs2 loc.idx.1 (reg, τ)
        ({ result := { reg := reg, cleanup := [] },
           evidence := EnsureLocalEvidence.fresh cs reg h_lookup rfl },
          ⟨cs3,
            (freshReg_state_incr cs).trans
              ((emit_state_incr cs1 [Instr.Assgn reg (Rhs.Alloc (layoutToTyVal τ))]).trans
                (setPlaceInfo_state_incr cs2 loc.idx.1 (reg, τ)))⟩)

def ensureLocalReg {Γ : Ctx} {τ : LayoutTy} (loc : Local Γ τ) : CompilerM PtrResult := do
  let ev ← ensureLocalRegE loc
  pure ev.result

def pathOffset : PathTo src dst → Nat
  | .nil => 0
  | .field (tys := tys) idx tail =>
      layoutSizeList (tys.take idx.1) + pathOffset tail

def borrowOffsetRhs (kind : RefKind) (base : Register) (offset : Word) : Rhs :=
  match kind with
  | .Shared => Rhs.BorOffset base offset
  | .Mut => Rhs.MutBorOffset base offset
  | .Raw => Rhs.CopyOffset base offset

inductive PlaceToRegEvidence {Γ : Ctx} :
    RefKind → {τ : LayoutTy} → Place Γ τ → PtrResult → Type where
  | local
      {τ : LayoutTy} (loc : Local Γ τ) (cs : CompilerState)
      (reg : Register) (layout : LayoutTy)
      (h_lookup : getPlaceInfo cs loc.idx.1 = some (reg, layout)) :
      PlaceToRegEvidence kind (.local loc) { reg := reg, cleanup := [] }
  | projZero
      {σ τ : LayoutTy} (base : Place Γ σ) (path : PathTo σ τ)
      (baseRes : PtrResult)
      (baseEv : PlaceToRegEvidence kind base baseRes)
      (h_offset : pathOffset path = 0) :
      PlaceToRegEvidence kind (.proj base path) baseRes
  | projOffset
      {σ τ : LayoutTy} (base : Place Γ σ) (path : PathTo σ τ)
      (baseRes : PtrResult) (tmpReg : Register)
      (baseEv : PlaceToRegEvidence kind base baseRes)
      (h_offset : pathOffset path ≠ 0) :
      PlaceToRegEvidence kind (.proj base path)
        { reg := tmpReg, cleanup := baseRes.cleanup ++ [tmpReg] }
  | deref
      {σ : LayoutTy} (ptrPlace : Place Γ (obseq.LayoutTy.PtrL σ))
      (ptrRes : PtrResult) (loadedReg : Register)
      (ptrEv : PlaceToRegEvidence RefKind.Shared ptrPlace ptrRes) :
      PlaceToRegEvidence kind (.deref ptrPlace)
        { reg := loadedReg, cleanup := [loadedReg] }

inductive PlaceToBorrowRegEvidence {Γ : Ctx} :
    RefKind → {τ : LayoutTy} → Place Γ τ → PtrResult → Type where
  | local
      {τ : LayoutTy} (loc : Local Γ τ) (baseRes : PtrResult) (tmpReg : Register)
      (baseEv : PlaceToRegEvidence kind (.local loc) baseRes) :
      PlaceToBorrowRegEvidence kind (.local loc)
        { reg := tmpReg, cleanup := [tmpReg] }
  | proj
      {σ τ : LayoutTy} (base : Place Γ σ) (path : PathTo σ τ)
      (baseRes : PtrResult) (tmpReg : Register)
      (baseEv : PlaceToRegEvidence kind base baseRes) :
      PlaceToBorrowRegEvidence kind (.proj base path)
        { reg := tmpReg, cleanup := baseRes.cleanup ++ [tmpReg] }
  | deref
      {σ : LayoutTy} (ptrPlace : Place Γ (obseq.LayoutTy.PtrL σ))
      (ptrRes : PtrResult) (loadedReg tmpReg : Register)
      (ptrEv : PlaceToRegEvidence RefKind.Shared ptrPlace ptrRes) :
      PlaceToBorrowRegEvidence kind (.deref ptrPlace)
        { reg := tmpReg, cleanup := [loadedReg, tmpReg] }

/-- Proof-facing place lowering. Invalid locals are rejected explicitly instead of
    silently falling back to register `R 0`. -/
def placeToRegChecked {Γ : Ctx} {τ : LayoutTy}
    (kind : RefKind) :
    (p : Place Γ τ) → CheckedEvidenceM PtrResult (PlaceToRegEvidence kind p)
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
  | .proj base path => do
      let baseOut ← placeToRegChecked kind base
      let baseRes := baseOut.result
      let offset := pathOffset path
      if h_offset : offset = 0 then
        pure {
          result := baseRes,
          evidence := PlaceToRegEvidence.projZero base path baseRes baseOut.evidence h_offset
        }
      else
        let tmpReg ← CheckedCompilerM.lift freshRegM
        let _ ← CheckedCompilerM.lift
          (emitM [Instr.Assgn tmpReg (borrowOffsetRhs kind baseRes.reg offset)])
        pure {
          result := { reg := tmpReg, cleanup := baseRes.cleanup ++ [tmpReg] },
          evidence := PlaceToRegEvidence.projOffset base path baseRes tmpReg baseOut.evidence h_offset
        }
  | .deref ptrPlace => do
      let ptrOut ← placeToRegChecked RefKind.Shared ptrPlace
      let ptrRes := ptrOut.result
      let loadedReg ← CheckedCompilerM.lift freshRegM
      let _ ← CheckedCompilerM.lift
        (emitM [Instr.Assgn loadedReg (Rhs.Load obseq.TyVal.PTy ptrRes.reg)])
      let _ ← CheckedCompilerM.lift (emitM (cleanupInstrs ptrRes.cleanup))
      pure {
        result := { reg := loadedReg, cleanup := [loadedReg] },
        evidence := PlaceToRegEvidence.deref ptrPlace ptrRes loadedReg ptrOut.evidence
      }

theorem placeToRegChecked_toCompilerM_local_of_getPlaceInfo
    {Γ : Ctx} {τ layout : LayoutTy}
    {kind : RefKind} {loc : Local Γ τ} {cs : CompilerState} {reg : Register}
    (h_lookup : getPlaceInfo cs loc.idx.1 = some (reg, layout)) :
    (placeToRegChecked kind (.local loc)).toCompilerM cs =
      ((Except.ok {
        result := { reg := reg, cleanup := [] },
        evidence := PlaceToRegEvidence.local loc cs reg layout h_lookup
      } : Except CompilerError
          (ResultWithEvidence PtrResult (PlaceToRegEvidence kind (.local loc)))),
        ⟨cs, StateIncr.refl cs⟩) := by
  let localOut : ResultWithEvidence PtrResult (PlaceToRegEvidence kind (.local loc)) := {
    result := { reg := reg, cleanup := [] },
    evidence := PlaceToRegEvidence.local loc cs reg layout h_lookup
  }
  let csOut : { cs' : CompilerState // StateIncr cs cs' } :=
    ⟨cs, StateIncr.refl cs⟩
  have h_pair :
      (match h_branch : getPlaceInfo cs loc.idx.1 with
        | some (reg', layout') =>
            ((Except.ok {
              result := { reg := reg', cleanup := [] },
              evidence := PlaceToRegEvidence.local loc cs reg' layout' h_branch
            } : Except CompilerError
                (ResultWithEvidence PtrResult (PlaceToRegEvidence kind (.local loc)))),
              csOut)
        | none =>
            ((Except.error (CompilerError.missingLocal loc.idx.1) : Except CompilerError
                (ResultWithEvidence PtrResult (PlaceToRegEvidence kind (.local loc)))),
              csOut)) =
      ((Except.ok localOut : Except CompilerError
          (ResultWithEvidence PtrResult (PlaceToRegEvidence kind (.local loc)))),
        csOut) := by
    unfold localOut csOut
    split
    · rename_i reg' layout' h_branch
      have h_eq : reg' = reg ∧ layout' = layout := by
        simpa [h_branch] using h_lookup
      rcases h_eq with ⟨rfl, rfl⟩
      have h_same : h_branch = h_lookup := Subsingleton.elim _ _
      cases h_same
      rfl
    · rename_i h_branch
      have h_false : False := by
        simp [h_branch] at h_lookup
      exact False.elim h_false
  simpa [placeToRegChecked, localOut, csOut] using h_pair

theorem placeToRegChecked_local_ok_of_getPlaceInfo
    {Γ : Ctx} {τ layout : LayoutTy}
    {kind : RefKind} {loc : Local Γ τ} {cs : CompilerState} {reg : Register}
    (h_lookup : getPlaceInfo cs loc.idx.1 = some (reg, layout)) :
    ∃ placeOut,
      CheckedCompilerM.value (placeToRegChecked kind (.local loc)) cs = Except.ok placeOut := by
  let localOut : ResultWithEvidence PtrResult (PlaceToRegEvidence kind (.local loc)) := {
    result := { reg := reg, cleanup := [] },
    evidence := PlaceToRegEvidence.local loc cs reg layout h_lookup
  }
  refine ⟨localOut, ?_⟩
  simpa [CheckedCompilerM.value, CompilerM.value, localOut] using
    congrArg Prod.fst
      (placeToRegChecked_toCompilerM_local_of_getPlaceInfo
        (kind := kind) (loc := loc) (cs := cs) (reg := reg) (layout := layout) h_lookup)

/-- Erased place lowering with the historical missing-local fallback.
    This is now only used at compatibility boundaries while checked callers go
    through `placeToRegChecked`. Fresh allocation should happen only through
    `ensureLocalReg`; all other place-to-register lowering should require an
    already allocated local in `placeRegMap`. -/
def placeToRegUnsafe {Γ : Ctx} {τ : LayoutTy} (kind : RefKind) : Place Γ τ → CompilerM PtrResult
  | .local loc =>
      fun cs =>
        match getPlaceInfo cs loc.idx.1 with
        | some (reg, _) => ({ reg := reg, cleanup := [] }, ⟨cs, StateIncr.refl cs⟩)
        | none => ({ reg := Register.R 0, cleanup := [] }, ⟨cs, StateIncr.refl cs⟩)
  | .proj base path => do
      let baseRes ← placeToRegUnsafe kind base
      let offset := pathOffset path
      if offset = 0 then
        pure baseRes
      else
        let tmpReg ← freshRegM
        emitM [Instr.Assgn tmpReg (borrowOffsetRhs kind baseRes.reg offset)]
        pure { reg := tmpReg, cleanup := baseRes.cleanup ++ [tmpReg] }
  | .deref ptrPlace => do
      let ptrRes ← placeToRegUnsafe RefKind.Shared ptrPlace
      let loadedReg ← freshRegM
      emitM [Instr.Assgn loadedReg (Rhs.Load obseq.TyVal.PTy ptrRes.reg)]
      emitM (cleanupInstrs ptrRes.cleanup)
      pure { reg := loadedReg, cleanup := [loadedReg] }

/-- Compatibility wrapper around `placeToRegChecked`.
    Invalid lowering preserves the historical fallback result but drops evidence. -/
def placeToRegE {Γ : Ctx} {τ : LayoutTy}
    (kind : RefKind) :
    (p : Place Γ τ) → CompilerM (ResultWithOptEvidence PtrResult (PlaceToRegEvidence kind p))
  | .local loc =>
      fun cs =>
        match h_lookup : getPlaceInfo cs loc.idx.1 with
        | some (reg, layout) =>
            ({ result := { reg := reg, cleanup := [] },
               evidence := some (PlaceToRegEvidence.local loc cs reg layout h_lookup) },
              ⟨cs, StateIncr.refl cs⟩)
        | none =>
            ({ result := { reg := Register.R 0, cleanup := [] }, evidence := none },
              ⟨cs, StateIncr.refl cs⟩)
  | .proj base path => do
      let baseChecked ← placeToRegE kind base
      let baseRes := baseChecked.result
      let offset := pathOffset path
      if h_offset : offset = 0 then
        pure {
          result := baseRes,
          evidence := baseChecked.evidence.map
            (fun baseEv => PlaceToRegEvidence.projZero base path baseRes baseEv h_offset)
        }
      else
        let tmpReg ← freshRegM
        emitM [Instr.Assgn tmpReg (borrowOffsetRhs kind baseRes.reg offset)]
        pure {
          result := { reg := tmpReg, cleanup := baseRes.cleanup ++ [tmpReg] },
          evidence := baseChecked.evidence.map
            (fun baseEv => PlaceToRegEvidence.projOffset base path baseRes tmpReg baseEv h_offset)
        }
  | .deref ptrPlace => do
      let ptrChecked ← placeToRegE RefKind.Shared ptrPlace
      let ptrRes := ptrChecked.result
      let loadedReg ← freshRegM
      emitM [Instr.Assgn loadedReg (Rhs.Load obseq.TyVal.PTy ptrRes.reg)]
      emitM (cleanupInstrs ptrRes.cleanup)
      pure {
        result := { reg := loadedReg, cleanup := [loadedReg] },
        evidence := ptrChecked.evidence.map
          (fun ptrEv => PlaceToRegEvidence.deref ptrPlace ptrRes loadedReg ptrEv)
      }

/-- Compatibility alias for the current erased compiler.
    Checked callers should prefer `placeToRegChecked`. -/
def placeToReg {Γ : Ctx} {τ : LayoutTy} (kind : RefKind) (p : Place Γ τ) :
    CompilerM PtrResult :=
  do
    let checked ← placeToRegE kind p
    pure checked.result

def placeToBorrowRegUnsafe {Γ : Ctx} {τ : LayoutTy}
    (kind : RefKind) : Place Γ τ → CompilerM PtrResult
  | .local loc => do
      let baseRes ← placeToRegUnsafe kind (.local loc)
      let tmpReg ← freshRegM
      emitM [Instr.Assgn tmpReg (borrowOffsetRhs kind baseRes.reg 0)]
      pure { reg := tmpReg, cleanup := [tmpReg] }
  | .proj base path => do
      let baseRes ← placeToRegUnsafe kind base
      let offset := pathOffset path
      let tmpReg ← freshRegM
      emitM [Instr.Assgn tmpReg (borrowOffsetRhs kind baseRes.reg offset)]
      pure { reg := tmpReg, cleanup := baseRes.cleanup ++ [tmpReg] }
  | .deref ptrPlace => do
      let ptrRes ← placeToRegUnsafe RefKind.Shared ptrPlace
      let loadedReg ← freshRegM
      emitM [Instr.Assgn loadedReg (Rhs.Load obseq.TyVal.PTy ptrRes.reg)]
      emitM (cleanupInstrs ptrRes.cleanup)
      let tmpReg ← freshRegM
      emitM [Instr.Assgn tmpReg (borrowOffsetRhs kind loadedReg 0)]
      pure { reg := tmpReg, cleanup := [loadedReg, tmpReg] }

def placeToBorrowRegChecked {Γ : Ctx} {τ : LayoutTy}
    (kind : RefKind) :
    (p : Place Γ τ) → CheckedEvidenceM PtrResult (PlaceToBorrowRegEvidence kind p)
  | .local loc => do
      let baseOut ← placeToRegChecked kind (.local loc)
      let baseRes := baseOut.result
      let tmpReg ← CheckedCompilerM.lift freshRegM
      let _ ← CheckedCompilerM.lift
        (emitM [Instr.Assgn tmpReg (borrowOffsetRhs kind baseRes.reg 0)])
      pure {
        result := { reg := tmpReg, cleanup := [tmpReg] },
        evidence := PlaceToBorrowRegEvidence.local loc baseRes tmpReg baseOut.evidence
      }
  | .proj base path => do
      let baseOut ← placeToRegChecked kind base
      let baseRes := baseOut.result
      let offset := pathOffset path
      let tmpReg ← CheckedCompilerM.lift freshRegM
      let _ ← CheckedCompilerM.lift
        (emitM [Instr.Assgn tmpReg (borrowOffsetRhs kind baseRes.reg offset)])
      pure {
        result := { reg := tmpReg, cleanup := baseRes.cleanup ++ [tmpReg] },
        evidence := PlaceToBorrowRegEvidence.proj base path baseRes tmpReg baseOut.evidence
      }
  | .deref ptrPlace => do
      let ptrOut ← placeToRegChecked RefKind.Shared ptrPlace
      let ptrRes := ptrOut.result
      let loadedReg ← CheckedCompilerM.lift freshRegM
      let _ ← CheckedCompilerM.lift
        (emitM [Instr.Assgn loadedReg (Rhs.Load obseq.TyVal.PTy ptrRes.reg)])
      let _ ← CheckedCompilerM.lift (emitM (cleanupInstrs ptrRes.cleanup))
      let tmpReg ← CheckedCompilerM.lift freshRegM
      let _ ← CheckedCompilerM.lift
        (emitM [Instr.Assgn tmpReg (borrowOffsetRhs kind loadedReg 0)])
      pure {
        result := { reg := tmpReg, cleanup := [loadedReg, tmpReg] },
        evidence := PlaceToBorrowRegEvidence.deref ptrPlace ptrRes loadedReg tmpReg ptrOut.evidence
      }

def placeToBorrowRegE {Γ : Ctx} {τ : LayoutTy}
    (kind : RefKind) :
    (p : Place Γ τ) → CompilerM (ResultWithOptEvidence PtrResult (PlaceToBorrowRegEvidence kind p))
  | .local loc => do
      let baseChecked ← placeToRegE kind (.local loc)
      let baseRes := baseChecked.result
      let tmpReg ← freshRegM
      emitM [Instr.Assgn tmpReg (borrowOffsetRhs kind baseRes.reg 0)]
      pure {
        result := { reg := tmpReg, cleanup := [tmpReg] },
        evidence := baseChecked.evidence.map
          (fun baseEv => PlaceToBorrowRegEvidence.local loc baseRes tmpReg baseEv)
      }
  | .proj base path => do
      let baseChecked ← placeToRegE kind base
      let baseRes := baseChecked.result
      let offset := pathOffset path
      let tmpReg ← freshRegM
      emitM [Instr.Assgn tmpReg (borrowOffsetRhs kind baseRes.reg offset)]
      pure {
        result := { reg := tmpReg, cleanup := baseRes.cleanup ++ [tmpReg] },
        evidence := baseChecked.evidence.map
          (fun baseEv => PlaceToBorrowRegEvidence.proj base path baseRes tmpReg baseEv)
      }
  | .deref ptrPlace => do
      let ptrChecked ← placeToRegE RefKind.Shared ptrPlace
      let ptrRes := ptrChecked.result
      let loadedReg ← freshRegM
      emitM [Instr.Assgn loadedReg (Rhs.Load obseq.TyVal.PTy ptrRes.reg)]
      emitM (cleanupInstrs ptrRes.cleanup)
      let tmpReg ← freshRegM
      emitM [Instr.Assgn tmpReg (borrowOffsetRhs kind loadedReg 0)]
      pure {
        result := { reg := tmpReg, cleanup := [loadedReg, tmpReg] },
        evidence := ptrChecked.evidence.map
          (fun ptrEv => PlaceToBorrowRegEvidence.deref ptrPlace ptrRes loadedReg tmpReg ptrEv)
      }

def placeToBorrowReg {Γ : Ctx} {τ : LayoutTy}
    (kind : RefKind) (p : Place Γ τ) : CompilerM PtrResult := do
  let checked ← placeToBorrowRegE kind p
  pure checked.result

inductive RExprToEvidence {Γ : Ctx}
    (dstPtr : Register) : {τ : LayoutTy} → RExpr Γ τ → Type where
  | constInit (value : Word) :
      RExprToEvidence dstPtr (.constInit value)
  | copy
      {τ : LayoutTy} (src : Place Γ τ) (srcRes : PtrResult)
      (srcEv : PlaceToRegEvidence RefKind.Shared src srcRes) :
      RExprToEvidence dstPtr (.copy src)
  | ref
      {σ : LayoutTy} (kind : RefKind) (src : Place Γ σ) (srcRes : PtrResult)
      (srcEv : PlaceToBorrowRegEvidence kind src srcRes) :
      RExprToEvidence dstPtr (.ref kind src)

inductive RExprEvidence {Γ : Ctx} :
    {τ : LayoutTy} → RExpr Γ τ → RExprResult → Type where
  | alloc
      {τ : LayoutTy} (expr : RExpr Γ τ)
      (reg : Register)
      (bodyEv : RExprToEvidence reg expr) :
      RExprEvidence expr { reg := reg }

def compileRExprToChecked
  (dstPtr : Register)
  {Γ : Ctx} {τ : LayoutTy}
  (expr : RExpr Γ τ) :
    CheckedEvidenceM Unit (fun _ => RExprToEvidence dstPtr expr) :=
  match expr with
  | .constInit value => do
      let _ ← CheckedCompilerM.lift
        (emitM [Instr.CStore obseq.TyVal.NatTy [Val.Dat value] dstPtr])
      pure { result := (), evidence := RExprToEvidence.constInit value }
  | .copy (τ := τ) src => do
      let srcOut ← placeToRegChecked RefKind.Shared src
      let srcRes := srcOut.result
      let _ ← CheckedCompilerM.lift
        (emitM ([Instr.Memcpy dstPtr srcRes.reg (layoutToTyVal τ)] ++ cleanupInstrs srcRes.cleanup))
      pure {
        result := (),
        evidence := RExprToEvidence.copy src srcRes srcOut.evidence
      }
  | .ref kind src => do
      let srcOut ← placeToBorrowRegChecked kind src
      let srcRes := srcOut.result
      let _ ← CheckedCompilerM.lift
        (emitM [Instr.RStore obseq.TyVal.PTy srcRes.reg dstPtr])
      pure {
        result := (),
        evidence := RExprToEvidence.ref kind src srcRes srcOut.evidence
      }

def compileRExprToE
  (dstPtr : Register)
  {Γ : Ctx} {τ : LayoutTy}
  (expr : RExpr Γ τ) :
    CompilerM (ResultWithOptEvidence Unit (fun _ => RExprToEvidence dstPtr expr)) :=
  match expr with
  | .constInit value => do
      emitM [Instr.CStore obseq.TyVal.NatTy [Val.Dat value] dstPtr]
      pure { result := (), evidence := some (RExprToEvidence.constInit value) }
  | .copy (τ := τ) src => do
      let srcChecked ← placeToRegE RefKind.Shared src
      let srcRes := srcChecked.result
      emitM ([Instr.Memcpy dstPtr srcRes.reg (layoutToTyVal τ)] ++ cleanupInstrs srcRes.cleanup)
      pure {
        result := (),
        evidence := srcChecked.evidence.map
          (fun srcEv => RExprToEvidence.copy src srcRes srcEv)
      }
  | .ref kind src => do
      let srcChecked ← placeToBorrowRegE kind src
      let srcRes := srcChecked.result
      emitM [Instr.RStore obseq.TyVal.PTy srcRes.reg dstPtr]
      pure {
        result := (),
        evidence := srcChecked.evidence.map
          (fun srcEv => RExprToEvidence.ref kind src srcRes srcEv)
      }

def compileRExprTo
  (dstPtr : Register)
  {Γ : Ctx} {τ : LayoutTy}
  (expr : RExpr Γ τ) : CompilerM Unit := do
  let checked ← compileRExprToE dstPtr expr
  pure checked.result

def compileRExprChecked
  {Γ : Ctx} {τ : LayoutTy}
  (expr : RExpr Γ τ) :
    CheckedEvidenceM RExprResult (RExprEvidence expr) := do
  let resReg ← CheckedCompilerM.lift freshRegM
  let _ ← CheckedCompilerM.lift
    (emitM [Instr.Assgn resReg (Rhs.Alloc (layoutToTyVal τ))])
  let bodyOut ← compileRExprToChecked resReg expr
  pure {
    result := { reg := resReg },
    evidence := RExprEvidence.alloc expr resReg bodyOut.evidence
  }

def compileRExprE
  {Γ : Ctx} {τ : LayoutTy}
  (expr : RExpr Γ τ) :
    CompilerM (ResultWithOptEvidence RExprResult (RExprEvidence expr)) := do
  let resReg ← freshRegM
  emitM [Instr.Assgn resReg (Rhs.Alloc (layoutToTyVal τ))]
  let bodyChecked ← compileRExprToE resReg expr
  pure {
    result := { reg := resReg },
    evidence := bodyChecked.evidence.map
      (fun bodyEv => RExprEvidence.alloc expr resReg bodyEv)
  }

def compileRExpr
  {Γ : Ctx} {τ : LayoutTy}
  (expr : RExpr Γ τ) : CompilerM RExprResult := do
  let checked ← compileRExprE expr
  pure checked.result

inductive StmtEvidence {Γ : Ctx} : Stmt Γ → Type where
  | halt :
      StmtEvidence .halt
  | assignLocal
      {τ : LayoutTy} (loc : Local Γ τ) (rhs : RExpr Γ τ)
      (dstRes : PtrResult)
      (dstEv : EnsureLocalEvidence loc dstRes)
      (rhsEv : RExprToEvidence dstRes.reg rhs) :
      StmtEvidence (.assign (.local loc) rhs)
  | assignPlace
      {τ : LayoutTy} (dst : Place Γ τ) (rhs : RExpr Γ τ)
      (dstRes : PtrResult)
      (dstEv : PlaceToRegEvidence RefKind.Mut dst dstRes)
      (rhsEv : RExprToEvidence dstRes.reg rhs) :
      StmtEvidence (.assign dst rhs)

def compileStmtChecked {Γ : Ctx} :
    (stmt : Stmt Γ) → CheckedEvidenceM Unit (fun _ => StmtEvidence stmt)
  | .halt => do
      let _ ← CheckedCompilerM.lift (emitM [Instr.Halt])
      pure { result := (), evidence := StmtEvidence.halt }
  | .assign (.local loc) rhs => do
      let dstOut ← CheckedCompilerM.lift (ensureLocalRegE loc)
      let dstRes := dstOut.result
      let rhsOut ← compileRExprToChecked dstRes.reg rhs
      pure {
        result := (),
        evidence := StmtEvidence.assignLocal loc rhs dstRes dstOut.evidence rhsOut.evidence
      }
  | .assign dst rhs => do
      let dstOut ← placeToRegChecked RefKind.Mut dst
      let dstRes := dstOut.result
      let rhsOut ← compileRExprToChecked dstRes.reg rhs
      let _ ← CheckedCompilerM.lift (emitM (cleanupInstrs dstRes.cleanup))
      pure {
        result := (),
        evidence := StmtEvidence.assignPlace dst rhs dstRes dstOut.evidence rhsOut.evidence
      }

def compileStmtsChecked {Γ : Ctx} : Prog Γ → CheckedCompilerM Unit
  | [] => pure ()
  | stmt :: rest => do
  let _ ← compileStmtChecked stmt
  compileStmtsChecked rest

def compileStmtE {Γ : Ctx} :
    (stmt : Stmt Γ) → CompilerM (ResultWithOptEvidence Unit (fun _ => StmtEvidence stmt))
  | .halt => do
      emitM [Instr.Halt]
      pure { result := (), evidence := some StmtEvidence.halt }
  | .assign (.local loc) rhs => do
      let dstChecked ← ensureLocalRegE loc
      let dstRes := dstChecked.result
      let rhsChecked ← compileRExprToE dstRes.reg rhs
      pure {
        result := (),
        evidence := rhsChecked.evidence.map
          (fun rhsEv => StmtEvidence.assignLocal loc rhs dstRes dstChecked.evidence rhsEv)
      }
  | .assign dst rhs => do
      let dstChecked ← placeToRegE RefKind.Mut dst
      let dstRes := dstChecked.result
      let rhsChecked ← compileRExprToE dstRes.reg rhs
      emitM (cleanupInstrs dstRes.cleanup)
      pure {
        result := (),
        evidence := match dstChecked.evidence, rhsChecked.evidence with
          | some dstEv, some rhsEv => some (StmtEvidence.assignPlace dst rhs dstRes dstEv rhsEv)
          | _, _ => none
      }

def compileStmt {Γ : Ctx} (stmt : Stmt Γ) : CompilerM Unit := do
  let checked ← compileStmtE stmt
  pure checked.result

theorem compileStmt_run_eq_compileStmtE
    {Γ : Ctx} (stmt : Stmt Γ) (cs : CompilerState) :
    CompilerM.run (compileStmt stmt) cs = CompilerM.run (compileStmtE stmt) cs :=
  rfl

theorem compileRExprTo_run_eq_compileRExprToE
    {Γ : Ctx} {τ : LayoutTy} (dstPtr : Register) (expr : RExpr Γ τ)
    (cs : CompilerState) :
    CompilerM.run (compileRExprTo dstPtr expr) cs =
      CompilerM.run (compileRExprToE dstPtr expr) cs :=
  rfl

theorem compileRExpr_run_eq_compileRExprE
    {Γ : Ctx} {τ : LayoutTy} (expr : RExpr Γ τ) (cs : CompilerState) :
    CompilerM.run (compileRExpr expr) cs = CompilerM.run (compileRExprE expr) cs :=
  rfl

def compileStmts {Γ : Ctx} : Prog Γ → CompilerM Unit
  | [] => pure ()
  | stmt :: rest => do
      compileStmt stmt
      compileStmts rest

def initialState (_Γ : Ctx) : CompilerState :=
  { nextReg := 0, nextLabel := 0, code := fun _ => none, placeRegMap := [] }

def compileProgFromChecked (cs0 : CompilerState) (prog : Prog Γ) : Except CompilerError TargetProg :=
  match CheckedCompilerM.value (compileStmtsChecked prog) cs0 with
  | .ok _ => .ok (CheckedCompilerM.run (compileStmtsChecked prog) cs0).code
  | .error err => .error err

def compileProg (prog : Prog Γ) : Except CompilerError TargetProg :=
  compileProgFromChecked (initialState Γ) prog

end obseq2.compile
