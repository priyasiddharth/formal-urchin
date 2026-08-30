import obseq3.syntax
import obseq3.oseair

/-!
mirlite-v3 → OSEA-IR-v3 compiler: the Checked family of
`src/obseq2/compile.lean`, ported to the v3 syntax/target.

Differences from v2:
- the compiler is TOTAL on obseq3's statement/rvalue surface: `constInit`/
  `copy`/`ref`/`uninit`/`exposeAddr`/`fromExposed`/`ptrCast` (a Memcpy at
  PTy)/`ptrOffset` (delta pre-scaled to cells)/`refSlice` (runtime-length
  `BorrowRest`)/`halt`, `pushProtectors`/`popProtectors`, `alloc`/`dealloc`,
  `assignIf` (via `SkipIf`, the target's only — forward-only — branch);
  `CompilerError.unsupported` is retained for future source constructs;
- one `Rhs.Borrow` (kind, prot, mask, len) replaces the three v2 borrow
  forms; internal place-lowering borrows use `prot := false, mask := []`,
  while an `RExpr.ref`'s own prot/mask are carried into the final borrow;
- cleanup entries are `(Register × Nat)` pairs so `Die` knows the static
  length of the borrow it retires;
- deref lowering does NOT clean up the loaded pointer register: its tag
  was loaded from memory, not minted by the compiler, and dying it would
  pop the source program's own pointer out of the stacks (v2 died it —
  correct there only because v1 stacks were single-address).
-/

namespace obseq3.compile

open obseq3.oseair (Register Instr Rhs Val)

abbrev TargetProg := obseq3.oseair.Prog
abbrev PlaceInfo := Register × LayoutTy
abbrev PlaceRegMap := List (Nat × PlaceInfo)

abbrev layoutToTyVal : LayoutTy → TyVal := obseq.layoutToTyVal

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

abbrev pathOffset {src dst : LayoutTy} (p : PathTo src dst) : Nat :=
  p.offset

/-- Ensure the root local of an assignment destination is allocated,
    mirroring mirlite's `preparePlaceAssign`/`allocateRoot` (which
    allocates the root before evaluating the rhs — e.g. aggregate
    desugaring assigns `_x.0` before `_x` was ever written). -/
def ensurePlaceRoot {Γ : Ctx} : {τ : LayoutTy} → Place Γ τ → CompilerM Unit
  | _, .local loc => do
      let _ ← ensureLocalRegE loc
      pure ()
  | _, .proj base _ => ensurePlaceRoot base
  | _, .deref ptrPlace => ensurePlaceRoot ptrPlace

/-- Internal place-lowering borrow: no protector, no freeze mask (compiler
    temps are pushed and died with no intervening foreign access). -/
def borrowRhs (kind : RefKind) (len : Nat) (base : Register) (offset : Word) : Rhs :=
  Rhs.Borrow kind false [] len base offset

inductive PlaceToRegEvidence {Γ : Ctx} :
    RefKind → {τ : LayoutTy} → Place Γ τ → PtrResult → Type where
  | local
      {τ : LayoutTy} (loc : Local Γ τ) (cs : CompilerState)
      (reg : Register) (layout : LayoutTy)
      (h_lookup : getPlaceInfo cs loc.idx.1 = some (reg, layout)) :
      PlaceToRegEvidence kind (.local loc) { reg := reg, cleanup := [] }
  | projAssoc
      {ρ σ τ : LayoutTy} (b : Place Γ ρ) (q : PathTo ρ σ) (p : PathTo σ τ)
      (res : PtrResult)
      (ev : PlaceToRegEvidence kind (.proj b (q.append p)) res) :
      PlaceToRegEvidence kind (.proj (.proj b q) p) res
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
        { reg := tmpReg, cleanup := baseRes.cleanup ++ [(tmpReg, blockSize τ)] }
  | deref
      {σ : LayoutTy} (ptrPlace : Place Γ (obseq.LayoutTy.PtrL σ))
      (ptrRes : PtrResult) (loadedReg : Register)
      (ptrEv : PlaceToRegEvidence RefKind.Shared ptrPlace ptrRes) :
      PlaceToRegEvidence kind (.deref ptrPlace)
        { reg := loadedReg, cleanup := [] }

inductive PlaceToBorrowRegEvidence {Γ : Ctx} :
    RefKind → {τ : LayoutTy} → Place Γ τ → PtrResult → Type where
  | local
      {τ : LayoutTy} (loc : Local Γ τ) (baseRes : PtrResult) (tmpReg : Register)
      (baseEv : PlaceToRegEvidence kind (.local loc) baseRes) :
      PlaceToBorrowRegEvidence kind (.local loc)
        { reg := tmpReg, cleanup := [(tmpReg, blockSize τ)] }
  | projAssoc
      {ρ σ τ : LayoutTy} (b : Place Γ ρ) (q : PathTo ρ σ) (p : PathTo σ τ)
      (res : PtrResult)
      (ev : PlaceToBorrowRegEvidence kind (.proj b (q.append p)) res) :
      PlaceToBorrowRegEvidence kind (.proj (.proj b q) p) res
  | proj
      {σ τ : LayoutTy} (base : Place Γ σ) (path : PathTo σ τ)
      (baseRes : PtrResult) (tmpReg : Register)
      (baseEv : PlaceToRegEvidence kind base baseRes) :
      PlaceToBorrowRegEvidence kind (.proj base path)
        { reg := tmpReg, cleanup := baseRes.cleanup ++ [(tmpReg, blockSize τ)] }
  | deref
      {σ : LayoutTy} (ptrPlace : Place Γ (obseq.LayoutTy.PtrL σ))
      (ptrRes : PtrResult) (loadedReg tmpReg : Register)
      (ptrEv : PlaceToRegEvidence RefKind.Shared ptrPlace ptrRes) :
      PlaceToBorrowRegEvidence kind (.deref ptrPlace)
        { reg := tmpReg, cleanup := [(tmpReg, blockSize σ)] }

/-- Proof-facing place lowering. Invalid locals are rejected explicitly. -/
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
  -- REASSOCIATE nested projections: `s.1.1` must retag exactly its own
  -- field, not the whole intermediate place `s.1` — a wide intermediate
  -- Borrow(Mut) invalidates live borrows of sibling fields, which is
  -- legal Rust (the nested-projection divergence,
  -- `local/nested_proj_borrow`, 2026-08-27). One borrow, anchored at the
  -- chain root, at the composed offset, with the FINAL field's length.
  | .proj (.proj b q) p => do
      let out ← placeToRegChecked kind (.proj b (q.append p))
      pure {
        result := out.result,
        evidence := PlaceToRegEvidence.projAssoc b q p out.result out.evidence
      }
  | .proj (τ := τ) base path => do
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
          (emitM [Instr.Assgn tmpReg (borrowRhs kind (blockSize τ) baseRes.reg offset)])
        pure {
          result := { reg := tmpReg, cleanup := baseRes.cleanup ++ [(tmpReg, blockSize τ)] },
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
        result := { reg := loadedReg, cleanup := [] },
        evidence := PlaceToRegEvidence.deref ptrPlace ptrRes loadedReg ptrOut.evidence
      }
  termination_by p => p.depth
  decreasing_by all_goals (simp [Place.depth]; try omega)

def placeToBorrowRegChecked {Γ : Ctx} {τ : LayoutTy}
    (kind : RefKind) (prot : Bool) (mask : List Bool) :
    (p : Place Γ τ) → CheckedEvidenceM PtrResult (PlaceToBorrowRegEvidence kind p)
  | .local (τ := τ) loc => do
      let baseOut ← placeToRegChecked kind (.local loc)
      let baseRes := baseOut.result
      let tmpReg ← CheckedCompilerM.lift freshRegM
      let _ ← CheckedCompilerM.lift
        (emitM [Instr.Assgn tmpReg (Rhs.Borrow kind prot mask (blockSize τ) baseRes.reg 0)])
      pure {
        result := { reg := tmpReg, cleanup := [(tmpReg, blockSize τ)] },
        evidence := PlaceToBorrowRegEvidence.local loc baseRes tmpReg baseOut.evidence
      }
  -- REASSOCIATE nested projections (same divergence as `placeToRegChecked`:
  -- `&mut s.1.0` must not route through a wide Mut borrow of `s.1`).
  | .proj (.proj b q) p => do
      let out ← placeToBorrowRegChecked kind prot mask (.proj b (q.append p))
      pure {
        result := out.result,
        evidence := PlaceToBorrowRegEvidence.projAssoc b q p out.result out.evidence
      }
  | .proj (τ := τ) base path => do
      let baseOut ← placeToRegChecked kind base
      let baseRes := baseOut.result
      let offset := pathOffset path
      let tmpReg ← CheckedCompilerM.lift freshRegM
      let _ ← CheckedCompilerM.lift
        (emitM [Instr.Assgn tmpReg (Rhs.Borrow kind prot mask (blockSize τ) baseRes.reg offset)])
      pure {
        result := { reg := tmpReg, cleanup := baseRes.cleanup ++ [(tmpReg, blockSize τ)] },
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
        (emitM [Instr.Assgn tmpReg (Rhs.Borrow kind prot mask (blockSize τ) loadedReg 0)])
      pure {
        result := { reg := tmpReg, cleanup := [(tmpReg, blockSize τ)] },
        evidence := PlaceToBorrowRegEvidence.deref ptrPlace ptrRes loadedReg tmpReg ptrOut.evidence
      }
  termination_by p => p.depth
  decreasing_by all_goals (simp [Place.depth]; try omega)

inductive RExprToEvidence {Γ : Ctx}
    (dstPtr : Register) : {τ : LayoutTy} → RExpr Γ τ → Type where
  | constInit (value : Word) :
      RExprToEvidence dstPtr (.constInit value)
  | copy
      {τ : LayoutTy} (src : Place Γ τ) (srcRes : PtrResult)
      (srcEv : PlaceToRegEvidence RefKind.Shared src srcRes) :
      RExprToEvidence dstPtr (.copy src)
  | ref
      {σ : LayoutTy} (kind : RefKind) (prot : Bool) (mask : List Bool)
      (src : Place Γ σ) (srcRes : PtrResult)
      (srcEv : PlaceToBorrowRegEvidence kind src srcRes) :
      RExprToEvidence dstPtr (.ref kind prot mask src)
  | uninit {τ : LayoutTy} :
      RExprToEvidence dstPtr (.uninit (τ := τ))
  | exposeAddr
      {σ : LayoutTy} (src : Place Γ (obseq.LayoutTy.PtrL σ)) (srcRes : PtrResult)
      (srcEv : PlaceToRegEvidence RefKind.Shared src srcRes) :
      RExprToEvidence dstPtr (.exposeAddr src)
  | fromExposed
      {τ : LayoutTy} (src : Place Γ obseq.LayoutTy.NatL) (srcRes : PtrResult)
      (srcEv : PlaceToRegEvidence RefKind.Shared src srcRes) :
      RExprToEvidence dstPtr (.fromExposed (τ := τ) src)
  | ptrCast
      {σ τ : LayoutTy} (src : Place Γ (obseq.LayoutTy.PtrL σ)) (srcRes : PtrResult)
      (srcEv : PlaceToRegEvidence RefKind.Shared src srcRes) :
      RExprToEvidence dstPtr (.ptrCast (τ := τ) src)
  | ptrOffset
      {σ τ : LayoutTy} (src : Place Γ (obseq.LayoutTy.PtrL σ)) (delta : Int)
      (srcRes : PtrResult)
      (srcEv : PlaceToRegEvidence RefKind.Shared src srcRes) :
      RExprToEvidence dstPtr (.ptrOffset (τ := τ) src delta)
  | refSlice
      {σ τ : LayoutTy} (kind : RefKind) (prot : Bool)
      (src : Place Γ (obseq.LayoutTy.PtrL σ)) (srcRes : PtrResult)
      (srcEv : PlaceToRegEvidence RefKind.Shared src srcRes) :
      RExprToEvidence dstPtr (.refSlice (τ := τ) kind prot src)

/-- The source-side lowering of an rhs: everything EXCEPT the final
    store through the destination register — the loads, borrows, temp
    assignments, and any src cleanups that may run before the store.
    Returned: the store instruction(s) as a function of the eventual
    destination register, the cleanups that must run AFTER the store
    (a copy's src borrow must survive its own `Memcpy`), and the
    evidence factory.

    This split is what lets `compileStmtChecked`'s assign-PLACE arm use
    MIR's lowering order — rhs first, then the destination — so no dst
    temporary `Borrow` is live while rhs code runs (the d34
    lowering-order bug, 2026-08-28). -/
structure RhsPre (Γ : Ctx) (τ : LayoutTy) (expr : RExpr Γ τ) where
  store : Register → List Instr
  postCleanup : List (Register × Nat)
  ev : (dstPtr : Register) → RExprToEvidence dstPtr expr

def compileRExprPreChecked
  {Γ : Ctx} {τ : LayoutTy} :
    (expr : RExpr Γ τ) → CheckedCompilerM (RhsPre Γ τ expr)
  | .constInit value =>
      pure {
        store := fun dstPtr => [Instr.CStore obseq.TyVal.NatTy [Val.Dat value] dstPtr],
        postCleanup := [],
        ev := fun _ => RExprToEvidence.constInit value
      }
  | .copy (τ := τ) src => do
      -- Rust materializes the copied value into a TEMPORARY before the
      -- destination place is evaluated (`_3 = (*_2); (*_1) = move _3`),
      -- and so do we: the READ happens here, in the rhs pre-phase, and
      -- only the write is deferred to the store. Emitting the read as a
      -- `Memcpy` at store time instead put it AFTER the destination
      -- lowering's own pointer reads, which is observable under Stacked
      -- Borrows (a chain read pops the source's tag) — see
      -- notes/2026-08-29-copy-nonlocal-dst-order.md. The temp is a
      -- REGISTER, not an allocation: registers hold whole value lists,
      -- so nothing perturbs the allocator watermarks.
      let srcOut ← placeToRegChecked RefKind.Shared src
      let srcRes := srcOut.result
      let tmpReg ← CheckedCompilerM.lift freshRegM
      let _ ← CheckedCompilerM.lift
        (emitM ([Instr.Assgn tmpReg (Rhs.Load (layoutToTyVal τ) srcRes.reg)]
          ++ cleanupInstrs srcRes.cleanup))
      pure {
        store := fun dstPtr => [Instr.RStore (layoutToTyVal τ) tmpReg dstPtr],
        postCleanup := [],
        ev := fun _ => RExprToEvidence.copy src srcRes srcOut.evidence
      }
  | .ref kind prot mask src => do
      let srcOut ← placeToBorrowRegChecked kind prot mask src
      let srcRes := srcOut.result
      pure {
        store := fun dstPtr => [Instr.RStore obseq.TyVal.PTy srcRes.reg dstPtr],
        postCleanup := [],
        ev := fun _ => RExprToEvidence.ref kind prot mask src srcRes srcOut.evidence
      }
  | .uninit =>
      -- mirlite fills the destination with `blockSize τ` undef cells via a
      -- useMut write; CStore of Undef values is the same event stream
      pure {
        store := fun dstPtr =>
          [Instr.CStore (layoutToTyVal τ) (List.replicate (blockSize τ) Val.Undef) dstPtr],
        postCleanup := [],
        ev := fun _ => RExprToEvidence.uninit
      }
  | .exposeAddr src => do
      let srcOut ← placeToRegChecked RefKind.Shared src
      let srcRes := srcOut.result
      let tmpReg ← CheckedCompilerM.lift freshRegM
      let _ ← CheckedCompilerM.lift
        (emitM ([Instr.Assgn tmpReg (Rhs.ExposeAddr srcRes.reg)]
          ++ cleanupInstrs srcRes.cleanup))
      pure {
        store := fun dstPtr => [Instr.RStore obseq.TyVal.NatTy tmpReg dstPtr],
        postCleanup := [],
        ev := fun _ => RExprToEvidence.exposeAddr src srcRes srcOut.evidence
      }
  | .fromExposed src => do
      let srcOut ← placeToRegChecked RefKind.Shared src
      let srcRes := srcOut.result
      let tmpReg ← CheckedCompilerM.lift freshRegM
      let _ ← CheckedCompilerM.lift
        (emitM ([Instr.Assgn tmpReg (Rhs.FromExposed srcRes.reg)]
          ++ cleanupInstrs srcRes.cleanup))
      pure {
        store := fun dstPtr => [Instr.RStore obseq.TyVal.PTy tmpReg dstPtr],
        postCleanup := [],
        ev := fun _ => RExprToEvidence.fromExposed src srcRes srcOut.evidence
      }
  | .ptrCast src => do
      -- tag-preserving type-punning cast = a one-cell copy with an SB
      -- read, which is exactly Memcpy at PTy
      let srcOut ← placeToRegChecked RefKind.Shared src
      let srcRes := srcOut.result
      pure {
        store := fun dstPtr => [Instr.Memcpy dstPtr srcRes.reg obseq.TyVal.PTy],
        postCleanup := srcRes.cleanup,
        ev := fun _ => RExprToEvidence.ptrCast src srcRes srcOut.evidence
      }
  | .ptrOffset (σ := σ) src delta => do
      -- delta is in pointees of the SOURCE type; pre-scale to cells
      let srcOut ← placeToRegChecked RefKind.Shared src
      let srcRes := srcOut.result
      let tmpReg ← CheckedCompilerM.lift freshRegM
      let _ ← CheckedCompilerM.lift
        (emitM ([Instr.Assgn tmpReg (Rhs.PtrOffset srcRes.reg (delta * (blockSize σ : Int)))]
          ++ cleanupInstrs srcRes.cleanup))
      pure {
        store := fun dstPtr => [Instr.RStore obseq.TyVal.PTy tmpReg dstPtr],
        postCleanup := [],
        ev := fun _ => RExprToEvidence.ptrOffset src delta srcRes srcOut.evidence
      }
  | .refSlice kind prot src => do
      let srcOut ← placeToRegChecked RefKind.Shared src
      let srcRes := srcOut.result
      let tmpReg ← CheckedCompilerM.lift freshRegM
      let _ ← CheckedCompilerM.lift
        (emitM ([Instr.Assgn tmpReg (Rhs.BorrowRest kind prot srcRes.reg)]
          ++ cleanupInstrs srcRes.cleanup))
      pure {
        store := fun dstPtr => [Instr.RStore obseq.TyVal.PTy tmpReg dstPtr],
        postCleanup := [],
        ev := fun _ => RExprToEvidence.refSlice kind prot src srcRes srcOut.evidence
      }

/-- Store-through-dst rhs lowering: the pre phase followed by the store
    and the post-store cleanups. The instruction stream is UNCHANGED
    from before the 2026-08-28 split for every rhs; only the assign-
    PLACE arm of `compileStmtChecked` interleaves differently. -/
def compileRExprToChecked
  (dstPtr : Register)
  {Γ : Ctx} {τ : LayoutTy}
  (expr : RExpr Γ τ) :
    CheckedEvidenceM Unit (fun _ => RExprToEvidence dstPtr expr) := do
  let pre ← compileRExprPreChecked expr
  let _ ← CheckedCompilerM.lift (emitM (pre.store dstPtr))
  let _ ← CheckedCompilerM.lift (emitM (cleanupInstrs pre.postCleanup))
  pure { result := (), evidence := pre.ev dstPtr }

/-- Evidence-free twin of `compileStmtChecked`'s two assign cases (kept in
    sync with them), for use as the guarded block of `assignIf`. -/
def compileAssignChecked {Γ : Ctx} {τ : LayoutTy}
    (dst : Place Γ τ) (rhs : RExpr Γ τ) : CheckedCompilerM Unit :=
  match dst with
  | .local loc => do
      let dstOut ← CheckedCompilerM.lift (ensureLocalRegE loc)
      let _ ← compileRExprToChecked dstOut.result.reg rhs
      pure ()
  | dst => do
      let _ ← CheckedCompilerM.lift (ensurePlaceRoot dst)
      let pre ← compileRExprPreChecked rhs
      let dstOut ← placeToRegChecked RefKind.Mut dst
      let _ ← CheckedCompilerM.lift (emitM (pre.store dstOut.result.reg))
      let _ ← CheckedCompilerM.lift (emitM (cleanupInstrs pre.postCleanup))
      let _ ← CheckedCompilerM.lift (emitM (cleanupInstrs dstOut.result.cleanup))
      pure ()

/-- Emit `SkipIf discrReg val n` followed by `body`, where `n` is the
    body's emitted length — measured by a dry-run compilation from the
    current state. The dry run and the real run start from the same
    `nextReg`/`placeRegMap`, and instructions carry only registers and
    *relative* skips, so both runs emit identical instruction sequences;
    only the start label differs. A body that fails to compile rejects
    the whole statement without emitting anything. -/
def emitSkipIfAround (discrReg : Register) (val : Word)
    (body : CheckedCompilerM Unit) : CheckedCompilerM Unit :=
  ⟨fun cs =>
    let probe := body.toCompilerM cs
    match probe.1 with
    | .error err => (.error err, ⟨cs, StateIncr.refl cs⟩)
    | .ok _ =>
      let bodyLen := probe.2.1.nextLabel - cs.nextLabel
      let cs1 := emit cs [Instr.SkipIf discrReg val bodyLen]
      let real := body.toCompilerM cs1
      (real.1, ⟨real.2.1, (emit_state_incr cs [Instr.SkipIf discrReg val bodyLen]).trans real.2.2⟩)⟩

/-- Lower an `AllocLen` to a register holding the fresh heap pointer.
    `const n` → `AllocN`; `fromPlace p` → lower `p` (Shared) and emit
    `AllocDyn`, whose in-instruction length read mirrors mirlite's
    `readAllocLen` SB read. -/
def compileAllocLenChecked {Γ : Ctx} (elemTy : TyVal) :
    AllocLen Γ → CheckedCompilerM Register
  | .const n => do
      let tmpReg ← CheckedCompilerM.lift freshRegM
      let _ ← CheckedCompilerM.lift (emitM [Instr.Assgn tmpReg (Rhs.AllocN elemTy n)])
      pure tmpReg
  | .fromPlace p => do
      let lenOut ← placeToRegChecked RefKind.Shared p
      let tmpReg ← CheckedCompilerM.lift freshRegM
      let _ ← CheckedCompilerM.lift
        (emitM ([Instr.Assgn tmpReg (Rhs.AllocDyn elemTy lenOut.result.reg)]
          ++ cleanupInstrs lenOut.result.cleanup))
      pure tmpReg

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
  | pushProtectors :
      StmtEvidence .pushProtectors
  | popProtectors :
      StmtEvidence .popProtectors
  | assignIf
      {τ : LayoutTy} (discr : Place Γ obseq.LayoutTy.NatL) (val : Word)
      (dst : Place Γ τ) (rhs : RExpr Γ τ) :
      StmtEvidence (.assignIf discr val dst rhs)
  | alloc
      {τ : LayoutTy} (dst : Place Γ (obseq.LayoutTy.PtrL τ)) (len : AllocLen Γ) :
      StmtEvidence (.alloc dst len)
  | dealloc
      {τ : LayoutTy} (dst : Place Γ (obseq.LayoutTy.PtrL τ)) :
      StmtEvidence (.dealloc dst)

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
      -- MIR's lowering order (the d34 fix): rhs SOURCE code first, then
      -- the destination lowering, then the store — no dst temporary
      -- `Borrow` is live while rhs code runs
      let _ ← CheckedCompilerM.lift (ensurePlaceRoot dst)
      let pre ← compileRExprPreChecked rhs
      let dstOut ← placeToRegChecked RefKind.Mut dst
      let dstRes := dstOut.result
      let _ ← CheckedCompilerM.lift (emitM (pre.store dstRes.reg))
      let _ ← CheckedCompilerM.lift (emitM (cleanupInstrs pre.postCleanup))
      let _ ← CheckedCompilerM.lift (emitM (cleanupInstrs dstRes.cleanup))
      pure {
        result := (),
        evidence := StmtEvidence.assignPlace dst rhs dstRes dstOut.evidence
          (pre.ev dstRes.reg)
      }
  | .pushProtectors => do
      let _ ← CheckedCompilerM.lift (emitM [Instr.PushProt])
      pure { result := (), evidence := StmtEvidence.pushProtectors }
  | .popProtectors => do
      let _ ← CheckedCompilerM.lift (emitM [Instr.PopProt])
      pure { result := (), evidence := StmtEvidence.popProtectors }
  | .alloc (τ := τ) (.local loc) len => do
      -- dst root first (mirlite's preparePlaceAssign order), then the
      -- length read + heap own, then the pointer store
      let dstOut ← CheckedCompilerM.lift (ensureLocalRegE loc)
      let allocReg ← compileAllocLenChecked (layoutToTyVal τ) len
      let _ ← CheckedCompilerM.lift
        (emitM [Instr.RStore obseq.TyVal.PTy allocReg dstOut.result.reg])
      pure { result := (), evidence := StmtEvidence.alloc (.local loc) len }
  | .alloc (τ := τ) dst len => do
      let _ ← CheckedCompilerM.lift (ensurePlaceRoot dst)
      let dstOut ← placeToRegChecked RefKind.Mut dst
      let allocReg ← compileAllocLenChecked (layoutToTyVal τ) len
      let _ ← CheckedCompilerM.lift
        (emitM ([Instr.RStore obseq.TyVal.PTy allocReg dstOut.result.reg]
          ++ cleanupInstrs dstOut.result.cleanup))
      pure { result := (), evidence := StmtEvidence.alloc dst len }
  | .dealloc dst => do
      -- Load performs the pointer-cell read mirlite's dealloc does;
      -- Dealloc checks offset 0 against the stored value and retires
      -- the allocation
      let pOut ← placeToRegChecked RefKind.Shared dst
      let loadedReg ← CheckedCompilerM.lift freshRegM
      let _ ← CheckedCompilerM.lift
        (emitM ([Instr.Assgn loadedReg (Rhs.Load obseq.TyVal.PTy pOut.result.reg)]
          ++ cleanupInstrs pOut.result.cleanup
          ++ [Instr.Dealloc loadedReg]))
      pure { result := (), evidence := StmtEvidence.dealloc dst }
  | .assignIf discr val dst rhs => do
      -- discriminant lowering is event-free for the corpus shapes (enum
      -- field 0 → projZero; locals → register lookup); any temp borrows
      -- die BEFORE the SkipIf — safe because SkipIf performs no SB access
      let discrOut ← placeToRegChecked RefKind.Shared discr
      let _ ← CheckedCompilerM.lift (emitM (cleanupInstrs discrOut.result.cleanup))
      emitSkipIfAround discrOut.result.reg val (compileAssignChecked dst rhs)
      pure { result := (), evidence := StmtEvidence.assignIf discr val dst rhs }

def compileStmtsChecked {Γ : Ctx} : Prog Γ → CheckedCompilerM Unit
  | [] => pure ()
  | stmt :: rest => do
  let _ ← compileStmtChecked stmt
  compileStmtsChecked rest

def initialState (_Γ : Ctx) : CompilerState :=
  { nextReg := 0, nextLabel := 0, code := fun _ => none, placeRegMap := [] }

def compileProgFromChecked (cs0 : CompilerState) (prog : Prog Γ) : Except CompilerError TargetProg :=
  match CheckedCompilerM.value (compileStmtsChecked prog) cs0 with
  | .ok _ => .ok (CheckedCompilerM.run (compileStmtsChecked prog) cs0).code
  | .error err => .error err

def compileProg (prog : Prog Γ) : Except CompilerError TargetProg :=
  compileProgFromChecked (initialState Γ) prog

/-- Per-source-statement label ranges `[start, end)` of the emitted code,
    computed by replaying the same per-statement compilation fold. Only
    meaningful when `compileProg` succeeded (the fold matches it exactly);
    used by the differential harness to attribute a target-UB label to a
    source statement. -/
def stmtLabelRanges {Γ : Ctx} (prog : Prog Γ) : List (Nat × Nat) :=
  (prog.foldl
    (fun (acc : List (Nat × Nat) × CompilerState) stmt =>
      let cs' := CheckedCompilerM.run (compileStmtChecked stmt) acc.2
      (acc.1 ++ [(acc.2.nextLabel, cs'.nextLabel)], cs'))
    ([], initialState Γ)).1

/-- Total number of emitted labels (fuel bound for running the target). -/
def emittedLabels {Γ : Ctx} (prog : Prog Γ) : Nat :=
  (CheckedCompilerM.run (compileStmtsChecked prog) (initialState Γ)).nextLabel

end obseq3.compile
