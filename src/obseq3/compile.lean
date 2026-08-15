import obseq3.syntax
import obseq3.oseair

/-!
mirlite-v3 → OSEA-IR-v3 compiler: the Checked family of
`src/obseq2/compile.lean`, ported to the v3 syntax/target.

Differences from v2:
- proof-core subset plus protector frames: `constInit`/`copy`/`ref`/
  `halt`/`pushProtectors`/`popProtectors` compile; every other
  statement/rvalue form is rejected with `CompilerError.unsupported`;
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
  | .ref kind prot mask src => do
      let srcOut ← placeToBorrowRegChecked kind prot mask src
      let srcRes := srcOut.result
      let _ ← CheckedCompilerM.lift
        (emitM [Instr.RStore obseq.TyVal.PTy srcRes.reg dstPtr])
      pure {
        result := (),
        evidence := RExprToEvidence.ref kind prot mask src srcRes srcOut.evidence
      }
  | .ptrCast _ => CheckedCompilerM.throw (.unsupported "rvalue ptrCast")
  | .ptrOffset _ _ => CheckedCompilerM.throw (.unsupported "rvalue ptrOffset")
  | .refSlice _ _ _ => CheckedCompilerM.throw (.unsupported "rvalue refSlice")
  | .exposeAddr _ => CheckedCompilerM.throw (.unsupported "rvalue exposeAddr")
  | .fromExposed _ => CheckedCompilerM.throw (.unsupported "rvalue fromExposed")
  | .uninit => CheckedCompilerM.throw (.unsupported "rvalue uninit")

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
      let _ ← CheckedCompilerM.lift (ensurePlaceRoot dst)
      let dstOut ← placeToRegChecked RefKind.Mut dst
      let dstRes := dstOut.result
      let rhsOut ← compileRExprToChecked dstRes.reg rhs
      let _ ← CheckedCompilerM.lift (emitM (cleanupInstrs dstRes.cleanup))
      pure {
        result := (),
        evidence := StmtEvidence.assignPlace dst rhs dstRes dstOut.evidence rhsOut.evidence
      }
  | .pushProtectors => do
      let _ ← CheckedCompilerM.lift (emitM [Instr.PushProt])
      pure { result := (), evidence := StmtEvidence.pushProtectors }
  | .popProtectors => do
      let _ ← CheckedCompilerM.lift (emitM [Instr.PopProt])
      pure { result := (), evidence := StmtEvidence.popProtectors }
  | .assignIf _ _ _ _ => CheckedCompilerM.throw (.unsupported "stmt assignIf")
  | .alloc _ _ => CheckedCompilerM.throw (.unsupported "stmt alloc")
  | .dealloc _ => CheckedCompilerM.throw (.unsupported "stmt dealloc")

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
