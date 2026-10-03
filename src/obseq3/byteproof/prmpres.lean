import obseq3.byteproof.fragment

/-!
# Compile-only: the place map changes only at a root allocation

`placeRegMap` grows only in `ensureLocalRegE` (a fresh root's `Alloc`).
Every other piece of the byte compiler — place lowering, borrows, reads,
every rvalue's pre-phase — leaves it as it found it (`PrmPres`). The
guarded assignment needs this for the branch NOT taken, where the source
never evaluates the body and so no value package speaks for it.
-/

namespace obseq3.byteproof

open obseq3 obseq3.bytes obseq3.proof
open obseq3.mirlite (MemValue Binding Env PlaceRes)
open obseq3.oseair (Val Register)
open obseq3.compileB

/-- A computation that leaves the place map alone. -/
def PrmPres {α : Type} (m : CheckedCompilerM α) : Prop :=
  ∀ cs, (CheckedCompilerM.run m cs).placeRegMap = cs.placeRegMap

theorem PrmPres.pure {α : Type} (a : α) : PrmPres (pure a : CheckedCompilerM α) := fun _ => rfl

theorem PrmPres.fresh : PrmPres (CheckedCompilerM.lift freshRegM) := fun _ => rfl

theorem PrmPres.emit (is : List oseairL.Instr) :
    PrmPres (CheckedCompilerM.lift (emitM is)) := fun _ => rfl

theorem PrmPres.bind {α β : Type} {m : CheckedCompilerM α} {f : α → CheckedCompilerM β}
    (hm : PrmPres m) (hf : ∀ a, PrmPres (f a)) : PrmPres (m >>= f) := by
  intro cs
  rw [CheckedCompilerM.run_bind]
  split
  · rw [hf _ _, hm cs]
  · exact hm cs

theorem placeToReg_prm {Γ : Ctx} {L : mirliteB.LayEnv Γ} :
    ∀ (n : Nat) {τ : LayoutTy} (p : Place Γ τ) (kind : RefKind), p.depth ≤ n →
      PrmPres (placeToRegChecked L kind p)
  | 0, _, p, _, h => by cases p <;> simp [Place.depth] at h
  | n + 1, _, .local loc, kind, _ => by
      intro cs
      simp only [CheckedCompilerM.run, CompilerM.run, placeToRegChecked]
      split <;> rfl
  | n + 1, _, .proj (.proj b q) p, kind, h => by
      intro cs
      rw [(placeToReg_assoc (L := L) kind b q p cs).1]
      exact placeToReg_prm n (.proj b (q.append p)) kind
        (by simp only [Place.depth] at h ⊢; omega) cs
  | n + 1, _, .proj (.local loc) f, kind, h => by
      intro cs
      rw [proj_eq f (fun _ _ _ h => by cases h)]
      refine PrmPres.bind (placeToReg_prm n (.local loc) kind
        (by simp only [Place.depth] at h ⊢; omega)) (fun a => ?_) cs
      dsimp only
      split
      · exact PrmPres.pure _
      · exact PrmPres.bind PrmPres.fresh fun _ => PrmPres.bind (PrmPres.emit _) fun _ => PrmPres.pure _
  | n + 1, _, .proj (.deref pp) f, kind, h => by
      intro cs
      rw [proj_eq f (fun _ _ _ h => by cases h)]
      refine PrmPres.bind (placeToReg_prm n (.deref pp) kind
        (by simp only [Place.depth] at h ⊢; omega)) (fun a => ?_) cs
      dsimp only
      split
      · exact PrmPres.pure _
      · exact PrmPres.bind PrmPres.fresh fun _ => PrmPres.bind (PrmPres.emit _) fun _ => PrmPres.pure _
  | n + 1, _, .deref q, kind, h => by
      intro cs
      have h_bind : placeToRegChecked L kind (.deref q)
          = (do
              let ptrOut ← placeToRegChecked L RefKind.Shared q
              let ptrRes := ptrOut.result
              let loadedReg ← CheckedCompilerM.lift freshRegM
              let _ ← CheckedCompilerM.lift
                (emitM [oseairL.Instr.Assgn loadedReg (oseairL.Rhs.Load (derefLoad L q) ptrRes.reg)])
              let _ ← CheckedCompilerM.lift (emitM (cleanupInstrs ptrRes.cleanup))
              pure {
                result := { reg := loadedReg, cleanup := [] },
                evidence := PlaceToRegEvidence.deref q ptrRes loadedReg ptrOut.evidence
              }) := by simp only [placeToRegChecked]
      rw [h_bind]
      exact PrmPres.bind (placeToReg_prm n q RefKind.Shared
        (by simp only [Place.depth] at h ⊢; omega)) (fun _ => PrmPres.bind PrmPres.fresh fun _ =>
          PrmPres.bind (PrmPres.emit _) fun _ => PrmPres.bind (PrmPres.emit _) fun _ =>
            PrmPres.pure _) cs

theorem placeToReg_prm' {Γ : Ctx} {L : mirliteB.LayEnv Γ} {τ : LayoutTy} (p : Place Γ τ)
    (kind : RefKind) : PrmPres (placeToRegChecked L kind p) :=
  placeToReg_prm p.depth p kind (Nat.le_refl _)

/-- Close a `PrmPres` goal built from binds of preserved pieces. -/
macro "prm_tac0" : tactic => `(tactic| repeat' (first
  | (exact PrmPres.pure _)
  | (exact PrmPres.fresh)
  | (exact PrmPres.emit _)
  | (exact placeToReg_prm' _ _)
  | (apply PrmPres.bind)
  | split
  | (dsimp only)
  | (intro _)))

theorem placeToBorrowReg_prm {Γ : Ctx} {L : mirliteB.LayEnv Γ} :
    ∀ (n : Nat) {τ : LayoutTy} (p : Place Γ τ) (kind : RefKind) (prot : Bool) (mask : List Bool),
      p.depth ≤ n → PrmPres (placeToBorrowRegChecked L kind prot mask p)
  | 0, _, p, _, _, _, h => by cases p <;> simp [Place.depth] at h
  | n + 1, _, .local loc, kind, prot, mask, _ => by
      simp only [placeToBorrowRegChecked]
      prm_tac0
  | n + 1, _, .proj (.proj b q) p, kind, prot, mask, h => by
      intro cs
      rw [(placeToBorrowReg_assoc (L := L) kind prot mask b q p cs).1]
      exact placeToBorrowReg_prm n (.proj b (q.append p)) kind prot mask
        (by simp only [Place.depth] at h ⊢; omega) cs
  | n + 1, _, .proj (.local loc) f, kind, prot, mask, _ => by
      simp only [placeToBorrowRegChecked]
      prm_tac0
  | n + 1, _, .proj (.deref pp) f, kind, prot, mask, _ => by
      simp only [placeToBorrowRegChecked]
      prm_tac0
  | n + 1, _, .deref q, kind, prot, mask, _ => by
      simp only [placeToBorrowRegChecked]
      prm_tac0

theorem placeToBorrowReg_prm' {Γ : Ctx} {L : mirliteB.LayEnv Γ} {τ : LayoutTy} (p : Place Γ τ)
    (kind : RefKind) (prot : Bool) (mask : List Bool) :
    PrmPres (placeToBorrowRegChecked L kind prot mask p) :=
  placeToBorrowReg_prm p.depth p kind prot mask (Nat.le_refl _)

theorem readToReg_prm {Γ : Ctx} {L : mirliteB.LayEnv Γ} {τ : LayoutTy} (p : Place Γ τ) :
    PrmPres (readToReg L p) := by
  simp only [readToReg]
  prm_tac0

theorem compileAllocLen_prm {Γ : Ctx} {L : mirliteB.LayEnv Γ} (pointee : BLayout)
    (len : AllocLen Γ) : PrmPres (compileAllocLenChecked L pointee len) := by
  cases len <;> simp only [compileAllocLenChecked, guardRead]
  · prm_tac0
  · exact PrmPres.bind (readToReg_prm _) fun _ => by prm_tac0

/-- `prm_tac0` with every preserved piece. -/
macro "prm_tac" : tactic => `(tactic| repeat' (first
  | (exact PrmPres.pure _)
  | (exact PrmPres.fresh)
  | (exact PrmPres.emit _)
  | (exact placeToReg_prm' _ _)
  | (exact placeToBorrowReg_prm' _ _ _ _)
  | (exact readToReg_prm _)
  | (exact compileAllocLen_prm _ _)
  | (apply PrmPres.bind)
  | split
  | (dsimp only)
  | (intro _)))

theorem compileRExprPre_prm {Γ : Ctx} {L : mirliteB.LayEnv Γ} (dstL : BLayout) {τ : LayoutTy}
    (rhs : RExpr Γ τ) : PrmPres (compileRExprPreChecked L dstL rhs) := by
  cases rhs <;> simp only [compileRExprPreChecked, readRhsPre] <;> prm_tac

end obseq3.byteproof
