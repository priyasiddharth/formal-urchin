import obseq3.proof.coverage
import obseq3.layout_agree

/-!
# Shape agreement implies the layout conditions

If every local's byte layout has its type's shape (`Agrees`), so does
every place's (`placeLayout_agrees`: a field of an agreeing tuple agrees
with the field's type, the pointee of an agreeing pointer with the
pointee type), and an agreeing `IntL`/`PtrL` layout is one leaf of the
layout's own size. So `PtrPlacesWF` and `LeafWF` follow from a check on
the locals alone, which the conformance harness runs on the loader's
layouts.
-/

namespace obseq3.proof

open obseq3 obseq3.bytes obseq3.proof
open obseq3.compile

/-- Every local's byte layout has its type's shape. -/
def LocalsAgree {Γ : Ctx} (L : mirlite.LayEnv Γ) : Prop :=
  ∀ i : Fin Γ.length, Agrees (Γ.get i) (L i) = true

theorem agreesList_getD : ∀ {ts : List LayoutTy} {fs : List BLayout},
    AgreesList ts fs = true → ∀ i : Fin ts.length, Agrees (ts.get i) (fs.getD i.1 default) = true
  | _ :: _, _ :: _, h, ⟨0, _⟩ => by
      simp only [AgreesList, Bool.and_eq_true] at h
      exact h.1
  | _ :: ts, _ :: fs, h, ⟨i + 1, hi⟩ => by
      simp only [AgreesList, Bool.and_eq_true] at h
      exact agreesList_getD h.2 ⟨i, Nat.lt_of_succ_lt_succ hi⟩
  | [], _, _, i => i.elim0
  | _ :: _, [], h, _ => by simp [AgreesList] at h

theorem fieldLayout_agrees {ρ τ : LayoutTy} (path : PathTo ρ τ) :
    ∀ {l : BLayout}, Agrees ρ l = true → Agrees τ (mirlite.fieldLayout l path.indices) = true := by
  induction path with
  | nil => intro l h; exact h
  | field idx tail ih =>
      intro l h
      cases l with
      | tup fs os sz al =>
          simp only [Agrees] at h
          exact ih (agreesList_getD h idx)
      | int _ => simp [Agrees] at h
      | ptr _ => simp [Agrees] at h

theorem placeLayout_agrees {Γ : Ctx} {L : mirlite.LayEnv Γ} (hL : LocalsAgree L)
    {τ : LayoutTy} (p : Place Γ τ) : Agrees τ (mirlite.placeLayout L p) = true := by
  induction p with
  | «local» loc =>
      simp only [mirlite.placeLayout]
      have := hL loc.idx
      rw [loc.hTy] at this
      exact this
  | proj b path ih => exact fieldLayout_agrees path ih
  | deref p ih =>
      simp only [mirlite.placeLayout]
      split
      · rename_i q h_eq
        rw [h_eq] at ih
        simpa [Agrees] using ih
      · rename_i h_ne
        cases h : mirlite.placeLayout L p with
        | ptr q => exact absurd h (h_ne q)
        | int _ => rw [h] at ih; simp [Agrees] at ih
        | tup _ _ _ _ => rw [h] at ih; simp [Agrees] at ih

theorem agrees_ptr_sizeB {τ : LayoutTy} {l : BLayout} (h : Agrees (.PtrL τ) l = true) :
    l.sizeB = ptrSizeB ∧ (mirlite.leafKind l).sizeB = l.sizeB := by
  cases l with
  | ptr q => exact ⟨rfl, rfl⟩
  | int _ => simp [Agrees] at h
  | tup _ _ _ _ => simp [Agrees] at h

theorem agrees_nat_leaf {t : IntTy} {l : BLayout} (h : Agrees (.IntL t) l = true) :
    (mirlite.leafKind l).sizeB = l.sizeB := by
  cases l with
  | int n => rfl
  | ptr _ => simp [Agrees] at h
  | tup _ _ _ _ => simp [Agrees] at h

theorem LocalsAgree.ptrWF {Γ : Ctx} {L : mirlite.LayEnv Γ} (hL : LocalsAgree L) :
    PtrPlacesWF L := fun p => (agrees_ptr_sizeB (placeLayout_agrees hL p)).1

theorem LocalsAgree.leafWF {Γ : Ctx} {L : mirlite.LayEnv Γ} (hL : LocalsAgree L) : LeafWF L :=
  ⟨fun p => (agrees_ptr_sizeB (placeLayout_agrees hL p)).2,
   fun p => agrees_nat_leaf (placeLayout_agrees hL p)⟩

/-- **Compiler correctness, for layouts of their types' shape.**
    The hypothesis is a decidable check on the locals' layouts. -/
theorem compile_correct_agrees {Γ : Ctx} (L : mirlite.LayEnv Γ) (hL : LocalsAgree L)
    (prog : Prog Γ) (compProg : oseair.Prog) (h_comp : compileProg L prog = .ok compProg)
    (n : Nat) {s_mir' : mirlite.State MSB Γ}
    (h_run : mirlite.runN MSB L n (mirlite.State.initial MSB Γ) prog = .ok s_mir') :
    ∃ (ρt : TagRenameMap) (s_osea' : oseair.State MSB) (m : Nat),
      oseair.runN MSB m (oseair.State.initial MSB) compProg = .Ok s_osea' ∧
      InvAtB L ρt s_mir' s_osea' (csAtB L (initialState Γ) prog s_mir'.pc) :=
  compile_correct_all L hL.ptrWF hL.leafWF prog compProg h_comp n h_run

end obseq3.proof
