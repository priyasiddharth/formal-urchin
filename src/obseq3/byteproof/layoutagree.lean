import obseq3.byteproof.coverage
import obseq3.layout_agree

/-!
# Shape agreement implies the layout conditions

If every local's byte layout has its type's shape (`Agrees`), so does
every place's (`placeLayout_agrees`: a field of an agreeing tuple agrees
with the field's type, the pointee of an agreeing pointer with the
pointee type), and an agreeing `NatL`/`PtrL` layout is one leaf of the
layout's own size. So `PtrPlacesWF` and `LeafWF` follow from a check on
the locals alone, which the conformance harness runs on the loader's
layouts.
-/

namespace obseq3.byteproof

open obseq3 obseq3.bytes obseq3.proof
open obseq3.compileB

/-- Every local's byte layout has its type's shape. -/
def LocalsAgree {Γ : Ctx} (L : mirliteB.LayEnv Γ) : Prop :=
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
    ∀ {l : BLayout}, Agrees ρ l = true → Agrees τ (mirliteB.fieldLayout l path.indices) = true := by
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

theorem placeLayout_agrees {Γ : Ctx} {L : mirliteB.LayEnv Γ} (hL : LocalsAgree L)
    {τ : LayoutTy} (p : Place Γ τ) : Agrees τ (mirliteB.placeLayout L p) = true := by
  induction p with
  | «local» loc =>
      simp only [mirliteB.placeLayout]
      have := hL loc.idx
      rw [loc.hTy] at this
      exact this
  | proj b path ih => exact fieldLayout_agrees path ih
  | deref p ih =>
      simp only [mirliteB.placeLayout]
      split
      · rename_i q h_eq
        rw [h_eq] at ih
        simpa [Agrees] using ih
      · rename_i h_ne
        cases h : mirliteB.placeLayout L p with
        | ptr q => exact absurd h (h_ne q)
        | int _ => rw [h] at ih; simp [Agrees] at ih
        | tup _ _ _ _ => rw [h] at ih; simp [Agrees] at ih

theorem agrees_ptr_size {τ : LayoutTy} {l : BLayout} (h : Agrees (.PtrL τ) l = true) :
    l.size = ptrSize ∧ (mirliteB.leafKind l).size = l.size := by
  cases l with
  | ptr q => exact ⟨rfl, rfl⟩
  | int _ => simp [Agrees] at h
  | tup _ _ _ _ => simp [Agrees] at h

theorem agrees_nat_leaf {l : BLayout} (h : Agrees .NatL l = true) :
    (mirliteB.leafKind l).size = l.size := by
  cases l with
  | int n => rfl
  | ptr _ => simp [Agrees] at h
  | tup _ _ _ _ => simp [Agrees] at h

theorem LocalsAgree.ptrWF {Γ : Ctx} {L : mirliteB.LayEnv Γ} (hL : LocalsAgree L) :
    PtrPlacesWF L := fun p => (agrees_ptr_size (placeLayout_agrees hL p)).1

theorem LocalsAgree.leafWF {Γ : Ctx} {L : mirliteB.LayEnv Γ} (hL : LocalsAgree L) : LeafWF L :=
  ⟨fun p => (agrees_ptr_size (placeLayout_agrees hL p)).2,
   fun p => agrees_nat_leaf (placeLayout_agrees hL p)⟩

/-- **Byte-level compiler correctness, for layouts of their types' shape.**
    The hypothesis is a decidable check on the locals' layouts. -/
theorem compileB_correct_agrees {Γ : Ctx} (L : mirliteB.LayEnv Γ) (hL : LocalsAgree L)
    (prog : Prog Γ) (compProg : oseairL.Prog) (h_comp : compileProg L prog = .ok compProg)
    (n : Nat) {s_mir' : mirliteB.State MSB Γ}
    (h_run : mirliteB.runN MSB L n (mirliteB.State.initial MSB Γ) prog = .ok s_mir') :
    ∃ (ρt : TagRenameMap) (s_osea' : oseairL.State MSB) (m : Nat),
      oseairL.runN MSB m (oseairL.State.initial MSB) compProg = .Ok s_osea' ∧
      InvAtB L ρt s_mir' s_osea' (csAtB L (initialState Γ) prog s_mir'.pc) :=
  compileB_correct_all L hL.ptrWF hL.leafWF prog compProg h_comp n h_run

end obseq3.byteproof
