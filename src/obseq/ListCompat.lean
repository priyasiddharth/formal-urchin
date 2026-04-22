import Init.Data.List.Lemmas

namespace List

/-- Compatibility alias for older code that used `List.get?`. -/
def get? (xs : List α) (i : Nat) : Option α :=
  xs[i]?

@[simp] theorem get?_eq_some_iff {xs : List α} {i : Nat} {a : α} :
    xs.get? i = some a ↔ ∃ h : i < xs.length, xs.get ⟨i, h⟩ = a := by
  simpa [List.get?] using
    (_root_.getElem?_eq_some_iff (c := xs) (i := i) (e := a))

@[simp] theorem get?_eq_none_iff {xs : List α} {i : Nat} :
    xs.get? i = none ↔ xs.length ≤ i := by
  simpa [List.get?] using
    (_root_.getElem?_eq_none_iff xs i)

end List
