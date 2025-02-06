
inductive Even : Nat → Prop where  | zero : Even 0  | add_two : ∀k : Nat, Even k → Even (k + 2)

theorem Even_Iff (n : Nat) :  Even n ↔ n = 0 ∨ (∃m : Nat, n = m + 2 ∧ Even m) := by
  apply Iff.intro  {
    intro hn
    cases hn
    case zero => simp

    cases hn with
    | zero => simp
    | add_two k hk =>
      apply Or.inr
      apply Exists.intro k  simp [hk]
    }
    {
    intro hor  cases hor with
      | inl heq => simp [heq, Even.zero]
      | inr hex =>  cases hex with
        | intro k hand =>  cases hand with
          | intro heq hk =>  simp [heq, Even.add_two _ hk]
    }
