import Lean.Data.AssocList

namespace accessperm
  abbrev Word := Nat
  -- Borrow stack
  abbrev BorrowStack := List Word -- Borrow stack as a list of `Nat` tags
  deriving instance Inhabited, Repr for BorrowStack

  abbrev SB:= Lean.AssocList (Word) (BorrowStack)
  deriving instance Inhabited for SB

  instance : Repr SB where
    reprPrec sb _ := repr sb.toList

    partial def SB.beq : SB → SB → Bool
      | Lean.AssocList.nil, Lean.AssocList.nil => true
      | Lean.AssocList.cons k1 v1 rest1, Lean.AssocList.cons k2 v2 rest2 =>
        let _ : BEq SB := ⟨SB.beq⟩
        k1 == k2 && v1 == v2 && rest1 == rest2
      | _, _ => false

    instance : BEq SB where
      beq := SB.beq

  structure AccessPerms where
    StackMap: SB
    NextTag: Word
  deriving Inhabited, Repr

  partial def AccessPerms.beq : AccessPerms → AccessPerms → Bool
    | ⟨sm1, nt1⟩, ⟨sm2, nt2⟩ =>
      sm1 == sm2 && nt1 == nt2

  instance : BEq AccessPerms where
    beq := AccessPerms.beq

  instance : Inhabited AccessPerms where
  default := { StackMap := Lean.AssocList.nil, NextTag := 0 }
end accessperm
