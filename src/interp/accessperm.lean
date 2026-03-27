import Lean.Data.AssocList

namespace accessperm

abbrev Word := Nat

inductive RefKind
| Own (tag: Word)
| MutRef (tag: Word)
| Ref (tag: Word)
| RawPtr (tag: Word)
deriving Inhabited, Repr

instance : BEq RefKind where
  beq
    | RefKind.Own t1, RefKind.Own t2 => t1 == t2
    | RefKind.MutRef t1, RefKind.MutRef t2 => t1 == t2
    | RefKind.Ref t1, RefKind.Ref t2 => t1 == t2
    | RefKind.RawPtr t1, RefKind.RawPtr t2 => t1 == t2
    | _, _ => false

  -- Borrow stack
  abbrev BorrowStack := List RefKind -- Borrow stack as a list of `Nat` tags
  deriving instance Inhabited, Repr, BEq for BorrowStack

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

  def getRefKind (addr: Word) (tag : Word) (ap : AccessPerms) : Option RefKind :=
    match ap.StackMap.find? addr with
    | some borrowstack =>
      match borrowstack with
      | [] => none
      | borrowstack =>
        borrowstack.find? (fun rk =>
          match rk with
          | RefKind.Own t => t == tag
          | RefKind.MutRef t => t == tag
          | RefKind.Ref t => t == tag
          | RefKind.RawPtr t => t == tag
        )
    | _ => none
end accessperm
