import obseq.types
import obseq3.sb

namespace obseq3

abbrev TyVal := obseq.TyVal
abbrev LayoutTy := obseq.LayoutTy

abbrev typeSize : TyVal → Nat := obseq.typeSize
abbrev typeSizeList : List TyVal → Nat := obseq.typeSizeList

abbrev layoutSize : LayoutTy → Nat := obseq.layoutSize
abbrev layoutSizeList : List LayoutTy → Nat := obseq.layoutSizeList

def blockSize (layout : LayoutTy) : Nat :=
  layoutSize layout

/- Decidable equality for `LayoutTy` (obseq derives only `BEq`).
   Needed by the conformance elaborator to produce `Local`/`Place`
   type-equality proofs from runtime-parsed programs. -/
mutual
  def layoutDecEq : (a b : LayoutTy) → Decidable (a = b)
    | .NatL, .NatL => .isTrue rfl
    | .NatL, .PtrL _ | .NatL, .TupL _ => .isFalse (by intro h; cases h)
    | .PtrL _, .NatL | .PtrL _, .TupL _ => .isFalse (by intro h; cases h)
    | .TupL _, .NatL | .TupL _, .PtrL _ => .isFalse (by intro h; cases h)
    | .PtrL a, .PtrL b =>
        match layoutDecEq a b with
        | .isTrue h => .isTrue (by rw [h])
        | .isFalse h => .isFalse (by intro hc; cases hc; exact h rfl)
    | .TupL as, .TupL bs =>
        match layoutListDecEq as bs with
        | .isTrue h => .isTrue (by rw [h])
        | .isFalse h => .isFalse (by intro hc; cases hc; exact h rfl)

  def layoutListDecEq : (as bs : List LayoutTy) → Decidable (as = bs)
    | [], [] => .isTrue rfl
    | [], _ :: _ => .isFalse (by intro h; cases h)
    | _ :: _, [] => .isFalse (by intro h; cases h)
    | a :: as, b :: bs =>
        match layoutDecEq a b, layoutListDecEq as bs with
        | .isTrue h₁, .isTrue h₂ => .isTrue (by rw [h₁, h₂])
        | .isFalse h₁, _ => .isFalse (by intro hc; cases hc; exact h₁ rfl)
        | _, .isFalse h₂ => .isFalse (by intro hc; cases hc; exact h₂ rfl)
end

instance : DecidableEq LayoutTy := layoutDecEq

end obseq3
