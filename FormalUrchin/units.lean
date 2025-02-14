-- This file contains the definitions of the types used in the formalization of the Urchin language.
import Lean.Data.AssocList

abbrev Word := Nat
abbrev BasePlace := Word
abbrev BasicBlock := Word
abbrev Place := List Word
abbrev Tag := Word
abbrev BB := Word
abbrev PC := Word
abbrev AddrStart := Word
abbrev Addr := Word

inductive TyVal
| NatTy : TyVal
| PTy : TyVal
| TupTy : List TyVal → TyVal

partial def TyVal.toString : TyVal → String
  | TyVal.NatTy => s!"NatTy"
  | TyVal.PTy => s!"PlaceTy"
  | TyVal.TupTy tys  =>
    let _ : ToString TyVal := ⟨TyVal.toString⟩
    s!"TupTy({String.intercalate ", " (tys.map toString)})"

instance : ToString TyVal where
  toString := TyVal.toString

partial def TyVal.beq : TyVal → TyVal → Bool
  | TyVal.NatTy, TyVal.NatTy => true
  | TyVal.PTy , TyVal.PTy => true
  | .TupTy (ty1 :: rest1), .TupTy (ty2::rest2) =>
    let _ : BEq TyVal := ⟨TyVal.beq⟩
    ty1 == ty2 && rest1 == rest2
  | _, _ => false

instance : BEq TyVal where
  beq := TyVal.beq
