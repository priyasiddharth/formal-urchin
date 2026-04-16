-- This file contains the definitions of the types used in the formalization of the Urchin language.
import obseq.ListCompat
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
  | TyVal.TupTy tys1, TyVal.TupTy tys2 =>
    let _ : BEq TyVal := ⟨TyVal.beq⟩
    tys1 == tys2
  | _, _ => false

instance : BEq TyVal where
  beq := TyVal.beq

-- Helper function for structural recursion
def typeSizeAux : List TyVal → Word → Word
| [], acc => acc
| TyVal.NatTy :: rest, acc | TyVal.PTy :: rest,acc  => typeSizeAux rest (acc + 1)
| TyVal.TupTy nested :: rest, acc =>
    let nestedSize := typeSizeAux nested 0 -- Process the nested tuple first
    typeSizeAux rest (acc + nestedSize)    -- Add its size to the accumulator

-- Get size of type in words
def typeSize (ty : TyVal) : Nat :=
  match ty with
  | TyVal.NatTy | TyVal.PTy => 1
  | TyVal.TupTy tys => typeSizeAux tys 0

-- Function to get the type of a sub-place, given a composite base type
-- E.g.,place = 0.0.1, bty = [(Nat, (Nat, Nat, Nat)), [Nat, Nat]] will return (Nat, Nat, Nat)
def getPlaceTypeFromBase (place : Place) (bty : TyVal) : Option TyVal :=
  match place with
  | [] => some bty
  | _ =>
    let rec traverse (ty : TyVal) (path : Place) : Option TyVal :=
      match path with
      | [] =>
        dbg_trace s!"getPlaceTypeFromBase: final type={ty}"
        some ty
      | idx :: rest =>
        match ty with
        | TyVal.TupTy tys =>
          if h : idx < tys.length then
            let nextTy := tys.get ⟨idx, h⟩
            dbg_trace s!"getPlaceTypeFromBase: idx={idx}, nextTy={nextTy}, rest={rest}"
            traverse nextTy rest
          else
            dbg_trace s!"getPlaceTypeFromBase: idx={idx} out of bounds for tys={tys}"
            none
        | _ =>
          dbg_trace s!"getPlaceTypeFromBase: non-tuple type encountered: {ty}"
          none
    traverse bty place

/- LayoutTyVal -/
/- This is needed when codegening from MIR to OSEAIR -/

inductive LayoutTyVal
| NatTy : LayoutTyVal
| PTy : LayoutTyVal → LayoutTyVal
| TupTy : List LayoutTyVal → LayoutTyVal

partial def LayoutTyVal.repr : LayoutTyVal → Nat → Std.Format
  | LayoutTyVal.NatTy, _ => Std.Format.text "NatTy"
  | LayoutTyVal.PTy ty, d => Std.Format.text s!"PlaceTy({LayoutTyVal.repr ty d})"
  | LayoutTyVal.TupTy tys, d =>
    let _ : Repr LayoutTyVal := ⟨LayoutTyVal.repr⟩
    let tysStr := tys.map (fun t => Std.Format.pretty (LayoutTyVal.repr t d))
    Std.Format.text s!"TupTy({String.intercalate ", " tysStr})"

instance : Repr LayoutTyVal where
  reprPrec := LayoutTyVal.repr

partial def LayoutTyVal.beq : LayoutTyVal → LayoutTyVal → Bool
  | LayoutTyVal.NatTy, LayoutTyVal.NatTy => true
  | LayoutTyVal.PTy ty1, LayoutTyVal.PTy ty2 =>
    let _ : BEq LayoutTyVal := ⟨LayoutTyVal.beq⟩
    ty1 == ty2
  | LayoutTyVal.TupTy tys1, LayoutTyVal.TupTy tys2 =>
    let _ : BEq LayoutTyVal := ⟨LayoutTyVal.beq⟩
    tys1 == tys2
  | _, _ => false

instance : BEq LayoutTyVal where
  beq := LayoutTyVal.beq

-- Helper function for structural recursion
def layoutTypeSizeAux : List LayoutTyVal → Word → Word
  | [], acc => acc
  | ty :: rest, acc =>
    let sz :=
      match ty with
      | LayoutTyVal.NatTy => 1
      | LayoutTyVal.PTy _ => 1
      | LayoutTyVal.TupTy nested => layoutTypeSizeAux nested 0
    layoutTypeSizeAux rest (acc + sz)

-- Get size of LayoutTyVal type in words
def layoutTypeSize : LayoutTyVal → Nat
  | LayoutTyVal.NatTy => 1
  | LayoutTyVal.PTy _ => 1
  | LayoutTyVal.TupTy tys => layoutTypeSizeAux tys 0


def getLayoutTypeFromBase (subplace : Place) (bty : LayoutTyVal) : Option LayoutTyVal :=
  match subplace with
  | [] => some bty
  | _ =>
    let rec traverse (ty : LayoutTyVal) (subplace : Place) : Option LayoutTyVal :=
      match subplace with
      | [] => some ty
      /-| _idx :: [] =>
        match ty with
        | LayoutTyVal.TupTy tys => LayoutTyVal.TupTy tys
        | _ => ty-/
      | idx :: rest =>
        match ty with
        | LayoutTyVal.TupTy tys =>
          if h : idx < tys.length then
            let nextTy := tys.get ⟨idx, h⟩
            traverse nextTy rest
          else
            none
        | _ => none
    traverse bty subplace


-- Helper function for structural recursion
def layoutTyValToTyValAux : List LayoutTyVal → List TyVal
  | [] => []
  | ty :: rest =>
    let t :=
      match ty with
      | LayoutTyVal.NatTy => TyVal.NatTy
      | LayoutTyVal.PTy _ => TyVal.PTy
      | LayoutTyVal.TupTy nested => TyVal.TupTy (layoutTyValToTyValAux nested)
    t :: layoutTyValToTyValAux rest

def layoutTyToTy : LayoutTyVal → TyVal
  | LayoutTyVal.NatTy => TyVal.NatTy
  | LayoutTyVal.PTy _ => TyVal.PTy
  | LayoutTyVal.TupTy tys => TyVal.TupTy (layoutTyValToTyValAux tys)


  def isPtrType : LayoutTyVal → Bool
    | LayoutTyVal.PTy _ => true
    | _ => false
