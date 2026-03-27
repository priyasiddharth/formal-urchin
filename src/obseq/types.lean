namespace obseq

inductive TyVal
| NatTy
| PTy
| TupTy (tys : List TyVal)
deriving Repr, BEq, Inhabited

inductive LayoutTy
| NatL
| PtrL (inner : LayoutTy)
| TupL (tys : List LayoutTy)
deriving Repr, BEq, Inhabited

instance : ToString TyVal where
  toString t := reprStr t

instance : ToString LayoutTy where
  toString t := reprStr t

mutual
  def typeSize : TyVal → Nat
  | TyVal.NatTy => 1
  | TyVal.PTy => 1
  | TyVal.TupTy tys => typeSizeList tys

  def typeSizeList : List TyVal → Nat
  | [] => 0
  | ty :: tys => typeSize ty + typeSizeList tys
end

mutual
  def layoutSize : LayoutTy → Nat
  | LayoutTy.NatL => 1
  | LayoutTy.PtrL _ => 1
  | LayoutTy.TupL tys => layoutSizeList tys

  def layoutSizeList : List LayoutTy → Nat
  | [] => 0
  | ty :: tys => layoutSize ty + layoutSizeList tys
end

mutual
  def layoutToTyVal : LayoutTy → TyVal
  | LayoutTy.NatL => TyVal.NatTy
  | LayoutTy.PtrL _ => TyVal.PTy
  | LayoutTy.TupL tys => TyVal.TupTy (layoutToTyValList tys)

  def layoutToTyValList : List LayoutTy → List TyVal
  | [] => []
  | ty :: tys => layoutToTyVal ty :: layoutToTyValList tys
end

def listGetOpt {α} : List α → Nat → Option α
| [], _ => none
| a :: _, 0 => some a
| _ :: as, n + 1 => listGetOpt as n

def layoutResolvePath (ty : LayoutTy) (path : List Nat) : Option (Nat × LayoutTy) :=
  match path with
  | [] => some (0, ty)
  | idx :: rest =>
      match ty with
      | LayoutTy.TupL tys =>
          match listGetOpt tys idx with
          | some subTy =>
              let preSize := layoutSizeList (tys.take idx)
              match layoutResolvePath subTy rest with
              | some (off, finalTy) => some (preSize + off, finalTy)
              | none => none
          | none => none
      | _ => none

def tyResolvePath (ty : TyVal) (path : List Nat) : Option (Nat × TyVal) :=
  match path with
  | [] => some (0, ty)
  | idx :: rest =>
      match ty with
      | TyVal.TupTy tys =>
          match listGetOpt tys idx with
          | some subTy =>
              let preSize := typeSizeList (tys.take idx)
              match tyResolvePath subTy rest with
              | some (off, finalTy) => some (preSize + off, finalTy)
              | none => none
          | none => none
      | _ => none

end obseq
