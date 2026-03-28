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

mutual
  @[simp] theorem typeSize_layoutToTyVal : ∀ ty, typeSize (layoutToTyVal ty) = layoutSize ty
  | LayoutTy.NatL => rfl
  | LayoutTy.PtrL _ => rfl
  | LayoutTy.TupL tys => by
      simp [layoutToTyVal, typeSize, layoutSize, typeSizeList_layoutToTyValList]

  @[simp] theorem typeSizeList_layoutToTyValList :
      ∀ tys, typeSizeList (layoutToTyValList tys) = layoutSizeList tys
  | [] => rfl
  | ty :: tys => by
      simp [layoutToTyValList, typeSizeList, layoutSizeList, typeSize_layoutToTyVal,
        typeSizeList_layoutToTyValList]
end

theorem layoutSizeList_take_get_le :
    ∀ tys idx subTy,
      listGetOpt tys idx = some subTy →
      layoutSizeList (tys.take idx) + layoutSize subTy ≤ layoutSizeList tys
  | [], _, _, h => by
      cases h
  | ty :: tys, 0, subTy, h => by
      cases h
      simp [layoutSizeList]
  | ty :: tys, idx + 1, subTy, h => by
      simp [listGetOpt] at h
      have ih := layoutSizeList_take_get_le tys idx subTy h
      simpa [List.take, layoutSizeList, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        Nat.add_le_add_left ih (layoutSize ty)

theorem listGetOpt_layoutToTyValList :
    ∀ tys idx subTy,
      listGetOpt tys idx = some subTy →
      listGetOpt (layoutToTyValList tys) idx = some (layoutToTyVal subTy)
  | [], _, _, h => by
      cases h
  | ty :: tys, 0, subTy, h => by
      cases h
      rfl
  | ty :: tys, idx + 1, subTy, h => by
      simpa [listGetOpt, layoutToTyValList] using
        listGetOpt_layoutToTyValList tys idx subTy h

theorem layoutToTyValList_take :
    ∀ tys idx,
      layoutToTyValList (tys.take idx) = (layoutToTyValList tys).take idx
  | [], idx => by
      cases idx <;> rfl
  | ty :: tys, 0 => rfl
  | ty :: tys, idx + 1 => by
      simp [List.take, layoutToTyValList, layoutToTyValList_take]

theorem typeSizeList_take_layoutToTyValList
    (tys : List LayoutTy)
    (idx : Nat) :
    typeSizeList ((layoutToTyValList tys).take idx) = layoutSizeList (tys.take idx) := by
  rw [← layoutToTyValList_take]
  exact typeSizeList_layoutToTyValList (tys.take idx)

theorem tyResolvePath_layoutToTyVal :
    ∀ ty path off subTy,
      layoutResolvePath ty path = some (off, subTy) →
      tyResolvePath (layoutToTyVal ty) path = some (off, layoutToTyVal subTy)
  | ty, [], off, subTy, h => by
      simp [layoutResolvePath] at h
      rcases h with ⟨rfl, rfl⟩
      simp [tyResolvePath]
  | LayoutTy.NatL, _ :: _, _, _, h => by
      simp [layoutResolvePath] at h
  | LayoutTy.PtrL _, _ :: _, _, _, h => by
      simp [layoutResolvePath] at h
  | LayoutTy.TupL tys, idx :: rest, off, subTy, h => by
      cases h_get : listGetOpt tys idx with
      | none =>
          simp [layoutResolvePath, h_get] at h
      | some subLayout =>
          cases h_res : layoutResolvePath subLayout rest with
          | none =>
              simp [layoutResolvePath, h_get, h_res] at h
          | some pair =>
              rcases pair with ⟨off', subLayout'⟩
              simp [layoutResolvePath, h_get, h_res] at h
              rcases h with ⟨rfl, rfl⟩
              have h_get' := listGetOpt_layoutToTyValList tys idx subLayout h_get
              simp [layoutToTyVal, tyResolvePath, h_get', h_res,
                typeSizeList_take_layoutToTyValList, typeSizeList_layoutToTyValList,
                tyResolvePath_layoutToTyVal subLayout rest off' subLayout' h_res]

theorem layoutResolvePath_layoutSize_le :
    ∀ ty path off subTy,
      layoutResolvePath ty path = some (off, subTy) →
      off + layoutSize subTy ≤ layoutSize ty
  | ty, [], off, subTy, h => by
      simp [layoutResolvePath] at h
      rcases h with ⟨rfl, rfl⟩
      simp
  | LayoutTy.NatL, _ :: _, _, _, h => by
      simp [layoutResolvePath] at h
  | LayoutTy.PtrL _, _ :: _, _, _, h => by
      simp [layoutResolvePath] at h
  | LayoutTy.TupL tys, idx :: rest, off, subTy, h => by
      cases h_get : listGetOpt tys idx with
      | none =>
          simp [layoutResolvePath, h_get] at h
      | some subLayout =>
          cases h_res : layoutResolvePath subLayout rest with
          | none =>
              simp [layoutResolvePath, h_get, h_res] at h
          | some pair =>
              rcases pair with ⟨off', subLayout'⟩
              simp [layoutResolvePath, h_get, h_res] at h
              rcases h with ⟨rfl, rfl⟩
              have h_child :=
                layoutResolvePath_layoutSize_le subLayout rest off' subLayout' h_res
              have h_prefix := layoutSizeList_take_get_le tys idx subLayout h_get
              have h_sum :
                  layoutSizeList (tys.take idx) + (off' + layoutSize subLayout') ≤
                    layoutSizeList (tys.take idx) + layoutSize subLayout :=
                Nat.add_le_add_left h_child _
              have h_total :
                  layoutSizeList (tys.take idx) + (off' + layoutSize subLayout') ≤
                    layoutSizeList tys :=
                Nat.le_trans h_sum h_prefix
              simpa [layoutSize, Nat.add_assoc] using h_total

end obseq
