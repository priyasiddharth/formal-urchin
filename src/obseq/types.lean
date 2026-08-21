import obseq.ListCompat

namespace obseq

inductive TyVal
| NatTy
| PTy
| TupTy (tys : List TyVal)
deriving Repr, Inhabited

inductive LayoutTy
| NatL
| PtrL (inner : LayoutTy)
| TupL (tys : List LayoutTy)
deriving Repr, Inhabited

/-! ### Structural equality

`deriving BEq` on these NESTED inductives (the `List` payload) compiles to
a `partial` — hence OPAQUE — function: nothing can be proved about it, not
even `t == t`. Since the target machine's `RStore` guards on `srcTy != ty`,
every proof about a register store would be stuck. So both `BEq`s are
hand-written structurally, with reflexivity available as a simp lemma. -/

mutual
  def TyVal.beq : TyVal → TyVal → Bool
  | .NatTy, .NatTy => true
  | .PTy, .PTy => true
  | .TupTy as, .TupTy bs => TyVal.beqList as bs
  | _, _ => false

  def TyVal.beqList : List TyVal → List TyVal → Bool
  | [], [] => true
  | a :: as, b :: bs => TyVal.beq a b && TyVal.beqList as bs
  | _, _ => false
end

instance : BEq TyVal := ⟨TyVal.beq⟩

mutual
  def LayoutTy.beq : LayoutTy → LayoutTy → Bool
  | .NatL, .NatL => true
  | .PtrL a, .PtrL b => LayoutTy.beq a b
  | .TupL as, .TupL bs => LayoutTy.beqList as bs
  | _, _ => false

  def LayoutTy.beqList : List LayoutTy → List LayoutTy → Bool
  | [], [] => true
  | a :: as, b :: bs => LayoutTy.beq a b && LayoutTy.beqList as bs
  | _, _ => false
end

instance : BEq LayoutTy := ⟨LayoutTy.beq⟩

mutual
  theorem TyVal.beq_refl : ∀ t : TyVal, TyVal.beq t t = true
  | .NatTy => rfl
  | .PTy => rfl
  | .TupTy ts => by
      show TyVal.beqList ts ts = true
      exact TyVal.beqList_refl ts

  theorem TyVal.beqList_refl : ∀ ts : List TyVal, TyVal.beqList ts ts = true
  | [] => rfl
  | t :: ts => by
      show (TyVal.beq t t && TyVal.beqList ts ts) = true
      rw [TyVal.beq_refl t, TyVal.beqList_refl ts]
      rfl
end

mutual
  theorem LayoutTy.beq_refl : ∀ t : LayoutTy, LayoutTy.beq t t = true
  | .NatL => rfl
  | .PtrL a => by
      show LayoutTy.beq a a = true
      exact LayoutTy.beq_refl a
  | .TupL ts => by
      show LayoutTy.beqList ts ts = true
      exact LayoutTy.beqList_refl ts

  theorem LayoutTy.beqList_refl : ∀ ts : List LayoutTy, LayoutTy.beqList ts ts = true
  | [] => rfl
  | t :: ts => by
      show (LayoutTy.beq t t && LayoutTy.beqList ts ts) = true
      rw [LayoutTy.beq_refl t, LayoutTy.beqList_refl ts]
      rfl
end

@[simp] theorem TyVal.beq_self (t : TyVal) : (t == t) = true := TyVal.beq_refl t

@[simp] theorem TyVal.bne_self (t : TyVal) : (t != t) = false := by
  simp only [bne, TyVal.beq_self, Bool.not_true]

@[simp] theorem LayoutTy.beq_self (t : LayoutTy) : (t == t) = true :=
  LayoutTy.beq_refl t

@[simp] theorem LayoutTy.bne_self (t : LayoutTy) : (t != t) = false := by
  simp only [bne, LayoutTy.beq_self, Bool.not_true]

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
