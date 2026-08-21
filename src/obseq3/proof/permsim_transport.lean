import obseq3.proof.common
import obseq3.proof.keystone

/-!
BRIDGE 3 — SB operations respect `PermSim`, CLOSED for `sb_write`:
renamed-equal states with a renamed acting tag produce renamed-equal
results. The proof is the transport family sketched in the refactor
assessment (journal 2026-08-18): generic `ListRel` transports, tag/beq
transport under `TagRenameWF`, `splitStack`/`firstProtectedIn`/
`writeCellContent` transports, and the `setChain` machinery from the
keystone re-run relationally.

Scope note: the acting tag is assumed non-wildcard
(`(tagS == wildcardTag) = false`). Wildcard resolution transport
(`resolveWildcardIn` over the renamed exposed set) is deliberately out of
scope: proof-core programs cannot mint wildcard pointers (`fromExposed`
is not a core rvalue), so no core acting tag is ever the wildcard. The
`sb_read`/`sb_die`/`sb_ref` members of the family reuse this file's
lemma stack and are stated when their consumers (leaves 2–3) close.
-/

namespace obseq3.proof

open obseq3

/-! ## Generic `ListRel` transports -/

theorem ListRel.append {α β} {R : α → β → Prop} :
    ∀ {as : List α} {bs : List β} {cs : List α} {ds : List β},
      ListRel R as bs → ListRel R cs ds → ListRel R (as ++ cs) (bs ++ ds) := by
  intro as
  induction as with
  | nil =>
      intro bs cs ds h1 h2
      cases bs with
      | nil => exact h2
      | cons b bs => simp [ListRel] at h1
  | cons a as ih =>
      intro bs cs ds h1 h2
      cases bs with
      | nil => simp [ListRel] at h1
      | cons b bs =>
          simp only [ListRel] at h1
          exact ⟨h1.1, ih h1.2 h2⟩

theorem ListRel.reverse {α β} {R : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, ListRel R as bs →
      ListRel R as.reverse bs.reverse := by
  intro as
  induction as with
  | nil =>
      intro bs h
      cases bs with
      | nil => exact h
      | cons b bs => simp [ListRel] at h
  | cons a as ih =>
      intro bs h
      cases bs with
      | nil => simp [ListRel] at h
      | cons b bs =>
          simp only [ListRel] at h
          simp only [List.reverse_cons]
          exact ListRel.append (ih h.2) ⟨h.1, trivial⟩

theorem ListRel.take {α β} {R : α → β → Prop} :
    ∀ (n : Nat) {as : List α} {bs : List β}, ListRel R as bs →
      ListRel R (as.take n) (bs.take n) := by
  intro n
  induction n with
  | zero => intro as bs _; trivial
  | succ n ih =>
      intro as bs h
      cases as with
      | nil =>
          cases bs with
          | nil => trivial
          | cons b bs => simp [ListRel] at h
      | cons a as =>
          cases bs with
          | nil => simp [ListRel] at h
          | cons b bs =>
              simp only [ListRel] at h
              simp only [List.take]
              exact ⟨h.1, ih h.2⟩

theorem ListRel.takeWhile {α β} {R : α → β → Prop} {p : α → Bool} {q : β → Bool}
    (h_pred : ∀ x y, R x y → q y = p x) :
    ∀ {as : List α} {bs : List β}, ListRel R as bs →
      ListRel R (as.takeWhile p) (bs.takeWhile q) := by
  intro as
  induction as with
  | nil =>
      intro bs h
      cases bs with
      | nil => trivial
      | cons b bs => simp [ListRel] at h
  | cons a as ih =>
      intro bs h
      cases bs with
      | nil => simp [ListRel] at h
      | cons b bs =>
          simp only [ListRel] at h
          rw [List.takeWhile_cons, List.takeWhile_cons, h_pred a b h.1]
          cases p a with
          | true => exact ⟨h.1, ih h.2⟩
          | false => trivial

theorem ListRel.filter {α β} {R : α → β → Prop} {p : α → Bool} {q : β → Bool}
    (h_pred : ∀ x y, R x y → q y = p x) :
    ∀ {as : List α} {bs : List β}, ListRel R as bs →
      ListRel R (as.filter p) (bs.filter q) := by
  intro as
  induction as with
  | nil =>
      intro bs h
      cases bs with
      | nil => trivial
      | cons b bs => simp [ListRel] at h
  | cons a as ih =>
      intro bs h
      cases bs with
      | nil => simp [ListRel] at h
      | cons b bs =>
          simp only [ListRel] at h
          rw [List.filter_cons, List.filter_cons, h_pred a b h.1]
          cases p a with
          | true => exact ⟨h.1, ih h.2⟩
          | false => exact ih h.2

theorem ListRel.find?_none {α β} {R : α → β → Prop} {p : α → Bool} {q : β → Bool}
    (h_pred : ∀ x y, R x y → q y = p x) :
    ∀ {as : List α} {bs : List β}, ListRel R as bs →
      as.find? p = none → bs.find? q = none := by
  intro as
  induction as with
  | nil =>
      intro bs h _
      cases bs with
      | nil => rfl
      | cons b bs => simp [ListRel] at h
  | cons a as ih =>
      intro bs h h_none
      cases bs with
      | nil => simp [ListRel] at h
      | cons b bs =>
          simp only [ListRel] at h
          simp only [List.find?_cons] at h_none ⊢
          cases hp : p a with
          | true => simp [hp] at h_none
          | false =>
              simp only [hp, Bool.false_eq_true, if_false] at h_none
              simp only [h_pred a b h.1, hp, Bool.false_eq_true, if_false]
              exact ih h.2 h_none

/-! ## Tag and item transports under `TagRenameWF` -/

theorem TagRenameWF.beq_eq {ρt : TagRenameMap} (h_wf : TagRenameWF ρt)
    {a b x y : Tag} (h_ab : ρt a = some b) (h_xy : ρt x = some y) :
    (b == y) = (a == x) := by
  by_cases h : a = x
  · subst h
    rw [h_ab] at h_xy
    injection h_xy with h'
    subst h'
    simp
  · have hby : b ≠ y := by
      intro hb
      subst hb
      exact h (h_wf.1 a x b h_ab h_xy)
    have h1 : (a == x) = false := by
      cases hax : a == x with
      | false => rfl
      | true => exact absurd (eq_of_beq hax) h
    have h2 : (b == y) = false := by
      cases hby' : b == y with
      | false => rfl
      | true => exact absurd (eq_of_beq hby') hby
    rw [h1, h2]

theorem ItemSim.tag_rel {ρt : TagRenameMap} {i i' : Item}
    (h : ItemSim ρt i i') : ρt i.tag = some i'.tag := by
  cases i <;> cases i' <;> simp only [ItemSim] at h <;>
    first
      | (simp only [Item.tag]; exact h)
      | (simp only [Item.tag]; exact h.2)

theorem ItemSim.grantsWrite_eq {ρt : TagRenameMap} {i i' : Item}
    (h : ItemSim ρt i i') : i'.grantsWrite = i.grantsWrite := by
  cases i with
  | Own t => cases i' <;> simp only [ItemSim] at h <;> rfl
  | MutRef t => cases i' <;> simp only [ItemSim] at h <;> rfl
  | Ref t => cases i' <;> simp only [ItemSim] at h <;> rfl
  | Disabled t => cases i' <;> simp only [ItemSim] at h <;> rfl
  | RawPtr m t =>
      cases i' <;> simp only [ItemSim] at h
      rw [h.1]
      cases m <;> rfl

theorem ItemSim.isSrw_eq {ρt : TagRenameMap} {i i' : Item}
    (h : ItemSim ρt i i') : i'.isSrw = i.isSrw := by
  cases i with
  | Own t => cases i' <;> simp only [ItemSim] at h <;> rfl
  | MutRef t => cases i' <;> simp only [ItemSim] at h <;> rfl
  | Ref t => cases i' <;> simp only [ItemSim] at h <;> rfl
  | Disabled t => cases i' <;> simp only [ItemSim] at h <;> rfl
  | RawPtr m t =>
      cases i' <;> simp only [ItemSim] at h
      rw [h.1]
      cases m <;> rfl

theorem TagListSim.contains_eq {ρt : TagRenameMap} (h_wf : TagRenameWF ρt)
    {a b : Tag} (h_ab : ρt a = some b) :
    ∀ {fS fT : List Tag}, TagListSim ρt fS fT →
      fT.contains b = fS.contains a := by
  intro fS
  induction fS with
  | nil =>
      intro fT h
      cases fT with
      | nil => rfl
      | cons y ys => simp [TagListSim, ListRel] at h
  | cons x xs ih =>
      intro fT h
      cases fT with
      | nil => simp [TagListSim, ListRel] at h
      | cons y ys =>
          simp only [TagListSim, ListRel] at h
          simp only [List.contains_cons]
          rw [h_wf.beq_eq h_ab h.1, ih h.2]

theorem isProtectedIn_transport {ρt : TagRenameMap} (h_wf : TagRenameWF ρt)
    {a b : Tag} (h_ab : ρt a = some b) :
    ∀ {pfS pfT : List (List Tag)}, ListRel (TagListSim ρt) pfS pfT →
      isProtectedIn pfT b = isProtectedIn pfS a := by
  intro pfS
  induction pfS with
  | nil =>
      intro pfT h
      cases pfT with
      | nil => rfl
      | cons f fs => simp [ListRel] at h
  | cons f fs ih =>
      intro pfT h
      cases pfT with
      | nil => simp [ListRel] at h
      | cons f' fs' =>
          simp only [ListRel] at h
          unfold isProtectedIn
          simp only [List.any_cons]
          rw [TagListSim.contains_eq h_wf h_ab h.1]
          have := ih h.2
          unfold isProtectedIn at this
          rw [this]

theorem firstProtectedIn_none_transport {ρt : TagRenameMap}
    (h_wf : TagRenameWF ρt)
    {pfS pfT : List (List Tag)} (h_pf : ListRel (TagListSim ρt) pfS pfT)
    {xs ys : BorrowStack} (h_rel : StackSim ρt xs ys)
    (h_none : firstProtectedIn pfS xs = none) :
    firstProtectedIn pfT ys = none := by
  unfold firstProtectedIn at h_none ⊢
  refine ListRel.find?_none ?_ h_rel h_none
  intro k k' hk
  cases k with
  | Own t =>
      cases k' <;> simp only [ItemSim] at hk
      exact isProtectedIn_transport h_wf hk h_pf
  | MutRef t =>
      cases k' <;> simp only [ItemSim] at hk
      exact isProtectedIn_transport h_wf hk h_pf
  | Ref t =>
      cases k' <;> simp only [ItemSim] at hk
      exact isProtectedIn_transport h_wf hk h_pf
  | Disabled t =>
      cases k' <;> simp only [ItemSim] at hk
      exact isProtectedIn_transport h_wf hk h_pf
  | RawPtr m t =>
      cases k' <;> simp only [ItemSim] at hk
      rw [hk.1]
      cases m with
      | true => rfl
      | false => exact isProtectedIn_transport h_wf hk.2 h_pf

/-! ## `splitStack` transport -/

theorem splitStack_some_transport {ρt : TagRenameMap} (h_wf : TagRenameWF ρt)
    {tagS tagT : Tag} (h_t : ρt tagS = some tagT) :
    ∀ {v v' : BorrowStack}, StackSim ρt v v' →
      ∀ {ab : BorrowStack} {it : Item} {bl : BorrowStack},
      splitStack v tagS = some (ab, it, bl) →
      ∃ ab' it' bl', splitStack v' tagT = some (ab', it', bl') ∧
        StackSim ρt ab ab' ∧ ItemSim ρt it it' ∧ StackSim ρt bl bl' := by
  intro v
  induction v with
  | nil =>
      intro v' hv ab it bl h
      simp [splitStack] at h
  | cons k rest ih =>
      intro v' hv ab it bl h
      cases v' with
      | nil => simp [StackSim, ListRel] at hv
      | cons k' rest' =>
          simp only [StackSim, ListRel] at hv
          have h_beq : (k'.tag == tagT) = (k.tag == tagS) :=
            h_wf.beq_eq (ItemSim.tag_rel hv.1) h_t
          simp only [splitStack] at h
          cases hkt : k.tag == tagS with
          | true =>
              simp [hkt] at h
              obtain ⟨h1, h2, h3⟩ := h
              subst h1; subst h2; subst h3
              refine ⟨[], k', rest', ?_, trivial, hv.1, hv.2⟩
              simp [splitStack, h_beq, hkt]
          | false =>
              simp only [hkt, Bool.false_eq_true, if_false] at h
              cases h_rec : splitStack rest tagS with
              | none => simp [h_rec] at h
              | some triple =>
                  obtain ⟨a2, f2, b2⟩ := triple
                  simp [h_rec] at h
                  obtain ⟨h1, h2, h3⟩ := h
                  subst h1; subst h2; subst h3
                  obtain ⟨a2', f2', b2', h_rec', h_a, h_f, h_b⟩ := ih hv.2 h_rec
                  refine ⟨k' :: a2', f2', b2', ?_, ⟨hv.1, h_a⟩, h_f, h_b⟩
                  simp [splitStack, h_beq, hkt, h_rec']

/-! ## `writeCellContent` transport -/

theorem writeCellContent_transport
    {ρt : TagRenameMap} {pfS pfT : List (List Tag)} {exS exT : List Tag}
    {a a' : Word} {tagS tagT : Tag} {v v' : BorrowStack} {w : BorrowStack}
    (h_wf : TagRenameWF ρt)
    (h_pf : ListRel (TagListSim ρt) pfS pfT)
    (h_t : ρt tagS = some tagT)
    (h_ts : (tagS == wildcardTag) = false)
    (h_v : StackSim ρt v v')
    (h_ok : writeCellContent pfS exS a tagS v = .ok w) :
    ∃ w', writeCellContent pfT exT a' tagT v' = .ok w' ∧ StackSim ρt w w' := by
  have h_tt : (tagT == wildcardTag) = false := by
    rw [h_wf.beq_eq h_t h_wf.2]
    exact h_ts
  unfold writeCellContent at h_ok ⊢
  rw [h_ts] at h_ok
  rw [h_tt]
  simp only [Bool.false_eq_true, if_false] at h_ok ⊢
  cases h_split : splitStack v tagS with
  | none => simp [h_split] at h_ok
  | some triple =>
      obtain ⟨ab, it, bl⟩ := triple
      obtain ⟨ab', it', bl', h_split', h_ab, h_it, h_bl⟩ :=
        splitStack_some_transport h_wf h_t h_v h_split
      simp only [h_split] at h_ok
      simp only [h_split']
      have h_gw := ItemSim.grantsWrite_eq h_it
      have h_srw := ItemSim.isSrw_eq h_it
      have h_len_ab : ab.length = ab'.length := ListRel.length_eq h_ab
      cases it with
      | Disabled t =>
          simp at h_ok
      | Ref t =>
          simp [Item.grantsWrite] at h_ok
      | RawPtr m t =>
          cases it' <;> simp only [ItemSim] at h_it
          rw [h_it.1]
          have h_t2 := h_it.2
          cases m with
          | false =>
              simp [Item.grantsWrite] at h_ok
          | true =>
              simp [Item.grantsWrite, Item.isSrw] at h_ok ⊢
              have h_grp : ListRel (ItemSim ρt)
                  (ab.reverse.takeWhile Item.isSrw)
                  (ab'.reverse.takeWhile Item.isSrw) :=
                ListRel.takeWhile (fun x y hxy => ItemSim.isSrw_eq hxy)
                  (ListRel.reverse h_ab)
              have h_len_grp : (ab.reverse.takeWhile Item.isSrw).length
                  = (ab'.reverse.takeWhile Item.isSrw).length :=
                ListRel.length_eq h_grp
              have h_rest : ListRel (ItemSim ρt)
                  (ab.take (ab.length - (ab.reverse.takeWhile Item.isSrw).length))
                  (ab'.take (ab'.length - (ab'.reverse.takeWhile Item.isSrw).length)) := by
                rw [← h_len_ab, ← h_len_grp]
                exact ListRel.take _ h_ab
              cases h_fp : firstProtectedIn pfS
                  (ab.take (ab.length - (ab.reverse.takeWhile Item.isSrw).length)) with
              | some p => simp [h_fp] at h_ok
              | none =>
                  simp only [h_fp] at h_ok
                  simp only [firstProtectedIn_none_transport h_wf h_pf h_rest h_fp]
                  simp only [Except.ok.injEq] at h_ok
                  refine ⟨_, rfl, ?_⟩
                  rw [← h_ok]
                  exact ListRel.append (ListRel.reverse h_grp)
                    ⟨by simp [ItemSim]; exact h_t2, h_bl⟩
      | Own t =>
          cases it' <;> simp only [ItemSim] at h_it
          simp [Item.grantsWrite, Item.isSrw] at h_ok ⊢
          cases h_fp : firstProtectedIn pfS ab with
          | some p => simp [h_fp] at h_ok
          | none =>
              simp only [h_fp] at h_ok
              simp only [firstProtectedIn_none_transport h_wf h_pf h_ab h_fp]
              simp only [Except.ok.injEq] at h_ok
              refine ⟨_, rfl, ?_⟩
              rw [← h_ok]
              exact ⟨by simp [ItemSim]; exact h_it, h_bl⟩
      | MutRef t =>
          cases it' <;> simp only [ItemSim] at h_it
          simp [Item.grantsWrite, Item.isSrw] at h_ok ⊢
          cases h_fp : firstProtectedIn pfS ab with
          | some p => simp [h_fp] at h_ok
          | none =>
              simp only [h_fp] at h_ok
              simp only [firstProtectedIn_none_transport h_wf h_pf h_ab h_fp]
              simp only [Except.ok.injEq] at h_ok
              refine ⟨_, rfl, ?_⟩
              rw [← h_ok]
              exact ⟨by simp [ItemSim]; exact h_it, h_bl⟩

/-! ## `readCellContent` / `dieCellContent` transports -/

theorem ListRel.map {α β} {R : α → β → Prop} {f : α → α} {g : β → β}
    (h_fg : ∀ x y, R x y → R (f x) (g y)) :
    ∀ {as : List α} {bs : List β}, ListRel R as bs →
      ListRel R (as.map f) (bs.map g) := by
  intro as
  induction as with
  | nil =>
      intro bs h
      cases bs with
      | nil => trivial
      | cons b bs => simp [ListRel] at h
  | cons a as ih =>
      intro bs h
      cases bs with
      | nil => simp [ListRel] at h
      | cons b bs =>
          simp only [ListRel] at h
          exact ⟨h_fg a b h.1, ih h.2⟩

theorem ItemSim.poppedByRead_eq {ρt : TagRenameMap} {i i' : Item}
    (h : ItemSim ρt i i') : i'.poppedByRead = i.poppedByRead := by
  cases i with
  | Own t => cases i' <;> simp only [ItemSim] at h <;> rfl
  | MutRef t => cases i' <;> simp only [ItemSim] at h <;> rfl
  | Ref t => cases i' <;> simp only [ItemSim] at h <;> rfl
  | Disabled t => cases i' <;> simp only [ItemSim] at h <;> rfl
  | RawPtr m t =>
      cases i' <;> simp only [ItemSim] at h
      rfl

/-- The read access\'s disable-in-place map respects `ItemSim`. -/
theorem ItemSim.disable_map {ρt : TagRenameMap} {k k' : Item}
    (h : ItemSim ρt k k') :
    ItemSim ρt (if k.poppedByRead then .Disabled k.tag else k)
      (if k'.poppedByRead then .Disabled k'.tag else k') := by
  cases k with
  | MutRef t =>
      cases k' <;> simp only [ItemSim] at h
      simpa [Item.poppedByRead, Item.tag, ItemSim] using h
  | Own t =>
      cases k' <;> simp only [ItemSim] at h
      simpa [Item.poppedByRead, ItemSim] using h
  | Ref t =>
      cases k' <;> simp only [ItemSim] at h
      simpa [Item.poppedByRead, ItemSim] using h
  | Disabled t =>
      cases k' <;> simp only [ItemSim] at h
      simpa [Item.poppedByRead, ItemSim] using h
  | RawPtr m t =>
      cases k' <;> simp only [ItemSim] at h
      simpa [Item.poppedByRead, ItemSim] using h

theorem readCell_content_form
    {P : List (List Tag)} {E : List Tag}
    (t : Tag) (ap : AccessPerms) (a : Word)
    (h_pf : ap.protFrames = P) (h_ex : ap.exposed = E) :
    readCell ap a t =
      match SB.find? ap.StackMap a with
      | none => .error s!"sb-read: no borrow stack at address {a}"
      | some stack =>
        match readCellContent P E a t stack with
        | .error e => .error e
        | .ok v => .ok { ap with StackMap := SB.set ap.StackMap a v } := by
  cases h_find : SB.find? ap.StackMap a with
  | none => simp only [readCell, h_find]
  | some stack =>
      cases h_content : readCellContent P E a t stack with
      | error e =>
          simp only [readCell, h_pf, h_ex, h_find, h_content]
      | ok v =>
          simp only [readCell, h_pf, h_ex, h_find, h_content]

theorem readCellContent_transport
    {ρt : TagRenameMap} {pfS pfT : List (List Tag)} {exS exT : List Tag}
    {a a' : Word} {tagS tagT : Tag} {v v' : BorrowStack} {w : BorrowStack}
    (h_wf : TagRenameWF ρt)
    (h_pf : ListRel (TagListSim ρt) pfS pfT)
    (h_t : ρt tagS = some tagT)
    (h_ts : (tagS == wildcardTag) = false)
    (h_v : StackSim ρt v v')
    (h_ok : readCellContent pfS exS a tagS v = .ok w) :
    ∃ w', readCellContent pfT exT a' tagT v' = .ok w' ∧ StackSim ρt w w' := by
  have h_tt : (tagT == wildcardTag) = false := by
    rw [h_wf.beq_eq h_t h_wf.2]
    exact h_ts
  unfold readCellContent at h_ok ⊢
  rw [h_ts] at h_ok
  rw [h_tt]
  simp only [Bool.false_eq_true, if_false] at h_ok ⊢
  cases h_split : splitStack v tagS with
  | none => simp [h_split] at h_ok
  | some triple =>
      obtain ⟨ab, it, bl⟩ := triple
      obtain ⟨ab', it', bl', h_split', h_ab, h_it, h_bl⟩ :=
        splitStack_some_transport h_wf h_t h_v h_split
      simp only [h_split] at h_ok
      simp only [h_split']
      have h_hit : ListRel (ItemSim ρt)
          (ab.filter (·.poppedByRead)) (ab'.filter (·.poppedByRead)) :=
        ListRel.filter (fun x y hxy => ItemSim.poppedByRead_eq hxy) h_ab
      have h_map : ListRel (ItemSim ρt)
          (ab.map (fun k => if k.poppedByRead then .Disabled k.tag else k))
          (ab'.map (fun k => if k.poppedByRead then .Disabled k.tag else k)) :=
        ListRel.map (fun x y hxy => ItemSim.disable_map hxy) h_ab
      cases it with
      | Disabled t =>
          simp at h_ok
      | Own t =>
          cases it' <;> simp only [ItemSim] at h_it
          cases h_fp : firstProtectedIn pfS (ab.filter (·.poppedByRead)) with
          | some p => simp [h_fp] at h_ok
          | none =>
              simp only [h_fp] at h_ok
              simp only [firstProtectedIn_none_transport h_wf h_pf h_hit h_fp]
              simp only [Except.ok.injEq] at h_ok
              refine ⟨_, rfl, ?_⟩
              rw [← h_ok]
              exact ListRel.append h_map ⟨by simp [ItemSim]; exact h_it, h_bl⟩
      | MutRef t =>
          cases it' <;> simp only [ItemSim] at h_it
          cases h_fp : firstProtectedIn pfS (ab.filter (·.poppedByRead)) with
          | some p => simp [h_fp] at h_ok
          | none =>
              simp only [h_fp] at h_ok
              simp only [firstProtectedIn_none_transport h_wf h_pf h_hit h_fp]
              simp only [Except.ok.injEq] at h_ok
              refine ⟨_, rfl, ?_⟩
              rw [← h_ok]
              exact ListRel.append h_map ⟨by simp [ItemSim]; exact h_it, h_bl⟩
      | Ref t =>
          cases it' <;> simp only [ItemSim] at h_it
          cases h_fp : firstProtectedIn pfS (ab.filter (·.poppedByRead)) with
          | some p => simp [h_fp] at h_ok
          | none =>
              simp only [h_fp] at h_ok
              simp only [firstProtectedIn_none_transport h_wf h_pf h_hit h_fp]
              simp only [Except.ok.injEq] at h_ok
              refine ⟨_, rfl, ?_⟩
              rw [← h_ok]
              exact ListRel.append h_map ⟨by simp [ItemSim]; exact h_it, h_bl⟩
      | RawPtr m t =>
          cases it' <;> simp only [ItemSim] at h_it
          rw [h_it.1]
          cases h_fp : firstProtectedIn pfS (ab.filter (·.poppedByRead)) with
          | some p => simp [h_fp] at h_ok
          | none =>
              simp only [h_fp] at h_ok
              simp only [firstProtectedIn_none_transport h_wf h_pf h_hit h_fp]
              simp only [Except.ok.injEq] at h_ok
              refine ⟨_, rfl, ?_⟩
              rw [← h_ok]
              exact ListRel.append h_map ⟨by simp [ItemSim]; exact h_it.2, h_bl⟩

theorem dieCellContent_transport
    {ρt : TagRenameMap} {pfS pfT : List (List Tag)}
    {tagS tagT : Tag} {v v' : BorrowStack} {w : BorrowStack}
    (h_wf : TagRenameWF ρt)
    (h_pf : ListRel (TagListSim ρt) pfS pfT)
    (h_t : ρt tagS = some tagT)
    (h_v : StackSim ρt v v')
    (h_ok : dieCellContent pfS tagS v = .ok w) :
    ∃ w', dieCellContent pfT tagT v' = .ok w' ∧ StackSim ρt w w' := by
  cases v with
  | nil => simp [dieCellContent] at h_ok
  | cons item below =>
      cases v' with
      | nil => simp [StackSim, ListRel] at h_v
      | cons item' below' =>
          simp only [StackSim, ListRel] at h_v
          obtain ⟨h_i, h_bl⟩ := h_v
          have h_beq : (item'.tag == tagT) = (item.tag == tagS) :=
            h_wf.beq_eq (ItemSim.tag_rel h_i) h_t
          simp only [dieCellContent] at h_ok ⊢
          rw [h_beq]
          cases hkt : item.tag == tagS with
          | false => simp [hkt] at h_ok
          | true =>
              simp only [hkt, if_true] at h_ok ⊢
              cases item with
              | Own t => simp at h_ok
              | Disabled t =>
                  cases item' <;> simp only [ItemSim] at h_i
                  rename_i t'
                  cases h_prot : isProtectedIn pfS t with
                  | true => simp [Item.tag, h_prot] at h_ok
                  | false =>
                      simp only [Item.tag, h_prot, Bool.false_eq_true, if_false,
                        Except.ok.injEq] at h_ok
                      have h_prot' : isProtectedIn pfT t' = false := by
                        rw [isProtectedIn_transport h_wf h_i h_pf]
                        exact h_prot
                      simp only [Item.tag, h_prot', Bool.false_eq_true, if_false,
                        Except.ok.injEq]
                      exact ⟨_, rfl, h_ok ▸ h_bl⟩
              | MutRef t =>
                  cases item' <;> simp only [ItemSim] at h_i
                  rename_i t'
                  cases h_prot : isProtectedIn pfS t with
                  | true => simp [Item.tag, h_prot] at h_ok
                  | false =>
                      simp only [Item.tag, h_prot, Bool.false_eq_true, if_false,
                        Except.ok.injEq] at h_ok
                      have h_prot' : isProtectedIn pfT t' = false := by
                        rw [isProtectedIn_transport h_wf h_i h_pf]
                        exact h_prot
                      simp only [Item.tag, h_prot', Bool.false_eq_true, if_false,
                        Except.ok.injEq]
                      exact ⟨_, rfl, h_ok ▸ h_bl⟩
              | Ref t =>
                  cases item' <;> simp only [ItemSim] at h_i
                  rename_i t'
                  cases h_prot : isProtectedIn pfS t with
                  | true => simp [Item.tag, h_prot] at h_ok
                  | false =>
                      simp only [Item.tag, h_prot, Bool.false_eq_true, if_false,
                        Except.ok.injEq] at h_ok
                      have h_prot' : isProtectedIn pfT t' = false := by
                        rw [isProtectedIn_transport h_wf h_i h_pf]
                        exact h_prot
                      simp only [Item.tag, h_prot', Bool.false_eq_true, if_false,
                        Except.ok.injEq]
                      exact ⟨_, rfl, h_ok ▸ h_bl⟩
              | RawPtr m t =>
                  cases item' <;> simp only [ItemSim] at h_i
                  rename_i m' t'
                  rw [h_i.1]
                  cases h_prot : isProtectedIn pfS t with
                  | true => simp [Item.tag, h_prot] at h_ok
                  | false =>
                      simp only [Item.tag, h_prot, Bool.false_eq_true, if_false,
                        Except.ok.injEq] at h_ok
                      have h_prot' : isProtectedIn pfT t' = false := by
                        rw [isProtectedIn_transport h_wf h_i.2 h_pf]
                        exact h_prot
                      simp only [Item.tag, h_prot', Bool.false_eq_true, if_false,
                        Except.ok.injEq]
                      exact ⟨_, rfl, h_ok ▸ h_bl⟩

/-! ## `SB`/`setChain`-level transports -/

theorem SB.find?_transport {ρt : TagRenameMap} :
    ∀ {x y : SB}, ListRel (CellSim ρt) x y →
      ∀ {a : Word} {s : BorrowStack}, SB.find? x a = some s →
      ∃ s', SB.find? y a = some s' ∧ StackSim ρt s s' := by
  intro x
  induction x with
  | nil =>
      intro y h a s hf
      simp [SB.find?] at hf
  | cons e x ih =>
      obtain ⟨k, st⟩ := e
      intro y h a s hf
      cases y with
      | nil => simp [ListRel] at h
      | cons e' y' =>
          obtain ⟨k', st'⟩ := e'
          simp only [ListRel, CellSim] at h
          obtain ⟨⟨h_key, h_st⟩, h_tail⟩ := h
          simp only [SB.find?] at hf ⊢
          rw [h_key]
          cases hk : k == a with
          | true =>
              simp only [hk, if_true] at hf ⊢
              injection hf with hf'
              subst hf'
              exact ⟨st', rfl, h_st⟩
          | false =>
              simp only [hk, Bool.false_eq_true, if_false] at hf ⊢
              exact ih h_tail hf

theorem SB.set_respects {ρt : TagRenameMap} {x y : SB}
    (h : ListRel (CellSim ρt) x y)
    {a : Word} {v v' : BorrowStack} (h_v : StackSim ρt v v') :
    ListRel (CellSim ρt) (SB.set x a v) (SB.set y a v') := by
  unfold SB.set
  refine ⟨⟨rfl, h_v⟩, ?_⟩
  refine ListRel.filter ?_ h
  intro e e' he
  obtain ⟨k, s⟩ := e
  obtain ⟨k', s'⟩ := e'
  obtain ⟨rfl, -⟩ := he
  rfl

theorem setChain_chain_respects {ρt : TagRenameMap}
    {W W' : Nat → BorrowStack} {addr : Word} {i len : Nat}
    {x y : SB}
    (h_xy : ListRel (CellSim ρt) x y)
    (h_W : ∀ j, i ≤ j → j < len → StackSim ρt (W j) (W' j)) :
    ListRel (CellSim ρt) (setChain x (chain W addr i len))
      (setChain y (chain W' addr i len)) := by
  by_cases h : i < len
  · rw [chain_step h, chain_step h, setChain, setChain]
    exact setChain_chain_respects
      (SB.set_respects h_xy (h_W i (Nat.le_refl i) h))
      (fun j h1 h2 => h_W j (by omega) h2)
  · rw [chain_stop h, chain_stop h]
    exact h_xy
  termination_by len - i

/-! ## BRIDGE 3 for `sb_write` -/

/-- BRIDGE 3, CLOSED for the write: `sb_write` respects `PermSim` — a
    successful source write through `tagS` is matched by a target write
    through the renamed `tagT`, and the results stay `PermSim`-related.
    Non-wildcard acting tags only (see the module docstring). -/
theorem sb_write_respects_PermSim
    {ρt : TagRenameMap} {src tgt src' : AccessPerms}
    {addr : Word} {len : Nat} {tagS tagT : Tag}
    (h_sim : PermSim ρt src tgt)
    (h_wf : TagRenameWF ρt)
    (h_tag : ρt tagS = some tagT)
    (h_ts : (tagS == wildcardTag) = false)
    (h_src : sb_write src addr len tagS = .ok src') :
    ∃ tgt', sb_write tgt addr len tagT = .ok tgt' ∧ PermSim ρt src' tgt' := by
  obtain ⟨h_stacks, h_prot, h_exp, h_next⟩ := h_sim
  have h_src0 : foldCells (fun ap a => writeCell ap a tagS) src (addr + 0) len
      = .ok src' := h_src
  obtain ⟨V, W, h_cells, h_src'⟩ :=
    foldCells_ok_inv
      (C := fun a stack => writeCellContent src.protFrames src.exposed a tagS stack)
      (msgNone := fun a => s!"sb-write: no borrow stack at address {a}")
      (P := src.protFrames) (E := src.exposed) (N := src.NextTag)
      (fun ap a h_pf h_ex _ => writeCell_content_form tagS ap a h_pf h_ex)
      len 0 src src' rfl rfl rfl h_src0
  have h_pkg : ∀ j, ∃ vj, ∃ wj, j < len →
      SB.find? tgt.StackMap (addr + j) = some vj ∧
        writeCellContent tgt.protFrames tgt.exposed (addr + j) tagT vj = .ok wj ∧
        StackSim ρt (W j) wj := by
    intro j
    by_cases hj : j < len
    · have hc := h_cells j (Nat.zero_le j) (by omega)
      obtain ⟨s', h_find', h_ss⟩ := SB.find?_transport h_stacks hc.1
      obtain ⟨w', h_w', h_ws⟩ :=
        writeCellContent_transport h_wf h_prot h_tag h_ts h_ss hc.2
      exact ⟨s', w', fun _ => ⟨h_find', h_w', h_ws⟩⟩
    · exact ⟨[], [], fun h => absurd h hj⟩
  have h_pkg' : ∀ j, j < len →
      SB.find? tgt.StackMap (addr + j) = some ((h_pkg j).choose) ∧
        writeCellContent tgt.protFrames tgt.exposed (addr + j) tagT
          ((h_pkg j).choose) = .ok ((h_pkg j).choose_spec.choose) ∧
        StackSim ρt (W j) ((h_pkg j).choose_spec.choose) :=
    fun j hj => (h_pkg j).choose_spec.choose_spec hj
  have h_tgt : foldCells (fun ap a => writeCell ap a tagT) tgt (addr + 0) len =
      .ok { tgt with StackMap := setChain tgt.StackMap (chain (fun j => (h_pkg j).choose_spec.choose) addr 0 (0 + len)) } :=
    foldCells_ok_of_cells
      (C := fun a stack => writeCellContent tgt.protFrames tgt.exposed a tagT stack)
      (msgNone := fun a => s!"sb-write: no borrow stack at address {a}")
      (P := tgt.protFrames) (E := tgt.exposed) (N := tgt.NextTag)
      (fun ap a h_pf h_ex _ => writeCell_content_form tagT ap a h_pf h_ex)
      len 0 tgt (fun j => (h_pkg j).choose)
      (fun j => (h_pkg j).choose_spec.choose)
      rfl rfl rfl
      (fun j h1 h2 => (h_pkg' j (by omega)).1)
      (fun j h1 h2 => (h_pkg' j (by omega)).2.1)
  rw [show (0 : Nat) + len = len from Nat.zero_add len] at h_tgt
  refine ⟨_, h_tgt, ?_⟩
  rw [h_src']
  rw [show (0 : Nat) + len = len from Nat.zero_add len]
  exact ⟨setChain_chain_respects h_stacks
      (fun j h1 h2 => (h_pkg' j h2).2.2),
    h_prot, h_exp, h_next⟩


/-- BRIDGE 3 family, `sb_read` member: a successful source read through
    `tagS` is matched by a target read through the renamed `tagT`, and the
    results stay `PermSim`-related. Non-wildcard acting tags only. -/
theorem sb_read_respects_PermSim
    {ρt : TagRenameMap} {src tgt src' : AccessPerms}
    {addr : Word} {len : Nat} {tagS tagT : Tag}
    (h_sim : PermSim ρt src tgt)
    (h_wf : TagRenameWF ρt)
    (h_tag : ρt tagS = some tagT)
    (h_ts : (tagS == wildcardTag) = false)
    (h_src : sb_read src addr len tagS = .ok src') :
    ∃ tgt', sb_read tgt addr len tagT = .ok tgt' ∧ PermSim ρt src' tgt' := by
  obtain ⟨h_stacks, h_prot, h_exp, h_next⟩ := h_sim
  have h_src0 : foldCells (fun ap a => readCell ap a tagS) src (addr + 0) len
      = .ok src' := h_src
  obtain ⟨V, W, h_cells, h_src'⟩ :=
    foldCells_ok_inv
      (C := fun a stack => readCellContent src.protFrames src.exposed a tagS stack)
      (msgNone := fun a => s!"sb-read: no borrow stack at address {a}")
      (P := src.protFrames) (E := src.exposed) (N := src.NextTag)
      (fun ap a h_pf h_ex _ => readCell_content_form tagS ap a h_pf h_ex)
      len 0 src src' rfl rfl rfl h_src0
  have h_pkg : ∀ j, ∃ vj, ∃ wj, j < len →
      SB.find? tgt.StackMap (addr + j) = some vj ∧
        readCellContent tgt.protFrames tgt.exposed (addr + j) tagT vj = .ok wj ∧
        StackSim ρt (W j) wj := by
    intro j
    by_cases hj : j < len
    · have hc := h_cells j (Nat.zero_le j) (by omega)
      obtain ⟨s', h_find', h_ss⟩ := SB.find?_transport h_stacks hc.1
      obtain ⟨w', h_w', h_ws⟩ :=
        readCellContent_transport h_wf h_prot h_tag h_ts h_ss hc.2
      exact ⟨s', w', fun _ => ⟨h_find', h_w', h_ws⟩⟩
    · exact ⟨[], [], fun h => absurd h hj⟩
  have h_pkg' : ∀ j, j < len →
      SB.find? tgt.StackMap (addr + j) = some ((h_pkg j).choose) ∧
        readCellContent tgt.protFrames tgt.exposed (addr + j) tagT
          ((h_pkg j).choose) = .ok ((h_pkg j).choose_spec.choose) ∧
        StackSim ρt (W j) ((h_pkg j).choose_spec.choose) :=
    fun j hj => (h_pkg j).choose_spec.choose_spec hj
  have h_tgt : foldCells (fun ap a => readCell ap a tagT) tgt (addr + 0) len =
      .ok { tgt with StackMap := setChain tgt.StackMap (chain (fun j => (h_pkg j).choose_spec.choose) addr 0 (0 + len)) } :=
    foldCells_ok_of_cells
      (C := fun a stack => readCellContent tgt.protFrames tgt.exposed a tagT stack)
      (msgNone := fun a => s!"sb-read: no borrow stack at address {a}")
      (P := tgt.protFrames) (E := tgt.exposed) (N := tgt.NextTag)
      (fun ap a h_pf h_ex _ => readCell_content_form tagT ap a h_pf h_ex)
      len 0 tgt (fun j => (h_pkg j).choose)
      (fun j => (h_pkg j).choose_spec.choose)
      rfl rfl rfl
      (fun j h1 h2 => (h_pkg' j (by omega)).1)
      (fun j h1 h2 => (h_pkg' j (by omega)).2.1)
  rw [show (0 : Nat) + len = len from Nat.zero_add len] at h_tgt
  refine ⟨_, h_tgt, ?_⟩
  rw [h_src']
  rw [show (0 : Nat) + len = len from Nat.zero_add len]
  exact ⟨setChain_chain_respects h_stacks
      (fun j h1 h2 => (h_pkg' j h2).2.2),
    h_prot, h_exp, h_next⟩

/-! ## `sb_ref` in fold-characterizable form

`sb_ref` is the ρt-GROWING member: it mints a fresh tag on each machine
(the values differ — counters only satisfy `≤`), so its transport extends
ρt at the fresh pair and needs `TagRenameBound` for injectivity. The
per-cell operation depends on the `RefKind` and, for `Shared`/`Raw false`,
on the freeze mask at the cell's index — hence the `foldCellsIdx`
characterizations rather than the plain `foldCells` ones. -/

/-- Stack-level content of `insertAboveCell` for a NON-wildcard acting tag
    (the wildcard-resolution branch never fires for compiler-minted or
    core-program tags). -/
def insertAboveContent (a : Word) (tag : Tag) (item : Item)
    (stack : BorrowStack) : Except String BorrowStack :=
  match splitStack stack tag with
  | none => .error s!"sb-insert: tag {tag} does not exist in the borrow stack at {a}"
  | some (_, .Disabled _, _) =>
      .error s!"sb-insert: tag {tag} does not exist in the borrow stack at {a} (disabled)"
  | some (above, granting, below) =>
      .ok (above ++ item :: granting :: below)

/-- `sb_ref`'s per-cell operation, lifted to a top-level definition so the
    fold characterizations can be stated about it (verbatim copy of the
    `cellOp` local in `sb_ref`, with `newItem` inlined per kind). -/
def refCellOp (tag newTag : Tag) (kind : RefKind) (mask : List Bool) :
    AccessPerms → Word → Nat → Except String AccessPerms :=
  match kind with
  | .Mut => fun ap a _ => do pushCell (← writeCell ap a tag) a (.MutRef newTag)
  | .Shared => fun ap a i =>
      if mask.getD i false then
        insertAboveCell ap a tag (.RawPtr true newTag)
      else do
        pushCell (← readCell ap a tag) a (.Ref newTag)
  | .Raw false => fun ap a i =>
      if mask.getD i false then
        insertAboveCell ap a tag (.RawPtr true newTag)
      else do
        pushCell (← readCell ap a tag) a (.RawPtr false newTag)
  | .Raw true => fun ap a _ => insertAboveCell ap a tag (.RawPtr true newTag)
  | .TwoPhase => fun ap a _ =>
      do insertAboveCell (← readCell ap a tag) a tag (.RawPtr true newTag)

/-- The per-cell stack content of `refCellOp`, in the `Option`-consuming
    shape `foldCellsIdx_ok_inv`/`_of_cells` eat. -/
def refCellContent (P : List (List Tag)) (E : List Tag) (a : Word)
    (tag newTag : Tag) (kind : RefKind) (mask : List Bool) (i : Nat) :
    Option BorrowStack → Except String BorrowStack
  | none =>
      match kind with
      | .Mut => .error s!"sb-write: no borrow stack at address {a}"
      | .Shared =>
          if mask.getD i false then
            .error s!"sb-insert: no borrow stack at address {a}"
          else
            .error s!"sb-read: no borrow stack at address {a}"
      | .Raw false =>
          if mask.getD i false then
            .error s!"sb-insert: no borrow stack at address {a}"
          else
            .error s!"sb-read: no borrow stack at address {a}"
      | .Raw true => .error s!"sb-insert: no borrow stack at address {a}"
      | .TwoPhase => .error s!"sb-read: no borrow stack at address {a}"
  | some stack =>
      match kind with
      | .Mut =>
          match writeCellContent P E a tag stack with
          | .error e => .error e
          | .ok v => .ok (.MutRef newTag :: v)
      | .Shared =>
          if mask.getD i false then
            insertAboveContent a tag (.RawPtr true newTag) stack
          else
            match readCellContent P E a tag stack with
            | .error e => .error e
            | .ok v => .ok (.Ref newTag :: v)
      | .Raw false =>
          if mask.getD i false then
            insertAboveContent a tag (.RawPtr true newTag) stack
          else
            match readCellContent P E a tag stack with
            | .error e => .error e
            | .ok v => .ok (.RawPtr false newTag :: v)
      | .Raw true => insertAboveContent a tag (.RawPtr true newTag) stack
      | .TwoPhase =>
          match readCellContent P E a tag stack with
          | .error e => .error e
          | .ok v => insertAboveContent a tag (.RawPtr true newTag) v

theorem refCellContent_none_error
    {P : List (List Tag)} {E : List Tag} {a : Word} {tag newTag : Tag}
    {kind : RefKind} {mask : List Bool} {i : Nat} {w : BorrowStack} :
    refCellContent P E a tag newTag kind mask i none ≠ .ok w := by
  intro h
  cases kind with
  | Mut => simp [refCellContent] at h
  | Shared => cases hm : mask.getD i false <;> simp [refCellContent, hm] at h
  | Raw m =>
      cases m with
      | false => cases hm : mask.getD i false <;> simp [refCellContent, hm] at h
      | true => simp [refCellContent] at h
  | TwoPhase => simp [refCellContent] at h

/-- `sb_ref` unfolded to the `refCellOp` fold plus the protector-frame
    registration (the shape the fold characterizations apply to). -/
theorem sb_ref_unfold (ap : AccessPerms) (addr : Word) (len : Nat) (tag : Tag)
    (kind : RefKind) (prot : Bool) (mask : List Bool) :
    sb_ref ap addr len tag kind prot mask =
      match foldCellsIdx (refCellOp tag ap.NextTag kind mask)
          { ap with NextTag := ap.NextTag + 1 } addr 0 len with
      | .error e => .error e
      | .ok apR =>
          if prot then
            match apR.protFrames with
            | [] => .error "sb-ref: protected retag outside any protector frame"
            | frame :: rest =>
                .ok ({ apR with protFrames := (ap.NextTag :: frame) :: rest },
                  ap.NextTag)
          else .ok (apR, ap.NextTag) := by
  have h_tail : ∀ (r : Except String AccessPerms),
      (do
        let apR ← r
        if prot then
          match apR.protFrames with
          | [] =>
              (.error "sb-ref: protected retag outside any protector frame" :
                Except String (AccessPerms × Tag))
          | frame :: rest =>
              return ({ apR with protFrames := (ap.NextTag :: frame) :: rest },
                ap.NextTag)
        else
          return (apR, ap.NextTag)) =
      match r with
      | .error e => .error e
      | .ok apR =>
          if prot then
            match apR.protFrames with
            | [] => .error "sb-ref: protected retag outside any protector frame"
            | frame :: rest =>
                .ok ({ apR with protFrames := (ap.NextTag :: frame) :: rest },
                  ap.NextTag)
          else .ok (apR, ap.NextTag) := by
    intro r
    cases r with
    | error e => rfl
    | ok apR =>
        cases prot with
        | false => rfl
        | true => cases h : apR.protFrames <;> simp [bind, Except.bind, h]
  cases kind with
  | Mut =>
      simp only [sb_ref, freshTag, RefKind.toItem, refCellOp]
      exact h_tail _
  | Shared =>
      simp only [sb_ref, freshTag, RefKind.toItem, refCellOp]
      exact h_tail _
  | Raw m =>
      cases m with
      | false =>
          simp only [sb_ref, freshTag, RefKind.toItem, refCellOp]
          exact h_tail _
      | true =>
          simp only [sb_ref, freshTag, RefKind.toItem, refCellOp]
          exact h_tail _
  | TwoPhase =>
      simp only [sb_ref, freshTag, RefKind.toItem, refCellOp]
      exact h_tail _

/-- `refCellOp` in the content-driven form the fold characterizations eat
    (NON-wildcard acting tag; `NextTag` plays no role in the op). -/
theorem refCellOp_content_form
    {P : List (List Tag)} {E : List Tag} {addr : Word}
    (tag newTag : Tag) (kind : RefKind) (mask : List Bool)
    (h_ts : (tag == wildcardTag) = false) :
    ∀ (ap : AccessPerms) (i : Nat), ap.protFrames = P → ap.exposed = E →
      refCellOp tag newTag kind mask ap (addr + i) i =
        match refCellContent P E (addr + i) tag newTag kind mask i
            (SB.find? ap.StackMap (addr + i)) with
        | .error e => .error e
        | .ok v => .ok { ap with StackMap := SB.set ap.StackMap (addr + i) v } := by
  intro ap i h_pf h_ex
  have h_insert : ∀ (item : Item),
      insertAboveCell ap (addr + i) tag item =
        match SB.find? ap.StackMap (addr + i) with
        | none => .error s!"sb-insert: no borrow stack at address {addr + i}"
        | some stack =>
          match insertAboveContent (addr + i) tag item stack with
          | .error e => .error e
          | .ok v => .ok { ap with StackMap := SB.set ap.StackMap (addr + i) v } := by
    intro item
    cases h_find : SB.find? ap.StackMap (addr + i) with
    | none => simp only [insertAboveCell, h_find]
    | some stack =>
        simp only [insertAboveCell, h_find, h_ts, Bool.false_eq_true, if_false]
        cases h_split : splitStack stack tag with
        | none => simp [insertAboveContent, h_split]
        | some triple =>
            obtain ⟨ab, it, bl⟩ := triple
            cases it <;> simp [insertAboveContent, h_split]
  cases kind with
  | Mut =>
      cases h_find : SB.find? ap.StackMap (addr + i) with
      | none =>
          simp only [refCellOp, refCellContent, writeCell, h_find, bind, Except.bind]
      | some stack =>
          cases h_content : writeCellContent P E (addr + i) tag stack with
          | error e =>
              simp only [refCellOp, refCellContent, writeCell, h_pf, h_ex, h_find,
                h_content, bind, Except.bind]
          | ok v =>
              simp only [refCellOp, refCellContent, writeCell, h_pf, h_ex, h_find,
                h_content, bind, Except.bind, pushCell, SB.find?_set_self, SB.set_set]
  | Shared =>
      cases h_mask : mask.getD i false with
      | true =>
          simp only [refCellOp, refCellContent, h_mask, if_true]
          rw [h_insert]
          cases h_find : SB.find? ap.StackMap (addr + i) <;> rfl
      | false =>
          simp only [refCellOp, refCellContent, h_mask, Bool.false_eq_true, if_false]
          cases h_find : SB.find? ap.StackMap (addr + i) with
          | none =>
              simp only [readCell, h_find, bind, Except.bind]
          | some stack =>
              cases h_content : readCellContent P E (addr + i) tag stack with
              | error e =>
                  simp only [readCell, h_pf, h_ex, h_find, h_content, bind, Except.bind]
              | ok v =>
                  simp only [readCell, h_pf, h_ex, h_find, h_content, bind, Except.bind,
                    pushCell, SB.find?_set_self, SB.set_set]
  | Raw m =>
      cases m with
      | false =>
          cases h_mask : mask.getD i false with
          | true =>
              simp only [refCellOp, refCellContent, h_mask, if_true]
              rw [h_insert]
              cases h_find : SB.find? ap.StackMap (addr + i) <;> rfl
          | false =>
              simp only [refCellOp, refCellContent, h_mask, Bool.false_eq_true, if_false]
              cases h_find : SB.find? ap.StackMap (addr + i) with
              | none =>
                  simp only [readCell, h_find, bind, Except.bind]
              | some stack =>
                  cases h_content : readCellContent P E (addr + i) tag stack with
                  | error e =>
                      simp only [readCell, h_pf, h_ex, h_find, h_content, bind,
                        Except.bind]
                  | ok v =>
                      simp only [readCell, h_pf, h_ex, h_find, h_content, bind,
                        Except.bind, pushCell, SB.find?_set_self, SB.set_set]
      | true =>
          simp only [refCellOp, refCellContent]
          rw [h_insert]
          cases h_find : SB.find? ap.StackMap (addr + i) <;> rfl
  | TwoPhase =>
      cases h_find : SB.find? ap.StackMap (addr + i) with
      | none =>
          simp only [refCellOp, refCellContent, readCell, h_find, bind, Except.bind]
      | some stack =>
          cases h_content : readCellContent P E (addr + i) tag stack with
          | error e =>
              simp only [refCellOp, refCellContent, readCell, h_pf, h_ex, h_find,
                h_content, bind, Except.bind]
          | ok v =>
              simp only [refCellOp, refCellContent, readCell, h_pf, h_ex, h_find,
                h_content, bind, Except.bind]
              rw [show insertAboveCell { ap with StackMap := SB.set ap.StackMap (addr + i) v }
                    (addr + i) tag (.RawPtr true newTag) =
                  match SB.find? (SB.set ap.StackMap (addr + i) v) (addr + i) with
                  | none => .error s!"sb-insert: no borrow stack at address {addr + i}"
                  | some stack =>
                    match insertAboveContent (addr + i) tag (.RawPtr true newTag) stack with
                    | .error e => .error e
                    | .ok u => .ok { ap with StackMap :=
                        SB.set (SB.set ap.StackMap (addr + i) v) (addr + i) u }
                  from by
                    cases h_find' : SB.find? (SB.set ap.StackMap (addr + i) v) (addr + i) with
                    | none => simp only [insertAboveCell, h_find']
                    | some stack' =>
                        simp only [insertAboveCell, h_find', h_ts, Bool.false_eq_true,
                          if_false]
                        cases h_split : splitStack stack' tag with
                        | none => simp [insertAboveContent, h_split]
                        | some triple =>
                            obtain ⟨ab, it, bl⟩ := triple
                            cases it <;> simp [insertAboveContent, h_split]]
              rw [SB.find?_set_self]
              cases h_ins : insertAboveContent (addr + i) tag (.RawPtr true newTag) v with
              | error e => rfl
              | ok u => simp only [SB.set_set]

/-- `insertAboveContent` transport: the untouched stack parts stay related,
    and the inserted items are related by hypothesis. -/
theorem insertAboveContent_transport
    {ρt : TagRenameMap} {a a' : Word} {tagS tagT : Tag}
    {itemS itemT : Item} {v v' w : BorrowStack}
    (h_wf : TagRenameWF ρt)
    (h_t : ρt tagS = some tagT)
    (h_item : ItemSim ρt itemS itemT)
    (h_v : StackSim ρt v v')
    (h_ok : insertAboveContent a tagS itemS v = .ok w) :
    ∃ w', insertAboveContent a' tagT itemT v' = .ok w' ∧ StackSim ρt w w' := by
  unfold insertAboveContent at h_ok ⊢
  cases h_split : splitStack v tagS with
  | none => simp [h_split] at h_ok
  | some triple =>
      obtain ⟨ab, it, bl⟩ := triple
      obtain ⟨ab', it', bl', h_split', h_ab, h_it, h_bl⟩ :=
        splitStack_some_transport h_wf h_t h_v h_split
      simp only [h_split] at h_ok
      simp only [h_split']
      cases it with
      | Disabled t => simp at h_ok
      | Own t =>
          cases it' <;> simp only [ItemSim] at h_it
          simp only [Except.ok.injEq] at h_ok
          refine ⟨_, rfl, ?_⟩
          rw [← h_ok]
          exact ListRel.append h_ab ⟨h_item, by simp [ItemSim]; exact h_it, h_bl⟩
      | MutRef t =>
          cases it' <;> simp only [ItemSim] at h_it
          simp only [Except.ok.injEq] at h_ok
          refine ⟨_, rfl, ?_⟩
          rw [← h_ok]
          exact ListRel.append h_ab ⟨h_item, by simp [ItemSim]; exact h_it, h_bl⟩
      | Ref t =>
          cases it' <;> simp only [ItemSim] at h_it
          simp only [Except.ok.injEq] at h_ok
          refine ⟨_, rfl, ?_⟩
          rw [← h_ok]
          exact ListRel.append h_ab ⟨h_item, by simp [ItemSim]; exact h_it, h_bl⟩
      | RawPtr m t =>
          cases it' <;> simp only [ItemSim] at h_it
          rw [h_it.1]
          simp only [Except.ok.injEq] at h_ok
          refine ⟨_, rfl, ?_⟩
          rw [← h_ok]
          exact ListRel.append h_ab
            ⟨h_item, by simp [ItemSim]; exact h_it.2, h_bl⟩

/-- `refCellContent` transport: relates the per-cell results of the two
    machines' retag folds. `h_new` is the fresh-pair mapping — callers
    instantiate ρt with the EXTENDED rename map. -/
theorem refCellContent_transport
    {ρt : TagRenameMap} {pfS pfT : List (List Tag)} {exS exT : List Tag}
    {a a' : Word} {tagS tagT newTagS newTagT : Tag}
    {kind : RefKind} {mask : List Bool} {i : Nat}
    {v v' w : BorrowStack}
    (h_wf : TagRenameWF ρt)
    (h_pf : ListRel (TagListSim ρt) pfS pfT)
    (h_t : ρt tagS = some tagT)
    (h_ts : (tagS == wildcardTag) = false)
    (h_new : ρt newTagS = some newTagT)
    (h_v : StackSim ρt v v')
    (h_ok : refCellContent pfS exS a tagS newTagS kind mask i (some v) = .ok w) :
    ∃ w', refCellContent pfT exT a' tagT newTagT kind mask i (some v') = .ok w' ∧
      StackSim ρt w w' := by
  cases kind with
  | Mut =>
      simp only [refCellContent] at h_ok ⊢
      cases h_w : writeCellContent pfS exS a tagS v with
      | error e => simp [h_w] at h_ok
      | ok u =>
          simp only [h_w, Except.ok.injEq] at h_ok
          obtain ⟨u', h_w', h_u⟩ :=
            writeCellContent_transport h_wf h_pf h_t h_ts h_v h_w
          simp only [h_w']
          refine ⟨_, rfl, ?_⟩
          rw [← h_ok]
          exact ⟨by simp [ItemSim]; exact h_new, h_u⟩
  | Shared =>
      cases h_mask : mask.getD i false with
      | true =>
          simp only [refCellContent, h_mask, if_true] at h_ok ⊢
          exact insertAboveContent_transport h_wf h_t
            (by simp [ItemSim]; exact h_new) h_v h_ok
      | false =>
          simp only [refCellContent, h_mask, Bool.false_eq_true, if_false] at h_ok ⊢
          cases h_r : readCellContent pfS exS a tagS v with
          | error e => simp [h_r] at h_ok
          | ok u =>
              simp only [h_r, Except.ok.injEq] at h_ok
              obtain ⟨u', h_r', h_u⟩ :=
                readCellContent_transport h_wf h_pf h_t h_ts h_v h_r
              simp only [h_r']
              refine ⟨_, rfl, ?_⟩
              rw [← h_ok]
              exact ⟨by simp [ItemSim]; exact h_new, h_u⟩
  | Raw m =>
      cases m with
      | false =>
          cases h_mask : mask.getD i false with
          | true =>
              simp only [refCellContent, h_mask, if_true] at h_ok ⊢
              exact insertAboveContent_transport h_wf h_t
                (by simp [ItemSim]; exact h_new) h_v h_ok
          | false =>
              simp only [refCellContent, h_mask, Bool.false_eq_true, if_false]
                at h_ok ⊢
              cases h_r : readCellContent pfS exS a tagS v with
              | error e => simp [h_r] at h_ok
              | ok u =>
                  simp only [h_r, Except.ok.injEq] at h_ok
                  obtain ⟨u', h_r', h_u⟩ :=
                    readCellContent_transport h_wf h_pf h_t h_ts h_v h_r
                  simp only [h_r']
                  refine ⟨_, rfl, ?_⟩
                  rw [← h_ok]
                  exact ⟨by simp [ItemSim]; exact h_new, h_u⟩
      | true =>
          simp only [refCellContent] at h_ok ⊢
          exact insertAboveContent_transport h_wf h_t
            (by simp [ItemSim]; exact h_new) h_v h_ok
  | TwoPhase =>
      simp only [refCellContent] at h_ok ⊢
      cases h_r : readCellContent pfS exS a tagS v with
      | error e => simp [h_r] at h_ok
      | ok u =>
          simp only [h_r] at h_ok
          obtain ⟨u', h_r', h_u⟩ :=
            readCellContent_transport h_wf h_pf h_t h_ts h_v h_r
          simp only [h_r']
          exact insertAboveContent_transport h_wf h_t
            (by simp [ItemSim]; exact h_new) h_u h_ok

/-- BRIDGE 3 family, `sb_ref` member — the ρt-GROWING transport: a
    successful source retag through `tagS` is matched by a target retag
    through the renamed `tagT`. The fresh tags are the two counters (which
    DIFFER), so the results are related under ρt extended at the fresh
    pair; `TagRenameBound` makes the extension injective, and the lemma
    returns the re-established bound at the bumped counters. Non-wildcard
    acting tags only. -/
theorem sb_ref_respects_PermSim
    {ρt : TagRenameMap} {src tgt src' : AccessPerms}
    {addr : Word} {len : Nat} {tagS tagT tS' : Tag}
    {kind : RefKind} {prot : Bool} {mask : List Bool}
    (h_sim : PermSim ρt src tgt)
    (h_wf : TagRenameWF ρt)
    (h_bound : TagRenameBound ρt src.NextTag tgt.NextTag)
    (h_tag : ρt tagS = some tagT)
    (h_ts : (tagS == wildcardTag) = false)
    (h_src : sb_ref src addr len tagS kind prot mask = .ok (src', tS')) :
    ∃ tgt',
      sb_ref tgt addr len tagT kind prot mask = .ok (tgt', tgt.NextTag) ∧
      tS' = src.NextTag ∧
      src'.NextTag = src.NextTag + 1 ∧
      tgt'.NextTag = tgt.NextTag + 1 ∧
      PermSim (ρt.extend src.NextTag tgt.NextTag) src' tgt' ∧
      TagRenameWF (ρt.extend src.NextTag tgt.NextTag) ∧
      TagRenameIncr ρt (ρt.extend src.NextTag tgt.NextTag) ∧
      TagRenameBound (ρt.extend src.NextTag tgt.NextTag)
        (src.NextTag + 1) (tgt.NextTag + 1) := by
  -- The extended rename map and its facts.
  have h_incr : TagRenameIncr ρt (ρt.extend src.NextTag tgt.NextTag) :=
    h_bound.extend_incr
  have h_wf' : TagRenameWF (ρt.extend src.NextTag tgt.NextTag) :=
    h_wf.extend h_bound
  have h_bound' : TagRenameBound (ρt.extend src.NextTag tgt.NextTag)
      (src.NextTag + 1) (tgt.NextTag + 1) := h_bound.extend
  have h_tag' : ρt.extend src.NextTag tgt.NextTag tagS = some tagT := h_incr _ _ h_tag
  have h_new' : ρt.extend src.NextTag tgt.NextTag src.NextTag = some tgt.NextTag :=
    TagRenameMap.extend_self ρt _ _
  obtain ⟨h_stacks', h_prot', h_exp', h_next⟩ := h_sim.rename_mono h_incr
  -- Unfold the source retag and invert its fold.
  rw [sb_ref_unfold] at h_src
  cases h_goS : foldCellsIdx (refCellOp tagS src.NextTag kind mask)
      { src with NextTag := src.NextTag + 1 } addr 0 len with
  | error e =>
      rw [h_goS] at h_src
      simp at h_src
  | ok apS =>
      rw [h_goS] at h_src
      simp only at h_src
      obtain ⟨W, h_cellsS, h_apS⟩ :=
        foldCellsIdx_ok_inv
          (C := fun i v? => refCellContent src.protFrames src.exposed (addr + i)
            tagS src.NextTag kind mask i v?)
          (P := src.protFrames) (E := src.exposed) (N := src.NextTag + 1)
          (fun ap i h_pf h_ex _ =>
            refCellOp_content_form tagS src.NextTag kind mask h_ts ap i h_pf h_ex)
          { src with NextTag := src.NextTag + 1 } apS rfl rfl rfl h_goS
      rw [show ({ src with NextTag := src.NextTag + 1 } : AccessPerms).StackMap
            = src.StackMap from rfl] at h_cellsS
      -- Per-cell target packaging: source find? and content succeed, so the
      -- target's do too, with `StackSim`-related results under the extension.
      have h_pkg : ∀ j, ∃ vj, ∃ wj, j < len →
          SB.find? tgt.StackMap (addr + j) = some vj ∧
            refCellContent tgt.protFrames tgt.exposed (addr + j) tagT tgt.NextTag
              kind mask j (some vj) = .ok wj ∧
            StackSim (ρt.extend src.NextTag tgt.NextTag) (W j) wj := by
        intro j
        by_cases hj : j < len
        · have hc := h_cellsS j (Nat.zero_le j) hj
          cases h_find : SB.find? src.StackMap (addr + j) with
          | none =>
              rw [h_find] at hc
              exact absurd hc refCellContent_none_error
          | some vj =>
              rw [h_find] at hc
              obtain ⟨vj', h_find', h_vs⟩ := SB.find?_transport h_stacks' h_find
              obtain ⟨wj', h_wj', h_ws⟩ :=
                refCellContent_transport h_wf' h_prot' h_tag' h_ts h_new' h_vs hc
              exact ⟨vj', wj', fun _ => ⟨h_find', h_wj', h_ws⟩⟩
        · exact ⟨[], [], fun h => absurd h hj⟩
      have h_pkg' : ∀ j, j < len →
          SB.find? tgt.StackMap (addr + j) = some ((h_pkg j).choose) ∧
            refCellContent tgt.protFrames tgt.exposed (addr + j) tagT tgt.NextTag
              kind mask j (some ((h_pkg j).choose)) = .ok ((h_pkg j).choose_spec.choose) ∧
            StackSim (ρt.extend src.NextTag tgt.NextTag) (W j)
              ((h_pkg j).choose_spec.choose) :=
        fun j hj => (h_pkg j).choose_spec.choose_spec hj
      -- Run the target fold.
      have h_goT : foldCellsIdx (refCellOp tagT tgt.NextTag kind mask)
          { tgt with NextTag := tgt.NextTag + 1 } addr 0 len =
          .ok { tgt with NextTag := tgt.NextTag + 1, StackMap :=
            setChain tgt.StackMap
              (chain (fun j => (h_pkg j).choose_spec.choose) addr 0 len) } := by
        have h_tt : (tagT == wildcardTag) = false := by
          rw [h_wf.beq_eq h_tag h_wf.2]
          exact h_ts
        exact foldCellsIdx_ok_of_cells
          (C := fun i v? => refCellContent tgt.protFrames tgt.exposed (addr + i)
            tagT tgt.NextTag kind mask i v?)
          (P := tgt.protFrames) (E := tgt.exposed) (N := tgt.NextTag + 1)
          (fun ap i h_pf h_ex _ =>
            refCellOp_content_form tagT tgt.NextTag kind mask h_tt ap i h_pf h_ex)
          { tgt with NextTag := tgt.NextTag + 1 }
          (fun j => (h_pkg j).choose_spec.choose)
          rfl rfl rfl
          (fun j h1 h2 => by
            rw [show ({ tgt with NextTag := tgt.NextTag + 1 } : AccessPerms).StackMap
                  = tgt.StackMap from rfl, (h_pkg' j h2).1]
            exact (h_pkg' j h2).2.1)
      -- The folded states are `PermSim`-related under the extension.
      have h_stacksR : ListRel (CellSim (ρt.extend src.NextTag tgt.NextTag))
          (setChain src.StackMap (chain W addr 0 len))
          (setChain tgt.StackMap
            (chain (fun j => (h_pkg j).choose_spec.choose) addr 0 len)) :=
        setChain_chain_respects h_stacks' (fun j h1 h2 => (h_pkg' j h2).2.2)
      -- Discharge the protector-registration branch and assemble.
      rw [sb_ref_unfold, h_goT]
      subst h_apS
      cases prot with
      | false =>
          simp only [Bool.false_eq_true, if_false, Except.ok.injEq, Prod.mk.injEq]
            at h_src
          obtain ⟨h_eq1, h_eq2⟩ := h_src
          refine ⟨_, rfl, h_eq2.symm, ?_, rfl, ?_, h_wf', h_incr, h_bound'⟩
          · rw [← h_eq1]
          · rw [← h_eq1]
            exact ⟨h_stacksR, h_prot', h_exp', Nat.succ_le_succ h_next⟩
      | true =>
          simp only [if_true] at h_src ⊢
          cases h_pfS : src.protFrames with
          | nil =>
              rw [show ({ src with NextTag := src.NextTag + 1, StackMap :=
                    setChain src.StackMap (chain W addr 0 len) }
                  : AccessPerms).protFrames = src.protFrames from rfl, h_pfS] at h_src
              simp at h_src
          | cons frame rest =>
              rw [show ({ src with NextTag := src.NextTag + 1, StackMap :=
                    setChain src.StackMap (chain W addr 0 len) }
                  : AccessPerms).protFrames = src.protFrames from rfl, h_pfS] at h_src
              simp only [Except.ok.injEq, Prod.mk.injEq] at h_src
              obtain ⟨h_eq1, h_eq2⟩ := h_src
              -- Target frames are nonempty and related.
              rw [h_pfS] at h_prot'
              cases h_pfT : tgt.protFrames with
              | nil =>
                  rw [h_pfT] at h_prot'
                  simp [ListRel] at h_prot'
              | cons frame' rest' =>
                  rw [h_pfT] at h_prot'
                  simp only [ListRel] at h_prot'
                  rw [show ({ tgt with NextTag := tgt.NextTag + 1, StackMap :=
                        setChain tgt.StackMap
                          (chain (fun j => (h_pkg j).choose_spec.choose) addr 0 len) }
                      : AccessPerms).protFrames = tgt.protFrames from rfl, h_pfT]
                  refine ⟨_, rfl, h_eq2.symm ▸ rfl, ?_, rfl, ?_, h_wf', h_incr, h_bound'⟩
                  · rw [← h_eq1]
                  · rw [← h_eq1]
                    refine ⟨h_stacksR, ?_, h_exp', Nat.succ_le_succ h_next⟩
                    exact ⟨⟨h_new', h_prot'.1⟩, h_prot'.2⟩

/-- BRIDGE 3 family, `sb_die` member: a successful source die through
    `tagS` is matched by a target die through the renamed `tagT`, and the
    results stay `PermSim`-related. (No wildcard side condition: `die` is
    only ever invoked on compiler-minted tags.) -/
theorem sb_die_respects_PermSim
    {ρt : TagRenameMap} {src tgt src' : AccessPerms}
    {addr : Word} {len : Nat} {tagS tagT : Tag}
    (h_sim : PermSim ρt src tgt)
    (h_wf : TagRenameWF ρt)
    (h_tag : ρt tagS = some tagT)
    (h_src : sb_die src addr len tagS = .ok src') :
    ∃ tgt', sb_die tgt addr len tagT = .ok tgt' ∧ PermSim ρt src' tgt' := by
  obtain ⟨h_stacks, h_prot, h_exp, h_next⟩ := h_sim
  have h_src0 : foldCells
      (fun ap a =>
        match ap.StackMap.find? a with
        | none => .error s!"sb-die: no borrow stack at address {a}"
        | some stack =>
            match dieCellContent ap.protFrames tagS stack with
            | .error e => .error e
            | .ok below => .ok { ap with StackMap := ap.StackMap.set a below })
      src (addr + 0) len = .ok src' := h_src
  obtain ⟨V, W, h_cells, h_src'⟩ :=
    foldCells_ok_inv
      (C := fun _ stack => dieCellContent src.protFrames tagS stack)
      (msgNone := fun a => s!"sb-die: no borrow stack at address {a}")
      (P := src.protFrames) (E := src.exposed) (N := src.NextTag)
      (fun ap a h_pf h_ex _ => by simp only [h_pf]; rfl)
      len 0 src src' rfl rfl rfl h_src0
  have h_pkg : ∀ j, ∃ vj, ∃ wj, j < len →
      SB.find? tgt.StackMap (addr + j) = some vj ∧
        dieCellContent tgt.protFrames tagT vj = .ok wj ∧
        StackSim ρt (W j) wj := by
    intro j
    by_cases hj : j < len
    · have hc := h_cells j (Nat.zero_le j) (by omega)
      obtain ⟨s', h_find', h_ss⟩ := SB.find?_transport h_stacks hc.1
      obtain ⟨w', h_w', h_ws⟩ :=
        dieCellContent_transport h_wf h_prot h_tag h_ss hc.2
      exact ⟨s', w', fun _ => ⟨h_find', h_w', h_ws⟩⟩
    · exact ⟨[], [], fun h => absurd h hj⟩
  have h_pkg' : ∀ j, j < len →
      SB.find? tgt.StackMap (addr + j) = some ((h_pkg j).choose) ∧
        dieCellContent tgt.protFrames tagT ((h_pkg j).choose)
          = .ok ((h_pkg j).choose_spec.choose) ∧
        StackSim ρt (W j) ((h_pkg j).choose_spec.choose) :=
    fun j hj => (h_pkg j).choose_spec.choose_spec hj
  have h_tgt : foldCells
      (fun ap a =>
        match ap.StackMap.find? a with
        | none => .error s!"sb-die: no borrow stack at address {a}"
        | some stack =>
            match dieCellContent ap.protFrames tagT stack with
            | .error e => .error e
            | .ok below => .ok { ap with StackMap := ap.StackMap.set a below })
      tgt (addr + 0) len =
      .ok { tgt with StackMap := setChain tgt.StackMap (chain (fun j => (h_pkg j).choose_spec.choose) addr 0 (0 + len)) } :=
    foldCells_ok_of_cells
      (C := fun _ stack => dieCellContent tgt.protFrames tagT stack)
      (msgNone := fun a => s!"sb-die: no borrow stack at address {a}")
      (P := tgt.protFrames) (E := tgt.exposed) (N := tgt.NextTag)
      (fun ap a h_pf h_ex _ => by simp only [h_pf]; rfl)
      len 0 tgt (fun j => (h_pkg j).choose)
      (fun j => (h_pkg j).choose_spec.choose)
      rfl rfl rfl
      (fun j h1 h2 => (h_pkg' j (by omega)).1)
      (fun j h1 h2 => (h_pkg' j (by omega)).2.1)
  rw [show (0 : Nat) + len = len from Nat.zero_add len] at h_tgt
  refine ⟨_, h_tgt, ?_⟩
  rw [h_src']
  rw [show (0 : Nat) + len = len from Nat.zero_add len]
  exact ⟨setChain_chain_respects h_stacks
      (fun j h1 h2 => (h_pkg' j h2).2.2),
    h_prot, h_exp, h_next⟩

end obseq3.proof
