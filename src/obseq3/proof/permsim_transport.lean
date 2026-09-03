import obseq3.proof.common
import obseq3.proof.keystone

/-!
BRIDGE 3 — SB operations respect `PermSim`: renamed-equal states with a
renamed acting tag produce renamed-equal results. The proof is the
transport family sketched in the refactor assessment (journal
2026-08-18): generic `ListRel` transports, tag/beq transport under
`TagRenameWF`, `splitStack`/`firstProtectedIn`/`writeCellContent`
transports, and the `setChain` machinery from the keystone re-run
relationally.

The family is COMPLETE — all five range ops:
- non-minting (ρt fixed): `sb_write` (2026-08-18), `sb_read` and
  `sb_die` (2026-08-19). These also leave `NextTag` alone, which is what
  makes `TagRenameBounded` free to re-establish across them
  (`sb_*_NextTag`).
- minting (ρt GROWS at the fresh pair): `sb_ref` and `sb_own`
  (2026-08-22). Both conclude for `ρt.extend srcFresh tgtFresh` and both
  need `TagRenameBounded` to keep that extension well-formed. `sb_ref`
  carries the retag-kind analysis (`refCellContent`/`refCellStep`);
  `sb_own` is the easy sibling — one cell op, no kind, no mask, no
  protector tail — but it is the only op whose cell action SUCCEEDS on a
  missing stack, so it reaches the fold characterizations through
  `foldCells_ok_iff_foldCellsIdx_ok`.

Scope note: the acting tag is assumed non-wildcard
(`(tagS == wildcardTag) = false`). Wildcard resolution transport
(`resolveWildcardIn` over the renamed exposed set) is deliberately out of
scope: proof-core programs cannot mint wildcard pointers (`fromExposed`
is not a core rvalue), so no core acting tag is ever the wildcard. The non-core
constructs that DO mint wildcards (`fromExposed`) are out of the proof
core, so their `resolveWildcardIn` transport is deferred with them.
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

/-! ## `insertAboveContent` transport -/

/-- Transport for the access-free retag placement. Unlike the access
    contents this one carries a *new* item on each side (the machines mint
    different fresh tags), so the inserted items are related by `ItemSim`
    rather than equal. No protector hypothesis: `insertAbove` pops nothing,
    so nothing can be protected against. -/
theorem insertAboveContent_transport
    {ρt : TagRenameMap} {exS exT : List Tag}
    {a a' : Word} {tagS tagT : Tag} {itS itT : Item}
    {v v' : BorrowStack} {w : BorrowStack}
    (h_wf : TagRenameWF ρt)
    (h_t : ρt tagS = some tagT)
    (h_ts : (tagS == wildcardTag) = false)
    (h_it : ItemSim ρt itS itT)
    (h_v : StackSim ρt v v')
    (h_ok : insertAboveContent exS a tagS itS v = .ok w) :
    ∃ w', insertAboveContent exT a' tagT itT v' = .ok w' ∧ StackSim ρt w w' := by
  have h_tt : (tagT == wildcardTag) = false := by
    rw [h_wf.beq_eq h_t h_wf.2]
    exact h_ts
  unfold insertAboveContent at h_ok ⊢
  rw [h_ts] at h_ok
  rw [h_tt]
  simp only [Bool.false_eq_true, if_false] at h_ok ⊢
  cases h_split : splitStack v tagS with
  | none => simp [h_split] at h_ok
  | some triple =>
      obtain ⟨ab, gr, bl⟩ := triple
      obtain ⟨ab', gr', bl', h_split', h_ab, h_gr, h_bl⟩ :=
        splitStack_some_transport h_wf h_t h_v h_split
      simp only [h_split] at h_ok
      simp only [h_split']
      -- The granting item cannot be `Disabled` on either side, and
      -- `ItemSim` preserves the constructor, so the two machines take the
      -- same branch of the placement match.
      cases gr <;> cases gr' <;> simp only [ItemSim] at h_gr <;>
        simp only [Except.ok.injEq] at h_ok ⊢ <;>
        first
          | exact absurd h_ok (by simp)
          | (refine ⟨_, rfl, ?_⟩
             rw [← h_ok]
             exact ListRel.append h_ab ⟨h_it, by simp only [ItemSim]; exact h_gr, h_bl⟩)
          | (refine ⟨_, rfl, ?_⟩
             rw [← h_ok]
             exact ListRel.append h_ab ⟨h_it, ⟨h_gr.1, h_gr.2⟩, h_bl⟩)

/-- `insertAboveCell` in content-driven form (the shape `foldCellsIdx_ok_inv`
    and `foldCellsIdx_ok_of_cells` consume). -/
theorem insertAboveCell_content_form
    {E : List Tag} (t : Tag) (it : Item) (ap : AccessPerms) (a : Word)
    (h_ex : ap.exposed = E) :
    insertAboveCell ap a t it =
      match SB.find? ap.StackMap a with
      | none => .error s!"sb-insert: no borrow stack at address {a}"
      | some stack =>
        match insertAboveContent E a t it stack with
        | .error e => .error e
        | .ok v => .ok { ap with StackMap := SB.set ap.StackMap a v } := by
  cases h_find : SB.find? ap.StackMap a with
  | none => simp only [insertAboveCell, h_find]
  | some stack =>
      cases h_content : insertAboveContent E a t it stack with
      | error e => simp only [insertAboveCell, h_ex, h_find, h_content]
      | ok v => simp only [insertAboveCell, h_ex, h_find, h_content]

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

/-! ## `sb_ref`'s per-cell op in content form

`sb_ref` is the one range op whose per-cell action varies with the retag
kind and the freeze mask, and whose action is a COMPOSITION of primitives
(access-then-place) rather than a single content rewrite. `refCellContent`
collapses each variant to a single stack-to-stack function so that the same
`foldCellsIdx` inversion/construction pair the other members use applies
here too. -/

/-- The stack-level content of one cell of a retag: the parent access (if
    the variant performs one) followed by the placement of the child item —
    on top for `Mut`/`Shared`/`Raw false`, directly above the granting item
    for the access-free SharedReadWrite variants. -/
def refCellContent (pf : List (List Tag)) (ex : List Tag) (a : Word) (tag : Tag)
    (kind : RefKind) (newTag : Tag) (mask : List Bool) (i : Nat)
    (stack : BorrowStack) : Except String BorrowStack :=
  match kind with
  | .Mut =>
      match writeCellContent pf ex a tag stack with
      | .error e => .error e
      | .ok v => .ok (Item.MutRef newTag :: v)
  | .Shared =>
      if mask.getD i false then insertAboveContent ex a tag (.RawPtr true newTag) stack
      else
        match readCellContent pf ex a tag stack with
        | .error e => .error e
        | .ok v => .ok (Item.Ref newTag :: v)
  | .Raw false =>
      if mask.getD i false then insertAboveContent ex a tag (.RawPtr true newTag) stack
      else
        match readCellContent pf ex a tag stack with
        | .error e => .error e
        | .ok v => .ok (Item.RawPtr false newTag :: v)
  | .Raw true => insertAboveContent ex a tag (.RawPtr true newTag) stack
  | .TwoPhase =>
      match readCellContent pf ex a tag stack with
      | .error e => .error e
      | .ok v => insertAboveContent ex a tag (.RawPtr true newTag) v

/-- `refCellContent` extended over the missing-stack case, i.e. the `C` that
    `foldCellsIdx_ok_inv`/`_ok_of_cells` consume. The error strings are the
    ones the composed primitives actually produce (they are never inspected;
    they only have to make the content form hold definitionally). -/
def refCellStep (pf : List (List Tag)) (ex : List Tag) (a : Word) (tag : Tag)
    (kind : RefKind) (newTag : Tag) (mask : List Bool) (i : Nat) :
    Option BorrowStack → Except String BorrowStack
  | none =>
      match kind with
      | .Mut => .error s!"sb-write: no borrow stack at address {a}"
      | .Shared | .Raw false =>
          if mask.getD i false then .error s!"sb-insert: no borrow stack at address {a}"
          else .error s!"sb-read: no borrow stack at address {a}"
      | .Raw true => .error s!"sb-insert: no borrow stack at address {a}"
      | .TwoPhase => .error s!"sb-read: no borrow stack at address {a}"
  | some stack => refCellContent pf ex a tag kind newTag mask i stack

/-- The content form of `refCellOp`: one cell's action is a rewrite of that
    cell's stack, leaving `protFrames`/`exposed`/`NextTag` alone. The
    composed variants (`access; place`) collapse via `SB.find?_set_self`
    (the placement sees the stack the access just wrote) and `SB.set_set`
    (the two writes to one cell fuse). -/
theorem refCellOp_content_form
    {P : List (List Tag)} {E : List Tag} {N : Tag} {addr : Word}
    (tag : Tag) (kind : RefKind) (newTag : Tag) (mask : List Bool) :
    ∀ ap i, ap.protFrames = P → ap.exposed = E → ap.NextTag = N →
      refCellOp tag kind newTag mask ap (addr + i) i =
        match refCellStep P E (addr + i) tag kind newTag mask i
            (SB.find? ap.StackMap (addr + i)) with
        | .error e => .error e
        | .ok v => .ok { ap with StackMap := SB.set ap.StackMap (addr + i) v } := by
  intro ap i h_pf h_ex _
  -- Resolve the cell FIRST: with `h_find` in every rewrite set both sides
  -- reduce past their outer `Option` match, which is what lets the inner
  -- content result be case-split as a genuine subterm.
  cases h_find : SB.find? ap.StackMap (addr + i) with
  | none =>
      cases kind with
      | Mut =>
          simp only [refCellOp, refCellStep, h_find,
            writeCell_content_form tag ap (addr + i) h_pf h_ex, bind, Except.bind]
      | Shared =>
          simp only [refCellOp, refCellStep, h_find,
            insertAboveCell_content_form (E := E) tag (.RawPtr true newTag) ap (addr + i) h_ex,
            readCell_content_form tag ap (addr + i) h_pf h_ex, bind, Except.bind]
          split <;> rfl
      | Raw m =>
          cases m with
          | true =>
              simp only [refCellOp, refCellStep, h_find,
                insertAboveCell_content_form (E := E) tag (.RawPtr true newTag) ap (addr + i) h_ex]
          | false =>
              simp only [refCellOp, refCellStep, h_find,
                insertAboveCell_content_form (E := E) tag (.RawPtr true newTag) ap (addr + i) h_ex,
                readCell_content_form tag ap (addr + i) h_pf h_ex, bind, Except.bind]
              split <;> rfl
      | TwoPhase =>
          simp only [refCellOp, refCellStep, h_find,
            readCell_content_form tag ap (addr + i) h_pf h_ex, bind, Except.bind]
  | some stack =>
      -- `access; push`: the push reads the stack the access just wrote
      -- (`SB.find?_set_self`) and the two writes to the cell fuse
      -- (`SB.set_set`).
      have h_read : ∀ (it : Item),
          (do pushCell (← readCell ap (addr + i) tag) (addr + i) it)
            = match (match readCellContent P E (addr + i) tag stack with
                     | Except.error e => Except.error e
                     | Except.ok v => Except.ok (it :: v)) with
              | Except.error e => Except.error e
              | Except.ok v =>
                  Except.ok { ap with StackMap := SB.set ap.StackMap (addr + i) v } := by
        intro it
        simp only [readCell_content_form tag ap (addr + i) h_pf h_ex, h_find]
        cases h_c : readCellContent P E (addr + i) tag stack with
        | error e => simp only [bind, Except.bind]
        | ok v =>
            simp only [bind, Except.bind, pushCell, SB.find?_set_self, SB.set_set]
      cases kind with
      | Mut =>
          simp only [refCellOp, refCellStep, refCellContent, h_find,
            writeCell_content_form tag ap (addr + i) h_pf h_ex]
          cases h_c : writeCellContent P E (addr + i) tag stack with
          | error e => simp only [bind, Except.bind]
          | ok v =>
              simp only [bind, Except.bind, pushCell, SB.find?_set_self, SB.set_set]
      | Shared =>
          simp only [refCellOp, refCellStep, refCellContent, h_find]
          by_cases h_m : mask.getD i false = true
          · simp only [if_pos h_m,
              insertAboveCell_content_form (E := E) tag (.RawPtr true newTag) ap (addr + i) h_ex,
              h_find]
          · simp only [if_neg h_m]
            exact h_read (Item.Ref newTag)
      | Raw m =>
          cases m with
          | true =>
              simp only [refCellOp, refCellStep, refCellContent, h_find,
                insertAboveCell_content_form (E := E) tag (.RawPtr true newTag) ap (addr + i) h_ex]
          | false =>
              simp only [refCellOp, refCellStep, refCellContent, h_find]
              by_cases h_m : mask.getD i false = true
              · simp only [if_pos h_m,
                  insertAboveCell_content_form (E := E) tag (.RawPtr true newTag) ap (addr + i) h_ex,
                  h_find]
              · simp only [if_neg h_m]
                exact h_read (Item.RawPtr false newTag)
      | TwoPhase =>
          simp only [refCellOp, refCellStep, refCellContent, h_find,
            readCell_content_form tag ap (addr + i) h_pf h_ex]
          cases h_c : readCellContent P E (addr + i) tag stack with
          | error e => simp only [bind, Except.bind]
          | ok v =>
              simp only [bind, Except.bind,
                insertAboveCell_content_form (E := E) tag (.RawPtr true newTag)
                  { ap with StackMap := SB.set ap.StackMap (addr + i) v } (addr + i) h_ex,
                SB.find?_set_self]
              cases h_ins : insertAboveContent E (addr + i) tag (.RawPtr true newTag) v with
              | error e => rfl
              | ok w => simp only [SB.set_set]

/-- Only a present stack can produce a successful cell step. -/
theorem refCellStep_ok_inv
    {pf : List (List Tag)} {ex : List Tag} {a : Word} {tag : Tag}
    {kind : RefKind} {newTag : Tag} {mask : List Bool} {i : Nat}
    {v? : Option BorrowStack} {w : BorrowStack}
    (h : refCellStep pf ex a tag kind newTag mask i v? = .ok w) :
    ∃ v, v? = some v ∧ refCellContent pf ex a tag kind newTag mask i v = .ok w := by
  cases v? with
  | some v => exact ⟨v, rfl, h⟩
  | none =>
      exfalso
      cases kind <;> simp only [refCellStep] at h <;> grind

/-- Transport for one cell of a retag. The child item is the one place where
    the two machines differ by construction (each mints at its own counter),
    so the fresh pair enters as `h_new` and the pushed/inserted items are
    `ItemSim`-related rather than equal. -/
theorem refCellContent_transport
    {ρt : TagRenameMap} {pfS pfT : List (List Tag)} {exS exT : List Tag}
    {a a' : Word} {tagS tagT newS newT : Tag} {kind : RefKind}
    {mask : List Bool} {i : Nat} {v v' w : BorrowStack}
    (h_wf : TagRenameWF ρt)
    (h_pf : ListRel (TagListSim ρt) pfS pfT)
    (h_t : ρt tagS = some tagT)
    (h_ts : (tagS == wildcardTag) = false)
    (h_new : ρt newS = some newT)
    (h_v : StackSim ρt v v')
    (h_ok : refCellContent pfS exS a tagS kind newS mask i v = .ok w) :
    ∃ w', refCellContent pfT exT a' tagT kind newT mask i v' = .ok w' ∧
      StackSim ρt w w' := by
  -- The access-free placements, in every variant that uses one.
  have h_ins : ∀ {u u' x : BorrowStack}, StackSim ρt u u' →
      insertAboveContent exS a tagS (.RawPtr true newS) u = .ok x →
      ∃ x', insertAboveContent exT a' tagT (.RawPtr true newT) u' = .ok x' ∧
        StackSim ρt x x' := by
    intro u u' x h_u h
    exact insertAboveContent_transport (itS := Item.RawPtr true newS)
      (itT := Item.RawPtr true newT) h_wf h_t h_ts ⟨rfl, h_new⟩ h_u h
  cases kind with
  | Mut =>
      simp only [refCellContent] at h_ok ⊢
      cases h_c : writeCellContent pfS exS a tagS v with
      | error e => rw [h_c] at h_ok; simp at h_ok
      | ok u =>
          rw [h_c] at h_ok
          simp only [Except.ok.injEq] at h_ok
          subst h_ok
          obtain ⟨u', h_u', h_us⟩ :=
            writeCellContent_transport h_wf h_pf h_t h_ts h_v h_c
          rw [h_u']
          exact ⟨_, rfl, ⟨h_new, h_us⟩⟩
  | Shared =>
      simp only [refCellContent] at h_ok ⊢
      by_cases h_m : mask.getD i false = true
      · simp only [if_pos h_m] at h_ok ⊢
        exact h_ins h_v h_ok
      · simp only [if_neg h_m] at h_ok ⊢
        cases h_c : readCellContent pfS exS a tagS v with
        | error e => rw [h_c] at h_ok; simp at h_ok
        | ok u =>
            rw [h_c] at h_ok
            simp only [Except.ok.injEq] at h_ok
            subst h_ok
            obtain ⟨u', h_u', h_us⟩ :=
              readCellContent_transport h_wf h_pf h_t h_ts h_v h_c
            rw [h_u']
            exact ⟨_, rfl, ⟨h_new, h_us⟩⟩
  | Raw m =>
      cases m with
      | true =>
          simp only [refCellContent] at h_ok ⊢
          exact h_ins h_v h_ok
      | false =>
          simp only [refCellContent] at h_ok ⊢
          by_cases h_m : mask.getD i false = true
          · simp only [if_pos h_m] at h_ok ⊢
            exact h_ins h_v h_ok
          · simp only [if_neg h_m] at h_ok ⊢
            cases h_c : readCellContent pfS exS a tagS v with
            | error e => rw [h_c] at h_ok; simp at h_ok
            | ok u =>
                rw [h_c] at h_ok
                simp only [Except.ok.injEq] at h_ok
                subst h_ok
                obtain ⟨u', h_u', h_us⟩ :=
                  readCellContent_transport h_wf h_pf h_t h_ts h_v h_c
                rw [h_u']
                exact ⟨_, rfl, ⟨⟨rfl, h_new⟩, h_us⟩⟩
  | TwoPhase =>
      simp only [refCellContent] at h_ok ⊢
      cases h_c : readCellContent pfS exS a tagS v with
      | error e => rw [h_c] at h_ok; simp at h_ok
      | ok u =>
          rw [h_c] at h_ok
          obtain ⟨u', h_u', h_us⟩ :=
            readCellContent_transport h_wf h_pf h_t h_ts h_v h_c
          rw [h_u']
          exact h_ins h_us h_ok

/-! ## `SB`/`setChain`-level transports -/

theorem SB.find?_transport {ρt : TagRenameMap}
    {x y : SB} (h : StackMapSim ρt x y)
    {a : Word} {s : BorrowStack} (hf : SB.find? x a = some s) :
    ∃ s', SB.find? y a = some s' ∧ StackSim ρt s s' :=
  h.find?_some hf

theorem SB.set_respects {ρt : TagRenameMap} {x y : SB}
    (h : StackMapSim ρt x y)
    {a : Word} {v v' : BorrowStack} (h_v : StackSim ρt v v') :
    StackMapSim ρt (SB.set x a v) (SB.set y a v') := by
  intro b
  by_cases hb : b = a
  · subst hb
    rw [SB.find?_set_self, SB.find?_set_self]
    exact h_v
  · rw [SB.find?_set_ne _ hb, SB.find?_set_ne _ hb]
    exact h b

theorem setChain_chain_respects {ρt : TagRenameMap}
    {W W' : Nat → BorrowStack} {addr : Word} {i len : Nat}
    {x y : SB}
    (h_xy : StackMapSim ρt x y)
    (h_W : ∀ j, i ≤ j → j < len → StackSim ρt (W j) (W' j)) :
    StackMapSim ρt (setChain x (chain W addr i len))
      (setChain y (chain W' addr i len)) := by
  by_cases h : i < len
  · rw [chain_step h, chain_step h, setChain, setChain]
    exact setChain_chain_respects
      (SB.set_respects h_xy (h_W i (Nat.le_refl i) h))
      (fun j h1 h2 => h_W j (by omega) h2)
  · rw [chain_stop h, chain_stop h]
    exact h_xy
  termination_by len - i

/-! ## `sb_own`'s per-cell op

`ownCell` is the one cell op that SUCCEEDS on a missing stack — it is what
creates the cell. That is why `sb_own` cannot go through
`foldCells_ok_inv` (whose `C` never sees the `none` case) and instead
reaches the indexed fold's `Option`-shaped characterizations via
`foldCells_ok_iff_foldCellsIdx_ok`. -/

/-- The stack-level content of an allocation at one cell: a fresh or empty
    cell becomes the singleton root stack; anything else is UB. -/
def ownCellStep (a : Word) (tag : Tag) :
    Option BorrowStack → Except String BorrowStack
  | none => .ok [Item.Own tag]
  | some [] => .ok [Item.Own tag]
  | some (_ :: _) => .error s!"sb-own: borrow stack at {a} is not empty"

theorem ownCell_content_form (t : Tag) (ap : AccessPerms) (a : Word) :
    ownCell ap a t =
      match ownCellStep a t (SB.find? ap.StackMap a) with
      | .error e => .error e
      | .ok v => .ok { ap with StackMap := SB.set ap.StackMap a v } := by
  cases h_find : SB.find? ap.StackMap a with
  | none => simp only [ownCell, ownCellStep, h_find]
  | some stack =>
      cases stack with
      | nil => simp only [ownCell, ownCellStep, h_find]
      | cons k rest => simp only [ownCell, ownCellStep, h_find]

/-- Absence of a cell transports too — the stack maps are related
    positionally, so they have the same keys in the same order. -/
theorem SB.find?_none_transport {ρt : TagRenameMap}
    {x y : SB} (h : StackMapSim ρt x y)
    {a : Word} (hf : SB.find? x a = none) : SB.find? y a = none :=
  h.find?_none hf

/-- Transport for one cell of an allocation. Both machines end with the
    singleton root stack carrying their own fresh tag; the source's success
    forces the cell to be absent-or-empty, and that property transports. -/
theorem ownCellStep_transport {ρt : TagRenameMap} {a a' : Word}
    {newS newT : Tag} {x y : SB} {b : Word} {w : BorrowStack}
    (h_xy : StackMapSim ρt x y)
    (h_new : ρt newS = some newT)
    (h_ok : ownCellStep a newS (SB.find? x b) = .ok w) :
    ownCellStep a' newT (SB.find? y b) = .ok [Item.Own newT] ∧
      StackSim ρt w [Item.Own newT] := by
  cases h_find : SB.find? x b with
  | none =>
      rw [h_find] at h_ok
      rw [SB.find?_none_transport h_xy h_find]
      simp only [ownCellStep, Except.ok.injEq] at h_ok ⊢
      subst h_ok
      exact ⟨trivial, h_new, trivial⟩
  | some s =>
      rw [h_find] at h_ok
      cases s with
      | cons k rest => simp only [ownCellStep] at h_ok; simp at h_ok
      | nil =>
          obtain ⟨s', h_find', h_ss⟩ := SB.find?_transport h_xy h_find
          cases s' with
          | cons k' rest' => simp [StackSim, ListRel] at h_ss
          | nil =>
              rw [h_find']
              simp only [ownCellStep, Except.ok.injEq] at h_ok ⊢
              subst h_ok
              exact ⟨trivial, h_new, trivial⟩

/-! ## Counter framing: the non-minting ops leave `NextTag` alone

`TagRenameBounded` is stated against the two machines' `NextTag`s, so every
step that carries it has to know how those counters moved. For the three
access ops the answer is "not at all" — they only rewrite stacks — which is
what makes the bound free to re-establish across a write, a read or a die. -/

theorem sb_write_NextTag {ap ap' : AccessPerms} {addr : Word} {len : Nat}
    {tag : Tag} (h : sb_write ap addr len tag = .ok ap') :
    ap'.NextTag = ap.NextTag := by
  obtain ⟨V, W, -, h_ap'⟩ :=
    foldCells_ok_inv
      (C := fun a stack => writeCellContent ap.protFrames ap.exposed a tag stack)
      (msgNone := fun a => s!"sb-write: no borrow stack at address {a}")
      (P := ap.protFrames) (E := ap.exposed) (N := ap.NextTag)
      (fun ap a h_pf h_ex _ => writeCell_content_form tag ap a h_pf h_ex)
      len 0 ap ap' rfl rfl rfl h
  rw [h_ap']


theorem sb_read_NextTag {ap ap' : AccessPerms} {addr : Word} {len : Nat}
    {tag : Tag} (h : sb_read ap addr len tag = .ok ap') :
    ap'.NextTag = ap.NextTag := by
  obtain ⟨V, W, -, h_ap'⟩ :=
    foldCells_ok_inv
      (C := fun a stack => readCellContent ap.protFrames ap.exposed a tag stack)
      (msgNone := fun a => s!"sb-read: no borrow stack at address {a}")
      (P := ap.protFrames) (E := ap.exposed) (N := ap.NextTag)
      (fun ap a h_pf h_ex _ => readCell_content_form tag ap a h_pf h_ex)
      len 0 ap ap' rfl rfl rfl h
  rw [h_ap']

theorem ListRel.mem_right {α β} {R : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, ListRel R as bs →
      ∀ {b : β}, b ∈ bs → ∃ a, a ∈ as ∧ R a b := by
  intro as
  induction as with
  | nil =>
      intro bs h b hb
      cases bs with
      | nil => simp at hb
      | cons x xs => simp [ListRel] at h
  | cons a as ih =>
      intro bs h b hb
      cases bs with
      | nil => simp at hb
      | cons x xs =>
          simp only [ListRel] at h
          rcases List.mem_cons.mp hb with h_eq | h_tail
          · exact ⟨a, List.mem_cons_self, h_eq ▸ h.1⟩
          · obtain ⟨a', h_mem', h_rel'⟩ := ih h.2 h_tail
            exact ⟨a', List.mem_cons_of_mem _ h_mem', h_rel'⟩

/-- A tag appearing in a target protector frame came through ρt. -/
theorem TagListSim.mem_range {ρt : TagRenameMap} :
    ∀ {fs ft : List Tag}, TagListSim ρt fs ft →
      ∀ {t : Tag}, t ∈ ft → ∃ ts, ρt ts = some t := by
  intro fs ft h t h_mem
  obtain ⟨a, -, h_rel⟩ := ListRel.mem_right h h_mem
  exact ⟨a, h_rel⟩

/-- The target's NEXT tag is not protected: every tag in its protector
    frames came through ρt, and `TagRenameBounded` puts ρt's whole range
    strictly below the counter. This is BRIDGE 1's `h_unprot` hypothesis,
    and it is DERIVABLE rather than assumed — the payoff for carrying the
    bound in the invariant. -/
theorem freshTag_not_protected {ρt : TagRenameMap} {src tgt : AccessPerms}
    (h_sim : PermSim ρt src tgt)
    (h_bd : TagRenameBounded ρt src.NextTag tgt.NextTag) :
    isProtectedIn tgt.protFrames tgt.NextTag = false := by
  obtain ⟨-, h_prot, -, -⟩ := h_sim
  simp only [isProtectedIn, List.any_eq_false]
  intro f h_mem_f h_c
  have h_mem_t : tgt.NextTag ∈ f := by simpa using h_c
  obtain ⟨fs, -, h_fsim⟩ := ListRel.mem_right h_prot h_mem_f
  obtain ⟨ts, h_ts⟩ := TagListSim.mem_range h_fsim h_mem_t
  exact absurd (h_bd _ _ h_ts).2 (Nat.lt_irrefl _)

/-- A mutable retag succeeds wherever the corresponding WRITE succeeds:
    `sb_ref … .Mut` is per cell `writeCell` followed by `pushCell`, and a
    push onto a stack the write just produced cannot fail. BRIDGE 1 takes
    the retag's success as a hypothesis; on the target side nothing else
    supplies it, because the SOURCE performs a bare write and there is no
    retag to transport. -/
theorem sb_ref_Mut_ok_of_sb_write_ok {ap ap' : AccessPerms}
    {addr : Word} {len : Nat} {tag : Tag}
    (h : sb_write ap addr len tag = .ok ap') :
    ∃ ap'' , sb_ref ap addr len tag .Mut false [] = .ok (ap'', ap.NextTag) := by
  have h0 : foldCells (fun ap a => writeCell ap a tag) ap (addr + 0) len = .ok ap' := h
  obtain ⟨V, W, h_cells, -⟩ :=
    foldCells_ok_inv
      (C := fun a stack => writeCellContent ap.protFrames ap.exposed a tag stack)
      (msgNone := fun a => s!"sb-write: no borrow stack at address {a}")
      (P := ap.protFrames) (E := ap.exposed) (N := ap.NextTag)
      (fun ap a h_pf h_ex _ => writeCell_content_form tag ap a h_pf h_ex)
      len 0 ap ap' rfl rfl rfl h0
  have h_fold := foldCellsIdx_ok_of_cells
    (op := refCellOp tag .Mut ap.NextTag [])
    (C := fun j v? => refCellStep ap.protFrames ap.exposed (addr + j) tag
                        .Mut ap.NextTag [] j v?)
    (P := ap.protFrames) (E := ap.exposed) (N := ap.NextTag + 1)
    (refCellOp_content_form (addr := addr) tag .Mut ap.NextTag [])
    (i := 0) (len := len)
    { ap with NextTag := ap.NextTag + 1 }
    (fun j => Item.MutRef ap.NextTag :: W j)
    rfl rfl rfl
    (fun j _ h2 => by
      have hc := h_cells j (Nat.zero_le j) (by omega)
      show refCellStep ap.protFrames ap.exposed (addr + j) tag .Mut ap.NextTag [] j
        (SB.find? ap.StackMap (addr + j)) = _
      rw [hc.1]
      simp only [refCellStep, refCellContent, hc.2])
  refine ⟨{ StackMap := setChain ap.StackMap
              (chain (fun j => Item.MutRef ap.NextTag :: W j) addr 0 len),
            NextTag := ap.NextTag + 1,
            protFrames := ap.protFrames,
            exposed := ap.exposed }, ?_⟩
  simp only [sb_ref, freshTag, bind, Except.bind, pure, Except.pure, h_fold,
    Bool.false_eq_true, if_false, Except.ok.injEq, Prod.mk.injEq, and_true]

/-- A shared retag (empty mask) succeeds wherever the corresponding READ
    succeeds — the Shared sibling of `sb_ref_Mut_ok_of_sb_write_ok`, and
    BRIDGE 1S's success supplier: the source's pointer-cell read is
    performed by `resolvePlaceAcc`, and this converts its success into the
    target's retag succeeding. -/
theorem sb_ref_Shared_ok_of_sb_read_ok {ap ap' : AccessPerms}
    {addr : Word} {len : Nat} {tag : Tag}
    (h : sb_read ap addr len tag = .ok ap') :
    ∃ ap'' , sb_ref ap addr len tag .Shared false [] = .ok (ap'', ap.NextTag) := by
  have h0 : foldCells (fun ap a => readCell ap a tag) ap (addr + 0) len = .ok ap' := h
  obtain ⟨V, W, h_cells, -⟩ :=
    foldCells_ok_inv
      (C := fun a stack => readCellContent ap.protFrames ap.exposed a tag stack)
      (msgNone := fun a => s!"sb-read: no borrow stack at address {a}")
      (P := ap.protFrames) (E := ap.exposed) (N := ap.NextTag)
      (fun ap a h_pf h_ex _ => readCell_content_form tag ap a h_pf h_ex)
      len 0 ap ap' rfl rfl rfl h0
  have h_fold := foldCellsIdx_ok_of_cells
    (op := refCellOp tag .Shared ap.NextTag [])
    (C := fun j v? => refCellStep ap.protFrames ap.exposed (addr + j) tag
                        .Shared ap.NextTag [] j v?)
    (P := ap.protFrames) (E := ap.exposed) (N := ap.NextTag + 1)
    (refCellOp_content_form (addr := addr) tag .Shared ap.NextTag [])
    (i := 0) (len := len)
    { ap with NextTag := ap.NextTag + 1 }
    (fun j => Item.Ref ap.NextTag :: W j)
    rfl rfl rfl
    (fun j _ h2 => by
      have hc := h_cells j (Nat.zero_le j) (by omega)
      show refCellStep ap.protFrames ap.exposed (addr + j) tag .Shared ap.NextTag [] j
        (SB.find? ap.StackMap (addr + j)) = _
      rw [hc.1]
      simp only [refCellStep, refCellContent, hc.2, List.getD_nil,
        Bool.false_eq_true, if_false])
  refine ⟨{ StackMap := setChain ap.StackMap
              (chain (fun j => Item.Ref ap.NextTag :: W j) addr 0 len),
            NextTag := ap.NextTag + 1,
            protFrames := ap.protFrames,
            exposed := ap.exposed }, ?_⟩
  simp only [sb_ref, freshTag, bind, Except.bind, pure, Except.pure, h_fold,
    Bool.false_eq_true, if_false, Except.ok.injEq, Prod.mk.injEq, and_true]

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

theorem sb_ref_respects_PermSim
    {ρt : TagRenameMap} {src tgt src' : AccessPerms}
    {addr : Word} {len : Nat} {tagS tagT newTagS : Tag}
    {kind : RefKind} {prot : Bool} {mask : List Bool}
    (h_sim : PermSim ρt src tgt)
    (h_wf : TagRenameWF ρt)
    (h_bd : TagRenameBounded ρt src.NextTag tgt.NextTag)
    (h_tag : ρt tagS = some tagT)
    (h_ts : (tagS == wildcardTag) = false)
    (h_src : sb_ref src addr len tagS kind prot mask = .ok (src', newTagS)) :
    ∃ tgt',
      sb_ref tgt addr len tagT kind prot mask = .ok (tgt', tgt.NextTag) ∧
      newTagS = src.NextTag ∧
      TagRenameIncr ρt (ρt.extend src.NextTag tgt.NextTag) ∧
      TagRenameWF (ρt.extend src.NextTag tgt.NextTag) ∧
      TagRenameBounded (ρt.extend src.NextTag tgt.NextTag) src'.NextTag tgt'.NextTag ∧
      PermSim (ρt.extend src.NextTag tgt.NextTag) src' tgt' := by
  have h_incr : TagRenameIncr ρt (ρt.extend src.NextTag tgt.NextTag) :=
    TagRenameIncr.extend h_bd (Nat.le_refl _)
  have h_wf' : TagRenameWF (ρt.extend src.NextTag tgt.NextTag) :=
    TagRenameWF.extend h_wf h_bd (Nat.le_refl _) (Nat.le_refl _)
  have h_tag' : (ρt.extend src.NextTag tgt.NextTag) tagS = some tagT :=
    h_incr _ _ h_tag
  have h_newpair : (ρt.extend src.NextTag tgt.NextTag) src.NextTag
      = some tgt.NextTag := TagRenameMap.extend_self ρt src.NextTag tgt.NextTag
  obtain ⟨h_stacks, h_prot, h_exp, h_next⟩ := PermSim.rename_mono h_incr h_sim
  simp only [sb_ref, freshTag] at h_src
  cases h_go : foldCellsIdx (refCellOp tagS kind src.NextTag mask)
      { src with NextTag := src.NextTag + 1 } addr 0 len with
  | error e =>
      rw [h_go] at h_src
      simp [bind, Except.bind] at h_src
  | ok apR =>
      rw [h_go] at h_src
      simp only [bind, Except.bind, pure, Except.pure] at h_src
      obtain ⟨W, h_cells, h_apR⟩ :=
        foldCellsIdx_ok_inv
          (op := refCellOp tagS kind src.NextTag mask)
          (C := fun j v? => refCellStep src.protFrames src.exposed (addr + j) tagS
                              kind src.NextTag mask j v?)
          (P := src.protFrames) (E := src.exposed) (N := src.NextTag + 1)
          (refCellOp_content_form (addr := addr) tagS kind src.NextTag mask)
          { src with NextTag := src.NextTag + 1 } apR rfl rfl rfl h_go
      rw [show ({ src with NextTag := src.NextTag + 1 } : AccessPerms).StackMap
            = src.StackMap from rfl] at h_cells
      have h_apR_pf : apR.protFrames = src.protFrames := by rw [h_apR]
      have h_apR_ex : apR.exposed = src.exposed := by rw [h_apR]
      have h_apR_nt : apR.NextTag = src.NextTag + 1 := by rw [h_apR]
      have h_apR_sm : apR.StackMap = setChain src.StackMap (chain W addr 0 len) := by
        rw [h_apR]
      -- The matching target cell results.
      have h_pkg : ∀ j, ∃ wj', j < len →
          refCellStep tgt.protFrames tgt.exposed (addr + j) tagT kind tgt.NextTag mask j
              (SB.find? tgt.StackMap (addr + j)) = .ok wj' ∧
            StackSim (ρt.extend src.NextTag tgt.NextTag) (W j) wj' := by
        intro j
        by_cases hj : j < len
        · obtain ⟨vj, h_find, h_content⟩ :=
            refCellStep_ok_inv (h_cells j (Nat.zero_le j) hj)
          obtain ⟨vj', h_find', h_vs⟩ := SB.find?_transport h_stacks h_find
          obtain ⟨wj', h_wj', h_ws⟩ :=
            refCellContent_transport h_wf' h_prot h_tag' h_ts h_newpair h_vs h_content
          exact ⟨wj', fun _ => ⟨by rw [h_find']; exact h_wj', h_ws⟩⟩
        · exact ⟨[], fun h => absurd h hj⟩
      -- Name the target cell results as an opaque family: keeping `h_pkg`
      -- out of the goal is what lets `tgt.protFrames` be rewritten later.
      obtain ⟨W', h_W'⟩ : ∃ W' : Nat → BorrowStack, ∀ j, j < len →
          refCellStep tgt.protFrames tgt.exposed (addr + j) tagT kind tgt.NextTag mask j
              (SB.find? tgt.StackMap (addr + j)) = .ok (W' j) ∧
            StackSim (ρt.extend src.NextTag tgt.NextTag) (W j) (W' j) :=
        ⟨fun j => (h_pkg j).choose, fun j hj => (h_pkg j).choose_spec hj⟩
      clear h_pkg
      have h_goT :=
        foldCellsIdx_ok_of_cells
          (op := refCellOp tagT kind tgt.NextTag mask)
          (C := fun j v? => refCellStep tgt.protFrames tgt.exposed (addr + j) tagT
                              kind tgt.NextTag mask j v?)
          (P := tgt.protFrames) (E := tgt.exposed) (N := tgt.NextTag + 1)
          (refCellOp_content_form (addr := addr) tagT kind tgt.NextTag mask)
          (i := 0) (len := len)
          { tgt with NextTag := tgt.NextTag + 1 } W'
          rfl rfl rfl
          (fun j _ h2 => (h_W' j h2).1)
      -- Common components of the result relation.
      have h_stacks_res : StackMapSim (ρt.extend src.NextTag tgt.NextTag)
          (setChain src.StackMap (chain W addr 0 len))
          (setChain tgt.StackMap (chain W' addr 0 len)) :=
        setChain_chain_respects h_stacks (fun j _ h2 => (h_W' j h2).2)
      have h_bd_res : TagRenameBounded (ρt.extend src.NextTag tgt.NextTag)
          (src.NextTag + 1) (tgt.NextTag + 1) :=
        TagRenameBounded.extend h_bd (Nat.le_succ _) (Nat.le_succ _)
          (Nat.lt_succ_self _) (Nat.lt_succ_self _)
      by_cases h_p : prot = true
      · -- Protected retag: the fresh tag joins the innermost frame, which
        -- exists on the target exactly when it exists on the source.
        simp only [if_pos h_p, h_apR_pf] at h_src
        cases h_pfS : src.protFrames with
        | nil =>
            rw [h_pfS] at h_src
            simp at h_src
        | cons frameS restS =>
            rw [h_pfS] at h_src
            simp only [Except.ok.injEq, Prod.mk.injEq] at h_src
            obtain ⟨h_src'_eq, h_newTag_eq⟩ := h_src
            rw [h_pfS] at h_prot
            cases h_pfT : tgt.protFrames with
            | nil => rw [h_pfT] at h_prot; simp [ListRel] at h_prot
            | cons frameT restT =>
                rw [h_pfT] at h_prot
                simp only [ListRel] at h_prot
                refine ⟨{ StackMap := setChain tgt.StackMap (chain W' addr 0 len),
                          NextTag := tgt.NextTag + 1,
                          protFrames := (tgt.NextTag :: frameT) :: restT,
                          exposed := tgt.exposed },
                        ?_, h_newTag_eq.symm, h_incr, h_wf', ?_, ?_⟩
                · simp only [sb_ref, freshTag, h_goT, bind, Except.bind, pure,
                    Except.pure, if_pos h_p]
                  rw [h_pfT]
                · rw [← h_src'_eq]
                  simpa [h_apR_nt] using h_bd_res
                · rw [← h_src'_eq]
                  refine ⟨?_, ?_, ?_, ?_⟩
                  · simpa [h_apR_sm] using h_stacks_res
                  · exact ⟨⟨h_newpair, h_prot.1⟩, h_prot.2⟩
                  · simpa [h_apR_ex] using h_exp
                  · simpa [h_apR_nt] using Nat.succ_le_succ h_next
      · -- Unprotected retag: the fold result is the whole answer.
        simp only [if_neg h_p] at h_src
        simp only [Except.ok.injEq, Prod.mk.injEq] at h_src
        obtain ⟨h_src'_eq, h_newTag_eq⟩ := h_src
        refine ⟨{ StackMap := setChain tgt.StackMap (chain W' addr 0 len),
                  NextTag := tgt.NextTag + 1,
                  protFrames := tgt.protFrames,
                  exposed := tgt.exposed },
                ?_, h_newTag_eq.symm, h_incr, h_wf', ?_, ?_⟩
        · simp only [sb_ref, freshTag, h_goT, bind, Except.bind, pure, Except.pure,
            if_neg h_p]
        · rw [← h_src'_eq]
          simpa [h_apR_nt] using h_bd_res
        · rw [← h_src'_eq]
          refine ⟨?_, ?_, ?_, ?_⟩
          · simpa [h_apR_sm] using h_stacks_res
          · simpa [h_apR_pf] using h_prot
          · simpa [h_apR_ex] using h_exp
          · simpa [h_apR_nt] using Nat.succ_le_succ h_next

/-- BRIDGE 3 family, `sb_own` member — the second and last minting op.

    Structurally the easy sibling of `sb_ref`: one fresh tag, one cell op
    with no kind analysis, no freeze mask and no protector tail. It reuses
    the same ρt-extension algebra, and its only real difference is that
    `ownCell` succeeds on a MISSING cell (it creates one), which is why the
    fold is characterized through `foldCells_ok_iff_foldCellsIdx_ok` rather
    than `foldCells_ok_inv`. -/
theorem sb_own_respects_PermSim
    {ρt : TagRenameMap} {src tgt src' : AccessPerms}
    {addr : Word} {len : Nat} {newTagS : Tag}
    (h_sim : PermSim ρt src tgt)
    (h_wf : TagRenameWF ρt)
    (h_bd : TagRenameBounded ρt src.NextTag tgt.NextTag)
    (h_src : sb_own src addr len = .ok (src', newTagS)) :
    ∃ tgt',
      sb_own tgt addr len = .ok (tgt', tgt.NextTag) ∧
      newTagS = src.NextTag ∧
      TagRenameIncr ρt (ρt.extend src.NextTag tgt.NextTag) ∧
      TagRenameWF (ρt.extend src.NextTag tgt.NextTag) ∧
      TagRenameBounded (ρt.extend src.NextTag tgt.NextTag) src'.NextTag tgt'.NextTag ∧
      PermSim (ρt.extend src.NextTag tgt.NextTag) src' tgt' := by
  have h_incr : TagRenameIncr ρt (ρt.extend src.NextTag tgt.NextTag) :=
    TagRenameIncr.extend h_bd (Nat.le_refl _)
  have h_wf' : TagRenameWF (ρt.extend src.NextTag tgt.NextTag) :=
    TagRenameWF.extend h_wf h_bd (Nat.le_refl _) (Nat.le_refl _)
  have h_newpair : (ρt.extend src.NextTag tgt.NextTag) src.NextTag
      = some tgt.NextTag := TagRenameMap.extend_self ρt src.NextTag tgt.NextTag
  obtain ⟨h_stacks, h_prot, h_exp, h_next⟩ := PermSim.rename_mono h_incr h_sim
  simp only [sb_own, freshTag] at h_src
  cases h_go : foldCells (fun ap a => ownCell ap a src.NextTag)
      { src with NextTag := src.NextTag + 1 } addr len with
  | error e =>
      rw [h_go] at h_src
      simp [bind, Except.bind] at h_src
  | ok apR =>
      rw [h_go] at h_src
      simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq,
        Prod.mk.injEq] at h_src
      obtain ⟨h_src'_eq, h_newTag_eq⟩ := h_src
      -- move to the indexed fold, whose characterizations see the `none` case
      have h_goI : foldCellsIdx (fun ap a _ => ownCell ap a src.NextTag)
          { src with NextTag := src.NextTag + 1 } addr 0 (0 + len) = .ok apR :=
        (foldCells_ok_iff_foldCellsIdx_ok (fun ap a => ownCell ap a src.NextTag) addr
          len 0 { src with NextTag := src.NextTag + 1 } apR).mp h_go
      rw [show (0 : Nat) + len = len from Nat.zero_add len] at h_goI
      obtain ⟨W, h_cells, h_apR⟩ :=
        foldCellsIdx_ok_inv
          (op := fun ap a _ => ownCell ap a src.NextTag)
          (C := fun j v? => ownCellStep (addr + j) src.NextTag v?)
          (P := src.protFrames) (E := src.exposed) (N := src.NextTag + 1)
          (fun ap _ _ _ _ => ownCell_content_form src.NextTag ap _)
          { src with NextTag := src.NextTag + 1 } apR rfl rfl rfl h_goI
      rw [show ({ src with NextTag := src.NextTag + 1 } : AccessPerms).StackMap
            = src.StackMap from rfl] at h_cells
      have h_apR_pf : apR.protFrames = src.protFrames := by rw [h_apR]
      have h_apR_ex : apR.exposed = src.exposed := by rw [h_apR]
      have h_apR_nt : apR.NextTag = src.NextTag + 1 := by rw [h_apR]
      have h_apR_sm : apR.StackMap = setChain src.StackMap (chain W addr 0 len) := by
        rw [h_apR]
      -- every cell ends as the singleton root stack, on both machines
      have h_pkg : ∀ j, j < len →
          ownCellStep (addr + j) tgt.NextTag (SB.find? tgt.StackMap (addr + j))
              = .ok [Item.Own tgt.NextTag] ∧
            StackSim (ρt.extend src.NextTag tgt.NextTag) (W j)
              [Item.Own tgt.NextTag] :=
        fun j hj =>
          ownCellStep_transport h_stacks h_newpair (h_cells j (Nat.zero_le j) hj)
      have h_goTI :=
        foldCellsIdx_ok_of_cells
          (op := fun ap a _ => ownCell ap a tgt.NextTag)
          (C := fun j v? => ownCellStep (addr + j) tgt.NextTag v?)
          (P := tgt.protFrames) (E := tgt.exposed) (N := tgt.NextTag + 1)
          (fun ap _ _ _ _ => ownCell_content_form tgt.NextTag ap _)
          (i := 0) (len := len)
          { tgt with NextTag := tgt.NextTag + 1 }
          (fun _ => [Item.Own tgt.NextTag])
          rfl rfl rfl
          (fun j _ h2 => (h_pkg j h2).1)
      have h_goT : foldCells (fun ap a => ownCell ap a tgt.NextTag)
          { tgt with NextTag := tgt.NextTag + 1 } addr len
          = .ok { { tgt with NextTag := tgt.NextTag + 1 } with
                  StackMap := setChain tgt.StackMap
                    (chain (fun _ => [Item.Own tgt.NextTag]) addr 0 len) } := by
        refine (foldCells_ok_iff_foldCellsIdx_ok
          (fun ap a => ownCell ap a tgt.NextTag) addr len 0
          { tgt with NextTag := tgt.NextTag + 1 } _).mpr ?_
        rw [show (0 : Nat) + len = len from Nat.zero_add len]
        exact h_goTI
      refine ⟨{ StackMap := setChain tgt.StackMap
                  (chain (fun _ => [Item.Own tgt.NextTag]) addr 0 len),
                NextTag := tgt.NextTag + 1,
                protFrames := tgt.protFrames,
                exposed := tgt.exposed },
              ?_, h_newTag_eq.symm, h_incr, h_wf', ?_, ?_⟩
      · simp only [sb_own, freshTag, h_goT, bind, Except.bind, pure, Except.pure]
      · rw [← h_src'_eq]
        simpa [h_apR_nt] using
          (TagRenameBounded.extend h_bd (Nat.le_succ _) (Nat.le_succ _)
            (Nat.lt_succ_self _) (Nat.lt_succ_self _))
      · rw [← h_src'_eq]
        refine ⟨?_, ?_, ?_, ?_⟩
        · simpa [h_apR_sm] using
            setChain_chain_respects h_stacks (fun j _ h2 => (h_pkg j h2).2)
        · simpa [h_apR_pf] using h_prot
        · simpa [h_apR_ex] using h_exp
        · simpa [h_apR_nt] using Nat.succ_le_succ h_next


/-- BRIDGE 1S, packaged. Given a source read already transported to the
    target, turn it into the *whole* borrow-read-die triple: take a
    `Shared` borrow at the fresh tag, read through it, retire it — and
    the result is still `PermSim` to the source's post-read state.

    Every copy leaf that reads through a lowered place ran this same
    eleven-line ritual: `freshTag_not_protected`, the `wildcardTag`
    bound, `sb_ref_Shared_ok_of_sb_read_ok`, `sb_ref_read_die_cancels`,
    then a hand-rebuilt `PermSim` stitching `h_sm`/`h_pfq`/`h_exq`/
    `h_ntle` back into the four fields. None of it varies.

    It takes the transported read rather than deriving it, because some
    leaves need the intermediate `PermSim` earlier — before the write
    transport — and cannot have it produced here. -/
theorem bridge1S_of_read {ρt : TagRenameMap} {src tgt src' tgtAcc : AccessPerms}
    {addr : Word} {len : Nat} {tagT : Tag}
    (h_sim : PermSim ρt src tgt)
    (h_wf : TagRenameWF ρt)
    (h_bd : TagRenameBounded ρt src.NextTag tgt.NextTag)
    (h_read_tgt : sb_read tgt addr len tagT = .ok tgtAcc)
    (h_psim2 : PermSim ρt src' tgtAcc) :
    ∃ q1 q2 q3,
      sb_ref tgt addr len tagT .Shared false [] = .ok (q1, tgt.NextTag) ∧
      sb_read q1 addr len tgt.NextTag = .ok q2 ∧
      sb_die q2 addr len tgt.NextTag = .ok q3 ∧
      PermSim ρt src' q3 ∧
      tgtAcc.NextTag ≤ q3.NextTag := by
  obtain ⟨q1, h_ref_tgt⟩ := sb_ref_Shared_ok_of_sb_read_ok h_read_tgt
  have h_unprot := freshTag_not_protected h_sim h_bd
  have h0 : wildcardTag < tgt.NextTag := (h_bd _ _ h_wf.2).2
  have h_ntw : (tgt.NextTag == wildcardTag) = false := by grind
  obtain ⟨q2, q3, qAcc, h_rd1, h_die1, h_rd2, h_sm, h_exq, h_pfq, h_ntle⟩ :=
    sb_ref_read_die_cancels h_ntw h_unprot h_ref_tgt
  have h_qAcc : qAcc = tgtAcc := by grind
  subst h_qAcc
  refine ⟨q1, q2, q3, h_ref_tgt, h_rd1, h_die1, ?_, h_ntle⟩
  obtain ⟨hs, hp, he, hn⟩ := h_psim2
  exact ⟨by rw [h_sm]; exact hs, by rw [h_pfq]; exact hp,
         by rw [h_exq]; exact he, Nat.le_trans hn h_ntle⟩

end obseq3.proof
