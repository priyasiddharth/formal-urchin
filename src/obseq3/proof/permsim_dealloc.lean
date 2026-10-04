import obseq3.proof.permsim_transport

/-!
# `PermSim` transport for deallocation and protector frames

A deallocation through related tags succeeds on both sides and keeps the
stacks related (`sb_dealloc_respects_PermSim`); pushing and popping a
protector frame acts alike on both sides (`PermSim.pushFrame`/`popFrame`).
-/

namespace obseq3.proof

open obseq3

/-- The per-cell op of `sb_dealloc`, named so the fold's steps can be
    rewritten by name. -/
def deallocCellOp (tag : Tag) (ap : AccessPerms) (a : Word) : Except String AccessPerms :=
  match ap.StackMap.find? a with
  | none => .error s!"sb-dealloc: no borrow stack at address {a}"
  | some stack =>
    match splitStack stack tag with
    | none => .error s!"deallocation through tag {tag}: that tag does not exist in the borrow stack at {a}"
    | some (above, item, below) =>
      if !item.grantsWrite then
        .error s!"sb-dealloc: tag {tag} (a read-only item) does not grant deallocation at {a}"
      else
        match firstProtected ap above,
              (item :: below).find? (fun k => (firstProtected ap [k]).isSome &&
                                              !ap.weakProt.contains k.tag) with
        | some p, _ =>
            .error s!"deallocating while item for tag {p.tag} is protected"
        | none, some p =>
            .error s!"deallocating while item for tag {p.tag} is strongly protected"
        | none, none =>
            .ok { ap with StackMap := ap.StackMap.filter (fun (x, _) => x != a) }

/-- "Protected and not weakly": the items that block a deallocation from
    below the popped part (`sb_dealloc`). -/
abbrev strongProt (pf : List (List Tag)) (wk : List Tag) (k : Item) : Bool :=
  (firstProtectedIn pf [k]).isSome && !wk.contains k.tag

theorem firstProtectedIn_singleton_isSome (pf : List (List Tag)) (k : Item) :
    (firstProtectedIn pf [k]).isSome = (!k.isSrw && isProtectedIn pf k.tag) := by
  cases k with
  | RawPtr m t =>
      cases m <;> simp only [firstProtectedIn, List.find?, Item.isSrw, Item.tag] <;>
        cases isProtectedIn pf t <;> rfl
  | Own t | MutRef t | Ref t | Disabled t =>
      simp only [firstProtectedIn, List.find?, Item.isSrw, Item.tag] <;>
        cases isProtectedIn pf t <;> rfl

/-- `strongProt` is the same on ρt-related items of related states. -/
theorem strongProt_eq {ρt : TagRenameMap} (h_wf : TagRenameWF ρt)
    {pfS pfT : List (List Tag)} (h_pf : ListRel (TagListSim ρt) pfS pfT)
    {wkS wkT : List Tag} (h_wk : TagListSim ρt wkS wkT)
    {k k' : Item} (hk : ItemSim ρt k k') :
    strongProt pfT wkT k' = strongProt pfS wkS k := by
  have ht := ItemSim.tag_rel hk
  simp only [strongProt]
  rw [firstProtectedIn_singleton_isSome, firstProtectedIn_singleton_isSome,
    ItemSim.isSrw_eq hk, isProtectedIn_transport h_wf ht h_pf,
    TagListSim.contains_eq h_wf ht h_wk]

theorem sb_dealloc_eq (ap : AccessPerms) (addr : Word) (lenB : Nat) (tag : Tag) :
    sb_dealloc ap addr lenB tag = foldCells (deallocCellOp tag) ap addr lenB := rfl

/-- One cell of `sb_dealloc`, inverted: the stack is there, the tag
    splits it at a write-granting item, nothing above it is protected,
    nothing at or below it is STRONGLY protected, and the cell is
    removed. -/
theorem deallocCellOp_ok_inv {ap ap' : AccessPerms} {a : Word} {tag : Tag}
    (h : deallocCellOp tag ap a = .ok ap') :
    ∃ stack ab item bl,
      ap.StackMap.find? a = some stack ∧
      splitStack stack tag = some (ab, item, bl) ∧
      item.grantsWrite = true ∧
      firstProtectedIn ap.protFrames ab = none ∧
      (item :: bl).find? (strongProt ap.protFrames ap.weakProt) = none ∧
      ap' = { ap with StackMap := ap.StackMap.filter (fun (x, _) => x != a) } := by
  simp only [deallocCellOp] at h
  split at h
  · simp at h
  rename_i stack h_find
  split at h
  · simp at h
  rename_i ab item bl h_split
  by_cases h_gw : item.grantsWrite = true
  · rw [if_neg (by simp [h_gw])] at h
    split at h
    · simp at h
    · simp at h
    rename_i h_fp h_sp
    cases h
    exact ⟨stack, ab, item, bl, h_find, h_split, h_gw, h_fp, h_sp, rfl⟩
  · rw [if_pos (by simpa using h_gw)] at h
    simp at h

/-- The converse. -/
theorem deallocCellOp_ok_eq (ap : AccessPerms) (a : Word) (tag : Tag)
    {stack ab bl : BorrowStack} {item : Item}
    (h_find : ap.StackMap.find? a = some stack)
    (h_split : splitStack stack tag = some (ab, item, bl))
    (h_gw : item.grantsWrite = true)
    (h_fp : firstProtectedIn ap.protFrames ab = none)
    (h_sp : (item :: bl).find? (strongProt ap.protFrames ap.weakProt) = none) :
    deallocCellOp tag ap a
      = .ok { ap with StackMap := ap.StackMap.filter (fun (x, _) => x != a) } := by
  simp only [deallocCellOp, h_find, h_split, firstProtected, h_fp, h_sp]
  rw [if_neg (by simp [h_gw])]

/-- The cell removed is gone. -/
theorem SB.find?_filter_self (a : Word) :
    ∀ (sb : SB), SB.find? (sb.filter (fun (e : Word × BorrowStack) => e.1 != a)) a = none
  | [] => rfl
  | (k, s) :: rest => by
      by_cases hk : k = a
      · rw [List.filter_cons_of_neg (by simp [hk])]
        exact SB.find?_filter_self a rest
      · rw [List.filter_cons_of_pos (by simp [hk])]
        simp only [SB.find?, show (k == a) = false by simp [hk]]
        exact SB.find?_filter_self a rest

/-- Removing the same cell on both sides keeps the maps related. -/
theorem StackMapSim.filter_cell {x y : SB} (h : StackMapSim ρt x y) (a : Word) :
    StackMapSim ρt (x.filter (fun (e : Word × BorrowStack) => e.1 != a))
      (y.filter (fun (e : Word × BorrowStack) => e.1 != a)) := by
  intro b
  by_cases hb : b = a
  · subst hb
    rw [SB.find?_filter_self, SB.find?_filter_self]
    trivial
  · rw [SB.find?_filter_ne hb, SB.find?_filter_ne hb]
    exact h b

/-- `sb_dealloc` transports along `PermSim`: the source freeing a block
    through a tag means the target frees it through the tag's image, and
    the results are related. Neither counter moves. -/
theorem sb_dealloc_respects_PermSim
    {ρt : TagRenameMap} {tagS tagT : Tag}
    (h_wf : TagRenameWF ρt) (h_tag : ρt tagS = some tagT) :
    ∀ (lenB : Nat) (addr : Word) {src tgt src' : AccessPerms},
      PermSim ρt src tgt →
      sb_dealloc src addr lenB tagS = .ok src' →
      ∃ tgt', sb_dealloc tgt addr lenB tagT = .ok tgt' ∧ PermSim ρt src' tgt' ∧
        src'.NextTag = src.NextTag ∧ tgt'.NextTag = tgt.NextTag := by
  intro lenB
  induction lenB with
  | zero =>
      intro addr src tgt src' h_sim h_src
      rw [sb_dealloc_eq] at h_src
      simp only [foldCells] at h_src
      cases h_src
      exact ⟨tgt, rfl, h_sim, rfl, rfl⟩
  | succ n ih =>
      intro addr src tgt src' h_sim h_src
      obtain ⟨h_stacks, h_prot, h_exp, h_next, h_wk⟩ := h_sim
      rw [sb_dealloc_eq] at h_src ⊢
      simp only [foldCells] at h_src
      split at h_src
      · simp at h_src
      rename_i src1 h_cell
      obtain ⟨stack, ab, item, bl, h_find, h_split, h_gw, h_fp, h_sp, rfl⟩ :=
        deallocCellOp_ok_inv h_cell
      obtain ⟨stack', h_find', h_ss⟩ := SB.find?_transport h_stacks h_find
      obtain ⟨ab', item', bl', h_split', h_ab, h_item, h_bl⟩ :=
        splitStack_some_transport h_wf h_tag h_ss h_split
      have h_gw' : item'.grantsWrite = true := by
        rw [ItemSim.grantsWrite_eq h_item]; exact h_gw
      have h_fp' : firstProtectedIn tgt.protFrames ab' = none :=
        firstProtectedIn_none_transport h_wf h_prot h_ab h_fp
      have h_sp' : (item' :: bl').find? (strongProt tgt.protFrames tgt.weakProt) = none :=
        ListRel.find?_none (fun k k' hk => strongProt_eq h_wf h_prot h_wk hk)
          (show StackSim ρt (item :: bl) (item' :: bl') from ⟨h_item, h_bl⟩) h_sp
      have h_sim1 : PermSim ρt
          { src with StackMap := src.StackMap.filter (fun (x, _) => x != addr) }
          { tgt with StackMap := tgt.StackMap.filter (fun (x, _) => x != addr) } :=
        ⟨StackMapSim.filter_cell h_stacks addr, h_prot, h_exp, h_next, h_wk⟩
      obtain ⟨tgt', h_tgt, h_sim', h_ns, h_nt⟩ := ih (addr + 1) h_sim1 h_src
      refine ⟨tgt', ?_, h_sim', h_ns, h_nt⟩
      simp only [foldCells]
      rw [deallocCellOp_ok_eq tgt addr tagT h_find' h_split' h_gw' h_fp' h_sp']
      rw [sb_dealloc_eq] at h_tgt
      exact h_tgt

/-- Pushing an (empty) frame on both sides keeps the frame lists related:
    `ListRel` of `[]` with `[]` is `True`. Nothing else moves. -/
theorem PermSim.pushFrame {sp tp : AccessPerms} (h : PermSim ρt sp tp) :
    PermSim ρt (MSB.pushFrame sp) (MSB.pushFrame tp) := by
  obtain ⟨h_st, h_pf, h_ex, h_nt, h_wk⟩ := h
  exact ⟨h_st, ⟨trivial, h_pf⟩, h_ex, h_nt, h_wk⟩

/-- Popping succeeds on the target whenever it does on the source — the
    lists are positionally related, so the target's is non-empty too —
    and the tails stay related. `NextTag` is untouched on both sides. -/
theorem PermSim.popFrame {sp sp' tp : AccessPerms} (h : PermSim ρt sp tp)
    (h_src : MSB.popFrame sp = .ok sp') :
    ∃ tp', MSB.popFrame tp = .ok tp' ∧ PermSim ρt sp' tp' ∧
      sp'.NextTag = sp.NextTag ∧ tp'.NextTag = tp.NextTag := by
  obtain ⟨h_st, h_pf, h_ex, h_nt, h_wk⟩ := h
  change sb_pop_frame sp = .ok sp' at h_src
  cases hs : sp.protFrames with
  | nil => simp [sb_pop_frame, hs] at h_src
  | cons f rest =>
    cases ht : tp.protFrames with
    | nil => rw [hs, ht] at h_pf; exact h_pf.elim
    | cons f' rest' =>
      simp only [sb_pop_frame, hs] at h_src
      injection h_src with h_src
      subst h_src
      rw [hs, ht] at h_pf
      refine ⟨{ tp with protFrames := rest' }, ?_, ⟨h_st, h_pf.2, h_ex, h_nt, h_wk⟩, rfl, rfl⟩
      change sb_pop_frame tp = _
      simp [sb_pop_frame, ht]

end obseq3.proof
