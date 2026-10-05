import obseq3.proof.stacksub

/-!
# Die elision, per cell

Each borrow-stack cell operation, run on A's stack and on B's (A's with
died extras interleaved, `StackSub`), succeeds on B when it does on A and
keeps the stacks related. The extras are harmless because:
- their tags differ from every A-tag at the cell (B's tags are distinct),
  so a split at an A-tag finds the same item;
- they are unprotected, so popping them is never UB;
- they are unexposed, so a wildcard never resolves to one;
- an extra is never directly below an SRW A-item, so it never splits an
  SRW run (`srwSplit_sub`).

`CellRel E N sa sb` packages the stack relation with the well-formedness
the transports consume: B's tags are distinct and below the counter `N`,
and A's stack bottoms out in its `Own` root (never empty).
-/

namespace obseq3.proof

open obseq3

/-- The cell relation of die elision. -/
def CellRel (E : Tag → Prop) (N : Tag) (sa sb : BorrowStack) : Prop :=
  (∃ b, StackSub E b sa sb) ∧ (sb.map Item.tag).Nodup ∧ (∀ i ∈ sb, i.tag < N) ∧
    ∃ t, sa.getLast? = some (.Own t)

/-! ## The general facts -/

theorem resolveWildcardIn_sub {E : Tag → Prop} {ex : List Tag}
    (hEx : ∀ t, E t → ex.contains t = false) {b : Bool} {sa sb : BorrowStack}
    (h : StackSub E b sa sb) (nw : Bool) :
    resolveWildcardIn ex sb nw = resolveWildcardIn ex sa nw := by
  unfold resolveWildcardIn
  congr 1
  induction h with
  | nil => rfl
  | same i _ _ ih => simp only [List.find?_cons, ih]
  | extra e he _ ih =>
      have hc := hEx _ he
      rw [List.find?_cons_of_neg (by cases e <;> simp_all [Item.tag]), ih]

theorem firstProtectedIn_none_sub {E : Tag → Prop} {pf : List (List Tag)}
    (hEp : ∀ t, E t → isProtectedIn pf t = false) {l l' : List Item}
    (hm : ∀ k ∈ l', k ∈ l ∨ E k.tag) (h : firstProtectedIn pf l = none) :
    firstProtectedIn pf l' = none := by
  unfold firstProtectedIn at h ⊢
  rw [List.find?_eq_none] at h ⊢
  intro k hk
  rcases hm k hk with hk | he
  · exact h k hk
  · have hp := hEp _ he
    cases k with
    | RawPtr m t => cases m <;> simp_all [Item.tag]
    | _ => simp_all [Item.tag]

/-! ## Write -/

theorem writeCellContentR_ok {pf : List (List Tag)} {addr : Word} {t : Tag}
    {s w : BorrowStack} (h : writeCellContentR pf addr t s = .ok w) :
    ∃ aa it ba, splitStack s t = some (aa, it, ba) ∧ it.grantsWrite = true ∧
      firstProtectedIn pf (if it.isSrw then (srwSplit aa).1 else aa) = none ∧
      w = (if it.isSrw then (srwSplit aa).2 else []) ++ it :: ba := by
  unfold writeCellContentR at h
  split at h
  · cases h
  rename_i aa it ba hsp
  refine ⟨aa, it, ba, hsp, ?_⟩
  split at h
  · cases h
  split at h
  · rename_i hgw
    rw [srwSplit_eq aa]
    cases hsrw : it.isSrw
    · simp only [hsrw, Bool.false_eq_true, if_false] at h ⊢
      split at h
      · cases h
      · rename_i hfp
        exact ⟨hgw, hfp, (Except.ok.inj h).symm⟩
    · simp only [hsrw, if_true] at h ⊢
      split at h
      · cases h
      · rename_i hfp
        exact ⟨hgw, hfp, (Except.ok.inj h).symm⟩
  · cases h

theorem writeCellContentR_of {pf : List (List Tag)} {addr : Word} {t : Tag}
    {s : BorrowStack} {aa : BorrowStack} {it : Item} {ba : BorrowStack}
    (hsp : splitStack s t = some (aa, it, ba)) (hgw : it.grantsWrite = true)
    (hfp : firstProtectedIn pf (if it.isSrw then (srwSplit aa).1 else aa) = none) :
    writeCellContentR pf addr t s = .ok ((if it.isSrw then (srwSplit aa).2 else []) ++ it :: ba) := by
  unfold writeCellContentR
  rw [hsp]
  simp only
  have hnd : ∀ t0, it ≠ .Disabled t0 := by
    intro t0 h; subst h; simp [Item.grantsWrite] at hgw
  split
  · exact absurd rfl (hnd _)
  · rw [if_pos hgw]
    rw [srwSplit_eq aa] at hfp ⊢
    cases hsrw : it.isSrw
    · simp only [hsrw, Bool.false_eq_true, if_false] at hfp ⊢
      rw [hfp]
    · simp only [hsrw, if_true] at hfp ⊢
      rw [hfp]

theorem writeCellContentR_sub {E : Tag → Prop} {pf : List (List Tag)}
    (hEp : ∀ t, E t → isProtectedIn pf t = false)
    {addr : Word} {t : Tag} {b : Bool} {sa sb wa : BorrowStack}
    (hsub : StackSub E b sa sb) (hnd : (sb.map Item.tag).Nodup)
    (hA : writeCellContentR pf addr t sa = .ok wa) :
    ∃ wb, writeCellContentR pf addr t sb = .ok wb ∧ ∃ b', StackSub E b' wa wb := by
  obtain ⟨aa, it, ba, hsp, hgw, hfp, rfl⟩ := writeCellContentR_ok hA
  obtain ⟨ab, bb, hspb, ⟨b1, hab, -⟩, ⟨b2, hbb, hc⟩⟩ := splitStack_sub hsub hnd hsp
  have h_tail : StackSub E false (it :: ba) (it :: bb) := .same it hbb hc
  cases hsrw : it.isSrw
  · -- a non-SRW item: everything above it goes, on both sides
    simp only [hsrw, Bool.false_eq_true, if_false, List.nil_append] at hfp ⊢
    refine ⟨it :: bb, ?_, false, h_tail⟩
    have := writeCellContentR_of (pf := pf) (addr := addr) hspb hgw
      (by simp only [hsrw, Bool.false_eq_true, if_false]
          exact firstProtectedIn_none_sub hEp (fun k hk => hab.mem_right hk) hfp)
    simpa [hsrw] using this
  · -- an SRW item: B keeps A's run and the SRW extras right above it
    simp only [hsrw, if_true] at hfp ⊢
    obtain ⟨Y, hY, hYE, hRb, -⟩ := srwSplit_sub hab
    have hB := writeCellContentR_of (pf := pf) (addr := addr) hspb hgw
      (by simp only [hsrw, if_true]; exact firstProtectedIn_none_sub hEp hRb hfp)
    simp only [hsrw, if_true] at hB
    refine ⟨_, hB, ?_⟩
    rw [hY, List.append_assoc]
    exact StackSub.extras Y hYE (StackSub.prefix_same _ h_tail)

/-! ## Read -/

/-- The item map of a read: Uniques above the granting item are disabled. -/
def disableF (k : Item) : Item := if k.poppedByRead then .Disabled k.tag else k

theorem disableF_tag (k : Item) : (disableF k).tag = k.tag := by
  unfold disableF; split <;> rfl

theorem disableF_srw (k : Item) : (disableF k).isSrw = k.isSrw := by
  unfold disableF; cases k <;> simp [Item.poppedByRead, Item.isSrw]

theorem readCellContentR_ok {pf : List (List Tag)} {addr : Word} {t : Tag}
    {s w : BorrowStack} (h : readCellContentR pf addr t s = .ok w) :
    ∃ aa it ba, splitStack s t = some (aa, it, ba) ∧ (∀ t0, it ≠ .Disabled t0) ∧
      firstProtectedIn pf (aa.filter (·.poppedByRead)) = none ∧
      w = aa.map disableF ++ it :: ba := by
  unfold readCellContentR at h
  cases hsp : splitStack s t with
  | none => simp [hsp] at h
  | some r =>
    obtain ⟨aa, it, ba⟩ := r
    rw [hsp] at h
    refine ⟨aa, it, ba, rfl, ?_⟩
    cases it with
    | Disabled t0 => simp at h
    | _ =>
      simp only at h
      split at h
      · cases h
      · rename_i hfp
        exact ⟨by simp, hfp, by rw [← Except.ok.inj h]; rfl⟩

theorem readCellContentR_of {pf : List (List Tag)} {addr : Word} {t : Tag}
    {s : BorrowStack} {aa : BorrowStack} {it : Item} {ba : BorrowStack}
    (hsp : splitStack s t = some (aa, it, ba)) (hnd : ∀ t0, it ≠ .Disabled t0)
    (hfp : firstProtectedIn pf (aa.filter (·.poppedByRead)) = none) :
    readCellContentR pf addr t s = .ok (aa.map disableF ++ it :: ba) := by
  cases it with
  | Disabled t0 => exact absurd rfl (hnd t0)
  | _ => simp only [readCellContentR, hsp, hfp]; rfl

theorem readCellContentR_sub {E : Tag → Prop} {pf : List (List Tag)}
    (hEp : ∀ t, E t → isProtectedIn pf t = false)
    {addr : Word} {t : Tag} {b : Bool} {sa sb wa : BorrowStack}
    (hsub : StackSub E b sa sb) (hnd : (sb.map Item.tag).Nodup)
    (hA : readCellContentR pf addr t sa = .ok wa) :
    ∃ wb, readCellContentR pf addr t sb = .ok wb ∧ ∃ b', StackSub E b' wa wb := by
  obtain ⟨aa, it, ba, hsp, hnd', hfp, rfl⟩ := readCellContentR_ok hA
  obtain ⟨ab, bb, hspb, ⟨b1, hab, -⟩, ⟨b2, hbb, hc⟩⟩ := splitStack_sub hsub hnd hsp
  have hfpB : firstProtectedIn pf (ab.filter (·.poppedByRead)) = none := by
    refine firstProtectedIn_none_sub hEp (fun k hk => ?_) hfp
    obtain ⟨hk1, hk2⟩ := List.mem_filter.mp hk
    rcases hab.mem_right hk1 with h | h
    · exact Or.inl (List.mem_filter.mpr ⟨h, hk2⟩)
    · exact Or.inr h
  exact ⟨_, readCellContentR_of hspb hnd' hfpB, b1,
    (hab.map disableF (fun i => ⟨disableF_tag i, disableF_srw i⟩)).append (.same it hbb hc)⟩

/-! ## Insert above -/

theorem insertAboveContentR_ok {addr : Word} {t : Tag} {x : Item}
    {s w : BorrowStack} (h : insertAboveContentR addr t x s = .ok w) :
    ∃ aa it ba, splitStack s t = some (aa, it, ba) ∧ (∀ t0, it ≠ .Disabled t0) ∧
      w = aa ++ x :: it :: ba := by
  unfold insertAboveContentR at h
  cases hsp : splitStack s t with
  | none => simp [hsp] at h
  | some r =>
    obtain ⟨aa, it, ba⟩ := r
    rw [hsp] at h
    cases it with
    | Disabled t0 => simp at h
    | _ =>
      simp only [Except.ok.injEq] at h
      exact ⟨aa, _, ba, rfl, by simp, h.symm⟩

theorem insertAboveContentR_of {addr : Word} {t : Tag} {x : Item}
    {s : BorrowStack} {aa : BorrowStack} {it : Item} {ba : BorrowStack}
    (hsp : splitStack s t = some (aa, it, ba)) (hnd : ∀ t0, it ≠ .Disabled t0) :
    insertAboveContentR addr t x s = .ok (aa ++ x :: it :: ba) := by
  cases it with
  | Disabled t0 => exact absurd rfl (hnd t0)
  | _ => simp only [insertAboveContentR, hsp]

theorem insertAboveContentR_sub {E : Tag → Prop}
    {addr : Word} {t : Tag} {x : Item} {b : Bool} {sa sb wa : BorrowStack}
    (hsub : StackSub E b sa sb) (hnd : (sb.map Item.tag).Nodup)
    (hA : insertAboveContentR addr t x sa = .ok wa) :
    ∃ wb, insertAboveContentR addr t x sb = .ok wb ∧ ∃ b', StackSub E b' wa wb ∧
      ∃ ab bb it, sb = ab ++ it :: bb ∧ wb = ab ++ x :: it :: bb := by
  obtain ⟨aa, it, ba, hsp, hnd', rfl⟩ := insertAboveContentR_ok hA
  obtain ⟨ab, bb, hspb, ⟨b1, hab, -⟩, ⟨b2, hbb, hc⟩⟩ := splitStack_sub hsub hnd hsp
  exact ⟨_, insertAboveContentR_of hspb hnd', b1,
    hab.append (.same x (.same it hbb hc) (by intro h; cases h)),
    ab, bb, it, (splitStack_some_eq hspb).1, rfl⟩

/-! ## The cell relation -/

theorem getLast?_append_cons {α} (X : List α) (y : α) (ys : List α) :
    (X ++ y :: ys).getLast? = (y :: ys).getLast? := by
  rw [List.getLast?_append]
  simp [List.getLast?_cons]

theorem CellRel.mono {E E' : Tag → Prop} {N N' : Tag} {sa sb : BorrowStack}
    (h : CellRel E N sa sb) (hE : ∀ x ∈ sb, E x.tag → E' x.tag) (hN : N ≤ N') :
    CellRel E' N' sa sb := by
  obtain ⟨⟨b, hs⟩, hnd, hbd, hl⟩ := h
  exact ⟨⟨b, hs.mono_mem hE⟩, hnd, fun i hi => Nat.lt_of_lt_of_le (hbd i hi) hN, hl⟩

theorem nodup_of_sublist {l l' : BorrowStack} (hs : l.Sublist l')
    (h : (l'.map Item.tag).Nodup) : (l.map Item.tag).Nodup :=
  List.Nodup.sublist (hs.map _) h

/-- Results that keep a sublist of B's stack (reads map it, writes cut
    it): B's tags stay distinct and bounded. -/
theorem cell_wf_sublist {N : Tag} {sb wb : BorrowStack}
    (hs : (wb.map Item.tag).Sublist (sb.map Item.tag))
    (hnd : (sb.map Item.tag).Nodup) (hbd : ∀ i ∈ sb, i.tag < N) :
    (wb.map Item.tag).Nodup ∧ ∀ i ∈ wb, i.tag < N := by
  refine ⟨List.Nodup.sublist hs hnd, fun i hi => ?_⟩
  obtain ⟨j, hj, hji⟩ := List.mem_map.mp (hs.subset (List.mem_map_of_mem hi))
  rw [← hji]; exact hbd j hj

theorem readCellContent_cell {E : Tag → Prop} {N : Tag} {pf : List (List Tag)} {ex : List Tag}
    (hEp : ∀ t, E t → isProtectedIn pf t = false) (hEx : ∀ t, E t → ex.contains t = false)
    {addr : Word} {tag : Tag} {sa sb wa : BorrowStack}
    (h : CellRel E N sa sb) (hA : readCellContent pf ex addr tag sa = .ok wa) :
    ∃ wb, readCellContent pf ex addr tag sb = .ok wb ∧ CellRel E N wa wb := by
  obtain ⟨⟨b, hs⟩, hnd, hbd, ⟨t0, hl⟩⟩ := h
  -- resolve the acting tag the same way on both sides
  obtain ⟨t, hAR, hBR⟩ : ∃ t, readCellContentR pf addr t sa = .ok wa ∧
      ∀ w, readCellContentR pf addr t sb = .ok w → readCellContent pf ex addr tag sb = .ok w := by
    by_cases hw : (tag == wildcardTag) = true
    · have htw : tag = wildcardTag := by simpa using hw
      subst htw
      cases hr : resolveWildcardIn ex sa false with
      | none => exact absurd hA (readCellContent_wild_none hr)
      | some t =>
          refine ⟨t, by rw [← readCellContent_wild hr]; exact hA, fun w hw' => ?_⟩
          rw [readCellContent_wild ((resolveWildcardIn_sub hEx hs false).trans hr)]; exact hw'
    · have hw' : (tag == wildcardTag) = false := by simpa using hw
      exact ⟨tag, by rw [← readCellContent_nonwild hw']; exact hA,
        fun w h => by rw [readCellContent_nonwild hw']; exact h⟩
  obtain ⟨wb, hBok, b', hs'⟩ := readCellContentR_sub hEp hs hnd hAR
  refine ⟨wb, hBR wb hBok, ⟨b', hs'⟩, ?_⟩
  obtain ⟨ab, it, bb, hspb, -, -, rfl⟩ := readCellContentR_ok hBok
  obtain ⟨aa, ita, ba, hspa, -, -, rfl⟩ := readCellContentR_ok hAR
  have hsb := (splitStack_some_eq hspb).1
  have hsa := (splitStack_some_eq hspa).1
  have hwf := cell_wf_sublist (N := N) (wb := ab.map disableF ++ it :: bb) (sb := sb)
    (by
      rw [hsb]
      simp [List.map_append, List.map_map, Function.comp_def, disableF_tag]) hnd hbd
  refine ⟨hwf.1, hwf.2, t0, ?_⟩
  rw [getLast?_append_cons, ← hl, hsa, getLast?_append_cons]

theorem writeCellContent_cell {E : Tag → Prop} {N : Tag} {pf : List (List Tag)} {ex : List Tag}
    (hEp : ∀ t, E t → isProtectedIn pf t = false) (hEx : ∀ t, E t → ex.contains t = false)
    {addr : Word} {tag : Tag} {sa sb wa : BorrowStack}
    (h : CellRel E N sa sb) (hA : writeCellContent pf ex addr tag sa = .ok wa) :
    ∃ wb, writeCellContent pf ex addr tag sb = .ok wb ∧ CellRel E N wa wb := by
  obtain ⟨⟨b, hs⟩, hnd, hbd, ⟨t0, hl⟩⟩ := h
  obtain ⟨t, hAR, hBR⟩ : ∃ t, writeCellContentR pf addr t sa = .ok wa ∧
      ∀ w, writeCellContentR pf addr t sb = .ok w → writeCellContent pf ex addr tag sb = .ok w := by
    by_cases hw : (tag == wildcardTag) = true
    · have htw : tag = wildcardTag := by simpa using hw
      subst htw
      cases hr : resolveWildcardIn ex sa true with
      | none => exact absurd hA (writeCellContent_wild_none hr)
      | some t =>
          refine ⟨t, by rw [← writeCellContent_wild hr]; exact hA, fun w hw' => ?_⟩
          rw [writeCellContent_wild ((resolveWildcardIn_sub hEx hs true).trans hr)]; exact hw'
    · have hw' : (tag == wildcardTag) = false := by simpa using hw
      exact ⟨tag, by rw [← writeCellContent_nonwild hw']; exact hA,
        fun w h => by rw [writeCellContent_nonwild hw']; exact h⟩
  obtain ⟨wb, hBok, b', hs'⟩ := writeCellContentR_sub hEp hs hnd hAR
  refine ⟨wb, hBR wb hBok, ⟨b', hs'⟩, ?_⟩
  obtain ⟨ab, it, bb, hspb, -, -, rfl⟩ := writeCellContentR_ok hBok
  obtain ⟨aa, ita, ba, hspa, -, -, rfl⟩ := writeCellContentR_ok hAR
  have hsb := (splitStack_some_eq hspb).1
  have hsa := (splitStack_some_eq hspa).1
  have hwf := cell_wf_sublist (N := N)
    (wb := (if it.isSrw then (srwSplit ab).2 else []) ++ it :: bb) (sb := sb)
    (by
      rw [hsb]
      refine List.Sublist.map _ (List.Sublist.append ?_ (List.Sublist.refl _))
      split
      · have h := List.sublist_append_right (srwSplit ab).1 (srwSplit ab).2
        rwa [srwSplit_append] at h
      · exact List.nil_sublist _) hnd hbd
  refine ⟨hwf.1, hwf.2, t0, ?_⟩
  rw [getLast?_append_cons, ← hl, hsa, getLast?_append_cons]

/-- Inserting the fresh item `x` (tag `N`, the minted tag) above an A-item. -/
theorem insertAboveContent_cell {E : Tag → Prop} {N : Tag} {ex : List Tag}
    (hEx : ∀ t, E t → ex.contains t = false)
    {addr : Word} {tag : Tag} {x : Item} (hx : x.tag = N) {sa sb wa : BorrowStack}
    (h : CellRel E N sa sb) (hA : insertAboveContent ex addr tag x sa = .ok wa) :
    ∃ wb, insertAboveContent ex addr tag x sb = .ok wb ∧ CellRel E (N + 1) wa wb := by
  obtain ⟨⟨b, hs⟩, hnd, hbd, ⟨t0, hl⟩⟩ := h
  obtain ⟨t, hAR, hBR⟩ : ∃ t, insertAboveContentR addr t x sa = .ok wa ∧
      ∀ w, insertAboveContentR addr t x sb = .ok w → insertAboveContent ex addr tag x sb = .ok w := by
    by_cases hw : (tag == wildcardTag) = true
    · have htw : tag = wildcardTag := by simpa using hw
      subst htw
      cases hr : resolveWildcardIn ex sa false with
      | none => exact absurd hA (insertAboveContent_wild_none hr)
      | some t =>
          refine ⟨t, by rw [← insertAboveContent_wild hr]; exact hA, fun w hw' => ?_⟩
          rw [insertAboveContent_wild ((resolveWildcardIn_sub hEx hs false).trans hr)]; exact hw'
    · have hw' : (tag == wildcardTag) = false := by simpa using hw
      exact ⟨tag, by rw [← insertAboveContent_nonwild hw']; exact hA,
        fun w h => by rw [insertAboveContent_nonwild hw']; exact h⟩
  obtain ⟨wb, hBok, b', hs', ab, bb, it, hsb, hwb⟩ := insertAboveContentR_sub hs hnd hAR
  refine ⟨wb, hBR wb hBok, ⟨b', hs'⟩, ?_, ?_, ?_⟩
  · have hN : x.tag ∉ sb.map Item.tag := by
      intro hm
      obtain ⟨j, hj, hjt⟩ := List.mem_map.mp hm
      have := hbd j hj; rw [hjt, hx] at this; exact Nat.lt_irrefl _ this
    have hp : (wb.map Item.tag).Perm (x.tag :: sb.map Item.tag) := by
      rw [hwb, hsb]
      simp only [List.map_append, List.map_cons]
      exact List.perm_middle
    exact hp.nodup_iff.mpr (List.nodup_cons.mpr ⟨hN, hnd⟩)
  · intro i hi
    rw [hwb] at hi
    rcases List.mem_append.mp hi with hi | hi
    · exact Nat.lt_succ_of_lt (hbd i (by rw [hsb]; exact List.mem_append_left _ hi))
    · rcases List.mem_cons.mp hi with rfl | hi
      · rw [hx]; exact Nat.lt_succ_self _
      · exact Nat.lt_succ_of_lt (hbd i (by rw [hsb]; exact List.mem_append_right _ hi))
  · obtain ⟨aa, ita, ba, hspa, -, rfl⟩ := insertAboveContentR_ok hAR
    have hsa := (splitStack_some_eq hspa).1
    refine ⟨t0, ?_⟩
    rw [getLast?_append_cons, ← hl, hsa, getLast?_append_cons, List.getLast?_cons_cons]

/-- Pushing the fresh, non-SRW item `x` (tag `N`). -/
theorem push_cell {E : Tag → Prop} {N : Tag} {x : Item} (hx : x.tag = N)
    (hxs : x.isSrw = false) {sa sb : BorrowStack} (h : CellRel E N sa sb) :
    CellRel E (N + 1) (x :: sa) (x :: sb) := by
  obtain ⟨⟨b, hs⟩, hnd, hbd, ⟨t0, hl⟩⟩ := h
  refine ⟨⟨false, .same x hs (fun _ => hxs)⟩, ?_, ?_, t0, ?_⟩
  · refine List.nodup_cons.mpr ⟨fun hm => ?_, hnd⟩
    obtain ⟨j, hj, hjt⟩ := List.mem_map.mp hm
    have := hbd j hj; rw [hjt, hx] at this; exact Nat.lt_irrefl _ this
  · intro i hi
    rcases List.mem_cons.mp hi with rfl | hi
    · rw [hx]; exact Nat.lt_succ_self _
    · exact Nat.lt_succ_of_lt (hbd i hi)
  · cases sa with
    | nil => simp at hl
    | cons y ys => rw [List.getLast?_cons_cons]; exact hl

/-- A fresh cell. -/
theorem own_cell {E : Tag → Prop} (N : Tag) :
    CellRel E (N + 1) [.Own N] [.Own N] :=
  ⟨⟨false, StackSub.refl _⟩, by simp, by simp [Item.tag], N, rfl⟩

/-- A's top item, kept by B, becomes an extra. -/
theorem StackSub.pop_head {E : Tag → Prop} {b : Bool} {x : Item} {wa sb : BorrowStack}
    (h : StackSub E b (x :: wa) sb) (hx : E x.tag) : ∃ b', StackSub E b' wa sb := by
  generalize hsa : x :: wa = sa at h
  induction h generalizing wa with
  | nil => cases hsa
  | @same b' sa' sb' i h' _ _ =>
      injection hsa with h1 h2
      subst h1 h2
      exact ⟨true, .extra x hx h'⟩
  | @extra b' sa' sb' e he h' ih =>
      obtain ⟨b'', h''⟩ := ih hsa
      exact ⟨true, .extra e he h''⟩

/-- A's `die` pops its top item `h`; B keeps it, now an extra (`E'` holds
    of its tag: retired, unprotected). -/
theorem dieCellContent_cell {E E' : Tag → Prop} {N : Tag} {pf : List (List Tag)} {tag : Tag}
    {sa sb wa : BorrowStack} (h : CellRel E N sa sb)
    (hA : dieCellContent pf tag sa = .ok wa)
    (hE : ∀ x ∈ sb, E x.tag → E' x.tag) (hE' : E' tag) :
    CellRel E' N wa sb := by
  obtain ⟨⟨b, hs⟩, hnd, hbd, ⟨t0, hl⟩⟩ := h
  cases sa with
  | nil => simp [dieCellContent] at hA
  | cons it below =>
    obtain ⟨htag, hno, -, rfl⟩ := dieCellContent_cons_inv hA
    refine ⟨?_, hnd, hbd, t0, ?_⟩
    · -- B's copy of `it` becomes an extra
      exact StackSub.pop_head (hs.mono_mem hE) (by rw [htag]; exact hE')
    · cases wa with
      | nil =>
          simp only [List.getLast?_singleton, Option.some.injEq] at hl
          exact absurd hl (hno t0)
      | cons y ys => rw [List.getLast?_cons_cons] at hl; exact hl

/-! ## Retag -/

theorem refCellContent_cell {E : Tag → Prop} {N : Tag} {pf : List (List Tag)} {ex : List Tag}
    (hEp : ∀ t, E t → isProtectedIn pf t = false) (hEx : ∀ t, E t → ex.contains t = false)
    {a : Word} {tag : Tag} {kind : RefKind} {mask : List Bool} {i : Nat}
    {sa sb wa : BorrowStack} (h : CellRel E N sa sb)
    (hA : refCellContent pf ex a tag kind N mask i sa = .ok wa) :
    ∃ wb, refCellContent pf ex a tag kind N mask i sb = .ok wb ∧ CellRel E (N + 1) wa wb := by
  -- an access, then a push of the fresh non-SRW item
  have access_push : ∀ (acc : BorrowStack → Except String BorrowStack) (x : Item),
      x.tag = N → x.isSrw = false →
      (∀ {va}, acc sa = .ok va → ∃ vb, acc sb = .ok vb ∧ CellRel E N va vb) →
      (match acc sa with | .error e => .error e | .ok v => .ok (x :: v)) = Except.ok wa →
      ∃ wb, (match acc sb with | .error e => .error e | .ok v => .ok (x :: v)) = Except.ok wb ∧
        CellRel E (N + 1) wa wb := by
    intro acc x hx hxs hacc hA
    split at hA
    · cases hA
    rename_i v hv
    obtain ⟨vb, hvb, hrel⟩ := hacc hv
    rw [hvb]
    obtain rfl := Except.ok.inj hA
    exact ⟨_, rfl, push_cell hx hxs hrel⟩
  cases kind with
  | Mut =>
      simp only [refCellContent] at hA ⊢
      exact access_push _ _ rfl rfl (writeCellContent_cell hEp hEx h) hA
  | BoxMut =>
      simp only [refCellContent] at hA ⊢
      exact access_push _ _ rfl rfl (writeCellContent_cell hEp hEx h) hA
  | Shared =>
      simp only [refCellContent] at hA ⊢
      split
      · rename_i hm
        rw [if_pos hm] at hA
        exact insertAboveContent_cell hEx rfl h hA
      · rename_i hm
        rw [if_neg hm] at hA
        exact access_push _ _ rfl rfl (readCellContent_cell hEp hEx h) hA
  | Raw m =>
      cases m with
      | false =>
          simp only [refCellContent] at hA ⊢
          split
          · rename_i hm
            rw [if_pos hm] at hA
            exact insertAboveContent_cell hEx rfl h hA
          · rename_i hm
            rw [if_neg hm] at hA
            exact access_push _ _ rfl rfl (readCellContent_cell hEp hEx h) hA
      | true =>
          simp only [refCellContent] at hA ⊢
          exact insertAboveContent_cell hEx rfl h hA
  | TwoPhase =>
      simp only [refCellContent] at hA ⊢
      split at hA
      · cases hA
      rename_i v hv
      obtain ⟨vb, hvb, hrel⟩ := readCellContent_cell hEp hEx h hv
      rw [hvb]
      exact insertAboveContent_cell hEx rfl hrel hA

end obseq3.proof
