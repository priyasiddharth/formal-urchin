import obseq3.proof.permsub

/-!
# Die elision, backward per operation

The converse of `permsub.lean`: when B (OSEA-IR_B's permission state, with
extras) performs an operation through a tag that A has NOT retired, A
performs it too. The acting item B finds is then not an extra (an extra's
tag is retired), so A has the same item; A pops or disables a subset of
what B does, so A's protector checks pass when B's do. A wildcard resolves
alike on both sides and never to an extra (extras are unexposed).

Each `*_back` lemma pairs this with the forward lemma: A succeeds, with a
result related to B's.
-/

namespace obseq3.proof

open obseq3

/-! ## Cells -/

/-- Splitting B at a tag that is not an extra's finds an A-item. -/
theorem splitStack_rev {E : Tag → Prop} {b : Bool} {sa sb : BorrowStack} {t : Tag}
    (h : StackSub E b sa sb) (ht : ¬ E t) {ab bb : BorrowStack} {it : Item}
    (hs : splitStack sb t = some (ab, it, bb)) :
    ∃ aa ba, splitStack sa t = some (aa, it, ba) := by
  induction h generalizing ab bb with
  | nil => simp [splitStack] at hs
  | @same b' sa' sb' i h' _ ih =>
      simp only [splitStack] at hs ⊢
      split at hs
      · rename_i hi
        simp only [Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨-, rfl, -⟩ := hs
        rw [if_pos hi]
        exact ⟨_, _, rfl⟩
      · rename_i hi
        rw [if_neg hi]
        split at hs
        · rename_i ab' it' bb' hs'
          simp only [Option.some.injEq, Prod.mk.injEq] at hs
          obtain ⟨-, rfl, -⟩ := hs
          obtain ⟨aa, ba, ha⟩ := ih hs'
          rw [ha]
          exact ⟨_, _, rfl⟩
        · cases hs
  | @extra b' sa' sb' e he h' ih =>
      simp only [splitStack] at hs
      split at hs
      · rename_i hi
        exact absurd (by rw [← (beq_iff_eq.mp hi)]; exact he) ht
      · split at hs
        · rename_i ab' it' bb' hs'
          simp only [Option.some.injEq, Prod.mk.injEq] at hs
          obtain ⟨-, rfl, -⟩ := hs
          exact ih hs'
        · cases hs

theorem firstProtectedIn_none_subset {pf : List (List Tag)} {l l' : List Item}
    (hm : ∀ k ∈ l, k ∈ l') (h : firstProtectedIn pf l' = none) :
    firstProtectedIn pf l = none := by
  unfold firstProtectedIn at h ⊢
  rw [List.find?_eq_none] at h ⊢
  exact fun k hk => h k (hm k hk)

theorem resolveWildcardIn_exposed {ex : List Tag} {s : BorrowStack} {nw : Bool} {t : Tag}
    (h : resolveWildcardIn ex s nw = some t) : ex.contains t = true := by
  unfold resolveWildcardIn at h
  obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.mp h
  have := List.find?_some hk
  cases k with
  | Disabled _ => simp at this
  | _ => simp only [Bool.and_eq_true] at this; exact this.1

/-- The facts the reverse cell lemmas consume. -/
def CellBack (E : Tag → Prop) (sa sb : BorrowStack) : Prop :=
  (∃ b, StackSub E b sa sb) ∧ (sb.map Item.tag).Nodup

theorem CellRel.back {E : Tag → Prop} {N : Tag} {sa sb : BorrowStack}
    (h : CellRel E N sa sb) : CellBack E sa sb := ⟨h.1, h.2.1⟩

theorem readCellContentR_rev {E : Tag → Prop} {pf : List (List Tag)} {addr : Word} {t : Tag}
    {sa sb wb : BorrowStack} (h : CellBack E sa sb) (ht : ¬ E t)
    (hB : readCellContentR pf addr t sb = .ok wb) :
    ∃ wa, readCellContentR pf addr t sa = .ok wa := by
  obtain ⟨⟨b, hsub⟩, hnd⟩ := h
  obtain ⟨ab, it, bb, hspb, hnd', hfp, -⟩ := readCellContentR_ok hB
  obtain ⟨aa, ba, hspa⟩ := splitStack_rev hsub ht hspb
  obtain ⟨ab', bb', hspb', ⟨b1, hab, -⟩, -⟩ := splitStack_sub hsub hnd hspa
  rw [hspb] at hspb'
  simp only [Option.some.injEq, Prod.mk.injEq] at hspb'
  obtain ⟨rfl, -, rfl⟩ := hspb'
  refine ⟨_, readCellContentR_of hspa hnd' (firstProtectedIn_none_subset (fun k hk => ?_) hfp)⟩
  obtain ⟨hk1, hk2⟩ := List.mem_filter.mp hk
  exact List.mem_filter.mpr ⟨hab.mem_left hk1, hk2⟩

theorem writeCellContentR_rev {E : Tag → Prop} {pf : List (List Tag)} {addr : Word} {t : Tag}
    {sa sb wb : BorrowStack} (h : CellBack E sa sb) (ht : ¬ E t)
    (hB : writeCellContentR pf addr t sb = .ok wb) :
    ∃ wa, writeCellContentR pf addr t sa = .ok wa := by
  obtain ⟨⟨b, hsub⟩, hnd⟩ := h
  obtain ⟨ab, it, bb, hspb, hgw, hfp, -⟩ := writeCellContentR_ok hB
  obtain ⟨aa, ba, hspa⟩ := splitStack_rev hsub ht hspb
  obtain ⟨ab', bb', hspb', ⟨b1, hab, -⟩, -⟩ := splitStack_sub hsub hnd hspa
  rw [hspb] at hspb'
  simp only [Option.some.injEq, Prod.mk.injEq] at hspb'
  obtain ⟨rfl, -, rfl⟩ := hspb'
  refine ⟨_, writeCellContentR_of hspa hgw ?_⟩
  cases hsrw : it.isSrw
  · simp only [hsrw, Bool.false_eq_true, if_false] at hfp ⊢
    exact firstProtectedIn_none_subset (fun k hk => hab.mem_left hk) hfp
  · simp only [hsrw, if_true] at hfp ⊢
    obtain ⟨-, -, -, -, hRa⟩ := srwSplit_sub hab
    exact firstProtectedIn_none_subset hRa hfp

theorem insertAboveContentR_rev {E : Tag → Prop} {addr : Word} {t : Tag} {x : Item}
    {sa sb wb : BorrowStack} (h : CellBack E sa sb) (ht : ¬ E t)
    (hB : insertAboveContentR addr t x sb = .ok wb) :
    ∃ wa, insertAboveContentR addr t x sa = .ok wa := by
  obtain ⟨⟨b, hsub⟩, -⟩ := h
  obtain ⟨ab, it, bb, hspb, hnd', -⟩ := insertAboveContentR_ok hB
  obtain ⟨aa, ba, hspa⟩ := splitStack_rev hsub ht hspb
  exact ⟨_, insertAboveContentR_of hspa hnd'⟩

/-- The acting tag a content op resolves to, on B, is resolved alike on A
    and is not an extra's. -/
theorem acting_rev {E : Tag → Prop} {ex : List Tag} (hEx : ∀ t, E t → ex.contains t = false)
    {sa sb : BorrowStack} (h : CellBack E sa sb) (nw : Bool) {tag : Tag}
    (htag : tag ≠ wildcardTag → ¬ E tag) :
    ((tag == wildcardTag) = false ∧ ¬ E tag) ∨
      (∃ t, tag = wildcardTag ∧ ¬ E t ∧ resolveWildcardIn ex sb nw = some t ∧
        resolveWildcardIn ex sa nw = some t) ∨
      (tag = wildcardTag ∧ resolveWildcardIn ex sb nw = none) := by
  obtain ⟨⟨b, hsub⟩, -⟩ := h
  by_cases hw : tag = wildcardTag
  · subst hw
    right
    cases hr : resolveWildcardIn ex sb nw with
    | none => exact Or.inr ⟨rfl, rfl⟩
    | some t =>
        refine Or.inl ⟨t, rfl, fun he => ?_, rfl, ?_⟩
        · have := resolveWildcardIn_exposed hr
          rw [hEx t he] at this; cases this
        · rw [← resolveWildcardIn_sub hEx hsub nw]; exact hr
  · exact Or.inl ⟨by simpa using hw, htag hw⟩

theorem readCellContent_rev {E : Tag → Prop} {pf : List (List Tag)} {ex : List Tag}
    (hEx : ∀ t, E t → ex.contains t = false) {addr : Word} {tag : Tag}
    {sa sb wb : BorrowStack} (h : CellBack E sa sb) (htag : tag ≠ wildcardTag → ¬ E tag)
    (hB : readCellContent pf ex addr tag sb = .ok wb) :
    ∃ wa, readCellContent pf ex addr tag sa = .ok wa := by
  rcases acting_rev hEx h false htag with ⟨hw, ht⟩ | ⟨t, rfl, ht, hrb, hra⟩ | ⟨rfl, hrb⟩
  · rw [readCellContent_nonwild hw] at hB ⊢
    exact readCellContentR_rev h ht hB
  · rw [readCellContent_wild hrb] at hB
    rw [readCellContent_wild hra]
    exact readCellContentR_rev h ht hB
  · exact absurd hB (readCellContent_wild_none hrb)

theorem writeCellContent_rev {E : Tag → Prop} {pf : List (List Tag)} {ex : List Tag}
    (hEx : ∀ t, E t → ex.contains t = false) {addr : Word} {tag : Tag}
    {sa sb wb : BorrowStack} (h : CellBack E sa sb) (htag : tag ≠ wildcardTag → ¬ E tag)
    (hB : writeCellContent pf ex addr tag sb = .ok wb) :
    ∃ wa, writeCellContent pf ex addr tag sa = .ok wa := by
  rcases acting_rev hEx h true htag with ⟨hw, ht⟩ | ⟨t, rfl, ht, hrb, hra⟩ | ⟨rfl, hrb⟩
  · rw [writeCellContent_nonwild hw] at hB ⊢
    exact writeCellContentR_rev h ht hB
  · rw [writeCellContent_wild hrb] at hB
    rw [writeCellContent_wild hra]
    exact writeCellContentR_rev h ht hB
  · exact absurd hB (writeCellContent_wild_none hrb)

theorem insertAboveContent_rev {E : Tag → Prop} {ex : List Tag}
    (hEx : ∀ t, E t → ex.contains t = false) {addr : Word} {tag : Tag} {x : Item}
    {sa sb wb : BorrowStack} (h : CellBack E sa sb) (htag : tag ≠ wildcardTag → ¬ E tag)
    (hB : insertAboveContent ex addr tag x sb = .ok wb) :
    ∃ wa, insertAboveContent ex addr tag x sa = .ok wa := by
  rcases acting_rev hEx h false htag with ⟨hw, ht⟩ | ⟨t, rfl, ht, hrb, hra⟩ | ⟨rfl, hrb⟩
  · rw [insertAboveContent_nonwild hw] at hB ⊢
    exact insertAboveContentR_rev h ht hB
  · rw [insertAboveContent_wild hrb] at hB
    rw [insertAboveContent_wild hra]
    exact insertAboveContentR_rev h ht hB
  · exact absurd hB (insertAboveContent_wild_none hrb)

theorem refCellContent_rev {E : Tag → Prop} {N : Tag} {pf : List (List Tag)} {ex : List Tag}
    (hEp : ∀ t, E t → isProtectedIn pf t = false) (hEx : ∀ t, E t → ex.contains t = false)
    {a : Word} {tag : Tag} {kind : RefKind} {mask : List Bool} {i : Nat}
    {sa sb wb : BorrowStack} (h : CellRel E N sa sb) (htag : tag ≠ wildcardTag → ¬ E tag)
    (hB : refCellContent pf ex a tag kind N mask i sb = .ok wb) :
    ∃ wa, refCellContent pf ex a tag kind N mask i sa = .ok wa := by
  have hb := h.back
  -- an access, then a push
  have access_push : ∀ (acc : BorrowStack → Except String BorrowStack) (x : Item),
      (∀ {vb}, acc sb = .ok vb → ∃ va, acc sa = .ok va) →
      (match acc sb with | .error e => .error e | .ok v => .ok (x :: v)) = Except.ok wb →
      ∃ wa, (match acc sa with | .error e => .error e | .ok v => .ok (x :: v)) = Except.ok wa := by
    intro acc x hacc hB
    split at hB
    · cases hB
    rename_i v hv
    obtain ⟨va, hva⟩ := hacc hv
    rw [hva]
    exact ⟨_, rfl⟩
  cases kind with
  | Mut | BoxMut =>
      simp only [refCellContent] at hB ⊢
      exact access_push _ _ (writeCellContent_rev hEx hb htag) hB
  | Shared =>
      simp only [refCellContent] at hB ⊢
      split
      · rename_i hm
        rw [if_pos hm] at hB
        exact insertAboveContent_rev hEx hb htag hB
      · rename_i hm
        rw [if_neg hm] at hB
        exact access_push _ _ (readCellContent_rev hEx hb htag) hB
  | Raw m =>
      cases m with
      | false =>
          simp only [refCellContent] at hB ⊢
          split
          · rename_i hm
            rw [if_pos hm] at hB
            exact insertAboveContent_rev hEx hb htag hB
          · rename_i hm
            rw [if_neg hm] at hB
            exact access_push _ _ (readCellContent_rev hEx hb htag) hB
      | true =>
          simp only [refCellContent] at hB ⊢
          exact insertAboveContent_rev hEx hb htag hB
  | TwoPhase =>
      simp only [refCellContent] at hB ⊢
      split at hB
      · cases hB
      rename_i vb hvb
      obtain ⟨va, hva⟩ := readCellContent_rev hEx hb htag hvb
      obtain ⟨vb', hvb', hrel⟩ := readCellContent_cell hEp hEx h hva
      rw [hvb] at hvb'
      obtain rfl := Except.ok.inj hvb'
      rw [hva]
      exact insertAboveContent_rev hEx hrel.back htag hB

/-! ## Ranges -/

theorem StackMapRel.find?_some_rev {R : BorrowStack → BorrowStack → Prop} {x y : SB}
    (h : StackMapRel R x y) {a : Word} {s' : BorrowStack}
    (hf : SB.find? y a = some s') : ∃ s, SB.find? x a = some s ∧ R s s' := by
  have := h a
  rw [hf] at this
  cases hx : SB.find? x a with
  | none => rw [hx] at this; exact this.elim
  | some s => rw [hx] at this; exact ⟨s, rfl, this⟩

theorem StackMapRel.find?_none_rev {R : BorrowStack → BorrowStack → Prop} {x y : SB}
    (h : StackMapRel R x y) {a : Word} (hf : SB.find? y a = none) : SB.find? x a = none := by
  have := h a
  rw [hf] at this
  cases hx : SB.find? x a with
  | none => rfl
  | some s => rw [hx] at this; exact this.elim

/-- The reverse of `foldCells_sub`: B's success gives A's. -/
theorem foldCells_rev
    {opA opB : AccessPerms → Word → Except String AccessPerms}
    {CA CB : Word → BorrowStack → Except String BorrowStack}
    {mA mB : Word → String}
    {R : BorrowStack → BorrowStack → Prop}
    {A B B' : AccessPerms} {addr : Word} {lenB : Nat}
    (hA_op : ∀ ap a, ap.protFrames = A.protFrames → ap.exposed = A.exposed →
      ap.NextTag = A.NextTag →
      opA ap a =
        match SB.find? ap.StackMap a with
        | none => .error (mA a)
        | some stack =>
          match CA a stack with
          | .error e => .error e
          | .ok v => .ok { ap with StackMap := SB.set ap.StackMap a v })
    (hB_op : ∀ ap a, ap.protFrames = B.protFrames → ap.exposed = B.exposed →
      ap.NextTag = B.NextTag →
      opB ap a =
        match SB.find? ap.StackMap a with
        | none => .error (mB a)
        | some stack =>
          match CB a stack with
          | .error e => .error e
          | .ok v => .ok { ap with StackMap := SB.set ap.StackMap a v })
    (hC : ∀ a sa sb wb, R sa sb → CB a sb = .ok wb → ∃ wa, CA a sa = .ok wa)
    (hrel : StackMapRel R A.StackMap B.StackMap)
    (h : foldCells opB B addr lenB = .ok B') :
    ∃ A', foldCells opA A addr lenB = .ok A' := by
  have h0 : foldCells opB B (addr + 0) lenB = .ok B' := h
  obtain ⟨V, W, h_cells, -⟩ :=
    foldCells_ok_inv (C := CB) (msgNone := mB) hB_op lenB 0 B B' rfl rfl rfl h0
  have h_pkg : ∀ j, ∃ vj, ∃ wj, j < lenB →
      SB.find? A.StackMap (addr + j) = some vj ∧ CA (addr + j) vj = .ok wj := by
    intro j
    by_cases hj : j < lenB
    · have hc := h_cells j (Nat.zero_le j) (by omega)
      obtain ⟨s, hf, hr⟩ := hrel.find?_some_rev hc.1
      obtain ⟨w, hw⟩ := hC _ _ _ _ hr hc.2
      exact ⟨s, w, fun _ => ⟨hf, hw⟩⟩
    · exact ⟨[], [], fun h => absurd h hj⟩
  have h_pkg' := fun j (hj : j < lenB) => (h_pkg j).choose_spec.choose_spec hj
  have hA := foldCells_ok_of_cells (C := CA) (msgNone := mA) hA_op lenB 0 A
    (fun j => (h_pkg j).choose) (fun j => (h_pkg j).choose_spec.choose) rfl rfl rfl
    (fun j _ h2 => (h_pkg' j (by omega)).1) (fun j _ h2 => (h_pkg' j (by omega)).2)
  exact ⟨_, hA⟩

/-- The acting-tag condition: not retired (a wildcard is resolved per cell). -/
abbrev ActOK (A : AccessPerms) (t : Tag) : Prop := t ≠ wildcardTag → t ∉ A.retired

theorem ActOK.not_extra {A : AccessPerms} {t : Tag} (h : ActOK A t) :
    t ≠ wildcardTag → ¬ Extra A t := fun hw he => h hw he.1

theorem sb_write_back {A B B' : AccessPerms} {addr : Word} {lenB : Nat} {t : Tag}
    (hs : PermSub A B) (ht : ActOK A t) (h : sb_write B addr lenB t = .ok B') :
    ∃ A', sb_write A addr lenB t = .ok A' ∧ PermSub A' B' := by
  obtain ⟨A', hA⟩ := foldCells_rev
    (CA := fun a stack => writeCellContent A.protFrames A.exposed a t stack)
    (CB := fun a stack => writeCellContent B.protFrames B.exposed a t stack)
    (fun ap a h_pf h_ex _ => writeCell_content_form t ap a h_pf h_ex)
    (fun ap a h_pf h_ex _ => writeCell_content_form t ap a h_pf h_ex)
    (fun a sa sb wb hr hB => by
      rw [hs.prot, hs.exp] at hB
      exact writeCellContent_rev hs.hEx hr.back ht.not_extra hB)
    hs.stacks h
  obtain ⟨B'', hB, hs'⟩ := sb_write_sub hs hA
  rw [h] at hB
  obtain rfl := Except.ok.inj hB
  exact ⟨A', hA, hs'⟩

theorem sb_read_back {A B B' : AccessPerms} {addr : Word} {lenB : Nat} {t : Tag}
    (hs : PermSub A B) (ht : ActOK A t) (h : sb_read B addr lenB t = .ok B') :
    ∃ A', sb_read A addr lenB t = .ok A' ∧ PermSub A' B' := by
  obtain ⟨A', hA⟩ := foldCells_rev
    (CA := fun a stack => readCellContent A.protFrames A.exposed a t stack)
    (CB := fun a stack => readCellContent B.protFrames B.exposed a t stack)
    (fun ap a h_pf h_ex _ => readCell_content_form t ap a h_pf h_ex)
    (fun ap a h_pf h_ex _ => readCell_content_form t ap a h_pf h_ex)
    (fun a sa sb wb hr hB => by
      rw [hs.prot, hs.exp] at hB
      exact readCellContent_rev hs.hEx hr.back ht.not_extra hB)
    hs.stacks h
  obtain ⟨B'', hB, hs'⟩ := sb_read_sub hs hA
  rw [h] at hB
  obtain rfl := Except.ok.inj hB
  exact ⟨A', hA, hs'⟩

theorem sb_ref_back {A B B' : AccessPerms} {addr : Word} {lenB : Nat} {t : Tag}
    {kind : RefKind} {prot : Bool} {mask : List Bool} {n : Tag}
    (hs : PermSub A B) (ht : ActOK A t)
    (h : sb_ref B addr lenB t kind prot mask = .ok (B', n)) :
    ∃ A', sb_ref A addr lenB t kind prot mask = .ok (A', n) ∧ PermSub A' B' := by
  suffices hA : ∃ A' n', sb_ref A addr lenB t kind prot mask = .ok (A', n') by
    obtain ⟨A', n', hA⟩ := hA
    obtain ⟨B'', hB, hs'⟩ := sb_ref_sub hs hA
    rw [h] at hB
    simp only [Except.ok.injEq, Prod.mk.injEq] at hB
    obtain ⟨rfl, rfl⟩ := hB
    exact ⟨A', hA, hs'⟩
  rw [sb_ref_eq] at h ⊢
  split at h
  · cases h
  rename_i bpR hgo
  obtain ⟨W', h_cells, rfl⟩ :=
    foldCellsIdx_ok_inv
      (op := refCellOp t kind B.NextTag mask)
      (C := fun j v? => refCellStep B.protFrames B.exposed (addr + j) t kind B.NextTag mask j v?)
      (P := B.protFrames) (E := B.exposed) (N := B.NextTag + 1)
      (refCellOp_content_form (addr := addr) t kind B.NextTag mask)
      { B with NextTag := B.NextTag + 1 } _ rfl rfl rfl hgo
  have h_pkg : ∀ j, ∃ wj, j < lenB →
      refCellStep A.protFrames A.exposed (addr + j) t kind A.NextTag mask j
          (SB.find? A.StackMap (addr + j)) = .ok wj := by
    intro j
    by_cases hj : j < lenB
    · obtain ⟨vb, hf, hc⟩ := refCellStep_ok_inv (h_cells j (Nat.zero_le j) hj)
      obtain ⟨va, hfa, hr⟩ := hs.stacks.find?_some_rev hf
      rw [hs.prot, hs.exp, hs.next] at hc
      obtain ⟨wa, hwa⟩ := refCellContent_rev hs.hEp hs.hEx hr ht.not_extra hc
      exact ⟨wa, fun _ => by rw [hfa]; exact hwa⟩
    · exact ⟨[], fun h => absurd h hj⟩
  have h_goA :=
    foldCellsIdx_ok_of_cells
      (op := refCellOp t kind A.NextTag mask)
      (C := fun j v? => refCellStep A.protFrames A.exposed (addr + j) t kind A.NextTag mask j v?)
      (P := A.protFrames) (E := A.exposed) (N := A.NextTag + 1)
      (refCellOp_content_form (addr := addr) t kind A.NextTag mask)
      (i := 0) (lenB := lenB)
      { A with NextTag := A.NextTag + 1 } (fun j => (h_pkg j).choose) rfl rfl rfl
      (fun j _ h2 => (h_pkg j).choose_spec h2)
  rw [h_goA]
  simp only at h ⊢
  rw [hs.prot, hs.wk, hs.next] at h
  split at h
  · cases h
  exact ⟨_, _, rfl⟩

theorem sb_own_back {A B B' : AccessPerms} {addr : Word} {lenB : Nat} {n : Tag}
    (hs : PermSub A B) (h : sb_own B addr lenB = .ok (B', n)) :
    ∃ A', sb_own A addr lenB = .ok (A', n) ∧ PermSub A' B' := by
  suffices hA : ∃ A' n', sb_own A addr lenB = .ok (A', n') by
    obtain ⟨A', n', hA⟩ := hA
    obtain ⟨B'', hB, hs'⟩ := sb_own_sub hs hA
    rw [h] at hB
    simp only [Except.ok.injEq, Prod.mk.injEq] at hB
    obtain ⟨rfl, rfl⟩ := hB
    exact ⟨A', hA, hs'⟩
  rw [sb_own_eq] at h ⊢
  split at h
  · cases h
  rename_i bpR hgo
  have hgo0 : foldCells (fun q a => ownCell q a B.NextTag) { B with NextTag := B.NextTag + 1 }
      (addr + 0) lenB = .ok bpR := hgo
  rw [foldCells_ok_iff_foldCellsIdx_ok] at hgo0
  obtain ⟨W, h_cells, -⟩ :=
    foldCellsIdx_ok_inv (op := fun ap a _ => ownCell ap a B.NextTag)
      (C := fun i o => ownCellStep (addr + i) B.NextTag o)
      (P := B.protFrames) (E := B.exposed) (N := B.NextTag + 1)
      (fun ap i _ _ _ => ownCell_content_form B.NextTag ap (addr + i))
      { B with NextTag := B.NextTag + 1 } _ rfl rfl rfl hgo0
  have hcA : ∀ j, 0 ≤ j → j < 0 + lenB →
      ownCellStep (addr + j) A.NextTag (SB.find? A.StackMap (addr + j)) = .ok [.Own A.NextTag] := by
    intro j h1 h2
    have hc := h_cells j h1 h2
    cases hf : SB.find? B.StackMap (addr + j) with
    | none => rw [hs.stacks.find?_none_rev hf]; rfl
    | some s' =>
        obtain ⟨s, hfa, hr⟩ := hs.stacks.find?_some_rev hf
        rw [show ({ B with NextTag := B.NextTag + 1 } : AccessPerms).StackMap = B.StackMap
          from rfl, hf] at hc
        cases s' with
        | cons _ _ => simp [ownCellStep] at hc
        | nil =>
            obtain ⟨⟨b, hsub⟩, -, -, t0, hl⟩ := hr
            rw [(hsub.nil_right).1] at hl
            simp at hl
  have hgoA :=
    foldCellsIdx_ok_of_cells (op := fun ap a _ => ownCell ap a A.NextTag)
      (C := fun i o => ownCellStep (addr + i) A.NextTag o)
      (P := A.protFrames) (E := A.exposed) (N := A.NextTag + 1)
      (fun ap i _ _ _ => ownCell_content_form A.NextTag ap (addr + i))
      (i := 0) (lenB := 0 + lenB) { A with NextTag := A.NextTag + 1 } (fun _ => [.Own A.NextTag])
      rfl rfl rfl hcA
  have hgoA' := (foldCells_ok_iff_foldCellsIdx_ok _ addr lenB 0 _ _).mpr hgoA
  rw [show foldCells (fun q a => ownCell q a A.NextTag) { A with NextTag := A.NextTag + 1 }
      addr lenB = _ from hgoA']
  exact ⟨_, _, rfl⟩

theorem sb_dealloc_back {tag : Tag} :
    ∀ (lenB : Nat) (addr : Word) {A B B' : AccessPerms},
      PermSub A B → tag ∉ A.retired → sb_dealloc B addr lenB tag = .ok B' →
      ∃ A', sb_dealloc A addr lenB tag = .ok A' ∧ PermSub A' B' := by
  intro lenB
  induction lenB with
  | zero =>
      intro addr A B B' hs _ h
      rw [sb_dealloc_eq] at h
      simp only [foldCells] at h
      cases h
      exact ⟨A, rfl, hs⟩
  | succ n ih =>
      intro addr A B B' hs ht h
      rw [sb_dealloc_eq] at h ⊢
      simp only [foldCells] at h
      split at h
      · simp at h
      rename_i B1 h_cell
      obtain ⟨stack', ab', item, bb', h_find', h_split', h_gw, h_fp, h_sp, rfl⟩ :=
        deallocCellOp_ok_inv h_cell
      obtain ⟨stack, h_find, hr⟩ := hs.stacks.find?_some_rev h_find'
      obtain ⟨⟨b, hsub⟩, hnd, -, -⟩ := hr
      obtain ⟨aa, ba, h_split⟩ := splitStack_rev hsub (fun he => ht he.1) h_split'
      obtain ⟨ab'', bb'', h_split'', ⟨b1, h1, -⟩, ⟨b2, h2, -⟩⟩ := splitStack_sub hsub hnd h_split
      rw [h_split'] at h_split''
      simp only [Option.some.injEq, Prod.mk.injEq] at h_split''
      obtain ⟨rfl, -, rfl⟩ := h_split''
      have h_fpA : firstProtectedIn A.protFrames aa = none := by
        rw [← hs.prot]
        exact firstProtectedIn_none_subset (fun k hk => h1.mem_left hk) h_fp
      have h_spA : (item :: ba).find? (strongProt A.protFrames A.weakProt) = none := by
        rw [← hs.prot, ← hs.wk]
        rw [List.find?_eq_none] at h_sp ⊢
        intro k hk
        rcases List.mem_cons.mp hk with rfl | hk
        · exact h_sp _ List.mem_cons_self
        · exact h_sp _ (List.mem_cons_of_mem _ (h2.mem_left hk))
      have hs1 : PermSub { A with StackMap := A.StackMap.filter (fun (x, _) => x != addr) }
          { B with StackMap := B.StackMap.filter (fun (x, _) => x != addr) } :=
        ⟨hs.stacks.filter_cell addr, hs.next, hs.prot, hs.exp, hs.wk, hs.ret, hs.disj⟩
      obtain ⟨A', h_A, hs'⟩ := ih (addr + 1) hs1 ht h
      refine ⟨A', ?_, hs'⟩
      simp only [foldCells]
      rw [deallocCellOp_ok_eq A addr tag h_find h_split h_gw h_fpA h_spA]
      rw [sb_dealloc_eq] at h_A
      exact h_A

theorem sb_expose_back {A B B' : AccessPerms} {t : Tag}
    (hs : PermSub A B) (ht : ActOK A t) (h : sb_expose B t = .ok B') :
    ∃ A', sb_expose A t = .ok A' ∧ PermSub A' B' := by
  suffices hA : ∃ A', sb_expose A t = .ok A' by
    obtain ⟨A', hA⟩ := hA
    obtain ⟨B'', hB, hs'⟩ := sb_expose_sub hs hA
    rw [h] at hB
    obtain rfl := Except.ok.inj hB
    exact ⟨A', hA, hs'⟩
  unfold sb_expose
  by_cases hw : (t == wildcardTag) = true
  · rw [if_pos hw]; exact ⟨_, rfl⟩
  · rw [if_neg hw]
    have hr : A.retired.contains t = false := by
      have := ht (by simpa using hw)
      simpa using this
    rw [if_neg (by rw [hr]; exact Bool.false_ne_true)]
    exact ⟨_, rfl⟩

theorem PermSub.popFrame_back {A B B' : AccessPerms} (hs : PermSub A B)
    (h : sb_pop_frame B = .ok B') : ∃ A', sb_pop_frame A = .ok A' ∧ PermSub A' B' := by
  suffices hA : ∃ A', sb_pop_frame A = .ok A' by
    obtain ⟨A', hA⟩ := hA
    obtain ⟨B'', hB, hs'⟩ := hs.popFrame hA
    rw [h] at hB
    obtain rfl := Except.ok.inj hB
    exact ⟨A', hA, hs'⟩
  unfold sb_pop_frame at h ⊢
  rw [hs.prot] at h
  split at h
  · cases h
  exact ⟨_, rfl⟩

end obseq3.proof
