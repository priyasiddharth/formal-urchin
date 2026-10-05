import obseq3.proof.die_back_ops

/-!
# Die elision, backward: inside a route bracket

The three facts about A's stacks a route bracket needs: the route borrow
leaves its item on top of every byte of its range (`sb_ref_push_top`); an
access through that top item leaves the stack as it is
(`sb_read_keeps_top`, `sb_write_keeps_top`); and a `Die` of an
unexposed, unprotected tag that is on top of every byte succeeds
(`sb_die_of_top`).
-/

namespace obseq3.proof

open obseq3 obseq3.bytes obseq3.oseair

/-- The top item of a byte's stack, as a route bracket keeps it. -/
def TopIs (A : AccessPerms) (c : Word) (t : Tag) : Prop :=
  ∃ it rest, SB.find? A.StackMap c = some (it :: rest) ∧ it.tag = t ∧
    (∀ t0, it ≠ .Own t0) ∧ (∀ t0, it ≠ .Disabled t0)

theorem splitStack_head {it : Item} {rest : BorrowStack} {t : Tag} (h : it.tag = t) :
    splitStack (it :: rest) t = some ([], it, rest) := by
  simp [splitStack, h]

/-- A push-kind route retag leaves its item, tagged with the counter, on
    top of every byte of its range. -/
theorem sb_ref_push_top {A A' : AccessPerms} {addr : Word} {n : Nat} {t : Tag}
    {k : RefKind} {u : Tag} (hk : PushKind k)
    (h : sb_ref A addr n t k false [] = .ok (A', u)) :
    ∀ j < n, TopIs A' (addr + j) A.NextTag := by
  rw [sb_ref_eq] at h
  split at h
  · cases h
  rename_i apR hgo
  obtain ⟨W, h_cells, rfl⟩ :=
    foldCellsIdx_ok_inv
      (op := refCellOp t k A.NextTag [])
      (C := fun j v? => refCellStep A.protFrames A.exposed (addr + j) t k A.NextTag [] j v?)
      (P := A.protFrames) (E := A.exposed) (N := A.NextTag + 1)
      (refCellOp_content_form (addr := addr) t k A.NextTag [])
      { A with NextTag := A.NextTag + 1 } _ rfl rfl rfl hgo
  simp only [regProt, Bool.false_eq_true, if_false, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  intro j hj
  have hf : SB.find? (setChain A.StackMap (chain W addr 0 n)) (addr + j) = some (W j) :=
    setChain_chain_find? _ j (Nat.zero_le j) hj
  obtain ⟨v, -, hc⟩ := refCellStep_ok_inv (h_cells j (Nat.zero_le j) hj)
  -- the pushed item
  have push : ∀ (x : Item) (acc : Except String BorrowStack),
      (match acc with | .error e => .error e | .ok v => .ok (x :: v)) = Except.ok (W j) →
      ∃ v', W j = x :: v' := by
    intro x acc ha
    split at ha
    · cases ha
    · exact ⟨_, (Except.ok.inj ha).symm⟩
  have hgetD : ([] : List Bool).getD j false = false := rfl
  obtain ⟨x, hx, hxo, hxd, v', hW⟩ : ∃ x : Item, x.tag = A.NextTag ∧ (∀ t0, x ≠ .Own t0) ∧
      (∀ t0, x ≠ .Disabled t0) ∧ ∃ v', W j = x :: v' := by
    cases k with
    | Mut =>
        simp only [refCellContent] at hc
        exact ⟨_, rfl, by simp, by simp, push _ _ hc⟩
    | BoxMut =>
        simp only [refCellContent] at hc
        exact ⟨_, rfl, by simp, by simp, push _ _ hc⟩
    | Shared =>
        simp only [refCellContent, hgetD, Bool.false_eq_true, if_false] at hc
        exact ⟨_, rfl, by simp, by simp, push _ _ hc⟩
    | Raw m =>
        cases m with
        | false =>
            simp only [refCellContent, hgetD, Bool.false_eq_true, if_false] at hc
            exact ⟨_, rfl, by simp, by simp, push _ _ hc⟩
        | true => exact hk.elim
    | TwoPhase => exact hk.elim
  exact ⟨x, v', by rw [hf, hW], hx, hxo, hxd⟩

/-- A read through the top item of a byte leaves its stack. -/
theorem readCellContent_top {pf : List (List Tag)} {ex : List Tag} {a : Word} {t : Tag}
    {it : Item} {rest w : BorrowStack} (ht0 : t ≠ wildcardTag) (ht : it.tag = t)
    (h : readCellContent pf ex a t (it :: rest) = .ok w) : w = it :: rest := by
  rw [readCellContent_nonwild (by simpa using ht0)] at h
  obtain ⟨aa, it', ba, hsp, -, -, rfl⟩ := readCellContentR_ok h
  rw [splitStack_head ht] at hsp
  simp only [Option.some.injEq, Prod.mk.injEq] at hsp
  obtain ⟨rfl, rfl, rfl⟩ := hsp
  rfl

theorem writeCellContent_top {pf : List (List Tag)} {ex : List Tag} {a : Word} {t : Tag}
    {it : Item} {rest w : BorrowStack} (ht0 : t ≠ wildcardTag) (ht : it.tag = t)
    (h : writeCellContent pf ex a t (it :: rest) = .ok w) : w = it :: rest := by
  rw [writeCellContent_nonwild (by simpa using ht0)] at h
  obtain ⟨aa, it', ba, hsp, -, -, rfl⟩ := writeCellContentR_ok h
  rw [splitStack_head ht] at hsp
  simp only [Option.some.injEq, Prod.mk.injEq] at hsp
  obtain ⟨rfl, rfl, rfl⟩ := hsp
  cases it.isSrw <;> rfl

/-- A content-driven fold leaves a byte whose step is the identity. -/
theorem foldCells_keeps
    {op : AccessPerms → Word → Except String AccessPerms}
    {C : Word → BorrowStack → Except String BorrowStack} {msgNone : Word → String}
    {A A' : AccessPerms} {addr : Word} {lenB : Nat}
    (h_op : ∀ ap a, ap.protFrames = A.protFrames → ap.exposed = A.exposed →
      ap.NextTag = A.NextTag →
      op ap a =
        match SB.find? ap.StackMap a with
        | none => .error (msgNone a)
        | some stack =>
          match C a stack with
          | .error e => .error e
          | .ok v => .ok { ap with StackMap := SB.set ap.StackMap a v })
    (h : foldCells op A addr lenB = .ok A') {c : Word} {s : BorrowStack}
    (hc : SB.find? A.StackMap c = some s) (hid : ∀ w, C c s = .ok w → w = s) :
    SB.find? A'.StackMap c = some s := by
  have h0 : foldCells op A (addr + 0) lenB = .ok A' := h
  obtain ⟨V, W, h_cells, rfl⟩ := foldCells_ok_inv (C := C) (msgNone := msgNone) h_op lenB 0 A A'
    rfl rfl rfl h0
  show SB.find? (setChain A.StackMap (chain W addr 0 (0 + lenB))) c = some s
  by_cases hm : c ∈ keysOf (chain W addr 0 (0 + lenB))
  · obtain ⟨j, h1, h2, rfl⟩ := mem_keysOf_chain hm
    rw [setChain_chain_find? _ j h1 h2]
    obtain ⟨hf, hw⟩ := h_cells j h1 h2
    rw [hc] at hf
    obtain rfl := Option.some.inj hf
    rw [hid _ hw]
  · rw [setChain_find?_not_mem _ _ hm]; exact hc

theorem sb_read_keeps_top {A A' : AccessPerms} {addr : Word} {lenB : Nat} {t : Tag}
    (h : sb_read A addr lenB t = .ok A') (ht0 : t ≠ wildcardTag) {c : Word}
    (hc : TopIs A c t) : TopIs A' c t := by
  obtain ⟨it, rest, hf, ht, ho, hd⟩ := hc
  exact ⟨it, rest, foldCells_keeps
    (C := fun a stack => readCellContent A.protFrames A.exposed a t stack)
    (fun ap a h_pf h_ex _ => readCell_content_form t ap a h_pf h_ex) h hf
    (fun w hw => readCellContent_top ht0 ht hw), ht, ho, hd⟩

theorem sb_write_keeps_top {A A' : AccessPerms} {addr : Word} {lenB : Nat} {t : Tag}
    (h : sb_write A addr lenB t = .ok A') (ht0 : t ≠ wildcardTag) {c : Word}
    (hc : TopIs A c t) : TopIs A' c t := by
  obtain ⟨it, rest, hf, ht, ho, hd⟩ := hc
  exact ⟨it, rest, foldCells_keeps
    (C := fun a stack => writeCellContent A.protFrames A.exposed a t stack)
    (fun ap a h_pf h_ex _ => writeCell_content_form t ap a h_pf h_ex) h hf
    (fun w hw => writeCellContent_top ht0 ht hw), ht, ho, hd⟩

theorem dieCellContent_route_top {pf : List (List Tag)} {t : Tag} {it : Item} {rest : BorrowStack}
    (ht : it.tag = t) (ho : ∀ t0, it ≠ .Own t0) (hp : isProtectedIn pf t = false) :
    dieCellContent pf t (it :: rest) = .ok rest := by
  subst ht
  cases it with
  | Own t0 => exact absurd rfl (ho t0)
  | _ => simp only [Item.tag] at hp; simp [dieCellContent, Item.tag, hp]

/-- A's `Die` of a route tag on top of every byte of its range. -/
theorem sb_die_of_top {A : AccessPerms} {addr : Word} {n : Nat} {t : Tag}
    (hex : A.exposed.contains t = false) (hp : isProtectedIn A.protFrames t = false)
    (htop : ∀ j < n, TopIs A (addr + j) t) :
    ∃ A', sb_die A addr n t = .ok A' := by
  have h_pkg : ∀ j, ∃ v, ∃ w, j < n →
      SB.find? A.StackMap (addr + j) = some v ∧ dieCellContent A.protFrames t v = .ok w := by
    intro j
    by_cases hj : j < n
    · obtain ⟨it, rest, hf, ht, ho, -⟩ := htop j hj
      exact ⟨_, _, fun _ => ⟨hf, dieCellContent_route_top ht ho hp⟩⟩
    · exact ⟨[], [], fun h => absurd h hj⟩
  have hf := foldCells_ok_of_cells
    (op := dieCellOp t)
    (C := fun _ stack => dieCellContent A.protFrames t stack)
    (msgNone := fun a => s!"sb-die: no borrow stack at address {a}")
    (P := A.protFrames) (E := A.exposed) (N := A.NextTag)
    (fun ap a h_pf h_ex _ => die_content_form t ap a h_pf h_ex)
    n 0 A (fun j => (h_pkg j).choose) (fun j => (h_pkg j).choose_spec.choose) rfl rfl rfl
    (fun j _ h2 => ((h_pkg j).choose_spec.choose_spec (by omega)).1)
    (fun j _ h2 => ((h_pkg j).choose_spec.choose_spec (by omega)).2)
  exact ⟨_, sb_die_ok_of_fold hex hf⟩

/-- `sb_die`'s result: the stacks only change, and the tag is retired. -/
theorem sb_die_fields {A A' : AccessPerms} {addr : Word} {n : Nat} {t : Tag}
    (h : sb_die A addr n t = .ok A') :
    ∃ sm, A' = { A with StackMap := sm, retired := t :: A.retired } := by
  obtain ⟨-, q, hf, rfl⟩ := sb_die_ok_inv h
  have h0 : foldCells (dieCellOp t) A (addr + 0) n = .ok q := hf
  obtain ⟨V, W, -, rfl⟩ :=
    foldCells_ok_inv (C := fun _ stack => dieCellContent A.protFrames t stack)
      (msgNone := fun a => s!"sb-die: no borrow stack at address {a}")
      (P := A.protFrames) (E := A.exposed) (N := A.NextTag)
      (fun ap a h_pf h_ex _ => die_content_form t ap a h_pf h_ex)
      n 0 A q rfl rfl rfl h0
  exact ⟨_, rfl⟩

end obseq3.proof
