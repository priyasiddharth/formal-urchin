import obseq3.proof.permsim_transport

/-!
# Die elision: one borrow stack with died items kept

OSEA-IR_B is OSEA-IR whose `Die` is a no-op (`PermissionModel.
stackedBorrowsNoDie`). After A (OSEA-IR) dies a tag, B still holds the
item: B's stack is A's with EXTRA items interleaved, each carrying a tag
that A retired and that is not protected. `StackSub E b sa sb` says `sb`
is `sa` with extras (tags satisfying `E`) interleaved; `b` records whether
the head of `sb` is an extra.

The one positional condition: an A-item directly above a block of extras
is not SharedReadWrite (`same`'s `hs`). That is what keeps an extra from
splitting an SRW run, so a write through an SRW item pops the same A-items
in both stacks (`srwSplit_sub`). It holds because extras only arise at
the top (a `Die` pops the top item), items are pushed only as non-SRW
(`MutRef`/`Ref`/`RawPtr false`), and SRW items are inserted directly above
an A-item.
-/

namespace obseq3.proof

open obseq3

/-- `sb` is `sa` with extra items (tags in `E`) interleaved; `b`: the head
    of `sb` is an extra. An A-item directly above an extra is not SRW. -/
inductive StackSub (E : Tag → Prop) : Bool → BorrowStack → BorrowStack → Prop
  | nil : StackSub E false [] []
  | same {b : Bool} {sa sb : BorrowStack} (i : Item) (h : StackSub E b sa sb)
      (hs : b = true → i.isSrw = false) : StackSub E false (i :: sa) (i :: sb)
  | extra {b : Bool} {sa sb : BorrowStack} (e : Item) (he : E e.tag)
      (h : StackSub E b sa sb) : StackSub E true sa (e :: sb)

namespace StackSub

variable {E : Tag → Prop}

theorem refl : ∀ (s : BorrowStack), StackSub E false s s
  | [] => .nil
  | i :: s => .same i (refl s) (by intro h; cases h)

theorem mem_left {b : Bool} {sa sb : BorrowStack} (h : StackSub E b sa sb) :
    ∀ {x : Item}, x ∈ sa → x ∈ sb := by
  induction h with
  | nil => intro x hx; exact hx
  | same i _ _ ih =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih hx)
  | extra e _ _ ih => intro x hx; exact List.mem_cons_of_mem _ (ih hx)

theorem mem_right {b : Bool} {sa sb : BorrowStack} (h : StackSub E b sa sb) :
    ∀ {x : Item}, x ∈ sb → x ∈ sa ∨ E x.tag := by
  induction h with
  | nil => intro x hx; exact Or.inl hx
  | same i _ _ ih =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Or.inl List.mem_cons_self
      · rcases ih hx with h | h
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · exact Or.inr h
  | extra e he _ ih =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Or.inr he
      · exact ih hx

theorem nil_right {b : Bool} {sa : BorrowStack} (h : StackSub E b sa []) : sa = [] ∧ b = false := by
  cases h; exact ⟨rfl, rfl⟩

/-- Weakening the extra predicate, needed only on the items present. -/
theorem mono_mem {E' : Tag → Prop} {b : Bool} {sa sb : BorrowStack}
    (h : StackSub E b sa sb) (hE : ∀ x ∈ sb, E x.tag → E' x.tag) : StackSub E' b sa sb := by
  induction h with
  | nil => exact .nil
  | same i _ hs ih =>
      exact .same i (ih fun x hx => hE x (List.mem_cons_of_mem _ hx)) hs
  | extra e he _ ih =>
      exact .extra e (hE e List.mem_cons_self he) (ih fun x hx => hE x (List.mem_cons_of_mem _ hx))

theorem mono {E' : Tag → Prop} {b : Bool} {sa sb : BorrowStack}
    (h : StackSub E b sa sb) (hE : ∀ t, E t → E' t) : StackSub E' b sa sb :=
  h.mono_mem fun x _ => hE x.tag

/-- Appending a tail whose head is an A-item (flag `false`). -/
theorem append {b1 : Bool} {xa xb ya yb : BorrowStack}
    (h1 : StackSub E b1 xa xb) (h2 : StackSub E false ya yb) :
    StackSub E b1 (xa ++ ya) (xb ++ yb) := by
  induction h1 with
  | nil => exact h2
  | same i _ hs ih => exact .same i ih hs
  | extra e he _ ih => exact .extra e he ih

/-- A block of extras on top. -/
theorem extras {b : Bool} {sa sb : BorrowStack} (Y : List Item) (hY : ∀ y ∈ Y, E y.tag)
    (h : StackSub E b sa sb) : ∃ b', StackSub E b' sa (Y ++ sb) := by
  induction Y with
  | nil => exact ⟨b, h⟩
  | cons y Y ih =>
      obtain ⟨b', h'⟩ := ih fun z hz => hY z (List.mem_cons_of_mem _ hz)
      exact ⟨true, .extra y (hY y List.mem_cons_self) h'⟩

/-- A block of A-items on top, none of them above an extra (the tail's
    head is an A-item). -/
theorem prefix_same {sa sb : BorrowStack} (l : List Item) (h : StackSub E false sa sb) :
    StackSub E false (l ++ sa) (l ++ sb) := by
  induction l with
  | nil => exact h
  | cons x l ih => exact .same x ih (by intro h; cases h)

/-- A tag-preserving, SRW-preserving map applied to both stacks. -/
theorem map {b : Bool} {sa sb : BorrowStack} (f : Item → Item)
    (hf : ∀ i, (f i).tag = i.tag ∧ (f i).isSrw = i.isSrw) (h : StackSub E b sa sb) :
    StackSub E b (sa.map f) (sb.map f) := by
  induction h with
  | nil => exact .nil
  | same i _ hs ih => exact .same (f i) ih (by rw [(hf i).2]; exact hs)
  | extra e he _ ih => exact .extra (f e) (by rw [(hf e).1]; exact he) ih

/-- No extras below an all-SRW A-stack whose head is not an extra: each
    extra block would sit directly under an SRW A-item. -/
theorem eq_of_all_srw {sa sb : BorrowStack} (h : StackSub E false sa sb)
    (hs : ∀ x ∈ sa, x.isSrw = true) : sb = sa := by
  generalize hb : false = b at h
  induction h with
  | nil => rfl
  | @same b' sa' sb' i h' hsc ih =>
      have hi := hs i List.mem_cons_self
      have hb' : b' = false := by
        cases b'
        · rfl
        · have := hsc rfl; rw [hi] at this; cases this
      subst hb'
      rw [ih (fun x hx => hs x (List.mem_cons_of_mem _ hx)) rfl]
  | extra => cases hb

end StackSub

/-! ## The SRW run of a write -/

/-- `(rest, run)`: `run` is the maximal all-SRW suffix of `l` (the items
    directly above the granting item, which a write through an SRW item
    keeps), `rest` the items above it, which the write pops. -/
def srwSplit : List Item → List Item × List Item
  | [] => ([], [])
  | x :: xs =>
      if (srwSplit xs).1.isEmpty && x.isSrw then ([], x :: (srwSplit xs).2)
      else (x :: (srwSplit xs).1, (srwSplit xs).2)

theorem srwSplit_append (l : List Item) : (srwSplit l).1 ++ (srwSplit l).2 = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      simp only [srwSplit]
      split
      · rename_i h
        simp only [Bool.and_eq_true, List.isEmpty_iff] at h
        have hx : (srwSplit xs).2 = xs := by
          have := ih; rw [h.1, List.nil_append] at this; exact this
        show [] ++ x :: (srwSplit xs).2 = x :: xs
        rw [hx, List.nil_append]
      · rw [List.cons_append, ih]

theorem srwSplit_run_srw (l : List Item) : ∀ x ∈ (srwSplit l).2, x.isSrw = true := by
  induction l with
  | nil => intro x hx; cases hx
  | cons y ys ih =>
      simp only [srwSplit]
      split
      · rename_i h
        simp only [Bool.and_eq_true] at h
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact h.2
        · exact ih x hx
      · exact ih

/-- The rest is empty or ends in a non-SRW item (the run is maximal). -/
theorem srwSplit_rest_last (l : List Item) :
    ∀ x, (srwSplit l).1.getLast? = some x → x.isSrw = false := by
  induction l with
  | nil => intro x h; cases h
  | cons y ys ih =>
      simp only [srwSplit]
      split
      · intro x h; cases h
      · rename_i h
        intro x hx
        cases hr : (srwSplit ys).1 with
        | nil =>
            rw [hr] at hx
            simp only [List.getLast?_singleton, Option.some.injEq] at hx
            subst hx
            simp only [hr, List.isEmpty_nil, Bool.true_and] at h
            simpa using h
        | cons r rs =>
            rw [hr] at hx
            have : (y :: r :: rs).getLast? = (r :: rs).getLast? := by
              simp [List.getLast?_cons_cons]
            rw [this] at hx
            exact ih x (by rw [hr]; exact hx)

/-- `writeCellContent`'s own split (`above.reverse.takeWhile isSrw`). -/
theorem srwSplit_eq (l : List Item) :
    srwSplit l = (l.take (l.length - (l.reverse.takeWhile Item.isSrw).length),
      (l.reverse.takeWhile Item.isSrw).reverse) := by
  -- characterise via `rest ++ run = l`, `run` all-SRW, `rest` not ending in SRW
  have h_app := srwSplit_append l
  have h_run := srwSplit_run_srw l
  have h_last := srwSplit_rest_last l
  generalize hr : (srwSplit l).1 = r at h_app h_last
  generalize hs : (srwSplit l).2 = s at h_app h_run
  subst h_app
  have h_tw : (r ++ s).reverse.takeWhile Item.isSrw = s.reverse := by
    rw [List.reverse_append, List.takeWhile_append_of_pos (fun x hx => by
      exact h_run x (List.mem_reverse.mp hx))]
    cases hrl : r.reverse with
    | nil => simp
    | cons z zs =>
        have hz : r.getLast? = some z := by
          rw [← List.head?_reverse, hrl]; rfl
        have := h_last z hz
        simp [List.takeWhile_cons, this]
  rw [Prod.ext_iff]
  refine ⟨?_, ?_⟩
  · show (srwSplit (r ++ s)).1 = _
    rw [hr, h_tw, List.length_reverse, List.length_append, Nat.add_sub_cancel,
      List.take_left' rfl]
  · show (srwSplit (r ++ s)).2 = _
    rw [hs, h_tw, List.reverse_reverse]

/-- A write through an SRW item, A against B: B's run is A's run with SRW
    extras on top; B's rest holds A's rest and extras. -/
theorem srwSplit_sub {E : Tag → Prop} {b : Bool} {xa xb : BorrowStack}
    (h : StackSub E b xa xb) :
    ∃ Y : List Item, (srwSplit xb).2 = Y ++ (srwSplit xa).2 ∧ (∀ y ∈ Y, E y.tag) ∧
      (∀ k ∈ (srwSplit xb).1, k ∈ (srwSplit xa).1 ∨ E k.tag) ∧
      (∀ k ∈ (srwSplit xa).1, k ∈ (srwSplit xb).1) := by
  induction h with
  | nil => exact ⟨[], rfl, by simp, by simp [srwSplit], by simp [srwSplit]⟩
  | @same b' sa sb i h' hsc ih =>
      obtain ⟨Y, hY, hYE, hRb, hRa⟩ := ih
      cases hi : i.isSrw with
      | false =>
          simp only [srwSplit, hi, Bool.and_false, Bool.false_eq_true, if_false]
          refine ⟨Y, hY, hYE, ?_, ?_⟩
          · intro k hk
            rcases List.mem_cons.mp hk with rfl | hk
            · exact Or.inl List.mem_cons_self
            · rcases hRb k hk with h | h
              · exact Or.inl (List.mem_cons_of_mem _ h)
              · exact Or.inr h
          · intro k hk
            rcases List.mem_cons.mp hk with rfl | hk
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ (hRa k hk)
      | true =>
          have hb' : b' = false := by
            cases b'
            · rfl
            · have := hsc rfl; rw [hi] at this; cases this
          subst hb'
          by_cases hra : (srwSplit sa).1 = []
          · -- A's whole `sa` is one SRW run: no extras at all below `i`
            have hall : ∀ x ∈ sa, x.isSrw = true := by
              intro x hx
              have := srwSplit_append sa
              rw [hra, List.nil_append] at this
              rw [← this] at hx
              exact srwSplit_run_srw sa x hx
            have heq := StackSub.eq_of_all_srw h' hall
            subst heq
            exact ⟨[], by simp, by simp, fun k hk => Or.inl hk, fun k hk => hk⟩
          · have hrb : (srwSplit sb).1 ≠ [] := by
              intro hrb
              obtain ⟨k, hk⟩ := List.exists_mem_of_ne_nil _ hra
              have := hRa k hk
              rw [hrb] at this; cases this
            have h1 : ((srwSplit sa).1.isEmpty && i.isSrw) = false := by
              simp [List.isEmpty_iff, hra]
            have h2 : ((srwSplit sb).1.isEmpty && i.isSrw) = false := by
              simp [List.isEmpty_iff, hrb]
            simp only [srwSplit, h1, h2, Bool.false_eq_true, if_false]
            refine ⟨Y, hY, hYE, ?_, ?_⟩
            · intro k hk
              rcases List.mem_cons.mp hk with rfl | hk
              · exact Or.inl List.mem_cons_self
              · rcases hRb k hk with h | h
                · exact Or.inl (List.mem_cons_of_mem _ h)
                · exact Or.inr h
            · intro k hk
              rcases List.mem_cons.mp hk with rfl | hk
              · exact List.mem_cons_self
              · exact List.mem_cons_of_mem _ (hRa k hk)
  | @extra b' sa sb e he h' ih =>
      obtain ⟨Y, hY, hYE, hRb, hRa⟩ := ih
      by_cases hc : ((srwSplit sb).1.isEmpty && e.isSrw) = true
      · simp only [srwSplit, hc, if_true]
        have hrb : (srwSplit sb).1 = [] := by
          simp only [Bool.and_eq_true, List.isEmpty_iff] at hc; exact hc.1
        refine ⟨e :: Y, by rw [hY]; rfl, ?_, by simp, ?_⟩
        · intro y hy
          rcases List.mem_cons.mp hy with rfl | hy
          · exact he
          · exact hYE y hy
        · intro k hk
          have := hRa k hk
          rw [hrb] at this; cases this
      · simp only [srwSplit, Bool.not_eq_true] at hc ⊢
        simp only [hc, Bool.false_eq_true, if_false]
        refine ⟨Y, hY, hYE, ?_, ?_⟩
        · intro k hk
          rcases List.mem_cons.mp hk with rfl | hk
          · exact Or.inr he
          · exact hRb k hk
        · intro k hk
          exact List.mem_cons_of_mem _ (hRa k hk)

/-! ## Splitting at a tag -/

theorem splitStack_some_eq {l : BorrowStack} {t : Tag} {a : BorrowStack} {x : Item}
    {bl : BorrowStack} (h : splitStack l t = some (a, x, bl)) :
    l = a ++ x :: bl ∧ x.tag = t := by
  induction l generalizing a with
  | nil => simp [splitStack] at h
  | cons y ys ih =>
      simp only [splitStack] at h
      split at h
      · rename_i hy
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨rfl, by simpa using hy⟩
      · split at h
        · rename_i ab fd bw h'
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          obtain ⟨h1, h2⟩ := ih h'
          exact ⟨by rw [h1]; rfl, h2⟩
        · cases h

/-- Splitting B at an A-item's tag finds the same item; the parts above
    and below are related (extras have other tags: B's tags are distinct). -/
theorem splitStack_sub {E : Tag → Prop} {b : Bool} {sa sb : BorrowStack} {t : Tag}
    (h : StackSub E b sa sb) (hnd : (sb.map Item.tag).Nodup)
    {aa : BorrowStack} {it : Item} {ba : BorrowStack}
    (hs : splitStack sa t = some (aa, it, ba)) :
    ∃ ab bb, splitStack sb t = some (ab, it, bb) ∧
      (∃ b1, StackSub E b1 aa ab ∧ (ab ≠ [] → b1 = b)) ∧
      (∃ b2, StackSub E b2 ba bb ∧ (b2 = true → it.isSrw = false)) := by
  induction h generalizing aa with
  | nil => simp [splitStack] at hs
  | @same b' sa' sb' i h' hsc ih =>
      simp only [splitStack] at hs ⊢
      split at hs
      · rename_i hi
        simp only [Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨rfl, rfl, rfl⟩ := hs
        rw [if_pos hi]
        exact ⟨[], sb', rfl, ⟨false, .nil, fun h => absurd rfl h⟩, ⟨b', h', hsc⟩⟩
      · rename_i hi
        rw [if_neg hi]
        split at hs
        · rename_i ab0 fd bw h_sp
          simp only [Option.some.injEq, Prod.mk.injEq] at hs
          obtain ⟨rfl, rfl, rfl⟩ := hs
          have hnd' : (sb'.map Item.tag).Nodup := (List.nodup_cons.mp hnd).2
          obtain ⟨ab, bb, h_spb, ⟨b1, hab, hfl⟩, hbb⟩ := ih hnd' h_sp
          rw [h_spb]
          refine ⟨i :: ab, bb, rfl, ⟨false, .same i hab ?_, fun _ => rfl⟩, hbb⟩
          -- the flag of `ab` is the flag of `sb'` when `ab` is not empty
          intro hb1
          by_cases hab0 : ab = []
          · subst hab0
            have := (StackSub.nil_right hab).2
            rw [hb1] at this; cases this
          · exact hsc (by rw [← hfl hab0]; exact hb1)
        · cases hs
  | @extra b' sa' sb' e he h' ih =>
      have hnd' : (sb'.map Item.tag).Nodup := (List.nodup_cons.mp hnd).2
      obtain ⟨ab, bb, h_spb, ⟨b1, hab, -⟩, hbb⟩ := ih hnd' hs
      have h_it : it ∈ sb' := by
        have := (splitStack_some_eq hs).1
        exact h'.mem_left (by rw [this]; simp)
      have h_ne : (e.tag == t) = false := by
        have h_et : e.tag ∉ sb'.map Item.tag := (List.nodup_cons.mp hnd).1
        have h_tag := (splitStack_some_eq hs).2
        cases hc : e.tag == t
        · rfl
        · have : e.tag = t := by simpa using hc
          exact absurd (List.mem_map.mpr ⟨it, h_it, by rw [h_tag, this]⟩) h_et
      simp only [splitStack, h_ne, Bool.false_eq_true, if_false, h_spb]
      exact ⟨e :: ab, bb, rfl, ⟨true, .extra e he hab, fun _ => rfl⟩, hbb⟩

end obseq3.proof
