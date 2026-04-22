namespace obseq

abbrev Word := Nat
abbrev Tag := Nat

inductive RefKind
| Own (tag: Tag)
| MutRef (tag: Tag)
| Ref (tag: Tag)
| RawPtr (tag: Tag)
deriving Inhabited, Repr, BEq

inductive RefOpKind
| Shared
| Mut
| Raw
deriving Inhabited, Repr, BEq

def RefKind.tag : RefKind → Tag
| Own t => t
| MutRef t => t
| Ref t => t
| RawPtr t => t

def RefKind.isMb : RefKind → Bool
| MutRef _ => true
| _ => false

def RefKind.isRaw : RefKind → Bool
| RawPtr _ => true
| _ => false

def RefOpKind.toStackKind : RefOpKind → Tag → RefKind
| RefOpKind.Shared => RefKind.Ref
| RefOpKind.Mut => RefKind.MutRef
| RefOpKind.Raw => RefKind.RawPtr

abbrev BorrowStack := List RefKind

/--
A StackedMap (SB) maps a memory location (Addr) to a borrow stack.
--/
abbrev SB := List (Word × BorrowStack)

def SB.find? (sb : SB) (addr : Word) : Option BorrowStack :=
  match sb with
  | [] => none
  | (a, stack) :: rest => if a == addr then some stack else SB.find? rest addr

/--
Insert one `(address, stack)` entry into an `SB`, keeping the list ordered by
address.

This is a raw insertion helper: it does not remove an existing entry for the
same address. `SB.insert` handles replacement by filtering first.
-/
def SB.insortEntry (entry : Word × BorrowStack) : SB → SB
  | [] => [entry]
  | head :: rest =>
      if entry.1 <= head.1 then entry :: head :: rest
      else head :: SB.insortEntry entry rest

/--
Rebuild an `SB` by repeatedly reinserting entries with `SB.insortEntry`.

Operationally this is a simple normalization pass used after filtering, and the
lemmas below show that it preserves membership.
-/
def SB.normalize : SB → SB
  | [] => []
  | entry :: rest => SB.insortEntry entry (SB.normalize rest)

def SB.insert (sb : SB) (addr : Word) (stack : BorrowStack) : SB :=
  SB.insortEntry (addr, stack) (SB.normalize (sb.filter (fun (a, _) => a != addr)))

structure AccessPerms where
  StackMap: SB
  NextTag: Tag
deriving Inhabited, Repr, BEq

def StackTagsUnique (stack : BorrowStack) : Prop :=
  ∀ ⦃k₁ k₂ : RefKind⦄, k₁ ∈ stack → k₂ ∈ stack → k₁.tag = k₂.tag → k₁ = k₂

def SBAddrsUnique (sb : SB) : Prop :=
  ∀ ⦃addr : Word⦄ ⦃stack₁ stack₂ : BorrowStack⦄,
    (addr, stack₁) ∈ sb → (addr, stack₂) ∈ sb → stack₁ = stack₂

/--
`SBValid` is the minimal structural well-formedness invariant used by the local
`obseq` preservation proofs.

- stack-map addresses are unique,
- tags are unique within each per-address borrow stack.

Freshness of `NextTag` is intentionally treated separately from this structural
invariant.
-/
def SBValid (ap : AccessPerms) : Prop :=
  SBAddrsUnique ap.StackMap ∧
  ∀ ⦃addr : Word⦄ ⦃stack : BorrowStack⦄,
    (addr, stack) ∈ ap.StackMap →
      StackTagsUnique stack

def freshTag (ap : AccessPerms) : Tag × AccessPerms :=
  (ap.NextTag, { ap with NextTag := ap.NextTag + 1 })

inductive SBResult
| Ok (ap : AccessPerms)
| Err (msg : String)
deriving Inhabited, Repr

open SBResult

-- Rule: sb-own
-- Premise: sb[a] = [], g is fresh
-- Conclusion: sb[a] = [(g, o)]
def sb_own (ap : AccessPerms) (addr : Word) : SBResult × Tag :=
  match ap.StackMap.find? addr with
  | some [] | none => -- Treat none as empty for initialization or explicit empty check?
    -- Paper says sb[a] = [], but in implementation usually we allocate and init.
    -- Assuming alloc calls this.
    let (tag, ap') := freshTag ap
    let stack := [RefKind.Own tag]
    let newSB := ap'.StackMap.insert addr stack
    (Ok { ap' with StackMap := newSB }, tag)
  | some _ => (Err s!"sb-own: stack at {addr} not empty", 0)

theorem sb_own_tag_eq_nextTag
  {ap ap' : AccessPerms}
  {addr tag : Word}
  (h_own : sb_own ap addr = (SBResult.Ok ap', tag)) :
  tag = ap.NextTag := by
  unfold sb_own at h_own
  cases h_find : ap.StackMap.find? addr with
  | none =>
      rw [h_find] at h_own
      unfold freshTag at h_own
      injection h_own with h_ok h_tag
      cases h_ok
      exact h_tag.symm
  | some stack =>
      cases stack with
      | nil =>
          rw [h_find] at h_own
          unfold freshTag at h_own
          injection h_own with h_ok h_tag
          cases h_ok
          exact h_tag.symm
      | cons item rest =>
          simp [h_find] at h_own

theorem sb_own_nextTag_succ
  {ap ap' : AccessPerms}
  {addr tag : Word}
  (h_own : sb_own ap addr = (SBResult.Ok ap', tag)) :
  ap'.NextTag = ap.NextTag + 1 := by
  unfold sb_own at h_own
  cases h_find : ap.StackMap.find? addr with
  | none =>
      rw [h_find] at h_own
      unfold freshTag at h_own
      injection h_own with h_ok _h_tag
      cases h_ok
      rfl
  | some stack =>
      cases stack with
      | nil =>
          rw [h_find] at h_own
          unfold freshTag at h_own
          injection h_own with h_ok _h_tag
          cases h_ok
          rfl
      | cons item rest =>
          simp [h_find] at h_own

-- Helper to find item in stack and split it: returns (above, item, below)
def splitStack (stack : BorrowStack) (tag : Tag) : Option (BorrowStack × RefKind × BorrowStack) :=
  match stack with
  | [] => none
  | item :: rest =>
    if item.tag == tag then
      some ([], item, rest)
    else
      match splitStack rest tag with
      | some (x, found, y) => some (item :: x, found, y)
      | none => none

theorem splitStack_result_mem
  {stack : BorrowStack} {tag : Tag} {x : BorrowStack} {item : RefKind} {y : BorrowStack} {k : RefKind}
  (h : splitStack stack tag = some (x, item, y))
  (hk : k ∈ item :: y) :
  k ∈ stack := by
  induction stack generalizing x item y k with
  | nil =>
      simp [splitStack] at h
  | cons head tail ih =>
      by_cases h_head : head.tag == tag
      · simp [splitStack, h_head] at h
        cases h with
        | intro hx h_rest =>
            cases h_rest with
            | intro h_item h_y =>
                subst x
                subst item
                subst y
                exact hk
      · cases h_tail : splitStack tail tag with
        | none =>
            simp [splitStack, h_head, h_tail] at h
        | some triple =>
            cases triple with
            | mk x' rest =>
                cases rest with
                | mk item' y' =>
                    simp [splitStack, h_head, h_tail] at h
                    cases h with
                    | intro hx h_rest =>
                        cases h_rest with
                        | intro h_item h_y =>
                subst x
                subst item
                subst y
                have h_mem_tail : k ∈ tail := ih h_tail hk
                exact List.Mem.tail _ h_mem_tail

theorem splitStack_eq_append
  {stack : BorrowStack} {tag : Tag} {x : BorrowStack} {item : RefKind} {y : BorrowStack}
  (h : splitStack stack tag = some (x, item, y)) :
  stack = x ++ item :: y := by
  induction stack generalizing x item y with
  | nil =>
      simp [splitStack] at h
  | cons head tail ih =>
      by_cases h_head : head.tag == tag
      · simp [splitStack, h_head] at h
        cases h with
        | intro h_x h_rest =>
            cases h_rest with
            | intro h_item h_y =>
                subst x
                subst item
                subst y
                simp
      · cases h_tail : splitStack tail tag with
        | none =>
            simp [splitStack, h_head, h_tail] at h
        | some triple =>
            cases triple with
            | mk x' rest =>
                cases rest with
                | mk item' y' =>
                    simp [splitStack, h_head, h_tail] at h
                    cases h with
                    | intro h_x h_rest =>
                        cases h_rest with
                        | intro h_item h_y =>
                            subst x
                            subst item
                            subst y
                            simp [ih h_tail]

theorem splitStack_found_tag
  {stack : BorrowStack} {tag : Tag} {x : BorrowStack} {item : RefKind} {y : BorrowStack}
  (h : splitStack stack tag = some (x, item, y)) :
  item.tag = tag := by
  induction stack generalizing x item y with
  | nil =>
      simp [splitStack] at h
  | cons head tail ih =>
      by_cases h_head : head.tag == tag
      · have h' : some ([], head, tail) = some (x, item, y) := by
          simpa [splitStack, h_head] using h
        cases h'
        simpa using h_head
      · cases h_tail : splitStack tail tag with
        | none =>
            simp [splitStack, h_head, h_tail] at h
        | some triple =>
            rcases triple with ⟨x', item', y'⟩
            have h' : some (head :: x', item', y') = some (x, item, y) := by
              simpa [splitStack, h_head, h_tail] using h
            cases h'
            exact ih h_tail

theorem SB.find?_some_mem
  {sb : SB} {addr : Word} {stack : BorrowStack}
  (h : SB.find? sb addr = some stack) :
  (addr, stack) ∈ sb := by
  induction sb with
  | nil =>
      simp [SB.find?] at h
  | cons entry rest ih =>
      cases entry with
      | mk a s =>
          by_cases h_eq : a = addr
          · subst h_eq
            simp [SB.find?] at h
            cases h
            exact List.Mem.head _
          · simp [SB.find?, h_eq] at h
            have h_mem_rest : (addr, stack) ∈ rest := ih h
            exact List.Mem.tail _ h_mem_rest

theorem mem_filter_mem_prop
  {α : Type} {p : α → Bool} {x : α} {xs : List α}
  (h : x ∈ xs.filter p) :
  x ∈ xs ∧ p x = true := by
  simpa using List.mem_filter.mp h

theorem mem_of_mem_append
  {α : Type} {x : α} {xs ys : List α}
  (h : x ∈ xs ++ ys) :
  x ∈ xs ∨ x ∈ ys := by
  exact List.mem_append.mp h

theorem mem_filter_of_mem
  {α : Type} {p : α → Bool} {x : α} {xs : List α}
  (h_mem : x ∈ xs)
  (h_prop : p x = true) :
  x ∈ xs.filter p := by
  exact List.mem_filter.mpr ⟨h_mem, by simpa using h_prop⟩

theorem SB.mem_insortEntry
  {entry item : Word × BorrowStack} {sb : SB} :
  item ∈ SB.insortEntry entry sb ↔ item = entry ∨ item ∈ sb := by
  induction sb with
  | nil =>
      simp [SB.insortEntry]
  | cons head rest ih =>
      by_cases h_le : entry.1 <= head.1
      · simp [SB.insortEntry, h_le, List.mem_cons]
      · simp [SB.insortEntry, h_le, List.mem_cons, ih, or_left_comm]

theorem SB.mem_normalize
  {item : Word × BorrowStack} {sb : SB} :
  item ∈ SB.normalize sb ↔ item ∈ sb := by
  induction sb with
  | nil =>
      simp [SB.normalize]
  | cons head rest ih =>
      simpa [SB.normalize, List.mem_cons, ih] using
        (SB.mem_insortEntry (entry := head) (item := item) (sb := SB.normalize rest))

theorem SB.find?_none_of_not_mem
  {sb : SB} {addr : Word}
  (h_absent : ∀ stack, (addr, stack) ∉ sb) :
  SB.find? sb addr = none := by
  induction sb with
  | nil =>
      rfl
  | cons entry rest ih =>
      cases entry with
      | mk a stack =>
          have h_head_absent : (addr, stack) ∉ (a, stack) :: rest := h_absent stack
          by_cases h_eq : a = addr
          · subst h_eq
            cases (h_head_absent (List.Mem.head _))
          · simp [SB.find?, h_eq]
            apply ih
            intro stack' h_mem
            exact h_absent stack' (List.Mem.tail _ h_mem)

theorem SB.find?_insortEntry_eq_of_absent
  {sb : SB} {addr : Word} {stack : BorrowStack}
  (h_absent : SB.find? sb addr = none) :
  SB.find? (SB.insortEntry (addr, stack) sb) addr = some stack := by
  induction sb with
  | nil =>
      simp [SB.insortEntry, SB.find?]
  | cons entry rest ih =>
      cases entry with
      | mk a stack' =>
          by_cases h_le : addr <= a
          · simp [SB.insortEntry, h_le, SB.find?]
          · have h_ne : a ≠ addr := by
              intro h_eq
              subst h_eq
              exact h_le (Nat.le_refl _)
            simp [SB.insortEntry, h_le, SB.find?, h_ne]
            have h_absent_rest : SB.find? rest addr = none := by
              simp [SB.find?, h_ne] at h_absent
              exact h_absent
            apply ih
            exact h_absent_rest

@[simp] theorem SB.find?_insert_eq
  (sb : SB) (addr : Word) (stack : BorrowStack) :
  SB.find? (SB.insert sb addr stack) addr = some stack := by
  unfold SB.insert
  apply SB.find?_insortEntry_eq_of_absent
  apply SB.find?_none_of_not_mem
  intro stack' h_mem
  have h_filter_mem : (addr, stack') ∈ sb.filter (fun (a, _) => a != addr) := by
    exact (SB.mem_normalize).1 h_mem
  have h_props := mem_filter_mem_prop h_filter_mem
  cases h_props with
  | intro _ h_prop =>
      simp at h_prop

theorem SB.mem_insert_of_mem_ne
  {sb : SB} {addr a : Word} {newStack stack : BorrowStack}
  (h_mem : (a, stack) ∈ sb)
  (h_ne : a ≠ addr) :
  (a, stack) ∈ SB.insert sb addr newStack := by
  unfold SB.insert
  apply (SB.mem_insortEntry).2
  apply Or.inr
  apply (SB.mem_normalize).2
  apply mem_filter_of_mem h_mem
  simp [h_ne]

theorem SB.mem_insert_cases
  {sb : SB} {addr a : Word} {newStack stack : BorrowStack}
  (h_mem : (a, stack) ∈ SB.insert sb addr newStack) :
  (a = addr ∧ stack = newStack) ∨ ((a, stack) ∈ sb ∧ a ≠ addr) := by
  unfold SB.insert at h_mem
  have h_mem' := (SB.mem_insortEntry).1 h_mem
  cases h_mem' with
  | inl h_eq =>
      cases h_eq
      exact Or.inl ⟨rfl, rfl⟩
  | inr h_old =>
      have h_old_filter := (SB.mem_normalize).1 h_old
      have h_props := mem_filter_mem_prop h_old_filter
      cases h_props with
      | intro h_in_sb h_prop =>
          have h_ne : a ≠ addr := by
            intro h_eq
            subst h_eq
            simp at h_prop
          exact Or.inr ⟨h_in_sb, h_ne⟩

theorem SB.find?_of_mem_unique
  {sb : SB} {addr : Word} {stack : BorrowStack}
  (h_unique : SBAddrsUnique sb)
  (h_mem : (addr, stack) ∈ sb) :
  SB.find? sb addr = some stack := by
  induction sb with
  | nil =>
      cases h_mem
  | cons entry rest ih =>
      cases entry with
      | mk a stack0 =>
          by_cases h_eq : a = addr
          · subst h_eq
            cases h_mem with
            | head =>
                simp [SB.find?]
            | tail _ h_tail =>
                have h_same : stack0 = stack := by
                  exact h_unique (List.Mem.head _) (List.Mem.tail _ h_tail)
                simp [SB.find?, h_same]
          · simp [SB.find?, h_eq]
            cases h_mem with
            | head =>
                cases (h_eq rfl)
            | tail _ h_tail =>
                apply ih
                · intro addr' stack₁ stack₂ h₁ h₂
                  exact h_unique (List.Mem.tail _ h₁) (List.Mem.tail _ h₂)
                · exact h_tail

theorem SBAddrsUnique_insert
  {sb : SB} {addr : Word} {stack : BorrowStack}
  (h_unique : SBAddrsUnique sb) :
  SBAddrsUnique (SB.insert sb addr stack) := by
  intro a stack₁ stack₂ h₁ h₂
  have h₁_cases := SB.mem_insert_cases h₁
  have h₂_cases := SB.mem_insert_cases h₂
  cases h₁_cases with
  | inl h_new₁ =>
      cases h_new₁ with
      | intro h_addr₁ h_stack₁ =>
          subst h_addr₁
          subst h_stack₁
          cases h₂_cases with
          | inl h_new₂ =>
              exact h_new₂.2.symm
          | inr h_old₂ =>
              exact False.elim (h_old₂.2 rfl)
  | inr h_old₁ =>
      cases h₂_cases with
      | inl h_new₂ =>
          exact False.elim (h_old₁.2 h_new₂.1)
      | inr h_old₂ =>
          exact h_unique h_old₁.1 h_old₂.1

theorem SB.find?_insert_ne
  {sb : SB} {addr addr' : Word} {stack : BorrowStack}
  (h_unique : SBAddrsUnique sb)
  (h_ne : addr' ≠ addr) :
  SB.find? (SB.insert sb addr stack) addr' = SB.find? sb addr' := by
  cases h_old : SB.find? sb addr' with
  | none =>
      cases h_new : SB.find? (SB.insert sb addr stack) addr' with
      | none =>
          rfl
      | some stack' =>
          have h_mem_new : (addr', stack') ∈ SB.insert sb addr stack :=
            SB.find?_some_mem h_new
          have h_cases := SB.mem_insert_cases h_mem_new
          cases h_cases with
          | inl h_eq =>
              exact False.elim (h_ne h_eq.1)
          | inr h_old_mem =>
              have h_old_some : SB.find? sb addr' = some stack' :=
                SB.find?_of_mem_unique h_unique h_old_mem.1
              rw [h_old] at h_old_some
              cases h_old_some
  | some stack' =>
      have h_mem_old : (addr', stack') ∈ sb :=
        SB.find?_some_mem h_old
      have h_mem_new : (addr', stack') ∈ SB.insert sb addr stack :=
        SB.mem_insert_of_mem_ne h_mem_old h_ne
      have h_new_eq : SB.find? (SB.insert sb addr stack) addr' = some stack' :=
        SB.find?_of_mem_unique (sb := SB.insert sb addr stack)
          (SBAddrsUnique_insert h_unique) h_mem_new
      simpa [h_old] using h_new_eq

theorem SBValid_insert
  {ap : AccessPerms} {addr : Word} {stack : BorrowStack}
  (h_valid : SBValid ap)
  (h_stack_unique : StackTagsUnique stack) :
  SBValid { ap with StackMap := SB.insert ap.StackMap addr stack } := by
  cases h_valid with
  | intro h_addr_unique h_stacks =>
      refine ⟨SBAddrsUnique_insert h_addr_unique, ?_⟩
      intro a stack' h_mem
      have h_cases := SB.mem_insert_cases h_mem
      cases h_cases with
      | inl h_new =>
          cases h_new with
          | intro h_addr h_stack =>
              subst h_addr
              subst h_stack
              exact h_stack_unique
      | inr h_old =>
          exact h_stacks h_old.1

theorem stack_unique_of_subset
  {stack newStack : BorrowStack}
  (h_unique : StackTagsUnique stack)
  (h_subset : ∀ ⦃k : RefKind⦄, k ∈ newStack → k ∈ stack) :
  StackTagsUnique newStack := by
  intro k₁ k₂ hk₁ hk₂ h_eq
  exact h_unique (h_subset hk₁) (h_subset hk₂) h_eq

-- Rule: sb-read
-- Premise: sb[a] = x ++ (g, k) :: y, k \in {o, mb, b, rw}
-- Conclusion: sb[a] = filter(x, ¬mb) ++ (g, k) :: y
def sb_read (ap : AccessPerms) (addr : Word) (tag : Tag) : SBResult :=
  match ap.StackMap.find? addr with
  | none => Err s!"sb-read: address {addr} not found"
  | some stack =>
    match splitStack stack tag with
    | none => Err s!"sb-read: tag {tag} not found in stack at {addr}"
    | some (x, item, y) =>
      match item with
      | RefKind.Own _ | RefKind.MutRef _ | RefKind.Ref _ | RefKind.RawPtr _ =>
        let x' := x.filter (fun k => !k.isMb)
        let newStack := x' ++ item :: y
        let newSB := ap.StackMap.insert addr newStack
        Ok { ap with StackMap := newSB }

theorem sb_read_nextTag_eq
  {ap ap' : AccessPerms}
  {addr tag : Word}
  (h_read : sb_read ap addr tag = SBResult.Ok ap') :
  ap'.NextTag = ap.NextTag := by
  unfold sb_read at h_read
  cases h_find : ap.StackMap.find? addr with
  | none =>
      simp [h_find] at h_read
  | some stack =>
      cases h_split : splitStack stack tag with
      | none =>
          simp [h_find, h_split] at h_read
      | some triple =>
          rcases triple with ⟨x, item, y⟩
          cases item <;> simp [h_find, h_split] at h_read
          all_goals
            cases h_read
            rfl

-- Rule: sb-use-mb
-- Premise: sb[a] = x ++ (g, k) :: y, k \in {o, mb}
-- Conclusion: sb[a] = (g, k) :: y
def sb_use_mb (ap : AccessPerms) (addr : Word) (tag : Tag) : SBResult :=
  match ap.StackMap.find? addr with
  | none => Err s!"sb-use-mb: address {addr} not found"
  | some stack =>
    match splitStack stack tag with
    | none => Err s!"sb-use-mb: tag {tag} not found in stack at {addr}"
    | some (_x, item, y) =>
      match item with
      | RefKind.Own _ | RefKind.MutRef _ =>
        let newStack := item :: y
        let newSB := ap.StackMap.insert addr newStack
        Ok { ap with StackMap := newSB }
      | _ => Err s!"sb-use-mb: tag {tag} is not Own or MutRef"

theorem sb_use_mb_nextTag_eq
  {ap ap' : AccessPerms}
  {addr tag : Word}
  (h_use : sb_use_mb ap addr tag = SBResult.Ok ap') :
  ap'.NextTag = ap.NextTag := by
  unfold sb_use_mb at h_use
  cases h_find : ap.StackMap.find? addr with
  | none =>
      simp [h_find] at h_use
  | some stack =>
      cases h_split : splitStack stack tag with
      | none =>
          simp [h_find, h_split] at h_use
      | some triple =>
          rcases triple with ⟨x, item, y⟩
          cases item <;> simp [h_find, h_split] at h_use
          all_goals
            cases h_use
            rfl

theorem sb_use_mb_preserves_valid
  {ap ap' : AccessPerms} {addr tag : Word}
  (h_valid : SBValid ap)
  (h_use : sb_use_mb ap addr tag = Ok ap') :
  SBValid ap' := by
  unfold sb_use_mb at h_use
  cases h_find : ap.StackMap.find? addr with
  | none =>
      simp [h_find] at h_use
  | some stack =>
      cases h_split : splitStack stack tag with
      | none =>
          simp [h_find, h_split] at h_use
      | some triple =>
          cases triple with
          | mk x rest =>
              cases rest with
              | mk item y =>
                  cases item with
                  | Own t =>
                      simp [h_find, h_split] at h_use
                      subst ap'
                      have h_mem_stack : (addr, stack) ∈ ap.StackMap :=
                        SB.find?_some_mem h_find
                      have h_tags_unique : StackTagsUnique stack := by
                        cases h_valid with
                        | intro _ h_stack_valid =>
                            exact h_stack_valid h_mem_stack
                      have h_new_mem :
                          ∀ ⦃k : RefKind⦄, k ∈ RefKind.Own t :: y → k ∈ stack := by
                        intro k hk
                        exact splitStack_result_mem h_split hk
                      refine SBValid_insert h_valid ?_
                      intro k₁ k₂ hk₁ hk₂ h_eq
                      apply h_tags_unique
                      · exact h_new_mem hk₁
                      · exact h_new_mem hk₂
                      · exact h_eq
                  | MutRef t =>
                      simp [h_find, h_split] at h_use
                      subst ap'
                      have h_mem_stack : (addr, stack) ∈ ap.StackMap :=
                        SB.find?_some_mem h_find
                      have h_tags_unique : StackTagsUnique stack := by
                        cases h_valid with
                        | intro _ h_stack_valid =>
                            exact h_stack_valid h_mem_stack
                      have h_new_mem :
                          ∀ ⦃k : RefKind⦄, k ∈ RefKind.MutRef t :: y → k ∈ stack := by
                        intro k hk
                        exact splitStack_result_mem h_split hk
                      refine SBValid_insert h_valid ?_
                      intro k₁ k₂ hk₁ hk₂ h_eq
                      apply h_tags_unique
                      · exact h_new_mem hk₁
                      · exact h_new_mem hk₂
                      · exact h_eq
                  | Ref t =>
                      simp [h_find, h_split] at h_use
                  | RawPtr t =>
                      simp [h_find, h_split] at h_use

theorem sb_read_preserves_valid
  {ap ap' : AccessPerms} {addr tag : Word}
  (h_valid : SBValid ap)
  (h_read : sb_read ap addr tag = Ok ap') :
  SBValid ap' := by
  unfold sb_read at h_read
  cases h_find : ap.StackMap.find? addr with
  | none =>
      simp [h_find] at h_read
  | some stack =>
      cases h_split : splitStack stack tag with
      | none =>
          simp [h_find, h_split] at h_read
      | some triple =>
          cases triple with
          | mk x rest =>
              cases rest with
              | mk item y =>
                  have h_mem_stack : (addr, stack) ∈ ap.StackMap :=
                    SB.find?_some_mem h_find
                  have h_tags_unique : StackTagsUnique stack := by
                    cases h_valid with
                    | intro _ h_stack_valid =>
                        exact h_stack_valid h_mem_stack
                  have h_stack_eq : stack = x ++ item :: y :=
                    splitStack_eq_append h_split
                  let newStack := x.filter (fun k => !k.isMb) ++ item :: y
                  have h_subset :
                      ∀ ⦃k : RefKind⦄, k ∈ newStack → k ∈ stack := by
                    intro k hk
                    dsimp [newStack] at hk
                    have hk' : k ∈ x.filter (fun k => !k.isMb) ∨ k ∈ item :: y :=
                      mem_of_mem_append hk
                    cases hk' with
                    | inl hk_left =>
                        have h_filter_props := mem_filter_mem_prop hk_left
                        cases h_filter_props with
                        | intro hk_x _ =>
                            rw [h_stack_eq]
                            exact List.mem_append_left (item :: y) hk_x
                    | inr hk_right =>
                        rw [h_stack_eq]
                        exact List.mem_append_right x hk_right
                  have h_new_unique : StackTagsUnique newStack :=
                    stack_unique_of_subset h_tags_unique h_subset
                  cases item with
                  | Own t =>
                      simp [h_find, h_split] at h_read
                      subst ap'
                      exact
                        SBValid_insert (ap := ap) (addr := addr)
                          (stack := x.filter (fun k => !k.isMb) ++ RefKind.Own t :: y)
                          h_valid h_new_unique
                  | MutRef t =>
                      simp [h_find, h_split] at h_read
                      subst ap'
                      exact
                        SBValid_insert (ap := ap) (addr := addr)
                          (stack := x.filter (fun k => !k.isMb) ++ RefKind.MutRef t :: y)
                          h_valid h_new_unique
                  | Ref t =>
                      simp [h_find, h_split] at h_read
                      subst ap'
                      exact
                        SBValid_insert (ap := ap) (addr := addr)
                          (stack := x.filter (fun k => !k.isMb) ++ RefKind.Ref t :: y)
                          h_valid h_new_unique
                  | RawPtr t =>
                      simp [h_find, h_split] at h_read
                      subst ap'
                      exact
                        SBValid_insert (ap := ap) (addr := addr)
                          (stack := x.filter (fun k => !k.isMb) ++ RefKind.RawPtr t :: y)
                          h_valid h_new_unique

-- Rule: sb-mv
-- Premise: sb[a] = x ++ [(g, o)], k \in {o}
-- Conclusion: sb[a] = []
def sb_move (ap : AccessPerms) (addr : Word) (tag : Tag) : SBResult :=
  match ap.StackMap.find? addr with
  | none => Err s!"sb-move: address {addr} not found"
  | some stack =>
    match stack.reverse with
    | item :: _rest =>
      if item.tag == tag then
        match item with
        | RefKind.Own _ =>
           let newSB := ap.StackMap.insert addr []
           Ok { ap with StackMap := newSB }
        | _ => Err s!"sb-move: tag {tag} is not Own"
      else Err s!"sb-move: tag {tag} is not at the bottom of the stack"
    | [] => Err s!"sb-move: stack empty"

-- Rules: sb-new-mut-ref / sb-new-ref
def sb_ref (ap : AccessPerms) (addr : Word) (tag : Tag) (kind : RefOpKind) : SBResult × Tag :=
  let parentRes :=
    match kind with
    | RefOpKind.Shared => sb_read ap addr tag
    | RefOpKind.Mut => sb_use_mb ap addr tag
    | RefOpKind.Raw => sb_use_mb ap addr tag
  match parentRes with
  | Ok ap' =>
    let (newTag, ap'') := freshTag ap'
    match ap''.StackMap.find? addr with
    | some stack =>
       let newItem := kind.toStackKind newTag
       let newStack := newItem :: stack
       let newSB := ap''.StackMap.insert addr newStack
       (Ok { ap'' with StackMap := newSB }, newTag)
    | none => (Err "sb-ref: stack gone?", 0)
  | Err msg => (Err msg, 0)

-- Rule: sb-die
-- Premise: sb[a] = (g, k) :: y, k \in {mb, b, rw}
-- Conclusion: sb[a] = y
def sb_die (ap : AccessPerms) (addr : Word) (tag : Tag) : SBResult :=
  match ap.StackMap.find? addr with
  | none => Err s!"sb-die: address {addr} not found"
  | some stack =>
    match stack with
    | item :: y =>
      if item.tag == tag then
        match item with
        | RefKind.Own _ => Err s!"sb-die: tag {tag} is not a die-able borrow"
        | RefKind.MutRef _ | RefKind.Ref _ | RefKind.RawPtr _ =>
            let newSB := ap.StackMap.insert addr y
            Ok { ap with StackMap := newSB }
      else Err s!"sb-die: top of stack is {item.tag}, expected {tag}"
    | [] => Err "sb-die: stack empty"

/-! ## Renaming-Based SB Simulation -/

abbrev AddrRenameMap := Word → Option Word
abbrev TagRenameMap := Tag → Option Tag

def extendAddrRenameMap (ρa : AddrRenameMap) (src dst : Word) : AddrRenameMap :=
  fun addr => if addr = src then some dst else ρa addr

def extendTagRenameMap (ρt : TagRenameMap) (src dst : Tag) : TagRenameMap :=
  fun tag => if tag = src then some dst else ρt tag

def stackAt (ap : AccessPerms) (addr : Word) : BorrowStack :=
  Option.getD (SB.find? ap.StackMap addr) []

def refkind_sim (ρt : TagRenameMap) : RefKind → RefKind → Prop
  | RefKind.Own t, RefKind.Own t' => ρt t = some t'
  | RefKind.MutRef t, RefKind.MutRef t' => ρt t = some t'
  | RefKind.Ref t, RefKind.Ref t' => ρt t = some t'
  | RefKind.RawPtr t, RefKind.RawPtr t' => ρt t = some t'
  | _, _ => False

def stack_sim (ρt : TagRenameMap) : BorrowStack → BorrowStack → Prop
  | [], [] => True
  | k :: ks, k' :: ks' => refkind_sim ρt k k' ∧ stack_sim ρt ks ks'
  | _, _ => False

def sb_at_sim (ρt : TagRenameMap) (ap_m ap_o : AccessPerms) (addr addr' : Word) : Prop :=
  stack_sim ρt (stackAt ap_m addr) (stackAt ap_o addr')

def stack_tag_live (stack : BorrowStack) (tag : Tag) : Prop :=
  ∃ k : RefKind, k ∈ stack ∧ k.tag = tag

def tag_live (ap : AccessPerms) (tag : Tag) : Prop :=
  ∃ addr, stack_tag_live (stackAt ap addr) tag

structure SbSimData
  (ρa : AddrRenameMap)
  (ρt : TagRenameMap)
  (ap_m ap_o : AccessPerms) : Prop where
  valid_mir : SBValid ap_m
  valid_osea : SBValid ap_o
  at_sim : ∀ addr addr', ρa addr = some addr' → sb_at_sim ρt ap_m ap_o addr addr'
  addr_inj :
    ∀ addr₁ addr₂ addr',
      ρa addr₁ = some addr' →
      ρa addr₂ = some addr' →
      addr₁ = addr₂
  tag_mapped : ∀ tag, tag_live ap_m tag → ∃ tag', ρt tag = some tag'
  tag_inj :
    ∀ tag₁ tag₂ tag',
      tag_live ap_m tag₁ →
      tag_live ap_m tag₂ →
      ρt tag₁ = some tag' →
      ρt tag₂ = some tag' →
      tag₁ = tag₂

def sb_sim
  (ρa : AddrRenameMap)
  (ρt : TagRenameMap)
  (ap_m ap_o : AccessPerms) : Prop :=
  SbSimData ρa ρt ap_m ap_o

theorem SBValid_of_stackMap_eq
  {ap ap' : AccessPerms}
  (h_stack : ap'.StackMap = ap.StackMap)
  (h_valid : SBValid ap) :
  SBValid ap' := by
  simpa [SBValid, h_stack] using h_valid

theorem sb_sim_of_right_stackMap_eq
  {ρa : AddrRenameMap}
  {ρt : TagRenameMap}
  {ap_m ap_o ap_o' : AccessPerms}
  (h_sim : sb_sim ρa ρt ap_m ap_o)
  (h_stack : ap_o'.StackMap = ap_o.StackMap) :
  sb_sim ρa ρt ap_m ap_o' := by
  cases h_sim with
  | mk valid_mir valid_osea at_sim addr_inj tag_mapped tag_inj =>
      refine ⟨valid_mir, SBValid_of_stackMap_eq h_stack valid_osea, ?_, addr_inj, tag_mapped, tag_inj⟩
      intro addr addr' h_addr
      simpa [sb_at_sim, stackAt, h_stack] using at_sim addr addr' h_addr

axiom sb_ref_mut_use_die_stack_eq
  {ap ap_ref ap_use ap_final ap_parent : AccessPerms}
  {addr tag tempTag : Word}
  (h_parent : sb_use_mb ap addr tag = Ok ap_parent)
  (h_ref : sb_ref ap addr tag RefOpKind.Mut = (Ok ap_ref, tempTag))
  (h_use : sb_use_mb ap_ref addr tempTag = Ok ap_use)
  (h_die : sb_die ap_use addr tempTag = Ok ap_final) :
  ap_final.StackMap = ap_parent.StackMap

axiom sb_ref_shared_read_die_stack_eq
  {ap ap_ref ap_read ap_final ap_parent : AccessPerms}
  {addr tag tempTag : Word}
  (h_parent : sb_read ap addr tag = Ok ap_parent)
  (h_ref : sb_ref ap addr tag RefOpKind.Shared = (Ok ap_ref, tempTag))
  (h_read : sb_read ap_ref addr tempTag = Ok ap_read)
  (h_die : sb_die ap_read addr tempTag = Ok ap_final) :
  ap_final.StackMap = ap_parent.StackMap

axiom sb_ref_mut_use_die_ok_of_use_ok
  {ap ap_parent : AccessPerms}
  {addr tag : Word}
  (h_parent : sb_use_mb ap addr tag = Ok ap_parent) :
  ∃ tempTag ap_ref ap_use ap_final,
    sb_ref ap addr tag RefOpKind.Mut = (Ok ap_ref, tempTag) ∧
    sb_use_mb ap_ref addr tempTag = Ok ap_use ∧
    sb_die ap_use addr tempTag = Ok ap_final ∧
    ap_final.StackMap = ap_parent.StackMap

axiom sb_ref_shared_read_die_ok_of_read_ok
  {ap ap_parent : AccessPerms}
  {addr tag : Word}
  (h_parent : sb_read ap addr tag = Ok ap_parent) :
  ∃ tempTag ap_ref ap_read ap_final,
    sb_ref ap addr tag RefOpKind.Shared = (Ok ap_ref, tempTag) ∧
    sb_read ap_ref addr tempTag = Ok ap_read ∧
    sb_die ap_read addr tempTag = Ok ap_final ∧
    ap_final.StackMap = ap_parent.StackMap

/-! ## Axioms -/

/--
`NextTag` is treated as an abstract freshness source.
-/
axiom freshTag_fresh
  {ap : AccessPerms} :
  ¬ tag_live ap ap.NextTag

theorem tag_live_of_find_mem
  {ap : AccessPerms} {addr : Word} {stack : BorrowStack} {k : RefKind}
  (h_find : ap.StackMap.find? addr = some stack)
  (h_mem : k ∈ stack) :
  tag_live ap k.tag := by
  refine ⟨addr, ⟨k, ?_, rfl⟩⟩
  simpa [stackAt, h_find] using h_mem

theorem tag_live_of_sb_read_ok
  {ap ap' : AccessPerms} {addr tag : Word}
  (h_read : sb_read ap addr tag = SBResult.Ok ap') :
  tag_live ap' tag := by
  unfold sb_read at h_read
  cases h_find : ap.StackMap.find? addr with
  | none =>
      simp [h_find] at h_read
  | some stack =>
      cases h_split : splitStack stack tag with
      | none =>
          simp [h_find, h_split] at h_read
      | some triple =>
          rcases triple with ⟨x, item, y⟩
          have h_item_tag := splitStack_found_tag h_split
          cases item with
          | Own t =>
              have ht : t = tag := by simpa using h_item_tag
              cases ht
              simp [h_find, h_split] at h_read
              subst ap'
              exact tag_live_of_find_mem
                (ap := { ap with StackMap := SB.insert ap.StackMap addr (x.filter (fun k => !k.isMb) ++ RefKind.Own tag :: y) })
                (addr := addr)
                (stack := x.filter (fun k => !k.isMb) ++ RefKind.Own tag :: y)
                (k := RefKind.Own tag)
                (SB.find?_insert_eq _ _ _)
                (by simp)
          | MutRef t =>
              have ht : t = tag := by simpa using h_item_tag
              cases ht
              simp [h_find, h_split] at h_read
              subst ap'
              exact tag_live_of_find_mem
                (ap := { ap with StackMap := SB.insert ap.StackMap addr (x.filter (fun k => !k.isMb) ++ RefKind.MutRef tag :: y) })
                (addr := addr)
                (stack := x.filter (fun k => !k.isMb) ++ RefKind.MutRef tag :: y)
                (k := RefKind.MutRef tag)
                (SB.find?_insert_eq _ _ _)
                (by simp)
          | Ref t =>
              have ht : t = tag := by simpa using h_item_tag
              cases ht
              simp [h_find, h_split] at h_read
              subst ap'
              exact tag_live_of_find_mem
                (ap := { ap with StackMap := SB.insert ap.StackMap addr (x.filter (fun k => !k.isMb) ++ RefKind.Ref tag :: y) })
                (addr := addr)
                (stack := x.filter (fun k => !k.isMb) ++ RefKind.Ref tag :: y)
                (k := RefKind.Ref tag)
                (SB.find?_insert_eq _ _ _)
                (by simp)
          | RawPtr t =>
              have ht : t = tag := by simpa using h_item_tag
              cases ht
              simp [h_find, h_split] at h_read
              subst ap'
              exact tag_live_of_find_mem
                (ap := { ap with StackMap := SB.insert ap.StackMap addr (x.filter (fun k => !k.isMb) ++ RefKind.RawPtr tag :: y) })
                (addr := addr)
                (stack := x.filter (fun k => !k.isMb) ++ RefKind.RawPtr tag :: y)
                (k := RefKind.RawPtr tag)
                (SB.find?_insert_eq _ _ _)
                (by simp)

theorem tag_live_of_sb_ref_new_ok
  {ap ap' : AccessPerms} {addr tag newTag : Word} {kind : RefOpKind}
  (h_ref : sb_ref ap addr tag kind = (SBResult.Ok ap', newTag)) :
  tag_live ap' newTag := by
  cases kind with
  | Shared =>
      unfold sb_ref at h_ref
      cases h_parent : sb_read ap addr tag with
      | Err msg =>
          simp [h_parent] at h_ref
      | Ok ap_parent =>
          cases h_find : { ap_parent with NextTag := ap_parent.NextTag + 1 }.StackMap.find? addr with
          | none =>
              simp [h_parent, freshTag, h_find] at h_ref
          | some stack =>
              simp [h_parent, freshTag, h_find] at h_ref
              rcases h_ref with ⟨rfl, rfl⟩
              exact tag_live_of_find_mem
                (ap :=
                  { { ap_parent with NextTag := ap_parent.NextTag + 1 } with
                    StackMap :=
                      SB.insert { ap_parent with NextTag := ap_parent.NextTag + 1 }.StackMap
                        addr (RefKind.Ref ap_parent.NextTag :: stack) })
                (addr := addr)
                (stack := RefKind.Ref ap_parent.NextTag :: stack)
                (k := RefKind.Ref ap_parent.NextTag)
                (SB.find?_insert_eq _ _ _)
                (by simp)
  | Mut =>
      unfold sb_ref at h_ref
      cases h_parent : sb_use_mb ap addr tag with
      | Err msg =>
          simp [h_parent] at h_ref
      | Ok ap_parent =>
          cases h_find : { ap_parent with NextTag := ap_parent.NextTag + 1 }.StackMap.find? addr with
          | none =>
              simp [h_parent, freshTag, h_find] at h_ref
          | some stack =>
              simp [h_parent, freshTag, h_find] at h_ref
              rcases h_ref with ⟨rfl, rfl⟩
              exact tag_live_of_find_mem
                (ap :=
                  { { ap_parent with NextTag := ap_parent.NextTag + 1 } with
                    StackMap :=
                      SB.insert { ap_parent with NextTag := ap_parent.NextTag + 1 }.StackMap
                        addr (RefKind.MutRef ap_parent.NextTag :: stack) })
                (addr := addr)
                (stack := RefKind.MutRef ap_parent.NextTag :: stack)
                (k := RefKind.MutRef ap_parent.NextTag)
                (SB.find?_insert_eq _ _ _)
                (by simp)
  | Raw =>
      unfold sb_ref at h_ref
      cases h_parent : sb_use_mb ap addr tag with
      | Err msg =>
          simp [h_parent] at h_ref
      | Ok ap_parent =>
          cases h_find : { ap_parent with NextTag := ap_parent.NextTag + 1 }.StackMap.find? addr with
          | none =>
              simp [h_parent, freshTag, h_find] at h_ref
          | some stack =>
              simp [h_parent, freshTag, h_find] at h_ref
              rcases h_ref with ⟨rfl, rfl⟩
              exact tag_live_of_find_mem
                (ap :=
                  { { ap_parent with NextTag := ap_parent.NextTag + 1 } with
                    StackMap :=
                      SB.insert { ap_parent with NextTag := ap_parent.NextTag + 1 }.StackMap
                        addr (RefKind.RawPtr ap_parent.NextTag :: stack) })
                (addr := addr)
                (stack := RefKind.RawPtr ap_parent.NextTag :: stack)
                (k := RefKind.RawPtr ap_parent.NextTag)
                (SB.find?_insert_eq _ _ _)
                (by simp)

        theorem sb_ref_new_stack_find
          {ap ap' : AccessPerms} {addr tag newTag : Word} {kind : RefOpKind}
          (h_ref : sb_ref ap addr tag kind = (SBResult.Ok ap', newTag)) :
          ∃ stack,
          ap'.StackMap.find? addr = some (kind.toStackKind newTag :: stack) := by
          cases kind with
          | Shared =>
            unfold sb_ref at h_ref
            cases h_parent : sb_read ap addr tag with
            | Err msg =>
              simp [h_parent] at h_ref
            | Ok ap_parent =>
              cases h_find : { ap_parent with NextTag := ap_parent.NextTag + 1 }.StackMap.find? addr with
              | none =>
                simp [h_parent, freshTag, h_find] at h_ref
              | some stack =>
                simp [h_parent, freshTag, h_find] at h_ref
                rcases h_ref with ⟨rfl, rfl⟩
                refine ⟨stack, ?_⟩
                simpa using
                (SB.find?_insert_eq
                  { ap_parent with NextTag := ap_parent.NextTag + 1 }.StackMap
                  addr
                  (RefKind.Ref ap_parent.NextTag :: stack))
          | Mut =>
            unfold sb_ref at h_ref
            cases h_parent : sb_use_mb ap addr tag with
            | Err msg =>
              simp [h_parent] at h_ref
            | Ok ap_parent =>
              cases h_find : { ap_parent with NextTag := ap_parent.NextTag + 1 }.StackMap.find? addr with
              | none =>
                simp [h_parent, freshTag, h_find] at h_ref
              | some stack =>
                simp [h_parent, freshTag, h_find] at h_ref
                rcases h_ref with ⟨rfl, rfl⟩
                refine ⟨stack, ?_⟩
                simpa using
                (SB.find?_insert_eq
                  { ap_parent with NextTag := ap_parent.NextTag + 1 }.StackMap
                  addr
                  (RefKind.MutRef ap_parent.NextTag :: stack))
          | Raw =>
            unfold sb_ref at h_ref
            cases h_parent : sb_use_mb ap addr tag with
            | Err msg =>
              simp [h_parent] at h_ref
            | Ok ap_parent =>
              cases h_find : { ap_parent with NextTag := ap_parent.NextTag + 1 }.StackMap.find? addr with
              | none =>
                simp [h_parent, freshTag, h_find] at h_ref
              | some stack =>
                simp [h_parent, freshTag, h_find] at h_ref
                rcases h_ref with ⟨rfl, rfl⟩
                refine ⟨stack, ?_⟩
                simpa using
                (SB.find?_insert_eq
                  { ap_parent with NextTag := ap_parent.NextTag + 1 }.StackMap
                  addr
                  (RefKind.RawPtr ap_parent.NextTag :: stack))

theorem sb_ref_nextTag_succ
  {ap ap' : AccessPerms} {addr tag newTag : Word} {kind : RefOpKind}
  (h_ref : sb_ref ap addr tag kind = (SBResult.Ok ap', newTag)) :
  ap'.NextTag = ap.NextTag + 1 := by
  cases kind with
  | Shared =>
      unfold sb_ref at h_ref
      cases h_parent : sb_read ap addr tag with
      | Err msg =>
          simp [h_parent] at h_ref
      | Ok ap_parent =>
          have h_parent_next : ap_parent.NextTag = ap.NextTag :=
            sb_read_nextTag_eq h_parent
          cases h_find : { ap_parent with NextTag := ap_parent.NextTag + 1 }.StackMap.find? addr with
          | none =>
              simp [h_parent, freshTag, h_find] at h_ref
          | some stack =>
              simp [h_parent, freshTag, h_find] at h_ref
              rcases h_ref with ⟨h_ap, _h_tag⟩
              have h_next_eq : ap'.NextTag = ap_parent.NextTag + 1 := by
                simpa using congrArg AccessPerms.NextTag h_ap.symm
              simpa [h_parent_next] using h_next_eq
  | Mut =>
      unfold sb_ref at h_ref
      cases h_parent : sb_use_mb ap addr tag with
      | Err msg =>
          simp [h_parent] at h_ref
      | Ok ap_parent =>
          have h_parent_next : ap_parent.NextTag = ap.NextTag :=
            sb_use_mb_nextTag_eq h_parent
          cases h_find : { ap_parent with NextTag := ap_parent.NextTag + 1 }.StackMap.find? addr with
          | none =>
              simp [h_parent, freshTag, h_find] at h_ref
          | some stack =>
              simp [h_parent, freshTag, h_find] at h_ref
              rcases h_ref with ⟨h_ap, _h_tag⟩
              have h_next_eq : ap'.NextTag = ap_parent.NextTag + 1 := by
                simpa using congrArg AccessPerms.NextTag h_ap.symm
              simpa [h_parent_next] using h_next_eq
  | Raw =>
      unfold sb_ref at h_ref
      cases h_parent : sb_use_mb ap addr tag with
      | Err msg =>
          simp [h_parent] at h_ref
      | Ok ap_parent =>
          have h_parent_next : ap_parent.NextTag = ap.NextTag :=
            sb_use_mb_nextTag_eq h_parent
          cases h_find : { ap_parent with NextTag := ap_parent.NextTag + 1 }.StackMap.find? addr with
          | none =>
              simp [h_parent, freshTag, h_find] at h_ref
          | some stack =>
              simp [h_parent, freshTag, h_find] at h_ref
              rcases h_ref with ⟨h_ap, _h_tag⟩
              have h_next_eq : ap'.NextTag = ap_parent.NextTag + 1 := by
                simpa using congrArg AccessPerms.NextTag h_ap.symm
              simpa [h_parent_next] using h_next_eq

theorem stack_unique_cons_of_fresh
  {ap : AccessPerms} {addr : Word} {stack : BorrowStack} {item : RefKind}
  (h_valid : SBValid ap)
  (h_find : ap.StackMap.find? addr = some stack)
  (h_fresh : ¬ tag_live ap item.tag) :
  StackTagsUnique (item :: stack) := by
  have h_mem_stack : (addr, stack) ∈ ap.StackMap :=
    SB.find?_some_mem h_find
  have h_unique_stack : StackTagsUnique stack :=
    h_valid.2 h_mem_stack
  intro k₁ k₂ hk₁ hk₂ h_eq
  simp at hk₁ hk₂
  rcases hk₁ with rfl | hk₁_tail
  · rcases hk₂ with rfl | hk₂_tail
    · rfl
    · exfalso
      apply h_fresh
      simpa [h_eq] using tag_live_of_find_mem h_find hk₂_tail
  · rcases hk₂ with rfl | hk₂_tail
    · exfalso
      apply h_fresh
      simpa [h_eq] using tag_live_of_find_mem h_find hk₁_tail
    · exact h_unique_stack hk₁_tail hk₂_tail h_eq

theorem stackAt_eq_of_find_eq
  {ap ap' : AccessPerms} {addr : Word}
  (h_find : ap'.StackMap.find? addr = ap.StackMap.find? addr) :
  stackAt ap' addr = stackAt ap addr := by
  simp [stackAt, h_find]

theorem sb_sim_of_right_stackAt_eq
  {ρa : AddrRenameMap}
  {ρt : TagRenameMap}
  {ap_m ap_o ap_o' : AccessPerms}
  (h_sim : sb_sim ρa ρt ap_m ap_o)
  (h_valid : SBValid ap_o')
  (h_stackAt :
    ∀ addr addr', ρa addr = some addr' → stackAt ap_o' addr' = stackAt ap_o addr') :
  sb_sim ρa ρt ap_m ap_o' := by
  cases h_sim with
  | mk valid_mir _ at_sim addr_inj tag_mapped tag_inj =>
      refine ⟨valid_mir, h_valid, ?_, addr_inj, tag_mapped, tag_inj⟩
      intro addr addr' h_addr
      simpa [sb_at_sim, h_stackAt addr addr' h_addr] using at_sim addr addr' h_addr

theorem sb_die_preserves_valid
  {ap ap' : AccessPerms} {addr tag : Word}
  (h_valid : SBValid ap)
  (h_die : sb_die ap addr tag = Ok ap') :
  SBValid ap' := by
  unfold sb_die at h_die
  cases h_find : ap.StackMap.find? addr with
  | none =>
      simp [h_find] at h_die
  | some stack =>
      cases stack with
      | nil =>
          simp [h_find] at h_die
      | cons item y =>
          by_cases h_tag : item.tag == tag
          · cases item with
            | Own t =>
                simp [h_find, h_tag] at h_die
            | MutRef t =>
                simp [h_find, h_tag] at h_die
                subst ap'
                have h_mem_stack : (addr, RefKind.MutRef t :: y) ∈ ap.StackMap :=
                  SB.find?_some_mem h_find
                have h_tags_unique : StackTagsUnique (RefKind.MutRef t :: y) :=
                  h_valid.2 h_mem_stack
                have h_new_unique : StackTagsUnique y := by
                  refine stack_unique_of_subset h_tags_unique ?_
                  intro k hk
                  exact List.Mem.tail _ hk
                exact SBValid_insert h_valid h_new_unique
            | Ref t =>
                simp [h_find, h_tag] at h_die
                subst ap'
                have h_mem_stack : (addr, RefKind.Ref t :: y) ∈ ap.StackMap :=
                  SB.find?_some_mem h_find
                have h_tags_unique : StackTagsUnique (RefKind.Ref t :: y) :=
                  h_valid.2 h_mem_stack
                have h_new_unique : StackTagsUnique y := by
                  refine stack_unique_of_subset h_tags_unique ?_
                  intro k hk
                  exact List.Mem.tail _ hk
                exact SBValid_insert h_valid h_new_unique
            | RawPtr t =>
                simp [h_find, h_tag] at h_die
                subst ap'
                have h_mem_stack : (addr, RefKind.RawPtr t :: y) ∈ ap.StackMap :=
                  SB.find?_some_mem h_find
                have h_tags_unique : StackTagsUnique (RefKind.RawPtr t :: y) :=
                  h_valid.2 h_mem_stack
                have h_new_unique : StackTagsUnique y := by
                  refine stack_unique_of_subset h_tags_unique ?_
                  intro k hk
                  exact List.Mem.tail _ hk
                exact SBValid_insert h_valid h_new_unique
          · simp [h_find, h_tag] at h_die

theorem sb_ref_preserves_valid
  {ap ap' : AccessPerms} {addr tag newTag : Word} {kind : RefOpKind}
  (h_valid : SBValid ap)
  (h_ref : sb_ref ap addr tag kind = (Ok ap', newTag)) :
  SBValid ap' := by
  cases kind with
  | Shared =>
      unfold sb_ref at h_ref
      cases h_parent : sb_read ap addr tag with
      | Err msg =>
          simp [h_parent] at h_ref
      | Ok ap_parent =>
          have h_parent_valid : SBValid ap_parent :=
            sb_read_preserves_valid h_valid h_parent
          cases h_find : ap_parent.StackMap.find? addr with
          | none =>
              simp [h_parent, h_find, freshTag] at h_ref
          | some stack =>
              simp [h_parent, h_find, freshTag] at h_ref
              rcases h_ref with ⟨h_ok, h_tag⟩
              cases h_ok
              cases h_tag
              have h_valid_next : SBValid { ap_parent with NextTag := ap_parent.NextTag + 1 } := by
                simpa [SBValid] using h_parent_valid
              have h_new_unique : StackTagsUnique (RefKind.Ref ap_parent.NextTag :: stack) := by
                refine stack_unique_cons_of_fresh h_parent_valid h_find ?_
                simpa using (freshTag_fresh (ap := ap_parent))
              exact
                SBValid_insert
                  (ap := { ap_parent with NextTag := ap_parent.NextTag + 1 })
                  h_valid_next h_new_unique
  | Mut =>
      unfold sb_ref at h_ref
      cases h_parent : sb_use_mb ap addr tag with
      | Err msg =>
          simp [h_parent] at h_ref
      | Ok ap_parent =>
          have h_parent_valid : SBValid ap_parent :=
            sb_use_mb_preserves_valid h_valid h_parent
          cases h_find : ap_parent.StackMap.find? addr with
          | none =>
              simp [h_parent, h_find, freshTag] at h_ref
          | some stack =>
              simp [h_parent, h_find, freshTag] at h_ref
              rcases h_ref with ⟨h_ok, h_tag⟩
              cases h_ok
              cases h_tag
              have h_valid_next : SBValid { ap_parent with NextTag := ap_parent.NextTag + 1 } := by
                simpa [SBValid] using h_parent_valid
              have h_new_unique : StackTagsUnique (RefKind.MutRef ap_parent.NextTag :: stack) := by
                refine stack_unique_cons_of_fresh h_parent_valid h_find ?_
                simpa using (freshTag_fresh (ap := ap_parent))
              exact
                SBValid_insert
                  (ap := { ap_parent with NextTag := ap_parent.NextTag + 1 })
                  h_valid_next h_new_unique
  | Raw =>
      unfold sb_ref at h_ref
      cases h_parent : sb_use_mb ap addr tag with
      | Err msg =>
          simp [h_parent] at h_ref
      | Ok ap_parent =>
          have h_parent_valid : SBValid ap_parent :=
            sb_use_mb_preserves_valid h_valid h_parent
          cases h_find : ap_parent.StackMap.find? addr with
          | none =>
              simp [h_parent, h_find, freshTag] at h_ref
          | some stack =>
              simp [h_parent, h_find, freshTag] at h_ref
              rcases h_ref with ⟨h_ok, h_tag⟩
              cases h_ok
              cases h_tag
              have h_valid_next : SBValid { ap_parent with NextTag := ap_parent.NextTag + 1 } := by
                simpa [SBValid] using h_parent_valid
              have h_new_unique : StackTagsUnique (RefKind.RawPtr ap_parent.NextTag :: stack) := by
                refine stack_unique_cons_of_fresh h_parent_valid h_find ?_
                simpa using (freshTag_fresh (ap := ap_parent))
              exact
                SBValid_insert
                  (ap := { ap_parent with NextTag := ap_parent.NextTag + 1 })
                  h_valid_next h_new_unique

axiom sb_read_sim_ok
  {ρa : AddrRenameMap} {ρt : TagRenameMap}
  {ap_m ap_o ap_m' : AccessPerms}
  {addr_m addr_o tag_m tag_o : Word}
  (h_sim : sb_sim ρa ρt ap_m ap_o)
  (h_addr : ρa addr_m = some addr_o)
  (h_tag : ρt tag_m = some tag_o)
  (h_read : sb_read ap_m addr_m tag_m = Ok ap_m') :
  ∃ ap_o',
    sb_read ap_o addr_o tag_o = Ok ap_o' ∧
    sb_sim ρa ρt ap_m' ap_o'

axiom sb_use_mb_sim_ok
  {ρa : AddrRenameMap} {ρt : TagRenameMap}
  {ap_m ap_o ap_m' : AccessPerms}
  {addr_m addr_o tag_m tag_o : Word}
  (h_sim : sb_sim ρa ρt ap_m ap_o)
  (h_addr : ρa addr_m = some addr_o)
  (h_tag : ρt tag_m = some tag_o)
  (h_use : sb_use_mb ap_m addr_m tag_m = Ok ap_m') :
  ∃ ap_o',
    sb_use_mb ap_o addr_o tag_o = Ok ap_o' ∧
    sb_sim ρa ρt ap_m' ap_o'

axiom sb_own_sim_extend
  {ρa : AddrRenameMap} {ρt : TagRenameMap}
  {ap_m ap_o ap_m' : AccessPerms}
  {addr_m addr_o tag_m : Word}
  (h_sim : sb_sim ρa ρt ap_m ap_o)
  (h_own : sb_own ap_m addr_m = (Ok ap_m', tag_m)) :
  ∃ tag_o ap_o',
    sb_own ap_o addr_o = (Ok ap_o', tag_o) ∧
    sb_sim
      (extendAddrRenameMap ρa addr_m addr_o)
      (extendTagRenameMap ρt tag_m tag_o)
      ap_m' ap_o'

/-! ### sb_ref bilateral simulation -/

/--
When `sb_ref` succeeds on the MIR side, the same operation succeeds on the
OSEA side with a (possibly different) fresh borrow tag.  The resulting access
permissions are SB-similar under the *same* address renaming but an *extended*
tag renaming that maps the new MIR borrow tag to the new OSEA borrow tag.
-/
axiom sb_ref_sim_ok
  {ρa : AddrRenameMap} {ρt : TagRenameMap}
  {ap_m ap_o ap_m' : AccessPerms}
  {addr_m addr_o tag_m tag_o newTag_m : Word}
  {kind : RefOpKind}
  (h_sim : sb_sim ρa ρt ap_m ap_o)
  (h_addr : ρa addr_m = some addr_o)
  (h_tag : ρt tag_m = some tag_o)
  (h_ref : sb_ref ap_m addr_m tag_m kind = (Ok ap_m', newTag_m)) :
  ∃ newTag_o ap_o',
    sb_ref ap_o addr_o tag_o kind = (Ok ap_o', newTag_o) ∧
    sb_sim ρa (extendTagRenameMap ρt newTag_m newTag_o) ap_m' ap_o'

/-! ### OSEA-only operations on unmapped addresses

The following three axioms express the principle that any successful SB
operation on an OSEA-side address that is **not** in the codomain of `ρa`
preserves the renaming-based simulation.  Intuitively, these operations only
touch stacks at addresses that no MIR address maps to, so every mapped
address's stack stays unchanged. -/

/--
Unilateral `sb_own` on an OSEA-only address preserves `sb_sim`.
-/
axiom sb_osea_only_own_preserves_sim
  {ρa : AddrRenameMap} {ρt : TagRenameMap}
  {ap_m ap_o ap_o' : AccessPerms}
  {addr_o tag_o : Word}
  (h_sim : sb_sim ρa ρt ap_m ap_o)
  (h_unmapped : ∀ a, ρa a ≠ some addr_o)
  (h_own : sb_own ap_o addr_o = (Ok ap_o', tag_o)) :
  sb_sim ρa ρt ap_m ap_o'

/--
Unilateral `sb_use_mb` on an OSEA-only address preserves `sb_sim`.
-/
axiom sb_osea_only_use_mb_preserves_sim
  {ρa : AddrRenameMap} {ρt : TagRenameMap}
  {ap_m ap_o ap_o' : AccessPerms}
  {addr_o tag_o : Word}
  (h_sim : sb_sim ρa ρt ap_m ap_o)
  (h_unmapped : ∀ a, ρa a ≠ some addr_o)
  (h_use : sb_use_mb ap_o addr_o tag_o = Ok ap_o') :
  sb_sim ρa ρt ap_m ap_o'

/--
Unilateral `sb_read` on an OSEA-only address preserves `sb_sim`.
-/
axiom sb_osea_only_read_preserves_sim
  {ρa : AddrRenameMap} {ρt : TagRenameMap}
  {ap_m ap_o ap_o' : AccessPerms}
  {addr_o tag_o : Word}
  (h_sim : sb_sim ρa ρt ap_m ap_o)
  (h_unmapped : ∀ a, ρa a ≠ some addr_o)
  (h_read : sb_read ap_o addr_o tag_o = Ok ap_o') :
  sb_sim ρa ρt ap_m ap_o'

@[simp] theorem extendAddrRenameMap_self
  (ρa : AddrRenameMap) (src dst : Word) :
  (extendAddrRenameMap ρa src dst) src = some dst := by
  simp [extendAddrRenameMap]

@[simp] theorem extendAddrRenameMap_ne
  (ρa : AddrRenameMap) (src dst addr : Word)
  (h_ne : addr ≠ src) :
  (extendAddrRenameMap ρa src dst) addr = ρa addr := by
  simp [extendAddrRenameMap, h_ne]

@[simp] theorem extendTagRenameMap_self
  (ρt : TagRenameMap) (src dst : Tag) :
  (extendTagRenameMap ρt src dst) src = some dst := by
  simp [extendTagRenameMap]

@[simp] theorem extendTagRenameMap_ne
  (ρt : TagRenameMap) (src dst tag : Tag)
  (h_ne : tag ≠ src) :
  (extendTagRenameMap ρt src dst) tag = ρt tag := by
  simp [extendTagRenameMap, h_ne]

/-! ### SB operation success lemmas -/

/--
`sb_own` succeeds on an address whose borrow stack is absent (`none`) or empty.
-/
theorem sb_osea_only_own_ok
  {ap : AccessPerms} {addr : Word}
  (h_empty : ap.StackMap.find? addr = none ∨
             ap.StackMap.find? addr = some []) :
  ∃ tag ap', sb_own ap addr = (SBResult.Ok ap', tag)
:= by
  unfold sb_own
  rcases h_empty with h_empty | h_empty
  · rw [h_empty]
    let ap1 : AccessPerms := { ap with NextTag := ap.NextTag + 1 }
    refine ⟨ap.NextTag, { ap1 with StackMap := ap1.StackMap.insert addr [RefKind.Own ap.NextTag] }, ?_⟩
    simp [freshTag, ap1]
  · rw [h_empty]
    let ap1 : AccessPerms := { ap with NextTag := ap.NextTag + 1 }
    refine ⟨ap.NextTag, { ap1 with StackMap := ap1.StackMap.insert addr [RefKind.Own ap.NextTag] }, ?_⟩
    simp [freshTag, ap1]

/--
After `sb_own` succeeds at `addr`, the stack there is exactly `[Own tag]`.
-/
theorem sb_own_creates_find
  {ap ap' : AccessPerms} {addr tag : Word}
  (h_own : sb_own ap addr = (SBResult.Ok ap', tag)) :
  ap'.StackMap.find? addr = some [RefKind.Own tag]
:= by
  unfold sb_own at h_own
  cases h_find : ap.StackMap.find? addr with
  | none =>
      rw [h_find] at h_own
      unfold freshTag at h_own
      injection h_own with h_ok h_tag
      cases h_ok
      cases h_tag
      exact SB.find?_insert_eq _ _ _
  | some stack =>
      cases stack with
      | nil =>
          rw [h_find] at h_own
          unfold freshTag at h_own
          injection h_own with h_ok h_tag
          cases h_ok
          cases h_tag
          exact SB.find?_insert_eq _ _ _
      | cons item rest =>
          simp [h_find] at h_own

theorem sb_own_preserves_valid
  {ap ap' : AccessPerms} {addr tag : Word}
  (h_valid : SBValid ap)
  (h_own : sb_own ap addr = (SBResult.Ok ap', tag)) :
  SBValid ap' := by
  unfold sb_own at h_own
  cases h_find : ap.StackMap.find? addr with
  | none =>
      rw [h_find] at h_own
      unfold freshTag at h_own
      injection h_own with h_ok h_tag
      cases h_ok
      have h_valid_next : SBValid { ap with NextTag := ap.NextTag + 1 } := by
        simpa [SBValid] using h_valid
      refine SBValid_insert h_valid_next ?_
      intro k₁ k₂ hk₁ hk₂ h_eq
      simp at hk₁ hk₂
      rcases hk₁ with rfl
      rcases hk₂ with rfl
      rfl
  | some stack =>
      cases stack with
      | nil =>
          rw [h_find] at h_own
          unfold freshTag at h_own
          injection h_own with h_ok h_tag
          cases h_ok
          have h_valid_next : SBValid { ap with NextTag := ap.NextTag + 1 } := by
            simpa [SBValid] using h_valid
          refine SBValid_insert h_valid_next ?_
          intro k₁ k₂ hk₁ hk₂ h_eq
          simp at hk₁ hk₂
          rcases hk₁ with rfl
          rcases hk₂ with rfl
          rfl
      | cons item rest =>
          simp [h_find] at h_own

theorem sb_own_preserves_find_ne
  {ap ap' : AccessPerms} {addr addr' tag : Word}
  (h_valid : SBValid ap)
  (h_own : sb_own ap addr = (SBResult.Ok ap', tag))
  (h_ne : addr' ≠ addr) :
  ap'.StackMap.find? addr' = ap.StackMap.find? addr' := by
  unfold sb_own at h_own
  cases h_find : ap.StackMap.find? addr with
  | none =>
      rw [h_find] at h_own
      unfold freshTag at h_own
      injection h_own with h_ok h_tag
      cases h_ok
      cases h_tag
      simpa using SB.find?_insert_ne h_valid.1 h_ne
  | some stack =>
      cases stack with
      | nil =>
          rw [h_find] at h_own
          unfold freshTag at h_own
          injection h_own with h_ok h_tag
          cases h_ok
          cases h_tag
          simpa using SB.find?_insert_ne h_valid.1 h_ne
      | cons hd tl =>
          simp [h_find] at h_own

    theorem sb_own_find_nonempty_ne
      {ap ap' : AccessPerms} {addr addr' tag : Word} {stack : BorrowStack}
      (h_own : sb_own ap addr = (SBResult.Ok ap', tag))
      (h_find : ap.StackMap.find? addr' = some stack)
      (h_nonempty : stack ≠ []) :
      addr' ≠ addr := by
      intro h_eq
      subst h_eq
      unfold sb_own at h_own
      rw [h_find] at h_own
      cases stack with
      | nil =>
        exact h_nonempty rfl
      | cons hd tl =>
        simp at h_own

/--
`sb_use_mb` succeeds when the stack is a singleton `[Own tag]`.
Provable from the `sb_use_mb` definition: `splitStack [Own tag] tag` returns
`some ([], Own tag, [])` and `Own` matches the `Own | MutRef` arm.
-/
theorem sb_use_mb_of_find_own
  {ap : AccessPerms} {addr tag : Word}
  (h_find : ap.StackMap.find? addr = some [RefKind.Own tag]) :
  ∃ ap', sb_use_mb ap addr tag = SBResult.Ok ap' := by
  unfold sb_use_mb
  simp only [h_find, splitStack, RefKind.tag, beq_self_eq_true, ↓reduceIte]
  exact ⟨_, rfl⟩

/--
After `sb_use_mb` on a singleton `[Own tag]` stack, the stack is still
`[Own tag]`.
-/
theorem sb_use_mb_preserves_find_own
  {ap ap' : AccessPerms} {addr tag : Word}
  (h_find : ap.StackMap.find? addr = some [RefKind.Own tag])
  (h_use : sb_use_mb ap addr tag = SBResult.Ok ap') :
  ap'.StackMap.find? addr = some [RefKind.Own tag] := by
  unfold sb_use_mb at h_use
  simp only [h_find, splitStack, RefKind.tag, beq_self_eq_true, ↓reduceIte,
             SBResult.Ok.injEq] at h_use
  subst h_use
  exact SB.find?_insert_eq _ _ _

/--
`sb_read` succeeds when the stack is a singleton `[Own tag]`.
Provable from the `sb_read` definition: `splitStack [Own tag] tag` returns
`some ([], Own tag, [])` and `Own` matches all allowed kinds.
-/
theorem sb_read_of_find_own
  {ap : AccessPerms} {addr tag : Word}
  (h_find : ap.StackMap.find? addr = some [RefKind.Own tag]) :
  ∃ ap', sb_read ap addr tag = SBResult.Ok ap' := by
  unfold sb_read
  simp only [h_find, splitStack, RefKind.tag, beq_self_eq_true, ↓reduceIte,
             List.filter, List.nil_append]
  exact ⟨_, rfl⟩

theorem sb_read_preserves_find_own
  {ap ap' : AccessPerms} {addr tag : Word}
  (h_find : ap.StackMap.find? addr = some [RefKind.Own tag])
  (h_read : sb_read ap addr tag = SBResult.Ok ap') :
  ap'.StackMap.find? addr = some [RefKind.Own tag] := by
  unfold sb_read at h_read
  simp only [h_find, splitStack, RefKind.tag, beq_self_eq_true, ↓reduceIte,
             List.filter, List.nil_append, SBResult.Ok.injEq] at h_read
  subst ap'
  exact SB.find?_insert_eq _ _ _

theorem sb_use_mb_preserves_find_ne
  {ap ap' : AccessPerms} {addr addr2 tag : Word}
  (h_valid : SBValid ap)
  (h_use : sb_use_mb ap addr tag = SBResult.Ok ap')
  (h_ne : addr2 ≠ addr) :
  ap'.StackMap.find? addr2 = ap.StackMap.find? addr2 := by
  unfold sb_use_mb at h_use
  cases h_find : ap.StackMap.find? addr with
  | none =>
      simp [h_find] at h_use
  | some stack =>
      cases h_split : splitStack stack tag with
      | none =>
          simp [h_find, h_split] at h_use
      | some triple =>
          cases triple with
          | mk x rest =>
              cases rest with
              | mk item y =>
                  cases item <;>
                    simp [h_find, h_split] at h_use <;>
                    subst ap' <;>
                    try simpa using (SB.find?_insert_ne h_valid.1 h_ne)

theorem sb_own_use_preserves_find_ne
  {ap ap2 ap3 : AccessPerms} {addr addr' tag : Word}
  (h_valid : SBValid ap)
  (h_own : sb_own ap addr = (SBResult.Ok ap2, tag))
  (h_use : sb_use_mb ap2 addr tag = SBResult.Ok ap3)
  (h_ne : addr' ≠ addr) :
  ap3.StackMap.find? addr' = ap.StackMap.find? addr' := by
  have h_valid_own : SBValid ap2 := sb_own_preserves_valid h_valid h_own
  calc
    ap3.StackMap.find? addr' = ap2.StackMap.find? addr' :=
      sb_use_mb_preserves_find_ne h_valid_own h_use h_ne
    _ = ap.StackMap.find? addr' :=
      sb_own_preserves_find_ne h_valid h_own h_ne

theorem sb_read_preserves_find_ne
  {ap ap' : AccessPerms} {addr addr2 tag : Word}
  (h_valid : SBValid ap)
  (h_read : sb_read ap addr tag = SBResult.Ok ap')
  (h_ne : addr2 ≠ addr) :
  ap'.StackMap.find? addr2 = ap.StackMap.find? addr2 := by
  unfold sb_read at h_read
  cases h_find : ap.StackMap.find? addr with
  | none =>
      simp [h_find] at h_read
  | some stack =>
      cases h_split : splitStack stack tag with
      | none =>
          simp [h_find, h_split] at h_read
      | some triple =>
          cases triple with
          | mk x rest =>
              cases rest with
              | mk item y =>
                  cases item <;>
                    simp [h_find, h_split] at h_read <;>
                    subst ap' <;>
                    simpa using (SB.find?_insert_ne h_valid.1 h_ne)

theorem sb_die_preserves_find_ne
  {ap ap' : AccessPerms} {addr addr2 tag : Word}
  (h_valid : SBValid ap)
  (h_die : sb_die ap addr tag = SBResult.Ok ap')
  (h_ne : addr2 ≠ addr) :
  ap'.StackMap.find? addr2 = ap.StackMap.find? addr2 := by
  unfold sb_die at h_die
  cases h_find : ap.StackMap.find? addr with
  | none =>
      simp [h_find] at h_die
  | some stack =>
      cases stack with
      | nil =>
          simp [h_find] at h_die
      | cons item y =>
          by_cases h_tag : item.tag == tag
          · cases item <;>
              simp [h_find, h_tag] at h_die <;>
              subst ap' <;>
              simpa using (SB.find?_insert_ne h_valid.1 h_ne)
          · simp [h_find, h_tag] at h_die

/--
`sb_ref` at `addr` does not change the borrow stack at any other address.
-/
theorem sb_ref_preserves_find_ne
  {ap ap' : AccessPerms} {addr addr2 tag newTag : Word} {kind : RefOpKind}
  (h_valid : SBValid ap)
  (h_ref : sb_ref ap addr tag kind = (SBResult.Ok ap', newTag))
  (h_ne : addr2 ≠ addr) :
  ap'.StackMap.find? addr2 = ap.StackMap.find? addr2 := by
  cases kind with
  | Shared =>
      unfold sb_ref at h_ref
      cases h_parent : sb_read ap addr tag with
      | Err msg =>
          simp [h_parent] at h_ref
      | Ok ap_parent =>
          have h_parent_valid : SBValid ap_parent :=
            sb_read_preserves_valid h_valid h_parent
          have h_parent_find :
              ap_parent.StackMap.find? addr2 = ap.StackMap.find? addr2 :=
            sb_read_preserves_find_ne h_valid h_parent h_ne
          cases h_find : ap_parent.StackMap.find? addr with
          | none =>
              simp [h_parent, h_find, freshTag] at h_ref
          | some stack =>
              simp [h_parent, h_find, freshTag] at h_ref
              rcases h_ref with ⟨h_ok, h_tag⟩
              cases h_ok
              cases h_tag
              calc
                (SB.insert ap_parent.StackMap addr (RefKind.Ref ap_parent.NextTag :: stack)).find? addr2
                    = ap_parent.StackMap.find? addr2 := by
                      simpa using (SB.find?_insert_ne h_parent_valid.1 h_ne)
                _ = ap.StackMap.find? addr2 := h_parent_find
  | Mut =>
      unfold sb_ref at h_ref
      cases h_parent : sb_use_mb ap addr tag with
      | Err msg =>
          simp [h_parent] at h_ref
      | Ok ap_parent =>
          have h_parent_valid : SBValid ap_parent :=
            sb_use_mb_preserves_valid h_valid h_parent
          have h_parent_find :
              ap_parent.StackMap.find? addr2 = ap.StackMap.find? addr2 :=
            sb_use_mb_preserves_find_ne h_valid h_parent h_ne
          cases h_find : ap_parent.StackMap.find? addr with
          | none =>
              simp [h_parent, h_find, freshTag] at h_ref
          | some stack =>
              simp [h_parent, h_find, freshTag] at h_ref
              rcases h_ref with ⟨h_ok, h_tag⟩
              cases h_ok
              cases h_tag
              calc
                (SB.insert ap_parent.StackMap addr (RefKind.MutRef ap_parent.NextTag :: stack)).find? addr2
                    = ap_parent.StackMap.find? addr2 := by
                      simpa using (SB.find?_insert_ne h_parent_valid.1 h_ne)
                _ = ap.StackMap.find? addr2 := h_parent_find
  | Raw =>
      unfold sb_ref at h_ref
      cases h_parent : sb_use_mb ap addr tag with
      | Err msg =>
          simp [h_parent] at h_ref
      | Ok ap_parent =>
          have h_parent_valid : SBValid ap_parent :=
            sb_use_mb_preserves_valid h_valid h_parent
          have h_parent_find :
              ap_parent.StackMap.find? addr2 = ap.StackMap.find? addr2 :=
            sb_use_mb_preserves_find_ne h_valid h_parent h_ne
          cases h_find : ap_parent.StackMap.find? addr with
          | none =>
              simp [h_parent, h_find, freshTag] at h_ref
          | some stack =>
              simp [h_parent, h_find, freshTag] at h_ref
              rcases h_ref with ⟨h_ok, h_tag⟩
              cases h_ok
              cases h_tag
              calc
                (SB.insert ap_parent.StackMap addr (RefKind.RawPtr ap_parent.NextTag :: stack)).find? addr2
                    = ap_parent.StackMap.find? addr2 := by
                      simpa using (SB.find?_insert_ne h_parent_valid.1 h_ne)
                _ = ap.StackMap.find? addr2 := h_parent_find

theorem tag_live_of_sb_ref_new_after_use_of_addr_ne
  {ap ap_ref ap_use : AccessPerms}
  {srcAddr dstAddr srcTag dstTag newTag : Word}
  {kind : RefOpKind}
  (h_valid : SBValid ap)
  (h_ref : sb_ref ap srcAddr srcTag kind = (SBResult.Ok ap_ref, newTag))
  (h_use : sb_use_mb ap_ref dstAddr dstTag = SBResult.Ok ap_use)
  (h_ne : dstAddr ≠ srcAddr) :
  tag_live ap_use newTag := by
  have h_valid_ref : SBValid ap_ref := sb_ref_preserves_valid h_valid h_ref
  rcases sb_ref_new_stack_find h_ref with ⟨stack, h_find_ref⟩
  have h_find_use : ap_use.StackMap.find? srcAddr = some (kind.toStackKind newTag :: stack) := by
    rw [sb_use_mb_preserves_find_ne h_valid_ref h_use h_ne.symm]
    exact h_find_ref
  cases kind with
  | Shared =>
      have h_find_use' : ap_use.StackMap.find? srcAddr = some (RefKind.Ref newTag :: stack) := by
        simpa [RefOpKind.toStackKind] using h_find_use
      simpa [RefKind.tag, RefOpKind.toStackKind] using
        (tag_live_of_find_mem (k := RefKind.Ref newTag) h_find_use' (by simp))
  | Mut =>
      have h_find_use' : ap_use.StackMap.find? srcAddr = some (RefKind.MutRef newTag :: stack) := by
        simpa [RefOpKind.toStackKind] using h_find_use
      simpa [RefKind.tag, RefOpKind.toStackKind] using
        (tag_live_of_find_mem (k := RefKind.MutRef newTag) h_find_use' (by simp))
  | Raw =>
      have h_find_use' : ap_use.StackMap.find? srcAddr = some (RefKind.RawPtr newTag :: stack) := by
        simpa [RefOpKind.toStackKind] using h_find_use
      simpa [RefKind.tag, RefOpKind.toStackKind] using
        (tag_live_of_find_mem (k := RefKind.RawPtr newTag) h_find_use' (by simp))

theorem sb_use_mb_exists_of_find_eq
  {ap ap' ap_after : AccessPerms} {addr tag : Word}
  (h_find_eq : ap'.StackMap.find? addr = ap.StackMap.find? addr)
  (h_use : sb_use_mb ap addr tag = Ok ap_after) :
  ∃ ap_after',
    sb_use_mb ap' addr tag = Ok ap_after' ∧
    ap_after'.StackMap.find? addr = ap_after.StackMap.find? addr := by
  unfold sb_use_mb at h_use
  cases h_find : ap.StackMap.find? addr with
  | none =>
      simp [h_find] at h_use
  | some stack =>
      have h_find' : ap'.StackMap.find? addr = some stack := by
        simpa [h_find] using h_find_eq
      cases h_split : splitStack stack tag with
      | none =>
          simp [h_find, h_split] at h_use
      | some triple =>
          cases triple with
          | mk x rest =>
              cases rest with
              | mk item y =>
                  cases item with
                  | Own t =>
                      simp [h_find, h_split] at h_use
                      subst ap_after
                      let ap_after' : AccessPerms :=
                        { ap' with StackMap := ap'.StackMap.insert addr (RefKind.Own t :: y) }
                      refine ⟨ap_after', ?_, ?_⟩
                      · simp [sb_use_mb, h_find', h_split, ap_after']
                      · simp [ap_after']
                  | MutRef t =>
                      simp [h_find, h_split] at h_use
                      subst ap_after
                      let ap_after' : AccessPerms :=
                        { ap' with StackMap := ap'.StackMap.insert addr (RefKind.MutRef t :: y) }
                      refine ⟨ap_after', ?_, ?_⟩
                      · simp [sb_use_mb, h_find', h_split, ap_after']
                      · simp [ap_after']
                  | Ref t =>
                      simp [h_find, h_split] at h_use
                  | RawPtr t =>
                      simp [h_find, h_split] at h_use

theorem sb_die_exists_of_find_eq
  {ap ap' ap_after : AccessPerms} {addr tag : Word}
  (h_find_eq : ap'.StackMap.find? addr = ap.StackMap.find? addr)
  (h_die : sb_die ap addr tag = Ok ap_after) :
  ∃ ap_after',
    sb_die ap' addr tag = Ok ap_after' ∧
    ap_after'.StackMap.find? addr = ap_after.StackMap.find? addr := by
  unfold sb_die at h_die
  cases h_find : ap.StackMap.find? addr with
  | none =>
      simp [h_find] at h_die
  | some stack =>
      have h_find' : ap'.StackMap.find? addr = some stack := by
        simpa [h_find] using h_find_eq
      cases stack with
      | nil =>
          simp [h_find] at h_die
      | cons item y =>
          by_cases h_tag : item.tag == tag
          · cases item with
            | Own t =>
                simp [h_find, h_tag] at h_die
            | MutRef t =>
                simp [h_find, h_tag] at h_die
                subst ap_after
                let ap_after' : AccessPerms :=
                  { ap' with StackMap := ap'.StackMap.insert addr y }
                refine ⟨ap_after', ?_, ?_⟩
                · simp [sb_die, h_find', h_tag, ap_after']
                · simp [ap_after']
            | Ref t =>
                simp [h_find, h_tag] at h_die
                subst ap_after
                let ap_after' : AccessPerms :=
                  { ap' with StackMap := ap'.StackMap.insert addr y }
                refine ⟨ap_after', ?_, ?_⟩
                · simp [sb_die, h_find', h_tag, ap_after']
                · simp [ap_after']
            | RawPtr t =>
                simp [h_find, h_tag] at h_die
                subst ap_after
                let ap_after' : AccessPerms :=
                  { ap' with StackMap := ap'.StackMap.insert addr y }
                refine ⟨ap_after', ?_, ?_⟩
                · simp [sb_die, h_find', h_tag, ap_after']
                · simp [ap_after']
          · simp [h_find, h_tag] at h_die

theorem sb_ref_mut_read_unmapped_use_die_sim_ok
  {ρa : AddrRenameMap}
  {ρt : TagRenameMap}
  {ap_m ap_o ap_m' : AccessPerms}
  {dst_m dst_o src_o : Word}
  {dst_tag_m dst_tag_o src_tag_o : Word}
  (h_sim : sb_sim ρa ρt ap_m ap_o)
  (h_dst_addr : ρa dst_m = some dst_o)
  (h_dst_tag : ρt dst_tag_m = some dst_tag_o)
  (h_use_m : sb_use_mb ap_m dst_m dst_tag_m = Ok ap_m')
  (h_src_find : ap_o.StackMap.find? src_o = some [RefKind.Own src_tag_o])
  (h_src_unmapped : ∀ a, ρa a ≠ some src_o) :
  ∃ tempTag ap_ref_o ap_read_o ap_write_o ap_final_o,
    sb_ref ap_o dst_o dst_tag_o RefOpKind.Mut = (Ok ap_ref_o, tempTag) ∧
    sb_read ap_ref_o src_o src_tag_o = Ok ap_read_o ∧
    sb_use_mb ap_read_o dst_o tempTag = Ok ap_write_o ∧
    sb_die ap_write_o dst_o tempTag = Ok ap_final_o ∧
    sb_sim ρa ρt ap_m' ap_final_o := by
  let ⟨ap_parent_o, h_parent_use, h_sb_parent⟩ :=
    sb_use_mb_sim_ok h_sim h_dst_addr h_dst_tag h_use_m
  let ⟨tempTag, ap_ref_o, ap_use_parent_o, ap_final_parent_o,
      h_ref, h_use_parent, h_die_parent, h_stack_eq_parent⟩ :=
    sb_ref_mut_use_die_ok_of_use_ok h_parent_use
  have h_valid_o : SBValid ap_o := h_sim.valid_osea
  have h_valid_ref : SBValid ap_ref_o :=
    sb_ref_preserves_valid h_valid_o h_ref
  have h_valid_use_parent : SBValid ap_use_parent_o :=
    sb_use_mb_preserves_valid h_valid_ref h_use_parent
  have h_src_ne_dst : src_o ≠ dst_o := by
    intro h_eq
    exact h_src_unmapped dst_m (h_eq ▸ h_dst_addr)
  have h_src_find_ref : ap_ref_o.StackMap.find? src_o = some [RefKind.Own src_tag_o] := by
    exact (sb_ref_preserves_find_ne h_valid_o h_ref h_src_ne_dst).trans h_src_find
  obtain ⟨ap_read_o, h_read⟩ := sb_read_of_find_own h_src_find_ref
  have h_valid_read : SBValid ap_read_o :=
    sb_read_preserves_valid h_valid_ref h_read
  have h_find_dst_after_read :
      ap_read_o.StackMap.find? dst_o = ap_ref_o.StackMap.find? dst_o := by
    exact sb_read_preserves_find_ne h_valid_ref h_read h_src_ne_dst.symm
  obtain ⟨ap_write_o, h_use_read, h_find_dst_after_use⟩ :=
    sb_use_mb_exists_of_find_eq h_find_dst_after_read h_use_parent
  have h_valid_write : SBValid ap_write_o :=
    sb_use_mb_preserves_valid h_valid_read h_use_read
  obtain ⟨ap_final_o, h_die_read, h_find_dst_after_die⟩ :=
    sb_die_exists_of_find_eq h_find_dst_after_use h_die_parent
  have h_valid_final : SBValid ap_final_o :=
    sb_die_preserves_valid h_valid_write h_die_read
  have h_sb_final_parent : sb_sim ρa ρt ap_m' ap_final_parent_o :=
    sb_sim_of_right_stackMap_eq h_sb_parent h_stack_eq_parent
  have h_mapped_stackAt :
      ∀ addr addr', ρa addr = some addr' →
        stackAt ap_final_o addr' = stackAt ap_final_parent_o addr' := by
    intro addr addr' h_addr
    have h_ne_src : addr' ≠ src_o := by
      intro h_eq
      exact h_src_unmapped addr (h_eq ▸ h_addr)
    by_cases h_eq_dst : addr' = dst_o
    · exact stackAt_eq_of_find_eq (by simpa [h_eq_dst] using h_find_dst_after_die)
    · have h_final_find :
          ap_final_o.StackMap.find? addr' = ap_final_parent_o.StackMap.find? addr' := by
        have h_final_left :
            ap_final_o.StackMap.find? addr' = ap_o.StackMap.find? addr' := by
          calc
            ap_final_o.StackMap.find? addr' = ap_write_o.StackMap.find? addr' := by
              exact sb_die_preserves_find_ne h_valid_write h_die_read h_eq_dst
            _ = ap_read_o.StackMap.find? addr' := by
              exact sb_use_mb_preserves_find_ne h_valid_read h_use_read h_eq_dst
            _ = ap_ref_o.StackMap.find? addr' := by
              exact sb_read_preserves_find_ne h_valid_ref h_read h_ne_src
            _ = ap_o.StackMap.find? addr' := by
              exact sb_ref_preserves_find_ne h_valid_o h_ref h_eq_dst
        have h_final_right :
            ap_final_parent_o.StackMap.find? addr' = ap_o.StackMap.find? addr' := by
          calc
            ap_final_parent_o.StackMap.find? addr' = ap_use_parent_o.StackMap.find? addr' := by
              exact sb_die_preserves_find_ne h_valid_use_parent h_die_parent h_eq_dst
            _ = ap_ref_o.StackMap.find? addr' := by
              exact sb_use_mb_preserves_find_ne h_valid_ref h_use_parent h_eq_dst
            _ = ap_o.StackMap.find? addr' := by
              exact sb_ref_preserves_find_ne h_valid_o h_ref h_eq_dst
        exact h_final_left.trans h_final_right.symm
      exact stackAt_eq_of_find_eq h_final_find
  have h_sb_final : sb_sim ρa ρt ap_m' ap_final_o :=
    sb_sim_of_right_stackAt_eq h_sb_final_parent h_valid_final h_mapped_stackAt
  exact ⟨tempTag, ap_ref_o, ap_read_o, ap_write_o, ap_final_o,
    h_ref, h_read, h_use_read, h_die_read, h_sb_final⟩

end obseq
