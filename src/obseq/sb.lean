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
A StackedMap (SB) maps a memory location (Addr) to a permission stack.
--/
abbrev SB := List (Word × BorrowStack)

def SB.find? (sb : SB) (addr : Word) : Option BorrowStack :=
  match sb with
  | [] => none
  | (a, stack) :: rest => if a == addr then some stack else SB.find? rest addr

def SB.insortEntry (entry : Word × BorrowStack) : SB → SB
  | [] => [entry]
  | head :: rest =>
      if entry.1 <= head.1 then entry :: head :: rest
      else head :: SB.insortEntry entry rest

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

def StackTagsBounded (nextTag : Tag) (stack : BorrowStack) : Prop :=
  ∀ ⦃k : RefKind⦄, k ∈ stack → k.tag < nextTag

def SBAddrsUnique (sb : SB) : Prop :=
  ∀ ⦃addr : Word⦄ ⦃stack₁ stack₂ : BorrowStack⦄,
    (addr, stack₁) ∈ sb → (addr, stack₂) ∈ sb → stack₁ = stack₂

/--
`SBValid` is the minimal structural well-formedness invariant used by the local
`obseq` preservation proofs.

- stack-map addresses are unique,
- tags are unique within each per-address borrow stack,
- every tag in every stack is below `NextTag`.
-/
def SBValid (ap : AccessPerms) : Prop :=
  SBAddrsUnique ap.StackMap ∧
  ∀ ⦃addr : Word⦄ ⦃stack : BorrowStack⦄,
    (addr, stack) ∈ ap.StackMap →
      StackTagsUnique stack ∧ StackTagsBounded ap.NextTag stack

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
      · simp [SB.insortEntry, h_le, List.mem_cons, ih, or_assoc, or_left_comm, or_comm]

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

theorem SB.mem_insert_self
  (sb : SB) (addr : Word) (stack : BorrowStack) :
  (addr, stack) ∈ SB.insert sb addr stack := by
  unfold SB.insert
  apply (SB.mem_insortEntry).2
  exact Or.inl rfl

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

theorem SBValid_insert
  {ap : AccessPerms} {addr : Word} {stack : BorrowStack}
  (h_valid : SBValid ap)
  (h_stack_unique : StackTagsUnique stack)
  (h_stack_bounded : StackTagsBounded ap.NextTag stack) :
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
              exact ⟨h_stack_unique, h_stack_bounded⟩
      | inr h_old =>
          exact h_stacks h_old.1

theorem stack_props_of_subset
  {stack newStack : BorrowStack} {nextTag : Tag}
  (h_unique : StackTagsUnique stack)
  (h_bounded : StackTagsBounded nextTag stack)
  (h_subset : ∀ ⦃k : RefKind⦄, k ∈ newStack → k ∈ stack) :
  StackTagsUnique newStack ∧ StackTagsBounded nextTag newStack := by
  refine ⟨?_, ?_⟩
  · intro k₁ k₂ hk₁ hk₂ h_eq
    exact h_unique (h_subset hk₁) (h_subset hk₂) h_eq
  · intro k hk
    exact h_bounded (h_subset hk)

theorem SBValid_nextTag_succ
  {ap : AccessPerms}
  (h_valid : SBValid ap) :
  SBValid { ap with NextTag := ap.NextTag + 1 } := by
  cases h_valid with
  | intro h_addr_unique h_stack_valid =>
      refine ⟨h_addr_unique, ?_⟩
      intro addr stack h_mem
      have h_props := h_stack_valid h_mem
      cases h_props with
      | intro h_unique h_bounded =>
          refine ⟨h_unique, ?_⟩
          intro k hk
          exact Nat.lt_trans (h_bounded hk) (Nat.lt_succ_self ap.NextTag)

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

-- Rule: sb-use-rw
-- Premise: sb[a] = x ++ (g, r) :: y, ∀ kx \in x. kx = r
-- Conclusion: sb[a] unchanged
def sb_use_rw (ap : AccessPerms) (addr : Word) (tag : Tag) : SBResult :=
  match ap.StackMap.find? addr with
  | none => Err s!"sb-use-rw: address {addr} not found"
  | some stack =>
    match splitStack stack tag with
    | none => Err s!"sb-use-rw: tag {tag} not found in stack at {addr}"
    | some (x, item, _y) =>
      match item with
      | RefKind.RawPtr _ =>
        if x.all (fun k => k.isRaw) then Ok ap
        else Err s!"sb-use-rw: items above raw pointer {tag} are not all raw"
      | _ => Err s!"sb-use-rw: tag {tag} is not RawPtr"

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
                      have h_stack_props : StackTagsUnique stack ∧ StackTagsBounded ap.NextTag stack := by
                        cases h_valid with
                        | intro _ h_stack_valid =>
                            exact h_stack_valid h_mem_stack
                      cases h_stack_props with
                      | intro h_tags_unique h_tags_bounded =>
                          have h_new_mem :
                              ∀ ⦃k : RefKind⦄, k ∈ RefKind.Own t :: y → k ∈ stack := by
                            intro k hk
                            exact splitStack_result_mem h_split hk
                          refine SBValid_insert h_valid ?_ ?_
                          · intro k₁ k₂ hk₁ hk₂ h_eq
                            apply h_tags_unique
                            · exact h_new_mem hk₁
                            · exact h_new_mem hk₂
                            · exact h_eq
                          · intro k hk
                            exact h_tags_bounded (h_new_mem hk)
                  | MutRef t =>
                      simp [h_find, h_split] at h_use
                      subst ap'
                      have h_mem_stack : (addr, stack) ∈ ap.StackMap :=
                        SB.find?_some_mem h_find
                      have h_stack_props : StackTagsUnique stack ∧ StackTagsBounded ap.NextTag stack := by
                        cases h_valid with
                        | intro _ h_stack_valid =>
                            exact h_stack_valid h_mem_stack
                      cases h_stack_props with
                      | intro h_tags_unique h_tags_bounded =>
                          have h_new_mem :
                              ∀ ⦃k : RefKind⦄, k ∈ RefKind.MutRef t :: y → k ∈ stack := by
                            intro k hk
                            exact splitStack_result_mem h_split hk
                          refine SBValid_insert h_valid ?_ ?_
                          · intro k₁ k₂ hk₁ hk₂ h_eq
                            apply h_tags_unique
                            · exact h_new_mem hk₁
                            · exact h_new_mem hk₂
                            · exact h_eq
                          · intro k hk
                            exact h_tags_bounded (h_new_mem hk)
                  | Ref t =>
                      simp [h_find, h_split] at h_use
                  | RawPtr t =>
                      simp [h_find, h_split] at h_use

theorem sb_own_preserves_valid
  {ap ap' : AccessPerms} {addr tag : Word}
  (h_valid : SBValid ap)
  (h_own : sb_own ap addr = (Ok ap', tag)) :
  SBValid ap' := by
  unfold sb_own at h_own
  cases h_find : ap.StackMap.find? addr with
  | none =>
      simp [h_find, freshTag] at h_own
      cases h_own with
      | intro h_ap h_tag =>
          subst ap'
          subst tag
          have h_valid' : SBValid { ap with NextTag := ap.NextTag + 1 } :=
            SBValid_nextTag_succ h_valid
          have h_insert :
              SBValid
                ({ { ap with NextTag := ap.NextTag + 1 } with
                  StackMap := SB.insert ({ ap with NextTag := ap.NextTag + 1 }).StackMap
                    addr [RefKind.Own ap.NextTag] }) := by
            refine SBValid_insert (ap := { ap with NextTag := ap.NextTag + 1 })
              (addr := addr) (stack := [RefKind.Own ap.NextTag]) h_valid' ?_ ?_
            · intro k₁ k₂ hk₁ hk₂ h_eq
              cases hk₁ with
              | head =>
                  cases hk₂ with
                  | head =>
                      rfl
                  | tail _ hk₂_tail =>
                      cases hk₂_tail
              | tail _ hk₁_tail =>
                  cases hk₁_tail
            · intro k hk
              cases hk with
              | head =>
                  exact Nat.lt_succ_self ap.NextTag
              | tail _ hk_tail =>
                  cases hk_tail
          exact h_insert
  | some stack =>
      cases stack with
      | nil =>
          simp [h_find, freshTag] at h_own
          cases h_own with
          | intro h_ap h_tag =>
              subst ap'
              subst tag
              have h_valid' : SBValid { ap with NextTag := ap.NextTag + 1 } :=
                SBValid_nextTag_succ h_valid
              have h_insert :
                  SBValid
                    ({ { ap with NextTag := ap.NextTag + 1 } with
                      StackMap := SB.insert ({ ap with NextTag := ap.NextTag + 1 }).StackMap
                        addr [RefKind.Own ap.NextTag] }) := by
                refine SBValid_insert (ap := { ap with NextTag := ap.NextTag + 1 })
                  (addr := addr) (stack := [RefKind.Own ap.NextTag]) h_valid' ?_ ?_
                · intro k₁ k₂ hk₁ hk₂ h_eq
                  cases hk₁ with
                  | head =>
                      cases hk₂ with
                      | head =>
                          rfl
                      | tail _ hk₂_tail =>
                          cases hk₂_tail
                  | tail _ hk₁_tail =>
                      cases hk₁_tail
                · intro k hk
                  cases hk with
                  | head =>
                      exact Nat.lt_succ_self ap.NextTag
                  | tail _ hk_tail =>
                      cases hk_tail
              exact h_insert
      | cons hd tl =>
          simp [h_find] at h_own

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
                  have h_stack_props : StackTagsUnique stack ∧ StackTagsBounded ap.NextTag stack := by
                    cases h_valid with
                    | intro _ h_stack_valid =>
                        exact h_stack_valid h_mem_stack
                  cases h_stack_props with
                  | intro h_tags_unique h_tags_bounded =>
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
                      cases item with
                      | Own t =>
                          simp [h_find, h_split] at h_read
                          subst ap'
                          have h_new_props :=
                            stack_props_of_subset h_tags_unique h_tags_bounded h_subset
                          cases h_new_props with
                          | intro h_new_unique h_new_bounded =>
                              have h_insert :
                                  SBValid
                                    { ap with
                                      StackMap := SB.insert ap.StackMap addr
                                        (x.filter (fun k => !k.isMb) ++ RefKind.Own t :: y) } :=
                                SBValid_insert (ap := ap) (addr := addr)
                                  (stack := x.filter (fun k => !k.isMb) ++ RefKind.Own t :: y)
                                  h_valid h_new_unique h_new_bounded
                              exact h_insert
                      | MutRef t =>
                          simp [h_find, h_split] at h_read
                          subst ap'
                          have h_new_props :=
                            stack_props_of_subset h_tags_unique h_tags_bounded h_subset
                          cases h_new_props with
                          | intro h_new_unique h_new_bounded =>
                              have h_insert :
                                  SBValid
                                    { ap with
                                      StackMap := SB.insert ap.StackMap addr
                                        (x.filter (fun k => !k.isMb) ++ RefKind.MutRef t :: y) } :=
                                SBValid_insert (ap := ap) (addr := addr)
                                  (stack := x.filter (fun k => !k.isMb) ++ RefKind.MutRef t :: y)
                                  h_valid h_new_unique h_new_bounded
                              exact h_insert
                      | Ref t =>
                          simp [h_find, h_split] at h_read
                          subst ap'
                          have h_new_props :=
                            stack_props_of_subset h_tags_unique h_tags_bounded h_subset
                          cases h_new_props with
                          | intro h_new_unique h_new_bounded =>
                              have h_insert :
                                  SBValid
                                    { ap with
                                      StackMap := SB.insert ap.StackMap addr
                                        (x.filter (fun k => !k.isMb) ++ RefKind.Ref t :: y) } :=
                                SBValid_insert (ap := ap) (addr := addr)
                                  (stack := x.filter (fun k => !k.isMb) ++ RefKind.Ref t :: y)
                                  h_valid h_new_unique h_new_bounded
                              exact h_insert
                      | RawPtr t =>
                          simp [h_find, h_split] at h_read
                          subst ap'
                          have h_new_props :=
                            stack_props_of_subset h_tags_unique h_tags_bounded h_subset
                          cases h_new_props with
                          | intro h_new_unique h_new_bounded =>
                              have h_insert :
                                  SBValid
                                    { ap with
                                      StackMap := SB.insert ap.StackMap addr
                                        (x.filter (fun k => !k.isMb) ++ RefKind.RawPtr t :: y) } :=
                                SBValid_insert (ap := ap) (addr := addr)
                                  (stack := x.filter (fun k => !k.isMb) ++ RefKind.RawPtr t :: y)
                                  h_valid h_new_unique h_new_bounded
                              exact h_insert

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

abbrev AddrRenaming := Word → Option Word
abbrev TagRenaming := Tag → Option Tag

def extendAddrRenaming (ρa : AddrRenaming) (src dst : Word) : AddrRenaming :=
  fun addr => if addr = src then some dst else ρa addr

def extendTagRenaming (ρt : TagRenaming) (src dst : Tag) : TagRenaming :=
  fun tag => if tag = src then some dst else ρt tag

def stackAt (ap : AccessPerms) (addr : Word) : BorrowStack :=
  Option.getD (SB.find? ap.StackMap addr) []

def refkind_sim (ρt : TagRenaming) : RefKind → RefKind → Prop
  | RefKind.Own t, RefKind.Own t' => ρt t = some t'
  | RefKind.MutRef t, RefKind.MutRef t' => ρt t = some t'
  | RefKind.Ref t, RefKind.Ref t' => ρt t = some t'
  | RefKind.RawPtr t, RefKind.RawPtr t' => ρt t = some t'
  | _, _ => False

def stack_sim (ρt : TagRenaming) : BorrowStack → BorrowStack → Prop
  | [], [] => True
  | k :: ks, k' :: ks' => refkind_sim ρt k k' ∧ stack_sim ρt ks ks'
  | _, _ => False

def sb_at_sim (ρt : TagRenaming) (ap_m ap_o : AccessPerms) (addr addr' : Word) : Prop :=
  stack_sim ρt (stackAt ap_m addr) (stackAt ap_o addr')

def stack_tag_live (stack : BorrowStack) (tag : Tag) : Prop :=
  ∃ k : RefKind, k ∈ stack ∧ k.tag = tag

def tag_live (ap : AccessPerms) (tag : Tag) : Prop :=
  ∃ addr, stack_tag_live (stackAt ap addr) tag

/--
Live tags are globally unique across the current stacked-borrows state.

This is stronger than per-stack uniqueness: if two live stack items share a tag,
they must be the very same item in the very same allocation stack.
-/
def LiveTagUnique (ap : AccessPerms) : Prop :=
  ∀ {addr₁ addr₂ : Word} {k₁ k₂ : RefKind},
    k₁ ∈ stackAt ap addr₁ →
    k₂ ∈ stackAt ap addr₂ →
    k₁.tag = k₂.tag →
    addr₁ = addr₂ ∧ k₁ = k₂

structure SbSimData
  (ρa : AddrRenaming)
  (ρt : TagRenaming)
  (ap_m ap_o : AccessPerms) : Prop where
  valid_mir : SBValid ap_m
  valid_osea : SBValid ap_o
  at_sim : ∀ addr addr', ρa addr = some addr' → sb_at_sim ρt ap_m ap_o addr addr'
  tag_mapped : ∀ tag, tag_live ap_m tag → ∃ tag', ρt tag = some tag'
  tag_inj :
    ∀ tag₁ tag₂ tag',
      tag_live ap_m tag₁ →
      tag_live ap_m tag₂ →
      ρt tag₁ = some tag' →
      ρt tag₂ = some tag' →
      tag₁ = tag₂

def sb_sim
  (ρa : AddrRenaming)
  (ρt : TagRenaming)
  (ap_m ap_o : AccessPerms) : Prop :=
  SbSimData ρa ρt ap_m ap_o

namespace SbSim

theorem valid_mir
  {ρa : AddrRenaming} {ρt : TagRenaming} {ap_m ap_o : AccessPerms}
  (h : sb_sim ρa ρt ap_m ap_o) :
  SBValid ap_m :=
  h.valid_mir

theorem valid_osea
  {ρa : AddrRenaming} {ρt : TagRenaming} {ap_m ap_o : AccessPerms}
  (h : sb_sim ρa ρt ap_m ap_o) :
  SBValid ap_o :=
  h.valid_osea

theorem at_sim
  {ρa : AddrRenaming} {ρt : TagRenaming} {ap_m ap_o : AccessPerms}
  (h : sb_sim ρa ρt ap_m ap_o)
  {addr addr' : Word}
  (h_addr : ρa addr = some addr') :
  sb_at_sim ρt ap_m ap_o addr addr' :=
  h.at_sim addr addr' h_addr

theorem map_tag
  {ρa : AddrRenaming} {ρt : TagRenaming} {ap_m ap_o : AccessPerms}
  (h : sb_sim ρa ρt ap_m ap_o)
  {tag : Tag}
  (h_live : tag_live ap_m tag) :
  ∃ tag', ρt tag = some tag' :=
  h.tag_mapped tag h_live

theorem inj
  {ρa : AddrRenaming} {ρt : TagRenaming} {ap_m ap_o : AccessPerms}
  (h : sb_sim ρa ρt ap_m ap_o)
  {tag₁ tag₂ tag' : Tag}
  (h_live₁ : tag_live ap_m tag₁)
  (h_live₂ : tag_live ap_m tag₂)
  (h_map₁ : ρt tag₁ = some tag')
  (h_map₂ : ρt tag₂ = some tag') :
  tag₁ = tag₂ :=
  h.tag_inj tag₁ tag₂ tag' h_live₁ h_live₂ h_map₁ h_map₂

end SbSim

@[simp] theorem extendAddrRenaming_self
  (ρa : AddrRenaming) (src dst : Word) :
  extendAddrRenaming ρa src dst src = some dst := by
  simp [extendAddrRenaming]

@[simp] theorem extendAddrRenaming_ne
  (ρa : AddrRenaming) (src dst addr : Word)
  (h_ne : addr ≠ src) :
  extendAddrRenaming ρa src dst addr = ρa addr := by
  simp [extendAddrRenaming, h_ne]

@[simp] theorem extendTagRenaming_self
  (ρt : TagRenaming) (src dst : Tag) :
  extendTagRenaming ρt src dst src = some dst := by
  simp [extendTagRenaming]

@[simp] theorem extendTagRenaming_ne
  (ρt : TagRenaming) (src dst tag : Tag)
  (h_ne : tag ≠ src) :
  extendTagRenaming ρt src dst tag = ρt tag := by
  simp [extendTagRenaming, h_ne]

theorem refkind_sim_tag
  {ρt : TagRenaming} {k k' : RefKind}
  (h : refkind_sim ρt k k') :
  ρt k.tag = some k'.tag := by
  cases k <;> cases k' <;> simpa [refkind_sim, RefKind.tag] using h

theorem refkind_sim_isMb
  {ρt : TagRenaming} {k k' : RefKind}
  (h : refkind_sim ρt k k') :
  k.isMb = k'.isMb := by
  cases k <;> cases k' <;> simp [refkind_sim, RefKind.isMb] at h ⊢

theorem refkind_sim_isRaw
  {ρt : TagRenaming} {k k' : RefKind}
  (h : refkind_sim ρt k k') :
  k.isRaw = k'.isRaw := by
  cases k <;> cases k' <;> simp [refkind_sim, RefKind.isRaw] at h ⊢

theorem stack_sim_append
  {ρt : TagRenaming}
  {xs xs' ys ys' : BorrowStack}
  (h_xs : stack_sim ρt xs xs')
  (h_ys : stack_sim ρt ys ys') :
  stack_sim ρt (xs ++ ys) (xs' ++ ys') := by
  revert xs' h_xs
  induction xs with
  | nil =>
      intro xs' h_xs
      cases xs' <;> simp [stack_sim] at h_xs ⊢
      simpa [stack_sim] using h_ys
  | cons x xs ih =>
      intro xs' h_xs
      cases xs' with
      | nil =>
          simp [stack_sim] at h_xs
      | cons x' xs' =>
          cases h_xs with
          | intro h_head h_tail =>
              simp [stack_sim]
              exact ⟨h_head, ih h_tail⟩

theorem stack_sim_nonempty_right
  {ρt : TagRenaming}
  {stack stack' : BorrowStack}
  (h : stack_sim ρt stack stack')
  (h_nonempty : stack ≠ []) :
  stack' ≠ [] := by
  cases stack <;> cases stack' <;> simp [stack_sim] at h h_nonempty ⊢

theorem stack_sim_filter_not_mb
  {ρt : TagRenaming}
  {stack stack' : BorrowStack}
  (h : stack_sim ρt stack stack') :
  stack_sim ρt (stack.filter (fun k => !k.isMb)) (stack'.filter (fun k => !k.isMb)) := by
  induction stack generalizing stack' with
  | nil =>
      cases stack' <;> simp [stack_sim] at h ⊢
  | cons head tail ih =>
      cases stack' with
      | nil =>
          simp [stack_sim] at h
      | cons head' tail' =>
          have h_head := h.1
          have h_tail := h.2
          have h_mb : head.isMb = head'.isMb := refkind_sim_isMb h_head
          by_cases h_keep : (!head.isMb) = true
          · have h_keep' : (!head'.isMb) = true := by simpa [h_mb] using h_keep
            simp [List.filter, h_keep, h_keep', stack_sim, h_head, ih h_tail]
          · have h_keep' : (!head'.isMb) = false := by simpa [h_mb] using h_keep
            simp [List.filter, h_keep, h_keep', ih h_tail]

theorem splitStack_found_tag
  {stack : BorrowStack} {tag : Tag} {x : BorrowStack} {item : RefKind} {y : BorrowStack}
  (h : splitStack stack tag = some (x, item, y)) :
  item.tag = tag := by
  induction stack generalizing x item y with
  | nil =>
      simp [splitStack] at h
  | cons head tail ih =>
      by_cases h_head : head.tag == tag
      · simp [splitStack, h_head] at h
        rcases h with ⟨rfl, rfl, rfl⟩
        exact LawfulBEq.eq_of_beq h_head
      · cases h_tail : splitStack tail tag with
        | none =>
            simp [splitStack, h_head, h_tail] at h
        | some triple =>
            cases triple with
            | mk x' rest =>
                cases rest with
                | mk item' y' =>
                    simp [splitStack, h_head, h_tail] at h
                    rcases h with ⟨rfl, rfl, rfl⟩
                    exact ih h_tail

theorem stack_sim_split
  {ρt : TagRenaming}
  {stack stack' : BorrowStack}
  {tag tag' : Tag}
  {x : BorrowStack} {item : RefKind} {y : BorrowStack}
  (h_sim : stack_sim ρt stack stack')
  (h_unique_tgt : StackTagsUnique stack')
  (h_tag_inj :
    ∀ {k₁ k₂ : RefKind} {mapped : Tag},
      k₁ ∈ stack →
      k₂ ∈ stack →
      ρt k₁.tag = some mapped →
      ρt k₂.tag = some mapped →
      k₁.tag = k₂.tag)
  (h_tag : ρt tag = some tag')
  (h_split : splitStack stack tag = some (x, item, y)) :
  ∃ x' item' y',
    splitStack stack' tag' = some (x', item', y') ∧
    stack_sim ρt x x' ∧
    refkind_sim ρt item item' ∧
    stack_sim ρt y y' := by
  induction stack generalizing stack' x item y with
  | nil =>
      simp [splitStack] at h_split
  | cons head tail ih =>
      cases stack' with
      | nil =>
          simp [stack_sim] at h_sim
      | cons head' tail' =>
          simp [stack_sim] at h_sim
          rcases h_sim with ⟨h_head_sim, h_tail_sim⟩
          by_cases h_head : head.tag == tag
          · simp [splitStack, h_head] at h_split
            rcases h_split with ⟨rfl, rfl, rfl⟩
            have h_head_eq : head.tag = tag := LawfulBEq.eq_of_beq h_head
            have h_head'_map : ρt head.tag = some head'.tag := refkind_sim_tag h_head_sim
            have h_head'_eq : head'.tag = tag' := by
              rw [h_head_eq] at h_head'_map
              have h_eq : some tag' = some head'.tag := h_tag.symm.trans h_head'_map
              exact (Option.some.inj h_eq).symm
            refine ⟨[], head', tail', ?_, by simp [stack_sim], h_head_sim, h_tail_sim⟩
            simp [splitStack, h_head'_eq]
          · have h_unique_tgt_tail : StackTagsUnique tail' := by
              intro k₁ k₂ hk₁ hk₂ h_eq
              exact h_unique_tgt (List.Mem.tail _ hk₁) (List.Mem.tail _ hk₂) h_eq
            have h_tag_inj_tail :
                ∀ {k₁ k₂ : RefKind} {mapped : Tag},
                  k₁ ∈ tail →
                  k₂ ∈ tail →
                  ρt k₁.tag = some mapped →
                  ρt k₂.tag = some mapped →
                  k₁.tag = k₂.tag := by
              intro k₁ k₂ mapped hk₁ hk₂ h_map₁ h_map₂
              exact h_tag_inj (List.Mem.tail _ hk₁) (List.Mem.tail _ hk₂) h_map₁ h_map₂
            cases h_tail : splitStack tail tag with
            | none =>
                simp [splitStack, h_head, h_tail] at h_split
            | some triple =>
                cases triple with
                | mk x0 rest =>
                    cases rest with
                    | mk item0 y0 =>
                        simp [splitStack, h_head, h_tail] at h_split
                        rcases h_split with ⟨rfl, rfl, rfl⟩
                        have h_ih :=
                          ih (stack' := tail') (x := x0) (item := item0) (y := y0)
                            h_tail_sim h_unique_tgt_tail h_tag_inj_tail h_tail
                        rcases h_ih with
                          ⟨x', item', y', h_split', h_x, h_item, h_y⟩
                        have h_item_tag : item0.tag = tag := splitStack_found_tag h_tail
                        have h_item'_map : ρt item0.tag = some item'.tag := refkind_sim_tag h_item
                        have h_item'_eq : item'.tag = tag' := by
                          rw [h_item_tag] at h_item'_map
                          have h_eq : some tag' = some item'.tag := h_tag.symm.trans h_item'_map
                          exact (Option.some.inj h_eq).symm
                        have h_head'_ne : head'.tag ≠ tag' := by
                          intro h_eq
                          have h_item_mem_tail : item' ∈ tail' :=
                            splitStack_result_mem h_split' (List.Mem.head _)
                          have h_same_item : head' = item' := by
                            apply h_unique_tgt
                            · exact List.Mem.head _
                            · exact List.Mem.tail _ h_item_mem_tail
                            · exact h_eq.trans h_item'_eq.symm
                          have h_head_map : ρt head.tag = some tag' := by
                            have h_map := refkind_sim_tag h_head_sim
                            simpa [h_same_item, h_item'_eq] using h_map
                          have h_item_mem : item0 ∈ head :: tail :=
                            splitStack_result_mem (stack := head :: tail) (tag := tag)
                              (x := head :: x0) (item := item0) (y := y0)
                              (by simp [splitStack, h_head, h_tail]) (List.Mem.head _)
                          have h_head_mem : head ∈ head :: tail := List.Mem.head _
                          have h_same_item_tag : head.tag = item0.tag :=
                            h_tag_inj h_head_mem h_item_mem h_head_map
                              (by simpa [h_item_tag, h_item'_eq] using h_item'_map)
                          have h_same_tag : head.tag = tag := h_same_item_tag.trans h_item_tag
                          have : False := by simpa [h_same_tag] using h_head
                          exact this.elim
                        refine ⟨head' :: x', item', y', ?_, ?_, h_item, h_y⟩
                        · simp [splitStack, h_head'_ne, h_split']
                        · exact ⟨h_head_sim, h_x⟩

theorem stack_tag_live_of_mem
  {stack : BorrowStack} {k : RefKind}
  (h_mem : k ∈ stack) :
  stack_tag_live stack k.tag := by
  exact ⟨k, h_mem, rfl⟩

theorem tag_live_of_stack_mem
  {ap : AccessPerms} {addr : Word} {k : RefKind}
  (h_mem : k ∈ stackAt ap addr) :
  tag_live ap k.tag := by
  exact ⟨addr, k, h_mem, rfl⟩

theorem stackAt_nonempty_find
  {ap : AccessPerms} {addr : Word} {stack : BorrowStack}
  (h_stack : stackAt ap addr = stack)
  (h_nonempty : stack ≠ []) :
  ap.StackMap.find? addr = some stack := by
  unfold stackAt at h_stack
  cases h_find : SB.find? ap.StackMap addr with
  | none =>
      simp [h_find] at h_stack
      contradiction
  | some stack' =>
      simp [h_find] at h_stack
      simpa [h_stack] using h_find

theorem stack_tag_live_bounded
  {stack : BorrowStack} {nextTag tag : Tag}
  (h_bounded : StackTagsBounded nextTag stack)
  (h_live : stack_tag_live stack tag) :
  tag < nextTag := by
  rcases h_live with ⟨k, hk, rfl⟩
  exact h_bounded hk

theorem tag_live_bounded
  {ap : AccessPerms} {tag : Tag}
  (h_valid : SBValid ap)
  (h_live : tag_live ap tag) :
  tag < ap.NextTag := by
  rcases h_live with ⟨addr, k, hk, rfl⟩
  have h_find : SB.find? ap.StackMap addr = some (stackAt ap addr) := by
    apply stackAt_nonempty_find (ap := ap) (addr := addr)
    · rfl
    · intro h_nil
      rw [h_nil] at hk
      cases hk
  cases h_valid with
  | intro _ h_stacks =>
      exact (h_stacks (SB.find?_some_mem h_find)).2 hk

theorem freshTag_not_live
  {ap : AccessPerms}
  (h_valid : SBValid ap) :
  ¬ tag_live ap ap.NextTag := by
  intro h_live
  exact Nat.lt_irrefl _ (tag_live_bounded h_valid h_live)

theorem SB.find?_insert_ne
  {sb : SB} {insertAddr addr : Word} {stack : BorrowStack}
  (h_unique : SBAddrsUnique sb)
  (h_ne : addr ≠ insertAddr) :
  SB.find? (SB.insert sb insertAddr stack) addr = SB.find? sb addr := by
  cases h_find : SB.find? sb addr with
  | none =>
      apply SB.find?_none_of_not_mem
      intro stack' h_mem
      have h_cases := SB.mem_insert_cases h_mem
      cases h_cases with
      | inl h_new =>
          exact h_ne h_new.1
      | inr h_old =>
          have h_old_find := SB.find?_of_mem_unique h_unique h_old.1
          rw [h_find] at h_old_find
          cases h_old_find
  | some stack0 =>
      have h_mem : (addr, stack0) ∈ sb := SB.find?_some_mem h_find
      have h_mem' : (addr, stack0) ∈ SB.insert sb insertAddr stack :=
        SB.mem_insert_of_mem_ne h_mem h_ne
      exact SB.find?_of_mem_unique (SBAddrsUnique_insert h_unique) h_mem'

@[simp] theorem stackAt_insert_eq
  (ap : AccessPerms) (addr : Word) (stack : BorrowStack) :
  stackAt { ap with StackMap := SB.insert ap.StackMap addr stack } addr = stack := by
  unfold stackAt
  simp [SB.find?_insert_eq]

@[simp] theorem stackAt_insert_ne
  (ap : AccessPerms) (insertAddr addr : Word) (stack : BorrowStack)
  (h_valid : SBValid ap)
  (h_ne : addr ≠ insertAddr) :
  stackAt { ap with StackMap := SB.insert ap.StackMap insertAddr stack } addr = stackAt ap addr := by
  unfold stackAt
  rw [SB.find?_insert_ne (sb := ap.StackMap) (insertAddr := insertAddr) (addr := addr)
    (stack := stack) h_valid.1 h_ne]

theorem liveTagUnique_nextTag
  {ap : AccessPerms}
  (h_unique : LiveTagUnique ap) :
  LiveTagUnique { ap with NextTag := ap.NextTag + 1 } := by
  intro addr₁ addr₂ k₁ k₂ hk₁ hk₂ h_tag
  exact h_unique hk₁ hk₂ h_tag

theorem liveTagUnique_insert_subset
  {ap : AccessPerms}
  {addr : Word}
  {newStack : BorrowStack}
  (h_valid : SBValid ap)
  (h_unique : LiveTagUnique ap)
  (h_subset : ∀ {k : RefKind}, k ∈ newStack → k ∈ stackAt ap addr) :
  LiveTagUnique { ap with StackMap := SB.insert ap.StackMap addr newStack } := by
  intro addr₁ addr₂ k₁ k₂ hk₁ hk₂ h_tag
  by_cases h₁ : addr₁ = addr
  · subst addr₁
    by_cases h₂ : addr₂ = addr
    · subst addr₂
      have hk₁_new : k₁ ∈ newStack := by simpa [stackAt_insert_eq] using hk₁
      have hk₂_new : k₂ ∈ newStack := by simpa [stackAt_insert_eq] using hk₂
      have hk₁_old : k₁ ∈ stackAt ap addr := h_subset hk₁_new
      have hk₂_old : k₂ ∈ stackAt ap addr := h_subset hk₂_new
      have h_old := h_unique hk₁_old hk₂_old h_tag
      exact ⟨rfl, h_old.2⟩
    · have hk₁_new : k₁ ∈ newStack := by simpa [stackAt_insert_eq] using hk₁
      have hk₁_old : k₁ ∈ stackAt ap addr := h_subset hk₁_new
      have hk₂_old : k₂ ∈ stackAt ap addr₂ := by
        rw [stackAt_insert_ne _ _ _ _ h_valid h₂] at hk₂
        exact hk₂
      exact h_unique hk₁_old hk₂_old h_tag
  · by_cases h₂ : addr₂ = addr
    · subst addr₂
      have hk₁_old : k₁ ∈ stackAt ap addr₁ := by
        rw [stackAt_insert_ne _ _ _ _ h_valid h₁] at hk₁
        exact hk₁
      have hk₂_new : k₂ ∈ newStack := by simpa [stackAt_insert_eq] using hk₂
      have hk₂_old : k₂ ∈ stackAt ap addr := h_subset hk₂_new
      exact h_unique hk₁_old hk₂_old h_tag
    · have hk₁_old : k₁ ∈ stackAt ap addr₁ := by
        rw [stackAt_insert_ne _ _ _ _ h_valid h₁] at hk₁
        exact hk₁
      have hk₂_old : k₂ ∈ stackAt ap addr₂ := by
        rw [stackAt_insert_ne _ _ _ _ h_valid h₂] at hk₂
        exact hk₂
      exact h_unique hk₁_old hk₂_old h_tag

theorem liveTagUnique_insert_fresh_head
  {ap : AccessPerms}
  {addr : Word}
  {newItem : RefKind}
  (h_valid : SBValid ap)
  (h_unique : LiveTagUnique ap)
  (h_fresh : ¬ tag_live ap newItem.tag) :
  LiveTagUnique
    { ap with
      StackMap := SB.insert ap.StackMap addr (newItem :: stackAt ap addr) } := by
  intro addr₁ addr₂ k₁ k₂ hk₁ hk₂ h_tag
  by_cases h₁ : addr₁ = addr
  · subst addr₁
    by_cases h₂ : addr₂ = addr
    · subst addr₂
      have hk₁_new : k₁ ∈ newItem :: stackAt ap addr := by
        simpa [stackAt_insert_eq] using hk₁
      have hk₂_new : k₂ ∈ newItem :: stackAt ap addr := by
        simpa [stackAt_insert_eq] using hk₂
      have hk₁_cases : k₁ = newItem ∨ k₁ ∈ stackAt ap addr := by
        simpa using hk₁_new
      have hk₂_cases : k₂ = newItem ∨ k₂ ∈ stackAt ap addr := by
        simpa using hk₂_new
      cases hk₁_cases with
      | inl hk₁_eq =>
          cases hk₂_cases with
          | inl hk₂_eq =>
              exact ⟨rfl, hk₁_eq.trans hk₂_eq.symm⟩
          | inr hk₂_old =>
              exfalso
              have h_tag' : newItem.tag = k₂.tag := by simpa [hk₁_eq] using h_tag
              exact h_fresh (by simpa [h_tag'] using tag_live_of_stack_mem (ap := ap) (addr := addr) hk₂_old)
      | inr hk₁_old =>
          cases hk₂_cases with
          | inl hk₂_eq =>
              exfalso
              have h_tag' : newItem.tag = k₁.tag := by simpa [hk₂_eq] using h_tag.symm
              exact h_fresh (by simpa [h_tag'] using tag_live_of_stack_mem (ap := ap) (addr := addr) hk₁_old)
          | inr hk₂_old =>
              have h_old := h_unique hk₁_old hk₂_old h_tag
              exact ⟨rfl, h_old.2⟩
    · have hk₁_new : k₁ ∈ newItem :: stackAt ap addr := by
        simpa [stackAt_insert_eq] using hk₁
      have hk₂_old : k₂ ∈ stackAt ap addr₂ := by
        rw [stackAt_insert_ne _ _ _ _ h_valid h₂] at hk₂
        exact hk₂
      have hk₁_cases : k₁ = newItem ∨ k₁ ∈ stackAt ap addr := by
        simpa using hk₁_new
      cases hk₁_cases with
      | inl hk₁_eq =>
          exfalso
          have h_tag' : newItem.tag = k₂.tag := by simpa [hk₁_eq] using h_tag
          exact h_fresh (by simpa [h_tag'] using tag_live_of_stack_mem (ap := ap) (addr := addr₂) hk₂_old)
      | inr hk₁_old =>
          exact h_unique hk₁_old hk₂_old h_tag
  · by_cases h₂ : addr₂ = addr
    · subst addr₂
      have hk₁_old : k₁ ∈ stackAt ap addr₁ := by
        rw [stackAt_insert_ne _ _ _ _ h_valid h₁] at hk₁
        exact hk₁
      have hk₂_new : k₂ ∈ newItem :: stackAt ap addr := by
        simpa [stackAt_insert_eq] using hk₂
      have hk₂_cases : k₂ = newItem ∨ k₂ ∈ stackAt ap addr := by
        simpa using hk₂_new
      cases hk₂_cases with
      | inl hk₂_eq =>
          exfalso
          have h_tag' : newItem.tag = k₁.tag := by simpa [hk₂_eq] using h_tag.symm
          exact h_fresh (by simpa [h_tag'] using tag_live_of_stack_mem (ap := ap) (addr := addr₁) hk₁_old)
      | inr hk₂_old =>
          exact h_unique hk₁_old hk₂_old h_tag
    · have hk₁_old : k₁ ∈ stackAt ap addr₁ := by
        rw [stackAt_insert_ne _ _ _ _ h_valid h₁] at hk₁
        exact hk₁
      have hk₂_old : k₂ ∈ stackAt ap addr₂ := by
        rw [stackAt_insert_ne _ _ _ _ h_valid h₂] at hk₂
        exact hk₂
      exact h_unique hk₁_old hk₂_old h_tag

theorem sb_read_preserves_liveTagUnique
  {ap ap' : AccessPerms} {addr tag : Word}
  (h_valid : SBValid ap)
  (h_unique : LiveTagUnique ap)
  (h_read : sb_read ap addr tag = Ok ap') :
  LiveTagUnique ap' := by
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
                  let newStack := x.filter (fun k => !k.isMb) ++ item :: y
                  have h_stack_eq : stack = x ++ item :: y :=
                    splitStack_eq_append h_split
                  have h_subset :
                      ∀ {k : RefKind}, k ∈ newStack → k ∈ stackAt ap addr := by
                    intro k hk
                    dsimp [newStack] at hk
                    have hk' : k ∈ x.filter (fun k => !k.isMb) ∨ k ∈ item :: y :=
                      mem_of_mem_append hk
                    unfold stackAt
                    rw [h_find]
                    cases hk' with
                    | inl hk_left =>
                        rw [h_stack_eq]
                        exact List.mem_append_left (item :: y) (mem_filter_mem_prop hk_left).1
                    | inr hk_right =>
                        rw [h_stack_eq]
                        exact List.mem_append_right x hk_right
                  cases item with
                  | Own t =>
                      simp [h_find, h_split, newStack] at h_read
                      cases h_read
                      intro addr₁ addr₂ k₁ k₂ hk₁ hk₂ h_tag
                      exact
                        (liveTagUnique_insert_subset
                          (ap := ap) (addr := addr) (newStack := newStack) h_valid h_unique h_subset)
                          hk₁ hk₂ h_tag
                  | MutRef t =>
                      simp [h_find, h_split, newStack] at h_read
                      cases h_read
                      intro addr₁ addr₂ k₁ k₂ hk₁ hk₂ h_tag
                      exact
                        (liveTagUnique_insert_subset
                          (ap := ap) (addr := addr) (newStack := newStack) h_valid h_unique h_subset)
                          hk₁ hk₂ h_tag
                  | Ref t =>
                      simp [h_find, h_split, newStack] at h_read
                      cases h_read
                      intro addr₁ addr₂ k₁ k₂ hk₁ hk₂ h_tag
                      exact
                        (liveTagUnique_insert_subset
                          (ap := ap) (addr := addr) (newStack := newStack) h_valid h_unique h_subset)
                          hk₁ hk₂ h_tag
                  | RawPtr t =>
                      simp [h_find, h_split, newStack] at h_read
                      cases h_read
                      intro addr₁ addr₂ k₁ k₂ hk₁ hk₂ h_tag
                      exact
                        (liveTagUnique_insert_subset
                          (ap := ap) (addr := addr) (newStack := newStack) h_valid h_unique h_subset)
                          hk₁ hk₂ h_tag

theorem sb_use_mb_preserves_liveTagUnique
  {ap ap' : AccessPerms} {addr tag : Word}
  (h_valid : SBValid ap)
  (h_unique : LiveTagUnique ap)
  (h_use : sb_use_mb ap addr tag = Ok ap') :
  LiveTagUnique ap' := by
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
                  let newStack := item :: y
                  have h_subset :
                      ∀ {k : RefKind}, k ∈ newStack → k ∈ stackAt ap addr := by
                    intro k hk
                    unfold stackAt
                    rw [h_find]
                    exact splitStack_result_mem h_split hk
                  cases item with
                  | Own t =>
                      simp [h_find, h_split, newStack] at h_use
                      cases h_use
                      intro addr₁ addr₂ k₁ k₂ hk₁ hk₂ h_tag
                      exact
                        (liveTagUnique_insert_subset
                          (ap := ap) (addr := addr) (newStack := newStack) h_valid h_unique h_subset)
                          hk₁ hk₂ h_tag
                  | MutRef t =>
                      simp [h_find, h_split, newStack] at h_use
                      cases h_use
                      intro addr₁ addr₂ k₁ k₂ hk₁ hk₂ h_tag
                      exact
                        (liveTagUnique_insert_subset
                          (ap := ap) (addr := addr) (newStack := newStack) h_valid h_unique h_subset)
                          hk₁ hk₂ h_tag
                  | Ref t =>
                      simp [h_find, h_split, newStack] at h_use
                  | RawPtr t =>
                      simp [h_find, h_split, newStack] at h_use

theorem sb_read_preserves_live_addrs
  {ap ap' : AccessPerms} {addr tag front : Word}
  (h_live : ∀ addr stack, (addr, stack) ∈ ap.StackMap → addr < front)
  (h_read : sb_read ap addr tag = Ok ap') :
  ∀ addr stack, (addr, stack) ∈ ap'.StackMap → addr < front := by
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
                  let newStack := x.filter (fun k => !k.isMb) ++ item :: y
                  cases item with
                  | Own t =>
                      simp [h_find, h_split, newStack] at h_read
                      subst ap'
                      intro addr0 stack0 h_mem
                      have h_cases := SB.mem_insert_cases h_mem
                      cases h_cases with
                      | inl h_new =>
                          rw [h_new.1]
                          exact h_live _ _ (SB.find?_some_mem h_find)
                      | inr h_old =>
                          exact h_live _ _ h_old.1
                  | MutRef t =>
                      simp [h_find, h_split, newStack] at h_read
                      subst ap'
                      intro addr0 stack0 h_mem
                      have h_cases := SB.mem_insert_cases h_mem
                      cases h_cases with
                      | inl h_new =>
                          rw [h_new.1]
                          exact h_live _ _ (SB.find?_some_mem h_find)
                      | inr h_old =>
                          exact h_live _ _ h_old.1
                  | Ref t =>
                      simp [h_find, h_split, newStack] at h_read
                      subst ap'
                      intro addr0 stack0 h_mem
                      have h_cases := SB.mem_insert_cases h_mem
                      cases h_cases with
                      | inl h_new =>
                          rw [h_new.1]
                          exact h_live _ _ (SB.find?_some_mem h_find)
                      | inr h_old =>
                          exact h_live _ _ h_old.1
                  | RawPtr t =>
                      simp [h_find, h_split, newStack] at h_read
                      subst ap'
                      intro addr0 stack0 h_mem
                      have h_cases := SB.mem_insert_cases h_mem
                      cases h_cases with
                      | inl h_new =>
                          rw [h_new.1]
                          exact h_live _ _ (SB.find?_some_mem h_find)
                      | inr h_old =>
                          exact h_live _ _ h_old.1

theorem sb_use_mb_preserves_live_addrs
  {ap ap' : AccessPerms} {addr tag front : Word}
  (h_live : ∀ addr stack, (addr, stack) ∈ ap.StackMap → addr < front)
  (h_use : sb_use_mb ap addr tag = Ok ap') :
  ∀ addr stack, (addr, stack) ∈ ap'.StackMap → addr < front := by
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
                  let newStack := item :: y
                  cases item with
                  | Own t =>
                      simp [h_find, h_split, newStack] at h_use
                      subst ap'
                      intro addr0 stack0 h_mem
                      have h_cases := SB.mem_insert_cases h_mem
                      cases h_cases with
                      | inl h_new =>
                          rw [h_new.1]
                          exact h_live _ _ (SB.find?_some_mem h_find)
                      | inr h_old =>
                          exact h_live _ _ h_old.1
                  | MutRef t =>
                      simp [h_find, h_split, newStack] at h_use
                      subst ap'
                      intro addr0 stack0 h_mem
                      have h_cases := SB.mem_insert_cases h_mem
                      cases h_cases with
                      | inl h_new =>
                          rw [h_new.1]
                          exact h_live _ _ (SB.find?_some_mem h_find)
                      | inr h_old =>
                          exact h_live _ _ h_old.1
                  | Ref t =>
                      simp [h_find, h_split, newStack] at h_use
                  | RawPtr t =>
                      simp [h_find, h_split, newStack] at h_use

theorem sb_own_preserves_live_addrs
  {ap ap' : AccessPerms} {addr tag front : Word}
  (h_live : ∀ addr stack, (addr, stack) ∈ ap.StackMap → addr < front)
  (h_own : sb_own ap addr = (Ok ap', tag))
  (h_fresh : addr < front) :
  ∀ addr0 stack, (addr0, stack) ∈ ap'.StackMap → addr0 < front := by
  unfold sb_own at h_own
  cases h_find : ap.StackMap.find? addr with
  | none =>
      simp [h_find] at h_own
      let ⟨h_ap', _h_tag⟩ := h_own
      subst ap'
      intro addr0 stack0 h_mem
      have h_cases := SB.mem_insert_cases h_mem
      cases h_cases with
      | inl h_new =>
          rw [h_new.1]
          exact h_fresh
      | inr h_old =>
          exact h_live _ _ h_old.1
  | some stack =>
      cases stack with
      | nil =>
          simp [h_find] at h_own
          let ⟨h_ap', _h_tag⟩ := h_own
          subst ap'
          intro addr0 stack0 h_mem
          have h_cases := SB.mem_insert_cases h_mem
          cases h_cases with
          | inl h_new =>
              rw [h_new.1]
              exact h_fresh
          | inr h_old =>
              exact h_live _ _ h_old.1
      | cons hd tl =>
          simp [h_find] at h_own

theorem sb_own_preserves_liveTagUnique
  {ap ap' : AccessPerms} {addr tag : Word}
  (h_valid : SBValid ap)
  (h_unique : LiveTagUnique ap)
  (h_own : sb_own ap addr = (Ok ap', tag)) :
  LiveTagUnique ap' := by
  unfold sb_own at h_own
  cases h_find : ap.StackMap.find? addr with
  | none =>
      simp [h_find, freshTag] at h_own
      rcases h_own with ⟨rfl, rfl⟩
      let ap1 : AccessPerms := { ap with NextTag := ap.NextTag + 1 }
      have h_valid1 : SBValid ap1 := SBValid_nextTag_succ h_valid
      have h_unique1 : LiveTagUnique ap1 := liveTagUnique_nextTag h_unique
      have h_fresh : ¬ tag_live ap1 ap.NextTag := by
        simpa [ap1, tag_live, stackAt] using freshTag_not_live (ap := ap) h_valid
      have h_insert :
          LiveTagUnique
            { ap1 with
              StackMap := SB.insert ap1.StackMap addr
                (RefKind.Own ap.NextTag :: stackAt ap1 addr) } :=
        liveTagUnique_insert_fresh_head
          (ap := ap1)
          (addr := addr)
          (newItem := RefKind.Own ap.NextTag)
          h_valid1 h_unique1 h_fresh
      have h_stackAt : stackAt ap1 addr = [] := by
        unfold stackAt
        simp [ap1, h_find]
      have h_insert' :
          LiveTagUnique
            { ap1 with
              StackMap := SB.insert ap1.StackMap addr [RefKind.Own ap.NextTag] } := by
        intro addr₁ addr₂ k₁ k₂ hk₁ hk₂ h_tag
        have hk₁' :
            k₁ ∈
              stackAt
                { ap1 with
                  StackMap := SB.insert ap1.StackMap addr
                    (RefKind.Own ap.NextTag :: stackAt ap1 addr) } addr₁ := by
          simpa [h_stackAt] using hk₁
        have hk₂' :
            k₂ ∈
              stackAt
                { ap1 with
                  StackMap := SB.insert ap1.StackMap addr
                    (RefKind.Own ap.NextTag :: stackAt ap1 addr) } addr₂ := by
          simpa [h_stackAt] using hk₂
        exact h_insert hk₁' hk₂' h_tag
      change LiveTagUnique
        { StackMap := ap.StackMap.insert addr [RefKind.Own ap.NextTag]
          NextTag := ap.NextTag + 1 }
      intro addr₁ addr₂ k₁ k₂ hk₁ hk₂ h_tag
      exact h_insert' hk₁ hk₂ h_tag
  | some stack =>
      cases stack with
      | nil =>
          simp [h_find, freshTag] at h_own
          rcases h_own with ⟨rfl, rfl⟩
          let ap1 : AccessPerms := { ap with NextTag := ap.NextTag + 1 }
          have h_valid1 : SBValid ap1 := SBValid_nextTag_succ h_valid
          have h_unique1 : LiveTagUnique ap1 := liveTagUnique_nextTag h_unique
          have h_fresh : ¬ tag_live ap1 ap.NextTag := by
            simpa [ap1, tag_live, stackAt] using freshTag_not_live (ap := ap) h_valid
          have h_insert :
              LiveTagUnique
                { ap1 with
                  StackMap := SB.insert ap1.StackMap addr
                    (RefKind.Own ap.NextTag :: stackAt ap1 addr) } :=
            liveTagUnique_insert_fresh_head
              (ap := ap1)
              (addr := addr)
              (newItem := RefKind.Own ap.NextTag)
              h_valid1 h_unique1 h_fresh
          have h_stackAt : stackAt ap1 addr = [] := by
            unfold stackAt
            simp [ap1, h_find]
          have h_insert' :
              LiveTagUnique
                { ap1 with
                  StackMap := SB.insert ap1.StackMap addr [RefKind.Own ap.NextTag] } := by
            intro addr₁ addr₂ k₁ k₂ hk₁ hk₂ h_tag
            have hk₁' :
                k₁ ∈
                  stackAt
                    { ap1 with
                      StackMap := SB.insert ap1.StackMap addr
                        (RefKind.Own ap.NextTag :: stackAt ap1 addr) } addr₁ := by
              simpa [h_stackAt] using hk₁
            have hk₂' :
                k₂ ∈
                  stackAt
                    { ap1 with
                      StackMap := SB.insert ap1.StackMap addr
                        (RefKind.Own ap.NextTag :: stackAt ap1 addr) } addr₂ := by
              simpa [h_stackAt] using hk₂
            exact h_insert hk₁' hk₂' h_tag
          change LiveTagUnique
            { StackMap := ap.StackMap.insert addr [RefKind.Own ap.NextTag]
              NextTag := ap.NextTag + 1 }
          intro addr₁ addr₂ k₁ k₂ hk₁ hk₂ h_tag
          exact h_insert' hk₁ hk₂ h_tag
      | cons hd tl =>
          simp [h_find] at h_own

theorem sb_ref_preserves_liveTagUnique
  {ap ap' : AccessPerms} {addr tag newTag : Word} {kind : RefOpKind}
  (h_valid : SBValid ap)
  (h_unique : LiveTagUnique ap)
  (h_ref : sb_ref ap addr tag kind = (Ok ap', newTag)) :
  LiveTagUnique ap' := by
  unfold sb_ref at h_ref
  cases kind with
  | Shared =>
      cases h_parent : sb_read ap addr tag with
      | Err msg =>
          simp [h_parent] at h_ref
      | Ok apParent =>
          have h_valid_parent : SBValid apParent :=
            sb_read_preserves_valid h_valid h_parent
          have h_unique_parent : LiveTagUnique apParent :=
            sb_read_preserves_liveTagUnique h_valid h_unique h_parent
          let ap1 : AccessPerms := { apParent with NextTag := apParent.NextTag + 1 }
          have h_valid1 : SBValid ap1 := SBValid_nextTag_succ h_valid_parent
          have h_unique1 : LiveTagUnique ap1 := liveTagUnique_nextTag h_unique_parent
          have h_fresh : ¬ tag_live ap1 apParent.NextTag := by
            simpa [ap1, tag_live, stackAt] using freshTag_not_live (ap := apParent) h_valid_parent
          cases h_find : ap1.StackMap.find? addr with
          | none =>
              simp [h_parent, freshTag, ap1, h_find] at h_ref
          | some stack =>
              simp [h_parent, freshTag, ap1, h_find] at h_ref
              rcases h_ref with ⟨rfl, rfl⟩
              have h_insert :
                  LiveTagUnique
                    { ap1 with
                      StackMap := SB.insert ap1.StackMap addr
                        (RefKind.Ref apParent.NextTag :: stackAt ap1 addr) } :=
                liveTagUnique_insert_fresh_head
                  (ap := ap1)
                  (addr := addr)
                  (newItem := RefKind.Ref apParent.NextTag)
                  h_valid1 h_unique1 h_fresh
              intro addr₁ addr₂ k₁ k₂ hk₁ hk₂ h_tag
              have hk₁' :
                  k₁ ∈
                    stackAt
                      { ap1 with
                        StackMap := SB.insert ap1.StackMap addr
                          (RefKind.Ref apParent.NextTag :: stackAt ap1 addr) } addr₁ := by
                simpa [ap1, stackAt, h_find] using hk₁
              have hk₂' :
                  k₂ ∈
                    stackAt
                      { ap1 with
                        StackMap := SB.insert ap1.StackMap addr
                          (RefKind.Ref apParent.NextTag :: stackAt ap1 addr) } addr₂ := by
                simpa [ap1, stackAt, h_find] using hk₂
              exact h_insert hk₁' hk₂' h_tag
  | Mut =>
      cases h_parent : sb_use_mb ap addr tag with
      | Err msg =>
          simp [h_parent] at h_ref
      | Ok apParent =>
          have h_valid_parent : SBValid apParent :=
            sb_use_mb_preserves_valid h_valid h_parent
          have h_unique_parent : LiveTagUnique apParent :=
            sb_use_mb_preserves_liveTagUnique h_valid h_unique h_parent
          let ap1 : AccessPerms := { apParent with NextTag := apParent.NextTag + 1 }
          have h_valid1 : SBValid ap1 := SBValid_nextTag_succ h_valid_parent
          have h_unique1 : LiveTagUnique ap1 := liveTagUnique_nextTag h_unique_parent
          have h_fresh : ¬ tag_live ap1 apParent.NextTag := by
            simpa [ap1, tag_live, stackAt] using freshTag_not_live (ap := apParent) h_valid_parent
          cases h_find : ap1.StackMap.find? addr with
          | none =>
              simp [h_parent, freshTag, ap1, h_find] at h_ref
          | some stack =>
              simp [h_parent, freshTag, ap1, h_find] at h_ref
              rcases h_ref with ⟨rfl, rfl⟩
              have h_insert :
                  LiveTagUnique
                    { ap1 with
                      StackMap := SB.insert ap1.StackMap addr
                        (RefKind.MutRef apParent.NextTag :: stackAt ap1 addr) } :=
                liveTagUnique_insert_fresh_head
                  (ap := ap1)
                  (addr := addr)
                  (newItem := RefKind.MutRef apParent.NextTag)
                  h_valid1 h_unique1 h_fresh
              intro addr₁ addr₂ k₁ k₂ hk₁ hk₂ h_tag
              have hk₁' :
                  k₁ ∈
                    stackAt
                      { ap1 with
                        StackMap := SB.insert ap1.StackMap addr
                          (RefKind.MutRef apParent.NextTag :: stackAt ap1 addr) } addr₁ := by
                simpa [ap1, stackAt, h_find] using hk₁
              have hk₂' :
                  k₂ ∈
                    stackAt
                      { ap1 with
                        StackMap := SB.insert ap1.StackMap addr
                          (RefKind.MutRef apParent.NextTag :: stackAt ap1 addr) } addr₂ := by
                simpa [ap1, stackAt, h_find] using hk₂
              exact h_insert hk₁' hk₂' h_tag
  | Raw =>
      cases h_parent : sb_use_mb ap addr tag with
      | Err msg =>
          simp [h_parent] at h_ref
      | Ok apParent =>
          have h_valid_parent : SBValid apParent :=
            sb_use_mb_preserves_valid h_valid h_parent
          have h_unique_parent : LiveTagUnique apParent :=
            sb_use_mb_preserves_liveTagUnique h_valid h_unique h_parent
          let ap1 : AccessPerms := { apParent with NextTag := apParent.NextTag + 1 }
          have h_valid1 : SBValid ap1 := SBValid_nextTag_succ h_valid_parent
          have h_unique1 : LiveTagUnique ap1 := liveTagUnique_nextTag h_unique_parent
          have h_fresh : ¬ tag_live ap1 apParent.NextTag := by
            simpa [ap1, tag_live, stackAt] using freshTag_not_live (ap := apParent) h_valid_parent
          cases h_find : ap1.StackMap.find? addr with
          | none =>
              simp [h_parent, freshTag, ap1, h_find] at h_ref
          | some stack =>
              simp [h_parent, freshTag, ap1, h_find] at h_ref
              rcases h_ref with ⟨rfl, rfl⟩
              have h_insert :
                  LiveTagUnique
                    { ap1 with
                      StackMap := SB.insert ap1.StackMap addr
                        (RefKind.RawPtr apParent.NextTag :: stackAt ap1 addr) } :=
                liveTagUnique_insert_fresh_head
                  (ap := ap1)
                  (addr := addr)
                  (newItem := RefKind.RawPtr apParent.NextTag)
                  h_valid1 h_unique1 h_fresh
              intro addr₁ addr₂ k₁ k₂ hk₁ hk₂ h_tag
              have hk₁' :
                  k₁ ∈
                    stackAt
                      { ap1 with
                        StackMap := SB.insert ap1.StackMap addr
                          (RefKind.RawPtr apParent.NextTag :: stackAt ap1 addr) } addr₁ := by
                simpa [ap1, stackAt, h_find] using hk₁
              have hk₂' :
                  k₂ ∈
                    stackAt
                      { ap1 with
                        StackMap := SB.insert ap1.StackMap addr
                          (RefKind.RawPtr apParent.NextTag :: stackAt ap1 addr) } addr₂ := by
                simpa [ap1, stackAt, h_find] using hk₂
              exact h_insert hk₁' hk₂' h_tag

end obseq
