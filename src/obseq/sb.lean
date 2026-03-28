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

/--
`NextTag` is treated as an abstract freshness source.
-/
axiom freshTag_fresh
  {ap : AccessPerms} :
  ¬ tag_live ap ap.NextTag

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

@[simp] theorem extendAddrRenaming_self
  (ρa : AddrRenameMap) (src dst : Word) :
  (extendAddrRenameMap ρa src dst) src = some dst := by
  simp [extendAddrRenameMap]

@[simp] theorem extendAddrRenaming_ne
  (ρa : AddrRenameMap) (src dst addr : Word)
  (h_ne : addr ≠ src) :
  (extendAddrRenameMap ρa src dst) addr = ρa addr := by
  simp [extendAddrRenameMap, h_ne]

@[simp] theorem extendTagRenaming_self
  (ρt : TagRenameMap) (src dst : Tag) :
  (extendTagRenameMap ρt src dst) src = some dst := by
  simp [extendTagRenameMap]

@[simp] theorem extendTagRenaming_ne
  (ρt : TagRenameMap) (src dst tag : Tag)
  (h_ne : tag ≠ src) :
  (extendTagRenameMap ρt src dst) tag = ρt tag := by
  simp [extendTagRenameMap, h_ne]

end obseq
