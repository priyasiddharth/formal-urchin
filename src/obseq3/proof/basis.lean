import obseq3.values

/-!
# The simulation's basis

What every simulation lemma is stated in: the tag renaming between the two
machines' permission states (`TagRenameMap`, grown monotonically and kept
injective), the per-byte stack relation it induces (`PermSim`), the
value relation (`MemValSim`), and list and register bookkeeping. The
renaming starts as `initialTagRename` (only the wildcard is mapped).
-/

namespace obseq3.proof

open obseq3
open obseq3.oseair (Register Val)

/-- The permission model both sides of the simulation are instantiated at. -/
abbrev MSB : PermissionModel := PermissionModel.stackedBorrows

/-- A register whose numeric index is strictly less than `bound`. -/
def RegisterBelow (bound : Nat) : Register → Prop
  | .R idx => idx < bound

theorem RegisterBelow.mono {b b' : Nat} (h : b ≤ b') :
    ∀ {r : Register}, RegisterBelow b r → RegisterBelow b' r
  | .R _, h_lt => Nat.lt_of_lt_of_le h_lt h

abbrev AddrRenameMap := Word → Option Word

abbrev TagRenameMap := Tag → Option Tag

/-- Tag rename maps grow monotonically. -/
def TagRenameIncr (ρt ρt' : TagRenameMap) : Prop :=
  ∀ tag tag', ρt tag = some tag' → ρt' tag = some tag'

theorem TagRenameIncr.refl (ρt : TagRenameMap) : TagRenameIncr ρt ρt :=
  fun _ _ h => h

theorem TagRenameIncr.trans {ρt ρt' ρt'' : TagRenameMap}
    (h₁ : TagRenameIncr ρt ρt') (h₂ : TagRenameIncr ρt' ρt'') :
    TagRenameIncr ρt ρt'' :=
  fun tag tag' h => h₂ tag tag' (h₁ tag tag' h)

def TagRenameWF (ρt : TagRenameMap) : Prop :=
  (∀ t1 t2 t', ρt t1 = some t' → ρt t2 = some t' → t1 = t2) ∧
  ρt wildcardTag = some wildcardTag

def TagRenameBounded (ρt : TagRenameMap) (nS nT : Tag) : Prop :=
  ∀ t t', ρt t = some t' → t < nS ∧ t' < nT

/-- Extend a rename map at one fresh pair. -/
def TagRenameMap.extend (ρt : TagRenameMap) (s t : Tag) : TagRenameMap :=
  fun x => if x = s then some t else ρt x

-- `grind` lemma registration: the definitions every renaming and
-- register-frame argument unfolds.
attribute [grind] RegisterBelow Fin.ext
attribute [grind] mirlite.Env.lookup mirlite.Env.set
attribute [grind] TagRenameBounded TagRenameMap.extend

@[simp] theorem TagRenameMap.extend_self (ρt : TagRenameMap) (s t : Tag) :
    ρt.extend s t s = some t := by
  simp [TagRenameMap.extend]

theorem TagRenameIncr.extend {ρt : TagRenameMap} {nS nT s t : Tag}
    (h_bd : TagRenameBounded ρt nS nT) (h_s : nS ≤ s) :
    TagRenameIncr ρt (ρt.extend s t) := by
  intro x x' hx
  grind

/-- `TagRenameWF` survives the fresh-pair extension: injectivity because the
    new target is outside the old range (the range bound), and the wildcard
    mapping because `wildcardTag = 0 < nS ≤ s`. -/
theorem TagRenameWF.extend {ρt : TagRenameMap} {nS nT s t : Tag}
    (h_wf : TagRenameWF ρt) (h_bd : TagRenameBounded ρt nS nT)
    (h_s : nS ≤ s) (h_t : nT ≤ t) :
    TagRenameWF (ρt.extend s t) := by
  obtain ⟨h_inj, h_wc⟩ := h_wf
  constructor
  · intro t1 t2 t' h1 h2
    grind
  · grind

/-- The bound itself grows with the counters. -/
theorem TagRenameBounded.extend {ρt : TagRenameMap} {nS nT nS' nT' s t : Tag}
    (h_bd : TagRenameBounded ρt nS nT)
    (h_le : nS ≤ nS') (h_le' : nT ≤ nT') (h_s : s < nS') (h_t : t < nT') :
    TagRenameBounded (ρt.extend s t) nS' nT' := by
  grind

/-- The bound is monotone in the counters (both machines only ever mint). -/
theorem TagRenameBounded.mono {ρt : TagRenameMap} {nS nT nS' nT' : Tag}
    (h_bd : TagRenameBounded ρt nS nT) (h_le : nS ≤ nS') (h_le' : nT ≤ nT') :
    TagRenameBounded ρt nS' nT' := by grind

/-- Pointwise relation between two lists of equal length (a local stand-in
    for Mathlib's `List.Forall₂`, which this project does not depend on). -/
def ListRel (R : α → β → Prop) : List α → List β → Prop
  | [], [] => True
  | a :: as, b :: bs => R a b ∧ ListRel R as bs
  | _, _ => False

theorem ListRel.imp {α β} {R S : α → β → Prop}
    (h : ∀ a b, R a b → S a b) :
    ∀ {as : List α} {bs : List β}, ListRel R as bs → ListRel S as bs := by
  intro as
  induction as with
  | nil =>
      intro bs hr
      cases bs with
      | nil => trivial
      | cons b bs => simp [ListRel] at hr
  | cons a as ih =>
      intro bs hr
      cases bs with
      | nil => simp [ListRel] at hr
      | cons b bs =>
          simp only [ListRel] at hr ⊢
          exact ⟨h a b hr.1, ih hr.2⟩

theorem ListRel.length_eq {α β} {R : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, ListRel R as bs → as.length = bs.length := by
  intro as
  induction as with
  | nil =>
      intro bs hr
      cases bs with
      | nil => rfl
      | cons b bs => simp [ListRel] at hr
  | cons a as ih =>
      intro bs hr
      cases bs with
      | nil => simp [ListRel] at hr
      | cons b bs =>
          simp only [ListRel] at hr
          simp [ih hr.2]

/-- Item-wise simulation: same constructor, tag mapped by ρt. Preserving the
    constructor (incl. `Disabled`) keeps SRW-grouping structure identical. -/
def ItemSim (ρt : TagRenameMap) : Item → Item → Prop
  | .Own t, .Own t' => ρt t = some t'
  | .MutRef t, .MutRef t' => ρt t = some t'
  | .Ref t, .Ref t' => ρt t = some t'
  | .RawPtr m t, .RawPtr m' t' => m' = m ∧ ρt t = some t'
  | .Disabled t, .Disabled t' => ρt t = some t'
  | _, _ => False

theorem ItemSim.mono {ρt ρt' : TagRenameMap} (h_incr : TagRenameIncr ρt ρt')
    (i i' : Item) (hi : ItemSim ρt i i') : ItemSim ρt' i i' := by
  cases i <;> cases i' <;> simp [ItemSim] at hi ⊢ <;>
    first
      | exact h_incr _ _ hi
      | exact ⟨hi.1, h_incr _ _ hi.2⟩

/-- Position-preserving stack simulation. -/
def StackSim (ρt : TagRenameMap) (src tgt : List Item) : Prop :=
  ListRel (ItemSim ρt) src tgt

def StackMapSim (ρt : TagRenameMap) (x y : SB) : Prop :=
  ∀ a : Word,
    match SB.find? x a, SB.find? y a with
    | none, none => True
    | some s, some s' => StackSim ρt s s'
    | _, _ => False

theorem StackMapSim.imp {ρt ρt' : TagRenameMap} {x y : SB}
    (h_i : ∀ i i', ItemSim ρt i i' → ItemSim ρt' i i')
    (h : StackMapSim ρt x y) : StackMapSim ρt' x y := by
  intro a
  have h' := h a
  cases hx : SB.find? x a with
  | none =>
      rw [hx] at h'
      cases hy : SB.find? y a with
      | none => simp
      | some s' => rw [hy] at h'; exact absurd h' (by simp)
  | some s =>
      rw [hx] at h'
      cases hy : SB.find? y a with
      | none => rw [hy] at h'; exact absurd h' (by simp)
      | some s' =>
          rw [hy] at h'
          simp only [hx, hy]
          exact ListRel.imp h_i h'

/-- Tag-list simulation (protector frames, exposed set). -/

theorem StackMapSim.find?_some {ρt : TagRenameMap} {x y : SB}
    (h : StackMapSim ρt x y) {a : Word} {s : BorrowStack}
    (hf : SB.find? x a = some s) :
    ∃ s', SB.find? y a = some s' ∧ StackSim ρt s s' := by
  have h' := h a
  rw [hf] at h'
  cases hy : SB.find? y a with
  | none => rw [hy] at h'; exact absurd h' (by simp)
  | some s' => rw [hy] at h'; exact ⟨s', rfl, h'⟩

theorem StackMapSim.find?_none {ρt : TagRenameMap} {x y : SB}
    (h : StackMapSim ρt x y) {a : Word}
    (hf : SB.find? x a = none) : SB.find? y a = none := by
  have h' := h a
  rw [hf] at h'
  cases hy : SB.find? y a with
  | none => rfl
  | some s' => rw [hy] at h'; exact absurd h' (by simp)

/-- The target side of a `StackMapSim` can be swapped for any
    `find?`-identical map — the disjoint-range commutation produces its
    result only up to representation order. -/
def TagListSim (ρt : TagRenameMap) (src tgt : List Tag) : Prop :=
  ListRel (fun t t' => ρt t = some t') src tgt

/-- The retired sets (`AccessPerms.retired`, tags a `Die` ended): a target
    tag that is a renamed source tag is retired only if the source tag is —
    the target also retires its route tags, which are outside ρt's range —
    and every target-retired tag was minted (below the target counter), so
    a fresh pair added to ρt is never a retired one. This is what lets the
    target's `sb_expose` succeed whenever the source's does. -/
def RetiredSim (ρt : TagRenameMap) (src tgt : AccessPerms) : Prop :=
  (∀ t t', ρt t = some t' → t' ∈ tgt.retired → t ∈ src.retired) ∧
  (∀ t' ∈ tgt.retired, t' < tgt.NextTag)

/-- The v3 permission relation: ρt-renamed stacks (position- and
    constructor-preserving), renamed protector frames and exposed set, a
    target counter at least the source's (the target mints extra tags for
    its internal borrows; `Die` pops the items but not the counter), the
    renamed weak-protector set, and the retired sets (`RetiredSim`). -/
def PermSim (ρt : TagRenameMap) (src tgt : AccessPerms) : Prop :=
  StackMapSim ρt src.StackMap tgt.StackMap ∧
  ListRel (TagListSim ρt) src.protFrames tgt.protFrames ∧
  TagListSim ρt src.exposed tgt.exposed ∧
  src.NextTag ≤ tgt.NextTag ∧
  TagListSim ρt src.weakProt tgt.weakProt ∧
  RetiredSim ρt src tgt

/-- `PermSim` transports along rename growth when no newly renamed target
    tag is retired (renames otherwise only appear positively). -/
theorem PermSim.rename_mono
    {ρt ρt' : TagRenameMap} {src tgt : AccessPerms}
    (h_incr : TagRenameIncr ρt ρt')
    (h_new : ∀ t t', ρt' t = some t' → ρt t = none → t' ∉ tgt.retired)
    (h_sim : PermSim ρt src tgt) :
    PermSim ρt' src tgt := by
  obtain ⟨h_stacks, h_prot, h_exp, h_next, h_wk, h_rt, h_rtb⟩ := h_sim
  refine ⟨?_, ?_, ?_, h_next, ?_, ?_, h_rtb⟩
  · exact StackMapSim.imp (fun i i' => ItemSim.mono h_incr i i') h_stacks
  · exact ListRel.imp (fun f f' hf =>
      ListRel.imp (fun t t' ht => h_incr _ _ ht) hf) h_prot
  · exact ListRel.imp (fun t t' ht => h_incr _ _ ht) h_exp
  · exact ListRel.imp (fun t t' ht => h_incr _ _ ht) h_wk
  · intro t t' h hr
    cases h0 : ρt t with
    | none => exact absurd hr (h_new t t' h h0)
    | some t0 =>
        have h1 := h_incr _ _ h0
        rw [h] at h1
        cases h1
        exact h_rt t t' h0 hr

/-- `PermSim` transports along the fresh-pair extension of ρt (the only
    way the renaming grows): the new target tag is the target counter,
    which no retired target tag reaches. -/
theorem PermSim.rename_extend {ρt : TagRenameMap} {src tgt : AccessPerms}
    (h_bd : TagRenameBounded ρt src.NextTag tgt.NextTag)
    (h_sim : PermSim ρt src tgt) :
    PermSim (ρt.extend src.NextTag tgt.NextTag) src tgt :=
  PermSim.rename_mono (TagRenameIncr.extend h_bd (Nat.le_refl _)) (fun t t' h h0 => by
    simp only [TagRenameMap.extend] at h
    split at h
    · cases h
      intro hm
      exact absurd (h_sim.2.2.2.2.2.2 _ hm) (Nat.lt_irrefl _)
    · rw [h0] at h
      cases h) h_sim

/-- `RetiredSim` survives any step that leaves both retired sets alone and
    does not lower the target counter. -/
theorem RetiredSim.of_eq {ρt : TagRenameMap} {src tgt src' tgt' : AccessPerms}
    (h : RetiredSim ρt src tgt) (h1 : src'.retired = src.retired)
    (h2 : tgt'.retired = tgt.retired) (h3 : tgt.NextTag ≤ tgt'.NextTag) :
    RetiredSim ρt src' tgt' :=
  ⟨fun t t' ht hm => by rw [h1]; exact h.1 t t' ht (by rw [← h2]; exact hm),
   fun t' hm => Nat.lt_of_lt_of_le (h.2 t' (by rw [← h2]; exact hm)) h3⟩

/-- Pointwise simulation between a source `MemValue` and a target `Val`. -/
def MemValSim
  (ρa : AddrRenameMap)
  (ρt : TagRenameMap) : mirlite.MemValue → Val → Prop
  -- undef refines ANY target value: an unwritten (or explicitly undef)
  -- source cell carries no information, and every source operation that
  -- would OBSERVE the word (branching, alloc-length reads, pointer
  -- loads) errs on undef, discharging the simulation obligation. This
  -- is what lets a copy relate `mirlite.readWordSeq` to
  -- `oseair.readWordSeq` cell-by-cell when the source range has holes
  -- (`readWordSeq_sim`) without a reverse-domain memory invariant.
  | .undef,           _                  => True
  | .word v,          .Dat v'            => v' = v
  | .ptrVal b o e s t,  .Ptr b' o' e' s' t'  =>
      ρa b = some b' ∧ o' = o ∧ e' = e ∧ s' = s ∧ ρt t = some t' ∧
      -- NO non-wildcard side condition: `fromExposed` stores pointers
      -- carrying `wildcardTag`, and since 2026-09-13 an access through
      -- one transports too (`resolveWildcardIn_transport`), so BRIDGE 3
      -- fires on writes through loaded pointers whatever their tag.
      -- the referent block is in ρa's domain (allocations are lockstep),
      -- which is what supplies `writeThroughPtr_sim`'s `h_dom` for deref
      -- destinations
      (∀ k, k < s → ∃ a', ρa (b + k) = some a')
  | _, _                                 => False

theorem lookup_filter_ne {α β : Type} [BEq α] [LawfulBEq α] {a addr : α} (hne : a ≠ addr) :
    (l : List (α × β)) →
    List.lookup a (l.filter (fun p => p.1 != addr)) = List.lookup a l
  | [] => rfl
  | (k, val) :: ps => by
      have ih := lookup_filter_ne (β := β) hne ps
      by_cases hk : k = addr
      · subst hk
        rw [List.filter_cons_of_neg (by simp)]
        rw [ih, List.lookup_cons]
        have hb : (a == k) = false := by simp [hne]
        rw [hb]
      · rw [List.filter_cons_of_pos (by simp [hk]), List.lookup_cons, List.lookup_cons, ih]

instance : LawfulBEq Register where
  eq_of_beq {a b} h := by
    cases a with | R n => cases b with | R m =>
      have h' : (n == m) = true := h
      simp only [beq_iff_eq] at h'
      simp [h']
  rfl {a} := by
    cases a with | R n =>
      show (n == n) = true
      simp

/-- The initial address rename: the identity. ρa is IDENTITY on its
    domain (lockstep bump allocation shares the address namespace), and
    `AllocLockstep` asks it to be total so that the degenerate pointer
    `fromExposed` mints for an unallocated address has a renamed base. -/
def initialAddrRename : AddrRenameMap := fun a => some a


/-- The initial tag rename: the wildcard fixed, nothing else. -/
def initialTagRename : TagRenameMap :=
  fun t => if t = wildcardTag then some wildcardTag else none

/-! ## Pointer chains -/

/-- Canonical pointer CHAINS — the pending-cleanup generalization of
    `LoadSpine`. A chain is a local, a dereference of a chain, or a
    dereference of a SINGLE projection whose base is a chain. Since
    `placeToRegChecked` reassociates consecutive projections into one,
    this covers every alternation of stars and fields except
    proj-of-proj spellings (a separate normalization transfer) and
    proj-TOPPED places (their pending `Die` is the consumer's business).
    Projections appear only directly under a deref: that deref's source
    dereferenceable check is what pays the interior `Borrow`'s bounds
    obligation. -/
inductive PtrChain {Γ : Ctx} : {τ : LayoutTy} → Place Γ τ → Prop
  | base {τ : LayoutTy} (loc : Local Γ τ) : PtrChain (.local loc)
  | deref {τ : LayoutTy} {p : Place Γ (LayoutTy.PtrL τ)} :
      PtrChain p → PtrChain (.deref p)
  | derefProj {σ τ : LayoutTy} {b : Place Γ σ}
      (f : PathTo σ (LayoutTy.PtrL τ)) :
      PtrChain b → PtrChain (.deref (.proj b f))

/-- Chains never carry a projection at the top — the shape
    `placeToRegChecked_proj_root_eq` asks for. -/
theorem PtrChain.not_proj {Γ : Ctx} {σ : LayoutTy} {b : Place Γ σ}
    (h : PtrChain b) :
    ∀ (σ' : LayoutTy) (bb : Place Γ σ') (q : PathTo σ' σ),
      b = bb.proj q → False := by
  intro σ' bb q h_eq
  cases h <;> simp_all

end obseq3.proof
