import obseq3.proof.permsim_dealloc
import obseq3.proof.permsim_transport
import obseq3.mirlite

/-!
# Memory simulation

The relation between the two machines' memories is per byte: at every address the source byte and
the target byte are the same byte, the target's provenance being the
source's with its tag renamed (`ρt`); an uninitialised source byte
refines anything. Addresses are not renamed: both machines allocate in
lockstep.

Under this relation a sub-value access — a one-byte
borrow inside a wider field, a partial read of a pointer, a write that
covers padding — is just a range of related bytes. The lemmas below are
stated for any address and length, and the value-level ones for any
layout, so nothing in them assumes cells. The Stacked Borrows side needs
nothing new: `sb_*_respects_PermSim` already take any `(addr, len)`.

STATUS (branch `byteaddress`, 2026-10-02): the lemmas here are used by the
first machine-step leaf, `proof/const_write.lean` (compiler +
layout-typed target, bound-local regime).
-/

namespace obseq3.proof

open obseq3 obseq3.bytes obseq3.proof
open obseq3.mirlite (MemValue)
open obseq3.oseair (Val)

/-! ## The relations -/

/-- Provenance under a tag renaming: the same allocation and extent, the
    tag renamed. -/
def ProvSim (ρt : TagRenameMap) : Option Prov → Option Prov → Prop
  | none, none => True
  | some p, some p' =>
      p'.base = p.base ∧ p'.sizeB = p.sizeB ∧ p'.extentB = p.extentB ∧ ρt p.tag = some p'.tag
  | _, _ => False

/-- One byte: an uninitialised source byte refines any target byte; an
    initialised one is the same byte with related provenance. -/
def ByteSim (ρt : TagRenameMap) : AbstractByte → AbstractByte → Prop
  | .uninit, _ => True
  | .init b p, .init b' p' => b' = b ∧ ProvSim ρt p p'
  | .init _ _, .uninit => False

/-- Memory, byte by byte at the SAME address. -/
def ByteMemSim (ρt : TagRenameMap) (mS mT : bytes.Mem) : Prop :=
  ∀ a, ByteSim ρt (mS.bytes a) (mT.bytes a)

/-- The two allocators in lockstep (the byte analogue of `AllocLockstep`). -/
def ByteAllocLockstep (mS mT : bytes.Mem) : Prop :=
  mT.allocs = mS.allocs ∧ mT.next = mS.next ∧ mT.freed = mS.freed

/-! ## List helpers -/

theorem ListRel.map_of {α β γ} {R : α → β → Prop} {f : γ → α} {g : γ → β}
    (h : ∀ x, R (f x) (g x)) : ∀ (l : List γ), ListRel R (l.map f) (l.map g)
  | [] => trivial
  | x :: xs => ⟨h x, ListRel.map_of h xs⟩

theorem ListRel.getD {α β} {R : α → β → Prop} {dS : α} {dT : β} (hd : R dS dT) :
    ∀ {as : List α} {bs : List β}, ListRel R as bs → ∀ i, R (as.getD i dS) (bs.getD i dT)
  | [], [], _, _ => by simpa using hd
  | _ :: _, _ :: _, h, 0 => by simpa using h.1
  | _ :: _, _ :: _, h, i + 1 => by simpa using ListRel.getD hd h.2 i
  | [], _ :: _, h, _ => absurd h (by simp [ListRel])
  | _ :: _, [], h, _ => absurd h (by simp [ListRel])

theorem ListRel.drop {α β} {R : α → β → Prop} :
    ∀ (n : Nat) {as : List α} {bs : List β}, ListRel R as bs →
      ListRel R (as.drop n) (bs.drop n)
  | 0, _, _, h => by simpa using h
  | _ + 1, [], [], _ => by simp [ListRel]
  | n + 1, _ :: _, _ :: _, h => ListRel.drop n h.2
  | _ + 1, [], _ :: _, h => absurd h (by simp [ListRel])
  | _ + 1, _ :: _, [], h => absurd h (by simp [ListRel])

theorem ListRel.replicate {α β} {R : α → β → Prop} {a : α} {b : β} (h : R a b) :
    ∀ n, ListRel R (List.replicate n a) (List.replicate n b)
  | 0 => trivial
  | n + 1 => ⟨h, ListRel.replicate h n⟩

/-! ## Memory: reads and writes of related byte ranges -/

/-- Reading the same range of related memories gives related bytes. -/
theorem ByteMemSim.read {ρt : TagRenameMap} {mS mT : bytes.Mem}
    (h : ByteMemSim ρt mS mT) (a n : Nat) :
    ListRel (ByteSim ρt) (mS.read a n) (mT.read a n) :=
  ListRel.map_of (fun i => h (a + i)) (List.range n)

/-- Writing related byte lists at the same address keeps the memories
    related — at ANY address and length, so a one-byte write into the
    middle of a wider value is the same lemma as a whole-value store. -/
theorem ByteMemSim.write {ρt : TagRenameMap} {mS mT : bytes.Mem}
    (h : ByteMemSim ρt mS mT) (a : Nat) {bs bs' : List AbstractByte}
    (hb : ListRel (ByteSim ρt) bs bs') :
    ByteMemSim ρt (mS.write a bs) (mT.write a bs') := by
  intro x
  have hlen := ListRel.length_eq hb
  simp only [bytes.Mem.write]
  rw [← hlen]
  split
  · exact ListRel.getD (dS := .uninit) (dT := .uninit) trivial hb (x - a)
  · exact h x

/-- A raw byte copy (`copyBytes`) keeps memories related. -/
theorem ByteMemSim.copyBytes {ρt : TagRenameMap} {mS mT : bytes.Mem}
    (h : ByteMemSim ρt mS mT) (dst src n : Nat) :
    ByteMemSim ρt (mS.copyBytes dst src n) (mT.copyBytes dst src n) :=
  h.write dst (h.read src n)

/-- Allocation in lockstep returns the same base and keeps both relations
    (allocation does not touch the bytes). -/
theorem ByteMemSim.allocate {ρt : TagRenameMap} {mS mT : bytes.Mem}
    (h : ByteMemSim ρt mS mT) (hl : ByteAllocLockstep mS mT) (size align : Nat) :
    (mT.allocate size align).1 = (mS.allocate size align).1 ∧
    ByteMemSim ρt (mS.allocate size align).2 (mT.allocate size align).2 ∧
    ByteAllocLockstep (mS.allocate size align).2 (mT.allocate size align).2 := by
  obtain ⟨ha, hn, hf⟩ := hl
  refine ⟨by simp [bytes.Mem.allocate, hn], fun x => h x, ?_⟩
  simp [ByteAllocLockstep, bytes.Mem.allocate, ha, hn, hf]

/-! ## Values: decoding and encoding related bytes -/

/-- Addresses are not renamed: both machines allocate in lockstep. -/
def idA : AddrRenameMap := fun a => some a

/-- A target value related to a source value (both held as `MemValue`s;
    the relation is `MemValSim` at identity addresses). -/
def ValSim (ρt : TagRenameMap) (v w : MemValue) : Prop :=
  MemValSim idA ρt v (oseair.ofMem w)

theorem ProvSim.functional {ρt : TagRenameMap} :
    ∀ {p q q' : Option Prov}, ProvSim ρt p q → ProvSim ρt p q' → q = q'
  | none, none, none, _, _ => rfl
  | some p, some q, some q', ⟨hb, hs, he, ht⟩, ⟨hb', hs', he', ht'⟩ => by
      have htag : q.tag = q'.tag := by rw [ht] at ht'; exact Option.some.inj ht'
      cases q; cases q'; simp_all
  | none, some _, _, h, _ => absurd h (by simp [ProvSim])
  | none, none, some _, _, h => absurd h (by simp [ProvSim])
  | some _, none, _, h, _ => absurd h (by simp [ProvSim])
  | some _, some _, none, _, h => absurd h (by simp [ProvSim])

theorem ProvSim.injective {ρt : TagRenameMap} (hwf : TagRenameWF ρt) :
    ∀ {p p' q : Option Prov}, ProvSim ρt p q → ProvSim ρt p' q → p = p'
  | none, none, none, _, _ => rfl
  | some p, some p', some q, ⟨hb, hs, he, ht⟩, ⟨hb', hs', he', ht'⟩ => by
      have htag : p.tag = p'.tag := hwf.1 _ _ _ ht ht'
      cases p; cases p'; simp_all
  | none, some _, none, _, h => absurd h (by simp [ProvSim])
  | some _, none, none, h, _ => absurd h (by simp [ProvSim])
  | none, _, some _, h, _ => absurd h (by simp [ProvSim])
  | some _, _, none, h, _ => absurd h (by simp [ProvSim])

/-- Renaming preserves "every byte carries the same provenance": the
    tag renaming is a function (same in, same out) and injective (a
    disagreement cannot be renamed into an agreement). -/
theorem all_eq_sim {ρt : TagRenameMap} (hwf : TagRenameWF ρt) {p p' : Option Prov}
    (hp : ProvSim ρt p p') :
    ∀ {rest : List (Option Prov)} {rest' : List (Option Prov)},
      ListRel (ProvSim ρt) rest rest' →
      rest.all (fun x => decide (x = p)) = rest'.all (fun x => decide (x = p'))
  | [], [], _ => rfl
  | x :: xs, x' :: xs', h => by
      have ih := all_eq_sim hwf hp h.2
      simp only [List.all_cons, ih]
      by_cases hx : x = p
      · subst hx
        have : x' = p' := ProvSim.functional h.1 hp
        simp [this]
      · have : x' ≠ p' := fun h' => hx (ProvSim.injective hwf h.1 (h' ▸ hp))
        simp [hx, this]
  | [], _ :: _, h => absurd h (by simp [ListRel])
  | _ :: _, [], h => absurd h (by simp [ListRel])

theorem commonProv_sim {ρt : TagRenameMap} (hwf : TagRenameWF ρt) :
    ∀ {ps ps' : List (Option Prov)}, ListRel (ProvSim ρt) ps ps' →
      ProvSim ρt (commonProv ps) (commonProv ps')
  | [], [], _ => trivial
  | p :: rest, p' :: rest', h => by
      simp only [commonProv, all_eq_sim hwf h.1 h.2]
      split
      · exact h.1
      · trivial
  | [], _ :: _, h => absurd h (by simp [ListRel])
  | _ :: _, [], h => absurd h (by simp [ListRel])

theorem mapM_byte_sim {ρt : TagRenameMap} :
    ∀ {bs bs' : List AbstractByte} {raw : List (Fin 256)}, ListRel (ByteSim ρt) bs bs' →
      bs.mapM AbstractByte.byte? = some raw → bs'.mapM AbstractByte.byte? = some raw
  | [], [], _, _, h => h
  | b :: bs, b' :: bs', raw, hr, h => by
      cases b with
      | uninit => simp [List.mapM_cons, AbstractByte.byte?] at h
      | init x p =>
          cases b' with
          | uninit => exact absurd hr.1 (by simp [ByteSim])
          | init x' p' =>
              have hx : x' = x := hr.1.1
              subst hx
              cases hrest : bs.mapM AbstractByte.byte? with
              | none => simp [List.mapM_cons, AbstractByte.byte?, hrest] at h
              | some rs =>
                  have ih := mapM_byte_sim hr.2 hrest
                  simp [List.mapM_cons, AbstractByte.byte?, hrest] at h
                  simp [List.mapM_cons, AbstractByte.byte?, ih, h]
  | [], _ :: _, _, hr, _ => absurd hr (by simp [ListRel])
  | _ :: _, [], _, hr, _ => absurd hr (by simp [ListRel])

theorem mapM_prov_sim {ρt : TagRenameMap} :
    ∀ {bs bs' : List AbstractByte} {ps : List (Option Prov)}, ListRel (ByteSim ρt) bs bs' →
      bs.mapM AbstractByte.prov? = some ps →
      ∃ ps', bs'.mapM AbstractByte.prov? = some ps' ∧ ListRel (ProvSim ρt) ps ps'
  | [], [], ps, _, h => by
      simp at h; subst h; exact ⟨[], rfl, trivial⟩
  | b :: bs, b' :: bs', ps, hr, h => by
      cases b with
      | uninit => simp [List.mapM_cons, AbstractByte.prov?] at h
      | init x p =>
          cases b' with
          | uninit => exact absurd hr.1 (by simp [ByteSim])
          | init x' p' =>
              cases hrest : bs.mapM AbstractByte.prov? with
              | none => simp [List.mapM_cons, AbstractByte.prov?, hrest] at h
              | some rs =>
                  obtain ⟨rs', hrs', hrel⟩ := mapM_prov_sim hr.2 hrest
                  simp [List.mapM_cons, AbstractByte.prov?, hrest] at h
                  subst h
                  exact ⟨p' :: rs', by simp [List.mapM_cons, AbstractByte.prov?, hrs'],
                    hr.1.2, hrel⟩
  | [], _ :: _, _, hr, _ => absurd hr (by simp [ListRel])
  | _ :: _, [], _, hr, _ => absurd hr (by simp [ListRel])

/-- Decoding related bytes at ANY scalar type gives related values — an
    integer read of a pointer's bytes, a pointer read of mixed bytes, a
    one-byte read out of a wider value. -/
theorem decodeV_sim {ρt : TagRenameMap} (hwf : TagRenameWF ρt) (k : Scalar)
    {bs bs' : List AbstractByte} (h : ListRel (ByteSim ρt) bs bs') :
    ValSim ρt (mirlite.decodeV k bs) (mirlite.decodeV k bs') := by
  cases k with
  | int n =>
      simp only [mirlite.decodeV, decodeInt]
      cases hs : bs.mapM AbstractByte.byte? with
      | none => simp [ValSim, MemValSim]
      | some raw =>
          rw [mapM_byte_sim h hs]
          simp [ValSim, MemValSim, oseair.ofMem]
  | ptr =>
      have hlen := ListRel.length_eq h
      unfold mirlite.decodeV decodePtr
      rw [← hlen]
      by_cases hl : bs.length = ptrSize
      · simp only [hl, if_true]
        cases hs : bs.mapM AbstractByte.byte? with
        | none => simp [ValSim, MemValSim]
        | some raw =>
            cases hp : bs.mapM AbstractByte.prov? with
            | none => simp [ValSim, MemValSim]
            | some ps =>
                obtain ⟨ps', hp', hrel⟩ := mapM_prov_sim h hp
                have hc := commonProv_sim hwf hrel
                rw [mapM_byte_sim h hs, hp']
                simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def]
                cases hcs : commonProv ps <;> cases hct : commonProv ps' <;>
                  rw [hcs, hct] at hc <;> simp only [ProvSim] at hc
                · simp [ValSim, MemValSim, oseair.ofMem, hwf.2, idA]
                · obtain ⟨hb, hsz, he, ht⟩ := hc
                  simp [ValSim, MemValSim, oseair.ofMem, idA, hb, hsz, he, ht]
      · simp [hl, ValSim, MemValSim]

/-! ## Values: encoding -/

/-- The relation a STORE needs: an undefined source value is stored as
    undefined on both sides (an `uninit` rvalue); any other value is
    related as `ValSim`. -/
def StoreSim (ρt : TagRenameMap) (v w : MemValue) : Prop :=
  (v = .undef ∧ w = .undef) ∨ (v ≠ .undef ∧ ValSim ρt v w)

theorem tagBytes_sim {ρt : TagRenameMap} {p p' : Option Prov} (h : ProvSim ρt p p')
    (l : List (Fin 256)) : ListRel (ByteSim ρt) (tagBytes p l) (tagBytes p' l) :=
  ListRel.map_of (fun _ => ⟨rfl, h⟩) l

theorem encodeAt_sim {ρt : TagRenameMap} {k : Scalar} {v w : MemValue}
    {bs : List AbstractByte} (h : StoreSim ρt v w) (he : mirlite.encodeAt k v = .ok bs) :
    ∃ bs', mirlite.encodeAt k w = .ok bs' ∧ ListRel (ByteSim ρt) bs bs' := by
  rcases h with ⟨rfl, rfl⟩ | ⟨hne, hv⟩
  · exact ⟨bs, he, by
      simp only [mirlite.encodeAt, Except.ok.injEq] at he
      subst he; exact ListRel.replicate trivial _⟩
  · cases v with
    | undef => exact absurd rfl hne
    | word x =>
        cases w <;> simp [ValSim, MemValSim, oseair.ofMem] at hv
        subst hv
        refine ⟨bs, he, ?_⟩
        simp only [mirlite.encodeAt] at he
        split at he
        · simp only [Except.ok.injEq] at he; subst he
          exact tagBytes_sim (p := none) (p' := none) trivial _
        · cases he
    | ptrVal b o e sz t =>
        cases w with
        | ptrVal b' o' e' sz' t' =>
            simp only [ValSim, MemValSim, oseair.ofMem, idA, Option.some.injEq] at hv
            obtain ⟨rfl, rfl, rfl, rfl, ht, -⟩ := hv
            simp only [mirlite.encodeAt] at he ⊢
            split at he
            · simp only [Except.ok.injEq] at he; subst he
              rw [if_pos ‹_›]
              exact ⟨_, rfl, ListRel.take _ (tagBytes_sim (by
                simp [ProvSim, ht]) _)⟩
            · cases he
        | _ => simp [ValSim, MemValSim, oseair.ofMem] at hv

/-! ## Whole values at a layout -/

/-- Reading a value of ANY byte layout (padding, narrow fields, reordered
    structs) from related memories gives related values, leaf by leaf. -/
theorem readL_sim {ρt : TagRenameMap} (hwf : TagRenameWF ρt) {mS mT : bytes.Mem}
    (h : ByteMemSim ρt mS mT) (a : Nat) (lay : BLayout) :
    ListRel (ValSim ρt) (mirlite.readL mS a lay) (mirlite.readL mT a lay) :=
  ListRel.map_of (fun ⟨o, k⟩ => decodeV_sim hwf k (h.read (a + o) k.size)) lay.leaves

/-- A monadic left fold over related lists, with a step that preserves a
    relation, preserves it. -/
theorem foldlM_sim {ε σ σ' α β : Type} (RS : σ → σ' → Prop) (RA : α → β → Prop)
    (f : σ → α → Except ε σ) (g : σ' → β → Except ε σ')
    (hstep : ∀ s s' a b s1, RS s s' → RA a b → f s a = .ok s1 →
      ∃ s1', g s' b = .ok s1' ∧ RS s1 s1') :
    ∀ {as : List α} {bs : List β} (s : σ) (s' : σ') (s1 : σ),
      ListRel RA as bs → RS s s' → as.foldlM f s = .ok s1 →
      ∃ s1', bs.foldlM g s' = .ok s1' ∧ RS s1 s1'
  | [], [], s, s', s1, _, hs, h => by
      simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
      subst h; exact ⟨s', rfl, hs⟩
  | a :: as, b :: bs, s, s', s1, hr, hs, h => by
      simp only [List.foldlM_cons] at h ⊢
      cases hf : f s a with
      | error e => rw [hf] at h; cases h
      | ok s2 =>
          rw [hf] at h
          obtain ⟨s2', hg, hs2⟩ := hstep s s' a b s2 hs hr.1 hf
          rw [hg]
          exact foldlM_sim RS RA f g hstep s2 s2' s1 hr.2 hs2 h
  | [], _ :: _, _, _, _, hr, _, _ => absurd hr (by simp [ListRel])
  | _ :: _, [], _, _, _, hr, _, _ => absurd hr (by simp [ListRel])

/-- `foldlM_sim` with the SAME step on both sides (as both machines' stores
    use one encoder). -/
theorem foldlM_sim_same {ε σ α : Type} (RS : σ → σ → Prop) (RA : α → α → Prop)
    (f : σ → α → Except ε σ)
    (hstep : ∀ s s' a b s1, RS s s' → RA a b → f s a = .ok s1 →
      ∃ s1', f s' b = .ok s1' ∧ RS s1 s1') :
    ∀ {as bs : List α} (s s' s1 : σ),
      ListRel RA as bs → RS s s' → as.foldlM f s = .ok s1 →
      ∃ s1', bs.foldlM f s' = .ok s1' ∧ RS s1 s1' :=
  foldlM_sim RS RA f f hstep

theorem zip_sim {α β γ : Type} {R : β → γ → Prop} :
    ∀ (ls : List α) {vs : List β} {ws : List γ}, ListRel R vs ws →
      ListRel (fun (p : α × β) (q : α × γ) => p.1 = q.1 ∧ R p.2 q.2) (ls.zip vs) (ls.zip ws)
  | [], _, _, _ => by simp [ListRel]
  | _ :: _, [], [], _ => by simp [ListRel]
  | l :: ls, _ :: _, _ :: _, h => ⟨⟨rfl, h.1⟩, zip_sim ls h.2⟩
  | _ :: _, [], _ :: _, h => absurd h (by simp [ListRel])
  | _ :: _, _ :: _, [], h => absurd h (by simp [ListRel])

/-- Storing related values at ANY byte layout into related memories keeps
    them related: each leaf is encoded at its width and overlaid on a
    buffer whose padding is uninit, on both sides. A store into a narrow
    field, or one that resets padding, is this lemma. -/
theorem writeL_sim {ρt : TagRenameMap} {mS mT mS' : bytes.Mem}
    (h : ByteMemSim ρt mS mT) {a : Nat} {lay : BLayout} {vs ws : List MemValue}
    (hv : ListRel (StoreSim ρt) vs ws) (hw : mirlite.writeL mS a lay vs = .ok mS') :
    ∃ mT', mirlite.writeL mT a lay ws = .ok mT' ∧ ByteMemSim ρt mS' mT' := by
  have hlen := ListRel.length_eq hv
  unfold mirlite.writeL at hw ⊢
  rw [← hlen]
  by_cases hc : (vs.length != lay.leaves.length) = true
  · rw [if_pos hc] at hw; cases hw
  · rw [if_neg hc] at hw ⊢
    simp only [bind, Except.bind, pure, Except.pure] at hw ⊢
    split at hw
    · cases hw
    · rename_i buf hbuf
      simp only [Except.ok.injEq] at hw
      subst hw
      obtain ⟨buf', hbuf', hrel⟩ := foldlM_sim_same (ListRel (ByteSim ρt))
        (fun (p q : (Nat × Scalar) × MemValue) => p.1 = q.1 ∧ StoreSim ρt p.2 q.2) _
        (fun s s' x y s1 hs hxy hf => by
          obtain ⟨⟨o, k⟩, v⟩ := x
          obtain ⟨⟨o', k'⟩, w⟩ := y
          obtain ⟨hok, hst⟩ := hxy
          simp only [Prod.mk.injEq] at hok
          obtain ⟨rfl, rfl⟩ := hok
          simp only at hf hst ⊢
          split at hf
          · cases hf
          · rename_i bs hbs
            simp only [Except.ok.injEq] at hf
            subst hf
            obtain ⟨bs', hbs', hrb⟩ := encodeAt_sim hst hbs
            rw [hbs']
            refine ⟨_, rfl, ?_⟩
            rw [← ListRel.length_eq hrb]
            exact ListRel.append (ListRel.append (ListRel.take _ hs) hrb) (ListRel.drop _ hs))
        _ _ buf (zip_sim lay.leaves hv) (ListRel.replicate trivial _) hbuf
      rw [hbuf']
      exact ⟨_, rfl, h.write a hrel⟩

/-! ## The two steps every leaf needs: a store and a load

Memory and permissions together, for the byte machines' typed accesses at
ANY byte layout — the step a compiled store or load performs on each
side. The permission half is `sb_*_respects_PermSim`,
unchanged: a per-byte stack is a stack, and a one-byte borrow's range is
just a short range. -/

/-- A typed store: the SB write over the value's bytes, then the encoded
    leaves. If the source succeeds, the target (same address, renamed tag,
    related values) succeeds, and both relations hold after. -/
theorem store_step_sim {ρt : TagRenameMap} (hwf : TagRenameWF ρt)
    {pS pT pS' : AccessPerms} {mS mT mS' : bytes.Mem}
    (hp : PermSim ρt pS pT) (hm : ByteMemSim ρt mS mT)
    {tagS tagT : Tag} (ht : ρt tagS = some tagT)
    {a : Nat} {lay : BLayout} {vs ws : List MemValue} (hv : ListRel (StoreSim ρt) vs ws)
    (hu : sb_write pS a lay.size tagS = .ok pS')
    (hw : mirlite.writeL mS a lay vs = .ok mS') :
    ∃ pT' mT', sb_write pT a lay.size tagT = .ok pT' ∧
      mirlite.writeL mT a lay ws = .ok mT' ∧
      PermSim ρt pS' pT' ∧ ByteMemSim ρt mS' mT' := by
  obtain ⟨pT', hu', hp'⟩ := sb_write_respects_PermSim hp hwf ht hu
  obtain ⟨mT', hw', hm'⟩ := writeL_sim hm hv hw
  exact ⟨pT', mT', hu', hw', hp', hm'⟩

/-- A typed load: the SB read over the value's bytes, then the decoded
    leaves. The target read succeeds and yields related values. -/
theorem load_step_sim {ρt : TagRenameMap} (hwf : TagRenameWF ρt)
    {pS pT pS' : AccessPerms} {mS mT : bytes.Mem}
    (hp : PermSim ρt pS pT) (hm : ByteMemSim ρt mS mT)
    {tagS tagT : Tag} (ht : ρt tagS = some tagT)
    {a : Nat} {lay : BLayout}
    (hu : sb_read pS a lay.size tagS = .ok pS') :
    ∃ pT', sb_read pT a lay.size tagT = .ok pT' ∧ PermSim ρt pS' pT' ∧
      ListRel (ValSim ρt) (mirlite.readL mS a lay) (mirlite.readL mT a lay) := by
  obtain ⟨pT', hu', hp'⟩ := sb_read_respects_PermSim hp hwf ht hu
  exact ⟨pT', hu', hp', readL_sim hwf hm a lay⟩

/-- A SUB-CELL store is the same lemma: a one-byte integer written at an
    address inside a wider value (`*(&mut s.b as *mut u32 as *mut u8) =
    0xFF`, local/narrow_fields_ok) keeps both relations, the rest of the
    wider value's bytes untouched on both sides. -/
theorem subcell_store_sim {ρt : TagRenameMap} (hwf : TagRenameWF ρt)
    {pS pT pS' : AccessPerms} {mS mT mS' : bytes.Mem}
    (hp : PermSim ρt pS pT) (hm : ByteMemSim ρt mS mT)
    {tagS tagT : Tag} (ht : ρt tagS = some tagT) {a x : Nat}
    (hu : sb_write pS a 1 tagS = .ok pS')
    (hw : mirlite.writeL mS a (.int 1) [.word x] = .ok mS') :
    ∃ pT' mT', sb_write pT a 1 tagT = .ok pT' ∧
      mirlite.writeL mT a (.int 1) [.word x] = .ok mT' ∧
      PermSim ρt pS' pT' ∧ ByteMemSim ρt mS' mT' :=
  store_step_sim hwf hp hm ht
    (show ListRel (StoreSim ρt) [.word x] [.word x] from
      ⟨Or.inr ⟨by simp, by simp [ValSim, MemValSim, oseair.ofMem]⟩, trivial⟩) hu hw

end obseq3.proof
