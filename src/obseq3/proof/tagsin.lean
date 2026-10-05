import obseq3.proof.memsim

/-!
# Where a tag can be

`MemOK P m`: every pointer tag in memory `m` satisfies `P`; `ValsOK P vs`:
every pointer tag in the values `vs` does. `MemOK` is the byte relation of
`memsim.lean` of `m` with itself under the partial identity `keepMap P`
(defined exactly on `P`), so reads (`decodeV_sim`) and stores
(`writeL_sim`) carry it for free.
-/

namespace obseq3.proof

open obseq3 obseq3.bytes
open obseq3.mirlite (MemValue)
open obseq3.oseair (Val)

open Classical in
/-- The partial identity on the tags satisfying `P`. -/
noncomputable def keepMap (P : Tag → Prop) : TagRenameMap :=
  fun t => if P t then some t else none

theorem keepMap_some {P : Tag → Prop} {t t' : Tag} :
    keepMap P t = some t' ↔ P t ∧ t' = t := by
  unfold keepMap
  by_cases h : P t
  · simp [h, eq_comm]
  · simp [h]

theorem keepMap_wf {P : Tag → Prop} (h0 : P wildcardTag) : TagRenameWF (keepMap P) :=
  ⟨fun t1 t2 t' h1 h2 => by
    rw [keepMap_some] at h1 h2
    rw [← h1.2, h2.2],
   keepMap_some.mpr ⟨h0, rfl⟩⟩

/-- Every pointer tag in memory satisfies `P`. -/
def MemOK (P : Tag → Prop) (m : bytes.Mem) : Prop := ByteMemSim (keepMap P) m m

theorem MemOK_iff {P : Tag → Prop} {m : bytes.Mem} :
    MemOK P m ↔ ∀ a b p, m.bytes a = .init b (some p) → P p.tag := by
  constructor
  · intro h a b p hb
    have := h a
    rw [hb] at this
    exact (keepMap_some.mp this.2.2.2.2).1
  · intro h a
    cases hb : m.bytes a with
    | uninit => trivial
    | init b p =>
        refine ⟨rfl, ?_⟩
        cases p with
        | none => trivial
        | some p => exact ⟨rfl, rfl, rfl, keepMap_some.mpr ⟨h a b p hb, rfl⟩⟩

theorem MemOK.mono {P Q : Tag → Prop} {m : bytes.Mem} (h : MemOK P m)
    (hPQ : ∀ t, P t → Q t) : MemOK Q m :=
  MemOK_iff.mpr fun a b p hb => hPQ _ (MemOK_iff.mp h a b p hb)

theorem MemOK.and {P Q : Tag → Prop} {m : bytes.Mem} (hP : MemOK P m) (hQ : MemOK Q m) :
    MemOK (fun t => P t ∧ Q t) m :=
  MemOK_iff.mpr fun a b p hb => ⟨MemOK_iff.mp hP a b p hb, MemOK_iff.mp hQ a b p hb⟩

/-- Every pointer tag in the values satisfies `P`. -/
def ValsOK (P : Tag → Prop) (vs : List Val) : Prop :=
  ∀ v ∈ vs, ∀ b o e s t, v = .Ptr b o e s t → P t

theorem ValsOK.mono {P Q : Tag → Prop} {vs : List Val} (h : ValsOK P vs)
    (hPQ : ∀ t, P t → Q t) : ValsOK Q vs :=
  fun v hv b o e s t he => hPQ _ (h v hv b o e s t he)

theorem ValsOK.and {P Q : Tag → Prop} {vs : List Val} (hP : ValsOK P vs) (hQ : ValsOK Q vs) :
    ValsOK (fun t => P t ∧ Q t) vs :=
  fun v hv b o e s t he => ⟨hP v hv b o e s t he, hQ v hv b o e s t he⟩

theorem ValsOK.nil (P : Tag → Prop) : ValsOK P [] := fun _ h => by cases h

theorem ValsOK.dat (P : Tag → Prop) (w : Word) : ValsOK P [.Dat w] := by
  intro v hv b o e s t he
  simp at hv; subst hv; cases he

theorem ValsOK.ptr {P : Tag → Prop} {b o e s t : Nat} (h : P t) :
    ValsOK P [.Ptr b o e s t] := by
  intro v hv b' o' e' s' t' he
  simp at hv; subst hv; cases he; exact h

/-- A decoded leaf's tag is one of the memory's. -/
theorem MemOK.decodeV {P : Tag → Prop} {m : bytes.Mem} (h : MemOK P m) (h0 : P wildcardTag)
    (k : Scalar) (a n : Nat) :
    ValsOK P [oseair.ofMem (mirlite.decodeV k (m.read a n))] := by
  have hs := decodeV_sim (keepMap_wf h0) k (h.read a n)
  intro v hv b o e s t he
  simp at hv; subst hv
  cases hd : mirlite.decodeV k (m.read a n) with
  | undef => rw [hd] at he; cases he
  | word w => rw [hd] at he; cases he
  | ptrVal b' o' e' s' t' =>
      rw [hd] at he hs
      simp only [oseair.ofMem, Val.Ptr.injEq] at he
      obtain ⟨-, -, -, -, rfl⟩ := he
      exact (keepMap_some.mp hs.2.2.2.2.1).1

theorem MemOK.readL {P : Tag → Prop} {m : bytes.Mem} (h : MemOK P m) (h0 : P wildcardTag)
    (addr : Nat) (lay : BLayout) :
    ValsOK P ((mirlite.readL m addr lay).map oseair.ofMem) := by
  intro v hv
  simp only [mirlite.readL, List.map_map, List.mem_map] at hv
  obtain ⟨⟨o, k⟩, -, rfl⟩ := hv
  exact h.decodeV h0 k (addr + o) k.sizeB _ (List.mem_singleton_self _)

/-- A store of values whose tags satisfy `P` keeps the memory's. -/
theorem MemOK.writeL {P : Tag → Prop} {m m' : bytes.Mem} (h : MemOK P m) (h0 : P wildcardTag)
    {a : Nat} {lay : BLayout} {vals : List Val} (hv : ValsOK P vals)
    (hw : mirlite.writeL m a lay (vals.map Val.toMem) = .ok m') : MemOK P m' := by
  have hrel : ListRel (StoreSim (keepMap P)) (vals.map Val.toMem) (vals.map Val.toMem) := by
    have : ∀ l : List Val, (∀ v ∈ l, ∀ b o e s t, v = .Ptr b o e s t → P t) →
        ListRel (StoreSim (keepMap P)) (l.map Val.toMem) (l.map Val.toMem) := by
      intro l
      induction l with
      | nil => intro _; trivial
      | cons v l ih =>
          intro hl
          refine ⟨?_, ih fun w hw => hl w (List.mem_cons_of_mem _ hw)⟩
          cases v with
          | Undef => exact Or.inl ⟨rfl, rfl⟩
          | Dat w => exact Or.inr ⟨by simp [Val.toMem], rfl⟩
          | Ptr b o e s t =>
              refine Or.inr ⟨by simp [Val.toMem], ?_⟩
              simp only [ValSim, MemValSim, Val.toMem, oseair.ofMem, idA]
              refine ⟨trivial, trivial, trivial, trivial,
                keepMap_some.mpr ⟨hl _ List.mem_cons_self b o e s t rfl, rfl⟩,
                fun k _ => ⟨_, rfl⟩⟩
    exact this vals hv
  obtain ⟨m'', hw', hs⟩ := writeL_sim h hrel hw
  rw [hw] at hw'
  obtain rfl := Except.ok.inj hw'
  exact hs

/-- Uninit bytes carry no tag. -/
theorem MemOK.write_uninit {P : Tag → Prop} {m : bytes.Mem} (h : MemOK P m) (a n : Nat) :
    MemOK P (m.write a (List.replicate n .uninit)) :=
  ByteMemSim.write h a (ListRel.replicate trivial n)

theorem MemOK.of_bytes {P : Tag → Prop} {m m' : bytes.Mem} (h : MemOK P m)
    (hb : m'.bytes = m.bytes) : MemOK P m' := by
  intro a; rw [hb]; exact h a

end obseq3.proof
