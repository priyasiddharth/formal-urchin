import obseq3.proof.die_back_check

/-!
# Route brackets in emitted code: segments

The compiler lays down code in contiguous SEGMENTS (`Emits`). `Seg live ins
lo hi seg` records what a segment keeps: every register it mentions is
live (a local's), passed in (`ins`), or one it created (index in the
window `[lo, hi)`); every `Die` closes a route bracket inside the segment,
on a register of the window; no `CStore` writes a pointer literal.
Segments compose (`Seg.append`, `Seg.snoc`, `Seg.close`), and a
program made of statement segments is a `RouteProg` (`route_compile.lean`).
-/

namespace obseq3.proof

open obseq3 obseq3.compile obseq3.oseair

def regIdx : Register → Nat
  | .R i => i

/-! ## Emitted segments -/

/-- `cs'` holds `seg` at `cs.nextLabel`, and ends right after it. -/
def Emits (cs cs' : CompilerState) (seg : List Instr) : Prop :=
  cs'.nextLabel = cs.nextLabel + seg.length ∧
    ∀ k (hk : k < seg.length), cs'.code (cs.nextLabel + k) = some seg[k]

theorem Emits.nil (cs : CompilerState) : Emits cs cs [] := ⟨by simp, fun k hk => by simp at hk⟩

theorem Emits.of_eq {cs cs' : CompilerState} (hl : cs'.nextLabel = cs.nextLabel)
    : Emits cs cs' [] := ⟨by simp [hl], fun k hk => by simp at hk⟩

theorem Emits.emit (cs : CompilerState) (l : List Instr) : Emits cs (compile.emit cs l) l := by
  refine ⟨rfl, fun k hk => ?_⟩
  simp only [compile.emit]
  rw [if_pos ⟨by omega, by omega⟩]
  simp [hk]

theorem Emits.trans {cs1 cs2 cs3 : CompilerState} {s1 s2 : List Instr}
    (h1 : Emits cs1 cs2 s1) (hi : StateIncr cs2 cs3) (h2 : Emits cs2 cs3 s2) :
    Emits cs1 cs3 (s1 ++ s2) := by
  refine ⟨by rw [h2.1, h1.1, List.length_append, Nat.add_assoc], fun k hk => ?_⟩
  by_cases hk1 : k < s1.length
  · rw [hi.code_eq _ (by rw [h1.1]; omega), h1.2 k hk1]
    simp [List.getElem_append_left hk1]
  · have := h2.2 (k - s1.length) (by simp at hk; omega)
    rw [h1.1, Nat.add_assoc, show s1.length + (k - s1.length) = k by omega] at this
    rw [this]
    simp [List.getElem_append_right (by omega : s1.length ≤ k)]

/-! ## Segments -/

theorem getElem?_some_lt {α} {l : List α} {q : Nat} {x : α} (h : l[q]? = some x) : q < l.length :=
  (List.getElem?_eq_some_iff.mp h).1

/-- `r` dies in the segment. -/
def DiedIn (seg : List Instr) (r : Register) : Prop := ∃ n, Instr.Die r n ∈ seg

/-- The `Die r n` at `p` closes a route bracket of `seg`, and `r` appears
    in `seg` only there. -/
def ClosedAt (seg : List Instr) (p : Nat) (r : Register) (n : Nat) : Prop :=
  2 ≤ p ∧
  (∃ k base off, PushKind k ∧ seg[p - 2]? = some (.Assgn r (.Borrow k false [] (some n) base off))) ∧
  (∃ i, seg[p - 1]? = some i ∧ i.through r = true) ∧
  (∀ q i, seg[q]? = some i → r ∈ i.regs → p - 2 ≤ q ∧ q ≤ p)

structure Seg (live ins : Register → Prop) (lo hi : Nat) (seg : List Instr) : Prop where
  regs : ∀ i ∈ seg, ∀ x ∈ i.regs, live x ∨ ins x ∨ (lo ≤ regIdx x ∧ regIdx x < hi)
  dies : ∀ p r n, seg[p]? = some (.Die r n) →
    ClosedAt seg p r n ∧ lo ≤ regIdx r ∧ regIdx r < hi
  cst : ∀ i ∈ seg, i.noPtrConst = true

/-- A register the next instruction may mention. -/
def RegOK (live ins : Register → Prop) (lo hi : Nat) (seg : List Instr) (x : Register) : Prop :=
  live x ∨ ins x ∨ (lo ≤ regIdx x ∧ regIdx x < hi ∧ ¬ DiedIn seg x)

theorem Seg.nil (live ins : Register → Prop) (lo hi : Nat) : Seg live ins lo hi [] :=
  ⟨by simp, fun p r n h => by simp at h, by simp⟩

theorem Seg.mono {live ins ins' : Register → Prop} {lo hi hi' : Nat} {seg : List Instr}
    (h : Seg live ins lo hi seg) (hins : ∀ x, ins x → ins' x) (hle : hi ≤ hi') :
    Seg live ins' lo hi' seg := by
  refine ⟨fun i hi x hx => ?_, fun p r n hp => ?_, h.cst⟩
  · rcases h.regs i hi x hx with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl (hins x h1))
    · exact Or.inr (Or.inr ⟨h1.1, by omega⟩)
  · obtain ⟨hc, h1, h2⟩ := h.dies p r n hp
    exact ⟨hc, h1, by omega⟩

/-- A died register is not live and not passed in. -/
theorem Seg.died_fresh {live ins : Register → Prop} {lo hi : Nat} {seg : List Instr}
    (h : Seg live ins lo hi seg) (hlive : ∀ x, live x → regIdx x < lo)
    (hins : ∀ x, ins x → regIdx x < lo) {r : Register} (hd : DiedIn seg r) :
    ¬ live r ∧ ¬ ins r ∧ lo ≤ regIdx r ∧ regIdx r < hi := by
  obtain ⟨n, hn⟩ := hd
  obtain ⟨p, hp, hpe⟩ := List.getElem_of_mem hn
  obtain ⟨-, h1, h2⟩ := h.dies p r n (by rw [List.getElem?_eq_getElem hp, hpe])
  exact ⟨fun hl => by have := hlive r hl; omega, fun hi => by have := hins r hi; omega, h1, h2⟩

theorem ClosedAt.append_right {seg seg' : List Instr} {p : Nat} {r : Register} {n : Nat}
    (h : ClosedAt seg p r n) (hp : p < seg.length) (hr : ∀ i ∈ seg', r ∉ i.regs) :
    ClosedAt (seg ++ seg') p r n := by
  obtain ⟨h2, ⟨k, b, o, hk, hb⟩, ⟨i, hi, ht⟩, hm⟩ := h
  refine ⟨h2, ⟨k, b, o, hk, ?_⟩, ⟨i, ?_, ht⟩, fun q j hq hj => ?_⟩
  · rw [List.getElem?_append_left (by omega)]; exact hb
  · rw [List.getElem?_append_left (by omega)]; exact hi
  · by_cases hql : q < seg.length
    · rw [List.getElem?_append_left hql] at hq; exact hm q j hq hj
    · rw [List.getElem?_append_right (by omega)] at hq
      exact absurd hj (hr j (List.mem_of_getElem? hq))

theorem ClosedAt.append_left {seg seg' : List Instr} {p : Nat} {r : Register} {n : Nat}
    (h : ClosedAt seg' p r n) (hr : ∀ i ∈ seg, r ∉ i.regs) :
    ClosedAt (seg ++ seg') (seg.length + p) r n := by
  obtain ⟨h2, ⟨k, b, o, hk, hb⟩, ⟨i, hi, ht⟩, hm⟩ := h
  refine ⟨by omega, ⟨k, b, o, hk, ?_⟩, ⟨i, ?_, ht⟩, fun q j hq hj => ?_⟩
  · rw [List.getElem?_append_right (by omega), show seg.length + p - 2 - seg.length = p - 2 by omega]
    exact hb
  · rw [List.getElem?_append_right (by omega), show seg.length + p - 1 - seg.length = p - 1 by omega]
    exact hi
  · by_cases hql : q < seg.length
    · rw [List.getElem?_append_left hql] at hq
      exact absurd hj (hr j (List.mem_of_getElem? hq))
    · rw [List.getElem?_append_right (by omega)] at hq
      have := hm _ j hq hj
      omega

/-- Concatenation: the second segment's passed-in registers are the
    first's, live ones, or ones the first created and did not die. -/
theorem Seg.append {live ins ins2 : Register → Prop} {lo mid hi : Nat} {s1 s2 : List Instr}
    (h1 : Seg live ins lo mid s1) (h2 : Seg live ins2 mid hi s2)
    (hlive : ∀ x, live x → regIdx x < lo) (hins : ∀ x, ins x → regIdx x < lo)
    (hins2 : ∀ x, ins2 x → RegOK live ins lo mid s1 x) (hlm : lo ≤ mid) (hmh : mid ≤ hi) :
    Seg live ins lo hi (s1 ++ s2) := by
  -- a register `s1` dies is not mentioned by `s2`, and conversely
  have h12 : ∀ r, DiedIn s1 r → ∀ i ∈ s2, r ∉ i.regs := by
    intro r hd i hi hr
    obtain ⟨hnl, hni, hlo, hhi⟩ := h1.died_fresh hlive hins hd
    rcases h2.regs i hi r hr with h | h | h
    · exact hnl h
    · rcases hins2 r h with h' | h' | h'
      · exact hnl h'
      · exact hni h'
      · exact h'.2.2 hd
    · omega
  have h21 : ∀ r, DiedIn s2 r → ∀ i ∈ s1, r ∉ i.regs := by
    intro r hd i hi hr
    obtain ⟨n, hn⟩ := hd
    obtain ⟨p, hp, hpe⟩ := List.getElem_of_mem hn
    obtain ⟨-, hlo, -⟩ := h2.dies p r n (by rw [List.getElem?_eq_getElem hp, hpe])
    rcases h1.regs i hi r hr with h | h | h
    · have := hlive r h; omega
    · have := hins r h; omega
    · omega
  refine ⟨fun i hi x hx => ?_, fun p r n hp => ?_, fun i hi => ?_⟩
  · rcases List.mem_append.mp hi with hi | hi
    · rcases h1.regs i hi x hx with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨h.1, by omega⟩)
    · rcases h2.regs i hi x hx with h | h | h
      · exact Or.inl h
      · rcases hins2 x h with h' | h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inl h')
        · exact Or.inr (Or.inr ⟨h'.1, by omega⟩)
      · exact Or.inr (Or.inr ⟨by omega, h.2⟩)
  · by_cases hpl : p < s1.length
    · rw [List.getElem?_append_left hpl] at hp
      obtain ⟨hc, hlo, hhi⟩ := h1.dies p r n hp
      exact ⟨hc.append_right hpl (h12 r ⟨n, List.mem_of_getElem? hp⟩), hlo, by omega⟩
    · rw [List.getElem?_append_right (by omega)] at hp
      obtain ⟨hc, hlo, hhi⟩ := h2.dies _ r n hp
      have := hc.append_left (h21 r ⟨n, List.mem_of_getElem? hp⟩)
      rw [show s1.length + (p - s1.length) = p by omega] at this
      exact ⟨this, by omega, hhi⟩
  · rcases List.mem_append.mp hi with hi | hi
    · exact h1.cst i hi
    · exact h2.cst i hi

/-- One instruction that is not a `Die`, whose registers are allowed. -/
theorem Seg.snoc {live ins : Register → Prop} {lo hi hi' : Nat} {seg : List Instr} {i : Instr}
    (h : Seg live ins lo hi seg) (hlive : ∀ x, live x → regIdx x < lo)
    (hins : ∀ x, ins x → regIdx x < lo)
    (hr : ∀ x ∈ i.regs, RegOK live ins lo hi' seg x)
    (hnd : ∀ r n, i ≠ .Die r n) (hc : i.noPtrConst = true)
    (hle : hi ≤ hi') (hlo : lo ≤ hi) :
    Seg live ins lo hi' (seg ++ [i]) := by
  refine Seg.append (ins2 := fun x => x ∈ i.regs ∧ RegOK live ins lo hi seg x) (mid := hi) h ?_
    hlive hins (fun x hx => hx.2) hlo hle
  refine ⟨fun j hj x hx => ?_, fun p r n hp => ?_, ?_⟩
  · simp only [List.mem_singleton] at hj; subst hj
    rcases hr x hx with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl ⟨hx, Or.inr (Or.inl h1)⟩)
    · by_cases hxh : regIdx x < hi
      · exact Or.inr (Or.inl ⟨hx, Or.inr (Or.inr ⟨h1.1, hxh, h1.2.2⟩)⟩)
      · exact Or.inr (Or.inr ⟨by omega, h1.2.1⟩)
  · cases p with
    | zero => simp at hp; exact absurd hp (hnd r n)
    | succ p => simp at hp
  · simpa using hc

/-- Closing a bracket: a route borrow of a fresh `r`, one access through
    it, then `Die r n`. -/
theorem Seg.close {live ins : Register → Prop} {lo hi : Nat} {pre : List Instr}
    {r : Register} {k : RefKind} {n : Nat} {b : Register} {off : Nat} {acc : Instr}
    (h : Seg live ins lo hi (pre ++ [.Assgn r (.Borrow k false [] (some n) b off), acc]))
    (hk : PushKind k) (hacc : acc.through r = true) (hfresh : ∀ i ∈ pre, r ∉ i.regs)
    (hw : lo ≤ regIdx r ∧ regIdx r < hi) :
    Seg live ins lo hi (pre ++ [.Assgn r (.Borrow k false [] (some n) b off), acc, .Die r n]) := by
  have hseg : pre ++ [.Assgn r (.Borrow k false [] (some n) b off), acc, .Die r n] =
      (pre ++ [.Assgn r (.Borrow k false [] (some n) b off), acc]) ++ [.Die r n] := by simp
  rw [hseg]
  -- the new `Die` is the only new instruction; it mentions only `r`
  have hnew : ClosedAt ((pre ++ [.Assgn r (.Borrow k false [] (some n) b off), acc]) ++ [.Die r n])
      (pre.length + 2) r n := by
    refine ⟨by omega, ⟨k, b, off, hk, by simp⟩, ⟨acc, by simp, hacc⟩, fun q i hq hi => ?_⟩
    by_cases hq1 : q < pre.length
    · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left hq1] at hq
      exact absurd hi (hfresh i (List.mem_of_getElem? hq))
    · have := getElem?_some_lt hq
      simp only [List.length_append, List.length_cons, List.length_nil] at this
      omega
  refine ⟨fun i hi x hx => ?_, fun p r' n' hp => ?_, fun i hi => ?_⟩
  · rcases List.mem_append.mp hi with hi | hi
    · exact h.regs i hi x hx
    · simp only [List.mem_singleton] at hi; subst hi
      simp only [Instr.regs, List.mem_singleton] at hx; subst hx
      exact Or.inr (Or.inr hw)
  · by_cases hp2 : p = pre.length + 2
    · subst hp2
      simp at hp
      obtain ⟨rfl, rfl⟩ := hp
      exact ⟨hnew, hw⟩
    · have hpl : p < pre.length + 2 := by
        have := getElem?_some_lt hp
        simp only [List.length_append, List.length_cons, List.length_nil] at this
        omega
      rw [List.getElem?_append_left (by simp; omega)] at hp
      obtain ⟨hc, h1, h2⟩ := h.dies p r' n' hp
      refine ⟨hc.append_right (by simp; omega) fun i hi hr => ?_, h1, h2⟩
      simp only [List.mem_singleton] at hi; subst hi
      simp only [Instr.regs, List.mem_singleton] at hr; subst hr
      -- `r` dies at `p` in the shorter segment: it would be mentioned in `pre`
      obtain ⟨h2', ⟨k', b', o', -, hb'⟩, -, hm⟩ := hc
      have hlt : p - 2 < pre.length := by
        refine Nat.lt_of_not_le fun hge => ?_
        have hp' : p = pre.length + 1 ∨ p = pre.length := by omega
        rcases hp' with rfl | rfl
        · simp at hp; subst hp; simp [Instr.through] at hacc
        · simp at hp
      rw [List.getElem?_append_left hlt] at hb'
      exact hfresh _ (List.mem_of_getElem? hb') (by simp [Instr.regs])
  · rcases List.mem_append.mp hi with hi | hi
    · exact h.cst i hi
    · simp at hi; subst hi; rfl

end obseq3.proof
