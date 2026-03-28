import obseq.proof.core

/-!
# `obseq.proof.state_helpers`

Shared lookup, write, and memory-simulation lemmas used by the concrete proof
clusters. This file intentionally stays cluster-agnostic.

The local preservation proofs in the statement-specific files follow the same
shape: recover concrete source/target addresses, execute one source or target
step, and then show that the simulation relations survive the resulting updates.

This helper layer supports exactly that proof strategy:

- `mem_vals_eq_*` packages the value-level memory agreement facts used by the
  active statement proofs, and
- `state_sim_*` plus the concrete target execution lemmas provide the reusable
  shells those proofs apply after inverting a source step.
-/

namespace obseq.proof

open obseq
open obseq.mirlite
open obseq.oseair hiding State Result
open obseq.compile
open scoped obseq.notation

/-! ## Axioms -/

axiom alloc_fresh_disjoint
  {π : PlaceMap}
  {ρa : AddrRenaming}
  {ρt : TagRenaming}
  {s_mir : mirlite.State}
  {s_osea : oseair.State}
  {freshAddr_m freshAddr_o : Word}
  {freshLayout : LayoutTy}
  (h_sim : StateSim π ρa ρt s_mir s_osea)
  {base : Word}
  {reg : Register}
  {layout : LayoutTy}
  (h_lookup : π.lookup base = some (reg, layout))
  {addr_m addr_o tag_m tag_o : Word}
  (h_ptr :
    place_runtime_sim π ρa ρt s_mir s_osea
      base reg addr_m addr_o tag_m tag_o layout) :
  addr_m ≠ freshAddr_m ∧
  blocks_disjoint addr_m (blockSize layout) freshAddr_m (blockSize freshLayout) ∧
  blocks_disjoint addr_o (blockSize layout) freshAddr_o (blockSize freshLayout)

axiom alloc_fresh_tag
  {π : PlaceMap}
  {ρa : AddrRenaming}
  {ρt : TagRenaming}
  {s_mir : mirlite.State}
  {s_osea : oseair.State}
  {freshTag : Word}
  (h_sim : StateSim π ρa ρt s_mir s_osea)
  {base : Word}
  {reg : Register}
  {layout : LayoutTy}
  (h_lookup : π.lookup base = some (reg, layout))
  {addr_m addr_o tag_m tag_o : Word}
  (h_ptr :
    place_runtime_sim π ρa ρt s_mir s_osea
      base reg addr_m addr_o tag_m tag_o layout) :
  tag_m ≠ freshTag

/--
`alloc_fresh_block` is the allocator-abstraction axiom: a freshly allocated
block simulates in both machines before any value is written.  In a
bump-pointer model this holds because cells beyond `addrStart` are absent from
`mMap` (both sides give `none`); other allocator strategies must satisfy the
same contract.
-/
axiom alloc_fresh_block
  {π : PlaceMap}
  {ρa : AddrRenaming}
  {ρt : TagRenaming}
  {s_mir : mirlite.State}
  {s_osea : oseair.State}
  {freshAddr_m freshAddr_o : Word}
  {freshLayout : LayoutTy}
  (h_sim : StateSim π ρa ρt s_mir s_osea) :
  block_sim_at s_mir s_osea freshAddr_m freshAddr_o freshLayout

theorem mem_vals_eq_word (n : Word) :
  mem_vals_eq [mirlite.MemValue.Val n] [oseair.Val.Dat n] := by
  exact mem_vals_eq.cons rfl mem_vals_eq.nil

/-! ## Same-Key Insert Lookup Facts -/

/-!
These lookup lemmas are still used through `simp` when the fresh-allocation
proofs rebuild the newly inserted source and target bindings.
-/

@[simp] theorem env_lookup_insert_eq
  (e : Env) (base : Word) (info : Word × TyVal × Tag) :
  (Env.insert e base info).lookup base = some info := by
  simp [Env.insert, Env.lookup, List.lookup]

@[simp] theorem reg_lookup_insert_eq
  (r : RegMap) (reg : Register) (val : TyVal × List oseair.Val) :
  (RegMap.insert r reg val).lookup reg = some val := by
  cases reg with
  | R idx =>
    simp [RegMap.insert, RegMap.lookup, List.lookup, instBEqRegister, registerBEq]

@[simp] theorem place_map_lookup_cons_eq
  (π : PlaceMap) (base : Word) (reg : Register) (layout : LayoutTy) :
  ((base, (reg, layout)) :: π).lookup base = some (reg, layout) := by
  simp [List.lookup]

theorem place_map_lookup_cons_ne
  {π : PlaceMap}
  {base base' : Word}
  {reg : Register}
  {layout : LayoutTy}
  {entry : Register × LayoutTy}
  (h_ne : base' ≠ base)
  (h_lookup : ((base, (reg, layout)) :: π).lookup base' = some entry) :
  π.lookup base' = some entry := by
  have h_beq : (base' == base) = false := by
    simp [h_ne]
  simpa [List.lookup, h_beq] using h_lookup

theorem place_map_lookup_cons_self
  {π : PlaceMap}
  {base : Word}
  {reg reg' : Register}
  {layout layout' : LayoutTy}
  (h_lookup : ((base, (reg, layout)) :: π).lookup base = some (reg', layout')) :
  reg' = reg ∧ layout' = layout := by
  have h_some : some (reg, layout) = some (reg', layout') := by
    simpa [List.lookup] using h_lookup
  cases h_some
  exact ⟨rfl, rfl⟩

/--
`list_lookup_filter_ne` is the base assoc-list lemma needed by the
`*_lookup_insert_ne` facts below.
-/
theorem list_lookup_filter_ne
  {α β : Type}
  [BEq α] [LawfulBEq α]
  (key banned : α)
  (xs : List (α × β))
  (h_ne : key ≠ banned) :
  List.lookup key (xs.filter (fun x => x.fst != banned)) = List.lookup key xs := by
  induction xs with
  | nil =>
      simp [List.lookup]
  | cons x xs ih =>
      cases x with
      | mk k v =>
          by_cases h_key : key = k
          · subst k
            have h_keep : (key != banned) = true := by
              simp [h_ne]
            have h_self : (key == key) = true := by
              exact LawfulBEq.rfl
            simp [List.filter, List.lookup, h_keep, h_self]
          · by_cases h_banned : k = banned
            · subst k
              have h_key_false : (key == banned) = false := by
                cases h_eq : (key == banned) with
                | true =>
                    exact False.elim (h_key (LawfulBEq.eq_of_beq h_eq))
                | false =>
                    rfl
              simp [List.filter, List.lookup, h_key_false, ih]
            · have h_key_false : (key == k) = false := by
                cases h_eq : (key == k) with
                | true =>
                    exact False.elim (h_key (LawfulBEq.eq_of_beq h_eq))
                | false =>
                    rfl
              have h_keep : (k != banned) = true := by
                simp [h_banned]
              simp [List.filter, List.lookup, h_key_false, h_keep, ih]

@[simp] theorem env_lookup_insert_ne
  (e : Env) (base other : Word) (info : Word × TyVal × Tag)
  (h_ne : other ≠ base) :
  (Env.insert e base info).lookup other = e.lookup other := by
  unfold Env.insert Env.lookup
  cases h_eq : (other == base) with
  | true =>
      have : other = base := by simpa using h_eq
      contradiction
  | false =>
      simp [List.lookup, h_eq]
      exact list_lookup_filter_ne other base e h_ne

@[simp] theorem reg_lookup_insert_ne
  (r : RegMap) (reg other : Register) (val : TyVal × List oseair.Val)
  (h_ne : other ≠ reg) :
  (RegMap.insert r reg val).lookup other = r.lookup other := by
  cases reg with
  | R idx =>
      cases other with
      | R otherIdx =>
          unfold RegMap.insert RegMap.lookup
          cases h_eq : (otherIdx == idx) with
          | true =>
              have : Register.R otherIdx = Register.R idx := by
                simpa [registerBEq, instBEqRegister] using h_eq
              contradiction
          | false =>
              simp [List.lookup, registerBEq, instBEqRegister, h_eq]
              exact list_lookup_filter_ne (Register.R otherIdx) (Register.R idx) r h_ne

/-! ## Simulation Transport Across Writes -/

/--
`mem_vals_eq_readWordSeq` rebuilds block value agreement from the pointwise
block simulation predicate used in `block_sim_at`.
-/
theorem mem_vals_eq_readWordSeq
  {m_mir : mirlite.Mem}
  {m_osea : oseair.Mem}
  {addr_m addr_o : Word}
  {sz : Nat}
  (h_cells :
    ∀ i, i < sz →
      mem_val_eq_opt (m_mir.find? (addr_m + i)) (m_osea.find? (addr_o + i))) :
  mem_vals_eq
    (mirlite.readWordSeq m_mir addr_m sz)
    (oseair.readWordSeq m_osea addr_o sz) := by
  induction sz generalizing addr_m addr_o with
  | zero =>
      exact mem_vals_eq.nil
  | succ sz ih =>
      have h0 := h_cells 0 (Nat.succ_pos _)
      rw [Nat.add_zero, Nat.add_zero] at h0
      have htail :
          ∀ i, i < sz →
            mem_val_eq_opt (m_mir.find? (addr_m + 1 + i)) (m_osea.find? (addr_o + 1 + i)) := by
        intro i hi
        have h_tail_i := h_cells (i + 1) (Nat.succ_lt_succ hi)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h_tail_i
      cases h_m : m_mir.find? addr_m <;> cases h_o : m_osea.find? addr_o <;>
        simp [mirlite.readWordSeq, oseair.readWordSeq,
          h_m, h_o, mem_val_eq_opt, mem_val_eq] at h0 ⊢ <;>
        exact mem_vals_eq.cons h0 (ih htail)

theorem mem_vals_eq_length
  {vals_mir : List mirlite.MemValue}
  {vals_osea : List oseair.Val}
  (h_vals : mem_vals_eq vals_mir vals_osea) :
  vals_mir.length = vals_osea.length := by
  induction h_vals with
  | nil =>
      rfl
  | cons _ _ ih =>
      simp [ih]

/-- Derive `vals_osea.length = blockSize layout` from `vals_mir.length = blockSize layout`
    and `mem_vals_eq vals_mir vals_osea`. This is a common pattern in allocation proofs. -/
theorem mem_vals_eq_length_blockSize
  {vals_mir : List mirlite.MemValue}
  {vals_osea : List oseair.Val}
  {layout : LayoutTy}
  (h_vals : mem_vals_eq vals_mir vals_osea)
  (h_len : vals_mir.length = blockSize layout) :
  vals_osea.length = blockSize layout := by
  rw [← h_len, mem_vals_eq_length h_vals]

theorem mem_vals_eq_get
  {vals_mir : List mirlite.MemValue}
  {vals_osea : List oseair.Val}
  (h_vals : mem_vals_eq vals_mir vals_osea) :
  ∀ i
    (h_mir : i < vals_mir.length)
    (h_osea : i < vals_osea.length),
      mem_val_eq (vals_mir.get ⟨i, h_mir⟩) (vals_osea.get ⟨i, h_osea⟩) := by
  induction h_vals with
  | nil =>
      intro i h_mir
      cases h_mir
  | cons h_head _ ih =>
      intro i h_mir h_osea
      cases i with
      | zero =>
          simpa using h_head
      | succ i =>
          exact ih i (Nat.lt_of_succ_lt_succ h_mir) (Nat.lt_of_succ_lt_succ h_osea)

@[simp] theorem mirlite_mem_find_write_eq
  (m : mirlite.Mem) (addr : Word) (v : mirlite.MemValue) :
  (m.write addr v).find? addr = some v := by
  simp [mirlite.Mem.write, mirlite.Mem.find?, List.lookup]

@[simp] theorem mirlite_mem_find_write_ne
  (m : mirlite.Mem) (addr other : Word) (v : mirlite.MemValue)
  (h_ne : other ≠ addr) :
  (m.write addr v).find? other = m.find? other := by
  unfold mirlite.Mem.write mirlite.Mem.find?
  cases h_eq : (other == addr) with
  | true =>
      have : other = addr := by simpa using h_eq
      contradiction
  | false =>
      simp [List.lookup, h_eq]
      exact list_lookup_filter_ne other addr m.mMap h_ne

@[simp] theorem oseair_mem_find_write_eq
  (m : oseair.Mem) (addr : Word) (v : oseair.Val) :
  (m.write addr v).find? addr = some v := by
  simp [oseair.Mem.write, oseair.Mem.find?, List.lookup]

@[simp] theorem oseair_mem_find_write_ne
  (m : oseair.Mem) (addr other : Word) (v : oseair.Val)
  (h_ne : other ≠ addr) :
  (m.write addr v).find? other = m.find? other := by
  unfold oseair.Mem.write oseair.Mem.find?
  cases h_eq : (other == addr) with
  | true =>
      have : other = addr := by simpa using h_eq
      contradiction
  | false =>
      simp [List.lookup, h_eq]
      exact list_lookup_filter_ne other addr m.mMap h_ne

@[simp] theorem mirlite_readWordSeq_length
  (m : mirlite.Mem) (addr : Word) (sz : Nat) :
  (mirlite.readWordSeq m addr sz).length = sz := by
  induction sz generalizing addr with
  | zero =>
      rfl
  | succ sz ih =>
      cases h_find : m.find? addr <;> simp [mirlite.readWordSeq, h_find, ih]

@[simp] theorem oseair_readWordSeq_length
  (m : oseair.Mem) (addr : Word) (sz : Nat) :
  (oseair.readWordSeq m addr sz).length = sz := by
  induction sz generalizing addr with
  | zero =>
      rfl
  | succ sz ih =>
      cases h_find : m.find? addr <;> simp [oseair.readWordSeq, h_find, ih]

theorem mirlite_find_writeWordSeq_of_ne
  {m : mirlite.Mem}
  {vals : List mirlite.MemValue}
  {addr query : Word}
  (h_ne : ∀ j, j < vals.length → query ≠ addr + j) :
  (mirlite.writeWordSeq m addr vals).find? query = m.find? query := by
  induction vals generalizing m addr with
  | nil =>
      simp [mirlite.writeWordSeq]
  | cons v vs ih =>
      have h_head : query ≠ addr := h_ne 0 (by simp)
      rw [mirlite.writeWordSeq, ← mirlite_mem_find_write_ne (m := m) (addr := addr)
        (other := query) (v := v) h_head]
      apply ih
      intro j hj
      have h_shift := h_ne (j + 1) (by simpa using Nat.succ_lt_succ hj)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h_shift

theorem mirlite_find_writeWordSeq_at
  {m : mirlite.Mem}
  {addr : Word}
  {vals : List mirlite.MemValue}
  {i : Nat}
  (h_i : i < vals.length) :
  (mirlite.writeWordSeq m addr vals).find? (addr + i) = some (vals.get ⟨i, h_i⟩) := by
  induction vals generalizing m addr i with
  | nil =>
      cases h_i
  | cons v vs ih =>
      cases i with
      | zero =>
          rw [mirlite.writeWordSeq]
          have h_keep :
              (mirlite.writeWordSeq (m.write addr v) (addr + 1) vs).find? addr =
                (m.write addr v).find? addr := by
            apply mirlite_find_writeWordSeq_of_ne
            intro j hj
            intro h_eq
            have h_eq' : addr + 0 = addr + (j + 1) := by
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h_eq
            have : 0 = j + 1 := Nat.add_left_cancel h_eq'
            exact Nat.succ_ne_zero j this.symm
          simpa [Nat.add_zero] using
            h_keep.trans (mirlite_mem_find_write_eq (m := m) (addr := addr) (v := v))
      | succ i =>
          have h_tail : i < vs.length := Nat.lt_of_succ_lt_succ h_i
          have h_rec :
              (mirlite.writeWordSeq (m.write addr v) (addr + 1) vs).find? (addr + 1 + i) =
                some (vs.get ⟨i, h_tail⟩) := by
            exact ih (m := m.write addr v) (addr := addr + 1) (i := i) h_tail
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h_rec

theorem oseair_find_writeWordSeq_of_ne
  {m : oseair.Mem}
  {vals : List oseair.Val}
  {addr query : Word}
  (h_ne : ∀ j, j < vals.length → query ≠ addr + j) :
  (oseair.writeWordSeq m addr vals).find? query = m.find? query := by
  induction vals generalizing m addr with
  | nil =>
      simp [oseair.writeWordSeq]
  | cons v vs ih =>
      have h_head : query ≠ addr := h_ne 0 (by simp)
      rw [oseair.writeWordSeq, ← oseair_mem_find_write_ne (m := m) (addr := addr)
        (other := query) (v := v) h_head]
      apply ih
      intro j hj
      have h_shift := h_ne (j + 1) (by simpa using Nat.succ_lt_succ hj)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h_shift

theorem oseair_find_writeWordSeq_at
  {m : oseair.Mem}
  {addr : Word}
  {vals : List oseair.Val}
  {i : Nat}
  (h_i : i < vals.length) :
  (oseair.writeWordSeq m addr vals).find? (addr + i) = some (vals.get ⟨i, h_i⟩) := by
  induction vals generalizing m addr i with
  | nil =>
      cases h_i
  | cons v vs ih =>
      cases i with
      | zero =>
          rw [oseair.writeWordSeq]
          have h_keep :
              (oseair.writeWordSeq (m.write addr v) (addr + 1) vs).find? addr =
                (m.write addr v).find? addr := by
            apply oseair_find_writeWordSeq_of_ne
            intro j hj
            intro h_eq
            have h_eq' : addr + 0 = addr + (j + 1) := by
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h_eq
            have : 0 = j + 1 := Nat.add_left_cancel h_eq'
            exact Nat.succ_ne_zero j this.symm
          simpa [Nat.add_zero] using
            h_keep.trans (oseair_mem_find_write_eq (m := m) (addr := addr) (v := v))
      | succ i =>
          have h_tail : i < vs.length := Nat.lt_of_succ_lt_succ h_i
          have h_rec :
              (oseair.writeWordSeq (m.write addr v) (addr + 1) vs).find? (addr + 1 + i) =
                some (vs.get ⟨i, h_tail⟩) := by
            exact ih (m := m.write addr v) (addr := addr + 1) (i := i) h_tail
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h_rec

theorem block_sim_at_write_exact
  {s_mir : mirlite.State}
  {s_osea : oseair.State}
  {dst_mir dst_osea : Word}
  {layout : LayoutTy}
  {vals_mir : List mirlite.MemValue}
  {vals_osea : List oseair.Val}
  (h_vals : mem_vals_eq vals_mir vals_osea)
  (h_len : vals_mir.length = blockSize layout) :
  block_sim_at
    { s_mir with mem := mirlite.writeWordSeq s_mir.mem dst_mir vals_mir }
    { s_osea with mem := oseair.writeWordSeq s_osea.mem dst_osea vals_osea }
    dst_mir dst_osea layout := by
  intro i hi
  have h_i_mir : i < vals_mir.length := by
    simpa [h_len] using hi
  have h_len_o : vals_osea.length = blockSize layout :=
    mem_vals_eq_length_blockSize h_vals h_len
  have h_i_osea : i < vals_osea.length := by
    simpa [h_len_o] using hi
  rw [mirlite_find_writeWordSeq_at h_i_mir, oseair_find_writeWordSeq_at h_i_osea]
  simpa [mem_val_eq_opt] using mem_vals_eq_get h_vals i h_i_mir h_i_osea

theorem block_sim_at_write_other
  {s_mir : mirlite.State}
  {s_osea : oseair.State}
  {addr_m addr_o : Word}
  {layout : LayoutTy}
  {dst_mir dst_osea : Word}
  {vals_mir : List mirlite.MemValue}
  {vals_osea : List oseair.Val}
  (h_block : block_sim_at s_mir s_osea addr_m addr_o layout)
  (h_disj_m : blocks_disjoint addr_m (blockSize layout) dst_mir vals_mir.length)
  (h_disj_o : blocks_disjoint addr_o (blockSize layout) dst_osea vals_osea.length) :
  block_sim_at
    { s_mir with mem := mirlite.writeWordSeq s_mir.mem dst_mir vals_mir }
    { s_osea with mem := oseair.writeWordSeq s_osea.mem dst_osea vals_osea }
    addr_m addr_o layout := by
  intro i hi
  have h_keep_m :
      (mirlite.writeWordSeq s_mir.mem dst_mir vals_mir).find? (addr_m + i) =
        s_mir.mem.find? (addr_m + i) := by
    apply mirlite_find_writeWordSeq_of_ne
    intro j hj
    exact h_disj_m i hi j hj
  have h_keep_o :
      (oseair.writeWordSeq s_osea.mem dst_osea vals_osea).find? (addr_o + i) =
        s_osea.mem.find? (addr_o + i) := by
    apply oseair_find_writeWordSeq_of_ne
    intro j hj
    exact h_disj_o i hi j hj
  simpa [h_keep_m, h_keep_o] using h_block i hi

theorem blocks_disjoint_subrange_right
  {addr₁ addr₂ : Word}
  {sz₁ sz₂ : Nat}
  {off subSz : Nat}
  (h_disj : blocks_disjoint addr₁ sz₁ addr₂ sz₂)
  (h_fit : off + subSz ≤ sz₂) :
  blocks_disjoint addr₁ sz₁ (addr₂ + off) subSz := by
  intro i hi j hj h_eq
  have hj' : off + j < sz₂ := by
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj off) h_fit
  have h_eq' : addr₁ + i = addr₂ + (off + j) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h_eq
  exact h_disj i hi (off + j) hj' h_eq'

theorem block_sim_at_write_subrange
  {s_mir : mirlite.State}
  {s_osea : oseair.State}
  {base_m base_o : Word}
  {baseLayout subLayout : LayoutTy}
  {off : Word}
  {vals_mir : List mirlite.MemValue}
  {vals_osea : List oseair.Val}
  (h_block : block_sim_at s_mir s_osea base_m base_o baseLayout)
  (h_vals : mem_vals_eq vals_mir vals_osea)
  (h_len : vals_mir.length = blockSize subLayout)
  (h_fit : off + blockSize subLayout ≤ blockSize baseLayout) :
  block_sim_at
    { s_mir with mem := mirlite.writeWordSeq s_mir.mem (base_m + off) vals_mir }
    { s_osea with mem := oseair.writeWordSeq s_osea.mem (base_o + off) vals_osea }
    base_m base_o baseLayout := by
  have h_len_o : vals_osea.length = blockSize subLayout :=
    mem_vals_eq_length_blockSize h_vals h_len
  intro i hi
  by_cases h_before : i < off
  · have h_keep_m :
        (mirlite.writeWordSeq s_mir.mem (base_m + off) vals_mir).find? (base_m + i) =
          s_mir.mem.find? (base_m + i) := by
      apply mirlite_find_writeWordSeq_of_ne
      intro j hj h_eq
      have h_eq' : base_m + i = base_m + (off + j) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h_eq
      have : i = off + j := Nat.add_left_cancel h_eq'
      exact (Nat.not_le_of_lt h_before) (by rw [this]; exact Nat.le_add_right off j)
    have h_keep_o :
        (oseair.writeWordSeq s_osea.mem (base_o + off) vals_osea).find? (base_o + i) =
          s_osea.mem.find? (base_o + i) := by
      apply oseair_find_writeWordSeq_of_ne
      intro j hj h_eq
      have h_eq' : base_o + i = base_o + (off + j) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h_eq
      have : i = off + j := Nat.add_left_cancel h_eq'
      exact (Nat.not_le_of_lt h_before) (by rw [this]; exact Nat.le_add_right off j)
    simpa [h_keep_m, h_keep_o] using h_block i hi
  · have h_off_le : off ≤ i := Nat.le_of_not_gt h_before
    by_cases h_inside : i < off + vals_mir.length
    · have h_sub_m : i - off < vals_mir.length := by
        have : off + (i - off) < off + vals_mir.length := by
          simpa [Nat.add_sub_of_le h_off_le] using h_inside
        exact Nat.lt_of_add_lt_add_left this
      have h_sub_o : i - off < vals_osea.length := by
        simpa [h_len_o, h_len] using h_sub_m
      have h_query_m : base_m + i = (base_m + off) + (i - off) := by
        calc
          base_m + i = base_m + (off + (i - off)) := by rw [Nat.add_sub_of_le h_off_le]
          _ = (base_m + off) + (i - off) := by simp [Nat.add_assoc]
      have h_query_o : base_o + i = (base_o + off) + (i - off) := by
        calc
          base_o + i = base_o + (off + (i - off)) := by rw [Nat.add_sub_of_le h_off_le]
          _ = (base_o + off) + (i - off) := by simp [Nat.add_assoc]
      rw [h_query_m, h_query_o, mirlite_find_writeWordSeq_at h_sub_m, oseair_find_writeWordSeq_at h_sub_o]
      simpa [mem_val_eq_opt] using mem_vals_eq_get h_vals (i - off) h_sub_m h_sub_o
    · have h_keep_m :
          (mirlite.writeWordSeq s_mir.mem (base_m + off) vals_mir).find? (base_m + i) =
            s_mir.mem.find? (base_m + i) := by
        apply mirlite_find_writeWordSeq_of_ne
        intro j hj h_eq
        have h_eq' : base_m + i = base_m + (off + j) := by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h_eq
        have : i = off + j := Nat.add_left_cancel h_eq'
        exact h_inside (by rw [this]; exact Nat.add_lt_add_left hj off)
      have h_keep_o :
          (oseair.writeWordSeq s_osea.mem (base_o + off) vals_osea).find? (base_o + i) =
            s_osea.mem.find? (base_o + i) := by
        apply oseair_find_writeWordSeq_of_ne
        intro j hj h_eq
        have h_eq' : base_o + i = base_o + (off + j) := by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h_eq
        have : i = off + j := Nat.add_left_cancel h_eq'
        have hj_mir : j < vals_mir.length := by
          simpa [h_len_o, h_len] using hj
        exact h_inside (by rw [this]; exact Nat.add_lt_add_left hj_mir off)
      simpa [h_keep_m, h_keep_o] using h_block i hi

theorem place_runtime_sim_write_post_iff
  {π : PlaceMap}
  {ρa : AddrRenaming}
  {ρt : TagRenaming}
  {s_mir : mirlite.State}
  {s_osea : oseair.State}
  {base : Word}
  {reg : Register}
  {addr_m addr_o tag_m tag_o : Word}
  {layout : LayoutTy}
  {dst_mir dst_osea : Word}
  {ap_m' ap_o' : AccessPerms}
  {pc_mir pc_osea : Nat}
  {vals_mir : List mirlite.MemValue}
  {vals_osea : List oseair.Val} :
  place_runtime_sim π ρa ρt s_mir s_osea base reg addr_m addr_o tag_m tag_o layout ↔
  place_runtime_sim π ρa ρt
    { s_mir with
      ap := ap_m',
      mem := mirlite.writeWordSeq s_mir.mem dst_mir vals_mir,
      pc := pc_mir }
    { s_osea with
      ap := ap_o',
      mem := oseair.writeWordSeq s_osea.mem dst_osea vals_osea,
      pc := pc_osea }
    base reg addr_m addr_o tag_m tag_o layout := by
  constructor <;> intro h
  all_goals (refine ⟨h.1, ?_, ?_, place_runtime_sim.addr h, place_runtime_sim.tag h⟩
             · simpa using place_runtime_sim.env h
             · simpa using place_runtime_sim.reg h)

theorem place_runtime_sim_write_post
  {π : PlaceMap}
  {ρa : AddrRenaming}
  {ρt : TagRenaming}
  {s_mir : mirlite.State}
  {s_osea : oseair.State}
  {base : Word}
  {reg : Register}
  {addr_m addr_o tag_m tag_o : Word}
  {layout : LayoutTy}
  {dst_mir dst_osea : Word}
  {ap_m' ap_o' : AccessPerms}
  {pc_mir pc_osea : Nat}
  {vals_mir : List mirlite.MemValue}
  {vals_osea : List oseair.Val}
  (h :
    place_runtime_sim π ρa ρt s_mir s_osea base reg addr_m addr_o tag_m tag_o layout) :
  place_runtime_sim π ρa ρt
    { s_mir with
      ap := ap_m',
      mem := mirlite.writeWordSeq s_mir.mem dst_mir vals_mir,
      pc := pc_mir }
    { s_osea with
      ap := ap_o',
      mem := oseair.writeWordSeq s_osea.mem dst_osea vals_osea,
      pc := pc_osea }
    base reg addr_m addr_o tag_m tag_o layout :=
  place_runtime_sim_write_post_iff.mp h

theorem place_runtime_sim_of_write_post
  {π : PlaceMap}
  {ρa : AddrRenaming}
  {ρt : TagRenaming}
  {s_mir : mirlite.State}
  {s_osea : oseair.State}
  {base : Word}
  {reg : Register}
  {addr_m addr_o tag_m tag_o : Word}
  {layout : LayoutTy}
  {dst_mir dst_osea : Word}
  {ap_m' ap_o' : AccessPerms}
  {pc_mir pc_osea : Nat}
  {vals_mir : List mirlite.MemValue}
  {vals_osea : List oseair.Val}
  (h :
    place_runtime_sim π ρa ρt
      { s_mir with
        ap := ap_m',
        mem := mirlite.writeWordSeq s_mir.mem dst_mir vals_mir,
        pc := pc_mir }
      { s_osea with
        ap := ap_o',
        mem := oseair.writeWordSeq s_osea.mem dst_osea vals_osea,
        pc := pc_osea }
      base reg addr_m addr_o tag_m tag_o layout) :
  place_runtime_sim π ρa ρt s_mir s_osea base reg addr_m addr_o tag_m tag_o layout :=
  place_runtime_sim_write_post_iff.mpr h

theorem place_runtime_sim_reg_insert_other_iff
  {π : PlaceMap}
  {ρa : AddrRenaming}
  {ρt : TagRenaming}
  {s_mir : mirlite.State}
  {s_osea : oseair.State}
  {base : Word}
  {reg tmpReg : Register}
  {addr_m addr_o tag_m tag_o : Word}
  {layout : LayoutTy}
  {tmpVal : TyVal × List oseair.Val}
  (h_ne : reg ≠ tmpReg) :
  place_runtime_sim π ρa ρt s_mir s_osea base reg addr_m addr_o tag_m tag_o layout ↔
  place_runtime_sim π ρa ρt
    s_mir
    { s_osea with reg := s_osea.reg.insert tmpReg tmpVal }
    base reg addr_m addr_o tag_m tag_o layout := by
  constructor <;> intro h
  all_goals (refine ⟨h.1, place_runtime_sim.env h, ?_, place_runtime_sim.addr h, place_runtime_sim.tag h⟩
             · simpa [h_ne] using place_runtime_sim.reg h)

theorem place_runtime_sim_reg_insert_other
  {π : PlaceMap}
  {ρa : AddrRenaming}
  {ρt : TagRenaming}
  {s_mir : mirlite.State}
  {s_osea : oseair.State}
  {base : Word}
  {reg tmpReg : Register}
  {addr_m addr_o tag_m tag_o : Word}
  {layout : LayoutTy}
  {tmpVal : TyVal × List oseair.Val}
  (h :
    place_runtime_sim π ρa ρt s_mir s_osea base reg addr_m addr_o tag_m tag_o layout)
  (h_ne : reg ≠ tmpReg) :
  place_runtime_sim π ρa ρt
    s_mir
    { s_osea with reg := s_osea.reg.insert tmpReg tmpVal }
    base reg addr_m addr_o tag_m tag_o layout :=
  (place_runtime_sim_reg_insert_other_iff h_ne).mp h

theorem place_runtime_sim_of_reg_insert_other
  {π : PlaceMap}
  {ρa : AddrRenaming}
  {ρt : TagRenaming}
  {s_mir : mirlite.State}
  {s_osea : oseair.State}
  {base : Word}
  {reg tmpReg : Register}
  {addr_m addr_o tag_m tag_o : Word}
  {layout : LayoutTy}
  {tmpVal : TyVal × List oseair.Val}
  (h :
    place_runtime_sim π ρa ρt
      s_mir
      { s_osea with reg := s_osea.reg.insert tmpReg tmpVal }
      base reg addr_m addr_o tag_m tag_o layout)
  (h_ne : reg ≠ tmpReg) :
  place_runtime_sim π ρa ρt s_mir s_osea base reg addr_m addr_o tag_m tag_o layout :=
  (place_runtime_sim_reg_insert_other_iff h_ne).mpr h

theorem blocks_disjoint_symm
  {addr₁ addr₂ : Word}
  {sz₁ sz₂ : Nat}
  (h : blocks_disjoint addr₁ sz₁ addr₂ sz₂) :
  blocks_disjoint addr₂ sz₂ addr₁ sz₁ := by
  intro i hi j hj h_eq
  exact h j hj i hi h_eq.symm

theorem state_sim_reg_insert_other
  {π : PlaceMap}
  {ρa : AddrRenaming}
  {ρt : TagRenaming}
  {s_mir : mirlite.State}
  {s_osea : oseair.State}
  {tmpReg : Register}
  {tmpVal : TyVal × List oseair.Val}
  (h_sim : StateSim π ρa ρt s_mir s_osea)
  (h_fresh : ∀ base layout, π.lookup base = some (tmpReg, layout) → False) :
  StateSim π ρa ρt
    s_mir
    { s_osea with reg := s_osea.reg.insert tmpReg tmpVal } := by
  refine ⟨?_, ?_, ?_⟩
  · simpa using StateSim.sb h_sim
  · intro base reg layout h_lookup
    let ⟨addr_m, addr_o, tag_m, tag_o, h_ptr, h_block⟩ := StateSim.place h_sim h_lookup
    have h_ne : reg ≠ tmpReg := by
      intro h_eq
      subst h_eq
      exact h_fresh base layout h_lookup
    refine ⟨addr_m, addr_o, tag_m, tag_o, place_runtime_sim_reg_insert_other h_ptr h_ne, h_block⟩
  · intro base₁ reg₁ layout₁ base₂ reg₂ layout₂ h_lookup₁ h_lookup₂ h_ne
      addr₁_m addr₁_o tag₁_m tag₁_o addr₂_m addr₂_o tag₂_m tag₂_o h_ptr₁ h_ptr₂
    have h_reg₁_ne : reg₁ ≠ tmpReg := by
      intro h_eq
      subst h_eq
      exact h_fresh base₁ layout₁ h_lookup₁
    have h_reg₂_ne : reg₂ ≠ tmpReg := by
      intro h_eq
      subst h_eq
      exact h_fresh base₂ layout₂ h_lookup₂
    exact StateSim.disjoint
      h_sim h_lookup₁ h_lookup₂ h_ne
      (place_runtime_sim_of_reg_insert_other h_ptr₁ h_reg₁_ne)
      (place_runtime_sim_of_reg_insert_other h_ptr₂ h_reg₂_ne)

theorem place_runtime_sim_alloc_write_old
  {π : PlaceMap}
  {ρa : AddrRenaming}
  {ρt : TagRenaming}
  {s_mir : mirlite.State}
  {s_osea : oseair.State}
  {base : Word}
  {reg : Register}
  {layout : LayoutTy}
  {freshAddr_m freshAddr_o : Word}
  {tag_m tag_o : Word}
  {base' : Word}
  {reg' : Register}
  {layout' : LayoutTy}
  {addr_m addr_o tag_m' tag_o' : Word}
  {s_mir' : mirlite.State}
  {s_osea' : oseair.State}
  (h_env :
    s_mir'.env = s_mir.env.insert base (freshAddr_m, layoutToTyVal layout, tag_m))
  (h_reg :
    s_osea'.reg = s_osea.reg.insert reg
      (TyVal.PTy, [oseair.Val.Ptr freshAddr_o 0 (blockSize layout) tag_o]))
  (h_pre :
    place_runtime_sim π ρa ρt s_mir s_osea
      base' reg' addr_m addr_o tag_m' tag_o' layout')
  (h_base_ne : base' ≠ base)
  (h_reg_ne : reg' ≠ reg)
  (h_addr_ne : addr_m ≠ freshAddr_m)
  (h_tag_ne : tag_m' ≠ tag_m) :
  place_runtime_sim
    ((base, (reg, layout)) :: π)
    (extendAddrRenameMap ρa freshAddr_m freshAddr_o)
    (extendTagRenameMap ρt tag_m tag_o)
    s_mir'
    s_osea'
    base' reg' addr_m addr_o tag_m' tag_o' layout' := by
  have h_base_beq : (base' == base) = false := by
    simp [h_base_ne]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [List.lookup, h_base_beq] using h_pre.1
  · simpa [h_env, h_base_ne] using place_runtime_sim.env h_pre
  · simpa [h_reg, h_reg_ne] using place_runtime_sim.reg h_pre
  · simpa [extendAddrRenameMap, h_addr_ne] using place_runtime_sim.addr h_pre
  · simpa [extendTagRenameMap, h_tag_ne] using place_runtime_sim.tag h_pre

theorem place_runtime_sim_alloc_write_eq_old
  {π : PlaceMap}
  {ρa_pre ρa_post : AddrRenaming}
  {ρt_pre ρt_post : TagRenaming}
  {s_mir : mirlite.State}
  {s_osea : oseair.State}
  {base : Word}
  {reg : Register}
  {layout : LayoutTy}
  {freshAddr_m freshAddr_o : Word}
  {tag_m tag_o : Word}
  {base' : Word}
  {reg' : Register}
  {layout' : LayoutTy}
  {addr_pre_m addr_pre_o tag_pre_m tag_pre_o : Word}
  {addr_m addr_o tag_m' tag_o' : Word}
  {s_mir' : mirlite.State}
  {s_osea' : oseair.State}
  (h_env :
    s_mir'.env = s_mir.env.insert base (freshAddr_m, layoutToTyVal layout, tag_m))
  (h_reg :
    s_osea'.reg = s_osea.reg.insert reg
      (TyVal.PTy, [oseair.Val.Ptr freshAddr_o 0 (blockSize layout) tag_o]))
  (h_pre :
    place_runtime_sim π ρa_pre ρt_pre s_mir s_osea
      base' reg' addr_pre_m addr_pre_o tag_pre_m tag_pre_o layout')
  (h_post :
    place_runtime_sim
      ((base, (reg, layout)) :: π)
      ρa_post ρt_post
      s_mir'
      s_osea'
      base' reg' addr_m addr_o tag_m' tag_o' layout')
  (h_base_ne : base' ≠ base)
  (h_reg_ne : reg' ≠ reg) :
  addr_m = addr_pre_m ∧ addr_o = addr_pre_o ∧ tag_m' = tag_pre_m ∧ tag_o' = tag_pre_o := by
  have h_env_pre := place_runtime_sim.env h_pre
  have h_env_post_insert :
      (s_mir.env.insert base (freshAddr_m, layoutToTyVal layout, tag_m)).lookup base' =
        some (addr_m, layoutToTyVal layout', tag_m') := by
    simpa [h_env] using place_runtime_sim.env h_post
  have h_env_post :
      s_mir.env.lookup base' =
        some (addr_m, layoutToTyVal layout', tag_m') := by
    simpa [h_base_ne] using h_env_post_insert
  have h_env_eq :
      addr_pre_m = addr_m ∧ tag_pre_m = tag_m' := by
    simpa using h_env_pre.symm.trans h_env_post
  have h_reg_pre := place_runtime_sim.reg h_pre
  have h_reg_post_insert :
      (s_osea.reg.insert reg
        (TyVal.PTy, [oseair.Val.Ptr freshAddr_o 0 (blockSize layout) tag_o])).lookup reg' =
        some (TyVal.PTy, [oseair.Val.Ptr addr_o 0 (blockSize layout') tag_o']) := by
    simpa [h_reg] using place_runtime_sim.reg h_post
  have h_reg_post :
      s_osea.reg.lookup reg' =
        some (TyVal.PTy, [oseair.Val.Ptr addr_o 0 (blockSize layout') tag_o']) := by
    simpa [h_reg_ne] using h_reg_post_insert
  have h_reg_eq :
      addr_pre_o = addr_o ∧ tag_pre_o = tag_o' := by
    simpa using h_reg_pre.symm.trans h_reg_post
  exact ⟨h_env_eq.1.symm, h_reg_eq.1.symm, h_env_eq.2.symm, h_reg_eq.2.symm⟩

theorem place_runtime_sim_alloc_write_new_eq
  {π : PlaceMap}
  {ρa' : AddrRenaming}
  {ρt' : TagRenaming}
  {s_mir : mirlite.State}
  {s_osea : oseair.State}
  {base : Word}
  {reg : Register}
  {layout : LayoutTy}
  {freshAddr_m freshAddr_o : Word}
  {tag_m tag_o : Word}
  {addr_m addr_o tag_m' tag_o' : Word}
  {s_mir' : mirlite.State}
  {s_osea' : oseair.State}
  (h_env :
    s_mir'.env = s_mir.env.insert base (freshAddr_m, layoutToTyVal layout, tag_m))
  (h_reg :
    s_osea'.reg = s_osea.reg.insert reg
      (TyVal.PTy, [oseair.Val.Ptr freshAddr_o 0 (blockSize layout) tag_o]))
  (h_post :
    place_runtime_sim
      ((base, (reg, layout)) :: π)
      ρa' ρt'
      s_mir'
      s_osea'
      base reg addr_m addr_o tag_m' tag_o' layout) :
  addr_m = freshAddr_m ∧ addr_o = freshAddr_o ∧ tag_m' = tag_m ∧ tag_o' = tag_o := by
  have h_env : freshAddr_m = addr_m ∧ tag_m = tag_m' := by
    simpa [h_env] using place_runtime_sim.env h_post
  have h_reg : freshAddr_o = addr_o ∧ tag_o = tag_o' := by
    simpa [h_reg] using place_runtime_sim.reg h_post
  exact ⟨h_env.1.symm, h_reg.1.symm, h_env.2.symm, h_reg.2.symm⟩

theorem state_sim_write_subrange
  {π : PlaceMap}
  {ρa : AddrRenaming}
  {ρt : TagRenaming}
  {s_mir : mirlite.State}
  {s_osea : oseair.State}
  {dst_base : Word}
  {dst_reg : Register}
  {baseLayout subLayout : LayoutTy}
  {dst_mir dst_osea : Word}
  {dst_tag_m dst_tag_o : Word}
  {off : Word}
  {ap_m' ap_o' : AccessPerms}
  {pc_mir pc_osea : Nat}
  {vals_mir : List mirlite.MemValue}
  {vals_osea : List oseair.Val}
  (h_sim : StateSim π ρa ρt s_mir s_osea)
  (h_dst :
    place_runtime_sim π ρa ρt s_mir s_osea
      dst_base dst_reg dst_mir dst_osea dst_tag_m dst_tag_o baseLayout)
  (h_sb : sb_sim ρa ρt ap_m' ap_o')
  (h_vals : mem_vals_eq vals_mir vals_osea)
  (h_len : vals_mir.length = blockSize subLayout)
  (h_fit : off + blockSize subLayout ≤ blockSize baseLayout) :
  StateSim π ρa ρt
    { s_mir with
      ap := ap_m',
      mem := mirlite.writeWordSeq s_mir.mem (dst_mir + off) vals_mir,
      pc := pc_mir }
    { s_osea with
      ap := ap_o',
      mem := oseair.writeWordSeq s_osea.mem (dst_osea + off) vals_osea,
      pc := pc_osea } := by
  refine ⟨h_sb, ?_, ?_⟩
  · intro base reg layout h_lookup
    by_cases h_base : base = dst_base
    · subst h_base
      have h_lookup_dst : π.lookup base = some (dst_reg, baseLayout) := h_dst.1
      have h_pair : (reg, layout) = (dst_reg, baseLayout) := by
        have h_some : some (reg, layout) = some (dst_reg, baseLayout) := by
          exact h_lookup.symm.trans h_lookup_dst
        injection h_some with h_pair
      cases h_pair
      let ⟨addr_m', addr_o', tag_m', tag_o', h_ptr_dst, h_block_dst⟩ := StateSim.place h_sim h_lookup_dst
      have h_eq_dst := place_runtime_sim.eq h_ptr_dst h_dst
      rcases h_eq_dst with ⟨h_addr_m, h_addr_o, h_tag_m, h_tag_o⟩
      subst h_addr_m h_addr_o h_tag_m h_tag_o
      refine ⟨addr_m', addr_o', tag_m', tag_o', ?_, ?_⟩
      · exact place_runtime_sim_write_post h_ptr_dst
      · simpa using
          block_sim_at_write_subrange
            (s_mir := s_mir)
            (s_osea := s_osea)
            (base_m := addr_m')
            (base_o := addr_o')
            (baseLayout := baseLayout)
            (subLayout := subLayout)
            (off := off)
            (vals_mir := vals_mir)
            (vals_osea := vals_osea)
            h_block_dst
            h_vals h_len h_fit
    · let ⟨addr_m, addr_o, tag_m, tag_o, h_ptr, h_block⟩ := StateSim.place h_sim h_lookup
      have h_sep :=
        StateSim.disjoint h_sim h_lookup h_dst.1 h_base h_ptr h_dst
      have h_len_o : vals_osea.length = blockSize subLayout :=
        mem_vals_eq_length_blockSize h_vals h_len
      have h_sep_m :
          blocks_disjoint addr_m (blockSize layout) (dst_mir + off) vals_mir.length := by
        exact blocks_disjoint_subrange_right h_sep.1 (by simpa [h_len] using h_fit)
      have h_sep_o :
          blocks_disjoint addr_o (blockSize layout) (dst_osea + off) vals_osea.length := by
        exact blocks_disjoint_subrange_right h_sep.2 (by simpa [h_len_o] using h_fit)
      refine ⟨addr_m, addr_o, tag_m, tag_o, place_runtime_sim_write_post h_ptr, ?_⟩
      simpa using
        block_sim_at_write_other
          (s_mir := s_mir)
          (s_osea := s_osea)
          (addr_m := addr_m)
          (addr_o := addr_o)
          (layout := layout)
          (dst_mir := dst_mir + off)
          (dst_osea := dst_osea + off)
          (vals_mir := vals_mir)
          (vals_osea := vals_osea)
          h_block h_sep_m h_sep_o
  · intro base₁ reg₁ layout₁ base₂ reg₂ layout₂ h_lookup₁ h_lookup₂ h_ne
      addr₁_m addr₁_o tag₁_m tag₁_o addr₂_m addr₂_o tag₂_m tag₂_o h_ptr₁ h_ptr₂
    exact StateSim.disjoint
      h_sim h_lookup₁ h_lookup₂ h_ne
      (place_runtime_sim_of_write_post h_ptr₁)
      (place_runtime_sim_of_write_post h_ptr₂)

/--
`state_sim_write` is the exact-write specialization of
`state_sim_write_subrange`.
-/
theorem state_sim_write
  {π : PlaceMap}
  {ρa : AddrRenaming}
  {ρt : TagRenaming}
  {s_mir : mirlite.State}
  {s_osea : oseair.State}
  {dst_base : Word}
  {dst_reg : Register}
  {dst_layout : LayoutTy}
  {dst_mir dst_osea : Word}
  {dst_tag_m dst_tag_o : Word}
  {ap_m' ap_o' : AccessPerms}
  {pc_mir pc_osea : Nat}
  {vals_mir : List mirlite.MemValue}
  {vals_osea : List oseair.Val}
  (h_sim : StateSim π ρa ρt s_mir s_osea)
  (h_dst :
    place_runtime_sim π ρa ρt s_mir s_osea
      dst_base dst_reg dst_mir dst_osea dst_tag_m dst_tag_o dst_layout)
  (h_sb : sb_sim ρa ρt ap_m' ap_o')
  (h_vals : mem_vals_eq vals_mir vals_osea)
  (h_len : vals_mir.length = blockSize dst_layout) :
  StateSim π ρa ρt
    { s_mir with
      ap := ap_m',
      mem := mirlite.writeWordSeq s_mir.mem dst_mir vals_mir,
      pc := pc_mir }
    { s_osea with
      ap := ap_o',
      mem := oseair.writeWordSeq s_osea.mem dst_osea vals_osea,
      pc := pc_osea } := by
  simpa [Nat.zero_add] using
    state_sim_write_subrange
      (π := π)
      (ρa := ρa)
      (ρt := ρt)
      (dst_base := dst_base)
      (dst_reg := dst_reg)
      (baseLayout := dst_layout)
      (subLayout := dst_layout)
      (dst_mir := dst_mir)
      (dst_osea := dst_osea)
      (dst_tag_m := dst_tag_m)
      (dst_tag_o := dst_tag_o)
      (off := 0)
      (ap_m' := ap_m')
      (ap_o' := ap_o')
      (pc_mir := pc_mir)
      (pc_osea := pc_osea)
      (vals_mir := vals_mir)
      (vals_osea := vals_osea)
      h_sim h_dst h_sb h_vals h_len
      (by simp)

/-! ## Allocator Abstraction -/

/--
`writeWordSeq` only updates `mMap`; the `addrStart` field is carried through
unchanged.  This lets us separate the simulation proof (which never inspects
`addrStart`) from the allocator bookkeeping.
-/
theorem mirlite_writeWordSeq_addrStart
    (m : mirlite.Mem) (a : Word) (addr : Word) (vals : List mirlite.MemValue) :
    mirlite.writeWordSeq { m with addrStart := a } addr vals =
      { mirlite.writeWordSeq m addr vals with addrStart := a } := by
  induction vals generalizing m addr with
  | nil => rfl
  | cons v vs ih =>
    simp only [mirlite.writeWordSeq]
    rw [show mirlite.Mem.write { m with addrStart := a } addr v =
             { mirlite.Mem.write m addr v with addrStart := a } from rfl, ih]

theorem oseair_writeWordSeq_addrStart
    (m : oseair.Mem) (a : Word) (addr : Word) (vals : List oseair.Val) :
    oseair.writeWordSeq { m with addrStart := a } addr vals =
      { oseair.writeWordSeq m addr vals with addrStart := a } := by
  induction vals generalizing m addr with
  | nil => rfl
  | cons v vs ih =>
    simp only [oseair.writeWordSeq]
    rw [show oseair.Mem.write { m with addrStart := a } addr v =
             { oseair.Mem.write m addr v with addrStart := a } from rfl, ih]

/--
`StateSim` depends on states only through `env`, `mem.mMap`, and `ap` (source)
and `reg`, `mem.mMap`, and `ap` (target).  In particular, `mem.addrStart` is
irrelevant, which is the key that lets allocator-specific bookkeeping be
kept out of simulation theorems.
-/
theorem StateSim.of_mem_mMap_eq
    {π : PlaceMap} {ρa : AddrRenaming} {ρt : TagRenaming}
    {s₁ s₂ : mirlite.State} {o₁ o₂ : oseair.State}
    (h : StateSim π ρa ρt s₁ o₁)
    (h_env   : s₁.env       = s₂.env)
    (h_map_m : s₁.mem.mMap  = s₂.mem.mMap)
    (h_ap_m  : s₁.ap        = s₂.ap)
    (h_reg   : o₁.reg       = o₂.reg)
    (h_map_o : o₁.mem.mMap  = o₂.mem.mMap)
    (h_ap_o  : o₁.ap        = o₂.ap) :
    StateSim π ρa ρt s₂ o₂ := by
  refine ⟨h_ap_m ▸ h_ap_o ▸ StateSim.sb h, ?_, ?_⟩
  · intro base reg layout h_lookup
    obtain ⟨addr_m, addr_o, tag_m, tag_o, h_ptr, h_block⟩ := StateSim.place h h_lookup
    exact ⟨addr_m, addr_o, tag_m, tag_o,
      ⟨h_ptr.1, h_env ▸ h_ptr.2.1, h_reg ▸ h_ptr.2.2.1, h_ptr.2.2.2⟩,
      fun i hi => by
        simpa [mirlite.Mem.find?, oseair.Mem.find?, ← h_map_m, ← h_map_o]
          using h_block i hi⟩
  · intro base₁ reg₁ layout₁ base₂ reg₂ layout₂ h_l1 h_l2 h_ne
        addr₁_m addr₁_o tag₁_m tag₁_o addr₂_m addr₂_o tag₂_m tag₂_o h_ptr₁ h_ptr₂
    exact StateSim.disjoint h h_l1 h_l2 h_ne
      ⟨h_ptr₁.1, h_env.symm ▸ h_ptr₁.2.1, h_reg.symm ▸ h_ptr₁.2.2.1, h_ptr₁.2.2.2⟩
      ⟨h_ptr₂.1, h_env.symm ▸ h_ptr₂.2.1, h_reg.symm ▸ h_ptr₂.2.2.1, h_ptr₂.2.2.2⟩

/-! ## Helper Lemmas for Allocation Proofs -/

/--
`reg_ne_of_place_not_in_π` proves that a register from an existing place lookup
cannot equal the fresh register being allocated, using the freshness hypothesis.
-/
theorem reg_ne_of_place_not_in_π
  {π : PlaceMap}
  {reg : Register}
  {base' : Word}
  {reg' : Register}
  {layout' : LayoutTy}
  (h_lookup : π.lookup base' = some (reg', layout'))
  (h_fresh : ∀ base layout, π.lookup base = some (reg, layout) → False) :
  reg' ≠ reg := by
  intro h_eq
  subst h_eq
  exact h_fresh base' layout' h_lookup

/--
`place_lookup_old` combines three common steps in allocation proofs:
1. `place_map_lookup_cons_ne` to get the old lookup from the cons-list
2. `StateSim.place` to get the place runtime simulation
3. `reg_ne_of_place_not_in_π` to prove register inequality

Given a simulation on `π` and a lookup in `(base, reg, layout) :: π` where
`base' ≠ base`, this returns the old lookup, place runtime simulation, and
register inequality proof.
-/
theorem place_lookup_old
  {π : PlaceMap}
  {ρa : AddrRenaming}
  {ρt : TagRenaming}
  {s_mir : mirlite.State}
  {s_osea : oseair.State}
  {base : Word}
  {reg : Register}
  {layout : LayoutTy}
  {base' : Word}
  {reg' : Register}
  {layout' : LayoutTy}
  (h_sim : StateSim π ρa ρt s_mir s_osea)
  (h_base_ne : base' ≠ base)
  (h_lookup : ((base, (reg, layout)) :: π).lookup base' = some (reg', layout'))
  (h_reg_fresh : ∀ base layout, π.lookup base = some (reg, layout) → False) :
  ∃ addr_m addr_o tag_m tag_o,
    π.lookup base' = some (reg', layout') ∧
    place_runtime_sim π ρa ρt s_mir s_osea base' reg' addr_m addr_o tag_m tag_o layout' ∧
    block_sim_at s_mir s_osea addr_m addr_o layout' ∧
    reg' ≠ reg := by
  have h_lookup_old : π.lookup base' = some (reg', layout') :=
    place_map_lookup_cons_ne h_base_ne h_lookup
  obtain ⟨addr_m, addr_o, tag_m, tag_o, h_ptr, h_block⟩ := StateSim.place h_sim h_lookup_old
  have h_reg_ne : reg' ≠ reg := reg_ne_of_place_not_in_π h_lookup_old h_reg_fresh
  exact ⟨addr_m, addr_o, tag_m, tag_o, h_lookup_old, h_ptr, h_block, h_reg_ne⟩

/--
`place_lookup_old_ptr` is a variant of `place_lookup_old` that returns only
the place_runtime_sim (without block_sim_at), for use in disjointness proofs.
-/
theorem place_lookup_old_ptr
  {π : PlaceMap}
  {ρa : AddrRenaming}
  {ρt : TagRenaming}
  {s_mir : mirlite.State}
  {s_osea : oseair.State}
  {base : Word}
  {reg : Register}
  {layout : LayoutTy}
  {base' : Word}
  {reg' : Register}
  {layout' : LayoutTy}
  (h_sim : StateSim π ρa ρt s_mir s_osea)
  (h_base_ne : base' ≠ base)
  (h_lookup : ((base, (reg, layout)) :: π).lookup base' = some (reg', layout'))
  (h_reg_fresh : ∀ base layout, π.lookup base = some (reg, layout) → False) :
  ∃ addr_m addr_o tag_m tag_o,
    π.lookup base' = some (reg', layout') ∧
    place_runtime_sim π ρa ρt s_mir s_osea base' reg' addr_m addr_o tag_m tag_o layout' ∧
    reg' ≠ reg := by
  obtain ⟨addr_m, addr_o, tag_m, tag_o, h_lookup_old, h_ptr, _, h_reg_ne⟩ :=
    place_lookup_old h_sim h_base_ne h_lookup h_reg_fresh
  exact ⟨addr_m, addr_o, tag_m, tag_o, h_lookup_old, h_ptr, h_reg_ne⟩

/--
`state_sim_alloc` is the allocator-agnostic extension of `StateSim` by one
fresh place.  The caller supplies `h_block_new` — proof that `freshAddr`
already simulates in the post-state — rather than having the theorem hardcode
how that block was established (e.g. via a write or some other initialisation).

The bump-allocator instantiation is `state_sim_alloc_write`, which derives
`h_block_new` from `block_sim_at_write_exact` and bridges the `addrStart`
bookkeeping via `mirlite/oseair_writeWordSeq_addrStart`.
-/
theorem state_sim_alloc
  {π : PlaceMap}
  {ρa ρa' : AddrRenaming}
  {ρt ρt' : TagRenaming}
  {s_mir : mirlite.State}
  {s_osea : oseair.State}
  {base : Word}
  {reg : Register}
  {layout : LayoutTy}
  {freshAddr_m freshAddr_o : Word}
  {tag_m tag_o : Word}
  {ap_m' ap_o' : AccessPerms}
  {pc_mir pc_osea : Nat}
  {vals_mir : List mirlite.MemValue}
  {vals_osea : List oseair.Val}
  (h_sim : StateSim π ρa ρt s_mir s_osea)
  (h_ρa' : ρa' = extendAddrRenameMap ρa freshAddr_m freshAddr_o)
  (h_ρt' : ρt' = extendTagRenameMap ρt tag_m tag_o)
  (h_reg_fresh : ∀ base' layout', π.lookup base' = some (reg, layout') → False)
  (h_sb : sb_sim ρa' ρt' ap_m' ap_o')
  (h_vals : mem_vals_eq vals_mir vals_osea)
  (h_len : vals_mir.length = blockSize layout)
  (h_block_new :
    block_sim_at
      { s_mir with
        env := s_mir.env.insert base (freshAddr_m, layoutToTyVal layout, tag_m),
        mem := mirlite.writeWordSeq s_mir.mem freshAddr_m vals_mir,
        ap := ap_m',
        pc := pc_mir }
      { s_osea with
        reg := s_osea.reg.insert reg
          (TyVal.PTy, [oseair.Val.Ptr freshAddr_o 0 (blockSize layout) tag_o]),
        mem := oseair.writeWordSeq s_osea.mem freshAddr_o vals_osea,
        ap := ap_o',
        pc := pc_osea }
      freshAddr_m freshAddr_o layout) :
  StateSim ((base, (reg, layout)) :: π) ρa' ρt'
    { s_mir with
      env := s_mir.env.insert base (freshAddr_m, layoutToTyVal layout, tag_m),
      mem := mirlite.writeWordSeq s_mir.mem freshAddr_m vals_mir,
      ap := ap_m',
      pc := pc_mir }
    { s_osea with
      reg := s_osea.reg.insert reg
        (TyVal.PTy, [oseair.Val.Ptr freshAddr_o 0 (blockSize layout) tag_o]),
      mem := oseair.writeWordSeq s_osea.mem freshAddr_o vals_osea,
      ap := ap_o',
      pc := pc_osea } := by
  subst h_ρa' h_ρt'
  refine ⟨h_sb, ?_, ?_⟩
  · intro base' reg' layout' h_lookup
    by_cases h_base : base' = base
    · subst base'
      have h_head := place_map_lookup_cons_self h_lookup
      have h_reg' : reg' = reg := h_head.1
      have h_layout' : layout' = layout := h_head.2
      subst reg'
      subst layout'
      refine ⟨freshAddr_m, freshAddr_o, tag_m, tag_o, ?_, h_block_new⟩
      refine ⟨by simp [List.lookup], ?_, ?_, ?_, ?_⟩
      · simpa using env_lookup_insert_eq s_mir.env base (freshAddr_m, layoutToTyVal layout, tag_m)
      · simpa using
          reg_lookup_insert_eq s_osea.reg reg
            (TyVal.PTy, [oseair.Val.Ptr freshAddr_o 0 (blockSize layout) tag_o])
      · simp [extendAddrRenameMap]
      · simp [extendTagRenameMap]
    · obtain ⟨addr_m, addr_o, tag_m', tag_o', h_lookup_old, h_ptr, h_block, h_reg_ne⟩ :=
        place_lookup_old h_sim h_base h_lookup h_reg_fresh
      have h_fresh :=
        alloc_fresh_disjoint
          (freshAddr_m := freshAddr_m)
          (freshAddr_o := freshAddr_o)
          (freshLayout := layout)
          h_sim h_lookup_old h_ptr
      have h_tag_ne :=
        alloc_fresh_tag
          (freshTag := tag_m)
          h_sim h_lookup_old h_ptr
      have h_len_o : vals_osea.length = blockSize layout :=
        mem_vals_eq_length_blockSize h_vals h_len
      have h_sep_m : blocks_disjoint addr_m (blockSize layout') freshAddr_m vals_mir.length := by
        simpa [h_len] using h_fresh.2.1
      have h_sep_o : blocks_disjoint addr_o (blockSize layout') freshAddr_o vals_osea.length := by
        simpa [h_len_o] using h_fresh.2.2
      refine ⟨addr_m, addr_o, tag_m', tag_o', ?_, ?_⟩
      · exact place_runtime_sim_alloc_write_old
          rfl rfl
          (base := base) (reg := reg) (layout := layout)
          (freshAddr_m := freshAddr_m) (freshAddr_o := freshAddr_o)
          (tag_m := tag_m) (tag_o := tag_o)
          h_ptr h_base h_reg_ne h_fresh.1 h_tag_ne
      · simpa [block_sim_at, mirlite.Mem.find?, oseair.Mem.find?] using
          block_sim_at_write_other
            (s_mir := s_mir) (s_osea := s_osea)
            (addr_m := addr_m) (addr_o := addr_o) (layout := layout')
            (dst_mir := freshAddr_m) (dst_osea := freshAddr_o)
            h_block h_sep_m h_sep_o
  · intro base₁ reg₁ layout₁ base₂ reg₂ layout₂ h_lookup₁ h_lookup₂ h_ne
        addr₁_m addr₁_o tag₁_m tag₁_o addr₂_m addr₂_o tag₂_m tag₂_o h_ptr₁ h_ptr₂
    by_cases h_base₁ : base₁ = base
    · by_cases h_base₂ : base₂ = base
      · subst h_base₁; subst h_base₂; contradiction
      · subst base₁
        have h_head₁ := place_map_lookup_cons_self h_lookup₁
        have h_reg₁ : reg₁ = reg := h_head₁.1
        have h_layout₁ : layout₁ = layout := h_head₁.2
        subst reg₁; subst layout₁
        have h_new₁ := place_runtime_sim_alloc_write_new_eq
          (ρa' := extendAddrRenameMap ρa freshAddr_m freshAddr_o)
          (ρt' := extendTagRenameMap ρt tag_m tag_o)
          rfl rfl
          (base := base) (reg := reg) (layout := layout)
          (freshAddr_m := freshAddr_m) (freshAddr_o := freshAddr_o)
          (tag_m := tag_m) (tag_o := tag_o) h_ptr₁
        obtain ⟨_, _, _, _, h_lookup₂_old, h_pre₂, h_reg₂_ne⟩ :=
          place_lookup_old_ptr h_sim h_base₂ h_lookup₂ h_reg_fresh
        have h_eq₂ := place_runtime_sim_alloc_write_eq_old
          rfl rfl
          (base := base) (reg := reg) (layout := layout)
          (freshAddr_m := freshAddr_m) (freshAddr_o := freshAddr_o)
          (tag_m := tag_m) (tag_o := tag_o)
          h_pre₂ h_ptr₂ h_base₂ h_reg₂_ne
        have h_fresh₂ :=
          alloc_fresh_disjoint
            (freshAddr_m := freshAddr_m) (freshAddr_o := freshAddr_o) (freshLayout := layout)
            h_sim h_lookup₂_old h_pre₂
        rcases h_new₁ with ⟨rfl, rfl, _, _⟩
        rcases h_eq₂ with ⟨rfl, rfl, _, _⟩
        exact ⟨blocks_disjoint_symm h_fresh₂.2.1, blocks_disjoint_symm h_fresh₂.2.2⟩
    · by_cases h_base₂ : base₂ = base
      · subst base₂
        have h_head₂ := place_map_lookup_cons_self h_lookup₂
        have h_reg₂ : reg₂ = reg := h_head₂.1
        have h_layout₂ : layout₂ = layout := h_head₂.2
        subst reg₂; subst layout₂
        obtain ⟨_, _, _, _, h_lookup₁_old, h_pre₁, h_reg₁_ne⟩ :=
          place_lookup_old_ptr h_sim h_base₁ h_lookup₁ h_reg_fresh
        have h_eq₁ := place_runtime_sim_alloc_write_eq_old
          rfl rfl
          (base := base) (reg := reg) (layout := layout)
          (freshAddr_m := freshAddr_m) (freshAddr_o := freshAddr_o)
          (tag_m := tag_m) (tag_o := tag_o)
          h_pre₁ h_ptr₁ h_base₁ h_reg₁_ne
        have h_new₂ := place_runtime_sim_alloc_write_new_eq
          (ρa' := extendAddrRenameMap ρa freshAddr_m freshAddr_o)
          (ρt' := extendTagRenameMap ρt tag_m tag_o)
          rfl rfl
          (base := base) (reg := reg) (layout := layout)
          (freshAddr_m := freshAddr_m) (freshAddr_o := freshAddr_o)
          (tag_m := tag_m) (tag_o := tag_o) h_ptr₂
        have h_fresh₁ :=
          alloc_fresh_disjoint
            (freshAddr_m := freshAddr_m) (freshAddr_o := freshAddr_o) (freshLayout := layout)
            h_sim h_lookup₁_old h_pre₁
        rcases h_eq₁ with ⟨rfl, rfl, _, _⟩
        rcases h_new₂ with ⟨rfl, rfl, _, _⟩
        exact ⟨h_fresh₁.2.1, h_fresh₁.2.2⟩
      · obtain ⟨_, _, _, _, h_lookup₁_old, h_pre₁, h_reg₁_ne⟩ :=
          place_lookup_old_ptr h_sim h_base₁ h_lookup₁ h_reg_fresh
        obtain ⟨_, _, _, _, h_lookup₂_old, h_pre₂, h_reg₂_ne⟩ :=
          place_lookup_old_ptr h_sim h_base₂ h_lookup₂ h_reg_fresh
        have h_eq₁ := place_runtime_sim_alloc_write_eq_old
          rfl rfl
          (base := base) (reg := reg) (layout := layout)
          (freshAddr_m := freshAddr_m) (freshAddr_o := freshAddr_o)
          (tag_m := tag_m) (tag_o := tag_o)
          h_pre₁ h_ptr₁ h_base₁ h_reg₁_ne
        have h_eq₂ := place_runtime_sim_alloc_write_eq_old
          rfl rfl
          (base := base) (reg := reg) (layout := layout)
          (freshAddr_m := freshAddr_m) (freshAddr_o := freshAddr_o)
          (tag_m := tag_m) (tag_o := tag_o)
          h_pre₂ h_ptr₂ h_base₂ h_reg₂_ne
        rcases h_eq₁ with ⟨rfl, rfl, _, _⟩
        rcases h_eq₂ with ⟨rfl, rfl, _, _⟩
        exact StateSim.disjoint h_sim h_lookup₁_old h_lookup₂_old h_ne h_pre₁ h_pre₂

theorem state_sim_alloc_write
  {π : PlaceMap}
  {ρa ρa' : AddrRenaming}
  {ρt ρt' : TagRenaming}
  {s_mir : mirlite.State}
  {s_osea : oseair.State}
  {base : Word}
  {reg : Register}
  {layout : LayoutTy}
  {freshAddr_m freshAddr_o : Word}
  {tag_m tag_o : Word}
  {ap_m' ap_o' : AccessPerms}
  {pc_mir pc_osea : Nat}
  {vals_mir : List mirlite.MemValue}
  {vals_osea : List oseair.Val}
  (h_sim : StateSim π ρa ρt s_mir s_osea)
  (h_ρa' : ρa' = extendAddrRenameMap ρa freshAddr_m freshAddr_o)
  (h_ρt' : ρt' = extendTagRenameMap ρt tag_m tag_o)
  (h_reg_fresh : ∀ base' layout', π.lookup base' = some (reg, layout') → False)
  (h_sb : sb_sim ρa' ρt' ap_m' ap_o')
  (h_vals : mem_vals_eq vals_mir vals_osea)
  (h_len : vals_mir.length = blockSize layout) :
  StateSim ((base, (reg, layout)) :: π) ρa' ρt'
    { s_mir with
      env := s_mir.env.insert base (freshAddr_m, layoutToTyVal layout, tag_m),
      mem := mirlite.writeWordSeq
        { s_mir.mem with addrStart := freshAddr_m + blockSize layout }
        freshAddr_m vals_mir,
      ap := ap_m',
      pc := pc_mir }
    { s_osea with
      reg := s_osea.reg.insert reg
        (TyVal.PTy, [oseair.Val.Ptr freshAddr_o 0 (blockSize layout) tag_o]),
      mem :=
        oseair.writeWordSeq
          { s_osea.mem with addrStart := freshAddr_o + blockSize layout }
          freshAddr_o vals_osea,
      ap := ap_o',
      pc := pc_osea } := by
  apply StateSim.of_mem_mMap_eq
    (state_sim_alloc h_sim h_ρa' h_ρt' h_reg_fresh h_sb h_vals h_len
      (block_sim_at_write_exact
        (s_mir := { s_mir with
          env := s_mir.env.insert base (freshAddr_m, layoutToTyVal layout, tag_m),
          mem := s_mir.mem,
          ap := ap_m',
          pc := pc_mir })
        (s_osea := { s_osea with
          reg := s_osea.reg.insert reg
            (TyVal.PTy, [oseair.Val.Ptr freshAddr_o 0 (blockSize layout) tag_o]),
          mem := s_osea.mem,
          ap := ap_o',
          pc := pc_osea })
        h_vals h_len))
  · rfl
  · simp [mirlite_writeWordSeq_addrStart]
  · rfl
  · rfl
  · simp [oseair_writeWordSeq_addrStart]
  · rfl

theorem osea_run_ptr_cstore_embedded_ok
  (s_osea : oseair.State)
  (prog : oseair.Prog)
  (layout : LayoutTy)
  (vals : List oseair.Val)
  (base off size tag : Word)
  (reg : Register)
  (ap' : AccessPerms)
  (h_start : StartsAt prog s_osea.pc [oseair.Instr.CStore (layoutToTyVal layout) vals reg])
  (h_reg :
    s_osea.reg.lookup reg =
      some (TyVal.PTy, [oseair.Val.Ptr base off size tag]))
  (h_off : off < size)
  (h_use : sb_use_mb s_osea.ap (base + off) tag = SBResult.Ok ap') :
  oseair.runN 1 s_osea prog =
    oseair.Result.Ok
      { s_osea with
        ap := ap',
        mem := oseair.writeWordSeq s_osea.mem (base + off) vals,
        pc := s_osea.pc + 1 } := by
  have h_stmt :
      prog.get? s_osea.pc =
        some (oseair.Instr.CStore (layoutToTyVal layout) vals reg) := StartsAt.singleton h_start
  rcases List.get?_eq_some_iff.mp h_stmt with ⟨h_pc, h_get⟩
  have h_step :
      oseair.step s_osea prog =
        oseair.Result.Ok
          { s_osea with
            ap := ap',
            mem := oseair.writeWordSeq s_osea.mem (base + off) vals,
            pc := s_osea.pc + 1 } := by
    unfold oseair.step oseair.writeThroughPtr
    rw [dif_pos h_pc, h_get]
    have h_bound : ¬ base + off >= base + size := by
      exact Nat.not_le_of_lt (Nat.add_lt_add_left h_off base)
    simp [h_reg, h_use, h_bound]
  simp [oseair.runN, h_step]

theorem osea_run_ptr_memcpy_embedded_ok
  (s_osea : oseair.State)
  (prog_osea : oseair.Prog)
  (layout : LayoutTy)
  (srcBase srcOff srcSize srcTag dstBase dstOff dstSize dstTag : Word)
  (srcReg dstReg : Register)
  (apRead apWrite : AccessPerms)
  (h_start :
    StartsAt prog_osea s_osea.pc
      [oseair.Instr.Memcpy dstReg srcReg (layoutToTyVal layout)])
  (h_src_reg :
    s_osea.reg.lookup srcReg =
      some (TyVal.PTy, [oseair.Val.Ptr srcBase srcOff srcSize srcTag]))
  (h_dst_reg :
    s_osea.reg.lookup dstReg =
      some (TyVal.PTy, [oseair.Val.Ptr dstBase dstOff dstSize dstTag]))
  (h_src_fit : srcOff + blockSize layout ≤ srcSize)
  (h_dst_fit : dstOff + blockSize layout ≤ dstSize)
  (h_read : sb_read s_osea.ap (srcBase + srcOff) srcTag = SBResult.Ok apRead)
  (h_write : sb_use_mb apRead (dstBase + dstOff) dstTag = SBResult.Ok apWrite) :
  oseair.runN 1 s_osea prog_osea =
    oseair.Result.Ok
      { s_osea with
        ap := apWrite,
        mem := oseair.writeWordSeq s_osea.mem (dstBase + dstOff)
          (oseair.readWordSeq s_osea.mem (srcBase + srcOff) (blockSize layout)),
        pc := s_osea.pc + 1 } := by
  have h_stmt :
      prog_osea.get? s_osea.pc =
        some (oseair.Instr.Memcpy dstReg srcReg (layoutToTyVal layout)) := by
    simpa using StartsAt.singleton h_start
  rcases List.get?_eq_some_iff.mp h_stmt with ⟨h_pc, h_get⟩
  have h_step :
      oseair.step s_osea prog_osea =
        oseair.Result.Ok
          { s_osea with
            ap := apWrite,
            mem := oseair.writeWordSeq s_osea.mem (dstBase + dstOff)
              (oseair.readWordSeq s_osea.mem (srcBase + srcOff) (blockSize layout)),
            pc := s_osea.pc + 1 } := by
    unfold oseair.step
    rw [dif_pos h_pc, h_get]
    have h_dst_bound : dstBase + dstOff + blockSize layout ≤ dstBase + dstSize := by
      simpa [Nat.add_assoc] using Nat.add_le_add_left h_dst_fit dstBase
    have h_src_bound : srcBase + srcOff + blockSize layout ≤ srcBase + srcSize := by
      simpa [Nat.add_assoc] using Nat.add_le_add_left h_src_fit srcBase
    have h_dst_bound' : dstBase + dstOff + layoutSize layout ≤ dstBase + dstSize := by
      simpa [blockSize_eq_layoutSize] using h_dst_bound
    have h_src_bound' : srcBase + srcOff + layoutSize layout ≤ srcBase + srcSize := by
      simpa [blockSize_eq_layoutSize] using h_src_bound
    simp [h_src_reg, h_dst_reg, h_read, h_write, blockSize, blockSize_eq_layoutSize,
      h_dst_bound, h_src_bound, h_dst_bound', h_src_bound']
  simp [oseair.runN, h_step]

theorem osea_run_memcpy_embedded_ok
  (s_osea : oseair.State)
  (prog_osea : oseair.Prog)
  (layout : LayoutTy)
  (srcAddr srcTag dstAddr dstTag : Word)
  (srcReg dstReg : Register)
  (apRead apWrite : AccessPerms)
  (h_start :
    StartsAt prog_osea s_osea.pc
      [oseair.Instr.Memcpy dstReg srcReg (layoutToTyVal layout)])
  (h_src_reg :
    s_osea.reg.lookup srcReg =
      some (TyVal.PTy, [oseair.Val.Ptr srcAddr 0 (blockSize layout) srcTag]))
  (h_dst_reg :
    s_osea.reg.lookup dstReg =
      some (TyVal.PTy, [oseair.Val.Ptr dstAddr 0 (blockSize layout) dstTag]))
  (h_read : sb_read s_osea.ap srcAddr srcTag = SBResult.Ok apRead)
  (h_write : sb_use_mb apRead dstAddr dstTag = SBResult.Ok apWrite) :
  oseair.runN 1 s_osea prog_osea =
    oseair.Result.Ok
      { s_osea with
        ap := apWrite,
        mem := oseair.writeWordSeq s_osea.mem dstAddr
          (oseair.readWordSeq s_osea.mem srcAddr (blockSize layout)),
        pc := s_osea.pc + 1 } := by
  simpa [Nat.zero_add] using
    osea_run_ptr_memcpy_embedded_ok
      s_osea prog_osea layout
      srcAddr 0 (blockSize layout) srcTag
      dstAddr 0 (blockSize layout) dstTag
      srcReg dstReg apRead apWrite
      h_start h_src_reg h_dst_reg
      (by simp)
      (by simp)
      (by simpa [Nat.zero_add] using h_read)
      (by simpa [Nat.zero_add] using h_write)

theorem osea_run_projected_cstore_embedded_ok
  (s_osea : oseair.State)
  (prog_osea : oseair.Prog)
  (baseLayout subLayout : LayoutTy)
  (vals : List oseair.Val)
  (addr tag : Word)
  (baseReg tmpReg : Register)
  (off tempTag : Word)
  (apRef apWrite apFinal : AccessPerms)
  (h_start :
    StartsAt prog_osea s_osea.pc
      [oseair.Instr.Assgn tmpReg (oseair.Rhs.MutBorOffset baseReg off),
       oseair.Instr.CStore (layoutToTyVal subLayout) vals tmpReg,
       oseair.Instr.Die tmpReg])
  (h_base_reg :
    s_osea.reg.lookup baseReg =
      some (TyVal.PTy, [oseair.Val.Ptr addr 0 (blockSize baseLayout) tag]))
  (h_off : off < blockSize baseLayout)
  (h_ref : sb_ref s_osea.ap (addr + off) tag RefOpKind.Mut = (SBResult.Ok apRef, tempTag))
  (h_use : sb_use_mb apRef (addr + off) tempTag = SBResult.Ok apWrite)
  (h_die : sb_die apWrite (addr + off) tempTag = SBResult.Ok apFinal) :
  oseair.runN 3 s_osea prog_osea =
    oseair.Result.Ok
      { s_osea with
        reg := s_osea.reg.insert tmpReg
          (TyVal.PTy, [oseair.Val.Ptr addr off (blockSize baseLayout) tempTag]),
        ap := apFinal,
        mem := oseair.writeWordSeq s_osea.mem (addr + off) vals,
        pc := s_osea.pc + 3 } := by
  have h_stmt0 :
      prog_osea.get? s_osea.pc =
        some (oseair.Instr.Assgn tmpReg (oseair.Rhs.MutBorOffset baseReg off)) := by
    simpa [Nat.zero_add] using (h_start 0).symm
  rcases List.get?_eq_some_iff.mp h_stmt0 with ⟨h_pc0, h_get0⟩
  let s1 : oseair.State :=
    { s_osea with
      reg := s_osea.reg.insert tmpReg
        (TyVal.PTy, [oseair.Val.Ptr addr off (blockSize baseLayout) tempTag]),
      ap := apRef,
      pc := s_osea.pc + 1 }
  have h_step0 :
      oseair.step s_osea prog_osea = oseair.Result.Ok s1 := by
    unfold oseair.step oseair.evalRhs
    rw [dif_pos h_pc0, h_get0]
    have h_off_bound : ¬ layoutSize baseLayout ≤ off := by
      simpa [blockSize_eq_layoutSize] using Nat.not_le_of_lt h_off
    simp [h_base_reg, h_off_bound, h_ref, s1, blockSize_eq_layoutSize]
  have h_start1 :
      StartsAt prog_osea (s_osea.pc + 1)
        [oseair.Instr.CStore (layoutToTyVal subLayout) vals tmpReg,
         oseair.Instr.Die tmpReg] :=
    StartsAt.tail h_start
  have h_stmt1 :
      prog_osea.get? (s_osea.pc + 1) =
        some (oseair.Instr.CStore (layoutToTyVal subLayout) vals tmpReg) := by
    simpa [Nat.zero_add] using (h_start1 0).symm
  rcases List.get?_eq_some_iff.mp h_stmt1 with ⟨h_pc1, h_get1⟩
  let s2 : oseair.State :=
    { s_osea with
      reg := s_osea.reg.insert tmpReg
        (TyVal.PTy, [oseair.Val.Ptr addr off (blockSize baseLayout) tempTag]),
      ap := apWrite,
      mem := oseair.writeWordSeq s_osea.mem (addr + off) vals,
      pc := s_osea.pc + 2 }
  have h_tmp_reg :
      s1.reg.lookup tmpReg =
        some (TyVal.PTy, [oseair.Val.Ptr addr off (blockSize baseLayout) tempTag]) := by
    simp [s1]
  have h_step1 :
      oseair.step s1 prog_osea = oseair.Result.Ok s2 := by
    unfold oseair.step oseair.writeThroughPtr
    rw [dif_pos h_pc1, h_get1]
    have h_off_size : off < layoutSize baseLayout := by
      simpa [blockSize_eq_layoutSize] using h_off
    have h_bound : ¬ addr + off >= addr + blockSize baseLayout := by
      exact Nat.not_le_of_lt (Nat.add_lt_add_left h_off addr)
    simp [s1, s2, h_tmp_reg, h_bound, h_use, h_off_size, blockSize_eq_layoutSize]
  have h_start2 :
      StartsAt prog_osea (s_osea.pc + 2) [oseair.Instr.Die tmpReg] := by
    exact StartsAt.tail h_start1
  have h_stmt2 :
      prog_osea.get? (s_osea.pc + 2) = some (oseair.Instr.Die tmpReg) := by
    simpa [Nat.zero_add] using (h_start2 0).symm
  rcases List.get?_eq_some_iff.mp h_stmt2 with ⟨h_pc2, h_get2⟩
  have h_step2 :
      oseair.step s2 prog_osea =
        oseair.Result.Ok
          { s_osea with
            reg := s_osea.reg.insert tmpReg
              (TyVal.PTy, [oseair.Val.Ptr addr off (blockSize baseLayout) tempTag]),
            ap := apFinal,
            mem := oseair.writeWordSeq s_osea.mem (addr + off) vals,
            pc := s_osea.pc + 3 } := by
    unfold oseair.step
    rw [dif_pos h_pc2, h_get2]
    simp [s2, h_tmp_reg, h_die]
  simp [oseair.runN, h_step0, h_step1, h_step2]

/--
Shared target-side simulation shell for existing-place writes that lower to
either a direct `CStore` or a projected borrow / `CStore` / `Die` sequence.

Statement-specific proofs still provide the MIR-step inversion result, the
payload values, and the fragment-specific `StartsAt` facts; this theorem
packages the common target execution and `StateSim` reconstruction.
-/
theorem existing_write_simulation
  {π : PlaceMap}
  {ρa : AddrRenaming}
  {ρt : TagRenaming}
  {s_mir : mirlite.State}
  {s_osea : oseair.State}
  {s_mir_next : mirlite.State}
  {prog_osea : oseair.Prog}
  {dst_base : Word}
  {dst_reg tmpReg : Register}
  {baseLayout subLayout : LayoutTy}
  {dst_mir dst_osea : Word}
  {dst_tag_m dst_tag_o off : Word}
  {vals_mir : List mirlite.MemValue}
  {vals_osea : List oseair.Val}
  {ap_m' : AccessPerms}
  (h_sim : StateSim π ρa ρt s_mir s_osea)
  (h_dst :
    place_runtime_sim π ρa ρt s_mir s_osea
      dst_base dst_reg dst_mir dst_osea dst_tag_m dst_tag_o baseLayout)
  (h_fit : off + blockSize subLayout ≤ blockSize baseLayout)
  (h_sub_nonempty : 0 < blockSize subLayout)
  (h_tmp_fresh : ∀ base layout, π.lookup base = some (tmpReg, layout) → False)
  (h_start_direct :
    off = 0 →
      StartsAt prog_osea s_osea.pc
        [oseair.Instr.CStore (layoutToTyVal subLayout) vals_osea dst_reg])
  (h_start_projected :
    off ≠ 0 →
      StartsAt prog_osea s_osea.pc
        [oseair.Instr.Assgn tmpReg (oseair.Rhs.MutBorOffset dst_reg off),
         oseair.Instr.CStore (layoutToTyVal subLayout) vals_osea tmpReg,
         oseair.Instr.Die tmpReg])
  (h_use : sb_use_mb s_mir.ap (dst_mir + off) dst_tag_m = SBResult.Ok ap_m')
  (h_next_full :
    s_mir_next =
      { s_mir with
        ap := ap_m',
        mem := mirlite.writeWordSeq s_mir.mem (dst_mir + off) vals_mir,
        pc := s_mir.pc + 1 })
  (h_vals : mem_vals_eq vals_mir vals_osea)
  (h_len : vals_mir.length = blockSize subLayout) :
  ∃ s_osea_next,
    StepStar s_osea prog_osea s_osea_next ∧
    StateSim π ρa ρt s_mir_next s_osea_next := by
  have h_reg :
      s_osea.reg.lookup dst_reg =
        some (TyVal.PTy, [oseair.Val.Ptr dst_osea 0 (blockSize baseLayout) dst_tag_o]) :=
    place_runtime_sim.reg h_dst
  have h_addr_base : ρa dst_mir = some dst_osea := place_runtime_sim.addr h_dst
  have h_addr : ρa (dst_mir + off) = some (dst_osea + off) :=
    addr_rename_offset h_addr_base
  have h_tag : ρt dst_tag_m = some dst_tag_o := place_runtime_sim.tag h_dst
  let ⟨ap_parent_o, h_target_parent_use, h_sb_parent⟩ :=
    sb_use_mb_sim_ok (StateSim.sb h_sim) h_addr h_tag h_use

  by_cases h_off : off = 0
  · have h_base_nonempty : 0 < blockSize baseLayout := by
      have h_sub_le : blockSize subLayout ≤ blockSize baseLayout := by
        simpa [h_off] using h_fit
      exact Nat.lt_of_lt_of_le h_sub_nonempty h_sub_le
    let s_osea_post :=
      { s_osea with
        ap := ap_parent_o,
        mem := oseair.writeWordSeq s_osea.mem dst_osea vals_osea,
        pc := s_osea.pc + 1 }
    have h_target_use0 :
        sb_use_mb s_osea.ap (dst_osea + 0) dst_tag_o = SBResult.Ok ap_parent_o := by
      simpa [h_off] using h_target_parent_use
    have h_target_run :
        oseair.runN 1 s_osea prog_osea = oseair.Result.Ok s_osea_post := by
      simpa [s_osea_post, h_off] using
        osea_run_ptr_cstore_embedded_ok
          s_osea prog_osea subLayout vals_osea
          dst_osea 0 (blockSize baseLayout) dst_tag_o dst_reg ap_parent_o
          (h_start_direct h_off) h_reg h_base_nonempty h_target_use0
    refine ⟨s_osea_post, StepStar.of_runN_ok h_target_run, ?_⟩
    rw [h_next_full]
    simpa [s_osea_post, h_off] using
      state_sim_write_subrange
        (π := π)
        (ρa := ρa)
        (ρt := ρt)
        (dst_base := dst_base)
        (dst_reg := dst_reg)
        (baseLayout := baseLayout)
        (subLayout := subLayout)
        (dst_mir := dst_mir)
        (dst_osea := dst_osea)
        (dst_tag_m := dst_tag_m)
        (dst_tag_o := dst_tag_o)
        (off := off)
        (ap_m' := ap_m')
        (ap_o' := ap_parent_o)
        (pc_mir := s_mir.pc + 1)
        (pc_osea := s_osea.pc + 1)
        (vals_mir := vals_mir)
        (vals_osea := vals_osea)
        h_sim h_dst h_sb_parent h_vals h_len h_fit
  · have h_off_lt : off < blockSize baseLayout := by
      exact Nat.lt_of_lt_of_le
        (Nat.lt_add_of_pos_right h_sub_nonempty)
        h_fit
    have h_reg_ne : dst_reg ≠ tmpReg := by
      intro h_eq
      subst h_eq
      exact h_tmp_fresh dst_base baseLayout h_dst.1
    let ⟨tempTag, ap_ref_o, ap_use_o, ap_final_o, h_ref, h_use_tmp, h_die, h_stack_eq⟩ :=
      sb_ref_mut_use_die_ok_of_use_ok h_target_parent_use
    have h_sb_final : sb_sim ρa ρt ap_m' ap_final_o :=
      sb_sim_of_right_stackMap_eq h_sb_parent h_stack_eq
    let s_osea_post :=
      { s_osea with
        reg := s_osea.reg.insert tmpReg
          (TyVal.PTy, [oseair.Val.Ptr dst_osea off (blockSize baseLayout) tempTag]),
        ap := ap_final_o,
        mem := oseair.writeWordSeq s_osea.mem (dst_osea + off) vals_osea,
        pc := s_osea.pc + 3 }
    have h_target_run :
        oseair.runN 3 s_osea prog_osea = oseair.Result.Ok s_osea_post := by
      simpa [s_osea_post] using
        osea_run_projected_cstore_embedded_ok
          s_osea prog_osea baseLayout subLayout vals_osea
          dst_osea dst_tag_o dst_reg tmpReg off tempTag
          ap_ref_o ap_use_o ap_final_o
          (h_start_projected h_off) h_reg h_off_lt h_ref h_use_tmp h_die
    have h_sim_reg :
        StateSim π ρa ρt
          s_mir
          { s_osea with
            reg := s_osea.reg.insert tmpReg
              (TyVal.PTy, [oseair.Val.Ptr dst_osea off (blockSize baseLayout) tempTag]) } := by
      exact state_sim_reg_insert_other h_sim h_tmp_fresh
    have h_dst_reg :
        place_runtime_sim π ρa ρt
          s_mir
          { s_osea with
            reg := s_osea.reg.insert tmpReg
              (TyVal.PTy, [oseair.Val.Ptr dst_osea off (blockSize baseLayout) tempTag]) }
          dst_base dst_reg dst_mir dst_osea dst_tag_m dst_tag_o baseLayout :=
      place_runtime_sim_reg_insert_other h_dst h_reg_ne
    refine ⟨s_osea_post, StepStar.of_runN_ok h_target_run, ?_⟩
    rw [h_next_full]
    simpa [s_osea_post] using
      state_sim_write_subrange
        (π := π)
        (ρa := ρa)
        (ρt := ρt)
        (dst_base := dst_base)
        (dst_reg := dst_reg)
        (baseLayout := baseLayout)
        (subLayout := subLayout)
        (dst_mir := dst_mir)
        (dst_osea := dst_osea)
        (dst_tag_m := dst_tag_m)
        (dst_tag_o := dst_tag_o)
        (off := off)
        (ap_m' := ap_m')
        (ap_o' := ap_final_o)
        (pc_mir := s_mir.pc + 1)
        (pc_osea := s_osea.pc + 3)
        (vals_mir := vals_mir)
        (vals_osea := vals_osea)
        h_sim_reg h_dst_reg h_sb_final h_vals h_len h_fit

end obseq.proof
