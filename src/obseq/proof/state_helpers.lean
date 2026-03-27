import obseq.proof.core

/-!
# `obseq.proof.state_helpers`

Shared lookup, write, and memory-simulation lemmas used by the concrete proof
clusters. This file intentionally stays cluster-agnostic.

The local preservation proofs in the statement-specific files follow the same
shape: recover concrete source/target addresses, execute one source or target
step, and then show that the simulation relations survive the resulting updates.

This helper layer supports exactly that proof strategy:

- the block-level `sim_mem_at_*` lemmas package the low-level memory reasoning
  needed by the constant and copy proofs into direct simulation transport
  steps, so the cluster files can rebuild `StateSim` without
  reopening concrete memory proofs each time.
-/

namespace obseq.proof

open obseq
open obseq.mirlite
open obseq.oseair hiding State Result
open obseq.compile
open scoped obseq.notation

theorem mem_vals_eq_get?
  {vals_mir : List mirlite.MemValue}
  {vals_osea : List oseair.Val}
  (h_vals : mem_vals_eq vals_mir vals_osea)
  (i : Nat) :
  mem_val_eq_opt (vals_mir.get? i) (vals_osea.get? i) := by
  induction h_vals generalizing i with
  | nil =>
      cases i <;> trivial
  | @cons v_mir v_osea vals_mir vals_osea h_head _h_tail ih =>
      cases i with
      | zero =>
          exact h_head
      | succ i =>
          exact ih i

/-! ## Same-Key Insert Lookup Facts -/

/-!
These are the only environment/register update lemmas still used by the active
proofs. The fresh-constant proofs rely on them through `simp` when rebuilding
the newly inserted source and target bindings.
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

/-! ## List Lookup Stability -/

/--
`list_lookup_filter_ne` is the base assoc-list lemma needed by the memory-side
`find?_write_ne` facts below.

The memory maps are implemented as assoc-lists updated by filtering out the old
key and consing the new binding. This theorem says that filtering a different
key leaves lookup at `key` unchanged.
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

/-! ## Concrete Memory Lookup and Write Facts -/

/-!
These lemmas are the memory-side normal forms used by the `sim_mem_at_*`
transport theorems below. They are kept because the transport proofs use them
implicitly through `simp`.
-/

@[simp] theorem mir_mem_find_write_eq
  (m : mirlite.Mem) (addr : Word) (v : mirlite.MemValue) :
  (m.write addr v).find? addr = some v := by
  simp [mirlite.Mem.write, mirlite.Mem.find?, List.lookup]

@[simp] theorem mir_mem_find_write_ne
  (m : mirlite.Mem) (addr1 addr2 : Word) (v : mirlite.MemValue)
  (h_ne : addr2 ≠ addr1) :
  (m.write addr1 v).find? addr2 = m.find? addr2 := by
  unfold mirlite.Mem.write mirlite.Mem.find?
  cases h_eq : (addr2 == addr1) with
  | true =>
      have : addr2 = addr1 := by simpa using h_eq
      contradiction
  | false =>
      simp [List.lookup, list_lookup_filter_ne, h_eq, h_ne]

@[simp] theorem mir_mem_write_addrStart
  (m : mirlite.Mem) (addr : Word) (v : mirlite.MemValue) :
  (m.write addr v).addrStart = m.addrStart := by
  rfl

@[simp] theorem osea_mem_find_write_eq
  (m : oseair.Mem) (addr : Word) (v : oseair.Val) :
  (m.write addr v).find? addr = some v := by
  simp [oseair.Mem.write, oseair.Mem.find?, List.lookup]

@[simp] theorem osea_mem_find_write_ne
  (m : oseair.Mem) (addr1 addr2 : Word) (v : oseair.Val)
  (h_ne : addr2 ≠ addr1) :
  (m.write addr1 v).find? addr2 = m.find? addr2 := by
  unfold oseair.Mem.write oseair.Mem.find?
  cases h_eq : (addr2 == addr1) with
  | true =>
      have : addr2 = addr1 := by simpa using h_eq
      contradiction
  | false =>
      simp [List.lookup, list_lookup_filter_ne, h_eq, h_ne]

@[simp] theorem osea_mem_write_addrStart
  (m : oseair.Mem) (addr : Word) (v : oseair.Val) :
  (m.write addr v).addrStart = m.addrStart := by
  rfl

@[simp] theorem mir_writeWordSeq_addrStart
  (m : mirlite.Mem) (addr : Word) (vals : List mirlite.MemValue) :
  (mirlite.writeWordSeq m addr vals).addrStart = m.addrStart := by
  induction vals generalizing m addr with
  | nil =>
      rfl
  | cons v vs ih =>
      simp [mirlite.writeWordSeq, ih]

@[simp] theorem mir_writeWordSeq_singleton
  (m : mirlite.Mem) (addr : Word) (v : mirlite.MemValue) :
  mirlite.writeWordSeq m addr [v] = m.write addr v := by
  simp [mirlite.writeWordSeq]

@[simp] theorem osea_writeWordSeq_addrStart
  (m : oseair.Mem) (addr : Word) (vals : List oseair.Val) :
  (oseair.writeWordSeq m addr vals).addrStart = m.addrStart := by
  induction vals generalizing m addr with
  | nil =>
      rfl
  | cons v vs ih =>
      simp [oseair.writeWordSeq, ih]

@[simp] theorem osea_writeWordSeq_singleton
  (m : oseair.Mem) (addr : Word) (v : oseair.Val) :
  oseair.writeWordSeq m addr [v] = m.write addr v := by
  simp [oseair.writeWordSeq]

theorem mir_mem_find_writeWordSeq_before
  (m : mirlite.Mem)
  (dst query : Word)
  (vals : List mirlite.MemValue)
  (h_lt : query < dst) :
  (mirlite.writeWordSeq m dst vals).find? query = m.find? query := by
  induction vals generalizing m dst query with
  | nil =>
      simp [mirlite.writeWordSeq]
  | cons v vs ih =>
      have h_ne : query ≠ dst := Nat.ne_of_lt h_lt
      simp [mirlite.writeWordSeq, h_ne,
        ih (m := m.write dst v) (dst := dst + 1) (query := query)
          (Nat.lt_trans h_lt (Nat.lt_succ_self dst))]

theorem osea_mem_find_writeWordSeq_before
  (m : oseair.Mem)
  (dst query : Word)
  (vals : List oseair.Val)
  (h_lt : query < dst) :
  (oseair.writeWordSeq m dst vals).find? query = m.find? query := by
  induction vals generalizing m dst query with
  | nil =>
      simp [oseair.writeWordSeq]
  | cons v vs ih =>
      have h_ne : query ≠ dst := Nat.ne_of_lt h_lt
      simp [oseair.writeWordSeq, h_ne,
        ih (m := m.write dst v) (dst := dst + 1) (query := query)
          (Nat.lt_trans h_lt (Nat.lt_succ_self dst))]

theorem mir_mem_find_writeWordSeq_after
  (m : mirlite.Mem)
  (dst query : Word)
  (vals : List mirlite.MemValue)
  (h_after : dst + vals.length ≤ query) :
  (mirlite.writeWordSeq m dst vals).find? query = m.find? query := by
  induction vals generalizing m dst query with
  | nil =>
      simp [mirlite.writeWordSeq]
  | cons v vs ih =>
      have h_succ_le_query : dst + 1 ≤ query := by
        exact Nat.le_trans (by simp) h_after
      have h_ne : query ≠ dst := by
        exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.lt_succ_self dst) h_succ_le_query)
      have h_after_tail : dst + 1 + vs.length ≤ query := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h_after
      simp [mirlite.writeWordSeq, h_ne,
        ih (m := m.write dst v) (dst := dst + 1) (query := query) h_after_tail]

theorem osea_mem_find_writeWordSeq_after
  (m : oseair.Mem)
  (dst query : Word)
  (vals : List oseair.Val)
  (h_after : dst + vals.length ≤ query) :
  (oseair.writeWordSeq m dst vals).find? query = m.find? query := by
  induction vals generalizing m dst query with
  | nil =>
      simp [oseair.writeWordSeq]
  | cons v vs ih =>
      have h_succ_le_query : dst + 1 ≤ query := by
        exact Nat.le_trans (by simp) h_after
      have h_ne : query ≠ dst := by
        exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.lt_succ_self dst) h_succ_le_query)
      have h_after_tail : dst + 1 + vs.length ≤ query := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h_after
      simp [oseair.writeWordSeq, h_ne,
        ih (m := m.write dst v) (dst := dst + 1) (query := query) h_after_tail]

theorem mir_mem_find_writeWordSeq_written
  (m : mirlite.Mem)
  (addr : Word)
  (vals : List mirlite.MemValue)
  (i : Nat)
  (h_i : i < vals.length) :
  (mirlite.writeWordSeq m addr vals).find? (addr + i) = vals.get? i := by
  induction vals generalizing m addr i with
  | nil =>
      cases Nat.not_lt_zero i h_i
  | cons v vs ih =>
      cases i with
      | zero =>
          rw [mirlite.writeWordSeq]
          have h_before :=
            mir_mem_find_writeWordSeq_before (m := m.write addr v) (dst := addr + 1)
              (query := addr) (vals := vs) (Nat.lt_succ_self addr)
          simp [Nat.add_zero]
          rw [h_before]
          rw [mir_mem_find_write_eq]
      | succ i =>
          have h_i' : i < vs.length := Nat.lt_of_succ_lt_succ h_i
          have h := ih (m := m.write addr v) (addr := addr + 1) (i := i) h_i'
          simpa [mirlite.writeWordSeq, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm,
            Nat.add_comm] using h

theorem osea_mem_find_writeWordSeq_written
  (m : oseair.Mem)
  (addr : Word)
  (vals : List oseair.Val)
  (i : Nat)
  (h_i : i < vals.length) :
  (oseair.writeWordSeq m addr vals).find? (addr + i) = vals.get? i := by
  induction vals generalizing m addr i with
  | nil =>
      cases Nat.not_lt_zero i h_i
  | cons v vs ih =>
      cases i with
      | zero =>
          rw [oseair.writeWordSeq]
          have h_before :=
            osea_mem_find_writeWordSeq_before (m := m.write addr v) (dst := addr + 1)
              (query := addr) (vals := vs) (Nat.lt_succ_self addr)
          simp [Nat.add_zero]
          rw [h_before]
          rw [osea_mem_find_write_eq]
      | succ i =>
          have h_i' : i < vs.length := Nat.lt_of_succ_lt_succ h_i
          have h := ih (m := m.write addr v) (addr := addr + 1) (i := i) h_i'
          simpa [oseair.writeWordSeq, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm,
            Nat.add_comm] using h

/-! ## Simulation Transport Across Writes -/

/--
`mem_val_eq_opt_writeWordSeq` is the pointwise write-transport lemma used by the
block simulation proofs.

If two memories agree at address `addr`, then writing pointwise-equal value
lists at the same destination address preserves agreement at `addr`, regardless
of whether `addr` lies inside the written block.
-/
theorem mem_val_eq_opt_writeWordSeq
  {m_mir : mirlite.Mem}
  {m_osea : oseair.Mem}
  {dst addr : Word}
  {vals_mir : List mirlite.MemValue}
  {vals_osea : List oseair.Val}
  (h_cell : mem_val_eq_opt (m_mir.find? addr) (m_osea.find? addr))
  (h_vals : mem_vals_eq vals_mir vals_osea) :
  mem_val_eq_opt
    ((mirlite.writeWordSeq m_mir dst vals_mir).find? addr)
    ((oseair.writeWordSeq m_osea dst vals_osea).find? addr) := by
  induction h_vals generalizing m_mir m_osea dst addr with
  | nil =>
      simp [mirlite.writeWordSeq, oseair.writeWordSeq]
      exact h_cell
  | @cons v_mir v_osea vals_mir vals_osea h_head _h_tail ih =>
      by_cases h_addr : addr = dst
      · subst addr
        have h_head_cell :
            mem_val_eq_opt
              ((m_mir.write dst v_mir).find? dst)
              ((m_osea.write dst v_osea).find? dst) := by
          simp [mem_val_eq_opt, h_head]
        rw [mirlite.writeWordSeq, oseair.writeWordSeq]
        exact ih (m_mir := m_mir.write dst v_mir)
          (m_osea := m_osea.write dst v_osea)
          (dst := dst + 1)
          (addr := dst)
          h_head_cell
      · have h_next :
          mem_val_eq_opt
            ((m_mir.write dst v_mir).find? addr)
            ((m_osea.write dst v_osea).find? addr) := by
          simp [h_addr, h_cell]
        rw [mirlite.writeWordSeq, oseair.writeWordSeq]
        exact ih (m_mir := m_mir.write dst v_mir)
          (m_osea := m_osea.write dst v_osea)
          (dst := dst + 1)
          (addr := addr)
          h_next

/--
`mem_vals_eq_readWordSeq` rebuilds block value agreement from the pointwise
memory simulation predicate used in `sim_mem_at`.
-/
theorem mem_vals_eq_readWordSeq
  {m_mir : mirlite.Mem}
  {m_osea : oseair.Mem}
  {addr : Word}
  {sz : Nat}
  (h_cells :
    ∀ i, i < sz →
      mem_val_eq_opt (m_mir.find? (addr + i)) (m_osea.find? (addr + i))) :
  mem_vals_eq
    (mirlite.readWordSeq m_mir addr sz)
    (oseair.readWordSeq m_osea addr sz) := by
  induction sz generalizing addr with
  | zero =>
      exact mem_vals_eq.nil
  | succ sz ih =>
      have h0 := h_cells 0 (Nat.succ_pos _)
      rw [Nat.add_zero] at h0
      have htail :
          ∀ i, i < sz →
            mem_val_eq_opt (m_mir.find? (addr + 1 + i)) (m_osea.find? (addr + 1 + i)) := by
        intro i hi
        have h_tail_i := h_cells (i + 1) (Nat.succ_lt_succ hi)
        rw [Nat.add_comm i 1, ←Nat.add_assoc] at h_tail_i
        exact h_tail_i
      cases h_m : m_mir.find? addr <;> cases h_o : m_osea.find? addr <;>
        simp [mirlite.readWordSeq, oseair.readWordSeq,
          h_m, h_o, mem_val_eq_opt, mem_val_eq] at h0 ⊢ <;>
        exact mem_vals_eq.cons h0 (ih htail)

/--
`sim_mem_at_write` transports block simulation across corresponding source/target
writes of pointwise-equal value lists.

This is the generic block lemma used both by the constant proofs and by the
copy proofs: once the written lists correspond under `mem_vals_eq`, block
simulation for any tracked base survives the write on both sides.
-/
theorem sim_mem_at_write
  {s_mir : mirlite.State}
  {s_osea : oseair.State}
  {trackedAddr : Word}
  {layout : LayoutTy}
  {dst : Word}
  {vals_mir : List mirlite.MemValue}
  {vals_osea : List oseair.Val}
  (h_sim : sim_mem_at s_mir s_osea trackedAddr layout)
  (h_vals : mem_vals_eq vals_mir vals_osea) :
  sim_mem_at
    { s_mir with mem := mirlite.writeWordSeq s_mir.mem dst vals_mir }
    { s_osea with mem := oseair.writeWordSeq s_osea.mem dst vals_osea }
    trackedAddr layout := by
  refine ⟨by simp [h_sim.1], ?_⟩
  intro i hi
  exact mem_val_eq_opt_writeWordSeq (h_sim.2 i hi) h_vals

theorem sim_mem_at_write_disjoint
  {s_mir : mirlite.State}
  {s_osea : oseair.State}
  {trackedAddr : Word}
  {layout : LayoutTy}
  {dst : Word}
  {writtenSize : Word}
  {vals_mir : List mirlite.MemValue}
  {vals_osea : List oseair.Val}
  (h_sim : sim_mem_at s_mir s_osea trackedAddr layout)
  (h_len_mir : vals_mir.length = writtenSize)
  (h_len_osea : vals_osea.length = writtenSize)
  (h_disjoint : interval_disjoint trackedAddr (blockSize layout) dst writtenSize) :
  sim_mem_at
    { s_mir with mem := mirlite.writeWordSeq s_mir.mem dst vals_mir }
    { s_osea with mem := oseair.writeWordSeq s_osea.mem dst vals_osea }
    trackedAddr layout := by
  refine ⟨by simp [h_sim.1], ?_⟩
  intro i hi
  cases h_disjoint with
  | inl h_before =>
      have h_lt_block : trackedAddr + i < trackedAddr + blockSize layout :=
        Nat.add_lt_add_left hi trackedAddr
      have h_lt_dst : trackedAddr + i < dst := Nat.lt_of_lt_of_le h_lt_block h_before
      rw [mir_mem_find_writeWordSeq_before (m := s_mir.mem) (dst := dst) (query := trackedAddr + i)
            (vals := vals_mir) h_lt_dst]
      rw [osea_mem_find_writeWordSeq_before (m := s_osea.mem) (dst := dst) (query := trackedAddr + i)
            (vals := vals_osea) h_lt_dst]
      exact h_sim.2 i hi
  | inr h_after =>
      have h_query_ge : trackedAddr ≤ trackedAddr + i := Nat.le_add_right trackedAddr i
      have h_after_mir : dst + vals_mir.length ≤ trackedAddr + i := by
        rw [h_len_mir]
        exact Nat.le_trans h_after h_query_ge
      have h_after_osea : dst + vals_osea.length ≤ trackedAddr + i := by
        rw [h_len_osea]
        exact Nat.le_trans h_after h_query_ge
      rw [mir_mem_find_writeWordSeq_after (m := s_mir.mem) (dst := dst) (query := trackedAddr + i)
            (vals := vals_mir) h_after_mir]
      rw [osea_mem_find_writeWordSeq_after (m := s_osea.mem) (dst := dst) (query := trackedAddr + i)
            (vals := vals_osea) h_after_osea]
      exact h_sim.2 i hi

end obseq.proof
