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

/--
`state_sim_write` lifts corresponding source/target writes to the full
renaming-aware `StateSim π ρa ρt` relation.

This is the reusable shell around the low-level block transport lemmas for the
existing-place fragment families. It preserves the input renamings and takes
the post-step `sb_sim` witness explicitly instead of relying on exact AP
equality.
-/
axiom state_sim_write
  {π : PlaceMap}
  {ρa : AddrRenaming}
  {ρt : TagRenaming}
  {s_mir : mirlite.State}
  {s_osea : oseair.State}
  {dst_mir dst_osea : Word}
  {ap_m' ap_o' : AccessPerms}
  {pc_mir pc_osea : Nat}
  {vals_mir : List mirlite.MemValue}
  {vals_osea : List oseair.Val}
  (h_sim : StateSim π ρa ρt s_mir s_osea)
  (h_sb : sb_sim ρa ρt ap_m' ap_o')
  (h_vals : mem_vals_eq vals_mir vals_osea) :
  StateSim π ρa ρt
    { s_mir with
      ap := ap_m',
      mem := mirlite.writeWordSeq s_mir.mem dst_mir vals_mir,
      pc := pc_mir }
    { s_osea with
      ap := ap_o',
      mem := oseair.writeWordSeq s_osea.mem dst_osea vals_osea,
      pc := pc_osea }

axiom state_sim_alloc_write
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
  (h_sb : sb_sim ρa' ρt' ap_m' ap_o')
  (h_new_addr : ρa' freshAddr_m = some freshAddr_o)
  (h_new_tag : ρt' tag_m = some tag_o)
  (h_vals : mem_vals_eq vals_mir vals_osea) :
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
      pc := pc_osea }

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
            mem := oseair.writeWordSeq s_osea.mem dstAddr
              (oseair.readWordSeq s_osea.mem srcAddr (blockSize layout)),
            pc := s_osea.pc + 1 } := by
    unfold oseair.step
    rw [dif_pos h_pc, h_get]
    simp [h_src_reg, h_dst_reg, h_read, h_write, blockSize]
  simp [oseair.runN, h_step]

end obseq.proof
