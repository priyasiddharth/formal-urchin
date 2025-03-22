import FormalUrchin.mirlight
import FormalUrchin.units
open mir

theorem readWordSeq_concat (mem : Mem) (addr : Word) (head : MemValue) (tail : List MemValue) :
  ReadWordSeq mem addr 1 = [head] →
  ReadWordSeq mem (addr + 1) tail.length = tail →
  ReadWordSeq mem addr (tail.length + 1) = head :: tail := by
    intros h_head h_tail
    have h_read_head : ReadWordSeq mem addr 1 = [head] →
      mem.mMap.find? addr = some head  := by
      cases heq : Lean.AssocList.find? addr mem.mMap
      case some v' =>
        intros h_read_head1
        simp [ReadWordSeq] at h_read_head1
        rw [heq] at h_read_head1
        --injection h_head with h_eq
        simp at h_read_head1
        congr
      case none =>
        intros h_read_head1
        simp [ReadWordSeq] at h_read_head1
        rw [heq] at h_read_head1
        contradiction
    have h_some_head := h_read_head h_head
    simp [ReadWordSeq]
    rw [h_some_head]
    rw [h_tail]
    simp

theorem readWordSeq_returns_sequence_of_bytes (mem : Mem) (addr : Word) (values : List MemValue) :
  (∀ i, (h: i < values.length) → mem.mMap.find? (addr + i) = some (values.get ⟨i, h⟩)) →
  ReadWordSeq mem addr values.length = values := by
  intros h_memhasvalues
  induction values generalizing addr
  case nil =>
    simp [ReadWordSeq]
  case cons head tail ih =>
    have h_head_eq : mem.mMap.find? addr = some head := h_memhasvalues 0 (by simp)
    have h_tail_eq : ∀ i, (h: i < tail.length) → mem.mMap.find? (addr + i + 1) = some (tail.get ⟨i, h⟩) := by
      intros i h_i
      specialize h_memhasvalues (i + 1)
      simp at h_memhasvalues
      simp
      apply h_memhasvalues h_i
    have h_head_read_ok : ReadWordSeq mem addr 1 = [head] := by
      simp [ReadWordSeq]
      simp [h_head_eq]
    have h_tail_read_ok : ReadWordSeq mem (addr + 1)
      tail.length = tail := by
      apply ih
      intros i h_i
      specialize h_memhasvalues (i + 1)
      simp at h_memhasvalues
      rw [Nat.add_assoc,Nat.add_comm 1 i]
      exact h_memhasvalues h_i
    have h_concat := readWordSeq_concat mem addr head tail h_head_read_ok h_tail_read_ok
    exact h_concat


@[simp]
theorem step_pc_stays_same_iff_halt2
    {bb: BB} {pc : PC} {prog : Prog} {env : Env} {mem : Mem} {ap : accessperm.AccessPerms}
    {stmt_list : List Stmt}
    (h_bb : prog.find? bb = some stmt_list)
    (h_stmt: pc < stmt_list.length):
      (stmt_list.get ⟨pc, h_stmt⟩ = Stmt.Halt) ↔
    Eval2 (bb, pc, prog, env, mem, ap) (bb, pc, prog, env, mem, ap) := by
  apply Iff.intro
  { intros h_stmt_eq
    apply Eval2.HaltRel
    exact h_bb
    exact h_stmt_eq
  }
  {
    intros h
    cases h
    case HaltRel s1 s2 s3 s4 =>
     -- Unify stmt_list and s1
      have : stmt_list = s1 := by
        rw [s4] at h_bb
        injection h_bb with h_eq
        symm
        exact h_eq
      subst this
      exact s3
}
@[simp]
theorem getPlaceAddr_returns_some_iff_in_env
    {base : Word} {rest: List Word}
    (env: Env) (place: Place) (addr: Addr) (offset: Word) (anyty: TyVal) (anytag: mir.Tag) :
    place = base :: rest →
    getPlaceOffset place anyty = some offset →
    env.find? base = some (addr, anyty, anytag) →
    getPlaceAddr place env = some (addr + offset) := by
  intros h_src h_getPlaceOffset h_InEnv
  simp [h_src] at h_getPlaceOffset
  simp [getPlaceAddr, h_src, h_InEnv, h_getPlaceOffset]

@[simp]
theorem copyFromMem_returns_value
    (ap: accessperm.AccessPerms)
     (src_baseaddr: Addr) (offset: Word) (values : List MemValue)
    (env: Env)
    (srcbase : Word)
    (srcrest : Place)
    (src : Place) (srcty: TyVal) (srctag: mir.Tag)
    (mem: Mem) :
    (h_src : src = srcbase :: srcrest) →
    (h_val : values ≠ []) →
    (∀ i, (h: i < values.length) → mem.mMap.find? (src_baseaddr + offset + i) = some (values.get ⟨i, h⟩)) →
    -- mir step
    env.find? srcbase = some (src_baseaddr, srcty, srctag) →
    mir.getPlaceType src env = some srcty →
    getPlaceOffset src srcty = some offset →
    mir.typeSize srcty = values.length →
    RExprToValFn (mir.RExpr.CopyOp src) env mem ap = RhsResult.Ok values srcty ap mem := by
  intros h_src h_val h_memhasvalues h_srcInEnv h_getPlaceTy h_getPlaceOffset h_tysz
  have h_read_word_seq :=
    readWordSeq_returns_sequence_of_bytes mem (src_baseaddr + offset) values h_memhasvalues
  have h_getPlaceAddr := getPlaceAddr_returns_some_iff_in_env env src src_baseaddr offset srcty srctag h_src h_getPlaceOffset h_srcInEnv
  simp [RExprToValFn, h_getPlaceAddr, h_srcInEnv, h_getPlaceTy, h_read_word_seq, h_tysz, h_val]


theorem findval_after_insert (mem : Mem) (addr : Word) (head : MemValue) :
  -- The `insert` function ensures that `find?` will return the newly inserted value for the given key.
  Lean.AssocList.find? addr (Lean.AssocList.insert mem.mMap addr head) = some head := by
  simp [Lean.AssocList.insert]
  by_cases h_contains : Lean.AssocList.contains addr mem.mMap
  case pos =>
    simp [Lean.AssocList.find?, Lean.AssocList.replace, h_contains]
    
  case neg =>
    simp [Lean.AssocList.find?, Lean.AssocList.cons, h_contains]

theorem find_after_insert (mem : Mem) (addr : Word) (head : MemValue) (tail : List MemValue) :
  -- The `insert` function ensures that `find?` will return the newly inserted value for the given key.
  Lean.AssocList.find? addr (Lean.AssocList.insert (WriteWordSeq mem (addr + 1) tail).mMap addr head) = some head := by
  simp [Lean.AssocList.find?, Lean.AssocList.insert]

theorem insert_only_updates_key (m : Lean.AssocList Word MemValue) (location : Word) (val : MemValue) (k : Word) :
  ¬location = k →
  Lean.AssocList.find? k (Lean.AssocList.insert m location val) = Lean.AssocList.find? k m := by
  intros h_cond
  simp [Lean.AssocList.insert, Lean.AssocList.find?]
  -- Use `h_cond` to deduce `location == k = false`
  sorry

theorem writeWordSeq_returns_word (mem : Mem) (mem': Mem) (addr : Word) (addr': Word) (value : MemValue) :
  WriteWordSeq mem addr [value] = mem' →
  (if addr' = addr then
    mem'.mMap.find? addr' = some (value)
  else
    mem'.mMap.find? addr' = mem.mMap.find? addr') := by

  intros h_writewordseq
  by_cases h_addr_eq: addr' = addr
  case pos =>
    simp [h_addr_eq]
    simp [WriteWordSeq] at h_writewordseq
    simp [←h_writewordseq]
    have h_find_after_insert := findval_after_insert mem addr value
    rw [←h_addr_eq]
    rw [←h_addr_eq] at h_find_after_insert
    exact h_find_after_insert
  case neg =>
    simp [h_addr_eq, ←h_writewordseq]
    simp [Eq.comm] at h_addr_eq
    have h_nomemchange := insert_only_updates_key mem.mMap addr value addr' h_addr_eq
    exact h_nomemchange

theorem sub_lt_of_lt_add {a b c : Nat} : (c > 0) → (a < c + b) → a - b < c := by
  intros hpos hlt
  cases Nat.lt_or_ge a b with
  | inl hlt =>
    rw [Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt)]
    exact hpos
  | inr hge =>
    have h1 : a - b + b < c + b := by
      rw [Nat.sub_add_cancel hge]
      exact hlt
    apply Nat.lt_of_add_lt_add_right h1

theorem WriteWordSeq_concat {mem'': Mem} (mem : Mem) (addr : Word) (head : MemValue) (tail : List MemValue) :
  ∃ mem' : Mem, (WriteWordSeq mem (addr + 1) tail = mem' ∧
   WriteWordSeq mem' addr [head] = mem'') ↔
  WriteWordSeq mem addr (head :: tail) = mem'' := by
  let mem' := WriteWordSeq mem (addr + 1) tail
  exists mem'
  apply Iff.intro
  {
    intro h
    obtain ⟨h_tail, h_head⟩ := h
    simp [WriteWordSeq]
    simp [WriteWordSeq] at h_head
    rw [← h_tail] at h_head
    exact h_head
  }
  {
    intro h
    simp [WriteWordSeq]
    simp [WriteWordSeq] at h

    apply And.intro
    {
      rfl
    }
    {
      simp [mem']
      exact h
    }
  }

theorem h_succ_is_plus1 {a b : Nat} (h : a < b) : a + 1 < b + 1 := by
  exact Nat.succ_lt_succ h

theorem get_tail_eq
  {α : Type}
  {addr addr' : Nat}
  (head : α) (tail : List α)
  (h₁ : addr' - addr < tail.length + 1)
  (h₂ : addr' ≥ addr + 1)
  (h_tail : tail.length > 0) :
  (head :: tail).get ⟨addr' - addr, h₁⟩ = tail[addr' - (addr + 1)] := by
  -- let n := addr' - addr
  let n := addr' - addr
  have hn_pos : n ≥ 1 := by
    have hn_pos : addr' - addr ≥ 1 := by
      apply Nat.le_sub_of_add_le
      rw [Nat.add_comm] at h₂
      exact h₂
    exact hn_pos

  let m := addr' - (addr + 1)
  have h_m_eq : n = m + 1 := by
    have h_eq' : addr' - (addr + 1) = addr' - addr  - 1 := by
      rw [Nat.sub_sub]
    symm
    simp [h_eq', m, n]
    have h_addr_ge : 1 ≤ addr' - addr := by
      apply Nat.le_sub_of_add_le
      rw [Nat.add_comm] at h₂
      exact h₂
    apply Nat.sub_add_cancel h_addr_ge
    -- Prove bounds for indexing
  have h_n_lt : n < (head :: tail).length := by
    change (addr' - addr) < (head :: tail).length
    simp
    exact h₁
  have h_eq' : addr' - (addr + 1) = addr' - addr  - 1 := by
        rw [Nat.sub_sub]
  have h_m_lt : m < tail.length := by
    change addr' - (addr + 1) < tail.length
    let hh_1 := sub_lt_of_lt_add h_tail h₁
    rw [←h_eq'] at hh_1
    exact hh_1
  change (head :: tail).get ⟨n, h_n_lt⟩ = tail[m]
  simp [h_m_eq]


theorem writeWordSeq_returns_sequence_of_words  {mem': Mem} (mem : Mem) (addr : Word) (addr': Word) (values : List MemValue) :
  ∃ mem' : Mem, WriteWordSeq mem addr values = mem' →
  (if h : addr' ≥ addr ∧ addr' - addr  < values.length then
    mem'.mMap.find? addr' = some (values.get ⟨addr' - addr, h.right⟩)
  else
    mem'.mMap.find? addr' = mem.mMap.find? addr') := by
  exists mem'
  intros h_write
  induction values generalizing mem' addr
  case nil =>
    simp [WriteWordSeq] at h_write
    have h_mem : mem' = mem := by
      rw [←h_write]
    subst h_mem
    simp
  case cons head tail ih =>
    obtain ⟨mem_intmd, h_iff⟩ := WriteWordSeq_concat mem addr head tail
    --specialize ih (addr + 1)
    let h_0 := (h_iff.mpr h_write).left
    let ih_1 := ih (addr + 1) h_0
    let h_1 := (h_iff.mpr h_write).right
    let h_2 := writeWordSeq_returns_word mem_intmd mem' addr addr' head
    let h_3 := h_2 h_1
    simp at ih_1
    simp
    let h_4 := And.intro h_3 ih_1
    simp at h_4
    by_cases h_cond : addr' ≥ addr ∧ addr' - addr < tail.length + 1
    case pos =>
      simp [h_cond]
      by_cases h_addr : addr' = addr
      case pos =>
        simp [h_addr] at h_3
        simp [h_addr]
        exact h_3
      case neg =>
        have h_addr_tail :
          addr' ≥ addr + 1 := by
          let h_addr_in_tail := And.intro h_addr h_cond.left
          -- Extract the two parts of the hypothesis
          obtain ⟨h_neq, h_ge⟩ := h_addr_in_tail
          -- Convert `addr' ≥ addr` and `addr' ≠ addr` to `addr' > addr`
          have h_gt : addr' > addr := Nat.lt_of_le_of_ne h_ge (Ne.symm h_neq)
          -- Apply the fact that `addr' > addr` implies `addr + 1 ≤ addr'`
          exact Nat.succ_le_of_lt h_gt
        by_cases h_no_tail : tail = []
        case pos =>
          -- This is an impossible case
          -- TODO: simplify the proof
          have h_tail_zero_length : tail.length = 0 := by
            rw [h_no_tail]
            simp
          simp [h_tail_zero_length, h_addr_tail] at h_cond
          let h_cond_right :=  Nat.le_of_sub_eq_zero h_cond.right
          let h_cond' :=  Nat.le_antisymm h_cond.left h_cond_right
          have h_contradiction : False := by
            rw [h_cond'] at h_addr
            exact h_addr rfl
          contradiction
        case neg =>
          have h_tail_ne_zero_length : tail.length > 0 := by
            cases tail with
            | nil => contradiction
            | cons _ _ => simp [List.length]
          let h_1_rgt_to_lft := sub_lt_of_lt_add h_tail_ne_zero_length h_cond.right
          have h_1_rgt_to_lft_rw : addr' - (addr + 1) < tail.length := by
            rw [Nat.sub_add_eq]
            exact h_1_rgt_to_lft
          simp [h_cond, h_addr_tail, h_1_rgt_to_lft_rw] at ih_1
          have h_addr_ne :
            addr' ≠ addr := by
            exact Ne.symm (Ne.symm h_addr)
          simp [h_addr_ne] at h_2
          let h_22 := h_2 h_1
          rw [h_22, ih_1]
          let h_skip_head := get_tail_eq head tail h_cond.right h_addr_tail h_tail_ne_zero_length
          simp [←h_skip_head]

    case neg =>
      simp [h_cond]
      have h_ih_neg :
        (addr + 1 ≤ addr' ∧ addr' - (addr + 1) < tail.length) → addr' ≥ addr ∧ addr' - addr < tail.length + 1 := by
        intros h_subset
        obtain ⟨h_ge, h_lt⟩ := h_subset
        have h_ge' : addr' ≥ addr := by
          exact Nat.le_of_succ_le h_ge
        have h_eq' : addr' - (addr + 1) = addr' - addr  - 1 := by
          rw [Nat.sub_sub]
        have h_lt' : addr' - addr < tail.length + 1 := by
          let h_eq := h_eq'
          rw [h_eq'] at h_lt
          have h_addr_ge : 1 ≤ addr' - addr := by
            apply Nat.le_sub_of_add_le
            rw [Nat.add_comm] at h_ge
            exact h_ge
          let h_x := Nat.sub_add_cancel h_addr_ge
          let h_x1 := h_succ_is_plus1 h_lt
          rw [h_x] at h_x1
          exact h_x1
        exact And.intro h_ge' h_lt'
      let hhhaaa := Not.imp h_cond h_ih_neg
      simp [hhhaaa] at ih_1
      have h_ih_neg2 :
        addr = addr' → addr' ≥ addr ∧ addr' - addr < tail.length + 1 := by
        intros h_eq
        rw [h_eq] at h_cond
        have h_ge : addr' ≥ addr := by
          exact Nat.le_of_eq h_eq
        have h_lt : addr' - addr < tail.length + 1 := by
          rw [Nat.sub_self] at h_cond
          simp [h_eq]
        exact And.intro h_ge h_lt
      let hhaaa2 := (Not.imp h_cond h_ih_neg2)
      have hhaaa3 :
        addr' ≠ addr := by
        exact Ne.symm hhaaa2
      simp [hhaaa3] at h_3
      rw [←h_3] at ih_1
      exact ih_1

@[simp]
theorem EvalStep_copy
    (prog: Prog) (bb: BB) (pc: PC) (pc': PC)
    (ap: accessperm.AccessPerms)
    (src_baseaddr: Addr) (offset: Word) (values : List MemValue)
    (dst_baseaddr: Addr) (dst_offset: Word) (values : List MemValue)
    (env: Env) (env': Env)
    (srcbase : Word)
    (srcrest : Place)
    (src : Place) (srcty: TyVal) (srctag: mir.Tag)
    (dst : Place) (dsttag: mir.Tag)
    (mem: Mem) (mem': Mem) :
    --  pre condition
    (h_src : src = srcbase :: srcrest) →
    (h_dst : dst = dstbase :: dstrest) →
    (h_val : values ≠ []) →
    (∀ i, (h: i < values.length) → mem.mMap.find? (src_baseaddr + offset + i) = some (values.get ⟨i, h⟩)) →
    env.find? srcbase = some (src_baseaddr, srcty, srctag) →
    mir.getPlaceType src env = some srcty →
    getPlaceOffset src srcty = some offset →
    mir.typeSize srcty = values.length →
    -- mir step
    Eval2 (bb, pc, prog, env, mem, ap) (bb, pc', prog, env', mem', ap) →
    -- post condition
    ∀ k', if k' == dstbase then env'.find? k' = some (dst_baseaddr, srcty, dsttag)
        else env'.find? k' = env.find? k' →
    getPlaceOffset dst srcty = some dst_offset →
    (h_addr: dst_addr = dst_baseaddr + dst_offset) →
    (prog.find? bb = some [mir.Stmt.Assgn dst (mir.RExpr.CopyOp (srcbase :: srcrest))]) →
    (∀ addr', i = addr' - dst_addr → if h : addr' ≥ dst_addr ∧ i < values.length then
      mem'.mMap.find? addr' = some (values.get ⟨i, h.right⟩)
    else
      mem'.mMap.find? addr' = mem.mMap.find? addr') := by
  sorry
