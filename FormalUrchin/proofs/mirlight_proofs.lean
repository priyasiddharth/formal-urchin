import FormalUrchin.mirlight

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
    simp [ReadWordSeq]
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
      rw [Nat.add_assoc,Nat.add_comm 1 i,]
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
