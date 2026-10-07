import obseq3.proof.die_back_step

/-!
# Die elision, backward: the machine

`step_back`: one OSEA-IR_B step from `Inv`-related states is matched by an
OSEA-IR step, and `Inv` holds again. `die_elision_back`: for route-bracket
programs, a run that succeeds on OSEA-IR_B succeeds on OSEA-IR in lockstep.
-/

namespace obseq3.proof

open obseq3 obseq3.bytes obseq3.oseair

/-! ## Inversions on the OSEA-IR side -/

theorem Instr.through_cases {r : Register} {i : Instr} (h : i.through r = true) :
    (∃ x rhs, i = .Assgn x rhs ∧ x ≠ r ∧
      ((∃ lay, rhs = .Load lay r) ∨ (∃ k, rhs = .ExposeAddr k r) ∨
       (∃ k, rhs = .FromExposed k r) ∨ (∃ k d ib, rhs = .PtrOffset k r d ib))) ∨
    (∃ lay s, i = .RStore lay s r ∧ s ≠ r) ∨
    (∃ lay vs, i = .CStore lay vs r) := by
  cases i with
  | Assgn x rhs =>
      left
      cases rhs <;> simp [Instr.through] at h
      all_goals (obtain ⟨rfl, hx⟩ := h; exact ⟨x, _, rfl, hx, by simp⟩)
  | RStore lay s p =>
      simp only [Instr.through, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
      obtain ⟨rfl, hs⟩ := h
      exact Or.inr (Or.inl ⟨lay, s, rfl, hs⟩)
  | CStore lay vs p =>
      simp only [Instr.through, beq_iff_eq] at h
      subst h
      exact Or.inr (Or.inr ⟨lay, vs, rfl⟩)
  | _ => simp [Instr.through] at h

/-- A route borrow on OSEA-IR: the register gets the fresh tag, and the
    retag is the one `sb_ref_push_top` speaks of. -/
theorem evalRhs_borrow_inv {pc : Nat} {reg : RegMap} {mem : bytes.Mem} {pA : AccessPerms}
    {k : RefKind} {n : Nat} {base : Register} {off : Nat}
    {vals : List Val} {sA1 : oseair.State MSB}
    (h : evalRhs MSB ⟨pc, reg, mem, pA⟩ (.Borrow k false [] (some n) base off) = .Ok vals sA1) :
    ∃ b0 bo ex sz tg u, reg.lookup base = some [.Ptr b0 bo ex sz tg] ∧
      sb_ref pA (b0 + bo + off) n tg k false [] = .ok (sA1.perms, u) ∧
      vals = [.Ptr b0 (bo + off) n sz u] ∧ sA1.pc = pc ∧ sA1.reg = reg ∧ sA1.mem = mem := by
  simp only [evalRhs] at h
  split at h
  · rename_i b0 bo ex sz tg hl
    try simp only at h
    split at h
    · cases h
    split at h
    · cases h
    split at h
    · rename_i p2 u hr
      cases h
      exact ⟨b0, bo, ex, sz, tg, u, hl, hr, rfl, rfl, rfl, rfl⟩
    · cases h
  · cases h

/-- An access through `r` on OSEA-IR: one read through `r`'s tag, then
    possibly an expose of a tag read from memory. -/
theorem evalRhs_through_inv {pc : Nat} {reg : RegMap} {mem : bytes.Mem} {pA : AccessPerms}
    {Q : Tag → Prop} (hm : MemOK Q mem) (hq0 : Q wildcardTag) {r : Register} {rhs : Rhs}
    (hrhs : (∃ lay, rhs = .Load lay r) ∨ (∃ k, rhs = .ExposeAddr k r) ∨
       (∃ k, rhs = .FromExposed k r) ∨ (∃ k d ib, rhs = .PtrOffset k r d ib))
    {vals : List Val} {sA1 : oseair.State MSB}
    (h : evalRhs MSB ⟨pc, reg, mem, pA⟩ rhs = .Ok vals sA1) :
    ∃ base off ext size tag len A2, reg.lookup r = some [.Ptr base off ext size tag] ∧
      sb_read pA (base + off) len tag = .ok A2 ∧
      (sA1.perms = A2 ∨ ∃ t', Q t' ∧ sA1.perms = { A2 with exposed := t' :: A2.exposed }) ∧
      sA1.pc = pc ∧ sA1.reg = reg ∧ sA1.mem = mem ∧ ValsOK Q vals := by
  -- the shared head: `readCellThrough`
  have rct : ∀ {k : Scalar} {v : Val} {p2 : AccessPerms},
      readCellThrough MSB ⟨pc, reg, mem, pA⟩ r k = .ok (v, p2) →
      ∃ base off ext size tag, reg.lookup r = some [.Ptr base off ext size tag] ∧
        sb_read pA (base + off) k.sizeB tag = .ok p2 ∧ ValsOK Q [v] := by
    intro k v p2 hc
    simp only [readCellThrough] at hc
    split at hc
    · rename_i base offset ext size tag hl
      split at hc
      · cases hc
      split at hc
      · cases hc
      split at hc
      · cases hc
      rename_i p3 hrd
      cases hc
      exact ⟨base, offset, ext, size, tag, hl, hrd, hm.decodeV hq0 k _ _⟩
    · cases hc
  rcases hrhs with ⟨lay, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, d, ib, rfl⟩
  · simp only [evalRhs] at h
    split at h
    · rename_i base offset ext size tag hl
      split at h
      · cases h
      split at h
      · cases h
      split at h
      · rename_i p2 hrd
        try simp only at h
        split at h
        · cases h
        cases h
        exact ⟨base, offset, ext, size, tag, _, _, hl, hrd, Or.inl rfl, rfl, rfl, rfl,
          hm.readL hq0 _ lay⟩
      · cases h
    · cases h
  · simp only [evalRhs] at h
    split at h
    · cases h
    · rename_i pBase pOff pExt pSize pTag p2 hc
      obtain ⟨base, off, ext, size, tag, hl, hrd, hv⟩ := rct hc
      try simp only at h
      split at h
      · rename_i p3 he
        cases h
        refine ⟨base, off, ext, size, tag, _, _, hl, hrd, ?_, rfl, rfl, rfl, ValsOK.dat _ _⟩
        rcases sb_expose_fields he with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr ⟨pTag, hv _ List.mem_cons_self _ _ _ _ _ rfl, rfl⟩
      · cases h
    · cases h
  · simp only [evalRhs] at h
    split at h
    · cases h
    · rename_i nn p2 hc
      obtain ⟨base, off, ext, size, tag, hl, hrd, -⟩ := rct hc
      cases h
      exact ⟨base, off, ext, size, tag, _, _, hl, hrd, Or.inl rfl, rfl, rfl, rfl, ValsOK.ptr hq0⟩
    · cases h
  · simp only [evalRhs] at h
    split at h
    · cases h
    · rename_i pBase pOff pExt pSize pTag p2 hc
      obtain ⟨base, off, ext, size, tag, hl, hrd, hv⟩ := rct hc
      try simp only at h
      split at h
      · cases h
      · cases h
        exact ⟨base, off, ext, size, tag, _, _, hl, hrd, Or.inl rfl, rfl, rfl, rfl,
          ValsOK.ptr (hv _ List.mem_cons_self _ _ _ _ _ rfl)⟩
    · cases h

/-! ## Bookkeeping -/

theorem IsBracket.unique {prog : oseair.Prog} {b : Nat} {r r' : Register} {n n' : Nat}
    (h : IsBracket prog b r n) (h' : IsBracket prog b r' n') : r' = r ∧ n' = n := by
  have := h.die.symm.trans h'.die
  simp only [Option.some.injEq, Instr.Die.injEq] at this
  exact ⟨this.1.symm, this.2.symm⟩

/-- No bracket opens at `pc` or has its access there: the next `pc` is
    inside no bracket. -/
def NotInBracket (prog : oseair.Prog) (pc : Nat) : Prop :=
  ∀ b r n, IsBracket prog b r n → pc ≠ b ∧ pc ≠ b + 1

theorem NotInBracket.of_shape {prog : oseair.Prog} {pc : Nat} {i : Instr}
    (hi : prog pc = some i) (h1 : ∀ x rhs, i ≠ .Assgn x rhs) (h2 : ∀ r, i.through r = false) :
    NotInBracket prog pc := by
  intro b r n hb
  refine ⟨fun he => ?_, fun he => ?_⟩
  · subst he
    obtain ⟨k, base, off, -, hk⟩ := hb.borrow
    rw [hi] at hk
    exact h1 _ _ (Option.some.inj hk)
  · subst he
    obtain ⟨j, hj, ht⟩ := hb.access
    rw [hi] at hj
    obtain rfl := Option.some.inj hj
    rw [h2] at ht; cases ht

theorem pend_vacuous {prog : oseair.Prog} {pc : Nat} {P : Register → Nat → Prop}
    (hnb : NotInBracket prog pc) :
    ∀ b r n, IsBracket prog b r n → (pc + 1 = b + 1 ∨ pc + 1 = b + 2) → P r n := by
  intro b r n hb hpc
  have := hnb b r n hb
  omega

theorem RegsOK.and {P Q : Register → Tag → Prop} {reg : RegMap} (hP : RegsOK P reg)
    (hQ : RegsOK Q reg) : RegsOK (fun x t => P x t ∧ Q x t) reg :=
  fun x vs hl => (hP x vs hl).and (hQ x vs hl)

theorem not_contains_of_lt {l : List Tag} {N : Tag} (h : ∀ t ∈ l, t < N) :
    l.contains N = false := by
  cases hc : l.contains N
  · rfl
  · have := h N (by simpa using hc)
    exact absurd this (Nat.lt_irrefl _)

theorem not_prot_of_lt {pf : List (List Tag)} {N : Tag}
    (h : ∀ t, isProtectedIn pf t = true → t < N) : isProtectedIn pf N = false := by
  cases hc : isProtectedIn pf N
  · rfl
  · exact absurd (h N hc) (Nat.lt_irrefl _)

/-- The registers' tags, given `Inv`: those the instruction at `pc` reads
    are good. -/
theorem Inv.good {prog : oseair.Prog} {sA : oseair.State MSB} {sB : oseair.State MSB_B}
    (hp : RouteProg prog) (hI : Inv prog sA sB) {i : Instr} (hi : prog sA.pc = some i)
    {y : Register} (hy : y ∈ i.regs) : ∀ vs, sA.reg.lookup y = some vs → ValsOK (Good sA.perms) vs :=
  fun vs hl v hv b o e s t he => hI.act_ok hp hi hy hl hv he

/-! ## The bracket steps -/

/-- The route borrow opens its bracket. -/
theorem pend_borrow {prog : oseair.Prog} {pc : Nat} {reg : RegMap} {mem : bytes.Mem}
    {pA : AccessPerms} (hpi : PInv pA) (hm : MemOK (Good pA) mem)
    (hregs : RegsOK (fun x t => t < pA.NextTag ∧ (t ∈ pA.retired → Dead prog pc x)) reg)
    {r : Register} {k : RefKind} {n : Nat} {base : Register} {off : Nat} (hk : PushKind k)
    {vals : List Val} {sA1 : oseair.State MSB}
    (he : evalRhs MSB ⟨pc, reg, mem, pA⟩ (.Borrow k false [] (some n) base off) = .Ok vals sA1) :
    Pending ⟨pc + 1, sA1.reg.insert r vals, sA1.mem, sA1.perms⟩ r n := by
  obtain ⟨b0, bo, ex, sz, tg, u, -, href, rfl, -, hreg1, hmem1⟩ := evalRhs_borrow_inv he
  obtain ⟨rfl, -, hret, hex, -, hpf⟩ := sb_ref_fields href
  have htop := sb_ref_push_top hk href
  rw [hreg1, hmem1]
  refine ⟨b0, bo + off, n, sz, pA.NextTag, RegMap.lookup_insert_self _ _ _, ?_⟩
  refine ⟨hpi.pos, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show pA.NextTag ∉ sA1.perms.retired
    rw [hret]; exact fun h => Nat.lt_irrefl _ (hpi.ret _ h).2
  · show sA1.perms.exposed.contains pA.NextTag = false
    rw [hex]; exact not_contains_of_lt hpi.exb
  · show isProtectedIn sA1.perms.protFrames pA.NextTag = false
    rw [hpf rfl]; exact not_prot_of_lt hpi.prot
  · intro j hj
    simpa only [Nat.add_assoc] using htop j hj
  · refine RegsOK.insert (hregs.mono fun x t h ht => absurd (ht ▸ h.1) (Nat.lt_irrefl _)) ?_
    exact ValsOK.ptr (P := fun t => t = pA.NextTag → r = r) (fun _ => rfl)
  · exact hm.mono fun t h ht => Nat.lt_irrefl _ (ht ▸ h.1)

/-- The bracket's access keeps it open. -/
theorem pend_access {pc : Nat} {reg : RegMap} {mem : bytes.Mem} {pA : AccessPerms}
    {r : Register} {n : Nat} (hP : Pending ⟨pc, reg, mem, pA⟩ r n)
    {x : Register} (hx : x ≠ r) {rhs : Rhs}
    (hrhs : (∃ lay, rhs = .Load lay r) ∨ (∃ k, rhs = .ExposeAddr k r) ∨
       (∃ k, rhs = .FromExposed k r) ∨ (∃ k d ib, rhs = .PtrOffset k r d ib))
    {vals : List Val} {sA1 : oseair.State MSB}
    (he : evalRhs MSB ⟨pc, reg, mem, pA⟩ rhs = .Ok vals sA1) :
    Pending ⟨pc + 1, sA1.reg.insert x vals, sA1.mem, sA1.perms⟩ r n := by
  obtain ⟨base, off, ext, size, N0, hlr, pa⟩ := hP
  obtain ⟨base', off', ext', size', tag, len, A2, hl', hrd, hperm, -, hreg1, hmem1, hv⟩ :=
    evalRhs_through_inv pa.mem (Nat.ne_of_lt pa.pos) hrhs he
  rw [hlr] at hl'
  simp only [Option.some.injEq, List.cons.injEq, Val.Ptr.injEq, and_true] at hl'
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hl'
  obtain ⟨sm, rfl⟩ := sb_read_fields hrd
  have htop2 := fun j hj => sb_read_keeps_top hrd (Nat.ne_of_lt pa.pos).symm (pa.top j hj)
  rw [hreg1, hmem1]
  refine ⟨base, off, ext, size, N0, by rw [RegMap.lookup_insert_ne _ _ (Ne.symm hx)]; exact hlr, ?_⟩
  rcases hperm with hperm | ⟨t', ht', hperm⟩ <;> rw [hperm]
  · exact ⟨pa.pos, pa.notret, pa.notex, pa.notprot, htop2,
      RegsOK.insert pa.regs (hv.mono fun t h ht => absurd ht h), pa.mem⟩
  · refine ⟨pa.pos, pa.notret, ?_, pa.notprot, htop2,
      RegsOK.insert pa.regs (hv.mono fun t h ht => absurd ht h), pa.mem⟩
    show (t' :: pA.exposed).contains N0 = false
    simp only [List.contains_cons, Bool.or_eq_false_iff]
    exact ⟨by simpa using fun h => ht' h.symm, pa.notex⟩

/-- A store that is the bracket's access keeps it open; the stored values
    come from another register, or are literals without pointers. -/
theorem pend_store {pc : Nat} {reg : RegMap} {mem : bytes.Mem} {pA : AccessPerms}
    {r : Register} {n : Nat} (hP : Pending ⟨pc, reg, mem, pA⟩ r n)
    {lay : BLayout} {vals : List Val}
    (hsrc : (∃ s, s ≠ r ∧ reg.lookup s = some vals) ∨
      (∀ v ∈ vals, ∀ b o e s t, v ≠ .Ptr b o e s t))
    {base offset ext size tag : Nat} (hl : reg.lookup r = some [.Ptr base offset ext size tag])
    {A' : AccessPerms} (hw : sb_write pA (base + offset) lay.sizeB tag = .ok A')
    {mem' : bytes.Mem} (hwl : mirlite.writeL mem (base + offset) lay (vals.map Val.toMem) = .ok mem') :
    Pending ⟨pc + 1, reg, mem', A'⟩ r n := by
  obtain ⟨base', off', ext', size', N0, hlr, pa⟩ := hP
  rw [hlr] at hl
  simp only [Option.some.injEq, List.cons.injEq, Val.Ptr.injEq, and_true] at hl
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hl
  have hv : ValsOK (· ≠ N0) vals := by
    rcases hsrc with ⟨s, hs, hls⟩ | hnp
    · exact (pa.regs s vals hls).mono fun t h ht => hs (h ht)
    · intro v hv b o e s t he; exact absurd he (hnp v hv b o e s t)
  obtain ⟨sm, rfl⟩ := sb_write_fields hw
  refine ⟨base', off', ext', size', N0, hlr, pa.pos, pa.notret, pa.notex, pa.notprot,
    fun j hj => sb_write_keeps_top hw (Nat.ne_of_lt pa.pos).symm (pa.top j hj), pa.regs,
    pa.mem.writeL (Nat.ne_of_lt pa.pos) hv hwl⟩

/-! ## One step -/

theorem step_back {prog : oseair.Prog} (hp : RouteProg prog) {pc : Nat} {reg : RegMap}
    {mem : bytes.Mem} {pA pB : AccessPerms}
    (hI : Inv prog ⟨pc, reg, mem, pA⟩ ⟨pc, reg, mem, pB⟩) {sB' : oseair.State MSB_B}
    (h : step MSB_B ⟨pc, reg, mem, pB⟩ prog = .Ok sB') :
    ∃ sA', step MSB ⟨pc, reg, mem, pA⟩ prog = .Ok sA' ∧ Inv prog sA' sB' := by
  have hs : PermSub pA pB := hI.rel.2.2.2
  have hpi : PInv pA := hI.pinv
  have hm : MemOK (Good pA) mem := hI.mem
  have hregs : RegsOK (fun x t => t < pA.NextTag ∧ (t ∈ pA.retired → Dead prog pc x)) reg :=
    hI.regs
  have hpend := hI.pend
  -- the registers stay put; `pc` only grows
  have regs_mono : ∀ {pc' : Nat} {A' : AccessPerms}, pc ≤ pc' → pA.NextTag ≤ A'.NextTag →
      A'.retired = pA.retired →
      RegsOK (fun x t => t < A'.NextTag ∧ (t ∈ A'.retired → Dead prog pc' x)) reg :=
    fun hpc hn hr => hregs.mono fun x t h =>
      ⟨Nat.lt_of_lt_of_le h.1 hn, fun ht => (h.2 (hr ▸ ht)).mono hpc⟩
  simp only [step] at h ⊢
  split at h
  · cases h
    exact ⟨_, rfl, hI⟩
  rename_i instr hi
  have hgood := fun {y : Register} (hy : y ∈ instr.regs) =>
    Inv.good (sA := ⟨pc, reg, mem, pA⟩) hp hI hi hy
  cases instr with
  | Halt => cases h; exact ⟨_, rfl, hI⟩
  | Assgn x rhs =>
      try simp only at h ⊢
      split at h
      · rename_i vals sB1 he
        obtain ⟨sA1, hea, hpc1, hreg1, hpcB, hregB, hmem1, hbytes, hs1, hpi1, hret1, hnt1, hv⟩ :=
          evalRhs_back hs hpi hm (fun y hy => hgood (by simp [Instr.regs, hy])) he
        rw [hea]
        cases h
        refine ⟨_, rfl, ⟨⟨rfl, by simp only [hregB, hreg1], hmem1, hs1⟩, hpi1, ?_, ?_, ?_⟩⟩
        · exact (hm.of_bytes hbytes).mono fun t h => h.mono hret1 hnt1
        · simp only [hreg1]
          exact (regs_mono (Nat.le_succ pc) hnt1 hret1).insert
            (hv.mono fun t h => ⟨h.1, fun hr => absurd hr h.2⟩)
        · -- the brackets
          simp only [hreg1] at hea ⊢
          intro b r n hb hpc'
          by_cases hC : pc = b
          · -- the route borrow opens bracket `b`
            subst hC
            obtain ⟨k, base, off, hk, hkb⟩ := hb.borrow
            rw [hi] at hkb
            simp only [Option.some.injEq, Instr.Assgn.injEq] at hkb
            obtain ⟨rfl, rfl⟩ := hkb
            rcases hpc' with hpc' | hpc'
            · have := pend_borrow (r := x) hpi hm hregs hk hea
              rwa [hreg1] at this
            · exfalso; omega
          by_cases hD : pc = b + 1
          · -- the access keeps bracket `b` open
            subst hD
            obtain ⟨j, hj, hthr⟩ := hb.access
            rw [hi] at hj
            obtain rfl := Option.some.inj hj
            rcases Instr.through_cases hthr with ⟨x', rhs', he', hx, hrhs⟩ | ⟨_, _, he', -⟩ |
                ⟨_, _, he'⟩
            · simp only [Instr.Assgn.injEq] at he'
              obtain ⟨rfl, rfl⟩ := he'
              rcases hpc' with hpc' | hpc'
              · exfalso; omega
              · have := pend_access (hpend b r n hb (Or.inl rfl)) hx hrhs hea
                rwa [hreg1] at this
            · cases he'
            · cases he'
          · -- otherwise the next `pc` opens no bracket: `b` would open at `pc`
            exfalso
            rcases hpc' with hpc' | hpc'
            · exact hC (by omega)
            · exact hD (by omega)
      · cases h
  | RStore lay src ptr =>
      try simp only at h ⊢
      split at h
      · rename_i vals hl
        have hv : ValsOK (Good pA) vals := hgood (by simp [Instr.regs]) vals hl
        obtain ⟨sA', hwa, hpcA, hpcB, hregA, hregB, hmemB, hs', ⟨sm, hpm⟩, hm', hwr⟩ :=
          writeThroughPtr_back hs hpi hm (hgood (by simp [Instr.regs])) hv h
        refine ⟨sA', hwa, ⟨⟨by rw [hpcA, hpcB], by rw [hregA, hregB], hmemB, hs'⟩, ?_, ?_, ?_, ?_⟩⟩
        · rw [hpm]; exact hpi.of_sm sm
        · rw [hpm]; exact hm'
        · rw [hpm, hregA, hpcA]; exact regs_mono (Nat.le_succ pc) (Nat.le_refl _) rfl
        · intro b r n hb hpc'
          rw [hpcA] at hpc'
          by_cases hD : pc = b + 1
          · subst hD
            obtain ⟨j, hj, hthr⟩ := hb.access
            rw [hi] at hj
            obtain rfl := Option.some.inj hj
            rcases Instr.through_cases hthr with ⟨_, _, he', -⟩ | ⟨lay', s', he', hsr⟩ |
                ⟨_, _, he'⟩
            · cases he'
            · simp only [Instr.RStore.injEq] at he'
              obtain ⟨-, hs1, hp1⟩ := he'
              subst hs1 hp1
              rcases hpc' with hpc' | hpc'
              · exfalso; omega
              · obtain ⟨base, offset, ext, size, tag, hlp, hw, hwl⟩ := hwr
                have := pend_store (hpend b _ n hb (Or.inl rfl)) (Or.inl ⟨_, hsr, hl⟩) hlp hw hwl
                obtain ⟨pcA', regA', memA', permsA'⟩ := sA'
                simp only at hpcA hregA ⊢
                subst hpcA hregA
                exact this
            · cases he'
          · exfalso
            rcases hpc' with hpc' | hpc'
            · have hpcb : pc = b := by omega
              subst hpcb
              obtain ⟨k, base, off, -, hkb⟩ := hb.borrow
              rw [hi] at hkb; cases hkb
            · exact hD (by omega)
      · cases h
  | CStore lay vals ptr =>
      have hnp : ∀ v ∈ vals, ∀ b o e s t, v ≠ .Ptr b o e s t := hp.2 pc lay vals ptr hi
      have hv : ValsOK (Good pA) vals := fun v hv b o e s t he => absurd he (hnp v hv b o e s t)
      obtain ⟨sA', hwa, hpcA, hpcB, hregA, hregB, hmemB, hs', ⟨sm, hpm⟩, hm', hwr⟩ :=
        writeThroughPtr_back hs hpi hm (hgood (by simp [Instr.regs])) hv h
      refine ⟨sA', hwa, ⟨⟨by rw [hpcA, hpcB], by rw [hregA, hregB], hmemB, hs'⟩, ?_, ?_, ?_, ?_⟩⟩
      · rw [hpm]; exact hpi.of_sm sm
      · rw [hpm]; exact hm'
      · rw [hpm, hregA, hpcA]; exact regs_mono (Nat.le_succ pc) (Nat.le_refl _) rfl
      · intro b r n hb hpc'
        rw [hpcA] at hpc'
        by_cases hD : pc = b + 1
        · subst hD
          obtain ⟨j, hj, hthr⟩ := hb.access
          rw [hi] at hj
          obtain rfl := Option.some.inj hj
          rcases Instr.through_cases hthr with ⟨_, _, he', -⟩ | ⟨_, _, he', -⟩ | ⟨lay', vs', he'⟩
          · cases he'
          · cases he'
          · simp only [Instr.CStore.injEq] at he'
            obtain ⟨-, -, hp1⟩ := he'
            subst hp1
            rcases hpc' with hpc' | hpc'
            · exfalso; omega
            · obtain ⟨base, offset, ext, size, tag, hlp, hw, hwl⟩ := hwr
              have := pend_store (hpend b _ n hb (Or.inl rfl)) (Or.inr hnp) hlp hw hwl
              obtain ⟨pcA', regA', memA', permsA'⟩ := sA'
              simp only at hpcA hregA ⊢
              subst hpcA hregA
              exact this
        · exfalso
          rcases hpc' with hpc' | hpc'
          · have hpcb : pc = b := by omega
            subst hpcb
            obtain ⟨k, base, off, -, hkb⟩ := hb.borrow
            rw [hi] at hkb; cases hkb
          · exact hD (by omega)
  | Die r n =>
      obtain ⟨b, rfl, hb⟩ := hp.1 _ r n hi
      obtain ⟨base, off, ext, size, N0, hlr, pa⟩ := hpend b r n hb (Or.inr rfl)
      try simp only at h ⊢
      rw [hlr] at h ⊢
      try simp only at h ⊢
      split at h
      · rename_i pB2 hd
        have hd' : pB2 = pB := (Except.ok.inj hd).symm
        subst hd'
        cases h
        obtain ⟨A', hdie⟩ := sb_die_of_top pa.notex pa.notprot pa.top
        have hdie' : MSB.die pA (base + off) n N0 = .ok A' := hdie
        rw [hdie']
        refine ⟨_, rfl, ⟨⟨rfl, rfl, rfl, sb_die_sub hs hdie⟩, ?_, ?_, ?_, ?_⟩⟩
        · obtain ⟨sm, rfl⟩ := sb_die_fields hdie
          have hN0 : N0 < pA.NextTag :=
            (hregs r _ hlr _ List.mem_cons_self _ _ _ _ _ rfl).1
          refine ⟨hpi.pos, fun t ht => ?_, hpi.exb, hpi.prot⟩
          rcases List.mem_cons.mp ht with rfl | ht
          · exact ⟨pa.pos, hN0⟩
          · exact hpi.ret t ht
        · obtain ⟨sm, rfl⟩ := sb_die_fields hdie
          exact (hm.and pa.mem).mono fun t h => ⟨h.1.1, fun ht => by
            rcases List.mem_cons.mp ht with rfl | ht
            · exact h.2 rfl
            · exact h.1.2 ht⟩
        · obtain ⟨sm, rfl⟩ := sb_die_fields hdie
          refine (hregs.and pa.regs).mono fun x t h => ⟨h.1.1, fun ht => ?_⟩
          rcases List.mem_cons.mp ht with rfl | ht
          · obtain rfl := h.2 rfl
            exact ⟨b + 2, n, hi, Nat.lt_succ_self _⟩
          · exact (h.1.2 ht).mono (Nat.le_succ _)
        · intro b' r' n' hb' hpc'
          exfalso
          simp only at hpc'
          rcases hpc' with hpc' | hpc'
          · -- `b' + 1 = b + 3`: `b'` would be a borrow, but it is the `Die`
            have : b' = b + 2 := by omega
            subst this
            obtain ⟨k, base', off', -, hkb⟩ := hb'.borrow
            rw [hi] at hkb; cases hkb
          · -- `b' + 2 = b + 3`: the `Die` would be `b'`'s access
            have : b' = b + 1 := by omega
            subst this
            obtain ⟨j, hj, hthr⟩ := hb'.access
            rw [hi] at hj
            obtain rfl := Option.some.inj hj
            simp [Instr.through] at hthr
      · cases h
  | Dealloc ptr =>
      try simp only at h ⊢
      split at h
      · rename_i base offset ext size tag hl
        split at h
        · cases h
        rename_i ho
        rw [if_neg ho]
        split at h
        · rename_i pB2 hd
          have ht : tag ∉ pA.retired :=
            (hgood (by simp [Instr.regs]) _ hl _ List.mem_cons_self _ _ _ _ _ rfl).2
          obtain ⟨A', hda, hs'⟩ := sb_dealloc_back size base hs ht hd
          have hda' : MSB.dealloc pA base size tag = .ok A' := hda
          rw [hda']
          cases h
          obtain ⟨sm, rfl⟩ := sb_dealloc_fields size base hda
          refine ⟨_, rfl, ⟨⟨rfl, rfl, rfl, hs'⟩, hpi.of_sm sm, ?_, ?_, ?_⟩⟩
          · exact (hm.write_uninit base size).of_bytes rfl
          · exact regs_mono (Nat.le_succ pc) (Nat.le_refl _) rfl
          · exact pend_vacuous (NotInBracket.of_shape hi (fun _ _ h => by cases h)
              (fun _ => rfl))
        · cases h
      · cases h
  | Check discr vals member =>
      try simp only at h ⊢
      split at h
      · rename_i v hl
        split at h
        · rename_i hv
          rw [if_pos hv]
          cases h
          exact ⟨_, rfl, ⟨⟨rfl, rfl, rfl, hs⟩, hpi, hm,
            regs_mono (Nat.le_succ pc) (Nat.le_refl _) rfl,
            pend_vacuous (NotInBracket.of_shape hi (fun _ _ h => by cases h) (fun _ => rfl))⟩⟩
        · cases h
      · cases h
  | PushProt =>
      cases h
      refine ⟨_, rfl, ⟨⟨rfl, rfl, rfl, hs.pushFrame⟩, ?_, hm,
        regs_mono (Nat.le_succ pc) (Nat.le_refl _) rfl,
        pend_vacuous (NotInBracket.of_shape hi (fun _ _ h => by cases h) (fun _ => rfl))⟩⟩
      refine ⟨hpi.pos, hpi.ret, hpi.exb, fun t ht => hpi.prot t ?_⟩
      simpa [MSB, PermissionModel.stackedBorrows, sb_push_frame, isProtectedIn] using ht
  | PopProt =>
      try simp only at h ⊢
      split at h
      · rename_i pB2 hpop
        obtain ⟨A', hpa, hs'⟩ := hs.popFrame_back hpop
        have hpa' : MSB.popFrame pA = .ok A' := hpa
        rw [hpa']
        cases h
        refine ⟨_, rfl, ⟨⟨rfl, rfl, rfl, hs'⟩, ?_, ?_, ?_,
          pend_vacuous (NotInBracket.of_shape hi (fun _ _ h => by cases h) (fun _ => rfl))⟩⟩
        all_goals
          unfold sb_pop_frame at hpa
          split at hpa
          · cases hpa
          rename_i f rest hpf
          cases hpa
        · refine ⟨hpi.pos, hpi.ret, hpi.exb, fun t ht => hpi.prot t ?_⟩
          rw [hpf]
          simp only [isProtectedIn, List.any_cons] at ht ⊢
          rw [ht, Bool.or_true]
        · exact hm
        · exact regs_mono (Nat.le_succ pc) (Nat.le_refl _) rfl
      · cases h

/-! ## Runs -/

theorem runN_back {prog : oseair.Prog} (hp : RouteProg prog) :
    ∀ (n : Nat) {sA : oseair.State MSB} {sB sB' : oseair.State MSB_B},
      Inv prog sA sB → runN MSB_B n sB prog = .Ok sB' →
      ∃ sA', runN MSB n sA prog = .Ok sA' ∧ Inv prog sA' sB'
  | 0, _, _, _, hI, h => by cases h; exact ⟨_, rfl, hI⟩
  | n + 1, sA, sB, sB', hI, h => by
      obtain ⟨pc, reg, mem, pA⟩ := sA
      obtain ⟨pcB, regB, memB, pB⟩ := sB
      have hrel := hI.rel
      obtain ⟨h1, h2, h3, -⟩ := hrel
      simp only at h1 h2 h3
      subst h1 h2 h3
      simp only [runN] at h ⊢
      split at h
      · rename_i sB1 hst
        obtain ⟨sA1, hsta, hI1⟩ := step_back hp hI hst
        rw [hsta]
        exact runN_back hp n hI1 h
      · cases h

/-- Die elision, backward: for a program whose `Die`s all close route
    brackets, a run that succeeds on OSEA-IR_B succeeds on OSEA-IR, in the
    same number of steps, ending at the same pc with the same registers
    and memory. -/
theorem die_elision_back (prog : oseair.Prog) (hp : RouteProg prog) (n : Nat)
    {s'' : oseair.State MSB_B}
    (h : runN MSB_B n (oseair.State.initial MSB_B) prog = .Ok s'') :
    ∃ s' : oseair.State MSB, runN MSB n (oseair.State.initial MSB) prog = .Ok s' ∧
      s'.pc = s''.pc ∧ s'.reg = s''.reg ∧ s'.mem = s''.mem := by
  obtain ⟨s', h', hI⟩ := runN_back hp n (Inv.initial prog) h
  obtain ⟨h1, h2, h3, -⟩ := hI.rel
  exact ⟨s', h', h1.symm, h2.symm, h3.symm⟩

/-- For route-bracket programs, OSEA-IR and OSEA-IR_B reach the same
    verdict at every step count. -/
theorem die_elision_iff (prog : oseair.Prog) (hp : RouteProg prog) (n : Nat) :
    (∃ s, runN MSB n (oseair.State.initial MSB) prog = .Ok s) ↔
      (∃ s, runN MSB_B n (oseair.State.initial MSB_B) prog = .Ok s) :=
  ⟨fun ⟨_, h⟩ => let ⟨s'', h'', _⟩ := die_elision prog n h; ⟨s'', h''⟩,
   fun ⟨_, h⟩ => let ⟨s', h', _⟩ := die_elision_back prog hp n h; ⟨s', h'⟩⟩

end obseq3.proof


