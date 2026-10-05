import obseq3.proof.permsub
import obseq3.oseair

/-!
# Die elision: OSEA-IR → OSEA-IR_B

OSEA-IR_B is OSEA-IR with `Die` a no-op (`MSB_B`, the permission model
`stackedBorrowsNoDie`). Removing every `Die` never makes a valid program
invalid: a run of `n` steps that succeeds on OSEA-IR succeeds on OSEA-IR_B
in lockstep, with the same pc, registers and memory (`die_elision`).

The machine half is model-generic: if every operation of a permission
model `M1` that succeeds is matched by `M2`'s with the same result tag and
related states (`ModelSim`), then `M2` simulates `M1` step for step
(`runN_msim`). The machine never inspects a permission state, only whether
an operation succeeded and which tag it returned. The SB half is
`permsub.lean`: `PermSub` is such a relation from `MSB` to `MSB_B`.
-/

namespace obseq3.proof

open obseq3 obseq3.bytes obseq3.oseair

/-- OSEA-IR_B's permission model. -/
abbrev MSB_B : PermissionModel := PermissionModel.stackedBorrowsNoDie

/-- `M2` forward-simulates `M1` along `R`, operation by operation. -/
structure ModelSim (M1 M2 : PermissionModel) (R : M1.State → M2.State → Prop) : Prop where
  init : R M1.init M2.init
  own : ∀ {s1 s2 a n s1' t}, R s1 s2 → M1.own s1 a n = .ok (s1', t) →
    ∃ s2', M2.own s2 a n = .ok (s2', t) ∧ R s1' s2'
  read : ∀ {s1 s2 a n t s1'}, R s1 s2 → M1.read s1 a n t = .ok s1' →
    ∃ s2', M2.read s2 a n t = .ok s2' ∧ R s1' s2'
  useMut : ∀ {s1 s2 a n t s1'}, R s1 s2 → M1.useMut s1 a n t = .ok s1' →
    ∃ s2', M2.useMut s2 a n t = .ok s2' ∧ R s1' s2'
  ref : ∀ {s1 s2 a n t kind prot mask s1' t'}, R s1 s2 →
    M1.ref s1 a n t kind prot mask = .ok (s1', t') →
    ∃ s2', M2.ref s2 a n t kind prot mask = .ok (s2', t') ∧ R s1' s2'
  die : ∀ {s1 s2 a n t s1'}, R s1 s2 → M1.die s1 a n t = .ok s1' →
    ∃ s2', M2.die s2 a n t = .ok s2' ∧ R s1' s2'
  dealloc : ∀ {s1 s2 a n t s1'}, R s1 s2 → M1.dealloc s1 a n t = .ok s1' →
    ∃ s2', M2.dealloc s2 a n t = .ok s2' ∧ R s1' s2'
  expose : ∀ {s1 s2 t s1'}, R s1 s2 → M1.expose s1 t = .ok s1' →
    ∃ s2', M2.expose s2 t = .ok s2' ∧ R s1' s2'
  pushFrame : ∀ {s1 s2}, R s1 s2 → R (M1.pushFrame s1) (M2.pushFrame s2)
  popFrame : ∀ {s1 s2 s1'}, R s1 s2 → M1.popFrame s1 = .ok s1' →
    ∃ s2', M2.popFrame s2 = .ok s2' ∧ R s1' s2'

/-- Machine states agree except for the permission state, which is
    `R`-related. -/
def StateRel {M1 M2 : PermissionModel} (R : M1.State → M2.State → Prop)
    (s1 : oseair.State M1) (s2 : oseair.State M2) : Prop :=
  s2.pc = s1.pc ∧ s2.reg = s1.reg ∧ s2.mem = s1.mem ∧ R s1.perms s2.perms

section generic

variable {M1 M2 : PermissionModel} {R : M1.State → M2.State → Prop}

theorem allocPtr_msim (hM : ModelSim M1 M2 R) {s1 : oseair.State M1} {s2 : oseair.State M2}
    (hs : StateRel R s1 s2) {sizeB alignB : Nat} {vals : List Val} {s1' : oseair.State M1}
    (h : allocPtr M1 s1 sizeB alignB = .Ok vals s1') :
    ∃ s2', allocPtr M2 s2 sizeB alignB = .Ok vals s2' ∧ StateRel R s1' s2' := by
  obtain ⟨pc1, reg1, mem1, p1⟩ := s1
  obtain ⟨pc2, reg2, mem2, p2⟩ := s2
  obtain ⟨h1, h2, h3, hp⟩ := hs
  simp only at h1 h2 h3 hp
  subst h1 h2 h3
  simp only [allocPtr] at h ⊢
  split at h
  · rename_i p1' t ho
    obtain ⟨p2', ho2, hp'⟩ := hM.own hp ho
    rw [ho2]
    cases h
    exact ⟨_, rfl, rfl, rfl, rfl, hp'⟩
  · cases h

theorem readCellThrough_msim (hM : ModelSim M1 M2 R) {s1 : oseair.State M1}
    {s2 : oseair.State M2} (hs : StateRel R s1 s2) {reg : Register} {k : Scalar}
    {v : Val} {p1' : M1.State}
    (h : readCellThrough M1 s1 reg k = .ok (v, p1')) :
    ∃ p2', readCellThrough M2 s2 reg k = .ok (v, p2') ∧ R p1' p2' := by
  obtain ⟨pc1, reg1, mem1, p1⟩ := s1
  obtain ⟨pc2, reg2, mem2, p2⟩ := s2
  obtain ⟨h1, h2, h3, hp⟩ := hs
  simp only at h1 h2 h3 hp
  subst h1 h2 h3
  simp only [readCellThrough] at h ⊢
  split at h
  · split at h
    · cases h
    rename_i hf
    rw [if_neg hf]
    split at h
    · cases h
    rename_i hb
    rw [if_neg hb]
    split at h
    · cases h
    rename_i p1'' hr
    obtain ⟨p2', hr2, hp'⟩ := hM.read hp hr
    rw [hr2]
    cases h
    exact ⟨_, rfl, hp'⟩
  · cases h

theorem evalRhs_msim (hM : ModelSim M1 M2 R) {s1 : oseair.State M1} {s2 : oseair.State M2}
    (hs : StateRel R s1 s2) (rhs : Rhs) {vals : List Val} {s1' : oseair.State M1}
    (h : evalRhs M1 s1 rhs = .Ok vals s1') :
    ∃ s2', evalRhs M2 s2 rhs = .Ok vals s2' ∧ StateRel R s1' s2' := by
  have hs0 := hs
  obtain ⟨pc1, reg1, mem1, p1⟩ := s1
  obtain ⟨pc2, reg2, mem2, p2⟩ := s2
  obtain ⟨h1, h2, h3, hp⟩ := hs
  simp only at h1 h2 h3 hp
  subst h1 h2 h3
  cases rhs with
  | Load lay reg =>
      simp only [evalRhs] at h ⊢
      split at h
      · split at h
        · cases h
        split at h
        · cases h
        split at h
        · rename_i p1' hr
          obtain ⟨p2', hr2, hp'⟩ := hM.read hp hr
          rw [hr2]
          split at h
          · cases h
          · cases h
            simp only [*]
            exact ⟨_, rfl, rfl, rfl, rfl, hp'⟩
        · cases h
      · cases h
  | Alloc lay => exact allocPtr_msim hM hs0 h
  | AllocN lay n => exact allocPtr_msim hM hs0 h
  | AllocDyn lay lenReg =>
      simp only [evalRhs] at h ⊢
      split at h
      · rename_i n hl
        exact allocPtr_msim hM hs0 h
      · cases h
  | ExposeAddr k srcPtr =>
      simp only [evalRhs] at h ⊢
      split at h
      · cases h
      · rename_i pBase pOff pExt pSize pTag p1' hr
        obtain ⟨p2', hr2, hp'⟩ := readCellThrough_msim hM hs0 hr
        rw [hr2]
        simp only
        split at h
        · rename_i p1'' he
          obtain ⟨p2'', he2, hp''⟩ := hM.expose hp' he
          rw [he2]
          cases h
          exact ⟨_, rfl, rfl, rfl, rfl, hp''⟩
        · cases h
      · cases h
  | FromExposed k srcPtr =>
      simp only [evalRhs] at h ⊢
      split at h
      · cases h
      · rename_i n p1' hr
        obtain ⟨p2', hr2, hp'⟩ := readCellThrough_msim hM hs0 hr
        rw [hr2]
        cases h
        exact ⟨_, rfl, rfl, rfl, rfl, hp'⟩
      · cases h
  | PtrOffset k srcPtr deltaB inbounds =>
      simp only [evalRhs] at h ⊢
      split at h
      · cases h
      · rename_i pBase pOff pExt pSize pTag p1' hr
        obtain ⟨p2', hr2, hp'⟩ := readCellThrough_msim hM hs0 hr
        rw [hr2]
        simp only
        split at h
        · cases h
        · cases h
          exact ⟨_, rfl, rfl, rfl, rfl, hp'⟩
      · cases h
  | Borrow kind prot mask lenB base offsetB =>
      simp only [evalRhs] at h ⊢
      split at h
      · cases lenB with
        | some n =>
            simp only at h ⊢
            split at h
            · cases h
            rename_i hf
            rw [if_neg hf]
            split at h
            · cases h
            rename_i hb
            rw [if_neg hb]
            split at h
            · rename_i p1' t' hr
              obtain ⟨p2', hr2, hp'⟩ := hM.ref hp hr
              rw [hr2]
              cases h
              exact ⟨_, rfl, rfl, rfl, rfl, hp'⟩
            · cases h
        | none =>
            simp only at h ⊢
            split at h
            · cases h
            rename_i hf
            rw [if_neg hf]
            split at h
            · rename_i p1' t' hr
              obtain ⟨p2', hr2, hp'⟩ := hM.ref hp hr
              rw [hr2]
              cases h
              exact ⟨_, rfl, rfl, rfl, rfl, hp'⟩
            · cases h
      · cases h
  | BinOp op r1 r2 | PlaceAddr r offB extB | SliceLen esz r | SubSlice esz rp rLo rHi
  | PtrOffsetBy t esz rp ri inbounds =>
      -- no permission event: the state passes through
      simp only [evalRhs] at h ⊢
      repeat' split at h
      all_goals (cases h <;> (try rw [if_neg ‹_›]) <;> exact ⟨_, rfl, rfl, rfl, rfl, hp⟩)

theorem writeThroughPtr_msim (hM : ModelSim M1 M2 R) {s1 : oseair.State M1}
    {s2 : oseair.State M2} (hs : StateRel R s1 s2) {ptr : Register} {lay : BLayout}
    {vals : List Val} {msg : String} {s1' : oseair.State M1}
    (h : writeThroughPtr M1 s1 ptr lay vals msg = .Ok s1') :
    ∃ s2', writeThroughPtr M2 s2 ptr lay vals msg = .Ok s2' ∧ StateRel R s1' s2' := by
  obtain ⟨pc1, reg1, mem1, p1⟩ := s1
  obtain ⟨pc2, reg2, mem2, p2⟩ := s2
  obtain ⟨h1, h2, h3, hp⟩ := hs
  simp only at h1 h2 h3 hp
  subst h1 h2 h3
  simp only [writeThroughPtr] at h ⊢
  split at h
  · split at h
    · cases h
    split at h
    · cases h
    split at h
    · rename_i p1' hr
      obtain ⟨p2', hr2, hp'⟩ := hM.useMut hp hr
      rw [hr2]
      simp only
      split at h
      · cases h
        simp only [*]
        exact ⟨_, rfl, rfl, rfl, rfl, hp'⟩
      · cases h
    · cases h
  · cases h

theorem step_msim (hM : ModelSim M1 M2 R) {s1 : oseair.State M1} {s2 : oseair.State M2}
    (hs : StateRel R s1 s2) (prog : oseair.Prog) {s1' : oseair.State M1}
    (h : step M1 s1 prog = .Ok s1') :
    ∃ s2', step M2 s2 prog = .Ok s2' ∧ StateRel R s1' s2' := by
  have hs0 := hs
  obtain ⟨pc1, reg1, mem1, p1⟩ := s1
  obtain ⟨pc2, reg2, mem2, p2⟩ := s2
  obtain ⟨h1, h2, h3, hp⟩ := hs
  simp only at h1 h2 h3 hp
  subst h1 h2 h3
  simp only [step] at h ⊢
  split at h
  · cases h; exact ⟨_, rfl, hs0⟩
  rename_i instr hi
  cases instr with
  | Halt => cases h; exact ⟨_, rfl, hs0⟩
  | Assgn reg rhs =>
      try simp only at h ⊢
      split at h
      · rename_i vals s1x he
        obtain ⟨s2x, he2, hx⟩ := evalRhs_msim hM hs0 rhs he
        rw [he2]
        cases h
        obtain ⟨hx1, hx2, hx3, hx4⟩ := hx
        exact ⟨_, rfl, rfl, by simp only [hx2], hx3, hx4⟩
      · cases h
  | RStore lay src ptr =>
      try simp only at h ⊢
      split at h
      · rename_i vals hl
        exact writeThroughPtr_msim hM hs0 h
      · cases h
  | CStore lay vals ptr => exact writeThroughPtr_msim hM hs0 h
  | Die reg lenB =>
      try simp only at h ⊢
      split at h
      · rename_i b o e s t hl
        try simp only
        split at h
        · rename_i p1' hd
          obtain ⟨p2', hd2, hp'⟩ := hM.die hp hd
          rw [hd2]
          cases h
          exact ⟨_, rfl, rfl, rfl, rfl, hp'⟩
        · cases h
      · cases h
  | Dealloc ptr =>
      try simp only at h ⊢
      split at h
      · rename_i b o e sz t hl
        try simp only
        split at h
        · cases h
        rename_i ho
        rw [if_neg ho]
        split at h
        · rename_i p1' hd
          obtain ⟨p2', hd2, hp'⟩ := hM.dealloc hp hd
          rw [hd2]
          cases h
          exact ⟨_, rfl, rfl, rfl, rfl, hp'⟩
        · cases h
      · cases h
  | SkipIf discr val skip =>
      try simp only at h ⊢
      split at h
      · rename_i v hl
        try simp only
        split at h
        · rename_i hv
          rw [if_pos hv]
          cases h
          exact ⟨_, rfl, rfl, rfl, rfl, hp⟩
        · rename_i hv
          rw [if_neg hv]
          cases h
          exact ⟨_, rfl, rfl, rfl, rfl, hp⟩
      · cases h
  | PushProt =>
      cases h
      exact ⟨_, rfl, rfl, rfl, rfl, hM.pushFrame hp⟩
  | PopProt =>
      try simp only at h ⊢
      split at h
      · rename_i p1' hd
        obtain ⟨p2', hd2, hp'⟩ := hM.popFrame hp hd
        rw [hd2]
        cases h
        exact ⟨_, rfl, rfl, rfl, rfl, hp'⟩
      · cases h

/-- Lockstep: `M2` runs every successful `M1` run, step for step. -/
theorem runN_msim (hM : ModelSim M1 M2 R) (prog : oseair.Prog) :
    ∀ (n : Nat) {s1 : oseair.State M1} {s2 : oseair.State M2} {s1' : oseair.State M1},
      StateRel R s1 s2 → runN M1 n s1 prog = .Ok s1' →
      ∃ s2', runN M2 n s2 prog = .Ok s2' ∧ StateRel R s1' s2'
  | 0, _, _, _, hs, h => by cases h; exact ⟨_, rfl, hs⟩
  | n + 1, s1, s2, s1', hs, h => by
      simp only [runN] at h ⊢
      split at h
      · rename_i s1x hst
        obtain ⟨s2x, hst2, hx⟩ := step_msim hM hs prog hst
        rw [hst2]
        exact runN_msim hM prog n hx h
      · cases h

end generic

/-! ## Stacked Borrows without `Die` simulates Stacked Borrows -/

theorem modelSim_noDie : ModelSim MSB MSB_B (fun a b => PermSub a b) where
  init := PermSub.initial
  own hs h := sb_own_sub hs h
  read hs h := sb_read_sub hs h
  useMut hs h := sb_write_sub hs h
  ref hs h := sb_ref_sub hs h
  die hs h := ⟨_, rfl, sb_die_sub hs h⟩
  dealloc hs h := sb_dealloc_sub _ _ hs h
  expose hs h := sb_expose_sub hs h
  pushFrame hs := hs.pushFrame
  popFrame hs h := hs.popFrame h

/-- Die elision: a run that succeeds on OSEA-IR succeeds on OSEA-IR_B (the
    same program with every `Die` a no-op), in the same number of steps,
    ending at the same pc with the same registers and memory. -/
theorem die_elision (prog : oseair.Prog) (n : Nat) {s' : oseair.State MSB}
    (h : runN MSB n (oseair.State.initial MSB) prog = .Ok s') :
    ∃ s'' : oseair.State MSB_B, runN MSB_B n (oseair.State.initial MSB_B) prog = .Ok s'' ∧
      s''.pc = s'.pc ∧ s''.reg = s'.reg ∧ s''.mem = s'.mem := by
  obtain ⟨s'', h'', h1, h2, h3, -⟩ := runN_msim modelSim_noDie prog n
    (s2 := oseair.State.initial MSB_B) ⟨rfl, rfl, rfl, modelSim_noDie.init⟩ h
  exact ⟨s'', h'', h1, h2, h3⟩

end obseq3.proof
