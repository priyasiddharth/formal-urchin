import obseq3.proof.die_back

/-!
# Die elision, backward: one machine operation

A successful OSEA-IR_B rvalue or store, from related states whose live
registers hold no retired tag, is matched by OSEA-IR's, with the
invariant's bounds kept (`evalRhs_back`, `writeThroughPtr_back`).
-/

namespace obseq3.proof

open obseq3 obseq3.bytes obseq3.oseair

theorem Good.mono {A A' : AccessPerms} {t : Tag} (h : Good A t)
    (hr : A'.retired = A.retired) (hn : A.NextTag ≤ A'.NextTag) : Good A' t :=
  ⟨Nat.lt_of_lt_of_le h.1 hn, by rw [hr]; exact h.2⟩

theorem PInv.of_sm {A : AccessPerms} (h : PInv A) (sm : SB) :
    PInv { A with StackMap := sm } := ⟨h.pos, h.ret, h.exb, h.prot⟩

theorem PInv.of_own {A : AccessPerms} (h : PInv A) (sm : SB) :
    PInv { A with StackMap := sm, NextTag := A.NextTag + 1 } :=
  ⟨Nat.succ_pos _, fun t ht => ⟨(h.ret t ht).1, Nat.lt_succ_of_lt (h.ret t ht).2⟩,
   fun t ht => Nat.lt_succ_of_lt (h.exb t ht),
   fun t ht => Nat.lt_succ_of_lt (h.prot t ht)⟩

theorem PInv.of_ref {A A' : AccessPerms} {addr : Word} {lenB : Nat} {t : Tag}
    {kind : RefKind} {prot : Bool} {mask : List Bool} {n : Tag} (h : PInv A)
    (hr : sb_ref A addr lenB t kind prot mask = .ok (A', n)) : PInv A' := by
  obtain ⟨-, hn, hret, hex, hp, -⟩ := sb_ref_fields hr
  refine ⟨by rw [hn]; exact Nat.succ_pos _, fun u hu => ?_, fun u hu => ?_, fun u hu => ?_⟩
  · rw [hret] at hu; rw [hn]; exact ⟨(h.ret u hu).1, Nat.lt_succ_of_lt (h.ret u hu).2⟩
  · rw [hex] at hu; rw [hn]; exact Nat.lt_succ_of_lt (h.exb u hu)
  · rw [hn]
    rcases hp u hu with rfl | hu'
    · exact Nat.lt_succ_self _
    · exact Nat.lt_succ_of_lt (h.prot u hu')

/-- The register's tags are good: an access through it is `ActOK`. -/
theorem actOK_of {A : AccessPerms} {reg : RegMap} {r : Register}
    (hr : ∀ vs, reg.lookup r = some vs → ValsOK (Good A) vs)
    {b o e s t : Nat} {rest : List Val} (hl : reg.lookup r = some (.Ptr b o e s t :: rest)) :
    ActOK A t :=
  fun _ => (hr _ hl _ List.mem_cons_self _ _ _ _ _ rfl).2

theorem readCellThrough_back {pc : Nat} {reg : RegMap} {mem : bytes.Mem} {pA pB : AccessPerms}
    (hs : PermSub pA pB) (hm : MemOK (Good pA) mem) (hw : Good pA wildcardTag)
    {r : Register} {k : Scalar}
    (hr : ∀ vs, reg.lookup r = some vs → ValsOK (Good pA) vs)
    {v : Val} {pB' : AccessPerms}
    (h : readCellThrough MSB_B ⟨pc, reg, mem, pB⟩ r k = .ok (v, pB')) :
    ∃ pA', readCellThrough MSB ⟨pc, reg, mem, pA⟩ r k = .ok (v, pA') ∧ PermSub pA' pB' ∧
      (∃ sm, pA' = { pA with StackMap := sm }) ∧ ValsOK (Good pA) [v] := by
  simp only [readCellThrough] at h ⊢
  split at h
  · rename_i base offset ext size tag hl
    split at h
    · cases h
    rename_i hf
    rw [if_neg hf]
    split at h
    · cases h
    rename_i hb
    rw [if_neg hb]
    split at h
    · cases h
    rename_i pB2 hrd
    obtain ⟨pA2, hra, hs2⟩ := sb_read_back hs (actOK_of hr hl) hrd
    have hra' : MSB.read pA (base + offset) k.sizeB tag = .ok pA2 := hra
    rw [hra']
    cases h
    exact ⟨pA2, rfl, hs2, sb_read_fields hra, hm.decodeV hw k _ _⟩
  · cases h

theorem allocPtr_back {pc : Nat} {reg : RegMap} {mem : bytes.Mem} {pA pB : AccessPerms}
    (hs : PermSub pA pB) (hpi : PInv pA) {sizeB alignB : Nat}
    {vals : List Val} {sB1 : oseair.State MSB_B}
    (h : allocPtr MSB_B ⟨pc, reg, mem, pB⟩ sizeB alignB = .Ok vals sB1) :
    ∃ sA1 : oseair.State MSB, allocPtr MSB ⟨pc, reg, mem, pA⟩ sizeB alignB = .Ok vals sA1 ∧
      sA1.pc = pc ∧ sA1.reg = reg ∧ sB1.pc = pc ∧ sB1.reg = reg ∧ sB1.mem = sA1.mem ∧
      sA1.mem.bytes = mem.bytes ∧ PermSub sA1.perms sB1.perms ∧ PInv sA1.perms ∧
      sA1.perms.retired = pA.retired ∧ pA.NextTag ≤ sA1.perms.NextTag ∧
      ValsOK (Good sA1.perms) vals := by
  simp only [allocPtr] at h ⊢
  split at h
  · rename_i pB2 tag ho
    obtain ⟨pA2, hoa, hs2⟩ := sb_own_back hs ho
    have hoa' : MSB.own pA (mem.allocate sizeB (max 1 alignB)).1 sizeB = .ok (pA2, tag) := hoa
    rw [hoa']
    cases h
    obtain ⟨rfl, sm, rfl⟩ := sb_own_fields hoa
    refine ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hs2, hpi.of_own sm, rfl, Nat.le_succ _, ?_⟩
    exact ValsOK.ptr ⟨Nat.lt_succ_self _, fun hr => Nat.lt_irrefl _ (hpi.ret _ hr).2⟩
  · cases h

/-- The bundle an rvalue's matched A-step comes with. -/
def RhsOut (pc : Nat) (reg : RegMap) (mem : bytes.Mem) (pA : AccessPerms) (vals : List Val)
    (sA1 : oseair.State MSB) (sB1 : oseair.State MSB_B) : Prop :=
  sA1.pc = pc ∧ sA1.reg = reg ∧ sB1.pc = pc ∧ sB1.reg = reg ∧ sB1.mem = sA1.mem ∧
    sA1.mem.bytes = mem.bytes ∧ PermSub sA1.perms sB1.perms ∧ PInv sA1.perms ∧
    sA1.perms.retired = pA.retired ∧ pA.NextTag ≤ sA1.perms.NextTag ∧
    ValsOK (Good sA1.perms) vals

theorem evalRhs_back {pc : Nat} {reg : RegMap} {mem : bytes.Mem} {pA pB : AccessPerms}
    (hs : PermSub pA pB) (hpi : PInv pA) (hm : MemOK (Good pA) mem) {rhs : Rhs}
    (hr : ∀ y ∈ rhs.regs, ∀ vs, reg.lookup y = some vs → ValsOK (Good pA) vs)
    {vals : List Val} {sB1 : oseair.State MSB_B}
    (h : evalRhs MSB_B ⟨pc, reg, mem, pB⟩ rhs = .Ok vals sB1) :
    ∃ sA1 : oseair.State MSB, evalRhs MSB ⟨pc, reg, mem, pA⟩ rhs = .Ok vals sA1 ∧
      RhsOut pc reg mem pA vals sA1 sB1 := by
  have hw := hpi.good_wild
  -- the state passes through untouched
  have same : ∀ (vs : List Val), ValsOK (Good pA) vs →
      RhsOut pc reg mem pA vs ⟨pc, reg, mem, pA⟩ ⟨pc, reg, mem, pB⟩ :=
    fun vs hv => ⟨rfl, rfl, rfl, rfl, rfl, rfl, hs, hpi, rfl, Nat.le_refl _, hv⟩
  cases rhs with
  | Load lay r =>
      have hr' := hr r (by simp [Rhs.regs])
      simp only [evalRhs] at h ⊢
      split at h
      · rename_i base offset ext size tag hl
        split at h
        · cases h
        rename_i hf
        rw [if_neg hf]
        split at h
        · cases h
        rename_i hb
        rw [if_neg hb]
        split at h
        · rename_i pB2 hrd
          obtain ⟨pA2, hra, hs2⟩ := sb_read_back hs (actOK_of hr' hl) hrd
          have hra' : MSB.read pA (base + offset) lay.sizeB tag = .ok pA2 := hra
          rw [hra']
          simp only
          split at h
          · cases h
          rename_i hu
          rw [if_neg hu]
          cases h
          obtain ⟨sm, rfl⟩ := sb_read_fields hra
          exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hs2, hpi.of_sm sm, rfl, Nat.le_refl _,
            hm.readL hw _ lay⟩
        · cases h
      · cases h
  | Alloc lay => exact allocPtr_back hs hpi h
  | AllocN lay n => exact allocPtr_back hs hpi h
  | AllocDyn lay lenReg =>
      simp only [evalRhs] at h ⊢
      split at h
      · exact allocPtr_back hs hpi h
      · cases h
  | ExposeAddr k p =>
      simp only [evalRhs] at h ⊢
      split at h
      · cases h
      · rename_i pBase pOff pExt pSize pTag pB2 hrc
        obtain ⟨pA2, hra, hs2, ⟨sm, rfl⟩, hv⟩ :=
          readCellThrough_back hs hm hw (hr p (by simp [Rhs.regs])) hrc
        rw [hra]
        simp only
        split at h
        · rename_i pB3 he
          have hgood := hv _ List.mem_cons_self _ _ _ _ _ rfl
          obtain ⟨pA3, hea, hs3⟩ := sb_expose_back hs2 (fun _ => hgood.2) he
          have hea' : MSB.expose { pA with StackMap := sm } pTag = .ok pA3 := hea
          rw [hea']
          cases h
          refine ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hs3, ?_, ?_, ?_, ValsOK.dat _ _⟩
          · rcases sb_expose_fields hea with rfl | rfl
            · exact hpi.of_sm sm
            · refine ⟨hpi.pos, hpi.ret, fun u hu => ?_, hpi.prot⟩
              rcases List.mem_cons.mp hu with rfl | hu
              · exact hgood.1
              · exact hpi.exb u hu
          · rcases sb_expose_fields hea with rfl | rfl <;> rfl
          · rcases sb_expose_fields hea with rfl | rfl <;> exact Nat.le_refl _
        · cases h
      · cases h
  | FromExposed k p =>
      simp only [evalRhs] at h ⊢
      split at h
      · cases h
      · rename_i n pB2 hrc
        obtain ⟨pA2, hra, hs2, ⟨sm, rfl⟩, -⟩ :=
          readCellThrough_back hs hm hw (hr p (by simp [Rhs.regs])) hrc
        rw [hra]
        cases h
        exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hs2, hpi.of_sm sm, rfl, Nat.le_refl _,
          ValsOK.ptr hw⟩
      · cases h
  | PtrOffset k p deltaB inbounds =>
      simp only [evalRhs] at h ⊢
      split at h
      · cases h
      · rename_i pBase pOff pExt pSize pTag pB2 hrc
        obtain ⟨pA2, hra, hs2, ⟨sm, rfl⟩, hv⟩ :=
          readCellThrough_back hs hm hw (hr p (by simp [Rhs.regs])) hrc
        rw [hra]
        simp only
        split at h
        · cases h
        · cases h
          exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hs2, hpi.of_sm sm, rfl, Nat.le_refl _,
            ValsOK.ptr (hv _ List.mem_cons_self _ _ _ _ _ rfl)⟩
      · cases h
  | Borrow kind prot mask lenB base offsetB =>
      have hr' := hr base (by simp [Rhs.regs])
      simp only [evalRhs] at h ⊢
      split at h
      · rename_i b0 bo ex sz tg hl
        have hact := actOK_of hr' hl
        cases lenB with
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
            · rename_i pB2 t' hrf
              obtain ⟨pA2, hra, hs2⟩ := sb_ref_back hs hact hrf
              have hra' : MSB.ref pA (b0 + bo + offsetB) n tg kind prot mask = .ok (pA2, t') := hra
              rw [hra']
              cases h
              obtain ⟨rfl, hn, hret, -, -, -⟩ := sb_ref_fields hra
              refine ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hs2, hpi.of_ref hra, hret,
                by rw [hn]; exact Nat.le_succ _, ValsOK.ptr ⟨by rw [hn]; exact Nat.lt_succ_self _,
                  fun hr => ?_⟩⟩
              rw [hret] at hr
              exact Nat.lt_irrefl _ (hpi.ret _ hr).2
            · cases h
        | none =>
            simp only at h ⊢
            split at h
            · cases h
            rename_i hf
            rw [if_neg hf]
            split at h
            · rename_i pB2 t' hrf
              obtain ⟨pA2, hra, hs2⟩ := sb_ref_back hs hact hrf
              have hra' : MSB.ref pA (b0 + bo + offsetB) ex tg kind prot mask = .ok (pA2, t') := hra
              rw [hra']
              cases h
              obtain ⟨rfl, hn, hret, -, -, -⟩ := sb_ref_fields hra
              refine ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hs2, hpi.of_ref hra, hret,
                by rw [hn]; exact Nat.le_succ _, ValsOK.ptr ⟨by rw [hn]; exact Nat.lt_succ_self _,
                  fun hr => ?_⟩⟩
              rw [hret] at hr
              exact Nat.lt_irrefl _ (hpi.ret _ hr).2
            · cases h
      · cases h
  | BinOp op r1 r2 =>
      simp only [evalRhs] at h ⊢
      repeat' split at h
      all_goals (cases h <;> exact ⟨_, rfl, same _ (ValsOK.dat _ _)⟩)
  | SliceLen esz r =>
      simp only [evalRhs] at h ⊢
      repeat' split at h
      all_goals (cases h <;> exact ⟨_, rfl, same _ (ValsOK.dat _ _)⟩)
  | PlaceAddr r offB extB =>
      simp only [evalRhs] at h ⊢
      split at h
      · rename_i base offset ext size tag hl
        cases h
        exact ⟨_, rfl, same _ (ValsOK.ptr
          (hr r (by simp [Rhs.regs]) _ hl _ List.mem_cons_self _ _ _ _ _ rfl))⟩
      · cases h
  | SubSlice esz rp rLo rHi =>
      simp only [evalRhs] at h ⊢
      split at h
      · rename_i base offset extent size tag l hi hl _ _
        split at h
        · cases h
        rename_i hc
        rw [if_neg hc]
        cases h
        exact ⟨_, rfl, same _ (ValsOK.ptr
          (hr rp (by simp [Rhs.regs]) _ hl _ List.mem_cons_self _ _ _ _ _ rfl))⟩
      · cases h
  | PtrOffsetBy t esz rp ri inbounds =>
      simp only [evalRhs] at h ⊢
      split at h
      · rename_i base offset extent size tag w hl _
        split at h
        · cases h
        · cases h
          exact ⟨_, rfl, same _ (ValsOK.ptr
            (hr rp (by simp [Rhs.regs]) _ hl _ List.mem_cons_self _ _ _ _ _ rfl))⟩
      · cases h

/-- A store through `ptr` of values whose tags are good. -/
theorem writeThroughPtr_back {pc : Nat} {reg : RegMap} {mem : bytes.Mem} {pA pB : AccessPerms}
    (hs : PermSub pA pB) (hpi : PInv pA) (hm : MemOK (Good pA) mem) {ptr : Register}
    (hr : ∀ vs, reg.lookup ptr = some vs → ValsOK (Good pA) vs)
    {lay : BLayout} {vals : List Val} (hv : ValsOK (Good pA) vals) {msg : String}
    {sB' : oseair.State MSB_B}
    (h : writeThroughPtr MSB_B ⟨pc, reg, mem, pB⟩ ptr lay vals msg = .Ok sB') :
    ∃ sA' : oseair.State MSB, writeThroughPtr MSB ⟨pc, reg, mem, pA⟩ ptr lay vals msg = .Ok sA' ∧
      sA'.pc = pc + 1 ∧ sB'.pc = pc + 1 ∧ sA'.reg = reg ∧ sB'.reg = reg ∧ sB'.mem = sA'.mem ∧
      PermSub sA'.perms sB'.perms ∧ (∃ sm, sA'.perms = { pA with StackMap := sm }) ∧
      MemOK (Good pA) sA'.mem ∧
      (∃ base offset ext size tag, reg.lookup ptr = some [.Ptr base offset ext size tag] ∧
        sb_write pA (base + offset) lay.sizeB tag = .ok sA'.perms ∧
        mirlite.writeL mem (base + offset) lay (vals.map Val.toMem) = .ok sA'.mem) := by
  simp only [writeThroughPtr] at h ⊢
  split at h
  · rename_i base offset ext size tag hl
    split at h
    · cases h
    rename_i hf
    rw [if_neg hf]
    split at h
    · cases h
    rename_i hb
    rw [if_neg hb]
    split at h
    · rename_i pB2 hwr
      obtain ⟨pA2, hwa, hs2⟩ := sb_write_back hs (actOK_of hr hl) hwr
      have hwa' : MSB.useMut pA (base + offset) lay.sizeB tag = .ok pA2 := hwa
      rw [hwa']
      simp only
      split at h
      · rename_i mem2 hwl
        cases h
        exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, hs2, sb_write_fields hwa,
          hm.writeL hpi.good_wild hv hwl, base, offset, ext, size, tag, hl, hwa, hwl⟩
      · cases h
    · cases h
  · cases h

end obseq3.proof
