import obseq3.byteproof.copy_chain

/-!
# Destination: a local's first assignment

`x := rhs` with `x` not yet allocated. Both machines allocate `x`'s block
first — the source in `preparePlaceAssign`, the compiled code with the
root `Alloc` of `ensurePlaceRoot` — and from there the statement is the
bound-local one on both sides:
- the compiler from the state after the `Alloc` emits exactly what it
  emits from the state before, minus the `Alloc` (`compileStmt_fresh_eq`);
- the source from the state after the allocation steps exactly as from the
  state before (`stepStmt_fresh_eq`).
So the leaf is one target step (the prologue, `freshroot_prologue`) and
then `storereg_local_simB`. The allocation mints a tag on both sides,
which grows the tag renaming (`sb_own_respects_PermSim`, unchanged).
-/

namespace obseq3.byteproof

open obseq3 obseq3.bytes obseq3.proof
open obseq3.mirlite (MemValue Binding Env PlaceRes)
open obseq3.oseair (Val Register)
open obseq3.compileB

/-! ## Renaming growth -/

theorem ProvSim.rename_mono {ρt ρt' : TagRenameMap} (hi : TagRenameIncr ρt ρt') :
    ∀ {p p' : Option Prov}, ProvSim ρt p p' → ProvSim ρt' p p'
  | none, none, _ => trivial
  | some _, some _, ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, hi _ _ h4⟩
  | none, some _, h => h.elim
  | some _, none, h => h.elim

theorem ByteSim.rename_mono {ρt ρt' : TagRenameMap} (hi : TagRenameIncr ρt ρt') :
    ∀ {x y : AbstractByte}, ByteSim ρt x y → ByteSim ρt' x y
  | .uninit, _, _ => trivial
  | .init _ _, .init _ _, ⟨hb, hp⟩ => ⟨hb, ProvSim.rename_mono hi hp⟩
  | .init _ _, .uninit, h => h.elim

theorem ByteMemSim.rename_mono {ρt ρt' : TagRenameMap} {mS mT : bytes.Mem}
    (hi : TagRenameIncr ρt ρt') (h : ByteMemSim ρt mS mT) : ByteMemSim ρt' mS mT :=
  fun a => ByteSim.rename_mono hi (h a)

/-! ## The compiled shape -/

/-- The compiler state after a fresh local's root `Alloc`. -/
def freshRootCS {Γ : Ctx} (L : mirliteB.LayEnv Γ) {τ : LayoutTy} (cs : CompilerState)
    (loc : Local Γ τ) : CompilerState :=
  setPlaceInfo
    (emit (bumpReg cs) [oseairL.Instr.Assgn (Register.R cs.nextReg) (oseairL.Rhs.Alloc (L loc.idx))])
    loc.idx.1 (Register.R cs.nextReg, τ)

theorem ensureLocalRegE_fresh {Γ : Ctx} {L : mirliteB.LayEnv Γ} {τ : LayoutTy}
    {loc : Local Γ τ} {cs : CompilerState} (h : getPlaceInfo cs loc.idx.1 = none) :
    CompilerM.run (ensureLocalRegE L loc) cs = freshRootCS L cs loc := by
  unfold CompilerM.run ensureLocalRegE
  split
  · rename_i reg layout h'
    rw [h'] at h; cases h
  · rfl

theorem getPlaceInfo_freshRoot_self {Γ : Ctx} {L : mirliteB.LayEnv Γ} {τ : LayoutTy}
    (cs : CompilerState) (loc : Local Γ τ) :
    getPlaceInfo (freshRootCS L cs loc) loc.idx.1 = some (Register.R cs.nextReg, τ) := by
  simp [freshRootCS, getPlaceInfo, setPlaceInfo]

theorem getPlaceInfo_freshRoot_ne {Γ : Ctx} {L : mirliteB.LayEnv Γ} {τ : LayoutTy}
    (cs : CompilerState) (loc : Local Γ τ) {idx : Nat} (h : idx ≠ loc.idx.1) :
    getPlaceInfo (freshRootCS L cs loc) idx = getPlaceInfo cs idx := by
  have hb : (idx == loc.idx.1) = false := by simp [h]
  simp only [freshRootCS, getPlaceInfo, setPlaceInfo, List.lookup, hb]
  rfl

/-- From a state that has not mapped the local, the statement compiles to
    the root `Alloc` followed by exactly what it compiles to once mapped. -/
theorem compileStmt_fresh_eq {Γ : Ctx} {L : mirliteB.LayEnv Γ} {τ : LayoutTy}
    {loc : Local Γ τ} {rhs : RExpr Γ τ} {cs : CompilerState}
    (h : getPlaceInfo cs loc.idx.1 = none) :
    CheckedCompilerM.run (compileStmtChecked L (.assign (.local loc) rhs)) cs
      = CheckedCompilerM.run (compileStmtChecked L (.assign (.local loc) rhs))
          (freshRootCS L cs loc) := by
  have h1 : CompilerM.run (ensurePlaceRoot L (.local loc)) cs = freshRootCS L cs loc := by
    simp only [ensurePlaceRoot, CompilerM.run_bind, CompilerM.run_pure, ensureLocalRegE_fresh h]
  have h2 : CompilerM.run (ensurePlaceRoot L (.local loc)) (freshRootCS L cs loc)
      = freshRootCS L cs loc := by
    simp only [ensurePlaceRoot, CompilerM.run_bind, CompilerM.run_pure,
      ensureLocalRegE_existing (L := L) (getPlaceInfo_freshRoot_self (L := L) cs loc)]
  simp only [compileStmtChecked, compileAssignChecked, CheckedCompilerM.run_bind,
    CheckedCompilerM.value_lift, CheckedCompilerM.run_lift]
  rw [h1, h2]

/-! ## The source -/

theorem stepStmt_fresh_eq {Γ : Ctx} {L : mirliteB.LayEnv Γ} {τ : LayoutTy}
    {loc : Local Γ τ} {rhs : RExpr Γ τ} {s s1 : mirliteB.State MSB Γ}
    (h_env : s.env.lookup loc = none)
    (h_alloc : mirliteB.allocateBase MSB L s loc = .ok s1)
    (h_env1 : ∃ b, s1.env.lookup loc = some b) :
    mirliteB.stepStmt MSB L s (.assign (.local loc) rhs)
      = mirliteB.stepStmt MSB L s1 (.assign (.local loc) rhs) := by
  have h0 : mirliteB.preparePlaceAssign MSB L s (.local loc) = .ok s1 := by
    simp only [mirliteB.preparePlaceAssign, mirliteB.resolvePlace?, h_env, mirliteB.allocateRoot,
      h_alloc]
  have h1 : mirliteB.preparePlaceAssign MSB L s1 (.local loc) = .ok s1 := by
    obtain ⟨b, hb⟩ := h_env1
    simp only [mirliteB.preparePlaceAssign, mirliteB.resolvePlace?, hb]
  simp only [mirliteB.stepStmt, mirliteB.doAssign, h0, h1]

/-! ## The prologue: the root `Alloc` against the source's allocation -/

theorem Local.ext_idx {Γ : Ctx} {τ τ' : LayoutTy} (l : Local Γ τ) (l' : Local Γ τ')
    (h : l'.idx = l.idx) : τ' = τ := by
  rw [← l'.hTy, ← l.hTy, h]

theorem freshroot_prologue {Γ : Ctx} {L : mirliteB.LayEnv Γ} {ρt : TagRenameMap}
    {s_mir s1 : mirliteB.State MSB Γ} {s_osea : oseairL.State MSB} {cs : CompilerState}
    {τ : LayoutTy} {loc : Local Γ τ} {compProg : oseairL.Prog}
    (h_inv : InvAtB L ρt s_mir s_osea cs)
    (h_env : s_mir.env.lookup loc = none)
    (h_alloc : mirliteB.allocateBase MSB L s_mir loc = .ok s1)
    (h_code : compProg s_osea.pc = some (oseairL.Instr.Assgn (Register.R cs.nextReg)
      (oseairL.Rhs.Alloc (L loc.idx)))) :
    ∃ (ρt' : TagRenameMap) (sA1 : oseairL.State MSB),
      TagRenameIncr ρt ρt' ∧
      oseairL.runN MSB 1 s_osea compProg = .Ok sA1 ∧
      InvAtB L ρt' s1 sA1 (freshRootCS L cs loc) ∧
      ∃ b, s1.env.lookup loc = some b := by
  simp only [mirliteB.allocateBase] at h_alloc
  split at h_alloc
  · cases h_alloc
  rename_i permsOwned tag hown
  simp only [mirliteB.Result.ok.injEq] at h_alloc
  subst h_alloc
  obtain ⟨h_base, h_memA, h_lockA⟩ := ByteMemSim.allocate h_inv.mem h_inv.alloc
    (L loc.idx).size (max 1 (L loc.idx).align)
  obtain ⟨tgt', h_own_t, h_tag, h_incr, h_wf', h_tbd', h_psim'⟩ :=
    sb_own_respects_PermSim h_inv.psim h_inv.wf_t h_inv.tbd hown
  subst h_tag
  have h_w : wildcardTag < s_mir.perms.NextTag := (h_inv.tbd _ _ h_inv.wf_t.2).1
  refine ⟨ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag,
    { s_osea with
        mem := (s_osea.mem.allocate (L loc.idx).size (max 1 (L loc.idx).align)).2,
        perms := tgt',
        reg := s_osea.reg.insert (Register.R cs.nextReg)
          [Val.Ptr (s_mir.mem.allocate (L loc.idx).size (max 1 (L loc.idx).align)).1 0
            (L loc.idx).size (L loc.idx).size s_osea.perms.NextTag],
        pc := s_osea.pc + 1 }, h_incr, ?_, ?_, ?_⟩
  · simp only [oseairL.runN, oseairL.step, h_code, oseairL.evalRhs, oseairL.allocPtr, h_base,
      PermissionModel.stackedBorrows, h_own_t]
  · exact {
      pc := by simp [freshRootCS, setPlaceInfo, emit, h_inv.pc]
      lbs := by
        intro τ' loc' b' h'
        simp only [mirlite.Env.lookup, mirlite.Env.set] at h'
        by_cases hi : loc'.idx = loc.idx
        · rw [if_pos hi] at h'
          have hτ := Local.ext_idx loc loc' hi
          subst hτ
          have hl : loc' = loc := by
            cases loc'; cases loc; simp only at hi; subst hi; rfl
          subst hl
          simp only [Option.some.injEq] at h'
          subst h'
          refine ⟨Register.R cs.nextReg, s_osea.perms.NextTag,
            getPlaceInfo_freshRoot_self cs loc', ⟨(L loc'.idx).size, ?_⟩,
            TagRenameMap.extend_self _ _ _, ?_⟩
          · exact RegMap.lookup_insert_self _ _ _
          · simp only [beq_eq_false_iff_ne]; exact (Nat.ne_of_lt h_w).symm
        · rw [if_neg hi] at h'
          obtain ⟨r, t, hpi, ⟨e, hr⟩, hrt, hnw⟩ := h_inv.lbs loc' b' h'
          have hne : loc'.idx.1 ≠ loc.idx.1 := fun h => hi (Fin.ext h)
          refine ⟨r, t, by rw [getPlaceInfo_freshRoot_ne cs loc hne]; exact hpi, ⟨e, ?_⟩,
            h_incr _ _ hrt, hnw⟩
          show (s_osea.reg.insert _ _).lookup r = _
          rw [RegMap.lookup_insert_ne _ _ (RegisterBelow.ne_fresh (h_inv.prb _ _ _ hpi))]
          exact hr
      mem := ByteMemSim.rename_mono h_incr h_memA
      alloc := h_lockA
      psim := h_psim'
      wf_t := h_wf'
      tbd := h_tbd'
      unmap := by
        intro τ' loc' h'
        simp only [mirlite.Env.lookup, mirlite.Env.set] at h'
        by_cases hi : loc'.idx = loc.idx
        · rw [if_pos hi] at h'; cases h'
        · rw [if_neg hi] at h'
          have hne : loc'.idx.1 ≠ loc.idx.1 := fun h => hi (Fin.ext h)
          rw [getPlaceInfo_freshRoot_ne cs loc hne]
          exact h_inv.unmap loc' h'
      prb := by
        intro idx r τ' h'
        by_cases hi : idx = loc.idx.1
        · subst hi
          rw [getPlaceInfo_freshRoot_self] at h'
          simp only [Option.some.injEq, Prod.mk.injEq] at h'
          obtain ⟨rfl, -⟩ := h'
          show cs.nextReg < cs.nextReg + 1
          omega
        · rw [getPlaceInfo_freshRoot_ne cs loc hi] at h'
          exact RegisterBelow.mono (Nat.le_succ _) (h_inv.prb _ _ _ h')
    }
  · exact ⟨_, by simp only [mirlite.Env.lookup, mirlite.Env.set, if_true]; rfl⟩

/-! ## The leaf -/

/-- A local's first assignment, for any rvalue with a value package
    (`proof/spine.lean`'s `storereg_localfresh_simulation`). -/
theorem storereg_localfresh_simB {Γ : Ctx} {L : mirliteB.LayEnv Γ} {ρt : TagRenameMap}
    {s_mir s_mir' : mirliteB.State MSB Γ} {s_osea : oseairL.State MSB}
    {τ : LayoutTy} {loc : Local Γ τ} {rhs : RExpr Γ τ} {cs : CompilerState}
    (compProg : oseairL.Prog)
    (h_pkg : ValuePkgB compProg L (L loc.idx) rhs)
    (h_inv : InvAtB L ρt s_mir s_osea cs)
    (h_code : CodeIncludedB compProg
      (CheckedCompilerM.run (compileStmtChecked L (.assign (.local loc) rhs)) cs))
    (h_env : s_mir.env.lookup loc = none)
    (h_step : mirliteB.stepStmt MSB L s_mir (.assign (.local loc) rhs) = .ok s_mir') :
    ∃ (ρt' : TagRenameMap) (s_osea' : oseairL.State MSB) (n : Nat),
      TagRenameIncr ρt ρt' ∧
      oseairL.runN MSB n s_osea compProg = .Ok s_osea' ∧
      InvAtB L ρt' s_mir' s_osea'
        (CheckedCompilerM.run (compileStmtChecked L (.assign (.local loc) rhs)) cs) := by
  have h_pi := h_inv.unmap loc h_env
  rw [compileStmt_fresh_eq h_pi] at h_code ⊢
  have h_prep : mirliteB.preparePlaceAssign MSB L s_mir (.local loc)
      = mirliteB.allocateBase MSB L s_mir loc := by
    simp only [mirliteB.preparePlaceAssign, mirliteB.resolvePlace?, h_env, mirliteB.allocateRoot]
  cases h_a : mirliteB.allocateBase MSB L s_mir loc with
  | err e =>
      simp only [mirliteB.stepStmt, mirliteB.doAssign, h_prep, h_a] at h_step
      cases h_step
  | ok s1 =>
  -- the root `Alloc` is the first instruction
  have h_codeF : CodeIncludedB compProg (freshRootCS L cs loc) :=
    h_code.mono (CheckedCompilerM.incr _ _)
  have h_alloc_instr : compProg s_osea.pc = some (oseairL.Instr.Assgn (Register.R cs.nextReg)
      (oseairL.Rhs.Alloc (L loc.idx))) := by
    rw [h_inv.pc]
    apply h_codeF
    · simp [freshRootCS, setPlaceInfo, emit]
    · simp [freshRootCS, setPlaceInfo, emit]
  obtain ⟨ρt', sA1, h_incr, h_run1, h_inv1, b, hb⟩ :=
    freshroot_prologue h_inv h_env h_a h_alloc_instr
  rw [stepStmt_fresh_eq h_env h_a ⟨b, hb⟩] at h_step
  obtain ⟨ρt'', s', n, h_incr2, h_run2, h_inv2⟩ :=
    storereg_local_simB compProg h_pkg h_inv1 h_code hb h_step
  exact ⟨ρt'', s', 1 + n, h_incr.trans h_incr2, runN_trans h_run1 h_run2, h_inv2⟩

end obseq3.byteproof
