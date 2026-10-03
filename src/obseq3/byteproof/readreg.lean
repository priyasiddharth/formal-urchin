import obseq3.byteproof.leafops

/-!
# Reading a place into a register

`compileB.readToReg` — copy's read with the value register exposed — is
how `binOp`, `sliceLen`, `subSlice`, an `alloc`'s runtime length, a
guard's discriminant and `dealloc`'s pointer are read. `readToReg_simB`
states its simulation against the source's `evalCopy` with the byte
invariant `InvAtB` at BOTH ends, so successive reads chain.
-/

namespace obseq3.byteproof

open obseq3 obseq3.bytes obseq3.proof
open obseq3.mirlite (MemValue Binding Env PlaceRes)
open obseq3.oseair (Val Register)
open obseq3.compileB

theorem readToReg_shape {Γ : Ctx} {L : mirliteB.LayEnv Γ} {σ : LayoutTy} {p : Place Γ σ}
    {cs : CompilerState}
    {sOut : ResultWithEvidence PtrResult (PlaceToRegEvidence L RefKind.Shared p)}
    (h_sval : CheckedCompilerM.value (placeToRegChecked L RefKind.Shared p) cs = .ok sOut)
    (h_sclean : sOut.result.cleanup = []) :
    CheckedCompilerM.run (readToReg L p) cs
      = emit (bumpReg (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared p) cs))
          [oseairL.Instr.Assgn
            (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared p) cs).nextReg)
            (oseairL.Rhs.Load (mirliteB.placeLayout L p) sOut.result.reg)] ∧
    CheckedCompilerM.value (readToReg L p) cs
      = .ok (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared p) cs).nextReg) := by
  simp only [readToReg, CheckedCompilerM.run_bind, CheckedCompilerM.value_bind, h_sval,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift, CheckedCompilerM.run_pure,
    CheckedCompilerM.value_pure]
  refine ⟨?_, rfl⟩
  simp only [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM, cleanupInstrs, h_sclean,
    List.reverse_nil, List.map_nil, List.append_nil]

/-- `evalCopy` succeeds only through a successful access resolution. -/
theorem evalCopy_resolves {Γ : Ctx} {L : mirliteB.LayEnv Γ} {sM : mirliteB.State MSB Γ}
    {σ : LayoutTy} {p : Place Γ σ} {out : mirliteB.EvalOutput MSB Γ}
    (h : mirliteB.evalCopy MSB L sM p = .ok out) :
    ∃ r, mirliteB.resolvePlaceAcc MSB L sM p = .ok r := by
  simp only [mirliteB.evalCopy] at h
  cases h_r : mirliteB.resolvePlaceAcc MSB L sM p with
  | error e => simp [h_r] at h
  | ok r => exact ⟨r, rfl⟩

/-- Compile-time: a place the source reads compiles (`CompilesB`). -/
theorem readToReg_compilesG {Γ : Ctx} {L : mirliteB.LayEnv Γ} {ρt : TagRenameMap}
    {sM : mirliteB.State MSB Γ} {sA : oseairL.State MSB} {cs : CompilerState}
    {σ : LayoutTy} {p : Place Γ σ} {out : mirliteB.EvalOutput MSB Γ}
    (h_comp : CompilesB L p) (h_lbs : LocalBindingSimB L ρt sM.env sA cs)
    (h_ev : mirliteB.evalCopy MSB L sM p = .ok out) :
    ∃ sOut, CheckedCompilerM.value (placeToRegChecked L RefKind.Shared p) cs = .ok sOut ∧
      sOut.result.cleanup = [] ∧
      (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared p) cs).placeRegMap
        = cs.placeRegMap := by
  obtain ⟨r, h_r⟩ := evalCopy_resolves h_ev
  exact h_comp sM cs RefKind.Shared r (fun loc b h => by
    obtain ⟨reg, t, hpi, -⟩ := h_lbs loc b h
    exact ⟨reg, _, hpi⟩) h_r

theorem readToReg_compiles {Γ : Ctx} {L : mirliteB.LayEnv Γ} {ρt : TagRenameMap}
    {sM : mirliteB.State MSB Γ} {sA : oseairL.State MSB} {cs : CompilerState}
    {σ : LayoutTy} {p : Place Γ σ} {out : mirliteB.EvalOutput MSB Γ}
    (h_chain : PtrChain p) (h_lbs : LocalBindingSimB L ρt sM.env sA cs)
    (h_ev : mirliteB.evalCopy MSB L sM p = .ok out) :
    ∃ sOut, CheckedCompilerM.value (placeToRegChecked L RefKind.Shared p) cs = .ok sOut ∧
      sOut.result.cleanup = [] ∧
      (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared p) cs).placeRegMap
        = cs.placeRegMap :=
  readToReg_compilesG (ptrChain_compilesB h_chain) h_lbs h_ev

theorem readToReg_simG {Γ : Ctx} {L : mirliteB.LayEnv Γ} {ρt : TagRenameMap}
    {compProg : oseairL.Prog}
    {sM : mirliteB.State MSB Γ} {sA : oseairL.State MSB} {cs : CompilerState}
    {σ : LayoutTy} {p : Place Γ σ} {out : mirliteB.EvalOutput MSB Γ}
    (h_low : LowersB L compProg p) (h_comp : CompilesB L p) (h_inv : InvAtB L ρt sM sA cs)
    (h_ev : mirliteB.evalCopy MSB L sM p = .ok out)
    (h_code : CodeIncludedB compProg (CheckedCompilerM.run (readToReg L p) cs)) :
    ∃ n s' vals, oseairL.runN MSB n sA compProg = .Ok s' ∧
      InvAtB L ρt out.state s' (CheckedCompilerM.run (readToReg L p) cs) ∧
      out.state = { sM with perms := out.state.perms } ∧
      s'.reg.lookup
        (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared p) cs).nextReg)
        = some vals ∧
      CheckedCompilerM.value (readToReg L p) cs
        = .ok (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared p) cs).nextReg) ∧
      ListRel (StoreSim ρt) out.values (vals.map oseair.Val.toMem) ∧
      cs.nextReg ≤ (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared p) cs).nextReg ∧
      (∀ r, RegisterBelow cs.nextReg r → s'.reg.lookup r = sA.reg.lookup r) := by
  obtain ⟨sOut, h_sval, h_sclean, h_sprm⟩ := readToReg_compilesG h_comp h_inv.lbs h_ev
  obtain ⟨h_run, h_val⟩ := readToReg_shape h_sval h_sclean
  rw [h_run] at h_code ⊢
  -- the source read
  simp only [mirliteB.evalCopy] at h_ev
  cases h_res : mirliteB.resolvePlaceAcc MSB L sM p with
  | error e => simp [h_res] at h_ev
  | ok rr =>
  obtain ⟨resolved, permsR⟩ := rr
  simp only [h_res] at h_ev
  split at h_ev
  · cases h_ev
  rename_i h_free
  split at h_ev
  · cases h_ev
  rename_i h_bnd
  split at h_ev
  · cases h_ev
  rename_i permsR' hu
  split at h_ev
  · cases h_ev
  rename_i h_def
  simp only [mirliteB.EvalResult.ok.injEq] at h_ev
  subst h_ev
  -- the place's lowering
  obtain ⟨sOut', n1, s1, tres, hS⟩ :=
    h_low ρt sM RefKind.Shared cs sA resolved permsR h_inv.wf_t h_res
      h_inv.tbd h_inv.lbs h_inv.prb h_inv.mem h_inv.alloc h_inv.psim h_inv.pc
      (h_code.mono ((bumpReg_state_incr' _).trans (emit_state_incr _ _)))
  have h_same : sOut' = sOut := by
    have := hS.val
    rw [h_sval] at this
    exact (Except.ok.inj this).symm
  subst h_same
  obtain ⟨ext, h_entry⟩ := hS.entry
  have hA : resolved.allocBase + (resolved.addr - resolved.allocBase) = resolved.addr :=
    Nat.add_sub_cancel' hS.le
  have h_mem1 : ByteMemSim ρt sM.mem s1.mem := by rw [hS.mem]; exact h_inv.mem
  have h_lock1 : ByteAllocLockstep sM.mem s1.mem := by rw [hS.mem]; exact h_inv.alloc
  obtain ⟨pT', hu', hp'⟩ := sb_read_respects_PermSim hS.psim h_inv.wf_t hS.rt hu
  have hrel := readL_sim h_inv.wf_t h_mem1 resolved.addr (mirliteB.placeLayout L p)
  obtain ⟨h_defT, h_relS⟩ := readL_rel hrel (by simpa using h_def)
  have h_freeT : s1.mem.isFreed resolved.allocBase = false := by
    simp only [bytes.Mem.isFreed, ← h_lock1.2.2] at h_free ⊢
    simpa using h_free
  have h_instr : compProg s1.pc = some (oseairL.Instr.Assgn
      (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared p) cs).nextReg)
      (oseairL.Rhs.Load (mirliteB.placeLayout L p) sOut'.result.reg)) := by
    rw [hS.pc]
    apply h_code
    · simp [emit]
    · simp [emit]
  let vals := (mirliteB.readL s1.mem resolved.addr (mirliteB.placeLayout L p)).map oseair.ofMem
  have h_ev1 : oseairL.evalRhs MSB s1 (oseairL.Rhs.Load (mirliteB.placeLayout L p) sOut'.result.reg)
      = .Ok vals { s1 with perms := pT' } := by
    simp only [PermissionModel.stackedBorrows] at hu'
    simp only [oseairL.evalRhs, h_entry, hA, h_freeT, Bool.false_eq_true, if_false, h_bnd,
      PermissionModel.stackedBorrows, hu']
    simp only [h_defT, Bool.false_eq_true, if_false]
    rfl
  have h_run1 := runN_Assgn h_instr h_ev1
  have h_frame : ∀ r, RegisterBelow cs.nextReg r →
      (s1.reg.insert (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared p) cs).nextReg)
        vals).lookup r = sA.reg.lookup r := fun r hr => by
    have hne := RegisterBelow.ne_fresh (RegisterBelow.mono hS.regmono hr)
    rw [RegMap.lookup_insert_ne _ _ hne]
    exact hS.frame r hr
  refine ⟨n1 + 1, _, vals, runN_trans hS.run h_run1, ?_, rfl, RegMap.lookup_insert_self _ _ _,
    h_val, h_relS, hS.regmono, h_frame⟩
  exact {
    pc := by
      show s1.pc + 1 = _
      rw [hS.pc]; rfl
    lbs := LocalBindingSimB.prm_congr (LocalBindingSimB.of_frame h_inv.lbs h_inv.prb h_frame) hS.prm
    mem := h_mem1
    alloc := h_lock1
    psim := hp'
    wf_t := h_inv.wf_t
    tbd := by
      show TagRenameBounded ρt permsR'.NextTag pT'.NextTag
      rw [sb_read_NextTag hu, sb_read_NextTag hu', hS.srcNT]
      exact TagRenameBounded.mono h_inv.tbd (Nat.le_refl _) hS.tgtNT
    unmap := fun loc h => by
      have : getPlaceInfo (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared p) cs)
          loc.idx.1 = none := by
        show List.lookup _ _ = _
        rw [hS.prm]; exact h_inv.unmap loc h
      exact this
    prb := fun idx r τ' h => by
      have : getPlaceInfo cs idx = some (r, τ') := by
        show List.lookup _ _ = _
        rw [← hS.prm]; exact h
      exact RegisterBelow.mono (Nat.le_trans hS.regmono (Nat.le_succ _)) (h_inv.prb idx r τ' this)
  }

theorem readToReg_simB {Γ : Ctx} {L : mirliteB.LayEnv Γ} {ρt : TagRenameMap}
    {compProg : oseairL.Prog} (hWF : PtrPlacesWF L)
    {sM : mirliteB.State MSB Γ} {sA : oseairL.State MSB} {cs : CompilerState}
    {σ : LayoutTy} {p : Place Γ σ} {out : mirliteB.EvalOutput MSB Γ}
    (h_chain : PtrChain p) (h_inv : InvAtB L ρt sM sA cs)
    (h_ev : mirliteB.evalCopy MSB L sM p = .ok out)
    (h_code : CodeIncludedB compProg (CheckedCompilerM.run (readToReg L p) cs)) :
    ∃ n s' vals, oseairL.runN MSB n sA compProg = .Ok s' ∧
      InvAtB L ρt out.state s' (CheckedCompilerM.run (readToReg L p) cs) ∧
      out.state = { sM with perms := out.state.perms } ∧
      s'.reg.lookup
        (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared p) cs).nextReg)
        = some vals ∧
      CheckedCompilerM.value (readToReg L p) cs
        = .ok (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared p) cs).nextReg) ∧
      ListRel (StoreSim ρt) out.values (vals.map oseair.Val.toMem) ∧
      cs.nextReg ≤ (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared p) cs).nextReg ∧
      (∀ r, RegisterBelow cs.nextReg r → s'.reg.lookup r = sA.reg.lookup r) :=
  readToReg_simG (ptrChain_lowers hWF h_chain) (ptrChain_compilesB h_chain) h_inv h_ev h_code

end obseq3.byteproof
