import obseq3.proof.freshroot

/-!
# Destination: a field

`b.f := rhs` with `b` a place that lowers (`LowersB`) and is not itself a
projection. At byte offset zero the field lowers exactly as its base
(`proj_zero_lowers`), so the general destination leaf applies. At a
nonzero offset the compiler borrows the field: `Borrow(Mut); store
through the temporary; Die` — and keystone's `sb_ref_use_die_cancels`
(any length, so the field's byte length here) shows the triple has the
stack effect of the source's one write through the base's tag.
-/

namespace obseq3.proof

open obseq3 obseq3.bytes obseq3.proof
open obseq3.mirlite (MemValue Binding Env PlaceRes)
open obseq3.oseair (Val Register)
open obseq3.compile

/-- A field at byte offset zero lowers as its base. -/
theorem proj_zero_lowers {Γ : Ctx} {L : mirlite.LayEnv Γ} {compProg : oseair.Prog}
    {ρ τ : LayoutTy} {b : Place Γ ρ} (f : PathTo ρ τ)
    (h_np : ∀ (σ' : LayoutTy) (bb : Place Γ σ') (q : PathTo σ' ρ), b = bb.proj q → False)
    (h0 : pathOffsetB L b f = 0) (hb : LowersB L compProg b) :
    LowersB L compProg (.proj b f) := by
  intro ρt sM kind cs sA resolved permsD hwf h_res h_tbd h_lbs h_prb h_mem h_lock h_psim h_pc
    h_inc
  simp only [mirlite.resolvePlaceAcc] at h_res
  cases h_rb : mirlite.resolvePlaceAcc MSB L sM b with
  | error e => simp [h_rb] at h_res
  | ok rb =>
  obtain ⟨bRes, permsB⟩ := rb
  simp only [h_rb, Except.ok.injEq, Prod.mk.injEq] at h_res
  obtain ⟨rfl, rfl⟩ := h_res
  -- the field's code is the base's
  have h_runEq : CheckedCompilerM.run (placeToRegChecked L kind (.proj b f)) cs
      = CheckedCompilerM.run (placeToRegChecked L kind b) cs := by
    cases h_bv : CheckedCompilerM.value (placeToRegChecked L kind b) cs with
    | ok bOut => exact ((proj_lowering (kind := kind) f h_np h_bv).1 h0).1
    | error e =>
        rw [proj_eq f h_np, CheckedCompilerM.run_bind, h_bv]
  rw [h_runEq] at h_inc
  obtain ⟨bOut, n1, s1, btag, hB⟩ :=
    hb ρt sM kind cs sA bRes permsB hwf h_rb h_tbd h_lbs h_prb h_mem h_lock h_psim h_pc h_inc
  obtain ⟨h_runP, outP, h_valP, h_resP⟩ := (proj_lowering (kind := kind) f h_np hB.val).1 h0
  have h0' : mirlite.fieldOffsetB (mirlite.placeLayout L b) f.indices = 0 := h0
  exact ⟨outP, n1, s1, btag, {
    val := h_valP
    clean := by rw [h_resP]; exact hB.clean
    run := hB.run
    pc := by rw [h_runP]; exact hB.pc
    mem := hB.mem
    psim := hB.psim
    srcNT := hB.srcNT
    tgtNT := hB.tgtNT
    entry := by
      obtain ⟨e, he⟩ := hB.entry
      exact ⟨e, by rw [h_resP]; simpa [h0'] using he⟩
    rt := hB.rt
    le := by simpa [h0'] using hB.le
    below := by rw [h_runP, h_resP]; exact hB.below
    prm := by rw [h_runP]; exact hB.prm
    regmono := by rw [h_runP]; exact hB.regmono
    labmono := by rw [h_runP]; exact hB.labmono
    frame := hB.frame }⟩

/-! ## Nonzero offset -/

/-- The statement's shape when the destination's lowering leaves a
    cleanup: the store, then the cleanup's `Die`s. -/
theorem compileStmt_storereg_dst' {Γ : Ctx} {L : mirlite.LayEnv Γ} {τ : LayoutTy}
    {dst : Place Γ τ} {rhs : RExpr Γ τ} {cs : CompilerState} {pOut : RhsPre L τ rhs}
    {mkStore : Register → oseair.Instr}
    {dOut : ResultWithEvidence PtrResult (PlaceToRegEvidence L RefKind.Mut dst)}
    (h_root : CompilerM.run (ensurePlaceRoot L dst) cs = cs)
    (h_pval : CheckedCompilerM.value (compileRExprPreChecked L (mirlite.placeLayout L dst) rhs) cs
      = .ok pOut)
    (h_store : ∀ d, pOut.store d = [mkStore d]) (h_post : pOut.postCleanup = [])
    (h_dval : CheckedCompilerM.value (placeToRegChecked L RefKind.Mut dst)
      (CheckedCompilerM.run (compileRExprPreChecked L (mirlite.placeLayout L dst) rhs) cs)
      = .ok dOut) :
    CheckedCompilerM.run (compileStmtChecked L (.assign dst rhs)) cs
      = emit (emit (CheckedCompilerM.run (placeToRegChecked L RefKind.Mut dst)
          (CheckedCompilerM.run (compileRExprPreChecked L (mirlite.placeLayout L dst) rhs) cs))
          [mkStore dOut.result.reg]) (cleanupInstrs dOut.result.cleanup) := by
  simp only [compileStmtChecked, compileAssignChecked, CheckedCompilerM.run_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, h_root, h_pval, h_dval, h_store, h_post]
  simp only [CompilerM.run, emitM, cleanupInstrs, List.reverse_nil, List.map_nil, emit_nil]

theorem code_three' (rb : CompilerState) (i1 i2 i3 : oseair.Instr) :
    (emit (emit (emit (bumpReg rb) [i1]) [i2]) [i3]).code rb.nextLabel = some i1 ∧
    (emit (emit (emit (bumpReg rb) [i1]) [i2]) [i3]).code (rb.nextLabel + 1) = some i2 ∧
    (emit (emit (emit (bumpReg rb) [i1]) [i2]) [i3]).code (rb.nextLabel + 2) = some i3 ∧
    (emit (emit (emit (bumpReg rb) [i1]) [i2]) [i3]).nextLabel = rb.nextLabel + 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [emit]
  all_goals (repeat (first | rw [if_neg (by omega)] | rw [if_pos (by omega)])) <;> rfl

/-- A field destination at a nonzero byte offset, for any rvalue with a
    value package. -/
theorem storereg_projoff_simB {Γ : Ctx} {L : mirlite.LayEnv Γ} {ρt : TagRenameMap}
    {s_mir s_mir' : mirlite.State MSB Γ} {s_osea : oseair.State MSB}
    {ρ τ : LayoutTy} {b : Place Γ ρ} {f : PathTo ρ τ} {rhs : RExpr Γ τ} {cs : CompilerState}
    (compProg : oseair.Prog)
    (h_np : ∀ (σ' : LayoutTy) (bb : Place Γ σ') (q : PathTo σ' ρ), b = bb.proj q → False)
    (h0 : pathOffsetB L b f ≠ 0) (hb : LowersB L compProg b)
    (h_prepOK : ∀ s1, mirlite.preparePlaceAssign MSB L s_mir (.proj b f) = .ok s1 →
      s1 = s_mir ∧ ∃ r, mirlite.resolvePlace? MSB L s_mir (.proj b f) = some r)
    (h_pkg : ValuePkgB compProg L (mirlite.placeLayout L (.proj b f)) rhs)
    (h_inv : InvAtB L ρt s_mir s_osea cs)
    (h_code : CodeIncludedB compProg
      (CheckedCompilerM.run (compileStmtChecked L (.assign (.proj b f) rhs)) cs))
    (h_step : mirlite.stepStmt MSB L s_mir (.assign (.proj b f) rhs) = .ok s_mir') :
    ∃ (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = .Ok s_osea' ∧
      InvAtB L ρt' s_mir' s_osea'
        (CheckedCompilerM.run (compileStmtChecked L (.assign (.proj b f) rhs)) cs) := by
  -- §1 the source: no allocation; the rvalue
  simp only [mirlite.stepStmt, mirlite.doAssign] at h_step
  cases h_prep : mirlite.preparePlaceAssign MSB L s_mir (.proj b f) with
  | err msg => rw [h_prep] at h_step; cases h_step
  | ok s1 =>
  rw [h_prep] at h_step
  obtain ⟨rfl, rp, h_rp⟩ := h_prepOK s1 h_prep
  simp only at h_step
  split at h_step
  · cases h_step
  rename_i output h_eval
  obtain ⟨mkStore, pOut, h_pval, h_storeR, h_postR, h_prmR, h_pkg'⟩ :=
    h_pkg ρt s1 s_osea cs h_inv.wf_t h_inv.tbd h_inv.lbs h_inv.prb h_inv.mem
      h_inv.alloc h_inv.psim h_inv.pc h_inv.unmap output h_eval
  split at h_step
  · cases h_step
  rename_i resolved permsD h_dres
  have h_root : CompilerM.run (ensurePlaceRoot L (.proj b f)) cs = cs := by
    refine ensurePlaceRoot_noop (s := s1) (fun loc bnd h => ?_) _ _ h_rp
    obtain ⟨r, t, hpi, -⟩ := h_inv.lbs loc bnd h
    exact ⟨r, _, hpi⟩
  -- §2 code inclusion down to the rvalue and the base
  have h_codeD := h_code.mono (assign_dst_incr (rhs := rhs) h_root h_pval)
  have h_codeB := h_codeD.mono (proj_incr (kind := RefKind.Mut) f
    (CheckedCompilerM.run (compileRExprPreChecked L (mirlite.placeLayout L (.proj b f)) rhs) cs)
    h_np)
  have h_codePre := h_codeB.mono (CheckedCompilerM.incr (placeToRegChecked L RefKind.Mut b)
    (CheckedCompilerM.run (compileRExprPreChecked L (mirlite.placeLayout L (.proj b f)) rhs) cs))
  obtain ⟨ρt', nR, sR, memO, perms₂, vals, h_incr_t, h_wf_t', h_ost, h_runR, h_regmono,
    h_lbsR, h_psimR, h_tbdR, h_memR, h_allocR, h_pcR, h_exec, h_valsRel⟩ := h_pkg' h_codePre
  rw [h_ost] at h_dres h_step
  have h_prbR : PlaceRegMapBoundB
      (CheckedCompilerM.run (compileRExprPreChecked L (mirlite.placeLayout L (.proj b f)) rhs) cs) :=
    fun idx r τ' h' => RegisterBelow.mono h_regmono (h_inv.prb idx r τ' (by
      show List.lookup _ _ = _
      rw [← h_prmR]; exact h'))
  -- §3 the base's lowering
  simp only [mirlite.resolvePlaceAcc] at h_dres
  cases h_bres : mirlite.resolvePlaceAcc MSB L { s1 with mem := memO, perms := perms₂ } b with
  | error e => simp [h_bres] at h_dres
  | ok rb =>
  obtain ⟨bRes, permsB⟩ := rb
  simp only [h_bres, Except.ok.injEq, Prod.mk.injEq] at h_dres
  obtain ⟨rfl, rfl⟩ := h_dres
  obtain ⟨bOut, n2, s2, btag, hB⟩ :=
    hb ρt' { s1 with mem := memO, perms := perms₂ } RefKind.Mut _ sR bRes permsB h_wf_t'
      h_bres h_tbdR h_lbsR h_prbR h_memR h_allocR h_psimR h_pcR h_codeB
  obtain ⟨h_runP, outP, h_valP, h_resP⟩ :=
    (proj_lowering (kind := RefKind.Mut) f h_np hB.val).2 h0
  have h_shape := compileStmt_storereg_dst' h_root h_pval h_storeR h_postR h_valP
  rw [h_resP, hB.clean, h_runP] at h_shape
  simp only [List.nil_append, cleanupInstrs, List.reverse_cons, List.reverse_nil,
    List.map_cons, List.map_nil] at h_shape
  rw [h_shape] at h_code ⊢
  -- §4 the source write
  simp only [mirlite.writeResolvedPlace] at h_step
  split at h_step
  · cases h_step
  rename_i h_free
  split at h_step
  · cases h_step
  rename_i h_bnd
  split at h_step
  case h_2 => cases h_step
  rename_i permsW hu
  split at h_step
  case h_2 => cases h_step
  rename_i memW hw
  simp only [mirlite.Result.ok.injEq] at h_step
  subst h_step
  obtain ⟨ext, h_bentry⟩ := hB.entry
  have hA : bRes.allocBase + (bRes.addr - bRes.allocBase) = bRes.addr :=
    Nat.add_sub_cancel' hB.le
  have h_bnd' : bRes.addr + pathOffsetB L b f + placeSizeB L (.proj b f)
      ≤ bRes.allocBase + bRes.allocSizeB := Nat.le_of_not_gt h_bnd
  have h_mem2 : ByteMemSim ρt' memO s2.mem := by rw [hB.mem]; exact h_memR
  have h_lock2 : ByteAllocLockstep memO s2.mem := by rw [hB.mem]; exact h_allocR
  -- the write transported; the target's Mut retag succeeds
  obtain ⟨p2, h_wr', h_psim2⟩ := sb_write_respects_PermSim hB.psim h_wf_t' hB.rt hu
  obtain ⟨q1, h_ref⟩ := sb_ref_Mut_ok_of_sb_write_ok h_wr'
  have h_tbd_mid : TagRenameBounded ρt' permsB.NextTag s2.perms.NextTag := by
    rw [hB.srcNT]; exact TagRenameBounded.mono h_tbdR (Nat.le_refl _) hB.tgtNT
  have h_unprot := freshTag_not_protected hB.psim h_tbd_mid
  have h0w : wildcardTag < s2.perms.NextTag := (h_tbd_mid _ _ h_wf_t'.2).2
  have h_ntw : (s2.perms.NextTag == wildcardTag) = false := by
    simp only [beq_eq_false_iff_ne]; exact (Nat.ne_of_lt h0w).symm
  obtain ⟨q2, q3, sAcc, h_wr1, h_die1, h_wr2, h_sm, h_ex, h_pf, h_ntle, h_wk⟩ :=
    sb_ref_use_die_cancels h_ntw h_unprot h_ref
  have h_acc : sAcc = p2 := Except.ok.inj (h_wr2.symm.trans h_wr')
  subst h_acc
  obtain ⟨mT', hw', hm'⟩ := writeL_sim h_mem2 h_valsRel hw
  have h_freeT : s2.mem.isFreed bRes.allocBase = false := by
    simp only [bytes.Mem.isFreed, ← h_lock2.2.2] at h_free ⊢
    simpa using h_free
  -- the code
  have hct := fun i1 i2 i3 => code_three'
    (CheckedCompilerM.run (placeToRegChecked L RefKind.Mut b)
      (CheckedCompilerM.run (compileRExprPreChecked L (mirlite.placeLayout L (.proj b f)) rhs) cs))
    i1 i2 i3
  have h_at : ∀ k instr, k < 3 →
      (emit (emit (emit (bumpReg (CheckedCompilerM.run (placeToRegChecked L RefKind.Mut b)
        (CheckedCompilerM.run (compileRExprPreChecked L (mirlite.placeLayout L (.proj b f)) rhs) cs)))
        [oseair.Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Mut b)
          (CheckedCompilerM.run (compileRExprPreChecked L (mirlite.placeLayout L (.proj b f)) rhs) cs)).nextReg)
          (borrowRhs RefKind.Mut (placeSizeB L (.proj b f)) bOut.result.reg (pathOffsetB L b f))])
        [mkStore (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Mut b)
          (CheckedCompilerM.run (compileRExprPreChecked L (mirlite.placeLayout L (.proj b f)) rhs) cs)).nextReg)])
        [oseair.Instr.Die (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Mut b)
          (CheckedCompilerM.run (compileRExprPreChecked L (mirlite.placeLayout L (.proj b f)) rhs) cs)).nextReg)
          (placeSizeB L (.proj b f))]).code (s2.pc + k) = some instr →
      compProg (s2.pc + k) = some instr := by
    intro k instr hk hc
    refine h_code _ instr ?_ hc
    rw [(hct _ _ _).2.2.2, hB.pc]; omega
  -- §5 Borrow; store; Die
  have h1 := runN_Borrow (s := s2) (h_at 0 _ (by omega) (by rw [hB.pc]; exact (hct _ _ _).1))
    h_bentry h_freeT (by rw [hA]; exact h_bnd') (by rw [hA]; exact h_ref)
  let S1 : oseair.State MSB :=
    { s2 with
        perms := q1,
        reg := s2.reg.insert
          (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Mut b)
            (CheckedCompilerM.run (compileRExprPreChecked L (mirlite.placeLayout L (.proj b f)) rhs) cs)).nextReg)
          [Val.Ptr bRes.allocBase (bRes.addr - bRes.allocBase + pathOffsetB L b f)
            (placeSizeB L (.proj b f)) bRes.allocSizeB s2.perms.NextTag],
        pc := s2.pc + 1 }
  have h_wtp : oseair.writeThroughPtr MSB S1
      (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Mut b)
        (CheckedCompilerM.run (compileRExprPreChecked L (mirlite.placeLayout L (.proj b f)) rhs) cs)).nextReg)
      (mirlite.placeLayout L (.proj b f)) vals "store"
      = .Ok { S1 with perms := q2, mem := mT', pc := S1.pc + 1 } := by
    have hA' : bRes.allocBase + (bRes.addr - bRes.allocBase + pathOffsetB L b f)
        = bRes.addr + pathOffsetB L b f := by rw [← Nat.add_assoc, hA]
    have h_nb : ¬ (bRes.allocBase + (bRes.addr - bRes.allocBase + pathOffsetB L b f)
        + (mirlite.placeLayout L (.proj b f)).sizeB > bRes.allocBase + bRes.allocSizeB) := by
      rw [hA']; exact h_bnd
    simp only [oseair.writeThroughPtr, S1, RegMap.lookup_insert_self, h_freeT,
      Bool.false_eq_true, if_false, h_nb, PermissionModel.stackedBorrows]
    rw [hA', h_wr1, hw']
  have h2 := h_exec S1 _ _
    (fun r hr => by
      have hne := RegisterBelow.ne_fresh (RegisterBelow.mono hB.regmono hr)
      show (s2.reg.insert _ _).lookup r = _
      rw [RegMap.lookup_insert_ne _ _ hne]
      exact hB.frame r hr)
    (h_at 1 _ (by omega) (by rw [hB.pc]; exact (hct _ _ _).2.1)) h_wtp
  have h3 := runN_Die (s := { S1 with perms := q2, mem := mT', pc := S1.pc + 1 })
    (h_at 2 _ (by omega) (by rw [hB.pc]; exact (hct _ _ _).2.2.1))
    (RegMap.lookup_insert_self _ _ _)
    (by rw [← Nat.add_assoc, hA]; exact h_die1)
  refine ⟨ρt', _, nR + n2 + 1 + 1 + 1, h_incr_t,
    runN_trans (runN_trans (runN_trans (runN_trans h_runR hB.run) h1) h2) h3, ?_⟩
  obtain ⟨bufS, rfl⟩ := writeL_eq_write hw
  obtain ⟨bufT, rfl⟩ := writeL_eq_write hw'
  exact {
    pc := by
      show s2.pc + 1 + 1 + 1 = _
      rw [(hct _ _ _).2.2.2, hB.pc]
    lbs := LocalBindingSimB.prm_congr (h_lbsR.of_frame h_prbR fun r hr => by
        have hne := RegisterBelow.ne_fresh (RegisterBelow.mono hB.regmono hr)
        show (s2.reg.insert _ _).lookup r = _
        rw [RegMap.lookup_insert_ne _ _ hne]
        exact hB.frame r hr) hB.prm
    mem := hm'
    alloc := h_lock2.write _ _ _ _
    psim := ⟨by rw [h_sm]; exact h_psim2.1, by rw [h_pf]; exact h_psim2.2.1,
      by rw [h_ex]; exact h_psim2.2.2.1, Nat.le_trans h_psim2.2.2.2.1 h_ntle,
      by rw [h_wk]; exact h_psim2.2.2.2.2⟩
    wf_t := h_wf_t'
    tbd := by
      have h1' := sb_write_NextTag hu
      show TagRenameBounded ρt' permsW.NextTag q3.NextTag
      rw [h1', hB.srcNT]
      refine TagRenameBounded.mono h_tbdR (Nat.le_refl _) (Nat.le_trans hB.tgtNT ?_)
      rw [← sb_write_NextTag h_wr']; exact h_ntle
    unmap := fun loc' h' => by
      have : getPlaceInfo (CheckedCompilerM.run (placeToRegChecked L RefKind.Mut b)
          (CheckedCompilerM.run (compileRExprPreChecked L (mirlite.placeLayout L (.proj b f)) rhs) cs))
          loc'.idx.1 = none := by
        show List.lookup _ _ = _
        rw [hB.prm, h_prmR]; exact h_inv.unmap loc' h'
      exact this
    prb := fun idx r τ' h' => by
      have : getPlaceInfo cs idx = some (r, τ') := by
        show List.lookup _ _ = _
        rw [← h_prmR, ← hB.prm]; exact h'
      exact RegisterBelow.mono (Nat.le_trans (Nat.le_trans h_regmono hB.regmono) (Nat.le_succ _))
        (h_inv.prb idx r τ' this)
  }

/-- A field of a base that lowers and is not a projection, at either
    offset, for any rvalue with a value package. -/
theorem storereg_proj_simB {Γ : Ctx} {L : mirlite.LayEnv Γ} {ρt : TagRenameMap}
    {s_mir s_mir' : mirlite.State MSB Γ} {s_osea : oseair.State MSB}
    {ρ τ : LayoutTy} {b : Place Γ ρ} {f : PathTo ρ τ} {rhs : RExpr Γ τ} {cs : CompilerState}
    (compProg : oseair.Prog)
    (h_np : ∀ (σ' : LayoutTy) (bb : Place Γ σ') (q : PathTo σ' ρ), b = bb.proj q → False)
    (hb : LowersB L compProg b)
    (h_prepOK : ∀ s1, mirlite.preparePlaceAssign MSB L s_mir (.proj b f) = .ok s1 →
      s1 = s_mir ∧ ∃ r, mirlite.resolvePlace? MSB L s_mir (.proj b f) = some r)
    (h_pkg : ValuePkgB compProg L (mirlite.placeLayout L (.proj b f)) rhs)
    (h_inv : InvAtB L ρt s_mir s_osea cs)
    (h_code : CodeIncludedB compProg
      (CheckedCompilerM.run (compileStmtChecked L (.assign (.proj b f) rhs)) cs))
    (h_step : mirlite.stepStmt MSB L s_mir (.assign (.proj b f) rhs) = .ok s_mir') :
    ∃ (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = .Ok s_osea' ∧
      InvAtB L ρt' s_mir' s_osea'
        (CheckedCompilerM.run (compileStmtChecked L (.assign (.proj b f) rhs)) cs) := by
  by_cases h0 : pathOffsetB L b f = 0
  · exact storereg_lowered_simB compProg (proj_zero_lowers f h_np h0 hb) h_prepOK h_pkg h_inv
      h_code h_step
  · exact storereg_projoff_simB compProg h_np h0 hb h_prepOK h_pkg h_inv h_code h_step

/-- `x.f := rhs`, `x` a bound local. -/
theorem storereg_projlocal_simB {Γ : Ctx} {L : mirlite.LayEnv Γ} {ρt : TagRenameMap}
    {s_mir s_mir' : mirlite.State MSB Γ} {s_osea : oseair.State MSB}
    {ρ τ : LayoutTy} {loc : Local Γ ρ} {f : PathTo ρ τ} {rhs : RExpr Γ τ} {cs : CompilerState}
    {bnd : Binding}
    (compProg : oseair.Prog) (hWF : PtrPlacesWF L)
    (h_env : s_mir.env.lookup loc = some bnd)
    (h_pkg : ValuePkgB compProg L (mirlite.placeLayout L (.proj (.local loc) f)) rhs)
    (h_inv : InvAtB L ρt s_mir s_osea cs)
    (h_code : CodeIncludedB compProg
      (CheckedCompilerM.run (compileStmtChecked L (.assign (.proj (.local loc) f) rhs)) cs))
    (h_step : mirlite.stepStmt MSB L s_mir (.assign (.proj (.local loc) f) rhs) = .ok s_mir') :
    ∃ (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = .Ok s_osea' ∧
      InvAtB L ρt' s_mir' s_osea'
        (CheckedCompilerM.run (compileStmtChecked L (.assign (.proj (.local loc) f) rhs)) cs) :=
  storereg_proj_simB compProg (fun _ _ _ h => by cases h)
    (ptrChain_lowers hWF (PtrChain.base loc))
    (fun s1 h_prep => by
      have hr : ∃ r, mirlite.resolvePlace? MSB L s_mir (.proj (.local loc) f) = some r := by
        simp [mirlite.resolvePlace?, h_env]
      obtain ⟨r, hr⟩ := hr
      simp only [mirlite.preparePlaceAssign, hr] at h_prep
      exact ⟨(mirlite.Result.ok.inj h_prep).symm, r, hr⟩)
    h_pkg h_inv h_code h_step

/-- `(*P).f := rhs`, `*P` a pointer chain. -/
theorem storereg_projchain_simB {Γ : Ctx} {L : mirlite.LayEnv Γ} {ρt : TagRenameMap}
    {s_mir s_mir' : mirlite.State MSB Γ} {s_osea : oseair.State MSB}
    {ρ τ : LayoutTy} {P : Place Γ (LayoutTy.PtrL ρ)} {f : PathTo ρ τ} {rhs : RExpr Γ τ}
    {cs : CompilerState}
    (compProg : oseair.Prog) (hWF : PtrPlacesWF L) (h_chain : PtrChain (.deref P))
    (h_pkg : ValuePkgB compProg L (mirlite.placeLayout L (.proj (.deref P) f)) rhs)
    (h_inv : InvAtB L ρt s_mir s_osea cs)
    (h_code : CodeIncludedB compProg
      (CheckedCompilerM.run (compileStmtChecked L (.assign (.proj (.deref P) f) rhs)) cs))
    (h_step : mirlite.stepStmt MSB L s_mir (.assign (.proj (.deref P) f) rhs) = .ok s_mir') :
    ∃ (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = .Ok s_osea' ∧
      InvAtB L ρt' s_mir' s_osea'
        (CheckedCompilerM.run (compileStmtChecked L (.assign (.proj (.deref P) f) rhs)) cs) :=
  storereg_proj_simB compProg (fun _ _ _ h => by cases h) (ptrChain_lowers hWF h_chain)
    (fun s1 h_prep => by
      simp only [mirlite.preparePlaceAssign] at h_prep
      split at h_prep
      · rename_i r h_r
        exact ⟨(mirlite.Result.ok.inj h_prep).symm, r, h_r⟩
      · simp [mirlite.allocateRoot] at h_prep)
    h_pkg h_inv h_code h_step

/-! ## A field of a local's first assignment -/

theorem compileStmt_freshproj_eq {Γ : Ctx} {L : mirlite.LayEnv Γ} {ρ τ : LayoutTy}
    {loc : Local Γ ρ} {f : PathTo ρ τ} {rhs : RExpr Γ τ} {cs : CompilerState}
    (h : getPlaceInfo cs loc.idx.1 = none) :
    CheckedCompilerM.run (compileStmtChecked L (.assign (.proj (.local loc) f) rhs)) cs
      = CheckedCompilerM.run (compileStmtChecked L (.assign (.proj (.local loc) f) rhs))
          (freshRootCS L cs loc) := by
  have h1 : CompilerM.run (ensurePlaceRoot L (.proj (.local loc) f)) cs = freshRootCS L cs loc := by
    simp only [ensurePlaceRoot, CompilerM.run_bind, CompilerM.run_pure, ensureLocalRegE_fresh h]
  have h2 : CompilerM.run (ensurePlaceRoot L (.proj (.local loc) f)) (freshRootCS L cs loc)
      = freshRootCS L cs loc := by
    simp only [ensurePlaceRoot, CompilerM.run_bind, CompilerM.run_pure,
      ensureLocalRegE_existing (L := L) (getPlaceInfo_freshRoot_self (L := L) cs loc)]
  simp only [compileStmtChecked, compileAssignChecked, CheckedCompilerM.run_bind,
    CheckedCompilerM.value_lift, CheckedCompilerM.run_lift]
  rw [h1, h2]

theorem stepStmt_freshproj_eq {Γ : Ctx} {L : mirlite.LayEnv Γ} {ρ τ : LayoutTy}
    {loc : Local Γ ρ} {f : PathTo ρ τ} {rhs : RExpr Γ τ} {s s1 : mirlite.State MSB Γ}
    (h_env : s.env.lookup loc = none)
    (h_alloc : mirlite.allocateBase MSB L s loc = .ok s1)
    (h_env1 : ∃ b, s1.env.lookup loc = some b) :
    mirlite.stepStmt MSB L s (.assign (.proj (.local loc) f) rhs)
      = mirlite.stepStmt MSB L s1 (.assign (.proj (.local loc) f) rhs) := by
  have h0 : mirlite.preparePlaceAssign MSB L s (.proj (.local loc) f) = .ok s1 := by
    simp only [mirlite.preparePlaceAssign, mirlite.resolvePlace?, h_env, mirlite.allocateRoot,
      h_alloc]
  have h1 : mirlite.preparePlaceAssign MSB L s1 (.proj (.local loc) f) = .ok s1 := by
    obtain ⟨b, hb⟩ := h_env1
    simp only [mirlite.preparePlaceAssign, mirlite.resolvePlace?, hb]
  simp only [mirlite.stepStmt, mirlite.doAssign, h0, h1]

/-- `x.f := rhs` with `x` not yet allocated. -/
theorem storereg_projlocalfresh_simB {Γ : Ctx} {L : mirlite.LayEnv Γ} {ρt : TagRenameMap}
    {s_mir s_mir' : mirlite.State MSB Γ} {s_osea : oseair.State MSB}
    {ρ τ : LayoutTy} {loc : Local Γ ρ} {f : PathTo ρ τ} {rhs : RExpr Γ τ} {cs : CompilerState}
    (compProg : oseair.Prog) (hWF : PtrPlacesWF L)
    (h_pkg : ValuePkgB compProg L (mirlite.placeLayout L (.proj (.local loc) f)) rhs)
    (h_inv : InvAtB L ρt s_mir s_osea cs)
    (h_code : CodeIncludedB compProg
      (CheckedCompilerM.run (compileStmtChecked L (.assign (.proj (.local loc) f) rhs)) cs))
    (h_env : s_mir.env.lookup loc = none)
    (h_step : mirlite.stepStmt MSB L s_mir (.assign (.proj (.local loc) f) rhs) = .ok s_mir') :
    ∃ (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = .Ok s_osea' ∧
      InvAtB L ρt' s_mir' s_osea'
        (CheckedCompilerM.run (compileStmtChecked L (.assign (.proj (.local loc) f) rhs)) cs) := by
  have h_pi := h_inv.unmap loc h_env
  rw [compileStmt_freshproj_eq h_pi] at h_code ⊢
  have h_prep : mirlite.preparePlaceAssign MSB L s_mir (.proj (.local loc) f)
      = mirlite.allocateBase MSB L s_mir loc := by
    simp only [mirlite.preparePlaceAssign, mirlite.resolvePlace?, h_env, mirlite.allocateRoot]
  cases h_a : mirlite.allocateBase MSB L s_mir loc with
  | err e =>
      simp only [mirlite.stepStmt, mirlite.doAssign, h_prep, h_a] at h_step
      cases h_step
  | ok s1 =>
  have h_codeF : CodeIncludedB compProg (freshRootCS L cs loc) :=
    h_code.mono (CheckedCompilerM.incr _ _)
  have h_alloc_instr : compProg s_osea.pc = some (oseair.Instr.Assgn (Register.R cs.nextReg)
      (oseair.Rhs.Alloc (L loc.idx))) := by
    rw [h_inv.pc]
    apply h_codeF
    · simp [freshRootCS, setPlaceInfo, emit]
    · simp [freshRootCS, setPlaceInfo, emit]
  obtain ⟨ρt', sA1, h_incr, h_run1, h_inv1, b, hb⟩ :=
    freshroot_prologue h_inv h_env h_a h_alloc_instr
  rw [stepStmt_freshproj_eq h_env h_a ⟨b, hb⟩] at h_step
  obtain ⟨ρt'', s', n, h_incr2, h_run2, h_inv2⟩ :=
    storereg_projlocal_simB compProg hWF hb h_pkg h_inv1 h_code h_step
  exact ⟨ρt'', s', 1 + n, h_incr.trans h_incr2, runN_trans h_run1 h_run2, h_inv2⟩

end obseq3.proof
