import obseq2.proof.common

namespace obseq2.proof

open obseq2
open obseq2.compile
open obseq2.oseair (Instr Register Rhs Val)

theorem CompilerInv_step_constInit
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq2.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_mir' : obseq2.mirlite.State PermissionModel.stackedBorrows Γ}
    {s_osea : oseair.State}
    {dst : Place Γ obseq.LayoutTy.NatL}
    (v : Word)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    (h_stmt : prog.get? s_mir.pc = some (.assign dst (.constInit v)))
    (h_step : obseq2.mirlite.stepStmt PermissionModel.stackedBorrows s_mir
                (.assign dst (.constInit v)) = .ok s_mir') :
    ∃ (s_osea' : oseair.State) (n : Nat),
      oseair.runN n s_osea (compileProgFrom cs0 prog) = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa ρt s_mir' s_osea' := by
  obtain ⟨h_pc, h_wf, h_tlr, h_lbs, h_sms, h_ap, h_wf_perms⟩ := h_inv
  simp only [obseq2.mirlite.stepStmt, obseq2.mirlite.evalRExpr] at h_step
  -- h_step : finishPlaceAssign M s_mir dst [MemValue.word v] rfl = .ok s_mir'
  have h_memval : MemValSim ρa ρt (obseq2.mirlite.MemValue.word v) (Val.Dat v) := rfl
  simp only [obseq2.mirlite.finishPlaceAssign] at h_step
  split at h_step
  · -- resolvePlace? s_mir dst = some resolved → writeResolvedPlace.
    rename_i resolved h_res
    let cs_cur := csAt cs0 prog s_mir.pc
    let dstRes := placeToReg cs_cur .Mut dst
    let fragLen := dstRes.cs.nextLabel - cs_cur.nextLabel
    have h_cs_cur_wf : CompilerStateWF Γ cs_cur := by
      simpa [cs_cur, csAt] using h_wf
    -- Slice condition: fragInstrs appears at s_osea.pc in compileProgFrom.
    have h_slice : ∀ (i : Fin fragLen),
        (compileProgFrom cs0 prog) (s_osea.pc + i.1) =
        dstRes.cs.code (cs_cur.nextLabel + i.1) := by
      intro i
      have h_q_eq : s_osea.pc + i.1 = cs_cur.nextLabel + i.1 := by
        simp [h_pc, targetPcAt, cs_cur, csAt]
      have h_q_lt_dst : s_osea.pc + i.1 < dstRes.cs.nextLabel := by
        have h_i := i.2
        simp [fragLen, h_q_eq] at h_i ⊢
        omega
      have h_q_lt_stmt :
          s_osea.pc + i.1 <
            (compileStmt cs_cur (.assign dst (.constInit v))).nextLabel := by
        have h_dst_stmt :
            dstRes.cs.nextLabel ≤
              (compileStmt cs_cur (.assign dst (.constInit v))).nextLabel := by
          simp [compileStmt, compileRExprTo, dstRes, emit]
          omega
        exact Nat.lt_of_lt_of_le h_q_lt_dst h_dst_stmt
      have h_prog :=
        compileProgFrom_code_eq_compileStmt
          (cs0 := cs0) (prog := prog) (stmt := .assign dst (.constInit v))
          h_stmt (q := s_osea.pc + i.1) h_q_lt_stmt
      rw [h_prog, h_q_eq]
      have h_after_cstore :
          (compileRExprTo (Γ := Γ) dstRes.cs dstRes.reg (.constInit v)).code
              (cs_cur.nextLabel + i.1) =
            dstRes.cs.code (cs_cur.nextLabel + i.1) := by
        simpa [compileRExprTo] using
          emit_code_lt_nextLabel dstRes.cs
            [Instr.CStore obseq.TyVal.NatTy [Val.Dat v] dstRes.reg]
            (by simpa [h_q_eq] using h_q_lt_dst)
      have h_q_lt_after_cstore :
          cs_cur.nextLabel + i.1 <
            (compileRExprTo (Γ := Γ) dstRes.cs dstRes.reg (.constInit v)).nextLabel := by
        exact Nat.lt_of_lt_of_le (by simpa [h_q_eq] using h_q_lt_dst)
          (compileRExprTo_state_incr dstRes.cs dstRes.reg (.constInit v)).nextLabel_le
      have h_after_cleanup :
          (emit (compileRExprTo (Γ := Γ) dstRes.cs dstRes.reg (.constInit v))
              (cleanupInstrs dstRes.cleanup)).code (cs_cur.nextLabel + i.1) =
            (compileRExprTo (Γ := Γ) dstRes.cs dstRes.reg (.constInit v)).code
              (cs_cur.nextLabel + i.1) :=
        emit_code_lt_nextLabel
          (compileRExprTo (Γ := Γ) dstRes.cs dstRes.reg (.constInit v))
          (cleanupInstrs dstRes.cleanup)
          h_q_lt_after_cstore
      simpa [compileStmt, dstRes] using h_after_cleanup.trans h_after_cstore
    -- Phase 1: placeToReg fragment runs directly via runN on compileProgFrom.
    obtain ⟨s_osea1, h_run1, h_ptr, h_mem1, h_pc1, h_regs1⟩ :=
      placeToReg_correct cs_cur .Mut dst (compileProgFrom cs0 prog)
        h_lbs h_sms h_cs_cur_wf (h_ap ▸ h_wf_perms) h_slice h_res
    -- placeToReg does not write memory; lift SourceMemSim to s_osea1.
    have h_sms1 : SourceMemSim ρa ρt s_mir.mem s_osea1.mem := h_mem1 ▸ h_sms
    -- Phase 2: CStore [Dat v] via writeThroughPtr simulates writeResolvedPlace.
    obtain ⟨s_osea2, h_wtp, h_sms2, h_reg2, h_pc2⟩ :=
      writeThroughPtr_sim ρa ρt v h_ptr h_sms1 h_step
    -- CStore is at s_osea1.pc in compileProgFrom.
    have h_cstore_instr :
        (compileProgFrom cs0 prog) s_osea1.pc =
        some (Instr.CStore obseq.TyVal.NatTy [Val.Dat v] dstRes.reg) := by
      have h_q_eq_dst : s_osea1.pc = dstRes.cs.nextLabel := by
        have h_start : s_osea.pc = cs_cur.nextLabel := by
          simpa [targetPcAt, cs_cur, csAt] using h_pc
        have h_ge := (placeToReg_state_incr cs_cur RefKind.Mut dst).nextLabel_le
        calc
          s_osea1.pc = s_osea.pc + (dstRes.cs.nextLabel - cs_cur.nextLabel) := h_pc1
          _ = cs_cur.nextLabel + (dstRes.cs.nextLabel - cs_cur.nextLabel) := by rw [h_start]
          _ = dstRes.cs.nextLabel := Nat.add_sub_of_le h_ge
      have h_q_lt_stmt :
          s_osea1.pc <
            (compileStmt cs_cur (.assign dst (.constInit v))).nextLabel := by
        simp [h_q_eq_dst, compileStmt, compileRExprTo, dstRes, emit]
        omega
      have h_prog :=
        compileProgFrom_code_eq_compileStmt
          (cs0 := cs0) (prog := prog) (stmt := .assign dst (.constInit v))
          h_stmt (q := s_osea1.pc) h_q_lt_stmt
      have h_cstore_local :
          (compileRExprTo (Γ := Γ) dstRes.cs dstRes.reg (.constInit v)).code
              dstRes.cs.nextLabel =
            some (Instr.CStore obseq.TyVal.NatTy [Val.Dat v] dstRes.reg) := by
        simp [compileRExprTo, emit]
      have h_q_lt_after_cstore :
          dstRes.cs.nextLabel <
            (compileRExprTo (Γ := Γ) dstRes.cs dstRes.reg (.constInit v)).nextLabel := by
        simp [compileRExprTo, emit]
      have h_cleanup_pres :
          (emit (compileRExprTo (Γ := Γ) dstRes.cs dstRes.reg (.constInit v))
              (cleanupInstrs dstRes.cleanup)).code dstRes.cs.nextLabel =
            (compileRExprTo (Γ := Γ) dstRes.cs dstRes.reg (.constInit v)).code
              dstRes.cs.nextLabel :=
        emit_code_lt_nextLabel
          (compileRExprTo (Γ := Γ) dstRes.cs dstRes.reg (.constInit v))
          (cleanupInstrs dstRes.cleanup)
          h_q_lt_after_cstore
      rw [h_prog, h_q_eq_dst]
      simpa [compileStmt, dstRes] using h_cleanup_pres.trans h_cstore_local
    have h_step2 : oseair.runN 1 s_osea1 (compileProgFrom cs0 prog) =
        oseair.Result.Ok s_osea2 :=
      runN_CStore_step (compileProgFrom cs0 prog) s_osea1 s_osea2
        obseq.TyVal.NatTy [Val.Dat v] dstRes.reg h_cstore_instr rfl h_wtp
    -- Combine phases 1 and 2.
    have h12 : oseair.runN (fragLen + 1) s_osea (compileProgFrom cs0 prog) =
        oseair.Result.Ok s_osea2 :=
      (oseair_runN_add fragLen 1 s_osea (compileProgFrom cs0 prog)
        s_osea1 h_run1).trans h_step2
    -- Phase 3: Die cleanup.
    have h_die_instrs : ∀ (i : Fin (cleanupInstrs dstRes.cleanup).length),
        (compileProgFrom cs0 prog) (s_osea2.pc + i.1) =
        some ((cleanupInstrs dstRes.cleanup).get i) := by
      intro i
      have h_start : s_osea.pc = cs_cur.nextLabel := by
        simpa [targetPcAt, cs_cur, csAt] using h_pc
      have h_dst_pc : s_osea1.pc = dstRes.cs.nextLabel := by
        have h_ge := (placeToReg_state_incr cs_cur RefKind.Mut dst).nextLabel_le
        calc
          s_osea1.pc = s_osea.pc + (dstRes.cs.nextLabel - cs_cur.nextLabel) := h_pc1
          _ = cs_cur.nextLabel + (dstRes.cs.nextLabel - cs_cur.nextLabel) := by rw [h_start]
          _ = dstRes.cs.nextLabel := Nat.add_sub_of_le h_ge
      have h_cleanup_pc : s_osea2.pc = dstRes.cs.nextLabel + 1 := by
        calc
          s_osea2.pc = s_osea1.pc + 1 := h_pc2
          _ = dstRes.cs.nextLabel + 1 := by rw [h_dst_pc]
      have h_q_eq : s_osea2.pc + i.1 = dstRes.cs.nextLabel + 1 + i.1 := by
        rw [h_cleanup_pc]
      have h_q_lt_stmt :
          s_osea2.pc + i.1 <
            (compileStmt cs_cur (.assign dst (.constInit v))).nextLabel := by
        have h_i := i.2
        simp [h_q_eq, compileStmt, compileRExprTo, dstRes, emit] at h_i ⊢
      have h_prog :=
        compileProgFrom_code_eq_compileStmt
          (cs0 := cs0) (prog := prog) (stmt := .assign dst (.constInit v))
          h_stmt (q := s_osea2.pc + i.1) h_q_lt_stmt
      have h_cleanup_local :
          (emit (compileRExprTo (Γ := Γ) dstRes.cs dstRes.reg (.constInit v))
              (cleanupInstrs dstRes.cleanup)).code (s_osea2.pc + i.1) =
            some ((cleanupInstrs dstRes.cleanup).get i) := by
        rw [h_q_eq]
        simp [compileRExprTo, emit, i.2]
      rw [h_prog]
      simpa [compileStmt, dstRes] using h_cleanup_local
    obtain ⟨s_osea_final, h_cleanup, h_mem_final, h_reg_final, h_pc_final⟩ :=
      runN_cleanupInstrs (compileProgFrom cs0 prog) s_osea2
        dstRes.cleanup h_die_instrs
    let diesLen := (cleanupInstrs dstRes.cleanup).length
    -- Combine (phases 1+2) and phase 3.
    have h123 : oseair.runN (fragLen + 1 + diesLen) s_osea
        (compileProgFrom cs0 prog) = oseair.Result.Ok s_osea_final :=
      (oseair_runN_add (fragLen + 1) diesLen s_osea (compileProgFrom cs0 prog)
        s_osea2 h12).trans h_cleanup
    -- Reconstruct CompilerInv for s_mir'.
    refine ⟨s_osea_final, fragLen + 1 + diesLen, h123, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · sorry  -- PC: s_osea_final.pc = targetPcAt cs0 prog s_mir'.pc
    · sorry  -- CompilerStateWF for prefix at s_mir'.pc
    · sorry  -- TargetLocalsReady: constInit leaves locals intact
    · sorry  -- LocalBindingSim: writeResolvedPlace doesn't change env
    · rw [h_mem_final]; exact h_sms2
    · sorry  -- ap = perms: Die cleanup restores ap after useMut
    · sorry  -- WellFormed s_mir'.perms
  · -- resolvePlace? s_mir dst = none → dst must be a fresh local.
    split at h_step
    · -- dst = .local loc → allocateBaseAndWrite.
      sorry
    · simp at h_step   -- .proj _: .err ≠ .ok
    · simp at h_step   -- .deref _: .err ≠ .ok

end obseq2.proof
