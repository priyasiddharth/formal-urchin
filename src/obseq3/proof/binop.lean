import obseq3.proof.common
import obseq3.proof.permsim_transport
import obseq3.proof.spine
import obseq3.proof.copy
import obseq3.proof.const_write
import obseq3.proof.alloc

/-!
# `binOp`: a REGISTER-ONLY value package

`binOp op a b : RExpr Γ NatL` reads two `NatL` places — copy's read,
twice — and combines the two words. The compiled shape is copy's read of
`a` with its register exposed (`readToReg`), copy's read of `b`, and then
ONE `Rhs.BinOp` on the two value registers: no memory, no permission
event, no new tag and no new address. The package is therefore `alloc`'s
`fromPlace` shape minus the allocation, with one extra obligation: the
FIRST operand's register must still hold its word after the SECOND read
has run. That is exactly the register frame the read packages now export
(`ReadRegPkg`, proof/copy.lean, 2026-09-24) — a read writes only
registers at or above the compiler state it started from, and the first
operand's register is below it.
-/

namespace obseq3.proof

open obseq3
open obseq3.compile
open obseq3.oseair (Instr Register Rhs Val)

variable {Γ : Ctx}

/-- copy's read touches ONLY the permission state: the second operand's
    read therefore resolves against the same env and memory as the
    first, which is what lets the package compile both reads before any
    code fact is available. -/
theorem evalCopy_state_shape {τ : LayoutTy} {M : PermissionModel}
    {s : mirlite.State M Γ} {p : Place Γ τ} {out : mirlite.EvalOutput M Γ τ}
    (h : mirlite.evalCopy M s p = .ok out) :
    out.state = { s with perms := out.state.perms } := by
  simp only [mirlite.evalCopy] at h
  split at h
  case h_1 => simp at h
  split at h
  · simp at h
  split at h
  case h_1 => simp at h
  split at h
  · simp at h
  injection h with h
  subst h
  rfl

/-- `resolvePlace?` never looks at the permissions. -/
theorem resolvePlace?_perms {τ : LayoutTy} {M : PermissionModel}
    (s : mirlite.State M Γ) (perms : M.State) (p : Place Γ τ) :
    mirlite.resolvePlace? (M := M) { s with perms := perms } p
      = mirlite.resolvePlace? (M := M) s p := by
  induction p with
  | «local» loc => rfl
  | proj base path ih => simp only [mirlite.resolvePlace?, ih]
  | deref ptr ih => simp only [mirlite.resolvePlace?, ih]

/-- `binOp` is a value package. -/
theorem binOp_valuePkg {Γ : Ctx} (op : BinOp)
    (a b : Place Γ obseq.LayoutTy.NatL) (compProg : oseair.Prog) :
    ValuePkg compProg (RExpr.binOp (Γ := Γ) op a b) := by
  intro ρa ρt sM sA csA h_id_a h_wf_t h_tbd h_lbs h_prb h_sms h_alloc h_psim h_pc
    output h_eval
  -- §1 invert the source: two reads, each a concrete word
  simp only [mirlite.evalRExpr] at h_eval
  split at h_eval
  case h_1 => simp at h_eval
  rename_i _ out1 h_copyA
  split at h_eval
  case h_2 => simp at h_eval
  rename_i x h_valsA
  split at h_eval
  case h_1 => simp at h_eval
  rename_i _ out2 h_copyB
  split at h_eval
  case h_2 => simp at h_eval
  rename_i y h_valsB
  -- the operation was not UB (`binOpUB`), or the source would have erred
  split at h_eval
  case h_1 => simp at h_eval
  rename_i h_ub
  injection h_eval with h_out
  subst h_out
  -- §2 the FIRST read, through copy's package with its register exposed
  have h_evalA : mirlite.evalRExpr MSB sM (.copy (flattenPlace a)) = .ok out1 := by
    rw [evalRExpr_copy_flatten]
    simp only [mirlite.evalRExpr]
    exact h_copyA
  obtain ⟨pOutA, h_pvalA, h_prmA, h_restA⟩ :=
    copy_readRegPkg_flat compProg a ρa ρt sM sA csA h_id_a h_wf_t h_tbd h_lbs h_prb
      h_sms h_alloc h_psim h_pc out1 h_evalA
  have h_sresA : ∃ rs permsS, mirlite.resolvePlaceAcc MSB sM a = .ok (rs, permsS) := by
    simp only [mirlite.evalCopy] at h_copyA
    cases h : mirlite.resolvePlaceAcc MSB sM a with
    | error e => rw [h] at h_copyA; simp at h_copyA
    | ok pr => exact ⟨pr.1, pr.2, rfl⟩
  obtain ⟨rsA, permsSA, h_sresA⟩ := h_sresA
  obtain ⟨aOut, hDA⟩ := placeToRegChecked_ok_of_placeInputsMapped
    (cs := csA) (kind := RefKind.Shared)
    (placeInputsMapped_of_localBindingSim_resolvePlace h_lbs
      (resolvePlace?_of_resolveAcc h_sresA))
  obtain ⟨h_afr, h_afv⟩ := readToReg_flat hDA
  -- §3 the SECOND read compiles too: `b` resolves against the env and
  -- memory the first read left untouched, so its place is mapped at the
  -- compiler state the first read ended in
  have h_shapeA := evalCopy_state_shape h_copyA
  have h_sresB : ∃ rs permsS, mirlite.resolvePlaceAcc MSB out1.state b = .ok (rs, permsS) := by
    simp only [mirlite.evalCopy] at h_copyB
    cases h : mirlite.resolvePlaceAcc MSB out1.state b with
    | error e => rw [h] at h_copyB; simp at h_copyB
    | ok pr => exact ⟨pr.1, pr.2, rfl⟩
  obtain ⟨rsB, permsSB, h_sresB⟩ := h_sresB
  have h_resB : mirlite.resolvePlace? (M := MSB) sM b = some rsB := by
    have h := resolvePlace?_of_resolveAcc h_sresB
    rw [h_shapeA, resolvePlace?_perms] at h
    exact h
  obtain ⟨bOut, hDB⟩ := placeToRegChecked_ok_of_placeInputsMapped
    (cs := CheckedCompilerM.run (readToReg a) csA) (kind := RefKind.Shared)
    (PlaceInputsMapped.placeRegMap_congr (readToReg_placeRegMap_any a csA) b
      (placeInputsMapped_of_localBindingSim_resolvePlace h_lbs h_resB))
  obtain ⟨h_bfr, h_bfv⟩ := readToReg_flat hDB
  -- §4 the compiled shape: the two reads, then the one `BinOp`
  have h_pre : CheckedCompilerM.run
      (compileRExprPreChecked (RExpr.binOp (Γ := Γ) op a b)) csA
      = emit { (CheckedCompilerM.run (readToReg b)
            (CheckedCompilerM.run (readToReg a) csA)) with
          nextReg := (CheckedCompilerM.run (readToReg b)
            (CheckedCompilerM.run (readToReg a) csA)).nextReg + 1 }
        [Instr.Assgn (Register.R (CheckedCompilerM.run (readToReg b)
            (CheckedCompilerM.run (readToReg a) csA)).nextReg)
          (Rhs.BinOp op
            (Register.R (CheckedCompilerM.run
              (placeToRegChecked RefKind.Shared (flattenPlace a)) csA).nextReg)
            (Register.R (CheckedCompilerM.run
              (placeToRegChecked RefKind.Shared (flattenPlace b))
              (CheckedCompilerM.run (readToReg a) csA)).nextReg))] := by
    simp only [compileRExprPreChecked, csMonad, csRun, h_afv, h_bfv]
  refine ⟨fun d => Instr.RStore obseq.TyVal.NatTy
      (Register.R (CheckedCompilerM.run (readToReg b)
        (CheckedCompilerM.run (readToReg a) csA)).nextReg) d,
    { store := fun d => [Instr.RStore obseq.TyVal.NatTy
        (Register.R (CheckedCompilerM.run (readToReg b)
          (CheckedCompilerM.run (readToReg a) csA)).nextReg) d],
      postCleanup := [],
      ev := fun _ => RExprToEvidence.binOp op a b
        (Register.R (CheckedCompilerM.run
          (placeToRegChecked RefKind.Shared (flattenPlace a)) csA).nextReg)
        (Register.R (CheckedCompilerM.run
          (placeToRegChecked RefKind.Shared (flattenPlace b))
          (CheckedCompilerM.run (readToReg a) csA)).nextReg)
        (Register.R (CheckedCompilerM.run (readToReg b)
          (CheckedCompilerM.run (readToReg a) csA)).nextReg) },
    by simp only [compileRExprPreChecked, csMonad, csRun, h_afv, h_bfv],
    fun _ => rfl, rfl,
    by rw [h_pre]; simp only [emit]
       rw [readToReg_placeRegMap_any b, readToReg_placeRegMap_any a], ?_⟩
  intro h_code
  -- §5 the first read's run
  have h_codeA : CodeIncluded compProg
      (CheckedCompilerM.run (compileRExprPreChecked (.copy (flattenPlace a))) csA) := by
    rw [← h_afr]
    refine h_code.mono ?_
    rw [h_pre]
    exact StateIncr.trans (CheckedCompilerM.incr (readToReg b) _)
      (StateIncr.trans (freshReg_state_incr _) (emit_state_incr _ _))
  obtain ⟨ρt1, nR1, sR1, perms₁, vals1, h_incrT1, h_wfT1, h_ostA, -, h_runA, h_regmonoA,
    h_lbsA, h_psimA, h_tbdA, h_smemA, h_pcA, h_vregA, h_valsRelA, h_vbelowA, h_frameA⟩ :=
    h_restA h_codeA
  rw [h_valsA] at h_valsRelA
  have h_vals1 := ListRel_word_inv h_valsRelA
  subst h_vals1
  rw [← h_afr] at h_regmonoA h_lbsA h_pcA h_vbelowA
  -- §6 the second read's run, at the post-first-read states
  have h_codeB : CodeIncluded compProg
      (CheckedCompilerM.run (compileRExprPreChecked (.copy (flattenPlace b)))
        (CheckedCompilerM.run (readToReg a) csA)) := by
    rw [← h_bfr]
    refine h_code.mono ?_
    rw [h_pre]
    exact StateIncr.trans (freshReg_state_incr _) (emit_state_incr _ _)
  have h_evalB : mirlite.evalRExpr MSB { sM with perms := perms₁ }
      (.copy (flattenPlace b)) = .ok out2 := by
    rw [evalRExpr_copy_flatten]
    simp only [mirlite.evalRExpr]
    rw [← h_ostA]
    exact h_copyB
  obtain ⟨pOutB, h_pvalB, h_prmB, h_restB⟩ :=
    copy_readRegPkg_flat compProg b ρa ρt1 { sM with perms := perms₁ } sR1
      (CheckedCompilerM.run (readToReg a) csA) h_id_a h_wfT1 h_tbdA h_lbsA
      (by
        intro idx reg τ' h_look
        rw [getPlaceInfo_congr' (readToReg_placeRegMap_any a csA)] at h_look
        exact RegisterBelow.mono h_regmonoA (h_prb idx reg τ' h_look))
      (SourceMemSim.of_mem_eq (AddrRenameIncr.refl ρa) h_incrT1 h_sms h_smemA)
      (AllocLockstep.of_mem_eq h_alloc h_smemA) h_psimA h_pcA out2 h_evalB
  obtain ⟨ρt2, nR2, sR2, perms₂, vals2, h_incrT2, h_wfT2, h_ostB, -, h_runB, h_regmonoB,
    h_lbsB, h_psimB, h_tbdB, h_smemB, h_pcB, h_vregB, h_valsRelB, h_vbelowB, h_frameB⟩ :=
    h_restB h_codeB
  rw [h_valsB] at h_valsRelB
  have h_vals2 := ListRel_word_inv h_valsRelB
  subst h_vals2
  rw [← h_bfr] at h_regmonoB h_lbsB h_pcB h_vbelowB
  -- the FIRST operand's register survived the second read
  have h_vregA' : oseair.RegMap.lookup sR2.reg
      (Register.R (CheckedCompilerM.run
        (placeToRegChecked RefKind.Shared (flattenPlace a)) csA).nextReg)
      = some (layoutToTyVal obseq.LayoutTy.NatL, [Val.Dat x]) := by
    rw [h_frameB _ h_vbelowA]
    exact h_vregA
  -- §7 the `BinOp` step
  have h_code0 : compProg sR2.pc
      = some (Instr.Assgn (Register.R (CheckedCompilerM.run (readToReg b)
            (CheckedCompilerM.run (readToReg a) csA)).nextReg)
          (Rhs.BinOp op
            (Register.R (CheckedCompilerM.run
              (placeToRegChecked RefKind.Shared (flattenPlace a)) csA).nextReg)
            (Register.R (CheckedCompilerM.run
              (placeToRegChecked RefKind.Shared (flattenPlace b))
              (CheckedCompilerM.run (readToReg a) csA)).nextReg))) := by
    rw [h_pcB]
    refine h_code _ _ ?_ ?_
    · rw [h_pre]; simp [emit]
    · rw [h_pre]
      have h := emit_code_at_new
        { (CheckedCompilerM.run (readToReg b)
            (CheckedCompilerM.run (readToReg a) csA)) with
          nextReg := (CheckedCompilerM.run (readToReg b)
            (CheckedCompilerM.run (readToReg a) csA)).nextReg + 1 }
        [Instr.Assgn (Register.R (CheckedCompilerM.run (readToReg b)
            (CheckedCompilerM.run (readToReg a) csA)).nextReg)
          (Rhs.BinOp op
            (Register.R (CheckedCompilerM.run
              (placeToRegChecked RefKind.Shared (flattenPlace a)) csA).nextReg)
            (Register.R (CheckedCompilerM.run
              (placeToRegChecked RefKind.Shared (flattenPlace b))
              (CheckedCompilerM.run (readToReg a) csA)).nextReg))]
        (k := 0) (by simp)
      simpa using h
  have h_run3 := runN_Assgn_BinOp_step compProg sR2 _ _ _ op _ _ x y
    h_code0 h_vregA' h_vregB h_ub
  -- §8 the tail: no memory, no tag, no address — everything transports
  rw [h_pre]
  have h_prm : (emit { (CheckedCompilerM.run (readToReg b)
        (CheckedCompilerM.run (readToReg a) csA)) with
      nextReg := (CheckedCompilerM.run (readToReg b)
        (CheckedCompilerM.run (readToReg a) csA)).nextReg + 1 }
    [Instr.Assgn (Register.R (CheckedCompilerM.run (readToReg b)
        (CheckedCompilerM.run (readToReg a) csA)).nextReg)
      (Rhs.BinOp op
        (Register.R (CheckedCompilerM.run
          (placeToRegChecked RefKind.Shared (flattenPlace a)) csA).nextReg)
        (Register.R (CheckedCompilerM.run
          (placeToRegChecked RefKind.Shared (flattenPlace b))
          (CheckedCompilerM.run (readToReg a) csA)).nextReg))]).placeRegMap
      = csA.placeRegMap := by
    simp only [emit]
    rw [readToReg_placeRegMap_any b, readToReg_placeRegMap_any a]
  refine ⟨ρa, ρt2, nR1 + nR2 + 1, _, sM.mem, perms₂,
    [Val.Dat (evalBinOp op x y)],
    AddrRenameIncr.refl ρa, h_id_a, TagRenameIncr.trans h_incrT1 h_incrT2, h_wfT2,
    by rw [h_ostB], rfl,
    oseair_runN_trans (oseair_runN_trans h_runA h_runB) h_run3,
    h_prm,
    (by
      refine Nat.le_trans h_regmonoA (Nat.le_trans h_regmonoB ?_)
      simp only [emit]
      omega),
    ?_,
    h_psimB, h_tbdB,
    SourceMemSim.of_mem_eq (AddrRenameIncr.refl ρa)
      (TagRenameIncr.trans h_incrT1 h_incrT2) h_sms
      (by show sR2.mem = sA.mem; rw [h_smemB, h_smemA]),
    AllocLockstep.of_mem_eq h_alloc (by show sR2.mem = sA.mem; rw [h_smemB, h_smemA]),
    (by
      show sR2.pc + 1 = _
      rw [h_pcB]
      simp only [emit, List.length_cons, List.length_nil]),
    StoreStep.rstore compProg _ _ obseq.TyVal.NatTy _ _
      (RegMap.lookup_insert_self _ _ _)
      (by simp only [emit, RegisterBelow]; omega),
    ⟨rfl, trivial⟩⟩
  -- the locals: the `BinOp` writes one FRESH register
  refine LocalBindingSim.placeRegMap_congr (cs := CheckedCompilerM.run (readToReg b)
      (CheckedCompilerM.run (readToReg a) csA)) (by simp only [emit]) ?_
  exact LocalBindingSim.insert_fresh_reg h_lbsB
    (by
      intro idx reg τ' h_look
      rw [getPlaceInfo_congr' (readToReg_placeRegMap_any b _),
        getPlaceInfo_congr' (readToReg_placeRegMap_any a csA)] at h_look
      exact RegisterBelow.mono (Nat.le_trans h_regmonoA h_regmonoB) (h_prb idx reg τ' h_look))
    (Nat.le_refl _) rfl

end obseq3.proof
