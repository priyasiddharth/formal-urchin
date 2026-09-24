import obseq3.proof.common
import obseq3.proof.permsim_transport
import obseq3.proof.spine
import obseq3.proof.copy
import obseq3.proof.const_write
import obseq3.proof.alloc
import obseq3.proof.dealloc

/-!
# `sliceLen`: slice metadata as a REGISTER-ONLY value package

`sliceLen p : RExpr Γ NatL` reads the fat pointer in `p` — copy's read,
once — and stores the length the pointer CLAIMS, in elements: its extent
divided by the element's block size. The compiled shape is copy's read
with its register exposed (`readToReg`) and one `Rhs.SliceLen` on the
value register: no memory, no permission event, no tag and no address.

So the package is `binOp`'s with ONE read instead of two, and the
extent survives the read because `MemValSim`'s pointer clause carries it
(`e' = e`, durable/pointer-values-carry-an-extent.md): the word the
target computes is the word mirlite computed, by construction.
-/

namespace obseq3.proof

open obseq3
open obseq3.compile
open obseq3.oseair (Instr Register Rhs Val)

variable {Γ : Ctx}

/-- `sliceLen` is a value package. -/
theorem sliceLen_valuePkg {Γ : Ctx} {σ : LayoutTy}
    (src : Place Γ (obseq.LayoutTy.PtrL σ)) (compProg : oseair.Prog) :
    ValuePkg compProg (RExpr.sliceLen (Γ := Γ) src) := by
  intro ρa ρt sM sA csA h_id_a h_wf_t h_tbd h_lbs h_prb h_sms h_alloc h_psim h_pc
    output h_eval
  -- §1 invert the source: one read, a pointer value
  simp only [mirlite.evalRExpr] at h_eval
  split at h_eval
  case h_1 => simp at h_eval
  rename_i _ out1 h_copy
  split at h_eval
  case h_2 => simp at h_eval
  rename_i b o e sz tag h_vals
  injection h_eval with h_out
  subst h_out
  -- §2 the read, through copy's package with its register exposed
  have h_evalC : mirlite.evalRExpr MSB sM (.copy (flattenPlace src)) = .ok out1 := by
    rw [evalRExpr_copy_flatten]
    simp only [mirlite.evalRExpr]
    exact h_copy
  obtain ⟨pOutC, h_pvalC, h_prmC, h_restC⟩ :=
    copy_readRegPkg_flat compProg src ρa ρt sM sA csA h_id_a h_wf_t h_tbd h_lbs h_prb
      h_sms h_alloc h_psim h_pc out1 h_evalC
  have h_sres : ∃ rs permsS, mirlite.resolvePlaceAcc MSB sM src = .ok (rs, permsS) := by
    simp only [mirlite.evalCopy] at h_copy
    cases h : mirlite.resolvePlaceAcc MSB sM src with
    | error err => rw [h] at h_copy; simp at h_copy
    | ok pr => exact ⟨pr.1, pr.2, rfl⟩
  obtain ⟨rs, permsS, h_sres⟩ := h_sres
  obtain ⟨sOut, hD⟩ := placeToRegChecked_ok_of_placeInputsMapped
    (cs := csA) (kind := RefKind.Shared)
    (placeInputsMapped_of_localBindingSim_resolvePlace h_lbs
      (resolvePlace?_of_resolveAcc h_sres))
  obtain ⟨h_fr, h_fv⟩ := readToReg_flat hD
  -- §3 the compiled shape: the read, then the one `SliceLen`
  have h_pre : CheckedCompilerM.run
      (compileRExprPreChecked (RExpr.sliceLen (Γ := Γ) src)) csA
      = emit { (CheckedCompilerM.run (readToReg src) csA) with
          nextReg := (CheckedCompilerM.run (readToReg src) csA).nextReg + 1 }
        [Instr.Assgn (Register.R (CheckedCompilerM.run (readToReg src) csA).nextReg)
          (Rhs.SliceLen (layoutToTyVal σ)
            (Register.R (CheckedCompilerM.run
              (placeToRegChecked RefKind.Shared (flattenPlace src)) csA).nextReg))] := by
    simp only [compileRExprPreChecked, csMonad, csRun, h_fv]
  refine ⟨fun d => Instr.RStore obseq.TyVal.NatTy
      (Register.R (CheckedCompilerM.run (readToReg src) csA).nextReg) d,
    { store := fun d => [Instr.RStore obseq.TyVal.NatTy
        (Register.R (CheckedCompilerM.run (readToReg src) csA).nextReg) d],
      postCleanup := [],
      ev := fun _ => RExprToEvidence.sliceLen src
        (Register.R (CheckedCompilerM.run
          (placeToRegChecked RefKind.Shared (flattenPlace src)) csA).nextReg)
        (Register.R (CheckedCompilerM.run (readToReg src) csA).nextReg) },
    by simp only [compileRExprPreChecked, csMonad, csRun, h_fv],
    fun _ => rfl, rfl,
    by rw [h_pre]; simp only [emit]; rw [readToReg_placeRegMap_any src], ?_⟩
  intro h_code
  -- §4 the read's run
  have h_codeR : CodeIncluded compProg
      (CheckedCompilerM.run (compileRExprPreChecked (.copy (flattenPlace src))) csA) := by
    rw [← h_fr]
    refine h_code.mono ?_
    rw [h_pre]
    exact StateIncr.trans (freshReg_state_incr _) (emit_state_incr _ _)
  obtain ⟨ρt1, nR, sR, perms₁, vals, h_incrT, h_wfT, h_ost, -, h_runR, h_regmono,
    h_lbsR, h_psimR, h_tbdR, h_smem, h_pcR, h_vreg, h_valsRel, h_vbelow, h_frameR⟩ :=
    h_restC h_codeR
  rw [h_vals] at h_valsRel
  obtain ⟨b', tag', h_valsE, h_rb, h_rt⟩ := ListRel_ptr_inv h_valsRel
  subst h_valsE
  rw [← h_fr] at h_regmono h_lbsR h_pcR h_vbelow
  -- §5 the `SliceLen` step: the extent crossed the read unchanged, so
  -- the target divides the SAME extent by the same element size
  have h_code0 : compProg sR.pc
      = some (Instr.Assgn (Register.R (CheckedCompilerM.run (readToReg src) csA).nextReg)
          (Rhs.SliceLen (layoutToTyVal σ)
            (Register.R (CheckedCompilerM.run
              (placeToRegChecked RefKind.Shared (flattenPlace src)) csA).nextReg))) := by
    rw [h_pcR]
    refine h_code _ _ ?_ ?_
    · rw [h_pre]; simp [emit]
    · rw [h_pre]
      have h := emit_code_at_new
        { (CheckedCompilerM.run (readToReg src) csA) with
          nextReg := (CheckedCompilerM.run (readToReg src) csA).nextReg + 1 }
        [Instr.Assgn (Register.R (CheckedCompilerM.run (readToReg src) csA).nextReg)
          (Rhs.SliceLen (layoutToTyVal σ)
            (Register.R (CheckedCompilerM.run
              (placeToRegChecked RefKind.Shared (flattenPlace src)) csA).nextReg))]
        (k := 0) (by simp)
      simpa using h
  have h_run2 := runN_Assgn_SliceLen_step compProg sR _ _ _ _ b' o e sz tag'
    h_code0 h_vreg
  have h_ts : obseq.typeSize (layoutToTyVal σ) = blockSize σ :=
    obseq.typeSize_layoutToTyVal _
  rw [h_ts] at h_run2
  -- §6 the tail: nothing grew — not memory, not a tag, not an address
  rw [h_pre]
  refine ⟨ρa, ρt1, nR + 1, _, sM.mem, perms₁, [Val.Dat (e / blockSize σ)],
    AddrRenameIncr.refl ρa, h_id_a, h_incrT, h_wfT,
    by rw [h_ost], rfl,
    oseair_runN_trans h_runR h_run2,
    (by simp only [emit]; rw [readToReg_placeRegMap_any src]),
    (by
      refine Nat.le_trans h_regmono ?_
      simp only [emit]
      omega),
    ?_,
    h_psimR, h_tbdR,
    SourceMemSim.of_mem_eq (AddrRenameIncr.refl ρa) h_incrT h_sms
      (by show sR.mem = sA.mem; exact h_smem),
    AllocLockstep.of_mem_eq h_alloc (by show sR.mem = sA.mem; exact h_smem),
    (by
      show sR.pc + 1 = _
      rw [h_pcR]
      simp only [emit, List.length_cons, List.length_nil]),
    StoreStep.rstore compProg _ _ obseq.TyVal.NatTy _ _
      (RegMap.lookup_insert_self _ _ _)
      (by simp only [emit, RegisterBelow]; omega),
    ⟨rfl, trivial⟩⟩
  -- the locals: the `SliceLen` writes one FRESH register
  refine LocalBindingSim.placeRegMap_congr
    (cs := CheckedCompilerM.run (readToReg src) csA) (by simp only [emit]) ?_
  exact LocalBindingSim.insert_fresh_reg h_lbsR
    (by
      intro idx reg τ' h_look
      rw [getPlaceInfo_congr' (readToReg_placeRegMap_any src csA)] at h_look
      exact RegisterBelow.mono h_regmono (h_prb idx reg τ' h_look))
    (Nat.le_refl _) rfl

end obseq3.proof
