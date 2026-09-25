import obseq3.proof.common
import obseq3.proof.permsim_transport
import obseq3.proof.spine
import obseq3.proof.copy
import obseq3.proof.const_write
import obseq3.proof.alloc
import obseq3.proof.dealloc
import obseq3.proof.binop

/-!
# `sliceLen`: slice metadata as a REGISTER-ONLY value package

`sliceLen p : RExpr Γ NatL` reads the fat pointer in `p` — copy's read,
once — and stores the length the pointer CLAIMS, in elements: its extent
divided by the element's block size. `subSlice p lo hi` reads the same
pointer and two bounds — three copy reads — and stores the pointer
narrowed to those elements. The compiled shape is copy's read
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

/-! ## `subSlice`: the same package with THREE reads

Narrowing is pure pointer arithmetic on the values three reads exposed:
the same allocation, the same tag, the offset moved by `lo` elements and
the extent cut to `hi − lo`. No retag (the borrow around a sub-slice is
its own rvalue), no memory event, and neither renaming grows — so the
tail is `sliceLen`'s with a pointer in place of a word, and the only new
work is carrying the FIRST two operands' registers across the reads that
follow them (the register frame the read packages export). -/

/-- `subSlice` is a value package. -/
theorem subSlice_valuePkg {Γ : Ctx} {σ : LayoutTy}
    (src : Place Γ (obseq.LayoutTy.PtrL σ)) (lo hi : Place Γ obseq.LayoutTy.NatL)
    (compProg : oseair.Prog) :
    ValuePkg compProg (RExpr.subSlice (Γ := Γ) src lo hi) := by
  intro ρa ρt sM sA csA h_id_a h_wf_t h_tbd h_lbs h_prb h_sms h_alloc h_psim h_pc
    output h_eval
  -- §1 invert the source: three reads, a pointer and two words, in range
  simp only [mirlite.evalRExpr] at h_eval
  split at h_eval
  case h_1 => simp at h_eval
  rename_i _ out1 h_copyP
  split at h_eval
  case h_2 => simp at h_eval
  rename_i b o e sz tag h_valsP
  split at h_eval
  case h_1 => simp at h_eval
  rename_i _ out2 h_copyL
  split at h_eval
  case h_2 => simp at h_eval
  rename_i l h_valsL
  split at h_eval
  case h_1 => simp at h_eval
  rename_i _ out3 h_copyH
  split at h_eval
  case h_2 => simp at h_eval
  rename_i h h_valsH
  split at h_eval
  case isTrue => simp at h_eval
  rename_i h_fit
  injection h_eval with h_out
  subst h_out
  -- §2 the pointer read
  have h_evalP : mirlite.evalRExpr MSB sM (.copy (flattenPlace src)) = .ok out1 := by
    rw [evalRExpr_copy_flatten]; simp only [mirlite.evalRExpr]; exact h_copyP
  obtain ⟨pOutP, h_pvalP, h_prmP, h_restP⟩ :=
    copy_readRegPkg_flat compProg src ρa ρt sM sA csA h_id_a h_wf_t h_tbd h_lbs h_prb
      h_sms h_alloc h_psim h_pc out1 h_evalP
  have h_sresP : ∃ rs permsS, mirlite.resolvePlaceAcc MSB sM src = .ok (rs, permsS) := by
    simp only [mirlite.evalCopy] at h_copyP
    cases hh : mirlite.resolvePlaceAcc MSB sM src with
    | error err => rw [hh] at h_copyP; simp at h_copyP
    | ok pr => exact ⟨pr.1, pr.2, rfl⟩
  obtain ⟨rsP, permsP, h_sresP⟩ := h_sresP
  obtain ⟨sOutP, hDP⟩ := placeToRegChecked_ok_of_placeInputsMapped
    (cs := csA) (kind := RefKind.Shared)
    (placeInputsMapped_of_localBindingSim_resolvePlace h_lbs
      (resolvePlace?_of_resolveAcc h_sresP))
  obtain ⟨h_pfr, h_pfv⟩ := readToReg_flat hDP
  -- §3 both bounds compile too: every read leaves env, memory and the
  -- place map alone, so their roots are mapped at the states that follow
  have h_shapeP := evalCopy_state_shape h_copyP
  have h_shapeL := evalCopy_state_shape h_copyL
  have h_sresL : ∃ rs permsS, mirlite.resolvePlaceAcc MSB out1.state lo = .ok (rs, permsS) := by
    simp only [mirlite.evalCopy] at h_copyL
    cases hh : mirlite.resolvePlaceAcc MSB out1.state lo with
    | error err => rw [hh] at h_copyL; simp at h_copyL
    | ok pr => exact ⟨pr.1, pr.2, rfl⟩
  obtain ⟨rsL, permsL, h_sresL⟩ := h_sresL
  have h_resL : mirlite.resolvePlace? (M := MSB) sM lo = some rsL := by
    have hh := resolvePlace?_of_resolveAcc h_sresL
    rw [h_shapeP, resolvePlace?_perms] at hh
    exact hh
  obtain ⟨sOutL, hDL⟩ := placeToRegChecked_ok_of_placeInputsMapped
    (cs := CheckedCompilerM.run (readToReg src) csA) (kind := RefKind.Shared)
    (PlaceInputsMapped.placeRegMap_congr (readToReg_placeRegMap_any src csA) lo
      (placeInputsMapped_of_localBindingSim_resolvePlace h_lbs h_resL))
  obtain ⟨h_lfr, h_lfv⟩ := readToReg_flat hDL
  have h_sresH : ∃ rs permsS, mirlite.resolvePlaceAcc MSB out2.state hi = .ok (rs, permsS) := by
    simp only [mirlite.evalCopy] at h_copyH
    cases hh : mirlite.resolvePlaceAcc MSB out2.state hi with
    | error err => rw [hh] at h_copyH; simp at h_copyH
    | ok pr => exact ⟨pr.1, pr.2, rfl⟩
  obtain ⟨rsH, permsH, h_sresH⟩ := h_sresH
  have h_resH : mirlite.resolvePlace? (M := MSB) sM hi = some rsH := by
    have hh := resolvePlace?_of_resolveAcc h_sresH
    rw [h_shapeL, h_shapeP, resolvePlace?_perms, resolvePlace?_perms] at hh
    exact hh
  obtain ⟨sOutH, hDH⟩ := placeToRegChecked_ok_of_placeInputsMapped
    (cs := CheckedCompilerM.run (readToReg lo)
      (CheckedCompilerM.run (readToReg src) csA)) (kind := RefKind.Shared)
    (PlaceInputsMapped.placeRegMap_congr
      ((readToReg_placeRegMap_any lo _).trans (readToReg_placeRegMap_any src csA)) hi
      (placeInputsMapped_of_localBindingSim_resolvePlace h_lbs h_resH))
  obtain ⟨h_hfr, h_hfv⟩ := readToReg_flat hDH
  -- §4 the compiled shape: three reads, then the one `SubSlice`
  have h_pre : CheckedCompilerM.run
      (compileRExprPreChecked (RExpr.subSlice (Γ := Γ) src lo hi)) csA
      = emit { (CheckedCompilerM.run (readToReg hi) (CheckedCompilerM.run (readToReg lo) (CheckedCompilerM.run (readToReg src) csA))) with nextReg := (CheckedCompilerM.run (readToReg hi) (CheckedCompilerM.run (readToReg lo) (CheckedCompilerM.run (readToReg src) csA))).nextReg + 1 }
        [Instr.Assgn (Register.R (CheckedCompilerM.run (readToReg hi) (CheckedCompilerM.run (readToReg lo) (CheckedCompilerM.run (readToReg src) csA))).nextReg)
          (Rhs.SubSlice (layoutToTyVal σ) (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (flattenPlace src)) csA).nextReg) (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (flattenPlace lo)) (CheckedCompilerM.run (readToReg src) csA)).nextReg) (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (flattenPlace hi)) (CheckedCompilerM.run (readToReg lo) (CheckedCompilerM.run (readToReg src) csA))).nextReg))] := by
    simp only [compileRExprPreChecked, csMonad, csRun, h_pfv, h_lfv, h_hfv]
  refine ⟨fun d => Instr.RStore obseq.TyVal.PTy (Register.R (CheckedCompilerM.run (readToReg hi) (CheckedCompilerM.run (readToReg lo) (CheckedCompilerM.run (readToReg src) csA))).nextReg) d,
    { store := fun d => [Instr.RStore obseq.TyVal.PTy (Register.R (CheckedCompilerM.run (readToReg hi) (CheckedCompilerM.run (readToReg lo) (CheckedCompilerM.run (readToReg src) csA))).nextReg) d],
      postCleanup := [],
      ev := fun _ => RExprToEvidence.subSlice src lo hi (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (flattenPlace src)) csA).nextReg) (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (flattenPlace lo)) (CheckedCompilerM.run (readToReg src) csA)).nextReg) (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (flattenPlace hi)) (CheckedCompilerM.run (readToReg lo) (CheckedCompilerM.run (readToReg src) csA))).nextReg)
        (Register.R (CheckedCompilerM.run (readToReg hi) (CheckedCompilerM.run (readToReg lo) (CheckedCompilerM.run (readToReg src) csA))).nextReg) },
    by simp only [compileRExprPreChecked, csMonad, csRun, h_pfv, h_lfv, h_hfv],
    fun _ => rfl, rfl,
    by rw [h_pre]; simp only [emit]
       rw [readToReg_placeRegMap_any hi, readToReg_placeRegMap_any lo,
         readToReg_placeRegMap_any src], ?_⟩
  intro h_code
  -- §5 the three runs, each at the state the previous left
  have h_codeP : CodeIncluded compProg
      (CheckedCompilerM.run (compileRExprPreChecked (.copy (flattenPlace src))) csA) := by
    rw [← h_pfr]
    refine h_code.mono ?_
    rw [h_pre]
    exact StateIncr.trans (CheckedCompilerM.incr (readToReg lo) _)
      (StateIncr.trans (CheckedCompilerM.incr (readToReg hi) _)
        (StateIncr.trans (freshReg_state_incr _) (emit_state_incr _ _)))
  obtain ⟨ρt1, nR1, sR1, perms₁, valsP, h_incrT1, h_wfT1, h_ostP, -, h_runP, h_regmonoP,
    h_lbsP, h_psimP, h_tbdP, h_smemP, h_pcP, h_vregP, h_relP, h_vbelowP, h_frameP⟩ :=
    h_restP h_codeP
  rw [h_valsP] at h_relP
  obtain ⟨b', tag', h_valsPE, h_rb, h_rt⟩ := ListRel_ptr_inv h_relP
  subst h_valsPE
  rw [← h_pfr] at h_regmonoP h_lbsP h_pcP h_vbelowP
  -- the LOW bound, at the post-pointer-read states
  have h_evalL : mirlite.evalRExpr MSB { sM with perms := perms₁ }
      (.copy (flattenPlace lo)) = .ok out2 := by
    rw [evalRExpr_copy_flatten]
    simp only [mirlite.evalRExpr]
    rw [← h_ostP]
    exact h_copyL
  obtain ⟨pOutL, h_pvalL, h_prmL, h_restL⟩ :=
    copy_readRegPkg_flat compProg lo ρa ρt1 { sM with perms := perms₁ } sR1 (CheckedCompilerM.run (readToReg src) csA)
      h_id_a h_wfT1 h_tbdP h_lbsP
      (by
        intro idx reg τ' h_look
        rw [getPlaceInfo_congr' (readToReg_placeRegMap_any src csA)] at h_look
        exact RegisterBelow.mono h_regmonoP (h_prb idx reg τ' h_look))
      (SourceMemSim.of_mem_eq (AddrRenameIncr.refl ρa) h_incrT1 h_sms h_smemP)
      (AllocLockstep.of_mem_eq h_alloc h_smemP) h_psimP h_pcP out2 h_evalL
  have h_codeL : CodeIncluded compProg
      (CheckedCompilerM.run (compileRExprPreChecked (.copy (flattenPlace lo))) (CheckedCompilerM.run (readToReg src) csA)) := by
    rw [← h_lfr]
    refine h_code.mono ?_
    rw [h_pre]
    exact StateIncr.trans (CheckedCompilerM.incr (readToReg hi) _)
      (StateIncr.trans (freshReg_state_incr _) (emit_state_incr _ _))
  obtain ⟨ρt2, nR2, sR2, perms₂, valsL, h_incrT2, h_wfT2, h_ostL, -, h_runL, h_regmonoL,
    h_lbsL, h_psimL, h_tbdL, h_smemL, h_pcL, h_vregL, h_relL, h_vbelowL, h_frameL⟩ :=
    h_restL h_codeL
  rw [h_valsL] at h_relL
  have h_valsLE := ListRel_word_inv h_relL
  subst h_valsLE
  rw [← h_lfr] at h_regmonoL h_lbsL h_pcL h_vbelowL
  -- the HIGH bound, at the post-low-read states
  have h_evalH : mirlite.evalRExpr MSB { sM with perms := perms₂ }
      (.copy (flattenPlace hi)) = .ok out3 := by
    rw [evalRExpr_copy_flatten]
    simp only [mirlite.evalRExpr]
    rw [show ({ sM with perms := perms₂ } : mirlite.State MSB Γ) = out2.state by
      rw [h_ostL]]
    exact h_copyH
  obtain ⟨pOutH, h_pvalH, h_prmH, h_restH⟩ :=
    copy_readRegPkg_flat compProg hi ρa ρt2 { sM with perms := perms₂ } sR2 (CheckedCompilerM.run (readToReg lo) (CheckedCompilerM.run (readToReg src) csA))
      h_id_a h_wfT2 h_tbdL h_lbsL
      (by
        intro idx reg τ' h_look
        rw [getPlaceInfo_congr' (readToReg_placeRegMap_any lo (CheckedCompilerM.run (readToReg src) csA)),
          getPlaceInfo_congr' (readToReg_placeRegMap_any src csA)] at h_look
        exact RegisterBelow.mono (Nat.le_trans h_regmonoP h_regmonoL)
          (h_prb idx reg τ' h_look))
      (SourceMemSim.of_mem_eq (AddrRenameIncr.refl ρa) h_incrT2
        (SourceMemSim.of_mem_eq (AddrRenameIncr.refl ρa) h_incrT1 h_sms h_smemP) h_smemL)
      (AllocLockstep.of_mem_eq (AllocLockstep.of_mem_eq h_alloc h_smemP) h_smemL)
      h_psimL h_pcL out3 h_evalH
  have h_codeH : CodeIncluded compProg
      (CheckedCompilerM.run (compileRExprPreChecked (.copy (flattenPlace hi))) (CheckedCompilerM.run (readToReg lo) (CheckedCompilerM.run (readToReg src) csA))) := by
    rw [← h_hfr]
    refine h_code.mono ?_
    rw [h_pre]
    exact StateIncr.trans (freshReg_state_incr _) (emit_state_incr _ _)
  obtain ⟨ρt3, nR3, sR3, perms₃, valsH, h_incrT3, h_wfT3, h_ostH, -, h_runH, h_regmonoH,
    h_lbsH, h_psimH, h_tbdH, h_smemH, h_pcH, h_vregH, h_relH, h_vbelowH, h_frameH⟩ :=
    h_restH h_codeH
  rw [h_valsH] at h_relH
  have h_valsHE := ListRel_word_inv h_relH
  subst h_valsHE
  rw [← h_hfr] at h_regmonoH h_lbsH h_pcH h_vbelowH
  -- the earlier operands survived the later reads
  have h_vregP' : oseair.RegMap.lookup sR3.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (flattenPlace src)) csA).nextReg)
      = some (layoutToTyVal (obseq.LayoutTy.PtrL σ), [Val.Ptr b' o e sz tag']) := by
    rw [h_frameH _ (RegisterBelow.mono h_regmonoL h_vbelowP),
      h_frameL _ h_vbelowP]
    exact h_vregP
  have h_vregL' : oseair.RegMap.lookup sR3.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (flattenPlace lo)) (CheckedCompilerM.run (readToReg src) csA)).nextReg)
      = some (layoutToTyVal obseq.LayoutTy.NatL, [Val.Dat l]) := by
    rw [h_frameH _ h_vbelowL]
    exact h_vregL
  -- §6 the `SubSlice` step
  have h_ts : obseq.typeSize (layoutToTyVal σ) = blockSize σ :=
    obseq.typeSize_layoutToTyVal _
  have h_code0 : compProg sR3.pc = some (Instr.Assgn (Register.R (CheckedCompilerM.run (readToReg hi) (CheckedCompilerM.run (readToReg lo) (CheckedCompilerM.run (readToReg src) csA))).nextReg)
          (Rhs.SubSlice (layoutToTyVal σ) (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (flattenPlace src)) csA).nextReg) (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (flattenPlace lo)) (CheckedCompilerM.run (readToReg src) csA)).nextReg) (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (flattenPlace hi)) (CheckedCompilerM.run (readToReg lo) (CheckedCompilerM.run (readToReg src) csA))).nextReg))) := by
    rw [h_pcH]
    refine h_code _ _ ?_ ?_
    · rw [h_pre]; simp [emit]
    · rw [h_pre]
      have hh := emit_code_at_new
        { (CheckedCompilerM.run (readToReg hi) (CheckedCompilerM.run (readToReg lo) (CheckedCompilerM.run (readToReg src) csA))) with nextReg := (CheckedCompilerM.run (readToReg hi) (CheckedCompilerM.run (readToReg lo) (CheckedCompilerM.run (readToReg src) csA))).nextReg + 1 }
        [Instr.Assgn (Register.R (CheckedCompilerM.run (readToReg hi) (CheckedCompilerM.run (readToReg lo) (CheckedCompilerM.run (readToReg src) csA))).nextReg)
          (Rhs.SubSlice (layoutToTyVal σ) (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (flattenPlace src)) csA).nextReg) (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (flattenPlace lo)) (CheckedCompilerM.run (readToReg src) csA)).nextReg) (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (flattenPlace hi)) (CheckedCompilerM.run (readToReg lo) (CheckedCompilerM.run (readToReg src) csA))).nextReg))]
        (k := 0) (by simp)
      simpa using hh
  have h_run4 := runN_Assgn_SubSlice_step compProg sR3 _ _ _ _ _ _ _ _
    b' o e sz l h tag' h_code0 h_vregP' h_vregL' h_vregH
    (by rw [h_ts]; simpa using h_fit)
  rw [h_ts] at h_run4
  -- §7 the tail: a narrowed pointer over the SAME allocation and tag —
  -- no memory, no new address, no new tag
  rw [h_pre]
  refine ⟨ρa, ρt3, nR1 + nR2 + nR3 + 1, _, sM.mem, perms₃,
    [Val.Ptr b' (o + l * blockSize σ) ((h - l) * blockSize σ) sz tag'],
    AddrRenameIncr.refl ρa, h_id_a,
    TagRenameIncr.trans h_incrT1 (TagRenameIncr.trans h_incrT2 h_incrT3), h_wfT3,
    by rw [h_ostH], rfl,
    oseair_runN_trans (oseair_runN_trans (oseair_runN_trans h_runP h_runL) h_runH) h_run4,
    (by simp only [emit]
        rw [readToReg_placeRegMap_any hi, readToReg_placeRegMap_any lo,
          readToReg_placeRegMap_any src]),
    (by
      refine Nat.le_trans h_regmonoP (Nat.le_trans h_regmonoL (Nat.le_trans h_regmonoH ?_))
      simp only [emit]
      omega),
    ?_,
    h_psimH, h_tbdH,
    SourceMemSim.of_mem_eq (AddrRenameIncr.refl ρa)
      (TagRenameIncr.trans h_incrT1 (TagRenameIncr.trans h_incrT2 h_incrT3)) h_sms
      (by show sR3.mem = sA.mem; rw [h_smemH, h_smemL, h_smemP]),
    AllocLockstep.of_mem_eq h_alloc (by show sR3.mem = sA.mem; rw [h_smemH, h_smemL, h_smemP]),
    (by
      show sR3.pc + 1 = _
      rw [h_pcH]
      simp only [emit, List.length_cons, List.length_nil]),
    StoreStep.rstore compProg _ _ obseq.TyVal.PTy _ _
      (RegMap.lookup_insert_self _ _ _)
      (by simp only [emit, RegisterBelow]; omega),
    ?_⟩
  · -- the locals: the narrowing writes one FRESH register
    refine LocalBindingSim.placeRegMap_congr (cs := (CheckedCompilerM.run (readToReg hi) (CheckedCompilerM.run (readToReg lo) (CheckedCompilerM.run (readToReg src) csA)))) (by simp only [emit]) ?_
    exact LocalBindingSim.insert_fresh_reg h_lbsH
      (by
        intro idx reg τ' h_look
        rw [getPlaceInfo_congr' (readToReg_placeRegMap_any hi _),
          getPlaceInfo_congr' (readToReg_placeRegMap_any lo _),
          getPlaceInfo_congr' (readToReg_placeRegMap_any src csA)] at h_look
        exact RegisterBelow.mono
          (Nat.le_trans h_regmonoP (Nat.le_trans h_regmonoL h_regmonoH))
          (h_prb idx reg τ' h_look))
      (Nat.le_refl _) rfl
  · -- the VALUE relation: same allocation, same tag, narrowed window —
    -- the tag rename only GREW across the two later reads
    obtain ⟨-, -, -, -, -, h_dom⟩ := h_relP.1
    exact ⟨⟨h_rb, rfl, rfl, rfl,
      (TagRenameIncr.trans h_incrT2 h_incrT3) _ _ h_rt, h_dom⟩, trivial⟩

end obseq3.proof
