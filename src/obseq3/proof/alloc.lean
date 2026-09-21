import obseq3.proof.common
import obseq3.proof.permsim_transport
import obseq3.proof.spine
import obseq3.proof.copy
import obseq3.proof.const_write

/-!
# `alloc`: a value package that EXTENDS memory

`alloc len : RExpr Γ (PtrL τ)` allocates `n * blockSize τ` units at the
watermark on both machines, owns them at a fresh tag, and leaves the
pointer in one register — `AllocN` for a static length, or copy's read
of the length place (`guardRead`) followed by `AllocDyn` on the VALUE
register. It is the first rvalue whose package uses the grown address
renaming and the `memO` the package hands back (2026-09-21): both
allocations are lockstep (`AllocLockstep`), so the rename grows by the
identity block at the shared watermark, exactly as a fresh-root
destination grows it.

The proof is one shared closing (`alloc_step_bundle`: from any related
pair of states and a one-step allocation on the target, everything the
package's tail asks for) and two thin constructors that establish the
one step: `AllocN` from the package's start states, `AllocDyn` from the
post-read states copy's read package (`copy_readRegPkg_flat`) leaves,
with the read's exposed register as the length.
-/

namespace obseq3.proof

open obseq3
open obseq3.compile
open obseq3.oseair (Instr Register Rhs Val)

variable {Γ : Ctx}

/-! ## The guard's read, shared with `alloc`'s dynamic length

`guardRead` is copy's read of a `NatL` place with its register exposed;
`assignIf`'s guard and `alloc`'s `fromPlace` length both consume it. -/

/-- `copy` of the flattened place is `copy` of the place (the read
    resolves for access, and flattening is invisible to resolution). -/
theorem evalRExpr_copy_flatten {τ : LayoutTy} {M : PermissionModel}
    (s : mirlite.State M Γ) (p : Place Γ τ) :
    mirlite.evalRExpr M s (.copy (flattenPlace p)) = mirlite.evalRExpr M s (.copy p) := by
  simp only [mirlite.evalRExpr, mirlite.evalCopy, resolvePlaceAcc_flatten]

/-- A read that compiled lowered its place. -/
theorem guardRead_value_inv {discr : Place Γ obseq.LayoutTy.NatL} {cs : CompilerState}
    {r : Register} (h : CheckedCompilerM.value (guardRead discr) cs = .ok r) :
    ∃ discrOut, CheckedCompilerM.value (placeToRegChecked RefKind.Shared discr) cs
      = .ok discrOut := by
  simp only [guardRead, csMonad] at h
  cases hD : CheckedCompilerM.value (placeToRegChecked RefKind.Shared discr) cs with
  | error e => rw [hD] at h; simp at h
  | ok discrOut => exact ⟨discrOut, rfl⟩

/-- The guard's read IS copy's read of the FLATTENED discriminant — the
    same run, and the value register is the read's temporary — so copy's
    read package (`copy_readRegPkg_flat`) speaks about it verbatim. -/
theorem guardRead_flat {discr : Place Γ obseq.LayoutTy.NatL} {cs : CompilerState}
    {discrOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared discr)}
    (hD : CheckedCompilerM.value (placeToRegChecked RefKind.Shared discr) cs = .ok discrOut) :
    CheckedCompilerM.run (guardRead discr) cs
      = CheckedCompilerM.run (compileRExprPreChecked (.copy (flattenPlace discr))) cs ∧
    CheckedCompilerM.value (guardRead discr) cs
      = .ok (Register.R (CheckedCompilerM.run
          (placeToRegChecked RefKind.Shared (flattenPlace discr)) cs).nextReg) := by
  obtain ⟨h_runF, h_valF⟩ := placeToRegChecked_flatten_agree discr RefKind.Shared cs
  cases hF : CheckedCompilerM.value (placeToRegChecked RefKind.Shared (flattenPlace discr)) cs with
  | error e =>
      exfalso
      rw [hF, hD] at h_valF
      simp [Except.map] at h_valF
  | ok flatOut =>
  have h_res : flatOut.result = discrOut.result := by
    rw [hF, hD] at h_valF
    simpa [Except.map] using h_valF
  constructor
  · simp only [guardRead, compileRExprPreChecked, readRhsPre, csMonad, hF, hD, h_runF, h_res,
      csRun, List.append_nil]
  · simp only [guardRead, csMonad, hD, h_runF, csRun]

/-- A single-word value list related to `[.word v]` is `[Val.Dat v]`. -/
theorem ListRel_word_inv {ρa : AddrRenameMap} {ρt : TagRenameMap} {v : Word} {vals : List Val}
    (h : ListRel (MemValSim ρa ρt) [mirlite.MemValue.word v] vals) : vals = [Val.Dat v] := by
  cases vals with
  | nil => exact absurd h (by simp [ListRel])
  | cons x xs =>
      cases xs with
      | cons y ys => exact absurd h.2 (by simp [ListRel])
      | nil =>
          cases x with
          | Dat v' => obtain ⟨h1, -⟩ := h; simp only [MemValSim] at h1; rw [h1]
          | Ptr b o s t => exact absurd h.1 (by simp [MemValSim])
          | Undef => exact absurd h.1 (by simp [MemValSim])

/-! ## The shared closing -/

/-- **The allocation step, packaged.** From related states `(memS,
    permsS, env)` / `sR1` at `(ρa, ρt, cs1)`, a successful source `own`
    of `n * blockSize τ` units at the watermark, and the target's
    one-step allocation into the fresh register `R cs1.nextReg`
    (conditional on ITS `own`, which `PermSim` supplies), everything a
    value package's tail asks for at the compiler state that emitted the
    one instruction: the identity block extends `ρa`, the fresh tag pair
    extends `ρt`, the memories stay related and lockstep, the pointer
    values are related. -/
theorem alloc_step_bundle {Γ : Ctx} (τ : LayoutTy) (n : Nat) (compProg : oseair.Prog)
    {ρa : AddrRenameMap} {ρt : TagRenameMap} {env : mirlite.Env Γ}
    {memS : mirlite.Mem} {permsS : MSB.State}
    {sR1 : oseair.State MSB} {cs1 : CompilerState} (instr : Instr)
    (h_id_a : IdentityOnDomain ρa) (h_wf_t : TagRenameWF ρt)
    (h_tbd : TagRenameBounded ρt permsS.NextTag sR1.perms.NextTag)
    (h_lbs : LocalBindingSim ρa ρt env sR1 cs1) (h_prb : PlaceRegMapBound cs1)
    (h_sms : SourceMemSim ρa ρt memS sR1.mem) (h_alloc : AllocLockstep ρa memS sR1.mem)
    (h_psim : PermSim ρt permsS sR1.perms) (h_pc : sR1.pc = cs1.nextLabel)
    {perms' : MSB.State} {tagS : Tag}
    (h_own_src : MSB.own permsS memS.addrStart (n * blockSize τ) = .ok (perms', tagS))
    (h_step : ∀ tgtPerms,
      MSB.own sR1.perms sR1.mem.addrStart (n * obseq.typeSize (layoutToTyVal τ))
        = .ok (tgtPerms, sR1.perms.NextTag) →
      oseair.runN MSB 1 sR1 compProg = oseair.Result.Ok
        { sR1 with
          mem := (oseair.allocate sR1.mem (n * obseq.typeSize (layoutToTyVal τ))).2,
          perms := tgtPerms,
          reg := oseair.RegMap.insert sR1.reg (Register.R cs1.nextReg)
            (obseq.TyVal.PTy, [Val.Ptr sR1.mem.addrStart 0
              (n * obseq.typeSize (layoutToTyVal τ)) sR1.perms.NextTag]),
          pc := sR1.pc + 1 }) :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (sR : oseair.State MSB) (vals : List Val),
      AddrRenameIncr ρa ρa' ∧
      IdentityOnDomain ρa' ∧
      TagRenameIncr ρt ρt' ∧
      TagRenameWF ρt' ∧
      vals.length = blockSize (obseq.LayoutTy.PtrL τ) ∧
      oseair.runN MSB 1 sR1 compProg = oseair.Result.Ok sR ∧
      LocalBindingSim ρa' ρt' env sR (emit { cs1 with nextReg := cs1.nextReg + 1 } [instr]) ∧
      PermSim ρt' perms' sR.perms ∧
      TagRenameBounded ρt' perms'.NextTag sR.perms.NextTag ∧
      SourceMemSim ρa' ρt' (mirlite.allocate memS (n * blockSize τ)).2 sR.mem ∧
      AllocLockstep ρa' (mirlite.allocate memS (n * blockSize τ)).2 sR.mem ∧
      sR.pc = (emit { cs1 with nextReg := cs1.nextReg + 1 } [instr]).nextLabel ∧
      StoreStep compProg sR (emit { cs1 with nextReg := cs1.nextReg + 1 } [instr]).nextReg
        (fun d => Instr.RStore obseq.TyVal.PTy (Register.R cs1.nextReg) d) vals ∧
      ListRel (MemValSim ρa' ρt')
        [mirlite.MemValue.ptrVal memS.addrStart 0 (n * blockSize τ) tagS] vals := by
  -- §1 the target's `own`, through `PermSim`
  obtain ⟨tgtPerms, h_own_tgt, h_tagS_eq, h_incr_t, h_wf_t', h_tbd', h_psim'⟩ :=
    sb_own_respects_PermSim h_psim h_wf_t h_tbd h_own_src
  subst h_tagS_eq
  have h_addr_eq : sR1.mem.addrStart = memS.addrStart := h_alloc.1
  have h_sz : obseq.typeSize (layoutToTyVal τ) = blockSize τ :=
    obseq.typeSize_layoutToTyVal _
  have h_units : n * obseq.typeSize (layoutToTyVal τ) = n * blockSize τ := by rw [h_sz]
  have h_run := h_step tgtPerms (by rw [h_units, h_addr_eq]; exact h_own_tgt)
  -- §2 the identity block at the shared watermark
  have h_incr_a := AddrRenameIncr.extendBlock h_id_a memS.addrStart (n * blockSize τ)
  have h_id_a' := IdentityOnDomain.extendBlock h_id_a memS.addrStart (n * blockSize τ)
  have h_rt_new : (ρt.extend permsS.NextTag sR1.perms.NextTag) permsS.NextTag
      = some sR1.perms.NextTag := TagRenameMap.extend_self _ _ _
  refine ⟨ρa.extendBlock memS.addrStart (n * blockSize τ),
    ρt.extend permsS.NextTag sR1.perms.NextTag, _,
    [Val.Ptr sR1.mem.addrStart 0 (n * obseq.typeSize (layoutToTyVal τ)) sR1.perms.NextTag],
    h_incr_a, h_id_a', h_incr_t, h_wf_t',
    by simp [blockSize, obseq.layoutSize], h_run, ?_, h_psim', h_tbd', ?_, ?_, ?_, ?_, ?_⟩
  · -- the locals: renames grow, the fresh register is above every mapped one
    refine LocalBindingSim.placeRegMap_congr (cs := cs1) rfl ?_
    exact LocalBindingSim.insert_fresh_reg
      (LocalBindingSim.rename_mono h_incr_a h_incr_t h_lbs) h_prb (Nat.le_refl _) rfl
  · -- memory: neither allocation touches a cell
    intro a v h_find
    exact SourceMemSim.rename_mono h_incr_a h_incr_t h_sms a v h_find
  · exact AllocLockstep.of_alloc h_alloc h_incr_a h_units rfl rfl
  · show sR1.pc + 1 = _
    rw [h_pc]
    simp only [emit, List.length_cons, List.length_nil]
  · refine StoreStep.rstore compProg _ _ obseq.TyVal.PTy (Register.R cs1.nextReg) _ ?_ ?_
    · exact RegMap.lookup_insert_self _ _ _
    · simp only [emit, RegisterBelow]
      omega
  · refine ⟨⟨?_, rfl, h_units, h_rt_new, ?_⟩, trivial⟩
    · rw [h_addr_eq]
      exact AddrRenameMap.extendBlock_base _ _ _
    · intro k hk
      exact ⟨memS.addrStart + k, AddrRenameMap.extendBlock_mem hk⟩

/-! ## The two constructors -/

/-- A STATIC length: the rvalue is one `AllocN`, at the package's start
    states. -/
theorem alloc_const_valuePkg {Γ : Ctx} (τ : LayoutTy) (n : Nat) (compProg : oseair.Prog) :
    ValuePkg compProg (RExpr.alloc (Γ := Γ) (τ := τ) (.const n)) := by
  intro ρa ρt sM sA csA h_id_a h_wf_t h_tbd h_lbs h_prb h_sms h_alloc h_psim h_pc
    output h_eval
  -- §1 invert the source: the own succeeded
  simp only [mirlite.evalRExpr, mirlite.evalAllocLen] at h_eval
  cases h_own_src : MSB.own sM.perms sM.mem.addrStart (n * blockSize τ) with
  | error e => rw [h_own_src] at h_eval; simp at h_eval
  | ok pr =>
  obtain ⟨perms', tagS⟩ := pr
  rw [h_own_src] at h_eval
  injection h_eval with h_out
  subst h_out
  -- §2 the compiled shape
  have h_pre : CheckedCompilerM.run
      (compileRExprPreChecked (RExpr.alloc (Γ := Γ) (τ := τ) (.const n))) csA
      = emit { csA with nextReg := csA.nextReg + 1 }
        [Instr.Assgn (Register.R csA.nextReg) (Rhs.AllocN (layoutToTyVal τ) n)] := by
    simp only [compileRExprPreChecked, compileAllocLenChecked, csMonad, csRun]
  refine ⟨fun d => Instr.RStore obseq.TyVal.PTy (Register.R csA.nextReg) d,
    { store := fun d => [Instr.RStore obseq.TyVal.PTy (Register.R csA.nextReg) d],
      postCleanup := [],
      ev := fun _ => RExprToEvidence.alloc (.const n) (Register.R csA.nextReg) },
    by simp only [compileRExprPreChecked, compileAllocLenChecked, csMonad, csRun],
    fun _ => rfl, rfl, by rw [h_pre]; rfl, ?_⟩
  intro h_code
  -- §3 the `AllocN` is in the program
  have h_code0 : compProg sA.pc
      = some (Instr.Assgn (Register.R csA.nextReg) (Rhs.AllocN (layoutToTyVal τ) n)) := by
    rw [h_pc]
    refine h_code _ _ ?_ ?_
    · rw [h_pre]; simp [emit]
    · rw [h_pre]
      have h := emit_code_at_new { csA with nextReg := csA.nextReg + 1 }
        [Instr.Assgn (Register.R csA.nextReg) (Rhs.AllocN (layoutToTyVal τ) n)]
        (k := 0) (by simp)
      simpa using h
  -- §4 the shared closing
  obtain ⟨ρa', ρt', sR, vals, h_incr_a, h_id_a', h_incr_t, h_wf_t', h_vlen, h_run,
    h_lbsR, h_psimR, h_tbdR, h_smsR, h_allocR, h_pcR, h_execR, h_rel⟩ :=
    alloc_step_bundle τ n compProg
      (Instr.Assgn (Register.R csA.nextReg) (Rhs.AllocN (layoutToTyVal τ) n))
      h_id_a h_wf_t h_tbd h_lbs h_prb h_sms h_alloc h_psim h_pc h_own_src
      (fun tgtPerms h_own =>
        runN_Assgn_AllocN_step compProg sA (Register.R csA.nextReg) (layoutToTyVal τ) n
          h_code0 h_own)
  rw [h_pre]
  exact ⟨ρa', ρt', 1, sR, _, perms', vals, h_incr_a, h_id_a', h_incr_t, h_wf_t', rfl,
    h_vlen, h_run, rfl, by simp only [emit]; omega, h_lbsR, h_psimR, h_tbdR,
    h_smsR, h_allocR, h_pcR, h_execR, h_rel⟩

/-- A READ length: copy's read of the length place (the guard's read,
    with its register exposed), then one `AllocDyn` on that register at
    the post-read states. -/
theorem alloc_fromPlace_valuePkg {Γ : Ctx} (τ : LayoutTy)
    (p : Place Γ obseq.LayoutTy.NatL) (compProg : oseair.Prog) :
    ValuePkg compProg (RExpr.alloc (Γ := Γ) (τ := τ) (.fromPlace p)) := by
  intro ρa ρt sM sA csA h_id_a h_wf_t h_tbd h_lbs h_prb h_sms h_alloc h_psim h_pc
    output h_eval
  -- §1 invert the source: the read gave a word, the own succeeded
  simp only [mirlite.evalRExpr, mirlite.evalAllocLen] at h_eval
  cases h_copy : mirlite.evalCopy MSB sM p with
  | err e => rw [h_copy] at h_eval; simp at h_eval
  | ok out =>
  rw [h_copy] at h_eval
  split at h_eval
  · simp at h_eval
  rename_i n s1 heq
  simp only at heq
  split at heq
  case h_2 => simp at heq
  rename_i n' h_vals
  injection heq with heq
  injection heq with h_n h_s1
  subst h_n h_s1
  cases h_own_src : MSB.own out.state.perms out.state.mem.addrStart (n' * blockSize τ) with
  | error e => rw [h_own_src] at h_eval; simp at h_eval
  | ok pr =>
  obtain ⟨perms', tagS⟩ := pr
  rw [h_own_src] at h_eval
  injection h_eval with h_out
  subst h_out
  -- §2 the read, through copy's package with the register exposed
  have h_evalC : mirlite.evalRExpr MSB sM (.copy (flattenPlace p)) = .ok out := by
    rw [evalRExpr_copy_flatten]
    simp only [mirlite.evalRExpr]
    exact h_copy
  obtain ⟨pOutC, h_pvalC, h_prmC, h_restC⟩ :=
    copy_readRegPkg_flat compProg p ρa ρt sM sA csA h_id_a h_wf_t h_tbd h_lbs h_prb
      h_sms h_alloc h_psim h_pc out h_evalC
  -- the read's place lowers, so the guard's read compiles and is that read
  have h_sres : ∃ rs permsS, mirlite.resolvePlaceAcc MSB sM p = .ok (rs, permsS) := by
    simp only [mirlite.evalCopy] at h_copy
    cases h : mirlite.resolvePlaceAcc MSB sM p with
    | error e => rw [h] at h_copy; simp at h_copy
    | ok pr => exact ⟨pr.1, pr.2, rfl⟩
  obtain ⟨rs, permsS, h_sres⟩ := h_sres
  obtain ⟨discrOut, hD⟩ := placeToRegChecked_ok_of_placeInputsMapped
    (cs := csA) (kind := RefKind.Shared)
    (placeInputsMapped_of_localBindingSim_resolvePlace h_lbs
      (resolvePlace?_of_resolveAcc h_sres))
  obtain ⟨h_gfr, h_gfv⟩ := guardRead_flat hD
  -- §3 the compiled shape: the read, then the `AllocDyn`
  have h_pre : CheckedCompilerM.run
      (compileRExprPreChecked (RExpr.alloc (Γ := Γ) (τ := τ) (.fromPlace p))) csA
      = emit { (CheckedCompilerM.run (guardRead p) csA) with
          nextReg := (CheckedCompilerM.run (guardRead p) csA).nextReg + 1 }
        [Instr.Assgn (Register.R (CheckedCompilerM.run (guardRead p) csA).nextReg)
          (Rhs.AllocDyn (layoutToTyVal τ) (Register.R (CheckedCompilerM.run
            (placeToRegChecked RefKind.Shared (flattenPlace p)) csA).nextReg))] := by
    simp only [compileRExprPreChecked, compileAllocLenChecked, csMonad, csRun, h_gfv]
  refine ⟨fun d => Instr.RStore obseq.TyVal.PTy
      (Register.R (CheckedCompilerM.run (guardRead p) csA).nextReg) d,
    { store := fun d => [Instr.RStore obseq.TyVal.PTy
        (Register.R (CheckedCompilerM.run (guardRead p) csA).nextReg) d],
      postCleanup := [],
      ev := fun _ => RExprToEvidence.alloc (.fromPlace p)
        (Register.R (CheckedCompilerM.run (guardRead p) csA).nextReg) },
    by simp only [compileRExprPreChecked, compileAllocLenChecked, csMonad, csRun, h_gfv],
    fun _ => rfl, rfl,
    by rw [h_pre]; simp only [emit]; exact guardRead_placeRegMap_any p csA, ?_⟩
  intro h_code
  -- §4 the read's run
  have h_codeR : CodeIncluded compProg
      (CheckedCompilerM.run (compileRExprPreChecked (.copy (flattenPlace p))) csA) := by
    rw [← h_gfr]
    refine h_code.mono ?_
    rw [h_pre]
    exact StateIncr.trans (freshReg_state_incr _) (emit_state_incr _ _)
  obtain ⟨ρt2, nR, sR, perms₂, vals, h_incrT2, h_wfT2, h_ost, -, h_runR, h_regmono,
    h_lbsR, h_psimR, h_tbdR, h_smem, h_pcR, h_vreg, h_valsRel⟩ := h_restC h_codeR
  rw [h_vals] at h_valsRel
  have h_valsD := ListRel_word_inv h_valsRel
  subst h_valsD
  rw [← h_gfr] at h_regmono h_lbsR h_pcR
  -- §5 the `AllocDyn` is in the program, at the read's end
  have h_code0 : compProg sR.pc
      = some (Instr.Assgn (Register.R (CheckedCompilerM.run (guardRead p) csA).nextReg)
          (Rhs.AllocDyn (layoutToTyVal τ) (Register.R (CheckedCompilerM.run
            (placeToRegChecked RefKind.Shared (flattenPlace p)) csA).nextReg))) := by
    rw [h_pcR]
    refine h_code _ _ ?_ ?_
    · rw [h_pre]; simp [emit]
    · rw [h_pre]
      have h := emit_code_at_new { (CheckedCompilerM.run (guardRead p) csA) with
          nextReg := (CheckedCompilerM.run (guardRead p) csA).nextReg + 1 }
        [Instr.Assgn (Register.R (CheckedCompilerM.run (guardRead p) csA).nextReg)
          (Rhs.AllocDyn (layoutToTyVal τ) (Register.R (CheckedCompilerM.run
            (placeToRegChecked RefKind.Shared (flattenPlace p)) csA).nextReg))]
        (k := 0) (by simp)
      simpa using h
  -- §6 the shared closing at the post-read states
  rw [h_ost] at h_own_src ⊢
  obtain ⟨ρa', ρt', sR', vals', h_incr_a, h_id_a', h_incr_t, h_wf_t', h_vlen, h_run,
    h_lbsR', h_psimR', h_tbdR', h_smsR', h_allocR', h_pcR', h_execR', h_rel⟩ :=
    alloc_step_bundle τ n' compProg (env := sM.env)
      (Instr.Assgn (Register.R (CheckedCompilerM.run (guardRead p) csA).nextReg)
        (Rhs.AllocDyn (layoutToTyVal τ) (Register.R (CheckedCompilerM.run
          (placeToRegChecked RefKind.Shared (flattenPlace p)) csA).nextReg)))
      h_id_a h_wfT2 h_tbdR h_lbsR
      (by
        intro idx reg τ' h_look
        rw [getPlaceInfo_congr' (guardRead_placeRegMap_any p csA)] at h_look
        exact RegisterBelow.mono h_regmono (h_prb idx reg τ' h_look))
      (SourceMemSim.of_mem_eq (AddrRenameIncr.refl ρa) h_incrT2 h_sms h_smem)
      (AllocLockstep.of_mem_eq h_alloc h_smem) h_psimR h_pcR h_own_src
      (fun tgtPerms h_own =>
        runN_Assgn_AllocDyn_step compProg sR _ _ (layoutToTyVal τ) _ n' h_code0 h_vreg h_own)
  rw [h_pre]
  refine ⟨ρa', ρt', nR + 1, sR', _, perms', vals', h_incr_a, h_id_a',
    TagRenameIncr.trans h_incrT2 h_incr_t, h_wf_t', rfl,
    h_vlen, oseair_runN_trans h_runR h_run, by simp only [emit]; exact guardRead_placeRegMap_any p csA,
    by simp only [emit]; omega, h_lbsR', h_psimR', h_tbdR', h_smsR', h_allocR', h_pcR', h_execR',
    h_rel⟩

/-- Every `alloc` is a value package. -/
theorem alloc_valuePkg {Γ : Ctx} {τ : LayoutTy} (len : AllocLen Γ) (compProg : oseair.Prog) :
    ValuePkg compProg (RExpr.alloc (Γ := Γ) (τ := τ) len) := by
  cases len with
  | const n => exact alloc_const_valuePkg τ n compProg
  | fromPlace p => exact alloc_fromPlace_valuePkg τ p compProg

end obseq3.proof
