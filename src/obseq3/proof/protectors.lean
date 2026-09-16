import obseq3.proof.ptrarith

/-!
# Protector frames: `pushProtectors` / `popProtectors`

The two statements are the only call-shaped structure either machine
has (durable/protectors-and-the-charon-inlining-seam.md). Both run the
SAME `PermissionModel` field on `perms` — `pushFrame := sb_push_frame`
conses an empty frame, `popFrame := sb_pop_frame` drops the innermost
or errors on none — and bump `pc`; the compiler emits `PushProt` /
`PopProt` one-to-one. Memory, registers, env and both renamings are
untouched, so the invariant's only moving clause is `PermSim`'s frame
list, and that is a positional `ListRel`: push is `cons` with an empty
pair, pop is inversion on `_ :: _`.

Admitting them is what makes every `prot = true` path in the ref and
refSlice leaves NON-vacuous: until now a core program had
`protFrames = []` forever, so a protected retag could only fail in the
source.
-/

namespace obseq3.proof

variable {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
variable {ρa : AddrRenameMap} {ρt : TagRenameMap}
variable {s_mir s_mir' : mirlite.State MSB Γ}
variable {s_osea : oseair.State MSB}

open obseq3
open obseq3.compile
open obseq3.oseair (Instr Register Rhs Val)

/-! ## Machine steps -/

theorem runN_PushProt_step (compProg : oseair.Prog) (s : oseair.State MSB)
    (h_instr : compProg s.pc = some Instr.PushProt) :
    oseair.runN MSB 1 s compProg = oseair.Result.Ok
      { s with perms := MSB.pushFrame s.perms, pc := s.pc + 1 } := by
  have h_step : oseair.step MSB s compProg = oseair.Result.Ok
      { s with perms := MSB.pushFrame s.perms, pc := s.pc + 1 } := by
    simp only [oseair.step, oseair.stepWith, h_instr]
  simp [oseair.runN_succ, oseair.runN_zero, h_step]

theorem runN_PopProt_step (compProg : oseair.Prog) (s : oseair.State MSB)
    {p2 : AccessPerms}
    (h_instr : compProg s.pc = some Instr.PopProt)
    (h_pop : MSB.popFrame s.perms = .ok p2) :
    oseair.runN MSB 1 s compProg = oseair.Result.Ok
      { s with perms := p2, pc := s.pc + 1 } := by
  have h_step : oseair.step MSB s compProg = oseair.Result.Ok
      { s with perms := p2, pc := s.pc + 1 } := by
    simp only [oseair.step, oseair.stepWith, h_instr, h_pop]
  simp [oseair.runN_succ, oseair.runN_zero, h_step]

/-! ## `PermSim` transport -/

/-- Pushing an (empty) frame on both sides keeps the frame lists related:
    `ListRel` of `[]` with `[]` is `True`. Nothing else moves. -/
theorem PermSim.pushFrame {sp tp : AccessPerms} (h : PermSim ρt sp tp) :
    PermSim ρt (MSB.pushFrame sp) (MSB.pushFrame tp) := by
  obtain ⟨h_st, h_pf, h_ex, h_nt⟩ := h
  exact ⟨h_st, ⟨trivial, h_pf⟩, h_ex, h_nt⟩

/-- Popping succeeds on the target whenever it does on the source — the
    lists are positionally related, so the target's is non-empty too —
    and the tails stay related. `NextTag` is untouched on both sides. -/
theorem PermSim.popFrame {sp sp' tp : AccessPerms} (h : PermSim ρt sp tp)
    (h_src : MSB.popFrame sp = .ok sp') :
    ∃ tp', MSB.popFrame tp = .ok tp' ∧ PermSim ρt sp' tp' ∧
      sp'.NextTag = sp.NextTag ∧ tp'.NextTag = tp.NextTag := by
  obtain ⟨h_st, h_pf, h_ex, h_nt⟩ := h
  change sb_pop_frame sp = .ok sp' at h_src
  cases hs : sp.protFrames with
  | nil => simp [sb_pop_frame, hs] at h_src
  | cons f rest =>
    cases ht : tp.protFrames with
    | nil => rw [hs, ht] at h_pf; exact h_pf.elim
    | cons f' rest' =>
      simp only [sb_pop_frame, hs] at h_src
      injection h_src with h_src
      subst h_src
      rw [hs, ht] at h_pf
      refine ⟨{ tp with protFrames := rest' }, ?_, ⟨h_st, h_pf.2, h_ex, h_nt⟩, rfl, rfl⟩
      change sb_pop_frame tp = _
      simp [sb_pop_frame, ht]

/-! ## The two statement leaves -/

theorem CompilerInv_step_pushProtectors
    (compProg : oseair.Prog)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    (h_stmt : prog.get? s_mir.pc = some .pushProtectors)
    (h_step : mirlite.stepStmt MSB s_mir .pushProtectors = .ok s_mir') :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' := by
  obtain ⟨csPrefix, ⟨h_csAt, h_pc⟩, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_tbd,
    h_alloc, h_unmap, h_prb⟩ := h_inv
  simp only [mirlite.stepStmt] at h_step
  cases h_step
  have h_stmtOut : CheckedCompilerM.value (compileStmtChecked (Γ := Γ) .pushProtectors)
      csPrefix = Except.ok ⟨(), StmtEvidence.pushProtectors⟩ := rfl
  have h_stmtRun : CheckedCompilerM.run (compileStmtChecked (Γ := Γ) .pushProtectors)
      csPrefix = emit csPrefix [Instr.PushProt] := rfl
  have h_code : compProg s_osea.pc = some Instr.PushProt := by
    rw [h_pc]
    refine CodeIncluded.of_stmt h_comp h_csAt h_stmt h_stmtOut _ _ ?_ ?_
    · rw [h_stmtRun]; simp [emit]
    · rw [h_stmtRun]
      simpa using emit_code_at_new csPrefix [Instr.PushProt] (k := 0) (by simp)
  refine ⟨ρa, ρt, _, 1, AddrRenameIncr.refl ρa, TagRenameIncr.refl ρt,
    runN_PushProt_step compProg s_osea h_code, ?_⟩
  refine ⟨CheckedCompilerM.run (compileStmtChecked .pushProtectors) csPrefix,
    ⟨prefixCompileState_succ h_csAt h_stmt h_stmtOut, ?_⟩, ?_, h_sms,
    PermSim.pushFrame h_psim, h_id_a, h_wf_t, h_tbd, h_alloc, ?_, ?_⟩
  · show s_osea.pc + 1 = _
    rw [h_pc, h_stmtRun]; simp [emit]
  · intro τ' loc' b h_env
    obtain ⟨reg, base, tag, h_pi, h_entry, h_ra, h_rt, h_nw, h_dom⟩ := h_lbs loc' b h_env
    exact ⟨reg, base, tag, by rw [h_stmtRun, getPlaceInfo_emit]; exact h_pi,
      h_entry, h_ra, h_rt, h_nw, h_dom⟩
  · intro τ' loc' h_none
    rw [h_stmtRun, getPlaceInfo_emit]; exact h_unmap loc' h_none
  · intro idx reg τ'' h_look
    rw [h_stmtRun, getPlaceInfo_emit] at h_look
    rw [h_stmtRun]
    exact h_prb idx reg τ'' h_look

theorem CompilerInv_step_popProtectors
    (compProg : oseair.Prog)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    (h_stmt : prog.get? s_mir.pc = some .popProtectors)
    (h_step : mirlite.stepStmt MSB s_mir .popProtectors = .ok s_mir') :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' := by
  obtain ⟨csPrefix, ⟨h_csAt, h_pc⟩, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_tbd,
    h_alloc, h_unmap, h_prb⟩ := h_inv
  simp only [mirlite.stepStmt] at h_step
  cases h_pop : MSB.popFrame s_mir.perms with
  | error e => rw [h_pop] at h_step; simp at h_step
  | ok perms' =>
  rw [h_pop] at h_step
  cases h_step
  obtain ⟨p2, h_pop_t, h_psim', h_ntS, h_ntT⟩ := PermSim.popFrame h_psim h_pop
  have h_stmtOut : CheckedCompilerM.value (compileStmtChecked (Γ := Γ) .popProtectors)
      csPrefix = Except.ok ⟨(), StmtEvidence.popProtectors⟩ := rfl
  have h_stmtRun : CheckedCompilerM.run (compileStmtChecked (Γ := Γ) .popProtectors)
      csPrefix = emit csPrefix [Instr.PopProt] := rfl
  have h_code : compProg s_osea.pc = some Instr.PopProt := by
    rw [h_pc]
    refine CodeIncluded.of_stmt h_comp h_csAt h_stmt h_stmtOut _ _ ?_ ?_
    · rw [h_stmtRun]; simp [emit]
    · rw [h_stmtRun]
      simpa using emit_code_at_new csPrefix [Instr.PopProt] (k := 0) (by simp)
  refine ⟨ρa, ρt, _, 1, AddrRenameIncr.refl ρa, TagRenameIncr.refl ρt,
    runN_PopProt_step compProg s_osea h_code h_pop_t, ?_⟩
  refine ⟨CheckedCompilerM.run (compileStmtChecked .popProtectors) csPrefix,
    ⟨prefixCompileState_succ h_csAt h_stmt h_stmtOut, ?_⟩, ?_, h_sms,
    h_psim', h_id_a, h_wf_t, ?_, h_alloc, ?_, ?_⟩
  · show s_osea.pc + 1 = _
    rw [h_pc, h_stmtRun]; simp [emit]
  · intro τ' loc' b h_env
    obtain ⟨reg, base, tag, h_pi, h_entry, h_ra, h_rt, h_nw, h_dom⟩ := h_lbs loc' b h_env
    exact ⟨reg, base, tag, by rw [h_stmtRun, getPlaceInfo_emit]; exact h_pi,
      h_entry, h_ra, h_rt, h_nw, h_dom⟩
  · show TagRenameBounded ρt perms'.NextTag p2.NextTag
    rw [h_ntS, h_ntT]; exact h_tbd
  · intro τ' loc' h_none
    rw [h_stmtRun, getPlaceInfo_emit]; exact h_unmap loc' h_none
  · intro idx reg τ'' h_look
    rw [h_stmtRun, getPlaceInfo_emit] at h_look
    rw [h_stmtRun]
    exact h_prb idx reg τ'' h_look

end obseq3.proof
