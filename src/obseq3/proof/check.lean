import obseq3.proof.fragment

/-!
# The `check` statement

`check p ∈ V` (or `∉`) reads the word at `p` as `copy` does and continues
when its membership agrees; otherwise the run is stuck. The compiler
lowers it as the read (`readToReg`, a `guardRead`) and one `Check` on the
loaded register. The two read the same word, so a passing source check is
matched by a passing target check (`check_simB`).
-/

namespace obseq3.proof

open obseq3 obseq3.bytes obseq3.proof
open obseq3.mirlite (MemValue)
open obseq3.oseair (Val Register)
open obseq3.compile

/-! ## Retargeting -/

/-- The invariant moves to another compile state with the same place map
    (and no fewer registers), the target pc following its label. -/
theorem InvAtB.retarget {Γ : Ctx} {L : mirlite.LayEnv Γ} {ρt : TagRenameMap}
    {s : mirlite.State MSB Γ} {sA : oseair.State MSB} {cs cs' : CompilerState}
    (h : InvAtB L ρt s sA cs) (h_prm : cs'.placeRegMap = cs.placeRegMap)
    (h_nr : cs.nextReg ≤ cs'.nextReg) :
    InvAtB L ρt s { sA with pc := cs'.nextLabel } cs' := {
  pc := rfl
  lbs := fun loc b hb => by
    obtain ⟨r, t, hpi, he, hrt, hnw⟩ := h.lbs loc b hb
    refine ⟨r, t, ?_, he, hrt, hnw⟩
    show List.lookup _ _ = _
    rw [h_prm]; exact hpi
  mem := h.mem
  alloc := h.alloc
  psim := h.psim
  wf_t := h.wf_t
  tbd := h.tbd
  unmap := fun loc hl => by
    show List.lookup _ _ = _
    rw [h_prm]; exact h.unmap loc hl
  prb := fun idx r τ' hpi => by
    have : getPlaceInfo cs idx = some (r, τ') := by
      show List.lookup _ _ = _
      rw [← h_prm]; exact hpi
    exact RegisterBelow.mono h_nr (h.prb idx r τ' this)
}

theorem InvAtB.src_pc {Γ : Ctx} {L : mirlite.LayEnv Γ} {ρt : TagRenameMap}
    {s : mirlite.State MSB Γ} {sA : oseair.State MSB} {cs : CompilerState} {p : Nat}
    (h : InvAtB L ρt s sA cs) : InvAtB L ρt { s with pc := p } sA cs :=
  ⟨h.pc, h.lbs, h.mem, h.alloc, h.psim, h.wf_t, h.tbd, h.unmap, h.prb⟩

/-! ## The leaf -/

theorem check_simB {Γ : Ctx} {L : mirlite.LayEnv Γ} {compProg : oseair.Prog}
    (hWF : PtrPlacesWF L) {t : IntTy} {discr : Place Γ (LayoutTy.IntL t)} {vals : List Word}
    {member : Bool} (h_d : ReadSrcB discr) :
    StmtSimB L compProg (.check discr vals member) := by
  intro ρt s_mir s_mir' s_osea cs h_inv h_code h_step
  -- the source: the read, the comparison
  simp only [mirlite.stepStmt] at h_step
  split at h_step
  · cases h_step
  rename_i out h_e
  split at h_step
  case h_2 => cases h_step
  rename_i v h_v
  split at h_step
  case isFalse => cases h_step
  rename_i h_mem
  simp only [mirlite.Result.ok.injEq] at h_step
  subst h_step
  -- the target: the read, then `Check`
  cases hv : CheckedCompilerM.value (readToReg L discr) cs with
  | error e =>
      exfalso
      have h_run : CheckedCompilerM.run (compileStmtChecked L (.check discr vals member)) cs =
          CheckedCompilerM.run (readToReg L discr) cs := by
        simp only [compileStmtChecked, guardRead, CheckedCompilerM.run_bind, hv]
      rw [h_run] at h_code
      obtain ⟨-, -, -, -, -, -, -, h_val, -, -, -⟩ := readToReg_simR hWF h_d h_inv h_e h_code
      rw [hv] at h_val; cases h_val
  | ok r =>
      have h_run : CheckedCompilerM.run (compileStmtChecked L (.check discr vals member)) cs =
          compile.emit (CheckedCompilerM.run (readToReg L discr) cs)
            [oseair.Instr.Check r vals member] := by
        simp only [compileStmtChecked, guardRead, CheckedCompilerM.run_bind,
          CheckedCompilerM.value_bind, hv, CheckedCompilerM.run_lift,
          CheckedCompilerM.value_lift, CheckedCompilerM.run_pure]
        rfl
      rw [h_run] at h_code ⊢
      generalize hcG : CheckedCompilerM.run (readToReg L discr) cs = csG at h_code ⊢
      have h_codeG : CodeIncludedB compProg (CheckedCompilerM.run (readToReg L discr) cs) := by
        rw [hcG]; exact h_code.mono (emit_state_incr csG _)
      obtain ⟨n1, sG, vals', h_r1, h_invG, -, h_l, h_val, h_rel, -, -⟩ :=
        readToReg_simR hWF h_d h_inv h_e h_codeG
      rw [hv] at h_val
      have hr := Except.ok.inj h_val
      rw [← hr] at h_l
      rw [h_v] at h_rel
      have hv' := word_of_storeSim h_rel
      subst hv'
      rw [hcG] at h_invG
      have h_pcG : sG.pc = csG.nextLabel := h_invG.pc
      have h_chk : compProg csG.nextLabel = some (oseair.Instr.Check r vals member) :=
        h_code _ _ (by simp [compile.emit]) (by simp [compile.emit])
      have h_run2 : oseair.runN MSB 1 sG compProg = .Ok { sG with pc := sG.pc + 1 } := by
        simp only [oseair.runN, oseair.step, h_pcG, h_chk, h_l, h_mem, if_true]
      have h_fin := h_invG.retarget (cs' := compile.emit csG [oseair.Instr.Check r vals member])
        rfl (Nat.le_refl _)
      have h_pc' : ({ sG with pc := (compile.emit csG [oseair.Instr.Check r vals member]).nextLabel }
          : oseair.State MSB) = { sG with pc := sG.pc + 1 } := by
        simp [compile.emit, h_pcG]
      rw [h_pc'] at h_fin
      exact ⟨ρt, _, n1 + 1, TagRenameIncr.refl ρt, runN_trans h_r1 h_run2, h_fin.src_pc⟩

end obseq3.proof
