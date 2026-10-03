import obseq3.byteproof.prmpres

/-!
# The guarded assignment: `assignIf`

`if discr == val { dst := rhs }`. Compiled as the destination's root
`Alloc` (on both paths, as the source's `ensureRoot`), the discriminant's
register read, a `SkipIf` over a RESERVED label, and the assignment's code
compiled from after it. Taken: the assignment leaf (`StmtSimB` for
`.assign dst rhs`) runs from the reserved label's successor. Not taken:
the target jumps over the body, whose compile state differs from the
guard's only in labels and registers — its place map is the guard's
(`compileAssign_prm`, `ensurePlaceRoot_idem`), so the invariant carries.
-/

namespace obseq3.byteproof

open obseq3 obseq3.bytes obseq3.proof
open obseq3.mirlite (MemValue Binding Env PlaceRes)
open obseq3.oseair (Val Register)
open obseq3.compileB

/-! ## Compile-time -/

theorem compileAssign_prm {Γ : Ctx} {L : mirliteB.LayEnv Γ} {τ : LayoutTy}
    (dst : Place Γ τ) (rhs : RExpr Γ τ) (cs : CompilerState) :
    (CheckedCompilerM.run (compileAssignChecked L dst rhs) cs).placeRegMap
      = (CompilerM.run (ensurePlaceRoot L dst) cs).placeRegMap := by
  simp only [compileAssignChecked]
  rw [CheckedCompilerM.run_bind, CheckedCompilerM.value_lift]
  dsimp only
  rw [CheckedCompilerM.run_lift]
  generalize CompilerM.run (ensurePlaceRoot L dst) cs = c
  have key : ∀ {β : Type} (X : CheckedCompilerM β), PrmPres X →
      (CheckedCompilerM.run X c).placeRegMap = c.placeRegMap := fun X hX => hX c
  apply key
  apply PrmPres.bind (compileRExprPre_prm _ _)
  intro pre
  prm_tac

/-- Running a root's allocation again, on a state whose place map already
    has it, emits nothing. -/
theorem ensurePlaceRoot_idem {Γ : Ctx} {L : mirliteB.LayEnv Γ} :
    ∀ {τ : LayoutTy} (dst : Place Γ τ) (c c' : CompilerState),
      c'.placeRegMap = (CompilerM.run (ensurePlaceRoot L dst) c).placeRegMap →
      CompilerM.run (ensurePlaceRoot L dst) c' = c'
  | _, .local loc, c, c', h => by
      have h_mapped : getPlaceInfo c' loc.idx.1 ≠ none := by
        intro h_none
        have h_none' : List.lookup loc.idx.1
            (CompilerM.run (ensurePlaceRoot L (.local loc)) c).placeRegMap = none := by
          rw [← h]; exact h_none
        cases h_pi : getPlaceInfo c loc.idx.1 with
        | some rl =>
            obtain ⟨r, l⟩ := rl
            simp only [ensurePlaceRoot, CompilerM.run_bind, CompilerM.run_pure,
              ensureLocalRegE_existing (L := L) h_pi] at h_none'
            rw [show getPlaceInfo c loc.idx.1 = List.lookup loc.idx.1 c.placeRegMap from rfl,
              h_none'] at h_pi
            cases h_pi
        | none =>
            simp only [ensurePlaceRoot, CompilerM.run_bind, CompilerM.run_pure,
              ensureLocalRegE_fresh (L := L) h_pi] at h_none'
            have := getPlaceInfo_freshRoot_self (L := L) c loc
            rw [show getPlaceInfo (freshRootCS L c loc) loc.idx.1
              = List.lookup loc.idx.1 (freshRootCS L c loc).placeRegMap from rfl, h_none'] at this
            cases this
      cases h' : getPlaceInfo c' loc.idx.1 with
      | none => exact absurd h' h_mapped
      | some rl =>
          obtain ⟨r, l⟩ := rl
          simp only [ensurePlaceRoot, CompilerM.run_bind, CompilerM.run_pure,
            ensureLocalRegE_existing (L := L) h']
  | _, .proj base _, c, c', h => ensurePlaceRoot_idem base c c' h
  | _, .deref q, c, c', h => ensurePlaceRoot_idem q c c' h

theorem emitSkipIfAround_ok {α : Type} (r : Register) (val : Word) (body : CheckedCompilerM α)
    (cs : CompilerState) {u : Unit}
    (h : CheckedCompilerM.value (emitSkipIfAround r val body) cs = .ok u) :
    (∃ a, CheckedCompilerM.value body (reserveLabel cs) = .ok a) ∧
    CheckedCompilerM.run (emitSkipIfAround r val body) cs
      = patchLabel (CheckedCompilerM.run body (reserveLabel cs)) cs.nextLabel
          (oseairL.Instr.SkipIf r val
            ((CheckedCompilerM.run body (reserveLabel cs)).nextLabel - (reserveLabel cs).nextLabel)) := by
  simp only [emitSkipIfAround, CheckedCompilerM.value, CheckedCompilerM.run, CompilerM.value,
    CompilerM.run] at h ⊢
  split at h
  · cases h
  · rename_i a h_a
    exact ⟨⟨a, h_a⟩, rfl⟩

theorem assignIf_shape {Γ : Ctx} {L : mirliteB.LayEnv Γ} {τ : LayoutTy}
    (discr : Place Γ (LayoutTy.IntL tN)) (val : Word) (dst : Place Γ τ) (rhs : RExpr Γ τ)
    (cs : CompilerState) {u : ResultWithEvidence Unit (fun _ => StmtEvidence L (.assignIf discr val dst rhs))}
    (h : CheckedCompilerM.value (compileStmtChecked L (.assignIf discr val dst rhs)) cs = .ok u) :
    ∃ r, CheckedCompilerM.value (guardRead L discr) (CompilerM.run (ensurePlaceRoot L dst) cs) = .ok r ∧
      (∃ ub, CheckedCompilerM.value (compileAssignChecked L dst rhs)
        (reserveLabel (CheckedCompilerM.run (guardRead L discr)
          (CompilerM.run (ensurePlaceRoot L dst) cs))) = .ok ub) ∧
      CheckedCompilerM.run (compileStmtChecked L (.assignIf discr val dst rhs)) cs
        = patchLabel (CheckedCompilerM.run (compileAssignChecked L dst rhs)
            (reserveLabel (CheckedCompilerM.run (guardRead L discr)
              (CompilerM.run (ensurePlaceRoot L dst) cs))))
          (CheckedCompilerM.run (guardRead L discr) (CompilerM.run (ensurePlaceRoot L dst) cs)).nextLabel
          (oseairL.Instr.SkipIf r val
            ((CheckedCompilerM.run (compileAssignChecked L dst rhs)
              (reserveLabel (CheckedCompilerM.run (guardRead L discr)
                (CompilerM.run (ensurePlaceRoot L dst) cs)))).nextLabel
             - (reserveLabel (CheckedCompilerM.run (guardRead L discr)
                (CompilerM.run (ensurePlaceRoot L dst) cs))).nextLabel)) := by
  simp only [compileStmtChecked, CheckedCompilerM.value_bind, CheckedCompilerM.run_bind,
    CheckedCompilerM.value_lift, CheckedCompilerM.run_lift] at h ⊢
  split at h
  · rename_i r h_r
    split at h
    · rename_i v h_v
      obtain ⟨hb, h_run⟩ := emitSkipIfAround_ok r val _ _ h_v
      refine ⟨r, h_r, hb, ?_⟩
      simp only [CheckedCompilerM.run_pure, h_run]
    · cases h
  · cases h

/-! ## The root prologue and retargeting -/

theorem ensureRoot_sim {Γ : Ctx} {L : mirliteB.LayEnv Γ} {compProg : oseairL.Prog} :
    ∀ {τ : LayoutTy} (dst : Place Γ τ) {ρt : TagRenameMap} {s s0 : mirliteB.State MSB Γ}
      {sA : oseairL.State MSB} {cs : CompilerState},
      InvAtB L ρt s sA cs → mirliteB.ensureRoot MSB L s dst = .ok s0 →
      CodeIncludedB compProg (CompilerM.run (ensurePlaceRoot L dst) cs) →
      ∃ (ρt' : TagRenameMap) (sA' : oseairL.State MSB) (n : Nat),
        TagRenameIncr ρt ρt' ∧ oseairL.runN MSB n sA compProg = .Ok sA' ∧
        InvAtB L ρt' s0 sA' (CompilerM.run (ensurePlaceRoot L dst) cs)
  | _, .local loc, ρt, s, s0, sA, cs, h_inv, h_er, h_code => by
      simp only [mirliteB.ensureRoot] at h_er
      split at h_er
      · rename_i b h_env
        simp only [mirliteB.Result.ok.injEq] at h_er
        subst h_er
        obtain ⟨r, t, hpi, -⟩ := h_inv.lbs loc b h_env
        have h_run : CompilerM.run (ensurePlaceRoot L (.local loc)) cs = cs := by
          simp only [ensurePlaceRoot, CompilerM.run_bind, CompilerM.run_pure,
            ensureLocalRegE_existing (L := L) hpi]
        rw [h_run]
        exact ⟨ρt, sA, 0, TagRenameIncr.refl ρt, rfl, h_inv⟩
      · rename_i h_env
        have h_pi := h_inv.unmap loc h_env
        have h_run : CompilerM.run (ensurePlaceRoot L (.local loc)) cs = freshRootCS L cs loc := by
          simp only [ensurePlaceRoot, CompilerM.run_bind, CompilerM.run_pure,
            ensureLocalRegE_fresh (L := L) h_pi]
        rw [h_run] at h_code ⊢
        have h_alloc_instr : compProg sA.pc = some (oseairL.Instr.Assgn (Register.R cs.nextReg)
            (oseairL.Rhs.Alloc (L loc.idx))) := by
          rw [h_inv.pc]
          apply h_code
          · simp [freshRootCS, setPlaceInfo, emit]
          · simp [freshRootCS, setPlaceInfo, emit]
        obtain ⟨ρt', sA1, h_incr, h_run1, h_inv1, -⟩ :=
          freshroot_prologue h_inv h_env h_er h_alloc_instr
        exact ⟨ρt', sA1, 1, h_incr, h_run1, h_inv1⟩
  | _, .proj base _, ρt, s, s0, sA, cs, h_inv, h_er, h_code =>
      ensureRoot_sim base h_inv (by simpa [mirliteB.ensureRoot] using h_er) h_code
  | _, .deref q, ρt, s, s0, sA, cs, h_inv, h_er, h_code =>
      ensureRoot_sim q h_inv (by simpa [mirliteB.ensureRoot] using h_er) h_code

/-- The invariant moves to another compile state with the same place map
    (and no fewer registers), the target pc following its label. -/
theorem InvAtB.retarget {Γ : Ctx} {L : mirliteB.LayEnv Γ} {ρt : TagRenameMap}
    {s : mirliteB.State MSB Γ} {sA : oseairL.State MSB} {cs cs' : CompilerState}
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

theorem InvAtB.src_pc {Γ : Ctx} {L : mirliteB.LayEnv Γ} {ρt : TagRenameMap}
    {s : mirliteB.State MSB Γ} {sA : oseairL.State MSB} {cs : CompilerState} {p : Nat}
    (h : InvAtB L ρt s sA cs) : InvAtB L ρt { s with pc := p } sA cs :=
  ⟨h.pc, h.lbs, h.mem, h.alloc, h.psim, h.wf_t, h.tbd, h.unmap, h.prb⟩

/-! ## The leaf -/

theorem assignIf_simB {Γ : Ctx} {L : mirliteB.LayEnv Γ} {compProg : oseairL.Prog}
    (hWF : PtrPlacesWF L) {τ : LayoutTy} {discr : Place Γ (LayoutTy.IntL tN)} {val : Word}
    {dst : Place Γ τ} {rhs : RExpr Γ τ}
    (h_d : ReadSrcB discr) (h_body : StmtSimB L compProg (.assign dst rhs))
    {ρt : TagRenameMap} {s_mir s_mir' : mirliteB.State MSB Γ} {s_osea : oseairL.State MSB}
    {cs : CompilerState} (h_inv : InvAtB L ρt s_mir s_osea cs)
    {u : ResultWithEvidence Unit (fun _ => StmtEvidence L (.assignIf discr val dst rhs))}
    (h_ok : CheckedCompilerM.value (compileStmtChecked L (.assignIf discr val dst rhs)) cs = .ok u)
    (h_code : CodeIncludedB compProg
      (CheckedCompilerM.run (compileStmtChecked L (.assignIf discr val dst rhs)) cs))
    (h_step : mirliteB.stepStmt MSB L s_mir (.assignIf discr val dst rhs) = .ok s_mir') :
    ∃ (ρt' : TagRenameMap) (s_osea' : oseairL.State MSB) (n : Nat),
      TagRenameIncr ρt ρt' ∧ oseairL.runN MSB n s_osea compProg = .Ok s_osea' ∧
      InvAtB L ρt' s_mir' s_osea'
        (CheckedCompilerM.run (compileStmtChecked L (.assignIf discr val dst rhs)) cs) := by
  obtain ⟨r, h_r, ⟨ub, h_ub⟩, h_shape⟩ := assignIf_shape (L := L) discr val dst rhs cs h_ok
  rw [h_shape] at h_code ⊢
  -- names for the compile states
  generalize hc0 : CompilerM.run (ensurePlaceRoot L dst) cs = c0 at h_r h_ub h_code ⊢
  generalize hcG : CheckedCompilerM.run (guardRead L discr) c0 = csG at h_ub h_code ⊢
  generalize hcB : CheckedCompilerM.run (compileAssignChecked L dst rhs) (reserveLabel csG) = cB
    at h_code ⊢
  have h_iG : StateIncr c0 csG := hcG ▸ CheckedCompilerM.incr _ _
  have h_iB : StateIncr (reserveLabel csG) cB := hcB ▸ CheckedCompilerM.incr _ _
  have h_iR := reserveLabel_state_incr csG
  have h_nlB : csG.nextLabel + 1 ≤ cB.nextLabel := h_iB.nextLabel_le
  -- what the patched final state includes
  have h_below : ∀ q, q < csG.nextLabel →
      (patchLabel cB csG.nextLabel (oseairL.Instr.SkipIf r val
        (cB.nextLabel - (reserveLabel csG).nextLabel))).code q = csG.code q := fun q hq => by
    show (if q = csG.nextLabel then _ else cB.code q) = _
    rw [if_neg (by omega), h_iB.code_eq q (by show q < csG.nextLabel + 1; omega)]
    exact h_iR.code_eq q hq
  have h_codeG : CodeIncludedB compProg csG := fun q i hq hc => by
    apply h_code q i (by show q < cB.nextLabel; omega)
    rw [h_below q hq]; exact hc
  have h_codeB : CodeIncludedB compProg cB := fun q i hq hc => by
    apply h_code q i hq
    show (if q = csG.nextLabel then _ else cB.code q) = _
    by_cases hq' : q = csG.nextLabel
    · subst hq'
      rw [h_iB.code_eq _ (by show csG.nextLabel < csG.nextLabel + 1; omega)] at hc
      simp [reserveLabel] at hc
    · rw [if_neg hq']; exact hc
  have h_skip : compProg csG.nextLabel = some (oseairL.Instr.SkipIf r val
      (cB.nextLabel - (reserveLabel csG).nextLabel)) :=
    h_code _ _ (by show csG.nextLabel < cB.nextLabel; omega) (by simp [patchLabel])
  -- the source: root, discriminant, branch
  simp only [mirliteB.stepStmt] at h_step
  split at h_step
  · cases h_step
  rename_i s0 h_er
  split at h_step
  · cases h_step
  rename_i out h_e
  split at h_step
  case h_2 => cases h_step
  rename_i v h_v
  -- the root prologue
  obtain ⟨ρt0, sA0, n0, h_i0, h_r0, h_inv0⟩ :=
    ensureRoot_sim dst h_inv h_er (by rw [hc0]; exact h_codeG.mono h_iG)
  rw [hc0] at h_inv0
  -- the discriminant's read
  have hcG' : CheckedCompilerM.run (readToReg L discr) c0 = csG := hcG
  have h_codeR : CodeIncludedB compProg (CheckedCompilerM.run (readToReg L discr) c0) := by
    rw [hcG']; exact h_codeG
  obtain ⟨n1, sG, vals, h_r1, h_invG, -, h_l, h_val, h_rel, -, -⟩ :=
    readToReg_simR hWF h_d h_inv0 h_e h_codeR
  have h_rr : r = Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared discr) c0).nextReg := by
    have : CheckedCompilerM.value (guardRead L discr) c0 = _ := h_val
    rw [h_r] at this
    exact Except.ok.inj this
  rw [h_v] at h_rel
  have hv1 := word_of_storeSim h_rel
  subst hv1
  rw [← h_rr] at h_l
  rw [hcG'] at h_invG
  have h_pcG : sG.pc = csG.nextLabel := h_invG.pc
  split at h_step
  · -- taken: the body is the assignment, from the reserved label's successor
    rename_i h_eq
    have h_run2 : oseairL.runN MSB 1 sG compProg = .Ok { sG with pc := sG.pc + 1 } := by
      simp only [oseairL.runN, oseairL.step, h_pcG, h_skip, h_l, h_eq, if_true]
    have h_inv1 : InvAtB L ρt0 out.state { sG with pc := sG.pc + 1 } (reserveLabel csG) := by
      have := h_invG.retarget (cs' := reserveLabel csG) rfl (Nat.le_refl _)
      simp only [reserveLabel] at this ⊢
      rw [h_pcG]; exact this
    obtain ⟨ρt', s', n2, h_i2, h_r2, h_inv2⟩ :=
      h_body ρt0 out.state s_mir' _ (reserveLabel csG) h_inv1
        (by show CodeIncludedB compProg (CheckedCompilerM.run (compileAssignChecked L dst rhs) _)
            rw [hcB]; exact h_codeB) h_step
    have h_inv2' : InvAtB L ρt' s_mir' s' cB := by
      rw [← hcB]; exact h_inv2
    refine ⟨ρt', s', n0 + n1 + 1 + n2, h_i0.trans h_i2,
      runN_trans (runN_trans (runN_trans h_r0 h_r1) h_run2) h_r2, ?_⟩
    have := h_inv2'.retarget (cs' := patchLabel cB csG.nextLabel (oseairL.Instr.SkipIf r val
      (cB.nextLabel - (reserveLabel csG).nextLabel))) rfl (Nat.le_refl _)
    have h_spc : { s' with pc := (patchLabel cB csG.nextLabel (oseairL.Instr.SkipIf r val
        (cB.nextLabel - (reserveLabel csG).nextLabel))).nextLabel } = s' := by
      show { s' with pc := cB.nextLabel } = s'
      rw [← h_inv2'.pc]
    rw [h_spc] at this
    exact this
  · -- not taken: jump over the body
    rename_i h_ne
    simp only [mirliteB.Result.ok.injEq] at h_step
    subst h_step
    have h_run2 : oseairL.runN MSB 1 sG compProg = .Ok
        { sG with pc := sG.pc + 1 + (cB.nextLabel - (reserveLabel csG).nextLabel) } := by
      simp only [oseairL.runN, oseairL.step, h_pcG, h_skip, h_l, h_ne, Bool.false_eq_true,
        if_false]
    have h_prm : (patchLabel cB csG.nextLabel (oseairL.Instr.SkipIf r val
        (cB.nextLabel - (reserveLabel csG).nextLabel))).placeRegMap = csG.placeRegMap := by
      show cB.placeRegMap = csG.placeRegMap
      rw [← hcB, compileAssign_prm, ensurePlaceRoot_idem dst cs (reserveLabel csG)]
      · rfl
      · show csG.placeRegMap = _
        rw [← hcG']
        show (CheckedCompilerM.run (readToReg L discr) c0).placeRegMap = _
        rw [readToReg_prm discr c0, ← hc0]
    have := h_invG.retarget (cs' := patchLabel cB csG.nextLabel (oseairL.Instr.SkipIf r val
      (cB.nextLabel - (reserveLabel csG).nextLabel))) h_prm
      (Nat.le_trans h_iR.nextReg_le h_iB.nextReg_le)
    have h_tpc : sG.pc + 1 + (cB.nextLabel - (reserveLabel csG).nextLabel)
        = (patchLabel cB csG.nextLabel (oseairL.Instr.SkipIf r val
          (cB.nextLabel - (reserveLabel csG).nextLabel))).nextLabel := by
      show sG.pc + 1 + (cB.nextLabel - (csG.nextLabel + 1)) = cB.nextLabel
      omega
    refine ⟨ρt0, _, n0 + n1 + 1, h_i0, runN_trans (runN_trans h_r0 h_r1) h_run2, ?_⟩
    rw [h_tpc]
    exact this.src_pc

end obseq3.byteproof
