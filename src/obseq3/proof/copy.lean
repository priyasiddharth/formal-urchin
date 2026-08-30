import obseq3.proof.common
import obseq3.proof.permsim_transport
import obseq3.proof.spine

namespace obseq3.proof

open obseq3
open obseq3.compile
open obseq3.oseair (Instr Register Rhs Val)

/-- The fragment of `dst := copy src` for a mapped local dst and ANY
    source place, stated over the OPAQUE run of the source lowering:
    the src-lowering code (whatever it emits — the mother lemma owns
    it), then the READ into a fresh register (`Load`), then the write
    (`RStore`). The read-before-write shape is rustc's; see
    notes/2026-09-03-copy-nonlocal-dst-order.md. -/
theorem compileStmt_copy_chainsrc_run
    {Γ : Ctx} {τ : LayoutTy}
    {dstLoc : Local Γ τ}
    {src : Place Γ τ}
    {cs : CompilerState} {dstReg : Register}
    {sOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared src)}
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = some (dstReg, τ))
    (h_sval : CheckedCompilerM.value (placeToRegChecked RefKind.Shared src) cs
      = Except.ok sOut)
    (h_sclean : sOut.result.cleanup = []) :
    CheckedCompilerM.run
        (compileStmtChecked
          (Stmt.assign (.local dstLoc) (.copy src))) cs
      = emit (emit
          { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) cs) with
              nextReg := (CheckedCompilerM.run
                (placeToRegChecked RefKind.Shared src) cs).nextReg + 1 }
          [Instr.Assgn (Register.R (CheckedCompilerM.run
              (placeToRegChecked RefKind.Shared src) cs).nextReg)
            (Rhs.Load (obseq.layoutToTyVal τ) sOut.result.reg)])
          [Instr.RStore (obseq.layoutToTyVal τ)
            (Register.R (CheckedCompilerM.run
              (placeToRegChecked RefKind.Shared src) cs).nextReg) dstReg] := by
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_existing h_dst
  have h_run' : (ensureLocalRegE dstLoc cs).snd.val = cs := h_run
  simp [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked,
    h_run, h_run', h_val, h_sval]
  simp [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM,
    cleanupInstrs, h_sclean, emit_nil]

/-- The chain-src copy lowers. -/
theorem compileStmt_copy_chainsrc_value
    {Γ : Ctx} {τ : LayoutTy}
    {dstLoc : Local Γ τ}
    {src : Place Γ τ}
    {cs : CompilerState} {dstReg : Register}
    {sOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared src)}
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = some (dstReg, τ))
    (h_sval : CheckedCompilerM.value (placeToRegChecked RefKind.Shared src) cs
      = Except.ok sOut) :
    ∃ so, CheckedCompilerM.value
      (compileStmtChecked
        (Stmt.assign (.local dstLoc) (.copy src))) cs
      = Except.ok so := by
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_existing h_dst
  simp only [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
    h_run, h_sval]
  exact ⟨_, rfl⟩

/-! ## Flatten transfer for the copy-src shape -/

theorem compileRExprToChecked_copysrc_flatten_run
    {Γ : Ctx} {τ : LayoutTy} {P : Place Γ (obseq.LayoutTy.PtrL τ)}
    (r : Register) (cs : CompilerState) :
    CheckedCompilerM.run
        (compileRExprToChecked r (RExpr.copy (Γ := Γ) (.deref P))) cs
      = CheckedCompilerM.run
          (compileRExprToChecked r (RExpr.copy (.deref (flattenPlace P)))) cs := by
  obtain ⟨h_agr, h_agv⟩ :=
    placeToRegChecked_flatten_agree (Place.deref P) RefKind.Shared cs
  rw [show flattenPlace (Place.deref P) = Place.deref (flattenPlace P) from rfl]
    at h_agr h_agv
  simp only [compileRExprToChecked, compileRExprPreChecked,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure]
  cases hF : CheckedCompilerM.value
      (placeToRegChecked RefKind.Shared (Place.deref (flattenPlace P))) cs with
  | error eF =>
      cases hO : CheckedCompilerM.value
          (placeToRegChecked RefKind.Shared (Place.deref P)) cs with
      | error eO =>
          simp only [hF, hO]
          exact h_agr.symm
      | ok oO =>
          exfalso
          rw [hF, hO] at h_agv
          simp [Except.map] at h_agv
  | ok oF =>
      cases hO : CheckedCompilerM.value
          (placeToRegChecked RefKind.Shared (Place.deref P)) cs with
      | error eO =>
          exfalso
          rw [hF, hO] at h_agv
          simp [Except.map] at h_agv
      | ok oO =>
          have h_res : oF.result = oO.result := by
            rw [hF, hO] at h_agv
            simpa [Except.map] using h_agv
          simp only [hF, hO, h_res]
          rw [h_agr]

theorem compileRExprToChecked_copysrc_flatten_valunit
    {Γ : Ctx} {τ : LayoutTy} {P : Place Γ (obseq.LayoutTy.PtrL τ)}
    (r : Register) (cs : CompilerState) :
    (CheckedCompilerM.value
        (compileRExprToChecked r (RExpr.copy (Γ := Γ) (.deref P))) cs).map
      (fun _ => ())
      = (CheckedCompilerM.value
          (compileRExprToChecked r (RExpr.copy (.deref (flattenPlace P)))) cs).map
        (fun _ => ()) := by
  obtain ⟨h_agr, h_agv⟩ :=
    placeToRegChecked_flatten_agree (Place.deref P) RefKind.Shared cs
  rw [show flattenPlace (Place.deref P) = Place.deref (flattenPlace P) from rfl]
    at h_agr h_agv
  simp only [compileRExprToChecked, compileRExprPreChecked,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure]
  cases hF : CheckedCompilerM.value
      (placeToRegChecked RefKind.Shared (Place.deref (flattenPlace P))) cs with
  | error eF =>
      cases hO : CheckedCompilerM.value
          (placeToRegChecked RefKind.Shared (Place.deref P)) cs with
      | error eO =>
          have h_e : eF = eO := by
            rw [hF, hO] at h_agv
            simpa [Except.map] using h_agv
          subst h_e
          simp [hF, hO, Except.map]
      | ok oO =>
          exfalso
          rw [hF, hO] at h_agv
          simp [Except.map] at h_agv
  | ok oF =>
      cases hO : CheckedCompilerM.value
          (placeToRegChecked RefKind.Shared (Place.deref P)) cs with
      | error eO =>
          exfalso
          rw [hF, hO] at h_agv
          simp [Except.map] at h_agv
      | ok oO =>
          simp [hF, hO, Except.map]

theorem compileStmt_copy_derefsrc_flatten_run
    {Γ : Ctx} {τ : LayoutTy}
    {dstLoc : Local Γ τ} {P : Place Γ (obseq.LayoutTy.PtrL τ)}
    (cs : CompilerState) :
    CheckedCompilerM.run
        (compileStmtChecked
          (Stmt.assign (.local dstLoc) (.copy (.deref P)))) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.local dstLoc) (.copy (.deref (flattenPlace P))))) cs := by
  simp only [compileStmtChecked,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure]
  have h_run := compileRExprToChecked_copysrc_flatten_run (Γ := Γ) (P := P)
    ((ensureLocalRegE dstLoc).value cs).result.reg
    (CompilerM.run (ensureLocalRegE dstLoc) cs)
  have h_val := compileRExprToChecked_copysrc_flatten_valunit (Γ := Γ) (P := P)
    ((ensureLocalRegE dstLoc).value cs).result.reg
    (CompilerM.run (ensureLocalRegE dstLoc) cs)
  cases hO : CheckedCompilerM.value
      (compileRExprToChecked ((ensureLocalRegE dstLoc).value cs).result.reg
        (RExpr.copy (Γ := Γ) (.deref P)))
      (CompilerM.run (ensureLocalRegE dstLoc) cs) with
  | error eO =>
      cases hF : CheckedCompilerM.value
          (compileRExprToChecked ((ensureLocalRegE dstLoc).value cs).result.reg
            (RExpr.copy (.deref (flattenPlace P))))
          (CompilerM.run (ensureLocalRegE dstLoc) cs) with
      | error eF =>
          simp only [hO, hF]
          exact h_run
      | ok oF =>
          exfalso
          rw [hO, hF] at h_val
          simp [Except.map] at h_val
  | ok oO =>
      cases hF : CheckedCompilerM.value
          (compileRExprToChecked ((ensureLocalRegE dstLoc).value cs).result.reg
            (RExpr.copy (.deref (flattenPlace P))))
          (CompilerM.run (ensureLocalRegE dstLoc) cs) with
      | error eF =>
          exfalso
          rw [hO, hF] at h_val
          simp [Except.map] at h_val
      | ok oF =>
          simp only [hO, hF]
          exact h_run

theorem compileStmt_copy_derefsrc_flatten_value
    {Γ : Ctx} {τ : LayoutTy}
    {dstLoc : Local Γ τ} {P : Place Γ (obseq.LayoutTy.PtrL τ)}
    (cs : CompilerState) :
    ∀ so, CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.local dstLoc) (.copy (.deref (flattenPlace P))))) cs
      = Except.ok so →
    ∃ so', CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.local dstLoc) (.copy (.deref P)))) cs
      = Except.ok so' := by
  intro so h_so
  have h_val := compileRExprToChecked_copysrc_flatten_valunit (Γ := Γ) (P := P)
    ((ensureLocalRegE dstLoc).value cs).result.reg
    (CompilerM.run (ensureLocalRegE dstLoc) cs)
  simp only [compileStmtChecked,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure] at h_so ⊢
  cases hO : CheckedCompilerM.value
      (compileRExprToChecked ((ensureLocalRegE dstLoc).value cs).result.reg
        (RExpr.copy (Γ := Γ) (.deref P)))
      (CompilerM.run (ensureLocalRegE dstLoc) cs) with
  | error eO =>
      exfalso
      cases hF : CheckedCompilerM.value
          (compileRExprToChecked ((ensureLocalRegE dstLoc).value cs).result.reg
            (RExpr.copy (.deref (flattenPlace P))))
          (CompilerM.run (ensureLocalRegE dstLoc) cs) with
      | error eF =>
          rw [hF] at h_so
          simp at h_so
      | ok oF =>
          rw [hO, hF] at h_val
          simp [Except.map] at h_val
  | ok oO =>
      simp only [hO]
      exact ⟨_, rfl⟩

/-- REGIME D→L over full chains, COLLAPSED 2026-08-31 (originally
    closed 2026-08-29 for load spines): `dst := copy *P` for every src
    with `PtrChain src` — spines, proj-topped pointer places
    (`x := copy *(s.f)`), interior projections at any depth. The mother
    lemma at `Shared` on the WHOLE source place performs the lowering
    including the final `Load`; the leaf adds one `Memcpy` whose source
    bound is the copy-range dereferenceability check and whose
    nonoverlapping check is the overlap guard via
    `resolvePlace?_of_resolveAcc`. No tag survives: renames grow by
    `refl`. -/
theorem copy_chainsrc_local_simulation
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {τ : LayoutTy}
    {dstLoc : Local Γ τ}
    {src : Place Γ τ}
    {bD : mirlite.Binding}
    (compProg : oseair.Prog)
    (h_chain : PtrChain src)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    {stmt0 : Stmt Γ}
    (h_stmt : prog.get? s_mir.pc = some stmt0)
    (h_run0 : ∀ cs, CheckedCompilerM.run (compileStmtChecked stmt0) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.local dstLoc) (.copy src))) cs)
    (h_val0 : ∀ cs so, CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.local dstLoc) (.copy src))) cs
        = Except.ok so →
      ∃ so', CheckedCompilerM.value (compileStmtChecked stmt0) cs
        = Except.ok so')
    (h_envD : mirlite.Env.lookup s_mir.env dstLoc = some bD)
    (h_step : mirlite.stepStmt MSB s_mir
      (.assign (.local dstLoc) (.copy src)) = .ok s_mir') :
    ∃ (s_osea' : oseair.State MSB) (n : Nat),
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa ρt s_mir' s_osea' := by
  obtain ⟨csPrefix, ⟨h_csAt, h_pc⟩, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_tbd,
    h_alloc, h_unmap, h_prb⟩ := h_inv
  obtain ⟨dstReg, baseD, tagD, h_piD, h_entryD, h_raD, h_rtD, h_nwD, h_domD⟩ :=
    h_lbs dstLoc bD h_envD
  have h_baseD : baseD = bD.addr := (h_id_a _ _ h_raD).symm
  subst h_baseD
  -- §1 invert: prepare is a no-op (bound dst); the rhs resolves the
  -- whole src place ACC-style (kept OPAQUE for the mother lemma),
  -- checks the range, and wide-reads through the resolved tag
  simp only [mirlite.stepStmt, mirlite.doAssign] at h_step
  cases h_prep : mirlite.preparePlaceAssign MSB s_mir (Place.local dstLoc) with
  | err msg => rw [h_prep] at h_step; simp at h_step
  | ok s1 =>
  rw [h_prep] at h_step
  have h_s1 : s1 = s_mir := by
    simp only [mirlite.preparePlaceAssign, mirlite.resolvePlace?, h_envD] at h_prep
    grind
  rw [h_s1] at h_step
  simp only [mirlite.evalRExpr] at h_step
  cases h_dres : mirlite.resolvePlaceAcc MSB s_mir src with
  | error e => rw [h_dres] at h_step; simp at h_step
  | ok pr =>
  obtain ⟨rs, permsP'⟩ := pr
  rw [h_dres] at h_step
  simp only at h_step
  by_cases h_fit : rs.addr + blockSize τ > rs.allocBase + rs.allocSize
  · rw [if_pos h_fit] at h_step
    simp at h_step
  · rw [if_neg h_fit] at h_step
    cases h_read_src : MSB.read permsP' rs.addr (blockSize τ) rs.tag with
    | error e => rw [h_read_src] at h_step; simp at h_step
    | ok perms₂ =>
    rw [h_read_src] at h_step
    simp only [mirlite.resolvePlaceAcc, h_envD] at h_step
    -- §2 compiler scaffolding: mapped-ness, statement value,
    -- code-inclusion for the whole src-place lowering
    have h_mapped : PlaceInputsMapped csPrefix src :=
      placeInputsMapped_of_localBindingSim_resolvePlace h_lbs
        (resolvePlace?_of_resolveAcc h_dres)
    obtain ⟨sOut0, h_sval0⟩ := placeToRegChecked_ok_of_placeInputsMapped
      (cs := csPrefix) (kind := RefKind.Shared) h_mapped
    obtain ⟨stmtOutC, h_stmtOutC⟩ :=
      compileStmt_copy_chainsrc_value h_piD h_sval0
    obtain ⟨stmtOut, h_stmtOut⟩ := h_val0 csPrefix stmtOutC h_stmtOutC
    have h_incrS : StateIncr
        (CheckedCompilerM.run
          (placeToRegChecked RefKind.Shared src) csPrefix)
        (CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix) := by
      rw [h_run0]
      obtain ⟨h_erun, h_eval⟩ := ensureLocalRegE_existing h_piD
      simp only [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked,
        CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
        CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
        CheckedCompilerM.run_pure, CheckedCompilerM.value_pure, h_erun, h_sval0]
      simp only [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM]
      exact StateIncr.trans (freshReg_state_incr _)
        (StateIncr.trans (emit_state_incr _ _)
          (StateIncr.trans (emit_state_incr _ _) (emit_state_incr _ _)))
    have h_instS : ∀ q' instr,
        q' < (CheckedCompilerM.run
          (placeToRegChecked RefKind.Shared src) csPrefix).nextLabel →
        (CheckedCompilerM.run
          (placeToRegChecked RefKind.Shared src) csPrefix).code q'
          = some instr →
        compProg q' = some instr := by
      intro q' instr h_lt h_code
      refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
      · exact Nat.lt_of_lt_of_le h_lt h_incrS.nextLabel_le
      · rw [h_incrS.code_eq q' h_lt]
        exact h_code
    -- §3 the mother lemma on the WHOLE src place (through the Load)
    obtain ⟨sOut, n1, s_mid, tres, h_sval, h_sclean, h_srun, h_spc, h_smem,
      h_spsim, h_snt1, h_snt2, h_slbs, h_sentry, h_srt, h_snw, h_sle, h_srange,
      h_sbelow, h_sprm, h_sregmono, h_slabmono, -, -⟩ :=
      ptrChain_lowering_sim h_id_a h_wf_t h_chain RefKind.Shared csPrefix s_osea
        rs permsP' h_dres h_tbd h_lbs h_prb h_sms h_psim h_pc h_instS
    have h_stmtRun := (h_run0 csPrefix).trans
      (compileStmt_copy_chainsrc_run h_piD h_sval h_sclean)
    have h_cancel : rs.allocBase + (rs.addr - rs.allocBase) = rs.addr :=
      Nat.add_sub_cancel' h_sle
    -- §4 transports: the wide read through the resolved tag, then the
    -- dst write
    obtain ⟨p2w, h_read2_tgt, h_psim2w⟩ :=
      sb_read_respects_PermSim h_spsim h_wf_t h_srt h_snw h_read_src
    have h_w := h_step
    simp only [mirlite.writeResolvedPlace] at h_w
    split at h_w
    · simp at h_w
    · rename_i h_nb
      split at h_w
      · rename_i perms₃ h_useMut_src
        cases h_w
        have h_useMut_src' : MSB.useMut perms₂ bD.addr (blockSize τ) bD.tag
            = .ok perms₃ := by
          grind
        obtain ⟨dstReg2, baseD2, tagD2, h_piD2, h_entryD2, h_raD2, h_rtD2,
          h_nwD2, -⟩ := h_slbs dstLoc bD h_envD
        have h_dr2 : dstReg2 = dstReg := by grind
        have h_baseD2 : baseD2 = bD.addr := (h_id_a _ _ h_raD2).symm
        rw [h_dr2, h_baseD2] at h_entryD2
        obtain ⟨p3w, h_useMut_tgt, h_psim3w⟩ :=
          sb_write_respects_PermSim h_psim2w h_wf_t h_rtD2 h_nwD2 h_useMut_src'
        -- §5 execute the READ into the temporary, then the write
        have h_ts : obseq.typeSize (obseq.layoutToTyVal τ) = blockSize τ := by
          simp [blockSize]
        have h_tmp : Register := Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg
        have h_code1 : compProg s_mid.pc
            = some (Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg)
                (Rhs.Load (obseq.layoutToTyVal τ) sOut.result.reg)) := by
          rw [h_spc]
          refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
          · rw [h_stmtRun]
            simp only [emit, List.length_cons, List.length_nil]
            omega
          · rw [h_stmtRun]
            rw [emit_code_lt_nextLabel _ _ (by
              simp only [emit, List.length_cons, List.length_nil]; omega)]
            have h := emit_code_at_new
              { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix) with
                  nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg + 1 }
              [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg)
                (Rhs.Load (obseq.layoutToTyVal τ) sOut.result.reg)]
              (k := 0) (by simp)
            simpa using h
        have h_code2 : compProg (s_mid.pc + 1)
            = some (Instr.RStore (obseq.layoutToTyVal τ)
                (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg) dstReg) := by
          rw [h_spc]
          refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
          · rw [h_stmtRun]
            simp only [emit, List.length_cons, List.length_nil]
            omega
          · rw [h_stmtRun]
            have h := emit_code_at_new
              (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix) with
                  nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg + 1 }
                [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg)
                  (Rhs.Load (obseq.layoutToTyVal τ) sOut.result.reg)])
              [Instr.RStore (obseq.layoutToTyVal τ)
                (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg) dstReg]
              (k := 0) (by simp)
            simpa [emit] using h
        have h_read2t : MSB.read s_mid.perms
            (rs.allocBase + (rs.addr - rs.allocBase))
            (obseq.typeSize (obseq.layoutToTyVal τ)) tres = .ok p2w := by
          rw [h_ts, h_cancel]
          exact h_read2_tgt
        have h_run1 := runN_Assgn_Load_ptr_step compProg s_mid
          (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg) sOut.result.reg
          (obseq.layoutToTyVal τ) h_code1 h_sentry
          (by rw [h_ts]; grind) h_read2t
        rw [h_ts, h_cancel] at h_run1
        -- the destination register survives the fresh temporary
        have h_regne : dstReg ≠ Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg := by
          cases dstReg with
          | R n =>
              have h_lt := h_prb _ _ _ h_piD
              have := h_sregmono
              grind [RegisterBelow]
        have h_dentry2 : oseair.RegMap.lookup
            (oseair.RegMap.insert s_mid.reg
              (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg)
              (obseq.layoutToTyVal τ,
                oseair.readWordSeq s_mid.mem rs.addr (blockSize τ))) dstReg
            = some (obseq.TyVal.PTy, [Val.Ptr bD.addr 0 (blockSize τ) tagD2]) := by
          rw [RegMap.lookup_insert_ne _ h_regne]
          exact h_entryD2
        have h_useMut2t : MSB.useMut p2w (bD.addr + 0)
            (oseair.readWordSeq s_mid.mem rs.addr (blockSize τ)).length tagD2
            = .ok p3w := by
          rw [Nat.add_zero, oseair_readWordSeq_length]
          exact h_useMut_tgt
        have h_wtp : oseair.writeThroughPtr MSB
            { s_mid with
                perms := p2w,
                reg := oseair.RegMap.insert s_mid.reg
                  (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg)
                  (obseq.layoutToTyVal τ,
                    oseair.readWordSeq s_mid.mem rs.addr (blockSize τ)),
                pc := s_mid.pc + 1 }
            dstReg (oseair.readWordSeq s_mid.mem rs.addr (blockSize τ))
            "RStore Invalid Regs"
            = oseair.Result.Ok
              { s_mid with
                  perms := p3w,
                  reg := oseair.RegMap.insert s_mid.reg
                    (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg)
                    (obseq.layoutToTyVal τ,
                      oseair.readWordSeq s_mid.mem rs.addr (blockSize τ)),
                  mem := oseair.writeWordSeq s_mid.mem bD.addr
                    (oseair.readWordSeq s_mid.mem rs.addr (blockSize τ)),
                  pc := s_mid.pc + 1 + 1 } := by
          simp only [oseair.writeThroughPtr, h_dentry2]
          rw [if_neg (by
            rw [oseair_readWordSeq_length, Nat.add_zero]
            exact Nat.not_lt.mpr (Nat.le_refl _))]
          simp only [h_useMut2t]
          rfl
        have h_run2 := runN_RStore_step compProg _ _
          (obseq.layoutToTyVal τ) (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg) dstReg
          _ _ h_code2 (RegMap.lookup_insert_self _ _ _) h_dentry2 h_wtp
        have h_runA := (oseair_runN_add n1 1 s_osea compProg s_mid h_srun).trans h_run1
        have h_run := (oseair_runN_add (n1 + 1) 1 s_osea compProg _ h_runA).trans h_run2
        -- §6 memory: the same values copied at the same addresses
        have h_rel : ListRel (MemValSim ρa ρt)
            (mirlite.readWordSeq s_mir.mem rs.addr (blockSize τ))
            (oseair.readWordSeq s_mid.mem rs.addr (blockSize τ)) := by
          rw [h_smem]
          exact readWordSeq_sim h_id_a h_sms (blockSize τ) rs.addr
        have h_dom : ∀ k,
            k < (mirlite.readWordSeq s_mir.mem rs.addr (blockSize τ)).length →
            ρa (bD.addr + k) = some (bD.addr + k) := by
          intro k hk
          obtain ⟨a', ha'⟩ := h_domD k (by simpa using hk)
          grind [IdentityOnDomain]
        have h_sms' : SourceMemSim ρa ρt
            (mirlite.writeWordSeq s_mir.mem bD.addr
              (mirlite.readWordSeq s_mir.mem rs.addr (blockSize τ)))
            (oseair.writeWordSeq s_mid.mem bD.addr
              (oseair.readWordSeq s_mid.mem rs.addr (blockSize τ))) :=
          SourceMemSim.writeWordSeq_extend h_id_a _ _ _ _ _ h_rel h_dom
            (by rw [h_smem]; exact h_sms)
        -- §7 rebuild the invariant (no rename growth; one fresh register)
        refine ⟨_, n1 + 1 + 1, h_run, ?_⟩
        refine ⟨CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix,
          ⟨prefixCompileState_succ h_csAt h_stmt h_stmtOut, ?_⟩, ?_, h_sms',
          h_psim3w, h_id_a, h_wf_t, ?_, ?_, ?_, ?_⟩
        · show s_mid.pc + 1 + 1 = _
          rw [h_spc, h_stmtRun]
          simp [emit]
        · have h_lbsT : LocalBindingSim ρa ρt s_mir.env
              { s_mid with
                  perms := p3w,
                  reg := oseair.RegMap.insert s_mid.reg
                    (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg)
                    (obseq.layoutToTyVal τ,
                      oseair.readWordSeq s_mid.mem rs.addr (blockSize τ)),
                  mem := oseair.writeWordSeq s_mid.mem bD.addr
                    (oseair.readWordSeq s_mid.mem rs.addr (blockSize τ)),
                  pc := s_mid.pc + 1 + 1 } csPrefix :=
            LocalBindingSim.insert_fresh_reg h_slbs h_prb h_sregmono rfl
          intro τ' loc' binding' h_env'
          obtain ⟨reg', base', tag', h_pi', h_entry', h_ra', h_rt', h_nw', h_dom'⟩ :=
            h_lbsT loc' binding' h_env'
          refine ⟨reg', base', tag', ?_, h_entry', h_ra', h_rt', h_nw', h_dom'⟩
          rw [h_stmtRun, getPlaceInfo_emit, getPlaceInfo_emit, getPlaceInfo_setNextReg]
          show (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).placeRegMap.lookup loc'.idx.1 = _
          rw [h_sprm]
          exact h_pi'
        · show TagRenameBounded ρt perms₃.NextTag p3w.NextTag
          rw [sb_write_NextTag h_useMut_src', sb_read_NextTag h_read_src, h_snt1,
            sb_write_NextTag h_useMut_tgt, sb_read_NextTag h_read2_tgt]
          exact TagRenameBounded.mono h_tbd (Nat.le_refl _) h_snt2
        · simp only [AllocLockstep, mirlite_writeWordSeq_addrStart,
            oseair_writeWordSeq_addrStart, h_smem]
          exact h_alloc
        · intro τ' loc' h_none
          rw [h_stmtRun, getPlaceInfo_emit, getPlaceInfo_emit, getPlaceInfo_setNextReg]
          show (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).placeRegMap.lookup loc'.idx.1 = none
          rw [h_sprm]
          exact h_unmap loc' h_none
        · intro idx reg'' τ'' h_look
          rw [h_stmtRun] at h_look ⊢
          rw [getPlaceInfo_emit, getPlaceInfo_emit, getPlaceInfo_setNextReg] at h_look
          have h_prm2 : (CheckedCompilerM.run
              (placeToRegChecked RefKind.Shared src) csPrefix).placeRegMap
              = csPrefix.placeRegMap := h_sprm
          have h_cs : getPlaceInfo csPrefix idx = some (reg'', τ'') := by
            show csPrefix.placeRegMap.lookup idx = _
            rw [← h_prm2]
            exact h_look
          refine RegisterBelow.mono ?_ (h_prb _ _ _ h_cs)
          simp only [emit]
          exact Nat.le_trans h_sregmono (Nat.le_succ _)
      · simp at h_w

/-! ## Proj-topped sources over CHAIN bases: fragments over the opaque
    base lowering. `placeToRegChecked Shared (.proj B path)` runs B's
    code (the mother lemma owns it), then passes the register through
    at offset zero or mints a `Borrow(Shared)` otherwise; the statement
    adds the `Memcpy` and the cleanup `Die`. -/

theorem compileStmt_copy_projchain_zero_run
    {Γ : Ctx} {τ σb : LayoutTy}
    {dstLoc : Local Γ τ} {B : Place Γ σb} {path : PathTo σb τ}
    {cs : CompilerState} {dstReg : Register}
    {bOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared B)}
    (h_np : ∀ (σ' : LayoutTy) (b : Place Γ σ') (q : PathTo σ' σb), B = b.proj q → False)
    (h_off : pathOffset path = 0)
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = some (dstReg, τ))
    (h_bval : CheckedCompilerM.value (placeToRegChecked RefKind.Shared B) cs
      = Except.ok bOut)
    (h_bclean : bOut.result.cleanup = []) :
    CheckedCompilerM.run
        (compileStmtChecked
          (Stmt.assign (.local dstLoc) (.copy (.proj B path)))) cs
      = emit (emit
          { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs) with
              nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg + 1 }
          [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg)
            (Rhs.Load (obseq.layoutToTyVal τ) bOut.result.reg)])
          [Instr.RStore (obseq.layoutToTyVal τ)
            (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg) dstReg] := by
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_existing h_dst
  have h_run' : (ensureLocalRegE dstLoc cs).snd.val = cs := h_run
  have h_proj_eq := placeToRegChecked_proj_root_eq (Γ := Γ)
    (kind := RefKind.Shared) (base := B) path h_np
  simp only [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked,
    h_proj_eq,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
    h_run, h_run', h_val, h_bval, h_off, dif_pos]
  simp [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM,
    cleanupInstrs, h_bclean, emit_nil]

theorem compileStmt_copy_projchain_zero_value
    {Γ : Ctx} {τ σb : LayoutTy}
    {dstLoc : Local Γ τ} {B : Place Γ σb} {path : PathTo σb τ}
    {cs : CompilerState} {dstReg : Register}
    {bOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared B)}
    (h_np : ∀ (σ' : LayoutTy) (b : Place Γ σ') (q : PathTo σ' σb), B = b.proj q → False)
    (h_off : pathOffset path = 0)
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = some (dstReg, τ))
    (h_bval : CheckedCompilerM.value (placeToRegChecked RefKind.Shared B) cs
      = Except.ok bOut) :
    ∃ so, CheckedCompilerM.value
      (compileStmtChecked
        (Stmt.assign (.local dstLoc) (.copy (.proj B path)))) cs
      = Except.ok so := by
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_existing h_dst
  have h_proj_eq := placeToRegChecked_proj_root_eq (Γ := Γ)
    (kind := RefKind.Shared) (base := B) path h_np
  simp only [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked,
    h_proj_eq,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
    h_run, h_bval, h_off, dif_pos]
  exact ⟨_, rfl⟩

theorem compileStmt_copy_projchain_offset_run
    {Γ : Ctx} {τ σb : LayoutTy}
    {dstLoc : Local Γ τ} {B : Place Γ σb} {path : PathTo σb τ}
    {cs : CompilerState} {dstReg : Register}
    {bOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared B)}
    (h_np : ∀ (σ' : LayoutTy) (b : Place Γ σ') (q : PathTo σ' σb), B = b.proj q → False)
    (h_off : pathOffset path ≠ 0)
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = some (dstReg, τ))
    (h_bval : CheckedCompilerM.value (placeToRegChecked RefKind.Shared B) cs
      = Except.ok bOut)
    (h_bclean : bOut.result.cleanup = []) :
    CheckedCompilerM.run
        (compileStmtChecked
          (Stmt.assign (.local dstLoc) (.copy (.proj B path)))) cs
      = emit (emit
          { (emit
              { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs) with
                  nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg + 1 }
              [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg)
                (borrowRhs RefKind.Shared (blockSize τ) bOut.result.reg
                  (pathOffset path))]) with
              nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg + 1 + 1 }
          [Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg + 1))
            (Rhs.Load (obseq.layoutToTyVal τ)
              (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg)),
           Instr.Die (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg) (blockSize τ)])
          [Instr.RStore (obseq.layoutToTyVal τ)
            (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg + 1)) dstReg] := by
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_existing h_dst
  have h_run' : (ensureLocalRegE dstLoc cs).snd.val = cs := h_run
  have h_proj_eq := placeToRegChecked_proj_root_eq (Γ := Γ)
    (kind := RefKind.Shared) (base := B) path h_np
  simp only [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked,
    h_proj_eq,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
    h_run, h_run', h_val, h_bval]
  simp [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM,
    cleanupInstrs, h_bclean, emit_nil, h_off, borrowRhs]
  rfl

theorem compileStmt_copy_projchain_offset_value
    {Γ : Ctx} {τ σb : LayoutTy}
    {dstLoc : Local Γ τ} {B : Place Γ σb} {path : PathTo σb τ}
    {cs : CompilerState} {dstReg : Register}
    {bOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared B)}
    (h_np : ∀ (σ' : LayoutTy) (b : Place Γ σ') (q : PathTo σ' σb), B = b.proj q → False)
    (h_off : pathOffset path ≠ 0)
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = some (dstReg, τ))
    (h_bval : CheckedCompilerM.value (placeToRegChecked RefKind.Shared B) cs
      = Except.ok bOut) :
    ∃ so, CheckedCompilerM.value
      (compileStmtChecked
        (Stmt.assign (.local dstLoc) (.copy (.proj B path)))) cs
      = Except.ok so := by
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_existing h_dst
  have h_proj_eq := placeToRegChecked_proj_root_eq (Γ := Γ)
    (kind := RefKind.Shared) (base := B) path h_np
  simp only [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked,
    h_proj_eq,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
    h_run, h_bval, dif_neg h_off]
  exact ⟨_, rfl⟩

/-- REGIME P0→L over CHAIN bases, COLLAPSED 2026-09-03: `dst := copy
    B.f` at ZERO offset for ANY canonical chain base `B` — a bound
    local (the old P0→L), a deref chain (`y := copy (*p).f` at offset
    0), any depth. The projection passes the base register through, so
    this is the chain-src leaf with a `+ 0` on the resolution. -/
theorem copy_projchain_zero_simulation
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {τ σb : LayoutTy}
    {dstLoc : Local Γ τ} {B : Place Γ σb} {path : PathTo σb τ}
    {bD : mirlite.Binding}
    (compProg : oseair.Prog)
    (h_chain : PtrChain B)
    (h_off : pathOffset path = 0)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    {stmt0 : Stmt Γ}
    (h_stmt : prog.get? s_mir.pc = some stmt0)
    (h_run0 : ∀ cs, CheckedCompilerM.run (compileStmtChecked stmt0) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.local dstLoc) (.copy (.proj B path)))) cs)
    (h_val0 : ∀ cs so, CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.local dstLoc) (.copy (.proj B path)))) cs
        = Except.ok so →
      ∃ so', CheckedCompilerM.value (compileStmtChecked stmt0) cs
        = Except.ok so')
    (h_envD : mirlite.Env.lookup s_mir.env dstLoc = some bD)
    (h_step : mirlite.stepStmt MSB s_mir
      (.assign (.local dstLoc) (.copy (.proj B path))) = .ok s_mir') :
    ∃ (s_osea' : oseair.State MSB) (n : Nat),
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa ρt s_mir' s_osea' := by
  have h_np := h_chain.not_proj
  obtain ⟨csPrefix, ⟨h_csAt, h_pc⟩, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_tbd,
    h_alloc, h_unmap, h_prb⟩ := h_inv
  obtain ⟨dstReg, baseD, tagD, h_piD, h_entryD, h_raD, h_rtD, h_nwD, h_domD⟩ :=
    h_lbs dstLoc bD h_envD
  have h_baseD : baseD = bD.addr := (h_id_a _ _ h_raD).symm
  subst h_baseD
  -- §1 invert the source step, keeping the CHAIN's resolution opaque
  simp only [mirlite.stepStmt, mirlite.doAssign] at h_step
  cases h_prep : mirlite.preparePlaceAssign MSB s_mir (Place.local dstLoc) with
  | err msg => rw [h_prep] at h_step; simp at h_step
  | ok s1 =>
  rw [h_prep] at h_step
  have h_s1 : s1 = s_mir := by
    simp only [mirlite.preparePlaceAssign, mirlite.resolvePlace?, h_envD] at h_prep
    grind
  rw [h_s1] at h_step
  simp only [mirlite.evalRExpr] at h_step
  cases h_bres : mirlite.resolvePlaceAcc MSB s_mir B with
  | error e =>
      rw [resolvePlaceAcc_proj_base_err h_bres] at h_step
      simp at h_step
  | ok pr =>
  obtain ⟨rb, permsP'⟩ := pr
  rw [resolvePlaceAcc_proj_base_ok h_bres] at h_step
  -- at zero offset the projected resolution IS the chain's
  have h_o' : PathTo.offset path = 0 := h_off
  simp only [h_o', Nat.add_zero] at h_step
  by_cases h_fit : rb.addr + blockSize τ > rb.allocBase + rb.allocSize
  · rw [if_pos h_fit] at h_step
    simp at h_step
  · rw [if_neg h_fit] at h_step
    cases h_read_src : MSB.read permsP' rb.addr (blockSize τ) rb.tag with
    | error e => rw [h_read_src] at h_step; simp at h_step
    | ok perms₂ =>
    rw [h_read_src] at h_step
    simp only [mirlite.resolvePlaceAcc, h_envD] at h_step
    -- §2 compiler scaffolding
    have h_mapped : PlaceInputsMapped csPrefix (Place.proj B path) :=
      placeInputsMapped_of_localBindingSim_resolvePlace h_lbs
        (resolvePlace?_of_resolveAcc
          (resolvePlaceAcc_proj_base_ok (path := path) h_bres))
    have h_mappedB : PlaceInputsMapped csPrefix B := h_mapped
    obtain ⟨bOut0, h_bval0⟩ := placeToRegChecked_ok_of_placeInputsMapped
      (cs := csPrefix) (kind := RefKind.Shared) h_mappedB
    obtain ⟨stmtOutC, h_stmtOutC⟩ :=
      compileStmt_copy_projchain_zero_value h_np h_off h_piD h_bval0
    obtain ⟨stmtOut, h_stmtOut⟩ := h_val0 csPrefix stmtOutC h_stmtOutC
    have h_incrS : StateIncr
        (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix)
        (CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix) := by
      rw [h_run0]
      obtain ⟨h_erun, h_eval⟩ := ensureLocalRegE_existing h_piD
      have h_proj_eq := placeToRegChecked_proj_root_eq (Γ := Γ)
        (kind := RefKind.Shared) (base := B) path h_np
      simp only [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked,
        h_proj_eq,
        CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
        CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
        CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
        h_erun, h_bval0, h_off, dif_pos]
      simp only [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM]
      exact StateIncr.trans (freshReg_state_incr _)
        (StateIncr.trans (emit_state_incr _ _)
          (StateIncr.trans (emit_state_incr _ _) (emit_state_incr _ _)))
    have h_instS : ∀ q' instr,
        q' < (CheckedCompilerM.run
          (placeToRegChecked RefKind.Shared B) csPrefix).nextLabel →
        (CheckedCompilerM.run
          (placeToRegChecked RefKind.Shared B) csPrefix).code q' = some instr →
        compProg q' = some instr := by
      intro q' instr h_lt h_code
      refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
      · exact Nat.lt_of_lt_of_le h_lt h_incrS.nextLabel_le
      · rw [h_incrS.code_eq q' h_lt]
        exact h_code
    -- §3 the mother lemma on the chain BASE
    obtain ⟨sOut, n1, s_mid, tres, h_sval, h_sclean, h_srun, h_spc, h_smem,
      h_spsim, h_snt1, h_snt2, h_slbs, h_sentry, h_srt, h_snw, h_sle, h_srange,
      h_sbelow, h_sprm, h_sregmono, h_slabmono, -, -⟩ :=
      ptrChain_lowering_sim h_id_a h_wf_t h_chain RefKind.Shared csPrefix s_osea
        rb permsP' h_bres h_tbd h_lbs h_prb h_sms h_psim h_pc h_instS
    have h_stmtRun := (h_run0 csPrefix).trans
      (compileStmt_copy_projchain_zero_run h_np h_off h_piD h_sval h_sclean)
    have h_cancel : rb.allocBase + (rb.addr - rb.allocBase) = rb.addr :=
      Nat.add_sub_cancel' h_sle
    -- §4 transports
    obtain ⟨p2w, h_read2_tgt, h_psim2w⟩ :=
      sb_read_respects_PermSim h_spsim h_wf_t h_srt h_snw h_read_src
    have h_w := h_step
    simp only [mirlite.writeResolvedPlace] at h_w
    split at h_w
    · simp at h_w
    · rename_i h_nb
      split at h_w
      · rename_i perms₃ h_useMut_src
        cases h_w
        have h_useMut_src' : MSB.useMut perms₂ bD.addr (blockSize τ) bD.tag
            = .ok perms₃ := by
          grind
        obtain ⟨dstReg2, baseD2, tagD2, h_piD2, h_entryD2, h_raD2, h_rtD2,
          h_nwD2, -⟩ := h_slbs dstLoc bD h_envD
        have h_dr2 : dstReg2 = dstReg := by grind
        have h_baseD2 : baseD2 = bD.addr := (h_id_a _ _ h_raD2).symm
        rw [h_dr2, h_baseD2] at h_entryD2
        obtain ⟨p3w, h_useMut_tgt, h_psim3w⟩ :=
          sb_write_respects_PermSim h_psim2w h_wf_t h_rtD2 h_nwD2 h_useMut_src'
        -- §5 the READ into the temporary, then the write
        have h_ts : obseq.typeSize (obseq.layoutToTyVal τ) = blockSize τ := by
          simp [blockSize]
        have h_code1 : compProg s_mid.pc
            = some (Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg)
                (Rhs.Load (obseq.layoutToTyVal τ) sOut.result.reg)) := by
          rw [h_spc]
          refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
          · rw [h_stmtRun]
            simp only [emit, List.length_cons, List.length_nil]
            omega
          · rw [h_stmtRun]
            rw [emit_code_lt_nextLabel _ _ (by
              simp only [emit, List.length_cons, List.length_nil]; omega)]
            have h := emit_code_at_new
              { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg + 1 }
              [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg)
                (Rhs.Load (obseq.layoutToTyVal τ) sOut.result.reg)]
              (k := 0) (by simp)
            simpa using h
        have h_code2 : compProg (s_mid.pc + 1)
            = some (Instr.RStore (obseq.layoutToTyVal τ)
                (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg) dstReg) := by
          rw [h_spc]
          refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
          · rw [h_stmtRun]
            simp only [emit, List.length_cons, List.length_nil]
            omega
          · rw [h_stmtRun]
            have h := emit_code_at_new
              (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg + 1 }
                [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg)
                  (Rhs.Load (obseq.layoutToTyVal τ) sOut.result.reg)])
              [Instr.RStore (obseq.layoutToTyVal τ)
                (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg) dstReg]
              (k := 0) (by simp)
            simpa [emit] using h
        have h_read2t : MSB.read s_mid.perms
            (rb.allocBase + (rb.addr - rb.allocBase))
            (obseq.typeSize (obseq.layoutToTyVal τ)) tres = .ok p2w := by
          rw [h_ts, h_cancel]
          exact h_read2_tgt
        have h_run1 := runN_Assgn_Load_ptr_step compProg s_mid
          (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg) sOut.result.reg
          (obseq.layoutToTyVal τ) h_code1 h_sentry
          (by rw [h_ts]; grind) h_read2t
        rw [h_ts, h_cancel] at h_run1
        have h_regne : dstReg ≠ Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg := by
          cases dstReg with
          | R n =>
              have h_lt := h_prb _ _ _ h_piD
              have := h_sregmono
              grind [RegisterBelow]
        have h_dentry2 : oseair.RegMap.lookup
            (oseair.RegMap.insert s_mid.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg)
              (obseq.layoutToTyVal τ,
                oseair.readWordSeq s_mid.mem rb.addr (blockSize τ))) dstReg
            = some (obseq.TyVal.PTy, [Val.Ptr bD.addr 0 (blockSize τ) tagD2]) := by
          rw [RegMap.lookup_insert_ne _ h_regne]
          exact h_entryD2
        have h_useMut2t : MSB.useMut p2w (bD.addr + 0)
            (oseair.readWordSeq s_mid.mem rb.addr (blockSize τ)).length tagD2
            = .ok p3w := by
          rw [Nat.add_zero, oseair_readWordSeq_length]
          exact h_useMut_tgt
        have h_wtp : oseair.writeThroughPtr MSB
            { s_mid with
                perms := p2w,
                reg := oseair.RegMap.insert s_mid.reg
                  (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg)
                  (obseq.layoutToTyVal τ,
                    oseair.readWordSeq s_mid.mem rb.addr (blockSize τ)),
                pc := s_mid.pc + 1 }
            dstReg (oseair.readWordSeq s_mid.mem rb.addr (blockSize τ))
            "RStore Invalid Regs"
            = oseair.Result.Ok
              { s_mid with
                  perms := p3w,
                  reg := oseair.RegMap.insert s_mid.reg
                    (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg)
                    (obseq.layoutToTyVal τ,
                      oseair.readWordSeq s_mid.mem rb.addr (blockSize τ)),
                  mem := oseair.writeWordSeq s_mid.mem bD.addr
                    (oseair.readWordSeq s_mid.mem rb.addr (blockSize τ)),
                  pc := s_mid.pc + 1 + 1 } := by
          simp only [oseair.writeThroughPtr, h_dentry2]
          rw [if_neg (by
            rw [oseair_readWordSeq_length, Nat.add_zero]
            exact Nat.not_lt.mpr (Nat.le_refl _))]
          simp only [h_useMut2t]
          rfl
        have h_run2 := runN_RStore_step compProg _ _
          (obseq.layoutToTyVal τ) (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg) dstReg
          _ _ h_code2 (RegMap.lookup_insert_self _ _ _) h_dentry2 h_wtp
        have h_runA := (oseair_runN_add n1 1 s_osea compProg s_mid h_srun).trans h_run1
        have h_run := (oseair_runN_add (n1 + 1) 1 s_osea compProg _ h_runA).trans h_run2
        -- §6 memory
        have h_rel : ListRel (MemValSim ρa ρt)
            (mirlite.readWordSeq s_mir.mem rb.addr (blockSize τ))
            (oseair.readWordSeq s_mid.mem rb.addr (blockSize τ)) := by
          rw [h_smem]
          exact readWordSeq_sim h_id_a h_sms (blockSize τ) rb.addr
        have h_dom : ∀ k,
            k < (mirlite.readWordSeq s_mir.mem rb.addr (blockSize τ)).length →
            ρa (bD.addr + k) = some (bD.addr + k) := by
          intro k hk
          obtain ⟨a', ha'⟩ := h_domD k (by simpa using hk)
          grind [IdentityOnDomain]
        have h_sms' : SourceMemSim ρa ρt
            (mirlite.writeWordSeq s_mir.mem bD.addr
              (mirlite.readWordSeq s_mir.mem rb.addr (blockSize τ)))
            (oseair.writeWordSeq s_mid.mem bD.addr
              (oseair.readWordSeq s_mid.mem rb.addr (blockSize τ))) :=
          SourceMemSim.writeWordSeq_extend h_id_a _ _ _ _ _ h_rel h_dom
            (by rw [h_smem]; exact h_sms)
        -- §7 rebuild the invariant
        refine ⟨_, n1 + 1 + 1, h_run, ?_⟩
        refine ⟨CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix,
          ⟨prefixCompileState_succ h_csAt h_stmt h_stmtOut, ?_⟩, ?_, h_sms',
          h_psim3w, h_id_a, h_wf_t, ?_, ?_, ?_, ?_⟩
        · show s_mid.pc + 1 + 1 = _
          rw [h_spc, h_stmtRun]
          simp [emit]
        · have h_lbsT : LocalBindingSim ρa ρt s_mir.env
              { s_mid with
                  perms := p3w,
                  reg := oseair.RegMap.insert s_mid.reg
                    (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg)
                    (obseq.layoutToTyVal τ,
                      oseair.readWordSeq s_mid.mem rb.addr (blockSize τ)),
                  mem := oseair.writeWordSeq s_mid.mem bD.addr
                    (oseair.readWordSeq s_mid.mem rb.addr (blockSize τ)),
                  pc := s_mid.pc + 1 + 1 } csPrefix :=
            LocalBindingSim.insert_fresh_reg h_slbs h_prb h_sregmono rfl
          intro τ' loc' binding' h_env'
          obtain ⟨reg', base', tag', h_pi', h_entry', h_ra', h_rt', h_nw', h_dom'⟩ :=
            h_lbsT loc' binding' h_env'
          refine ⟨reg', base', tag', ?_, h_entry', h_ra', h_rt', h_nw', h_dom'⟩
          rw [h_stmtRun, getPlaceInfo_emit]
          show (CheckedCompilerM.run
            (placeToRegChecked RefKind.Shared B) csPrefix).placeRegMap.lookup
              loc'.idx.1 = _
          rw [h_sprm]
          exact h_pi'
        · show TagRenameBounded ρt perms₃.NextTag p3w.NextTag
          rw [sb_write_NextTag h_useMut_src', sb_read_NextTag h_read_src, h_snt1,
            sb_write_NextTag h_useMut_tgt, sb_read_NextTag h_read2_tgt]
          exact TagRenameBounded.mono h_tbd (Nat.le_refl _) h_snt2
        · simp only [AllocLockstep, mirlite_writeWordSeq_addrStart,
            oseair_writeWordSeq_addrStart, h_smem]
          exact h_alloc
        · intro τ' loc' h_none
          rw [h_stmtRun, getPlaceInfo_emit]
          show (CheckedCompilerM.run
            (placeToRegChecked RefKind.Shared B) csPrefix).placeRegMap.lookup
              loc'.idx.1 = none
          rw [h_sprm]
          exact h_unmap loc' h_none
        · intro idx reg'' τ'' h_look
          rw [h_stmtRun] at h_look ⊢
          rw [getPlaceInfo_emit] at h_look
          have h_prm2 : (CheckedCompilerM.run
              (placeToRegChecked RefKind.Shared B) csPrefix).placeRegMap
              = csPrefix.placeRegMap := h_sprm
          have h_cs : getPlaceInfo csPrefix idx = some (reg'', τ'') := by
            show csPrefix.placeRegMap.lookup idx = _
            rw [← h_prm2]
            exact h_look
          refine RegisterBelow.mono ?_ (h_prb _ _ _ h_cs)
          simp only [emit]
          exact Nat.le_trans h_sregmono (Nat.le_succ _)
      · simp at h_w

/-- REGIME P→L over CHAIN bases, COLLAPSED 2026-09-03: `dst := copy
    B.f` at NONZERO offset for ANY canonical chain base `B` — a bound
    local (the old P→L) or a deref chain (`y := copy (*p).f`). The
    mother lemma at `Shared` on `B` supplies the base register; the
    statement adds `[Borrow(Shared); Memcpy; Die]`, whose dst `useMut`
    (inside the atomic `Memcpy`) slides between BRIDGE 1S's phases by
    the overlap guard's disjointness. The `Borrow`'s bound is the
    SOURCE's own copy-range check, not typing. -/
theorem copy_projchain_offset_simulation
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {τ σb : LayoutTy}
    {dstLoc : Local Γ τ} {B : Place Γ σb} {path : PathTo σb τ}
    {bD : mirlite.Binding}
    (compProg : oseair.Prog)
    (h_chain : PtrChain B)
    (h_off : pathOffset path ≠ 0)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    {stmt0 : Stmt Γ}
    (h_stmt : prog.get? s_mir.pc = some stmt0)
    (h_run0 : ∀ cs, CheckedCompilerM.run (compileStmtChecked stmt0) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.local dstLoc) (.copy (.proj B path)))) cs)
    (h_val0 : ∀ cs so, CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.local dstLoc) (.copy (.proj B path)))) cs
        = Except.ok so →
      ∃ so', CheckedCompilerM.value (compileStmtChecked stmt0) cs
        = Except.ok so')
    (h_envD : mirlite.Env.lookup s_mir.env dstLoc = some bD)
    (h_step : mirlite.stepStmt MSB s_mir
      (.assign (.local dstLoc) (.copy (.proj B path))) = .ok s_mir') :
    ∃ (s_osea' : oseair.State MSB) (n : Nat),
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa ρt s_mir' s_osea' := by
  have h_np := h_chain.not_proj
  obtain ⟨csPrefix, ⟨h_csAt, h_pc⟩, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_tbd,
    h_alloc, h_unmap, h_prb⟩ := h_inv
  obtain ⟨dstReg, baseD, tagD, h_piD, h_entryD, h_raD, h_rtD, h_nwD, h_domD⟩ :=
    h_lbs dstLoc bD h_envD
  have h_baseD : baseD = bD.addr := (h_id_a _ _ h_raD).symm
  subst h_baseD
  -- §1 invert the source step, chain resolution opaque
  simp only [mirlite.stepStmt, mirlite.doAssign] at h_step
  cases h_prep : mirlite.preparePlaceAssign MSB s_mir (Place.local dstLoc) with
  | err msg => rw [h_prep] at h_step; simp at h_step
  | ok s1 =>
  rw [h_prep] at h_step
  have h_s1 : s1 = s_mir := by
    simp only [mirlite.preparePlaceAssign, mirlite.resolvePlace?, h_envD] at h_prep
    grind
  rw [h_s1] at h_step
  simp only [mirlite.evalRExpr] at h_step
  cases h_bres : mirlite.resolvePlaceAcc MSB s_mir B with
  | error e =>
      rw [resolvePlaceAcc_proj_base_err h_bres] at h_step
      simp at h_step
  | ok pr =>
  obtain ⟨rb, permsP'⟩ := pr
  rw [resolvePlaceAcc_proj_base_ok h_bres] at h_step
  simp only [gt_iff_lt] at h_step
  by_cases h_fit : rb.allocBase + rb.allocSize
      < rb.addr + PathTo.offset path + blockSize τ
  · rw [if_pos h_fit] at h_step
    simp at h_step
  · rw [if_neg h_fit] at h_step
    cases h_read_src : MSB.read permsP' (rb.addr + PathTo.offset path)
        (blockSize τ) rb.tag with
    | error e => rw [h_read_src] at h_step; simp at h_step
    | ok perms₂ =>
    rw [h_read_src] at h_step
    simp only [mirlite.resolvePlaceAcc, h_envD] at h_step
    -- §2 compiler scaffolding
    have h_mapped : PlaceInputsMapped csPrefix (Place.proj B path) :=
      placeInputsMapped_of_localBindingSim_resolvePlace h_lbs
        (resolvePlace?_of_resolveAcc
          (resolvePlaceAcc_proj_base_ok (path := path) h_bres))
    have h_mappedB : PlaceInputsMapped csPrefix B := h_mapped
    obtain ⟨bOut0, h_bval0⟩ := placeToRegChecked_ok_of_placeInputsMapped
      (cs := csPrefix) (kind := RefKind.Shared) h_mappedB
    obtain ⟨stmtOutC, h_stmtOutC⟩ :=
      compileStmt_copy_projchain_offset_value h_np h_off h_piD h_bval0
    obtain ⟨stmtOut, h_stmtOut⟩ := h_val0 csPrefix stmtOutC h_stmtOutC
    have h_incrS : StateIncr
        (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix)
        (CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix) := by
      rw [h_run0]
      obtain ⟨h_erun, h_eval⟩ := ensureLocalRegE_existing h_piD
      have h_proj_eq := placeToRegChecked_proj_root_eq (Γ := Γ)
        (kind := RefKind.Shared) (base := B) path h_np
      simp only [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked,
        h_proj_eq,
        CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
        CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
        CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
        h_erun, h_bval0, dif_neg h_off]
      simp only [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM]
      exact StateIncr.trans (freshReg_state_incr _)
        (StateIncr.trans (emit_state_incr _ _)
          (StateIncr.trans (freshReg_state_incr _)
            (StateIncr.trans (emit_state_incr _ _)
              (StateIncr.trans (emit_state_incr _ _) (emit_state_incr _ _)))))
    have h_instS : ∀ q' instr,
        q' < (CheckedCompilerM.run
          (placeToRegChecked RefKind.Shared B) csPrefix).nextLabel →
        (CheckedCompilerM.run
          (placeToRegChecked RefKind.Shared B) csPrefix).code q' = some instr →
        compProg q' = some instr := by
      intro q' instr h_lt h_code
      refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
      · exact Nat.lt_of_lt_of_le h_lt h_incrS.nextLabel_le
      · rw [h_incrS.code_eq q' h_lt]
        exact h_code
    -- §3 the mother lemma on the chain BASE
    obtain ⟨sOut, n1, s_mid, tres, h_sval, h_sclean, h_srun, h_spc, h_smem,
      h_spsim, h_snt1, h_snt2, h_slbs, h_sentry, h_srt, h_snw, h_sle, h_srange,
      h_sbelow, h_sprm, h_sregmono, h_slabmono, -, -⟩ :=
      ptrChain_lowering_sim h_id_a h_wf_t h_chain RefKind.Shared csPrefix s_osea
        rb permsP' h_bres h_tbd h_lbs h_prb h_sms h_psim h_pc h_instS
    have h_stmtRun := (h_run0 csPrefix).trans
      (compileStmt_copy_projchain_offset_run h_np h_off h_piD h_sval h_sclean)
    have h_cancel : rb.allocBase + (rb.addr - rb.allocBase) = rb.addr :=
      Nat.add_sub_cancel' h_sle
    -- §4 transports: the projected read, the dst write
    obtain ⟨p2, h_read_tgt, h_psim2⟩ :=
      sb_read_respects_PermSim h_spsim h_wf_t h_srt h_snw h_read_src
    have h_w := h_step
    simp only [mirlite.writeResolvedPlace] at h_w
    split at h_w
    · simp at h_w
    · rename_i h_nb
      split at h_w
      · rename_i perms₃ h_useMut_src
        cases h_w
        have h_useMut_src' : MSB.useMut perms₂ bD.addr (blockSize τ) bD.tag
            = .ok perms₃ := by
          grind
        obtain ⟨dstReg2, baseD2, tagD2, h_piD2, h_entryD2, h_raD2, h_rtD2,
          h_nwD2, -⟩ := h_slbs dstLoc bD h_envD
        have h_dr2 : dstReg2 = dstReg := by grind
        have h_baseD2 : baseD2 = bD.addr := (h_id_a _ _ h_raD2).symm
        rw [h_dr2, h_baseD2] at h_entryD2
        obtain ⟨p3, h_useMut_tgt, h_psim3⟩ :=
          sb_write_respects_PermSim h_psim2 h_wf_t h_rtD2 h_nwD2 h_useMut_src'
        -- §5 BRIDGE 1S over the mother's register
        obtain ⟨q1, h_ref_tgt⟩ := sb_ref_Shared_ok_of_sb_read_ok h_read_tgt
        have h_tbd2 : TagRenameBounded ρt permsP'.NextTag s_mid.perms.NextTag := by
          rw [h_snt1]
          exact TagRenameBounded.mono h_tbd (Nat.le_refl _) h_snt2
        have h_unprot := freshTag_not_protected h_spsim h_tbd2
        have h0 : wildcardTag < s_mid.perms.NextTag := (h_tbd2 _ _ h_wf_t.2).2
        have h_ntw : (s_mid.perms.NextTag == wildcardTag) = false := by grind
        obtain ⟨q2, q3, qAcc', h_rd1, h_die1, h_rd2, h_sm, h_exq, h_pfq, h_ntle⟩ :=
          sb_ref_read_die_cancels h_ntw h_unprot h_ref_tgt
        have h_qAcc : qAcc' = p2 := by grind
        subst h_qAcc
        -- §6 BRIDGE 1S: the temporary retires BEFORE the write, so the
        -- keystone's Borrow/read/die is contiguous and the destination
        -- write simply follows the parent read (no commutation needed)
        have h_psim2q : PermSim ρt perms₂ q3 := by
          obtain ⟨hs, hp, he, hn⟩ := h_psim2
          exact ⟨by rw [h_sm]; exact hs, by rw [h_pfq]; exact hp,
                 by rw [h_exq]; exact he, Nat.le_trans hn h_ntle⟩
        obtain ⟨r', h_useMut_tgt', h_psim_final⟩ :=
          sb_write_respects_PermSim h_psim2q h_wf_t h_rtD2 h_nwD2 h_useMut_src'
        -- §7 the four instructions after the base lowering
        have h_ts : obseq.typeSize (obseq.layoutToTyVal τ) = blockSize τ := by
          simp [blockSize]
        have h_code1 : compProg s_mid.pc
            = some (Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg)
                (borrowRhs RefKind.Shared (blockSize τ) sOut.result.reg
                  (pathOffset path))) := by
          rw [h_spc]
          refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
          · rw [h_stmtRun]
            simp only [emit, List.length_cons, List.length_nil]
            omega
          · rw [h_stmtRun]
            rw [emit_code_lt_nextLabel _ _ (by
              simp only [emit, List.length_cons, List.length_nil]; omega)]
            rw [emit_code_lt_nextLabel _ _ (by
              simp only [emit, List.length_cons, List.length_nil]; omega)]
            have h := emit_code_at_new
              { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg + 1 }
              [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg)
                (borrowRhs RefKind.Shared (blockSize τ) sOut.result.reg
                  (pathOffset path))]
              (k := 0) (by simp)
            simpa using h
        have h_code2 : compProg (s_mid.pc + 1)
            = some (Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg + 1))
                (Rhs.Load (obseq.layoutToTyVal τ) (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg))) := by
          rw [h_spc]
          refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
          · rw [h_stmtRun]
            simp only [emit, List.length_cons, List.length_nil]
            omega
          · rw [h_stmtRun]
            rw [emit_code_lt_nextLabel _ _ (by
              simp only [emit, List.length_cons, List.length_nil]; omega)]
            have h := emit_code_at_new
              { (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg + 1 }
                  [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg)
                    (borrowRhs RefKind.Shared (blockSize τ) sOut.result.reg
                      (pathOffset path))]) with
                  nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg + 1 + 1 }
              [Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg + 1)) (Rhs.Load (obseq.layoutToTyVal τ) (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg)),
               Instr.Die (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg) (blockSize τ)]
              (k := 0) (by simp)
            simpa [emit] using h
        have h_code3 : compProg (s_mid.pc + 1 + 1)
            = some (Instr.Die (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg) (blockSize τ)) := by
          rw [h_spc]
          refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
          · rw [h_stmtRun]
            simp only [emit, List.length_cons, List.length_nil]
            omega
          · rw [h_stmtRun]
            rw [emit_code_lt_nextLabel _ _ (by
              simp only [emit, List.length_cons, List.length_nil]; omega)]
            have h := emit_code_at_new
              { (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg + 1 }
                  [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg)
                    (borrowRhs RefKind.Shared (blockSize τ) sOut.result.reg
                      (pathOffset path))]) with
                  nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg + 1 + 1 }
              [Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg + 1)) (Rhs.Load (obseq.layoutToTyVal τ) (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg)),
               Instr.Die (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg) (blockSize τ)]
              (k := 1) (by simp)
            simpa [emit] using h
        have h_code4 : compProg (s_mid.pc + 1 + 1 + 1)
            = some (Instr.RStore (obseq.layoutToTyVal τ) (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg + 1)) dstReg) := by
          rw [h_spc]
          refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
          · rw [h_stmtRun]
            simp only [emit, List.length_cons, List.length_nil]
            omega
          · rw [h_stmtRun]
            have h := emit_code_at_new
              (emit { (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg + 1 }
                  [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg)
                    (borrowRhs RefKind.Shared (blockSize τ) sOut.result.reg
                      (pathOffset path))]) with
                  nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg + 1 + 1 }
                [Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg + 1)) (Rhs.Load (obseq.layoutToTyVal τ) (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg)),
                 Instr.Die (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg) (blockSize τ)])
              [Instr.RStore (obseq.layoutToTyVal τ) (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg + 1)) dstReg]
              (k := 0) (by simp)
            simpa [emit] using h
        -- §8 execute: Borrow, Load, Die, RStore
        have h_le1 : rb.allocBase + (rb.addr - rb.allocBase) + pathOffset path
            + blockSize τ ≤ rb.allocBase + rb.allocSize := by
          rw [h_cancel]
          have := Nat.not_lt.mp h_fit
          grind
        have h_ref_tgt' : MSB.ref s_mid.perms
            (rb.allocBase + (rb.addr - rb.allocBase) + pathOffset path)
            (blockSize τ) tres RefKind.Shared false []
            = .ok (q1, s_mid.perms.NextTag) := by
          rw [h_cancel]
          exact h_ref_tgt
        have h_run1 := runN_Assgn_Borrow_step compProg s_mid
          (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg) sOut.result.reg RefKind.Shared false []
          (blockSize τ) (pathOffset path)
          h_code1 h_sentry h_le1 h_ref_tgt'
        have h_bentry : PtrRegisterEntry
            (oseair.RegMap.insert s_mid.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg) (obseq.TyVal.PTy, [Val.Ptr rb.allocBase
                (rb.addr - rb.allocBase + pathOffset path)
                rb.allocSize s_mid.perms.NextTag]))
            (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg) rb.allocBase (rb.addr - rb.allocBase + pathOffset path)
            rb.allocSize s_mid.perms.NextTag :=
          RegMap.lookup_insert_self _ _ _
        have h_read2 : MSB.read q1
            (rb.allocBase + (rb.addr - rb.allocBase + pathOffset path))
            (obseq.typeSize (obseq.layoutToTyVal τ)) s_mid.perms.NextTag
            = .ok q2 := by
          rw [h_ts, ← Nat.add_assoc, h_cancel]
          exact h_rd1
        have h_run2 := runN_Assgn_Load_ptr_step compProg
          { s_mid with
              perms := q1,
              reg := oseair.RegMap.insert s_mid.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg) (obseq.TyVal.PTy, [Val.Ptr rb.allocBase
                (rb.addr - rb.allocBase + pathOffset path)
                rb.allocSize s_mid.perms.NextTag]),
              pc := s_mid.pc + 1 }
          (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg + 1)) (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg) (obseq.layoutToTyVal τ) h_code2 h_bentry
          (by rw [h_ts]; grind) h_read2
        rw [h_ts, ← Nat.add_assoc, h_cancel] at h_run2
        -- the borrow register survives the value register's insert
        have h_regbv : (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg) ≠ (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg + 1)) := by
          intro h_eq
          injection h_eq with h_eq'
          omega
        have h_bentry2 : oseair.RegMap.lookup
            (oseair.RegMap.insert
              (oseair.RegMap.insert s_mid.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg) (obseq.TyVal.PTy, [Val.Ptr rb.allocBase
                (rb.addr - rb.allocBase + pathOffset path)
                rb.allocSize s_mid.perms.NextTag])) (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg + 1))
              (obseq.layoutToTyVal τ, (oseair.readWordSeq s_mid.mem (rb.addr + pathOffset path) (blockSize τ)))) (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg)
            = some (obseq.TyVal.PTy, [Val.Ptr rb.allocBase
                (rb.addr - rb.allocBase + pathOffset path)
                rb.allocSize s_mid.perms.NextTag]) := by
          rw [RegMap.lookup_insert_ne _ h_regbv]
          exact h_bentry
        have h_die1' : MSB.die q2
            (rb.allocBase + (rb.addr - rb.allocBase + pathOffset path))
            (blockSize τ) s_mid.perms.NextTag = .ok q3 := by
          rw [← Nat.add_assoc, h_cancel]
          exact h_die1
        have h_run3 := runN_Die_step compProg
          { s_mid with
              perms := q2,
              reg := oseair.RegMap.insert
                (oseair.RegMap.insert s_mid.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg) (obseq.TyVal.PTy, [Val.Ptr rb.allocBase
                (rb.addr - rb.allocBase + pathOffset path)
                rb.allocSize s_mid.perms.NextTag])) (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg + 1))
                (obseq.layoutToTyVal τ, (oseair.readWordSeq s_mid.mem (rb.addr + pathOffset path) (blockSize τ))),
              pc := s_mid.pc + 1 + 1 }
          (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg) (blockSize τ) h_code3 h_bentry2 h_die1'
        -- the destination register survives both inserts
        have h_regne : dstReg ≠ (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg + 1)) := by
          cases dstReg with
          | R n =>
              have h_lt := h_prb _ _ _ h_piD
              have := h_sregmono
              grind [RegisterBelow]
        have h_regne2 : dstReg ≠ (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg) := by
          cases dstReg with
          | R n =>
              have h_lt := h_prb _ _ _ h_piD
              have := h_sregmono
              grind [RegisterBelow]
        have h_dentry3 : oseair.RegMap.lookup
            (oseair.RegMap.insert
              (oseair.RegMap.insert s_mid.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg) (obseq.TyVal.PTy, [Val.Ptr rb.allocBase
                (rb.addr - rb.allocBase + pathOffset path)
                rb.allocSize s_mid.perms.NextTag])) (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg + 1))
              (obseq.layoutToTyVal τ, (oseair.readWordSeq s_mid.mem (rb.addr + pathOffset path) (blockSize τ)))) dstReg
            = some (obseq.TyVal.PTy, [Val.Ptr bD.addr 0 (blockSize τ) tagD2]) := by
          rw [RegMap.lookup_insert_ne _ h_regne, RegMap.lookup_insert_ne _ h_regne2]
          exact h_entryD2
        have h_useMut3 : MSB.useMut q3 (bD.addr + 0) (oseair.readWordSeq s_mid.mem (rb.addr + pathOffset path) (blockSize τ)).length tagD2
            = .ok r' := by
          rw [Nat.add_zero, oseair_readWordSeq_length]
          exact h_useMut_tgt'
        have h_wtp : oseair.writeThroughPtr MSB
            { s_mid with
                perms := q3,
                reg := oseair.RegMap.insert
                  (oseair.RegMap.insert s_mid.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg) (obseq.TyVal.PTy, [Val.Ptr rb.allocBase
                (rb.addr - rb.allocBase + pathOffset path)
                rb.allocSize s_mid.perms.NextTag])) (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg + 1))
                  (obseq.layoutToTyVal τ, (oseair.readWordSeq s_mid.mem (rb.addr + pathOffset path) (blockSize τ))),
                pc := s_mid.pc + 1 + 1 + 1 }
            dstReg (oseair.readWordSeq s_mid.mem (rb.addr + pathOffset path) (blockSize τ)) "RStore Invalid Regs"
            = oseair.Result.Ok
              { s_mid with
                  perms := r',
                  reg := oseair.RegMap.insert
                    (oseair.RegMap.insert s_mid.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg) (obseq.TyVal.PTy, [Val.Ptr rb.allocBase
                (rb.addr - rb.allocBase + pathOffset path)
                rb.allocSize s_mid.perms.NextTag])) (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg + 1))
                    (obseq.layoutToTyVal τ, (oseair.readWordSeq s_mid.mem (rb.addr + pathOffset path) (blockSize τ))),
                  mem := oseair.writeWordSeq s_mid.mem bD.addr (oseair.readWordSeq s_mid.mem (rb.addr + pathOffset path) (blockSize τ)),
                  pc := s_mid.pc + 1 + 1 + 1 + 1 } := by
          simp only [oseair.writeThroughPtr, h_dentry3]
          rw [if_neg (by
            rw [oseair_readWordSeq_length, Nat.add_zero]
            exact Nat.not_lt.mpr (Nat.le_refl _))]
          simp only [h_useMut3]
          rfl
        have h_run4 := runN_RStore_step compProg _ _
          (obseq.layoutToTyVal τ) (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg + 1)) dstReg _ _ h_code4
          (RegMap.lookup_insert_self _ _ _) h_dentry3 h_wtp
        have h_runA := (oseair_runN_add n1 1 s_osea compProg s_mid h_srun).trans h_run1
        have h_runB := (oseair_runN_add (n1 + 1) 1 s_osea compProg _ h_runA).trans h_run2
        have h_runC := (oseair_runN_add (n1 + 1 + 1) 1 s_osea compProg _ h_runB).trans h_run3
        have h_run := (oseair_runN_add (n1 + 1 + 1 + 1) 1 s_osea compProg _ h_runC).trans h_run4
        -- §9 memory
        have h_rel : ListRel (MemValSim ρa ρt)
            (mirlite.readWordSeq s_mir.mem (rb.addr + pathOffset path) (blockSize τ))
            (oseair.readWordSeq s_mid.mem (rb.addr + pathOffset path) (blockSize τ)) := by
          rw [h_smem]
          exact readWordSeq_sim h_id_a h_sms (blockSize τ) (rb.addr + pathOffset path)
        have h_dom : ∀ k,
            k < (mirlite.readWordSeq s_mir.mem (rb.addr + pathOffset path)
              (blockSize τ)).length →
            ρa (bD.addr + k) = some (bD.addr + k) := by
          intro k hk
          obtain ⟨a', ha'⟩ := h_domD k (by simpa using hk)
          grind [IdentityOnDomain]
        have h_sms' : SourceMemSim ρa ρt
            (mirlite.writeWordSeq s_mir.mem bD.addr
              (mirlite.readWordSeq s_mir.mem (rb.addr + pathOffset path) (blockSize τ)))
            (oseair.writeWordSeq s_mid.mem bD.addr (oseair.readWordSeq s_mid.mem (rb.addr + pathOffset path) (blockSize τ))) :=
          SourceMemSim.writeWordSeq_extend h_id_a _ _ _ _ _ h_rel h_dom
            (by rw [h_smem]; exact h_sms)
        -- §10 rebuild the invariant
        refine ⟨_, n1 + 1 + 1 + 1 + 1, h_run, ?_⟩
        refine ⟨CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix,
          ⟨prefixCompileState_succ h_csAt h_stmt h_stmtOut, ?_⟩, ?_, h_sms',
          h_psim_final, h_id_a, h_wf_t, ?_, ?_, ?_, ?_⟩
        · show s_mid.pc + 1 + 1 + 1 + 1 = _
          rw [h_spc, h_stmtRun]
          simp [emit]
        · have h_lbs1 : LocalBindingSim ρa ρt s_mir.env
              { s_mid with
                  perms := q1,
                  reg := oseair.RegMap.insert s_mid.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg) (obseq.TyVal.PTy, [Val.Ptr rb.allocBase
                (rb.addr - rb.allocBase + pathOffset path)
                rb.allocSize s_mid.perms.NextTag]),
                  pc := s_mid.pc + 1 } csPrefix :=
            LocalBindingSim.insert_fresh_reg h_slbs h_prb h_sregmono rfl
          have h_lbs2 : LocalBindingSim ρa ρt s_mir.env
              { s_mid with
                  perms := r',
                  reg := oseair.RegMap.insert
                    (oseair.RegMap.insert s_mid.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg) (obseq.TyVal.PTy, [Val.Ptr rb.allocBase
                (rb.addr - rb.allocBase + pathOffset path)
                rb.allocSize s_mid.perms.NextTag])) (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg + 1))
                    (obseq.layoutToTyVal τ, (oseair.readWordSeq s_mid.mem (rb.addr + pathOffset path) (blockSize τ))),
                  mem := oseair.writeWordSeq s_mid.mem bD.addr (oseair.readWordSeq s_mid.mem (rb.addr + pathOffset path) (blockSize τ)),
                  pc := s_mid.pc + 1 + 1 + 1 + 1 } csPrefix :=
            LocalBindingSim.insert_fresh_reg h_lbs1 h_prb
              (Nat.le_trans h_sregmono (Nat.le_succ _)) rfl
          intro τ' loc' binding' h_env'
          obtain ⟨reg', base', tag', h_pi', h_entry', h_ra', h_rt', h_nw', h_dom'⟩ :=
            h_lbs2 loc' binding' h_env'
          refine ⟨reg', base', tag', ?_, h_entry', h_ra', h_rt', h_nw', h_dom'⟩
          rw [h_stmtRun, getPlaceInfo_emit, getPlaceInfo_emit, getPlaceInfo_setNextReg,
            getPlaceInfo_emit, getPlaceInfo_setNextReg]
          show (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).placeRegMap.lookup loc'.idx.1 = _
          rw [h_sprm]
          exact h_pi'
        · show TagRenameBounded ρt perms₃.NextTag r'.NextTag
          rw [sb_write_NextTag h_useMut_src', sb_read_NextTag h_read_src, h_snt1,
            sb_write_NextTag h_useMut_tgt']
          refine TagRenameBounded.mono h_tbd (Nat.le_refl _) ?_
          refine Nat.le_trans h_snt2 ?_
          rw [← sb_read_NextTag h_read_tgt]
          exact h_ntle
        · simp only [AllocLockstep, mirlite_writeWordSeq_addrStart,
            oseair_writeWordSeq_addrStart, h_smem]
          exact h_alloc
        · intro τ' loc' h_none
          rw [h_stmtRun, getPlaceInfo_emit, getPlaceInfo_emit, getPlaceInfo_setNextReg,
            getPlaceInfo_emit, getPlaceInfo_setNextReg]
          show (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).placeRegMap.lookup loc'.idx.1 = none
          rw [h_sprm]
          exact h_unmap loc' h_none
        · intro idx reg'' τ'' h_look
          rw [h_stmtRun] at h_look ⊢
          rw [getPlaceInfo_emit, getPlaceInfo_emit, getPlaceInfo_setNextReg,
            getPlaceInfo_emit, getPlaceInfo_setNextReg] at h_look
          have h_cs : getPlaceInfo csPrefix idx = some (reg'', τ'') := by
            show csPrefix.placeRegMap.lookup idx = _
            rw [← h_sprm]
            exact h_look
          refine RegisterBelow.mono ?_ (h_prb _ _ _ h_cs)
          simp only [emit]
          exact Nat.le_trans h_sregmono (Nat.le_trans (Nat.le_succ _) (Nat.le_succ _))
      · simp at h_w

/-! ## Flatten transfer for a copy source of ANY shape -/

theorem compileRExprToChecked_copysrc_anyflatten_run
    {Γ : Ctx} {τ : LayoutTy} (src : Place Γ τ)
    (r : Register) (cs : CompilerState) :
    CheckedCompilerM.run (compileRExprToChecked r (RExpr.copy src)) cs
      = CheckedCompilerM.run
          (compileRExprToChecked r (RExpr.copy (flattenPlace src))) cs := by
  obtain ⟨h_agr, h_agv⟩ := placeToRegChecked_flatten_agree src RefKind.Shared cs
  simp only [compileRExprToChecked, compileRExprPreChecked,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure]
  cases hF : CheckedCompilerM.value
      (placeToRegChecked RefKind.Shared (flattenPlace src)) cs with
  | error eF =>
      cases hO : CheckedCompilerM.value (placeToRegChecked RefKind.Shared src) cs with
      | error eO =>
          simp only [hF, hO]
          exact h_agr.symm
      | ok oO =>
          exfalso
          rw [hF, hO] at h_agv
          simp [Except.map] at h_agv
  | ok oF =>
      cases hO : CheckedCompilerM.value (placeToRegChecked RefKind.Shared src) cs with
      | error eO =>
          exfalso
          rw [hF, hO] at h_agv
          simp [Except.map] at h_agv
      | ok oO =>
          have h_res : oF.result = oO.result := by
            rw [hF, hO] at h_agv
            simpa [Except.map] using h_agv
          simp only [hF, hO, h_res]
          rw [h_agr]

theorem compileRExprToChecked_copysrc_anyflatten_valunit
    {Γ : Ctx} {τ : LayoutTy} (src : Place Γ τ)
    (r : Register) (cs : CompilerState) :
    (CheckedCompilerM.value (compileRExprToChecked r (RExpr.copy src)) cs).map
      (fun _ => ())
      = (CheckedCompilerM.value
          (compileRExprToChecked r (RExpr.copy (flattenPlace src))) cs).map
        (fun _ => ()) := by
  obtain ⟨h_agr, h_agv⟩ := placeToRegChecked_flatten_agree src RefKind.Shared cs
  simp only [compileRExprToChecked, compileRExprPreChecked,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure]
  cases hF : CheckedCompilerM.value
      (placeToRegChecked RefKind.Shared (flattenPlace src)) cs with
  | error eF =>
      cases hO : CheckedCompilerM.value (placeToRegChecked RefKind.Shared src) cs with
      | error eO =>
          have h_e : eF = eO := by
            rw [hF, hO] at h_agv
            simpa [Except.map] using h_agv
          subst h_e
          simp [hF, hO, Except.map]
      | ok oO =>
          exfalso
          rw [hF, hO] at h_agv
          simp [Except.map] at h_agv
  | ok oF =>
      cases hO : CheckedCompilerM.value (placeToRegChecked RefKind.Shared src) cs with
      | error eO =>
          exfalso
          rw [hF, hO] at h_agv
          simp [Except.map] at h_agv
      | ok oO =>
          simp [hF, hO, Except.map]

theorem compileStmt_copy_srcflatten_run
    {Γ : Ctx} {τ : LayoutTy} {dstLoc : Local Γ τ} (src : Place Γ τ)
    (cs : CompilerState) :
    CheckedCompilerM.run
        (compileStmtChecked (Stmt.assign (.local dstLoc) (.copy src))) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.local dstLoc) (.copy (flattenPlace src)))) cs := by
  simp only [compileStmtChecked,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure]
  have h_run := compileRExprToChecked_copysrc_anyflatten_run src
    ((ensureLocalRegE dstLoc).value cs).result.reg
    (CompilerM.run (ensureLocalRegE dstLoc) cs)
  have h_val := compileRExprToChecked_copysrc_anyflatten_valunit src
    ((ensureLocalRegE dstLoc).value cs).result.reg
    (CompilerM.run (ensureLocalRegE dstLoc) cs)
  cases hO : CheckedCompilerM.value
      (compileRExprToChecked ((ensureLocalRegE dstLoc).value cs).result.reg
        (RExpr.copy src))
      (CompilerM.run (ensureLocalRegE dstLoc) cs) with
  | error eO =>
      cases hF : CheckedCompilerM.value
          (compileRExprToChecked ((ensureLocalRegE dstLoc).value cs).result.reg
            (RExpr.copy (flattenPlace src)))
          (CompilerM.run (ensureLocalRegE dstLoc) cs) with
      | error eF =>
          simp only [hO, hF]
          exact h_run
      | ok oF =>
          exfalso
          rw [hO, hF] at h_val
          simp [Except.map] at h_val
  | ok oO =>
      cases hF : CheckedCompilerM.value
          (compileRExprToChecked ((ensureLocalRegE dstLoc).value cs).result.reg
            (RExpr.copy (flattenPlace src)))
          (CompilerM.run (ensureLocalRegE dstLoc) cs) with
      | error eF =>
          exfalso
          rw [hO, hF] at h_val
          simp [Except.map] at h_val
      | ok oF =>
          simp only [hO, hF]
          exact h_run

/-- Existential form: the dependent evidence type of the flattened
    statement's value is not transportable along the flattening
    equation, but its EXISTENTIAL is (the motive hides the type). -/
theorem compileStmt_copy_srcflatten_value
    {Γ : Ctx} {τ : LayoutTy} {dstLoc : Local Γ τ} (src : Place Γ τ)
    (cs : CompilerState)
    (h_ex : ∃ so, CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.local dstLoc) (.copy (flattenPlace src)))) cs
      = Except.ok so) :
    ∃ so', CheckedCompilerM.value
        (compileStmtChecked (Stmt.assign (.local dstLoc) (.copy src))) cs
      = Except.ok so' := by
  obtain ⟨so, h_so⟩ := h_ex
  have h_val := compileRExprToChecked_copysrc_anyflatten_valunit src
    ((ensureLocalRegE dstLoc).value cs).result.reg
    (CompilerM.run (ensureLocalRegE dstLoc) cs)
  simp only [compileStmtChecked,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure] at h_so ⊢
  cases hO : CheckedCompilerM.value
      (compileRExprToChecked ((ensureLocalRegE dstLoc).value cs).result.reg
        (RExpr.copy src))
      (CompilerM.run (ensureLocalRegE dstLoc) cs) with
  | error eO =>
      exfalso
      cases hF : CheckedCompilerM.value
          (compileRExprToChecked ((ensureLocalRegE dstLoc).value cs).result.reg
            (RExpr.copy (flattenPlace src)))
          (CompilerM.run (ensureLocalRegE dstLoc) cs) with
      | error eF =>
          rw [hF] at h_so
          simp at h_so
      | ok oF =>
          rw [hO, hF] at h_val
          simp [Except.map] at h_val
  | ok oO =>
      simp only [hO]
      exact ⟨_, rfl⟩

/-! ## FRESH destination (regime B for copy): `ensurePlaceRoot`'s root
    `Alloc` runs first, then the source lowering, then the `Memcpy`. -/

theorem compileStmt_copy_fresh_chainsrc_run
    {Γ : Ctx} {τ : LayoutTy}
    {dstLoc : Local Γ τ} {src : Place Γ τ}
    {cs : CompilerState}
    {sOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared src)}
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = none)
    (h_sval : CheckedCompilerM.value (placeToRegChecked RefKind.Shared src)
      (setPlaceInfo
        (emit { cs with nextReg := cs.nextReg + 1 }
          [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal τ))])
        dstLoc.idx.1 (Register.R cs.nextReg, τ))
      = Except.ok sOut)
    (h_sclean : sOut.result.cleanup = []) :
    CheckedCompilerM.run
        (compileStmtChecked (Stmt.assign (.local dstLoc) (.copy src))) cs
      = emit (emit
          { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src)
          (setPlaceInfo
            (emit { cs with nextReg := cs.nextReg + 1 }
              [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal τ))])
            dstLoc.idx.1 (Register.R cs.nextReg, τ))) with
              nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src)
          (setPlaceInfo
            (emit { cs with nextReg := cs.nextReg + 1 }
              [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal τ))])
            dstLoc.idx.1 (Register.R cs.nextReg, τ))).nextReg + 1 }
          [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src)
          (setPlaceInfo
            (emit { cs with nextReg := cs.nextReg + 1 }
              [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal τ))])
            dstLoc.idx.1 (Register.R cs.nextReg, τ))).nextReg)
            (Rhs.Load (obseq.layoutToTyVal τ) sOut.result.reg)])
          [Instr.RStore (obseq.layoutToTyVal τ)
            (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src)
          (setPlaceInfo
            (emit { cs with nextReg := cs.nextReg + 1 }
              [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal τ))])
            dstLoc.idx.1 (Register.R cs.nextReg, τ))).nextReg) (Register.R cs.nextReg)] := by
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_fresh (loc := dstLoc) h_dst
  simp only [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
    h_run, h_val, h_sval]
  simp [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM, cleanupInstrs, h_sclean, emit_nil]

theorem compileStmt_copy_fresh_chainsrc_value
    {Γ : Ctx} {τ : LayoutTy}
    {dstLoc : Local Γ τ} {src : Place Γ τ}
    {cs : CompilerState}
    {sOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared src)}
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = none)
    (h_sval : CheckedCompilerM.value (placeToRegChecked RefKind.Shared src)
      (setPlaceInfo
        (emit { cs with nextReg := cs.nextReg + 1 }
          [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal τ))])
        dstLoc.idx.1 (Register.R cs.nextReg, τ))
      = Except.ok sOut) :
    ∃ so, CheckedCompilerM.value
      (compileStmtChecked (Stmt.assign (.local dstLoc) (.copy src))) cs
      = Except.ok so := by
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_fresh (loc := dstLoc) h_dst
  simp only [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
    h_run, h_sval]
  exact ⟨_, rfl⟩

/-- REGIME B for copy, CLOSED 2026-09-03: `dst := copy src` where the
    DESTINATION LOCAL IS UNBOUND — the statement's own execution
    allocates it. mirlite's `preparePlaceAssign` allocates the τ-sized
    root and binds it BEFORE the source is read, and `ensurePlaceRoot`
    emits the matching root `Alloc`; the source lowering then runs in
    the post-allocation states on both machines (the mother lemma is
    called at the extended renames), and one `Memcpy` finishes. Any
    aliasing (`y := copy y`) is rejected source-side by the overlap
    guard, since the destination resolves after the allocation. -/
theorem copy_fresh_chainsrc_simulation
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {τ : LayoutTy}
    {dstLoc : Local Γ τ} {src : Place Γ τ}
    (compProg : oseair.Prog)
    (h_chain : PtrChain src)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    {stmt0 : Stmt Γ}
    (h_stmt : prog.get? s_mir.pc = some stmt0)
    (h_run0 : ∀ cs, CheckedCompilerM.run (compileStmtChecked stmt0) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.local dstLoc) (.copy src))) cs)
    (h_val0 : ∀ cs so, CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.local dstLoc) (.copy src))) cs
        = Except.ok so →
      ∃ so', CheckedCompilerM.value (compileStmtChecked stmt0) cs
        = Except.ok so')
    (h_envD : mirlite.Env.lookup s_mir.env dstLoc = none)
    (h_step : mirlite.stepStmt MSB s_mir
      (.assign (.local dstLoc) (.copy src)) = .ok s_mir') :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' := by
  obtain ⟨csPrefix, ⟨h_csAt, h_pc⟩, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_tbd,
    h_alloc, h_unmap, h_prb⟩ := h_inv
  have h_pi_none : getPlaceInfo csPrefix dstLoc.idx.1 = none := h_unmap dstLoc h_envD
  -- §1 the source allocates the destination root before reading
  simp only [mirlite.stepStmt, mirlite.doAssign] at h_step
  cases h_prep : mirlite.preparePlaceAssign MSB s_mir (Place.local dstLoc) with
  | err msg => rw [h_prep] at h_step; simp at h_step
  | ok s1 =>
  rw [h_prep] at h_step
  simp only [mirlite.preparePlaceAssign, mirlite.resolvePlace?, h_envD,
    mirlite.allocateRoot, mirlite.allocateBase, mirlite.allocate] at h_prep
  cases h_own_src : MSB.own s_mir.perms s_mir.mem.addrStart (blockSize τ) with
  | error e => rw [h_own_src] at h_prep; simp at h_prep
  | ok pr =>
  obtain ⟨permsOwned, tagS⟩ := pr
  rw [h_own_src] at h_prep
  injection h_prep with h_s1
  -- §2 the two ρ extensions and the post-allocation source state
  obtain ⟨tgtPerms, h_own_tgt, h_tagS_eq, h_incr_t, h_wf_t', h_tbd', h_psim'⟩ :=
    sb_own_respects_PermSim h_psim h_wf_t h_tbd h_own_src
  subst h_tagS_eq
  have h_addr_eq : s_osea.mem.addrStart = s_mir.mem.addrStart := h_alloc
  have h_incr_a :=
    AddrRenameIncr.extendBlock h_id_a s_mir.mem.addrStart (blockSize τ)
  have h_id_a' :=
    IdentityOnDomain.extendBlock h_id_a s_mir.mem.addrStart (blockSize τ)
  have h_ra_dom : ∀ k, k < blockSize τ →
      (ρa.extendBlock s_mir.mem.addrStart (blockSize τ))
        (s_mir.mem.addrStart + k) = some (s_mir.mem.addrStart + k) :=
    fun _ hk => AddrRenameMap.extendBlock_mem hk
  have h_ra_base : (ρa.extendBlock s_mir.mem.addrStart (blockSize τ))
      s_mir.mem.addrStart = some s_mir.mem.addrStart :=
    AddrRenameMap.extendBlock_base _ _ _
  have h_rt_new : (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag)
      s_mir.perms.NextTag = some s_osea.perms.NextTag :=
    TagRenameMap.extend_self _ _ _
  have h0 : wildcardTag < s_mir.perms.NextTag := (h_tbd _ _ h_wf_t.2).1
  have h_nw : (s_mir.perms.NextTag == wildcardTag) = false := by grind
  -- the post-allocation source state stays ABSTRACT (`s1`); everything
  -- needed about it comes from the allocation equation
  have h_lookup_set : mirlite.Env.lookup s1.env dstLoc
      = some { addr := s_mir.mem.addrStart, tag := s_mir.perms.NextTag } := by
    rw [← h_s1]
    simp [mirlite.Env.lookup, mirlite.Env.set]
  have h_perms1 : s1.perms = permsOwned := by rw [← h_s1]
  have h_pc1 : s1.pc = s_mir.pc := by rw [← h_s1]
  have h_memstart1 : s1.mem.addrStart = s_mir.mem.addrStart + blockSize τ := by
    rw [← h_s1]
  have h_find1 : ∀ a, mirlite.Mem.find? s1.mem a = mirlite.Mem.find? s_mir.mem a := by
    intro a
    rw [← h_s1]
    rfl
  -- §3 the source read, kept OPAQUE at the chain
  simp only [mirlite.evalRExpr] at h_step
  cases h_sres : mirlite.resolvePlaceAcc MSB s1 src with
  | error e => rw [h_sres] at h_step; simp at h_step
  | ok pr2 =>
  obtain ⟨rs, permsP'⟩ := pr2
  rw [h_sres] at h_step
  simp only at h_step
  by_cases h_fitS : rs.addr + blockSize τ > rs.allocBase + rs.allocSize
  · rw [if_pos h_fitS] at h_step
    simp at h_step
  · rw [if_neg h_fitS] at h_step
    cases h_read_src : MSB.read permsP' rs.addr (blockSize τ) rs.tag with
    | error e => rw [h_read_src] at h_step; simp at h_step
    | ok perms₂ =>
    rw [h_read_src] at h_step
    simp only [mirlite.resolvePlaceAcc, h_lookup_set] at h_step
    -- §4 the compiled prefix: the root `Alloc` and the post-alloc state
    have h_erun : CompilerM.run (ensureLocalRegE dstLoc) csPrefix
        = setPlaceInfo
            (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
              [Instr.Assgn (Register.R csPrefix.nextReg)
                (Rhs.Alloc (layoutToTyVal τ))])
            dstLoc.idx.1 (Register.R csPrefix.nextReg, τ) :=
      (ensureLocalRegE_fresh (loc := dstLoc) h_pi_none).1
    have h_pi_new : getPlaceInfo
        (setPlaceInfo
          (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
            [Instr.Assgn (Register.R csPrefix.nextReg)
              (Rhs.Alloc (layoutToTyVal τ))])
          dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))
        dstLoc.idx.1 = some (Register.R csPrefix.nextReg, τ) :=
      getPlaceInfo_setPlaceInfo_self _ _ _
    have h_sz : obseq.typeSize (layoutToTyVal τ) = blockSize τ :=
      obseq.typeSize_layoutToTyVal _
    have h_own_tgt' : MSB.own s_osea.perms s_osea.mem.addrStart
        (obseq.typeSize (layoutToTyVal τ))
        = .ok (tgtPerms, s_osea.perms.NextTag) := by
      rw [h_sz, h_addr_eq]
      exact h_own_tgt
    -- the post-Alloc target state
    have h_prb1 : PlaceRegMapBound
        (setPlaceInfo
          (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
            [Instr.Assgn (Register.R csPrefix.nextReg)
              (Rhs.Alloc (layoutToTyVal τ))])
          dstLoc.idx.1 (Register.R csPrefix.nextReg, τ)) := by
      intro idx reg τ'' h_look
      by_cases h_i : idx = dstLoc.idx.1
      · subst h_i
        rw [getPlaceInfo_setPlaceInfo_self] at h_look
        injection h_look with h_look'
        have : reg = Register.R csPrefix.nextReg := (congrArg Prod.fst h_look').symm
        subst this
        show csPrefix.nextReg < _
        simp only [emit, setPlaceInfo]
        grind
      · rw [getPlaceInfo_setPlaceInfo_ne _ h_i] at h_look
        refine RegisterBelow.mono ?_ (h_prb _ _ _ h_look)
        simp only [emit, setPlaceInfo]
        grind
    have h_lbs1 : LocalBindingSim
        (ρa.extendBlock s_mir.mem.addrStart (blockSize τ))
        (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag)
        s1.env
        { s_osea with
            mem := (oseair.allocate s_osea.mem
              (obseq.typeSize (layoutToTyVal τ))).2,
            perms := tgtPerms,
            reg := oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
              (obseq.TyVal.PTy, [Val.Ptr s_osea.mem.addrStart 0
                (obseq.typeSize (layoutToTyVal τ)) s_osea.perms.NextTag]),
            pc := s_osea.pc + 1 }
        (setPlaceInfo
          (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
            [Instr.Assgn (Register.R csPrefix.nextReg)
              (Rhs.Alloc (layoutToTyVal τ))])
          dstLoc.idx.1 (Register.R csPrefix.nextReg, τ)) := by
      rw [← h_s1]
      intro τ' loc' binding' h_env'
      by_cases h_idx : loc'.idx = dstLoc.idx
      · have h_ty : τ' = τ := by
          rw [← loc'.hTy, h_idx, dstLoc.hTy]
        subst h_ty
        have h_b : binding' = { addr := s_mir.mem.addrStart,
                                tag := s_mir.perms.NextTag } := by
          grind [mirlite.Env.lookup, mirlite.Env.set]
        subst h_b
        refine ⟨Register.R csPrefix.nextReg, s_mir.mem.addrStart,
          s_osea.perms.NextTag, ?_, ?_, ?_, h_rt_new, h_nw, ?_⟩
        · rw [show loc'.idx.1 = dstLoc.idx.1 from congrArg Fin.val h_idx]
          exact h_pi_new
        · show oseair.RegMap.lookup _ _ = _
          rw [← h_addr_eq, ← h_sz]
          exact RegMap.lookup_insert_self _ _ _
        · exact h_ra_base
        · intro k hk
          exact ⟨s_mir.mem.addrStart + k, h_ra_dom k hk⟩
      · have h_env'' : mirlite.Env.lookup s_mir.env loc' = some binding' := by
          simpa only [mirlite.Env.lookup, mirlite.Env.set, if_neg h_idx]
            using h_env'
        obtain ⟨reg', base', tag', h_pi', h_entry', h_ra', h_rt', h_nw', h_dom'⟩ :=
          h_lbs loc' binding' h_env''
        have h_idxv : loc'.idx.1 ≠ dstLoc.idx.1 := by grind [Fin.ext]
        have h_regne : reg' ≠ Register.R csPrefix.nextReg := by
          cases reg' with
          | R n =>
              have h_lt := h_prb _ _ _ h_pi'
              grind [RegisterBelow]
        refine ⟨reg', base', tag', ?_, ?_, h_incr_a _ _ h_ra',
          h_incr_t _ _ h_rt', h_nw',
          fun k hk => ⟨(h_dom' k hk).choose,
            h_incr_a _ _ (h_dom' k hk).choose_spec⟩⟩
        · rw [getPlaceInfo_setPlaceInfo_ne _ h_idxv]
          exact h_pi'
        · show oseair.RegMap.lookup _ _ = _
          rw [RegMap.lookup_insert_ne _ h_regne]
          exact h_entry'
    -- §5 the statement value and code inclusion for the source lowering
    obtain ⟨sOut0, h_sval0⟩ := placeToRegChecked_ok_of_placeInputsMapped
      (cs := setPlaceInfo
          (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
            [Instr.Assgn (Register.R csPrefix.nextReg)
              (Rhs.Alloc (layoutToTyVal τ))])
          dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))
      (kind := RefKind.Shared)
      (placeInputsMapped_of_localBindingSim_resolvePlace h_lbs1
        (resolvePlace?_of_resolveAcc h_sres))
    obtain ⟨stmtOutC, h_stmtOutC⟩ :=
      compileStmt_copy_fresh_chainsrc_value h_pi_none h_sval0
    obtain ⟨stmtOut, h_stmtOut⟩ := h_val0 csPrefix stmtOutC h_stmtOutC
    have h_incrS : StateIncr
        (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src)
          (setPlaceInfo
            (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
              [Instr.Assgn (Register.R csPrefix.nextReg)
                (Rhs.Alloc (layoutToTyVal τ))])
            dstLoc.idx.1 (Register.R csPrefix.nextReg, τ)))
        (CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix) := by
      rw [h_run0]
      simp only [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked,
        CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
        CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
        CheckedCompilerM.run_pure, CheckedCompilerM.value_pure, h_erun, h_sval0]
      simp only [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM]
      exact StateIncr.trans (freshReg_state_incr _)
        (StateIncr.trans (emit_state_incr _ _)
          (StateIncr.trans (emit_state_incr _ _) (emit_state_incr _ _)))
    have h_instS : ∀ q' instr,
        q' < (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src)
          (setPlaceInfo
            (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
              [Instr.Assgn (Register.R csPrefix.nextReg)
                (Rhs.Alloc (layoutToTyVal τ))])
            dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextLabel →
        (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src)
          (setPlaceInfo
            (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
              [Instr.Assgn (Register.R csPrefix.nextReg)
                (Rhs.Alloc (layoutToTyVal τ))])
            dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).code q' = some instr →
        compProg q' = some instr := by
      intro q' instr h_lt h_code
      refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
      · exact Nat.lt_of_lt_of_le h_lt h_incrS.nextLabel_le
      · rw [h_incrS.code_eq q' h_lt]
        exact h_code
    -- §6 execute the `Alloc`
    have h_code0 : compProg s_osea.pc
        = some (Instr.Assgn (Register.R csPrefix.nextReg)
            (Rhs.Alloc (layoutToTyVal τ))) := by
      rw [h_pc]
      refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
      · refine Nat.lt_of_lt_of_le ?_ h_incrS.nextLabel_le
        refine Nat.lt_of_lt_of_le ?_
          (CheckedCompilerM.incr (placeToRegChecked RefKind.Shared src) _).nextLabel_le
        simp only [emit, setPlaceInfo, List.length_cons, List.length_nil]
        omega
      · rw [h_incrS.code_eq _ (by
          refine Nat.lt_of_lt_of_le ?_
            (CheckedCompilerM.incr (placeToRegChecked RefKind.Shared src) _).nextLabel_le
          simp only [emit, setPlaceInfo, List.length_cons, List.length_nil]
          omega)]
        rw [(CheckedCompilerM.incr (placeToRegChecked RefKind.Shared src)
          (setPlaceInfo
            (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
              [Instr.Assgn (Register.R csPrefix.nextReg)
                (Rhs.Alloc (layoutToTyVal τ))])
            dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).code_eq _ (by
          simp only [emit, setPlaceInfo, List.length_cons, List.length_nil]
          omega)]
        show (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } _).code _ = _
        have h := emit_code_at_new { csPrefix with nextReg := csPrefix.nextReg + 1 }
          [Instr.Assgn (Register.R csPrefix.nextReg)
            (Rhs.Alloc (layoutToTyVal τ))] (k := 0) (by simp)
        simpa using h
    have h_run0' := runN_Assgn_Alloc_step compProg s_osea
      (Register.R csPrefix.nextReg) (layoutToTyVal τ) h_code0 h_own_tgt'
    -- §7 the mother lemma on the source, at the POST-allocation states
    obtain ⟨sOut, n1, s_mid, tres, h_sval, h_sclean, h_srun, h_spc, h_smem,
      h_spsim, h_snt1, h_snt2, h_slbs, h_sentry, h_srt, h_snw, h_sle, h_srange,
      h_sbelow, h_sprm, h_sregmono, h_slabmono, -, -⟩ :=
      ptrChain_lowering_sim h_id_a' h_wf_t' h_chain RefKind.Shared
        (setPlaceInfo
          (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
            [Instr.Assgn (Register.R csPrefix.nextReg)
              (Rhs.Alloc (layoutToTyVal τ))])
          dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))
        { s_osea with
            mem := (oseair.allocate s_osea.mem
              (obseq.typeSize (layoutToTyVal τ))).2,
            perms := tgtPerms,
            reg := oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
              (obseq.TyVal.PTy, [Val.Ptr s_osea.mem.addrStart 0
                (obseq.typeSize (layoutToTyVal τ)) s_osea.perms.NextTag]),
            pc := s_osea.pc + 1 }
        rs permsP' h_sres (by rw [h_perms1]; exact h_tbd') h_lbs1 h_prb1
        (by
          intro a v h_find
          rw [h_find1] at h_find
          exact SourceMemSim.rename_mono h_incr_a h_incr_t h_sms a v h_find)
        (by rw [h_perms1]; exact h_psim')
        (by
          show s_osea.pc + 1 = _
          rw [h_pc]
          simp only [emit, setPlaceInfo, List.length_cons, List.length_nil])
        h_instS
    have h_stmtRun := (h_run0 csPrefix).trans
      (compileStmt_copy_fresh_chainsrc_run h_pi_none h_sval h_sclean)
    have h_gp : ∀ i, getPlaceInfo
        (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src)
          (setPlaceInfo
            (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
              [Instr.Assgn (Register.R csPrefix.nextReg)
                (Rhs.Alloc (layoutToTyVal τ))])
            dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))) i
        = getPlaceInfo
          (setPlaceInfo
            (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
              [Instr.Assgn (Register.R csPrefix.nextReg)
                (Rhs.Alloc (layoutToTyVal τ))])
            dstLoc.idx.1 (Register.R csPrefix.nextReg, τ)) i :=
      fun i => by simp only [getPlaceInfo, h_sprm]
    have h_cancel : rs.allocBase + (rs.addr - rs.allocBase) = rs.addr :=
      Nat.add_sub_cancel' h_sle
    -- §8 transports: the wide read, then the dst write
    obtain ⟨p2w, h_read2_tgt, h_psim2w⟩ :=
      sb_read_respects_PermSim h_spsim h_wf_t' h_srt h_snw h_read_src
    have h_w := h_step
    simp only [mirlite.writeResolvedPlace] at h_w
    split at h_w
    · simp at h_w
    · rename_i h_nb
      split at h_w
      · rename_i perms₃ h_useMut_src
        cases h_w
        have h_useMut_src' : MSB.useMut perms₂ s_mir.mem.addrStart (blockSize τ)
            s_mir.perms.NextTag = .ok perms₃ := by
          grind
        obtain ⟨dstReg2, baseD2, tagD2, h_piD2, h_entryD2, h_raD2, h_rtD2,
          h_nwD2, h_domD2⟩ := h_slbs dstLoc _ h_lookup_set
        have h_dr2 : dstReg2 = Register.R csPrefix.nextReg := by grind
        have h_baseD2 : baseD2 = s_mir.mem.addrStart := (h_id_a' _ _ h_raD2).symm
        rw [h_dr2, h_baseD2] at h_entryD2
        obtain ⟨p3w, h_useMut_tgt, h_psim3w⟩ :=
          sb_write_respects_PermSim h_psim2w h_wf_t' h_rtD2 h_nwD2 h_useMut_src'
        -- §9 the READ into the temporary, then the write
        have h_ts : obseq.typeSize (obseq.layoutToTyVal τ) = blockSize τ := by
          simp [blockSize]
        have h_code1 : compProg s_mid.pc
            = some (Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg)
                (Rhs.Load (obseq.layoutToTyVal τ) sOut.result.reg)) := by
          rw [h_spc]
          refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
          · rw [h_stmtRun]
            simp only [emit, List.length_cons, List.length_nil]
            omega
          · rw [h_stmtRun]
            rw [emit_code_lt_nextLabel _ _ (by
              simp only [emit, List.length_cons, List.length_nil]; omega)]
            have h := emit_code_at_new
              { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg + 1 }
              [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg) (Rhs.Load (obseq.layoutToTyVal τ) sOut.result.reg)]
              (k := 0) (by simp)
            simpa using h
        have h_code2 : compProg (s_mid.pc + 1)
            = some (Instr.RStore (obseq.layoutToTyVal τ) (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg)
                (Register.R csPrefix.nextReg)) := by
          rw [h_spc]
          refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
          · rw [h_stmtRun]
            simp only [emit, List.length_cons, List.length_nil]
            omega
          · rw [h_stmtRun]
            have h := emit_code_at_new
              (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg + 1 }
                [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg) (Rhs.Load (obseq.layoutToTyVal τ) sOut.result.reg)])
              [Instr.RStore (obseq.layoutToTyVal τ) (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg) (Register.R csPrefix.nextReg)]
              (k := 0) (by simp)
            simpa [emit] using h
        have h_read2t : MSB.read s_mid.perms
            (rs.allocBase + (rs.addr - rs.allocBase))
            (obseq.typeSize (obseq.layoutToTyVal τ)) tres = .ok p2w := by
          rw [h_ts, h_cancel]
          exact h_read2_tgt
        have h_run1 := runN_Assgn_Load_ptr_step compProg s_mid
          (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg) sOut.result.reg (obseq.layoutToTyVal τ) h_code1 h_sentry
          (by rw [h_ts]; grind) h_read2t
        rw [h_ts, h_cancel] at h_run1
        have h_regne : Register.R csPrefix.nextReg ≠ (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg) := by
          intro h_eq
          injection h_eq with h_eq'
          have h1 : csPrefix.nextReg + 1 ≤ (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg := by
            have := h_sregmono
            simp only [setPlaceInfo, emit] at this
            exact this
          omega
        have h_dentry2 : oseair.RegMap.lookup
            (oseair.RegMap.insert s_mid.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg)
              (obseq.layoutToTyVal τ, (oseair.readWordSeq s_mid.mem rs.addr (blockSize τ)))) (Register.R csPrefix.nextReg)
            = some (obseq.TyVal.PTy,
                [Val.Ptr s_mir.mem.addrStart 0 (blockSize τ) tagD2]) := by
          rw [RegMap.lookup_insert_ne _ h_regne]
          exact h_entryD2
        have h_useMut2t : MSB.useMut p2w (s_mir.mem.addrStart + 0)
            (oseair.readWordSeq s_mid.mem rs.addr (blockSize τ)).length tagD2 = .ok p3w := by
          rw [Nat.add_zero, oseair_readWordSeq_length]
          exact h_useMut_tgt
        have h_wtp : oseair.writeThroughPtr MSB
            { s_mid with
                perms := p2w,
                reg := oseair.RegMap.insert s_mid.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg)
                  (obseq.layoutToTyVal τ, (oseair.readWordSeq s_mid.mem rs.addr (blockSize τ))),
                pc := s_mid.pc + 1 }
            (Register.R csPrefix.nextReg) (oseair.readWordSeq s_mid.mem rs.addr (blockSize τ)) "RStore Invalid Regs"
            = oseair.Result.Ok
              { s_mid with
                  perms := p3w,
                  reg := oseair.RegMap.insert s_mid.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg)
                    (obseq.layoutToTyVal τ, (oseair.readWordSeq s_mid.mem rs.addr (blockSize τ))),
                  mem := oseair.writeWordSeq s_mid.mem s_mir.mem.addrStart (oseair.readWordSeq s_mid.mem rs.addr (blockSize τ)),
                  pc := s_mid.pc + 1 + 1 } := by
          simp only [oseair.writeThroughPtr, h_dentry2]
          rw [if_neg (by
            rw [oseair_readWordSeq_length, Nat.add_zero]
            exact Nat.not_lt.mpr (Nat.le_refl _))]
          simp only [h_useMut2t]
          rfl
        have h_run2 := runN_RStore_step compProg _ _
          (obseq.layoutToTyVal τ) (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg) (Register.R csPrefix.nextReg) _ _ h_code2
          (RegMap.lookup_insert_self _ _ _) h_dentry2 h_wtp
        have h_runA := (oseair_runN_add 1 n1 s_osea compProg _ h_run0').trans h_srun
        have h_runB := (oseair_runN_add (1 + n1) 1 s_osea compProg s_mid h_runA).trans
          h_run1
        have h_run := (oseair_runN_add (1 + n1 + 1) 1 s_osea compProg _ h_runB).trans
          h_run2
        -- §10 memory
        have h_rws1 : ∀ (a n : Nat),
            mirlite.readWordSeq s1.mem a n = mirlite.readWordSeq s_mir.mem a n :=
          fun a n => mirlite_readWordSeq_congr h_find1 n a
        have h_sms1 : SourceMemSim
            (ρa.extendBlock s_mir.mem.addrStart (blockSize τ))
            (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag) s1.mem s_mid.mem := by
          intro a v h_find
          rw [h_find1] at h_find
          rw [h_smem]
          exact SourceMemSim.rename_mono h_incr_a h_incr_t h_sms a v h_find
        have h_rel : ListRel (MemValSim
            (ρa.extendBlock s_mir.mem.addrStart (blockSize τ))
            (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag))
            (mirlite.readWordSeq s1.mem rs.addr (blockSize τ))
            (oseair.readWordSeq s_mid.mem rs.addr (blockSize τ)) :=
          readWordSeq_sim h_id_a' h_sms1 (blockSize τ) rs.addr
        have h_dom : ∀ k,
            k < (mirlite.readWordSeq s1.mem rs.addr (blockSize τ)).length →
            (ρa.extendBlock s_mir.mem.addrStart (blockSize τ))
              (s_mir.mem.addrStart + k) = some (s_mir.mem.addrStart + k) := by
          intro k hk
          exact h_ra_dom k (by rw [h_rws1] at hk; simpa using hk)
        have h_sms' := SourceMemSim.writeWordSeq_extend h_id_a' _ _ _ _ _ h_rel h_dom
          h_sms1
        -- §11 rebuild the invariant under both extended renames
        refine ⟨_, _, _, 1 + n1 + 1 + 1, h_incr_a, h_incr_t, h_run, ?_⟩
        refine ⟨CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix,
          ⟨prefixCompileState_succ (by rw [h_pc1]; exact h_csAt)
            (by rw [h_pc1]; exact h_stmt) h_stmtOut, ?_⟩, ?_, h_sms',
          h_psim3w, h_id_a', h_wf_t', ?_, ?_, ?_, ?_⟩
        · show s_mid.pc + 1 + 1 = _
          rw [h_spc, h_stmtRun]
          simp [emit]
        · have h_lbsT : LocalBindingSim
              (ρa.extendBlock s_mir.mem.addrStart (blockSize τ))
              (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag) s1.env
              { s_mid with
                  perms := p3w,
                  reg := oseair.RegMap.insert s_mid.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg)
                    (obseq.layoutToTyVal τ, (oseair.readWordSeq s_mid.mem rs.addr (blockSize τ))),
                  mem := oseair.writeWordSeq s_mid.mem s_mir.mem.addrStart (oseair.readWordSeq s_mid.mem rs.addr (blockSize τ)),
                  pc := s_mid.pc + 1 + 1 } (setPlaceInfo
            (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
              [Instr.Assgn (Register.R csPrefix.nextReg)
                (Rhs.Alloc (layoutToTyVal τ))])
            dstLoc.idx.1 (Register.R csPrefix.nextReg, τ)) :=
            LocalBindingSim.insert_fresh_reg h_slbs h_prb1 h_sregmono rfl
          intro τ' loc' binding' h_env'
          obtain ⟨reg', base', tag', h_pi', h_entry', h_ra', h_rt', h_nw', h_dom'⟩ :=
            h_lbsT loc' binding' h_env'
          refine ⟨reg', base', tag', ?_, h_entry', h_ra', h_rt', h_nw', h_dom'⟩
          rw [h_stmtRun, getPlaceInfo_emit, getPlaceInfo_emit, getPlaceInfo_setNextReg,
            h_gp]
          exact h_pi'
        · show TagRenameBounded _ perms₃.NextTag p3w.NextTag
          rw [sb_write_NextTag h_useMut_src', sb_read_NextTag h_read_src, h_snt1,
            sb_write_NextTag h_useMut_tgt, sb_read_NextTag h_read2_tgt]
          exact TagRenameBounded.mono h_tbd'
            (Nat.le_of_eq (congrArg AccessPerms.NextTag h_perms1.symm)) h_snt2
        · simp only [AllocLockstep, mirlite_writeWordSeq_addrStart,
            oseair_writeWordSeq_addrStart, h_smem, h_memstart1]
          show (oseair.allocate s_osea.mem (obseq.typeSize (layoutToTyVal τ))).2.addrStart
            = _
          simp only [oseair.allocate]
          rw [h_addr_eq, h_sz]
        · intro τ' loc' h_none
          have h_none1 : mirlite.Env.lookup s1.env loc' = none := h_none
          rw [← h_s1] at h_none1
          by_cases h_idx : loc'.idx = dstLoc.idx
          · exfalso
            simp only [mirlite.Env.lookup, mirlite.Env.set, h_idx, if_pos rfl]
              at h_none1
            exact absurd h_none1 (by simp)
          have h_idxv : loc'.idx.1 ≠ dstLoc.idx.1 := fun h => h_idx (Fin.ext h)
          have h_none0 : mirlite.Env.lookup s_mir.env loc' = none := by
            simpa only [mirlite.Env.lookup, mirlite.Env.set, if_neg h_idx]
              using h_none1
          rw [h_stmtRun, getPlaceInfo_emit, getPlaceInfo_emit, getPlaceInfo_setNextReg,
            h_gp, getPlaceInfo_setPlaceInfo_ne _ h_idxv]
          exact h_unmap loc' h_none0
        · intro idx reg'' τ'' h_look
          rw [h_stmtRun] at h_look ⊢
          rw [getPlaceInfo_emit, getPlaceInfo_emit, getPlaceInfo_setNextReg, h_gp]
            at h_look
          refine RegisterBelow.mono ?_ (h_prb1 _ _ _ h_look)
          simp only [emit]
          exact Nat.le_trans h_sregmono (Nat.le_succ _)
      · simp at h_w

/-! ## FRESH destination with a PROJ-TOPPED source: the root `Alloc`,
    then the base lowering, then the projection's own shape. -/

theorem compileStmt_copy_fresh_projchain_zero_run
    {Γ : Ctx} {τ σb : LayoutTy}
    {dstLoc : Local Γ τ} {B : Place Γ σb} {path : PathTo σb τ}
    {cs : CompilerState}
    {bOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared B)}
    (h_np : ∀ (σ' : LayoutTy) (b : Place Γ σ') (q : PathTo σ' σb), B = b.proj q → False)
    (h_off : pathOffset path = 0)
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = none)
    (h_bval : CheckedCompilerM.value (placeToRegChecked RefKind.Shared B)
      (setPlaceInfo
        (emit { cs with nextReg := cs.nextReg + 1 }
          [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal τ))])
        dstLoc.idx.1 (Register.R cs.nextReg, τ)) = Except.ok bOut)
    (h_bclean : bOut.result.cleanup = []) :
    CheckedCompilerM.run
        (compileStmtChecked
          (Stmt.assign (.local dstLoc) (.copy (.proj B path)))) cs
      = emit (emit
          { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
          (setPlaceInfo
            (emit { cs with nextReg := cs.nextReg + 1 }
              [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal τ))])
            dstLoc.idx.1 (Register.R cs.nextReg, τ))) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
          (setPlaceInfo
            (emit { cs with nextReg := cs.nextReg + 1 }
              [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal τ))])
            dstLoc.idx.1 (Register.R cs.nextReg, τ))).nextReg + 1 }
          [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
          (setPlaceInfo
            (emit { cs with nextReg := cs.nextReg + 1 }
              [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal τ))])
            dstLoc.idx.1 (Register.R cs.nextReg, τ))).nextReg) (Rhs.Load (obseq.layoutToTyVal τ) bOut.result.reg)])
          [Instr.RStore (obseq.layoutToTyVal τ) (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
          (setPlaceInfo
            (emit { cs with nextReg := cs.nextReg + 1 }
              [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal τ))])
            dstLoc.idx.1 (Register.R cs.nextReg, τ))).nextReg) (Register.R cs.nextReg)] := by
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_fresh (loc := dstLoc) h_dst
  have h_proj_eq := placeToRegChecked_proj_root_eq (Γ := Γ)
    (kind := RefKind.Shared) (base := B) path h_np
  simp only [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked,
    h_proj_eq,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
    h_run, h_val, h_bval, h_off, dif_pos]
  simp [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM,
    cleanupInstrs, h_bclean, emit_nil]

theorem compileStmt_copy_fresh_projchain_zero_value
    {Γ : Ctx} {τ σb : LayoutTy}
    {dstLoc : Local Γ τ} {B : Place Γ σb} {path : PathTo σb τ}
    {cs : CompilerState}
    {bOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared B)}
    (h_np : ∀ (σ' : LayoutTy) (b : Place Γ σ') (q : PathTo σ' σb), B = b.proj q → False)
    (h_off : pathOffset path = 0)
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = none)
    (h_bval : CheckedCompilerM.value (placeToRegChecked RefKind.Shared B)
      (setPlaceInfo
        (emit { cs with nextReg := cs.nextReg + 1 }
          [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal τ))])
        dstLoc.idx.1 (Register.R cs.nextReg, τ)) = Except.ok bOut) :
    ∃ so, CheckedCompilerM.value
      (compileStmtChecked (Stmt.assign (.local dstLoc) (.copy (.proj B path)))) cs
      = Except.ok so := by
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_fresh (loc := dstLoc) h_dst
  have h_proj_eq := placeToRegChecked_proj_root_eq (Γ := Γ)
    (kind := RefKind.Shared) (base := B) path h_np
  simp only [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked,
    h_proj_eq,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
    h_run, h_bval, h_off, dif_pos]
  exact ⟨_, rfl⟩

theorem compileStmt_copy_fresh_projchain_offset_run
    {Γ : Ctx} {τ σb : LayoutTy}
    {dstLoc : Local Γ τ} {B : Place Γ σb} {path : PathTo σb τ}
    {cs : CompilerState}
    {bOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared B)}
    (h_np : ∀ (σ' : LayoutTy) (b : Place Γ σ') (q : PathTo σ' σb), B = b.proj q → False)
    (h_off : pathOffset path ≠ 0)
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = none)
    (h_bval : CheckedCompilerM.value (placeToRegChecked RefKind.Shared B)
      (setPlaceInfo
        (emit { cs with nextReg := cs.nextReg + 1 }
          [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal τ))])
        dstLoc.idx.1 (Register.R cs.nextReg, τ)) = Except.ok bOut)
    (h_bclean : bOut.result.cleanup = []) :
    CheckedCompilerM.run
        (compileStmtChecked
          (Stmt.assign (.local dstLoc) (.copy (.proj B path)))) cs
      = emit (emit
          { (emit
              { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
            (setPlaceInfo
              (emit { cs with nextReg := cs.nextReg + 1 }
                [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal τ))])
              dstLoc.idx.1 (Register.R cs.nextReg, τ))) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
            (setPlaceInfo
              (emit { cs with nextReg := cs.nextReg + 1 }
                [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal τ))])
              dstLoc.idx.1 (Register.R cs.nextReg, τ))).nextReg + 1 }
              [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
            (setPlaceInfo
              (emit { cs with nextReg := cs.nextReg + 1 }
                [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal τ))])
              dstLoc.idx.1 (Register.R cs.nextReg, τ))).nextReg)
                (borrowRhs RefKind.Shared (blockSize τ) bOut.result.reg
                  (pathOffset path))]) with
              nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
            (setPlaceInfo
              (emit { cs with nextReg := cs.nextReg + 1 }
                [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal τ))])
              dstLoc.idx.1 (Register.R cs.nextReg, τ))).nextReg + 1 + 1 }
          [Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
            (setPlaceInfo
              (emit { cs with nextReg := cs.nextReg + 1 }
                [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal τ))])
              dstLoc.idx.1 (Register.R cs.nextReg, τ))).nextReg + 1)) (Rhs.Load (obseq.layoutToTyVal τ) (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
            (setPlaceInfo
              (emit { cs with nextReg := cs.nextReg + 1 }
                [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal τ))])
              dstLoc.idx.1 (Register.R cs.nextReg, τ))).nextReg)),
           Instr.Die (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
            (setPlaceInfo
              (emit { cs with nextReg := cs.nextReg + 1 }
                [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal τ))])
              dstLoc.idx.1 (Register.R cs.nextReg, τ))).nextReg) (blockSize τ)])
          [Instr.RStore (obseq.layoutToTyVal τ) (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
            (setPlaceInfo
              (emit { cs with nextReg := cs.nextReg + 1 }
                [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal τ))])
              dstLoc.idx.1 (Register.R cs.nextReg, τ))).nextReg + 1)) (Register.R cs.nextReg)] := by
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_fresh (loc := dstLoc) h_dst
  have h_proj_eq := placeToRegChecked_proj_root_eq (Γ := Γ)
    (kind := RefKind.Shared) (base := B) path h_np
  simp only [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked,
    h_proj_eq,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
    h_run, h_val, h_bval]
  simp [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM,
    cleanupInstrs, h_bclean, emit_nil, h_off, borrowRhs]
  rfl

theorem compileStmt_copy_fresh_projchain_offset_value
    {Γ : Ctx} {τ σb : LayoutTy}
    {dstLoc : Local Γ τ} {B : Place Γ σb} {path : PathTo σb τ}
    {cs : CompilerState}
    {bOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared B)}
    (h_np : ∀ (σ' : LayoutTy) (b : Place Γ σ') (q : PathTo σ' σb), B = b.proj q → False)
    (h_off : pathOffset path ≠ 0)
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = none)
    (h_bval : CheckedCompilerM.value (placeToRegChecked RefKind.Shared B)
      (setPlaceInfo
        (emit { cs with nextReg := cs.nextReg + 1 }
          [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal τ))])
        dstLoc.idx.1 (Register.R cs.nextReg, τ)) = Except.ok bOut) :
    ∃ so, CheckedCompilerM.value
      (compileStmtChecked (Stmt.assign (.local dstLoc) (.copy (.proj B path)))) cs
      = Except.ok so := by
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_fresh (loc := dstLoc) h_dst
  have h_proj_eq := placeToRegChecked_proj_root_eq (Γ := Γ)
    (kind := RefKind.Shared) (base := B) path h_np
  simp only [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked,
    h_proj_eq,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
    h_run, h_bval, dif_neg h_off]
  exact ⟨_, rfl⟩

/-- REGIME B for copy with a PROJ-TOPPED source at ZERO offset,
    CLOSED 2026-09-03: `dst := copy B.f` with an UNBOUND destination and
    `pathOffset f = 0`. The projection passes the base register through,
    so this is the chain-source regime B with a `+ 0` on the source
    resolution. -/
theorem copy_fresh_projchain_zero_simulation
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {τ σb : LayoutTy}
    {dstLoc : Local Γ τ} {B : Place Γ σb} {path : PathTo σb τ}
    (compProg : oseair.Prog)
    (h_chain : PtrChain B)
    (h_off : pathOffset path = 0)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    {stmt0 : Stmt Γ}
    (h_stmt : prog.get? s_mir.pc = some stmt0)
    (h_run0 : ∀ cs, CheckedCompilerM.run (compileStmtChecked stmt0) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.local dstLoc) (.copy (.proj B path)))) cs)
    (h_val0 : ∀ cs so, CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.local dstLoc) (.copy (.proj B path)))) cs
        = Except.ok so →
      ∃ so', CheckedCompilerM.value (compileStmtChecked stmt0) cs
        = Except.ok so')
    (h_envD : mirlite.Env.lookup s_mir.env dstLoc = none)
    (h_step : mirlite.stepStmt MSB s_mir
      (.assign (.local dstLoc) (.copy (.proj B path))) = .ok s_mir') :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' := by
  obtain ⟨csPrefix, ⟨h_csAt, h_pc⟩, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_tbd,
    h_alloc, h_unmap, h_prb⟩ := h_inv
  have h_pi_none : getPlaceInfo csPrefix dstLoc.idx.1 = none := h_unmap dstLoc h_envD
  -- §1 the source allocates the destination root before reading
  simp only [mirlite.stepStmt, mirlite.doAssign] at h_step
  cases h_prep : mirlite.preparePlaceAssign MSB s_mir (Place.local dstLoc) with
  | err msg => rw [h_prep] at h_step; simp at h_step
  | ok s1 =>
  rw [h_prep] at h_step
  simp only [mirlite.preparePlaceAssign, mirlite.resolvePlace?, h_envD,
    mirlite.allocateRoot, mirlite.allocateBase, mirlite.allocate] at h_prep
  cases h_own_src : MSB.own s_mir.perms s_mir.mem.addrStart (blockSize τ) with
  | error e => rw [h_own_src] at h_prep; simp at h_prep
  | ok pr =>
  obtain ⟨permsOwned, tagS⟩ := pr
  rw [h_own_src] at h_prep
  injection h_prep with h_s1
  -- §2 the two ρ extensions and the post-allocation source state
  obtain ⟨tgtPerms, h_own_tgt, h_tagS_eq, h_incr_t, h_wf_t', h_tbd', h_psim'⟩ :=
    sb_own_respects_PermSim h_psim h_wf_t h_tbd h_own_src
  subst h_tagS_eq
  have h_addr_eq : s_osea.mem.addrStart = s_mir.mem.addrStart := h_alloc
  have h_incr_a :=
    AddrRenameIncr.extendBlock h_id_a s_mir.mem.addrStart (blockSize τ)
  have h_id_a' :=
    IdentityOnDomain.extendBlock h_id_a s_mir.mem.addrStart (blockSize τ)
  have h_ra_dom : ∀ k, k < blockSize τ →
      (ρa.extendBlock s_mir.mem.addrStart (blockSize τ))
        (s_mir.mem.addrStart + k) = some (s_mir.mem.addrStart + k) :=
    fun _ hk => AddrRenameMap.extendBlock_mem hk
  have h_ra_base : (ρa.extendBlock s_mir.mem.addrStart (blockSize τ))
      s_mir.mem.addrStart = some s_mir.mem.addrStart :=
    AddrRenameMap.extendBlock_base _ _ _
  have h_rt_new : (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag)
      s_mir.perms.NextTag = some s_osea.perms.NextTag :=
    TagRenameMap.extend_self _ _ _
  have h0 : wildcardTag < s_mir.perms.NextTag := (h_tbd _ _ h_wf_t.2).1
  have h_nw : (s_mir.perms.NextTag == wildcardTag) = false := by grind
  -- the post-allocation source state stays ABSTRACT (`s1`); everything
  -- needed about it comes from the allocation equation
  have h_lookup_set : mirlite.Env.lookup s1.env dstLoc
      = some { addr := s_mir.mem.addrStart, tag := s_mir.perms.NextTag } := by
    rw [← h_s1]
    simp [mirlite.Env.lookup, mirlite.Env.set]
  have h_perms1 : s1.perms = permsOwned := by rw [← h_s1]
  have h_pc1 : s1.pc = s_mir.pc := by rw [← h_s1]
  have h_memstart1 : s1.mem.addrStart = s_mir.mem.addrStart + blockSize τ := by
    rw [← h_s1]
  have h_find1 : ∀ a, mirlite.Mem.find? s1.mem a = mirlite.Mem.find? s_mir.mem a := by
    intro a
    rw [← h_s1]
    rfl
  -- §3 the source read, kept OPAQUE at the chain
  simp only [mirlite.evalRExpr] at h_step
  have h_np := h_chain.not_proj
  have h_o' : PathTo.offset path = 0 := h_off
  cases h_sres : mirlite.resolvePlaceAcc MSB s1 B with
  | error e =>
      rw [resolvePlaceAcc_proj_base_err h_sres] at h_step
      simp at h_step
  | ok pr2 =>
  obtain ⟨rs, permsP'⟩ := pr2
  rw [resolvePlaceAcc_proj_base_ok h_sres] at h_step
  simp only [h_o', Nat.add_zero] at h_step
  by_cases h_fitS : rs.addr + blockSize τ > rs.allocBase + rs.allocSize
  · rw [if_pos h_fitS] at h_step
    simp at h_step
  · rw [if_neg h_fitS] at h_step
    cases h_read_src : MSB.read permsP' rs.addr (blockSize τ) rs.tag with
    | error e => rw [h_read_src] at h_step; simp at h_step
    | ok perms₂ =>
    rw [h_read_src] at h_step
    simp only [mirlite.resolvePlaceAcc, h_lookup_set] at h_step
    -- §4 the compiled prefix: the root `Alloc` and the post-alloc state
    have h_erun : CompilerM.run (ensureLocalRegE dstLoc) csPrefix
        = setPlaceInfo
            (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
              [Instr.Assgn (Register.R csPrefix.nextReg)
                (Rhs.Alloc (layoutToTyVal τ))])
            dstLoc.idx.1 (Register.R csPrefix.nextReg, τ) :=
      (ensureLocalRegE_fresh (loc := dstLoc) h_pi_none).1
    have h_pi_new : getPlaceInfo
        (setPlaceInfo
          (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
            [Instr.Assgn (Register.R csPrefix.nextReg)
              (Rhs.Alloc (layoutToTyVal τ))])
          dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))
        dstLoc.idx.1 = some (Register.R csPrefix.nextReg, τ) :=
      getPlaceInfo_setPlaceInfo_self _ _ _
    have h_sz : obseq.typeSize (layoutToTyVal τ) = blockSize τ :=
      obseq.typeSize_layoutToTyVal _
    have h_own_tgt' : MSB.own s_osea.perms s_osea.mem.addrStart
        (obseq.typeSize (layoutToTyVal τ))
        = .ok (tgtPerms, s_osea.perms.NextTag) := by
      rw [h_sz, h_addr_eq]
      exact h_own_tgt
    -- the post-Alloc target state
    have h_prb1 : PlaceRegMapBound
        (setPlaceInfo
          (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
            [Instr.Assgn (Register.R csPrefix.nextReg)
              (Rhs.Alloc (layoutToTyVal τ))])
          dstLoc.idx.1 (Register.R csPrefix.nextReg, τ)) := by
      intro idx reg τ'' h_look
      by_cases h_i : idx = dstLoc.idx.1
      · subst h_i
        rw [getPlaceInfo_setPlaceInfo_self] at h_look
        injection h_look with h_look'
        have : reg = Register.R csPrefix.nextReg := (congrArg Prod.fst h_look').symm
        subst this
        show csPrefix.nextReg < _
        simp only [emit, setPlaceInfo]
        grind
      · rw [getPlaceInfo_setPlaceInfo_ne _ h_i] at h_look
        refine RegisterBelow.mono ?_ (h_prb _ _ _ h_look)
        simp only [emit, setPlaceInfo]
        grind
    have h_lbs1 : LocalBindingSim
        (ρa.extendBlock s_mir.mem.addrStart (blockSize τ))
        (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag)
        s1.env
        { s_osea with
            mem := (oseair.allocate s_osea.mem
              (obseq.typeSize (layoutToTyVal τ))).2,
            perms := tgtPerms,
            reg := oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
              (obseq.TyVal.PTy, [Val.Ptr s_osea.mem.addrStart 0
                (obseq.typeSize (layoutToTyVal τ)) s_osea.perms.NextTag]),
            pc := s_osea.pc + 1 }
        (setPlaceInfo
          (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
            [Instr.Assgn (Register.R csPrefix.nextReg)
              (Rhs.Alloc (layoutToTyVal τ))])
          dstLoc.idx.1 (Register.R csPrefix.nextReg, τ)) := by
      rw [← h_s1]
      intro τ' loc' binding' h_env'
      by_cases h_idx : loc'.idx = dstLoc.idx
      · have h_ty : τ' = τ := by
          rw [← loc'.hTy, h_idx, dstLoc.hTy]
        subst h_ty
        have h_b : binding' = { addr := s_mir.mem.addrStart,
                                tag := s_mir.perms.NextTag } := by
          grind [mirlite.Env.lookup, mirlite.Env.set]
        subst h_b
        refine ⟨Register.R csPrefix.nextReg, s_mir.mem.addrStart,
          s_osea.perms.NextTag, ?_, ?_, ?_, h_rt_new, h_nw, ?_⟩
        · rw [show loc'.idx.1 = dstLoc.idx.1 from congrArg Fin.val h_idx]
          exact h_pi_new
        · show oseair.RegMap.lookup _ _ = _
          rw [← h_addr_eq, ← h_sz]
          exact RegMap.lookup_insert_self _ _ _
        · exact h_ra_base
        · intro k hk
          exact ⟨s_mir.mem.addrStart + k, h_ra_dom k hk⟩
      · have h_env'' : mirlite.Env.lookup s_mir.env loc' = some binding' := by
          simpa only [mirlite.Env.lookup, mirlite.Env.set, if_neg h_idx]
            using h_env'
        obtain ⟨reg', base', tag', h_pi', h_entry', h_ra', h_rt', h_nw', h_dom'⟩ :=
          h_lbs loc' binding' h_env''
        have h_idxv : loc'.idx.1 ≠ dstLoc.idx.1 := by grind [Fin.ext]
        have h_regne : reg' ≠ Register.R csPrefix.nextReg := by
          cases reg' with
          | R n =>
              have h_lt := h_prb _ _ _ h_pi'
              grind [RegisterBelow]
        refine ⟨reg', base', tag', ?_, ?_, h_incr_a _ _ h_ra',
          h_incr_t _ _ h_rt', h_nw',
          fun k hk => ⟨(h_dom' k hk).choose,
            h_incr_a _ _ (h_dom' k hk).choose_spec⟩⟩
        · rw [getPlaceInfo_setPlaceInfo_ne _ h_idxv]
          exact h_pi'
        · show oseair.RegMap.lookup _ _ = _
          rw [RegMap.lookup_insert_ne _ h_regne]
          exact h_entry'
    -- §5 the statement value and code inclusion for the source lowering
    have h_mappedP : PlaceInputsMapped
        (setPlaceInfo
          (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
            [Instr.Assgn (Register.R csPrefix.nextReg)
              (Rhs.Alloc (layoutToTyVal τ))])
          dstLoc.idx.1 (Register.R csPrefix.nextReg, τ)) (Place.proj B path) :=
      placeInputsMapped_of_localBindingSim_resolvePlace h_lbs1
        (resolvePlace?_of_resolveAcc
          (resolvePlaceAcc_proj_base_ok (path := path) h_sres))
    have h_mappedB : PlaceInputsMapped
        (setPlaceInfo
          (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
            [Instr.Assgn (Register.R csPrefix.nextReg)
              (Rhs.Alloc (layoutToTyVal τ))])
          dstLoc.idx.1 (Register.R csPrefix.nextReg, τ)) B := h_mappedP
    obtain ⟨sOut0, h_sval0⟩ := placeToRegChecked_ok_of_placeInputsMapped
      (cs := setPlaceInfo
          (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
            [Instr.Assgn (Register.R csPrefix.nextReg)
              (Rhs.Alloc (layoutToTyVal τ))])
          dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))
      (kind := RefKind.Shared) h_mappedB
    obtain ⟨stmtOutC, h_stmtOutC⟩ :=
      compileStmt_copy_fresh_projchain_zero_value h_np h_off h_pi_none h_sval0
    obtain ⟨stmtOut, h_stmtOut⟩ := h_val0 csPrefix stmtOutC h_stmtOutC
    have h_incrS : StateIncr
        (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
          (setPlaceInfo
            (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
              [Instr.Assgn (Register.R csPrefix.nextReg)
                (Rhs.Alloc (layoutToTyVal τ))])
            dstLoc.idx.1 (Register.R csPrefix.nextReg, τ)))
        (CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix) := by
      rw [h_run0]
      simp only [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked,
        placeToRegChecked_proj_root_eq (Γ := Γ) (kind := RefKind.Shared)
          (base := B) path h_np,
        CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
        CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
        CheckedCompilerM.run_pure, CheckedCompilerM.value_pure, h_erun, h_sval0,
        h_off, dif_pos]
      simp only [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM]
      exact StateIncr.trans (freshReg_state_incr _)
        (StateIncr.trans (emit_state_incr _ _)
          (StateIncr.trans (emit_state_incr _ _) (emit_state_incr _ _)))
    have h_instS : ∀ q' instr,
        q' < (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
          (setPlaceInfo
            (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
              [Instr.Assgn (Register.R csPrefix.nextReg)
                (Rhs.Alloc (layoutToTyVal τ))])
            dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextLabel →
        (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
          (setPlaceInfo
            (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
              [Instr.Assgn (Register.R csPrefix.nextReg)
                (Rhs.Alloc (layoutToTyVal τ))])
            dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).code q' = some instr →
        compProg q' = some instr := by
      intro q' instr h_lt h_code
      refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
      · exact Nat.lt_of_lt_of_le h_lt h_incrS.nextLabel_le
      · rw [h_incrS.code_eq q' h_lt]
        exact h_code
    -- §6 execute the `Alloc`
    have h_code0 : compProg s_osea.pc
        = some (Instr.Assgn (Register.R csPrefix.nextReg)
            (Rhs.Alloc (layoutToTyVal τ))) := by
      rw [h_pc]
      refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
      · refine Nat.lt_of_lt_of_le ?_ h_incrS.nextLabel_le
        refine Nat.lt_of_lt_of_le ?_
          (CheckedCompilerM.incr (placeToRegChecked RefKind.Shared B) _).nextLabel_le
        simp only [emit, setPlaceInfo, List.length_cons, List.length_nil]
        omega
      · rw [h_incrS.code_eq _ (by
          refine Nat.lt_of_lt_of_le ?_
            (CheckedCompilerM.incr (placeToRegChecked RefKind.Shared B) _).nextLabel_le
          simp only [emit, setPlaceInfo, List.length_cons, List.length_nil]
          omega)]
        rw [(CheckedCompilerM.incr (placeToRegChecked RefKind.Shared B)
          (setPlaceInfo
            (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
              [Instr.Assgn (Register.R csPrefix.nextReg)
                (Rhs.Alloc (layoutToTyVal τ))])
            dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).code_eq _ (by
          simp only [emit, setPlaceInfo, List.length_cons, List.length_nil]
          omega)]
        show (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } _).code _ = _
        have h := emit_code_at_new { csPrefix with nextReg := csPrefix.nextReg + 1 }
          [Instr.Assgn (Register.R csPrefix.nextReg)
            (Rhs.Alloc (layoutToTyVal τ))] (k := 0) (by simp)
        simpa using h
    have h_run0' := runN_Assgn_Alloc_step compProg s_osea
      (Register.R csPrefix.nextReg) (layoutToTyVal τ) h_code0 h_own_tgt'
    -- §7 the mother lemma on the source, at the POST-allocation states
    obtain ⟨sOut, n1, s_mid, tres, h_sval, h_sclean, h_srun, h_spc, h_smem,
      h_spsim, h_snt1, h_snt2, h_slbs, h_sentry, h_srt, h_snw, h_sle, h_srange,
      h_sbelow, h_sprm, h_sregmono, h_slabmono, -, -⟩ :=
      ptrChain_lowering_sim h_id_a' h_wf_t' h_chain RefKind.Shared
        (setPlaceInfo
          (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
            [Instr.Assgn (Register.R csPrefix.nextReg)
              (Rhs.Alloc (layoutToTyVal τ))])
          dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))
        { s_osea with
            mem := (oseair.allocate s_osea.mem
              (obseq.typeSize (layoutToTyVal τ))).2,
            perms := tgtPerms,
            reg := oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
              (obseq.TyVal.PTy, [Val.Ptr s_osea.mem.addrStart 0
                (obseq.typeSize (layoutToTyVal τ)) s_osea.perms.NextTag]),
            pc := s_osea.pc + 1 }
        rs permsP' h_sres (by rw [h_perms1]; exact h_tbd') h_lbs1 h_prb1
        (by
          intro a v h_find
          rw [h_find1] at h_find
          exact SourceMemSim.rename_mono h_incr_a h_incr_t h_sms a v h_find)
        (by rw [h_perms1]; exact h_psim')
        (by
          show s_osea.pc + 1 = _
          rw [h_pc]
          simp only [emit, setPlaceInfo, List.length_cons, List.length_nil])
        h_instS
    have h_stmtRun := (h_run0 csPrefix).trans
      (compileStmt_copy_fresh_projchain_zero_run h_np h_off h_pi_none h_sval h_sclean)
    have h_gp : ∀ i, getPlaceInfo
        (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
          (setPlaceInfo
            (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
              [Instr.Assgn (Register.R csPrefix.nextReg)
                (Rhs.Alloc (layoutToTyVal τ))])
            dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))) i
        = getPlaceInfo
          (setPlaceInfo
            (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
              [Instr.Assgn (Register.R csPrefix.nextReg)
                (Rhs.Alloc (layoutToTyVal τ))])
            dstLoc.idx.1 (Register.R csPrefix.nextReg, τ)) i :=
      fun i => by simp only [getPlaceInfo, h_sprm]
    have h_cancel : rs.allocBase + (rs.addr - rs.allocBase) = rs.addr :=
      Nat.add_sub_cancel' h_sle
    -- §8 transports: the wide read, then the dst write
    obtain ⟨p2w, h_read2_tgt, h_psim2w⟩ :=
      sb_read_respects_PermSim h_spsim h_wf_t' h_srt h_snw h_read_src
    have h_w := h_step
    simp only [mirlite.writeResolvedPlace] at h_w
    split at h_w
    · simp at h_w
    · rename_i h_nb
      split at h_w
      · rename_i perms₃ h_useMut_src
        cases h_w
        have h_useMut_src' : MSB.useMut perms₂ s_mir.mem.addrStart (blockSize τ)
            s_mir.perms.NextTag = .ok perms₃ := by
          grind
        obtain ⟨dstReg2, baseD2, tagD2, h_piD2, h_entryD2, h_raD2, h_rtD2,
          h_nwD2, h_domD2⟩ := h_slbs dstLoc _ h_lookup_set
        have h_dr2 : dstReg2 = Register.R csPrefix.nextReg := by grind
        have h_baseD2 : baseD2 = s_mir.mem.addrStart := (h_id_a' _ _ h_raD2).symm
        rw [h_dr2, h_baseD2] at h_entryD2
        obtain ⟨p3w, h_useMut_tgt, h_psim3w⟩ :=
          sb_write_respects_PermSim h_psim2w h_wf_t' h_rtD2 h_nwD2 h_useMut_src'
        -- §9 the READ into the temporary, then the write
        have h_ts : obseq.typeSize (obseq.layoutToTyVal τ) = blockSize τ := by
          simp [blockSize]
        have h_code1 : compProg s_mid.pc
            = some (Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg)
                (Rhs.Load (obseq.layoutToTyVal τ) sOut.result.reg)) := by
          rw [h_spc]
          refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
          · rw [h_stmtRun]
            simp only [emit, List.length_cons, List.length_nil]
            omega
          · rw [h_stmtRun]
            rw [emit_code_lt_nextLabel _ _ (by
              simp only [emit, List.length_cons, List.length_nil]; omega)]
            have h := emit_code_at_new
              { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg + 1 }
              [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg) (Rhs.Load (obseq.layoutToTyVal τ) sOut.result.reg)]
              (k := 0) (by simp)
            simpa using h
        have h_code2 : compProg (s_mid.pc + 1)
            = some (Instr.RStore (obseq.layoutToTyVal τ) (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg)
                (Register.R csPrefix.nextReg)) := by
          rw [h_spc]
          refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
          · rw [h_stmtRun]
            simp only [emit, List.length_cons, List.length_nil]
            omega
          · rw [h_stmtRun]
            have h := emit_code_at_new
              (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg + 1 }
                [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg) (Rhs.Load (obseq.layoutToTyVal τ) sOut.result.reg)])
              [Instr.RStore (obseq.layoutToTyVal τ) (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg) (Register.R csPrefix.nextReg)]
              (k := 0) (by simp)
            simpa [emit] using h
        have h_read2t : MSB.read s_mid.perms
            (rs.allocBase + (rs.addr - rs.allocBase))
            (obseq.typeSize (obseq.layoutToTyVal τ)) tres = .ok p2w := by
          rw [h_ts, h_cancel]
          exact h_read2_tgt
        have h_run1 := runN_Assgn_Load_ptr_step compProg s_mid
          (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg) sOut.result.reg (obseq.layoutToTyVal τ) h_code1 h_sentry
          (by rw [h_ts]; grind) h_read2t
        rw [h_ts, h_cancel] at h_run1
        have h_regne : Register.R csPrefix.nextReg ≠ (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg) := by
          intro h_eq
          injection h_eq with h_eq'
          have h1 : csPrefix.nextReg + 1 ≤ (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg := by
            have := h_sregmono
            simp only [setPlaceInfo, emit] at this
            exact this
          omega
        have h_dentry2 : oseair.RegMap.lookup
            (oseair.RegMap.insert s_mid.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg)
              (obseq.layoutToTyVal τ, (oseair.readWordSeq s_mid.mem rs.addr (blockSize τ)))) (Register.R csPrefix.nextReg)
            = some (obseq.TyVal.PTy,
                [Val.Ptr s_mir.mem.addrStart 0 (blockSize τ) tagD2]) := by
          rw [RegMap.lookup_insert_ne _ h_regne]
          exact h_entryD2
        have h_useMut2t : MSB.useMut p2w (s_mir.mem.addrStart + 0)
            (oseair.readWordSeq s_mid.mem rs.addr (blockSize τ)).length tagD2 = .ok p3w := by
          rw [Nat.add_zero, oseair_readWordSeq_length]
          exact h_useMut_tgt
        have h_wtp : oseair.writeThroughPtr MSB
            { s_mid with
                perms := p2w,
                reg := oseair.RegMap.insert s_mid.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg)
                  (obseq.layoutToTyVal τ, (oseair.readWordSeq s_mid.mem rs.addr (blockSize τ))),
                pc := s_mid.pc + 1 }
            (Register.R csPrefix.nextReg) (oseair.readWordSeq s_mid.mem rs.addr (blockSize τ)) "RStore Invalid Regs"
            = oseair.Result.Ok
              { s_mid with
                  perms := p3w,
                  reg := oseair.RegMap.insert s_mid.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg)
                    (obseq.layoutToTyVal τ, (oseair.readWordSeq s_mid.mem rs.addr (blockSize τ))),
                  mem := oseair.writeWordSeq s_mid.mem s_mir.mem.addrStart (oseair.readWordSeq s_mid.mem rs.addr (blockSize τ)),
                  pc := s_mid.pc + 1 + 1 } := by
          simp only [oseair.writeThroughPtr, h_dentry2]
          rw [if_neg (by
            rw [oseair_readWordSeq_length, Nat.add_zero]
            exact Nat.not_lt.mpr (Nat.le_refl _))]
          simp only [h_useMut2t]
          rfl
        have h_run2 := runN_RStore_step compProg _ _
          (obseq.layoutToTyVal τ) (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg) (Register.R csPrefix.nextReg) _ _ h_code2
          (RegMap.lookup_insert_self _ _ _) h_dentry2 h_wtp
        have h_runA := (oseair_runN_add 1 n1 s_osea compProg _ h_run0').trans h_srun
        have h_runB := (oseair_runN_add (1 + n1) 1 s_osea compProg s_mid h_runA).trans
          h_run1
        have h_run := (oseair_runN_add (1 + n1 + 1) 1 s_osea compProg _ h_runB).trans
          h_run2
        -- §10 memory
        have h_rws1 : ∀ (a n : Nat),
            mirlite.readWordSeq s1.mem a n = mirlite.readWordSeq s_mir.mem a n :=
          fun a n => mirlite_readWordSeq_congr h_find1 n a
        have h_sms1 : SourceMemSim
            (ρa.extendBlock s_mir.mem.addrStart (blockSize τ))
            (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag) s1.mem s_mid.mem := by
          intro a v h_find
          rw [h_find1] at h_find
          rw [h_smem]
          exact SourceMemSim.rename_mono h_incr_a h_incr_t h_sms a v h_find
        have h_rel : ListRel (MemValSim
            (ρa.extendBlock s_mir.mem.addrStart (blockSize τ))
            (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag))
            (mirlite.readWordSeq s1.mem rs.addr (blockSize τ))
            (oseair.readWordSeq s_mid.mem rs.addr (blockSize τ)) :=
          readWordSeq_sim h_id_a' h_sms1 (blockSize τ) rs.addr
        have h_dom : ∀ k,
            k < (mirlite.readWordSeq s1.mem rs.addr (blockSize τ)).length →
            (ρa.extendBlock s_mir.mem.addrStart (blockSize τ))
              (s_mir.mem.addrStart + k) = some (s_mir.mem.addrStart + k) := by
          intro k hk
          exact h_ra_dom k (by rw [h_rws1] at hk; simpa using hk)
        have h_sms' := SourceMemSim.writeWordSeq_extend h_id_a' _ _ _ _ _ h_rel h_dom
          h_sms1
        -- §11 rebuild the invariant under both extended renames
        refine ⟨_, _, _, 1 + n1 + 1 + 1, h_incr_a, h_incr_t, h_run, ?_⟩
        refine ⟨CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix,
          ⟨prefixCompileState_succ (by rw [h_pc1]; exact h_csAt)
            (by rw [h_pc1]; exact h_stmt) h_stmtOut, ?_⟩, ?_, h_sms',
          h_psim3w, h_id_a', h_wf_t', ?_, ?_, ?_, ?_⟩
        · show s_mid.pc + 1 + 1 = _
          rw [h_spc, h_stmtRun]
          simp [emit]
        · have h_lbsT : LocalBindingSim
              (ρa.extendBlock s_mir.mem.addrStart (blockSize τ))
              (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag) s1.env
              { s_mid with
                  perms := p3w,
                  reg := oseair.RegMap.insert s_mid.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg)
                    (obseq.layoutToTyVal τ, (oseair.readWordSeq s_mid.mem rs.addr (blockSize τ))),
                  mem := oseair.writeWordSeq s_mid.mem s_mir.mem.addrStart (oseair.readWordSeq s_mid.mem rs.addr (blockSize τ)),
                  pc := s_mid.pc + 1 + 1 } (setPlaceInfo
            (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
              [Instr.Assgn (Register.R csPrefix.nextReg)
                (Rhs.Alloc (layoutToTyVal τ))])
            dstLoc.idx.1 (Register.R csPrefix.nextReg, τ)) :=
            LocalBindingSim.insert_fresh_reg h_slbs h_prb1 h_sregmono rfl
          intro τ' loc' binding' h_env'
          obtain ⟨reg', base', tag', h_pi', h_entry', h_ra', h_rt', h_nw', h_dom'⟩ :=
            h_lbsT loc' binding' h_env'
          refine ⟨reg', base', tag', ?_, h_entry', h_ra', h_rt', h_nw', h_dom'⟩
          rw [h_stmtRun, getPlaceInfo_emit, getPlaceInfo_emit, getPlaceInfo_setNextReg,
            h_gp]
          exact h_pi'
        · show TagRenameBounded _ perms₃.NextTag p3w.NextTag
          rw [sb_write_NextTag h_useMut_src', sb_read_NextTag h_read_src, h_snt1,
            sb_write_NextTag h_useMut_tgt, sb_read_NextTag h_read2_tgt]
          exact TagRenameBounded.mono h_tbd'
            (Nat.le_of_eq (congrArg AccessPerms.NextTag h_perms1.symm)) h_snt2
        · simp only [AllocLockstep, mirlite_writeWordSeq_addrStart,
            oseair_writeWordSeq_addrStart, h_smem, h_memstart1]
          show (oseair.allocate s_osea.mem (obseq.typeSize (layoutToTyVal τ))).2.addrStart
            = _
          simp only [oseair.allocate]
          rw [h_addr_eq, h_sz]
        · intro τ' loc' h_none
          have h_none1 : mirlite.Env.lookup s1.env loc' = none := h_none
          rw [← h_s1] at h_none1
          by_cases h_idx : loc'.idx = dstLoc.idx
          · exfalso
            simp only [mirlite.Env.lookup, mirlite.Env.set, h_idx, if_pos rfl]
              at h_none1
            exact absurd h_none1 (by simp)
          have h_idxv : loc'.idx.1 ≠ dstLoc.idx.1 := fun h => h_idx (Fin.ext h)
          have h_none0 : mirlite.Env.lookup s_mir.env loc' = none := by
            simpa only [mirlite.Env.lookup, mirlite.Env.set, if_neg h_idx]
              using h_none1
          rw [h_stmtRun, getPlaceInfo_emit, getPlaceInfo_emit, getPlaceInfo_setNextReg,
            h_gp, getPlaceInfo_setPlaceInfo_ne _ h_idxv]
          exact h_unmap loc' h_none0
        · intro idx reg'' τ'' h_look
          rw [h_stmtRun] at h_look ⊢
          rw [getPlaceInfo_emit, getPlaceInfo_emit, getPlaceInfo_setNextReg, h_gp]
            at h_look
          refine RegisterBelow.mono ?_ (h_prb1 _ _ _ h_look)
          simp only [emit]
          exact Nat.le_trans h_sregmono (Nat.le_succ _)
      · simp at h_w

/-- REGIME B for copy with a PROJ-TOPPED source at NONZERO offset,
    CLOSED 2026-09-03: `dst := copy B.f` with an UNBOUND destination.
    The root `Alloc` runs first and the mother lemma is called at the
    post-allocation states under both extended renames (regime B's
    prefix); the ending is the projection's `Borrow(Shared); Memcpy;
    Die`, with the destination's `useMut` sliding between BRIDGE 1S's
    phases by the overlap guard's disjointness. -/
theorem copy_fresh_projchain_offset_simulation
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {τ σb : LayoutTy}
    {dstLoc : Local Γ τ} {B : Place Γ σb} {path : PathTo σb τ}
    (compProg : oseair.Prog)
    (h_chain : PtrChain B)
    (h_off : pathOffset path ≠ 0)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    {stmt0 : Stmt Γ}
    (h_stmt : prog.get? s_mir.pc = some stmt0)
    (h_run0 : ∀ cs, CheckedCompilerM.run (compileStmtChecked stmt0) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.local dstLoc) (.copy (.proj B path)))) cs)
    (h_val0 : ∀ cs so, CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.local dstLoc) (.copy (.proj B path)))) cs
        = Except.ok so →
      ∃ so', CheckedCompilerM.value (compileStmtChecked stmt0) cs
        = Except.ok so')
    (h_envD : mirlite.Env.lookup s_mir.env dstLoc = none)
    (h_step : mirlite.stepStmt MSB s_mir
      (.assign (.local dstLoc) (.copy (.proj B path))) = .ok s_mir') :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' := by
  obtain ⟨csPrefix, ⟨h_csAt, h_pc⟩, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_tbd,
    h_alloc, h_unmap, h_prb⟩ := h_inv
  have h_pi_none : getPlaceInfo csPrefix dstLoc.idx.1 = none := h_unmap dstLoc h_envD
  -- §1 the source allocates the destination root before reading
  simp only [mirlite.stepStmt, mirlite.doAssign] at h_step
  cases h_prep : mirlite.preparePlaceAssign MSB s_mir (Place.local dstLoc) with
  | err msg => rw [h_prep] at h_step; simp at h_step
  | ok s1 =>
  rw [h_prep] at h_step
  simp only [mirlite.preparePlaceAssign, mirlite.resolvePlace?, h_envD,
    mirlite.allocateRoot, mirlite.allocateBase, mirlite.allocate] at h_prep
  cases h_own_src : MSB.own s_mir.perms s_mir.mem.addrStart (blockSize τ) with
  | error e => rw [h_own_src] at h_prep; simp at h_prep
  | ok pr =>
  obtain ⟨permsOwned, tagS⟩ := pr
  rw [h_own_src] at h_prep
  injection h_prep with h_s1
  -- §2 the two ρ extensions and the post-allocation source state
  obtain ⟨tgtPerms, h_own_tgt, h_tagS_eq, h_incr_t, h_wf_t', h_tbd', h_psim'⟩ :=
    sb_own_respects_PermSim h_psim h_wf_t h_tbd h_own_src
  subst h_tagS_eq
  have h_addr_eq : s_osea.mem.addrStart = s_mir.mem.addrStart := h_alloc
  have h_incr_a :=
    AddrRenameIncr.extendBlock h_id_a s_mir.mem.addrStart (blockSize τ)
  have h_id_a' :=
    IdentityOnDomain.extendBlock h_id_a s_mir.mem.addrStart (blockSize τ)
  have h_ra_dom : ∀ k, k < blockSize τ →
      (ρa.extendBlock s_mir.mem.addrStart (blockSize τ))
        (s_mir.mem.addrStart + k) = some (s_mir.mem.addrStart + k) :=
    fun _ hk => AddrRenameMap.extendBlock_mem hk
  have h_ra_base : (ρa.extendBlock s_mir.mem.addrStart (blockSize τ))
      s_mir.mem.addrStart = some s_mir.mem.addrStart :=
    AddrRenameMap.extendBlock_base _ _ _
  have h_rt_new : (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag)
      s_mir.perms.NextTag = some s_osea.perms.NextTag :=
    TagRenameMap.extend_self _ _ _
  have h0 : wildcardTag < s_mir.perms.NextTag := (h_tbd _ _ h_wf_t.2).1
  have h_nw : (s_mir.perms.NextTag == wildcardTag) = false := by grind
  -- the post-allocation source state stays ABSTRACT (`s1`); everything
  -- needed about it comes from the allocation equation
  have h_lookup_set : mirlite.Env.lookup s1.env dstLoc
      = some { addr := s_mir.mem.addrStart, tag := s_mir.perms.NextTag } := by
    rw [← h_s1]
    simp [mirlite.Env.lookup, mirlite.Env.set]
  have h_perms1 : s1.perms = permsOwned := by rw [← h_s1]
  have h_pc1 : s1.pc = s_mir.pc := by rw [← h_s1]
  have h_memstart1 : s1.mem.addrStart = s_mir.mem.addrStart + blockSize τ := by
    rw [← h_s1]
  have h_find1 : ∀ a, mirlite.Mem.find? s1.mem a = mirlite.Mem.find? s_mir.mem a := by
    intro a
    rw [← h_s1]
    rfl
  -- §3 the source read, kept OPAQUE at the chain
  simp only [mirlite.evalRExpr] at h_step
  have h_np := h_chain.not_proj
  cases h_sres : mirlite.resolvePlaceAcc MSB s1 B with
  | error e =>
      rw [resolvePlaceAcc_proj_base_err h_sres] at h_step
      simp at h_step
  | ok pr2 =>
  obtain ⟨rs, permsP'⟩ := pr2
  rw [resolvePlaceAcc_proj_base_ok h_sres] at h_step
  simp only [gt_iff_lt] at h_step
  by_cases h_fitS : rs.allocBase + rs.allocSize
      < rs.addr + PathTo.offset path + blockSize τ
  · rw [if_pos h_fitS] at h_step
    simp at h_step
  · rw [if_neg h_fitS] at h_step
    cases h_read_src : MSB.read permsP' (rs.addr + PathTo.offset path)
        (blockSize τ) rs.tag with
    | error e => rw [h_read_src] at h_step; simp at h_step
    | ok perms₂ =>
    rw [h_read_src] at h_step
    simp only [mirlite.resolvePlaceAcc, h_lookup_set] at h_step
    -- §4 the compiled prefix: the root `Alloc` and the post-alloc state
    have h_erun : CompilerM.run (ensureLocalRegE dstLoc) csPrefix
        = setPlaceInfo
            (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
              [Instr.Assgn (Register.R csPrefix.nextReg)
                (Rhs.Alloc (layoutToTyVal τ))])
            dstLoc.idx.1 (Register.R csPrefix.nextReg, τ) :=
      (ensureLocalRegE_fresh (loc := dstLoc) h_pi_none).1
    have h_pi_new : getPlaceInfo
        (setPlaceInfo
          (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
            [Instr.Assgn (Register.R csPrefix.nextReg)
              (Rhs.Alloc (layoutToTyVal τ))])
          dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))
        dstLoc.idx.1 = some (Register.R csPrefix.nextReg, τ) :=
      getPlaceInfo_setPlaceInfo_self _ _ _
    have h_sz : obseq.typeSize (layoutToTyVal τ) = blockSize τ :=
      obseq.typeSize_layoutToTyVal _
    have h_own_tgt' : MSB.own s_osea.perms s_osea.mem.addrStart
        (obseq.typeSize (layoutToTyVal τ))
        = .ok (tgtPerms, s_osea.perms.NextTag) := by
      rw [h_sz, h_addr_eq]
      exact h_own_tgt
    -- the post-Alloc target state
    have h_prb1 : PlaceRegMapBound
        (setPlaceInfo
          (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
            [Instr.Assgn (Register.R csPrefix.nextReg)
              (Rhs.Alloc (layoutToTyVal τ))])
          dstLoc.idx.1 (Register.R csPrefix.nextReg, τ)) := by
      intro idx reg τ'' h_look
      by_cases h_i : idx = dstLoc.idx.1
      · subst h_i
        rw [getPlaceInfo_setPlaceInfo_self] at h_look
        injection h_look with h_look'
        have : reg = Register.R csPrefix.nextReg := (congrArg Prod.fst h_look').symm
        subst this
        show csPrefix.nextReg < _
        simp only [emit, setPlaceInfo]
        grind
      · rw [getPlaceInfo_setPlaceInfo_ne _ h_i] at h_look
        refine RegisterBelow.mono ?_ (h_prb _ _ _ h_look)
        simp only [emit, setPlaceInfo]
        grind
    have h_lbs1 : LocalBindingSim
        (ρa.extendBlock s_mir.mem.addrStart (blockSize τ))
        (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag)
        s1.env
        { s_osea with
            mem := (oseair.allocate s_osea.mem
              (obseq.typeSize (layoutToTyVal τ))).2,
            perms := tgtPerms,
            reg := oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
              (obseq.TyVal.PTy, [Val.Ptr s_osea.mem.addrStart 0
                (obseq.typeSize (layoutToTyVal τ)) s_osea.perms.NextTag]),
            pc := s_osea.pc + 1 }
        (setPlaceInfo
          (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
            [Instr.Assgn (Register.R csPrefix.nextReg)
              (Rhs.Alloc (layoutToTyVal τ))])
          dstLoc.idx.1 (Register.R csPrefix.nextReg, τ)) := by
      rw [← h_s1]
      intro τ' loc' binding' h_env'
      by_cases h_idx : loc'.idx = dstLoc.idx
      · have h_ty : τ' = τ := by
          rw [← loc'.hTy, h_idx, dstLoc.hTy]
        subst h_ty
        have h_b : binding' = { addr := s_mir.mem.addrStart,
                                tag := s_mir.perms.NextTag } := by
          grind [mirlite.Env.lookup, mirlite.Env.set]
        subst h_b
        refine ⟨Register.R csPrefix.nextReg, s_mir.mem.addrStart,
          s_osea.perms.NextTag, ?_, ?_, ?_, h_rt_new, h_nw, ?_⟩
        · rw [show loc'.idx.1 = dstLoc.idx.1 from congrArg Fin.val h_idx]
          exact h_pi_new
        · show oseair.RegMap.lookup _ _ = _
          rw [← h_addr_eq, ← h_sz]
          exact RegMap.lookup_insert_self _ _ _
        · exact h_ra_base
        · intro k hk
          exact ⟨s_mir.mem.addrStart + k, h_ra_dom k hk⟩
      · have h_env'' : mirlite.Env.lookup s_mir.env loc' = some binding' := by
          simpa only [mirlite.Env.lookup, mirlite.Env.set, if_neg h_idx]
            using h_env'
        obtain ⟨reg', base', tag', h_pi', h_entry', h_ra', h_rt', h_nw', h_dom'⟩ :=
          h_lbs loc' binding' h_env''
        have h_idxv : loc'.idx.1 ≠ dstLoc.idx.1 := by grind [Fin.ext]
        have h_regne : reg' ≠ Register.R csPrefix.nextReg := by
          cases reg' with
          | R n =>
              have h_lt := h_prb _ _ _ h_pi'
              grind [RegisterBelow]
        refine ⟨reg', base', tag', ?_, ?_, h_incr_a _ _ h_ra',
          h_incr_t _ _ h_rt', h_nw',
          fun k hk => ⟨(h_dom' k hk).choose,
            h_incr_a _ _ (h_dom' k hk).choose_spec⟩⟩
        · rw [getPlaceInfo_setPlaceInfo_ne _ h_idxv]
          exact h_pi'
        · show oseair.RegMap.lookup _ _ = _
          rw [RegMap.lookup_insert_ne _ h_regne]
          exact h_entry'
    -- §5 the statement value and code inclusion for the source lowering
    have h_mappedP : PlaceInputsMapped
        (setPlaceInfo
          (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
            [Instr.Assgn (Register.R csPrefix.nextReg)
              (Rhs.Alloc (layoutToTyVal τ))])
          dstLoc.idx.1 (Register.R csPrefix.nextReg, τ)) (Place.proj B path) :=
      placeInputsMapped_of_localBindingSim_resolvePlace h_lbs1
        (resolvePlace?_of_resolveAcc
          (resolvePlaceAcc_proj_base_ok (path := path) h_sres))
    have h_mappedB : PlaceInputsMapped
        (setPlaceInfo
          (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
            [Instr.Assgn (Register.R csPrefix.nextReg)
              (Rhs.Alloc (layoutToTyVal τ))])
          dstLoc.idx.1 (Register.R csPrefix.nextReg, τ)) B := h_mappedP
    obtain ⟨sOut0, h_sval0⟩ := placeToRegChecked_ok_of_placeInputsMapped
      (cs := setPlaceInfo
          (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
            [Instr.Assgn (Register.R csPrefix.nextReg)
              (Rhs.Alloc (layoutToTyVal τ))])
          dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))
      (kind := RefKind.Shared) h_mappedB
    obtain ⟨stmtOutC, h_stmtOutC⟩ :=
      compileStmt_copy_fresh_projchain_offset_value h_np h_off h_pi_none h_sval0
    obtain ⟨stmtOut, h_stmtOut⟩ := h_val0 csPrefix stmtOutC h_stmtOutC
    have h_incrS : StateIncr
        (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
          (setPlaceInfo
            (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
              [Instr.Assgn (Register.R csPrefix.nextReg)
                (Rhs.Alloc (layoutToTyVal τ))])
            dstLoc.idx.1 (Register.R csPrefix.nextReg, τ)))
        (CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix) := by
      rw [h_run0]
      simp only [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked,
        placeToRegChecked_proj_root_eq (Γ := Γ) (kind := RefKind.Shared)
          (base := B) path h_np,
        CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
        CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
        CheckedCompilerM.run_pure, CheckedCompilerM.value_pure, h_erun, h_sval0,
        dif_neg h_off]
      simp only [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM]
      exact StateIncr.trans (freshReg_state_incr _)
        (StateIncr.trans (emit_state_incr _ _)
          (StateIncr.trans (freshReg_state_incr _)
            (StateIncr.trans (emit_state_incr _ _)
              (StateIncr.trans (emit_state_incr _ _) (emit_state_incr _ _)))))
    have h_instS : ∀ q' instr,
        q' < (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
          (setPlaceInfo
            (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
              [Instr.Assgn (Register.R csPrefix.nextReg)
                (Rhs.Alloc (layoutToTyVal τ))])
            dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextLabel →
        (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
          (setPlaceInfo
            (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
              [Instr.Assgn (Register.R csPrefix.nextReg)
                (Rhs.Alloc (layoutToTyVal τ))])
            dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).code q' = some instr →
        compProg q' = some instr := by
      intro q' instr h_lt h_code
      refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
      · exact Nat.lt_of_lt_of_le h_lt h_incrS.nextLabel_le
      · rw [h_incrS.code_eq q' h_lt]
        exact h_code
    -- §6 execute the `Alloc`
    have h_code0 : compProg s_osea.pc
        = some (Instr.Assgn (Register.R csPrefix.nextReg)
            (Rhs.Alloc (layoutToTyVal τ))) := by
      rw [h_pc]
      refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
      · refine Nat.lt_of_lt_of_le ?_ h_incrS.nextLabel_le
        refine Nat.lt_of_lt_of_le ?_
          (CheckedCompilerM.incr (placeToRegChecked RefKind.Shared B) _).nextLabel_le
        simp only [emit, setPlaceInfo, List.length_cons, List.length_nil]
        omega
      · rw [h_incrS.code_eq _ (by
          refine Nat.lt_of_lt_of_le ?_
            (CheckedCompilerM.incr (placeToRegChecked RefKind.Shared B) _).nextLabel_le
          simp only [emit, setPlaceInfo, List.length_cons, List.length_nil]
          omega)]
        rw [(CheckedCompilerM.incr (placeToRegChecked RefKind.Shared B)
          (setPlaceInfo
            (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
              [Instr.Assgn (Register.R csPrefix.nextReg)
                (Rhs.Alloc (layoutToTyVal τ))])
            dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).code_eq _ (by
          simp only [emit, setPlaceInfo, List.length_cons, List.length_nil]
          omega)]
        show (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } _).code _ = _
        have h := emit_code_at_new { csPrefix with nextReg := csPrefix.nextReg + 1 }
          [Instr.Assgn (Register.R csPrefix.nextReg)
            (Rhs.Alloc (layoutToTyVal τ))] (k := 0) (by simp)
        simpa using h
    have h_run0' := runN_Assgn_Alloc_step compProg s_osea
      (Register.R csPrefix.nextReg) (layoutToTyVal τ) h_code0 h_own_tgt'
    -- §7 the mother lemma on the source, at the POST-allocation states
    obtain ⟨sOut, n1, s_mid, tres, h_sval, h_sclean, h_srun, h_spc, h_smem,
      h_spsim, h_snt1, h_snt2, h_slbs, h_sentry, h_srt, h_snw, h_sle, h_srange,
      h_sbelow, h_sprm, h_sregmono, h_slabmono, -, -⟩ :=
      ptrChain_lowering_sim h_id_a' h_wf_t' h_chain RefKind.Shared
        (setPlaceInfo
          (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
            [Instr.Assgn (Register.R csPrefix.nextReg)
              (Rhs.Alloc (layoutToTyVal τ))])
          dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))
        { s_osea with
            mem := (oseair.allocate s_osea.mem
              (obseq.typeSize (layoutToTyVal τ))).2,
            perms := tgtPerms,
            reg := oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
              (obseq.TyVal.PTy, [Val.Ptr s_osea.mem.addrStart 0
                (obseq.typeSize (layoutToTyVal τ)) s_osea.perms.NextTag]),
            pc := s_osea.pc + 1 }
        rs permsP' h_sres (by rw [h_perms1]; exact h_tbd') h_lbs1 h_prb1
        (by
          intro a v h_find
          rw [h_find1] at h_find
          exact SourceMemSim.rename_mono h_incr_a h_incr_t h_sms a v h_find)
        (by rw [h_perms1]; exact h_psim')
        (by
          show s_osea.pc + 1 = _
          rw [h_pc]
          simp only [emit, setPlaceInfo, List.length_cons, List.length_nil])
        h_instS
    have h_stmtRun := (h_run0 csPrefix).trans
      (compileStmt_copy_fresh_projchain_offset_run h_np h_off h_pi_none h_sval h_sclean)
    have h_gp : ∀ i, getPlaceInfo (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
            (setPlaceInfo
              (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                [Instr.Assgn (Register.R csPrefix.nextReg)
                  (Rhs.Alloc (layoutToTyVal τ))])
              dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))) i
        = getPlaceInfo (setPlaceInfo
              (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                [Instr.Assgn (Register.R csPrefix.nextReg)
                  (Rhs.Alloc (layoutToTyVal τ))])
              dstLoc.idx.1 (Register.R csPrefix.nextReg, τ)) i :=
      fun i => by simp only [getPlaceInfo, h_sprm]
    have h_cancel : rs.allocBase + (rs.addr - rs.allocBase) = rs.addr :=
      Nat.add_sub_cancel' h_sle
    -- §8 transports: the projected read, then the dst write
    obtain ⟨p2, h_read_tgt, h_psim2⟩ :=
      sb_read_respects_PermSim h_spsim h_wf_t' h_srt h_snw h_read_src
    have h_w := h_step
    simp only [mirlite.writeResolvedPlace] at h_w
    split at h_w
    · simp at h_w
    · rename_i h_nb
      split at h_w
      · rename_i perms₃ h_useMut_src
        cases h_w
        have h_useMut_src' : MSB.useMut perms₂ s_mir.mem.addrStart (blockSize τ)
            s_mir.perms.NextTag = .ok perms₃ := by
          grind
        obtain ⟨dstReg2, baseD2, tagD2, h_piD2, h_entryD2, h_raD2, h_rtD2,
          h_nwD2, h_domD2⟩ := h_slbs dstLoc _ h_lookup_set
        have h_dr2 : dstReg2 = Register.R csPrefix.nextReg := by grind
        have h_baseD2 : baseD2 = s_mir.mem.addrStart := (h_id_a' _ _ h_raD2).symm
        rw [h_dr2, h_baseD2] at h_entryD2
        obtain ⟨p3, h_useMut_tgt, h_psim3⟩ :=
          sb_write_respects_PermSim h_psim2 h_wf_t' h_rtD2 h_nwD2 h_useMut_src'
        -- §9 BRIDGE 1S over the mother's register
        obtain ⟨q1, h_ref_tgt⟩ := sb_ref_Shared_ok_of_sb_read_ok h_read_tgt
        have h_tbd2 : TagRenameBounded
            (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag)
            permsP'.NextTag s_mid.perms.NextTag := by
          rw [h_snt1, h_perms1]
          exact TagRenameBounded.mono h_tbd' (Nat.le_refl _) h_snt2
        have h_unprot := freshTag_not_protected h_spsim h_tbd2
        have h0' : wildcardTag < s_mid.perms.NextTag := (h_tbd2 _ _ h_wf_t'.2).2
        have h_ntw : (s_mid.perms.NextTag == wildcardTag) = false := by grind
        obtain ⟨q2, q3, qAcc', h_rd1, h_die1, h_rd2, h_sm, h_exq, h_pfq, h_ntle⟩ :=
          sb_ref_read_die_cancels h_ntw h_unprot h_ref_tgt
        have h_qAcc : qAcc' = p2 := by grind
        subst h_qAcc
        -- §6 BRIDGE 1S: the temporary retires BEFORE the write, so the
        -- keystone's Borrow/read/die is contiguous and the destination
        -- write simply follows the parent read (no commutation needed)
        have h_psim2q : PermSim (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag) perms₂ q3 := by
          obtain ⟨hs, hp, he, hn⟩ := h_psim2
          exact ⟨by rw [h_sm]; exact hs, by rw [h_pfq]; exact hp,
                 by rw [h_exq]; exact he, Nat.le_trans hn h_ntle⟩
        obtain ⟨r', h_useMut_tgt', h_psim_final⟩ :=
          sb_write_respects_PermSim h_psim2q h_wf_t' h_rtD2 h_nwD2 h_useMut_src'
        -- §7 the four instructions after the base lowering
        have h_ts : obseq.typeSize (obseq.layoutToTyVal τ) = blockSize τ := by
          simp [blockSize]
        have h_code1 : compProg s_mid.pc
            = some (Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg)
                (borrowRhs RefKind.Shared (blockSize τ) sOut.result.reg
                  (pathOffset path))) := by
          rw [h_spc]
          refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
          · rw [h_stmtRun]
            simp only [emit, List.length_cons, List.length_nil]
            omega
          · rw [h_stmtRun]
            rw [emit_code_lt_nextLabel _ _ (by
              simp only [emit, List.length_cons, List.length_nil]; omega)]
            rw [emit_code_lt_nextLabel _ _ (by
              simp only [emit, List.length_cons, List.length_nil]; omega)]
            have h := emit_code_at_new
              { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg + 1 }
              [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg)
                (borrowRhs RefKind.Shared (blockSize τ) sOut.result.reg
                  (pathOffset path))]
              (k := 0) (by simp)
            simpa using h
        have h_code2 : compProg (s_mid.pc + 1)
            = some (Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg + 1))
                (Rhs.Load (obseq.layoutToTyVal τ) (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg))) := by
          rw [h_spc]
          refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
          · rw [h_stmtRun]
            simp only [emit, List.length_cons, List.length_nil]
            omega
          · rw [h_stmtRun]
            rw [emit_code_lt_nextLabel _ _ (by
              simp only [emit, List.length_cons, List.length_nil]; omega)]
            have h := emit_code_at_new
              { (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg + 1 }
                  [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg)
                    (borrowRhs RefKind.Shared (blockSize τ) sOut.result.reg
                      (pathOffset path))]) with
                  nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg + 1 + 1 }
              [Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg + 1)) (Rhs.Load (obseq.layoutToTyVal τ) (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg)),
               Instr.Die (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg) (blockSize τ)]
              (k := 0) (by simp)
            simpa [emit] using h
        have h_code3 : compProg (s_mid.pc + 1 + 1)
            = some (Instr.Die (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg) (blockSize τ)) := by
          rw [h_spc]
          refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
          · rw [h_stmtRun]
            simp only [emit, List.length_cons, List.length_nil]
            omega
          · rw [h_stmtRun]
            rw [emit_code_lt_nextLabel _ _ (by
              simp only [emit, List.length_cons, List.length_nil]; omega)]
            have h := emit_code_at_new
              { (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg + 1 }
                  [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg)
                    (borrowRhs RefKind.Shared (blockSize τ) sOut.result.reg
                      (pathOffset path))]) with
                  nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg + 1 + 1 }
              [Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg + 1)) (Rhs.Load (obseq.layoutToTyVal τ) (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg)),
               Instr.Die (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg) (blockSize τ)]
              (k := 1) (by simp)
            simpa [emit] using h
        have h_code4 : compProg (s_mid.pc + 1 + 1 + 1)
            = some (Instr.RStore (obseq.layoutToTyVal τ) (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg + 1)) (Register.R csPrefix.nextReg)) := by
          rw [h_spc]
          refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
          · rw [h_stmtRun]
            simp only [emit, List.length_cons, List.length_nil]
            omega
          · rw [h_stmtRun]
            have h := emit_code_at_new
              (emit { (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg + 1 }
                  [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg)
                    (borrowRhs RefKind.Shared (blockSize τ) sOut.result.reg
                      (pathOffset path))]) with
                  nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg + 1 + 1 }
                [Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg + 1)) (Rhs.Load (obseq.layoutToTyVal τ) (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg)),
                 Instr.Die (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg) (blockSize τ)])
              [Instr.RStore (obseq.layoutToTyVal τ) (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg + 1)) (Register.R csPrefix.nextReg)]
              (k := 0) (by simp)
            simpa [emit] using h
        -- §8 execute: Borrow, Load, Die, RStore
        have h_le1 : rs.allocBase + (rs.addr - rs.allocBase) + pathOffset path
            + blockSize τ ≤ rs.allocBase + rs.allocSize := by
          rw [h_cancel]
          have := Nat.not_lt.mp h_fitS
          grind
        have h_ref_tgt' : MSB.ref s_mid.perms
            (rs.allocBase + (rs.addr - rs.allocBase) + pathOffset path)
            (blockSize τ) tres RefKind.Shared false []
            = .ok (q1, s_mid.perms.NextTag) := by
          rw [h_cancel]
          exact h_ref_tgt
        have h_run1 := runN_Assgn_Borrow_step compProg s_mid
          (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg) sOut.result.reg RefKind.Shared false []
          (blockSize τ) (pathOffset path)
          h_code1 h_sentry h_le1 h_ref_tgt'
        have h_bentry : PtrRegisterEntry
            (oseair.RegMap.insert s_mid.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg) (obseq.TyVal.PTy, [Val.Ptr rs.allocBase
                (rs.addr - rs.allocBase + pathOffset path)
                rs.allocSize s_mid.perms.NextTag]))
            (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg) rs.allocBase (rs.addr - rs.allocBase + pathOffset path)
            rs.allocSize s_mid.perms.NextTag :=
          RegMap.lookup_insert_self _ _ _
        have h_read2 : MSB.read q1
            (rs.allocBase + (rs.addr - rs.allocBase + pathOffset path))
            (obseq.typeSize (obseq.layoutToTyVal τ)) s_mid.perms.NextTag
            = .ok q2 := by
          rw [h_ts, ← Nat.add_assoc, h_cancel]
          exact h_rd1
        have h_run2 := runN_Assgn_Load_ptr_step compProg
          { s_mid with
              perms := q1,
              reg := oseair.RegMap.insert s_mid.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg) (obseq.TyVal.PTy, [Val.Ptr rs.allocBase
                (rs.addr - rs.allocBase + pathOffset path)
                rs.allocSize s_mid.perms.NextTag]),
              pc := s_mid.pc + 1 }
          (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg + 1)) (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg) (obseq.layoutToTyVal τ) h_code2 h_bentry
          (by rw [h_ts]; grind) h_read2
        rw [h_ts, ← Nat.add_assoc, h_cancel] at h_run2
        -- the borrow register survives the value register's insert
        have h_regbv : (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg) ≠ (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg + 1)) := by
          intro h_eq
          injection h_eq with h_eq'
          omega
        have h_bentry2 : oseair.RegMap.lookup
            (oseair.RegMap.insert
              (oseair.RegMap.insert s_mid.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg) (obseq.TyVal.PTy, [Val.Ptr rs.allocBase
                (rs.addr - rs.allocBase + pathOffset path)
                rs.allocSize s_mid.perms.NextTag])) (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg + 1))
              (obseq.layoutToTyVal τ, (oseair.readWordSeq s_mid.mem (rs.addr + pathOffset path) (blockSize τ)))) (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg)
            = some (obseq.TyVal.PTy, [Val.Ptr rs.allocBase
                (rs.addr - rs.allocBase + pathOffset path)
                rs.allocSize s_mid.perms.NextTag]) := by
          rw [RegMap.lookup_insert_ne _ h_regbv]
          exact h_bentry
        have h_die1' : MSB.die q2
            (rs.allocBase + (rs.addr - rs.allocBase + pathOffset path))
            (blockSize τ) s_mid.perms.NextTag = .ok q3 := by
          rw [← Nat.add_assoc, h_cancel]
          exact h_die1
        have h_run3 := runN_Die_step compProg
          { s_mid with
              perms := q2,
              reg := oseair.RegMap.insert
                (oseair.RegMap.insert s_mid.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg) (obseq.TyVal.PTy, [Val.Ptr rs.allocBase
                (rs.addr - rs.allocBase + pathOffset path)
                rs.allocSize s_mid.perms.NextTag])) (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg + 1))
                (obseq.layoutToTyVal τ, (oseair.readWordSeq s_mid.mem (rs.addr + pathOffset path) (blockSize τ))),
              pc := s_mid.pc + 1 + 1 }
          (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg) (blockSize τ) h_code3 h_bentry2 h_die1'
        -- the destination register survives both inserts
        have h_regne : (Register.R csPrefix.nextReg) ≠ (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg + 1)) := by
          intro h_eq
          injection h_eq with h_eq'
          have h1 : csPrefix.nextReg + 1 ≤ (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg := by
            have := h_sregmono
            simp only [setPlaceInfo, emit] at this
            exact this
          omega
        have h_regne2 : (Register.R csPrefix.nextReg) ≠ (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg) := by
          intro h_eq
          injection h_eq with h_eq'
          have h1 : csPrefix.nextReg + 1 ≤ (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg := by
            have := h_sregmono
            simp only [setPlaceInfo, emit] at this
            exact this
          omega
        have h_dentry3 : oseair.RegMap.lookup
            (oseair.RegMap.insert
              (oseair.RegMap.insert s_mid.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg) (obseq.TyVal.PTy, [Val.Ptr rs.allocBase
                (rs.addr - rs.allocBase + pathOffset path)
                rs.allocSize s_mid.perms.NextTag])) (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg + 1))
              (obseq.layoutToTyVal τ, (oseair.readWordSeq s_mid.mem (rs.addr + pathOffset path) (blockSize τ)))) (Register.R csPrefix.nextReg)
            = some (obseq.TyVal.PTy, [Val.Ptr s_mir.mem.addrStart 0 (blockSize τ) tagD2]) := by
          rw [RegMap.lookup_insert_ne _ h_regne, RegMap.lookup_insert_ne _ h_regne2]
          exact h_entryD2
        have h_useMut3 : MSB.useMut q3 (s_mir.mem.addrStart + 0) (oseair.readWordSeq s_mid.mem (rs.addr + pathOffset path) (blockSize τ)).length tagD2
            = .ok r' := by
          rw [Nat.add_zero, oseair_readWordSeq_length]
          exact h_useMut_tgt'
        have h_wtp : oseair.writeThroughPtr MSB
            { s_mid with
                perms := q3,
                reg := oseair.RegMap.insert
                  (oseair.RegMap.insert s_mid.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg) (obseq.TyVal.PTy, [Val.Ptr rs.allocBase
                (rs.addr - rs.allocBase + pathOffset path)
                rs.allocSize s_mid.perms.NextTag])) (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg + 1))
                  (obseq.layoutToTyVal τ, (oseair.readWordSeq s_mid.mem (rs.addr + pathOffset path) (blockSize τ))),
                pc := s_mid.pc + 1 + 1 + 1 }
            (Register.R csPrefix.nextReg) (oseair.readWordSeq s_mid.mem (rs.addr + pathOffset path) (blockSize τ)) "RStore Invalid Regs"
            = oseair.Result.Ok
              { s_mid with
                  perms := r',
                  reg := oseair.RegMap.insert
                    (oseair.RegMap.insert s_mid.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg) (obseq.TyVal.PTy, [Val.Ptr rs.allocBase
                (rs.addr - rs.allocBase + pathOffset path)
                rs.allocSize s_mid.perms.NextTag])) (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg + 1))
                    (obseq.layoutToTyVal τ, (oseair.readWordSeq s_mid.mem (rs.addr + pathOffset path) (blockSize τ))),
                  mem := oseair.writeWordSeq s_mid.mem s_mir.mem.addrStart (oseair.readWordSeq s_mid.mem (rs.addr + pathOffset path) (blockSize τ)),
                  pc := s_mid.pc + 1 + 1 + 1 + 1 } := by
          simp only [oseair.writeThroughPtr, h_dentry3]
          rw [if_neg (by
            rw [oseair_readWordSeq_length, Nat.add_zero]
            exact Nat.not_lt.mpr (Nat.le_refl _))]
          simp only [h_useMut3]
          rfl
        have h_run4 := runN_RStore_step compProg _ _
          (obseq.layoutToTyVal τ) (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg + 1)) (Register.R csPrefix.nextReg) _ _ h_code4
          (RegMap.lookup_insert_self _ _ _) h_dentry3 h_wtp
        have h_run0A := (oseair_runN_add 1 n1 s_osea compProg _ h_run0').trans h_srun
        have h_runA := (oseair_runN_add (1 + n1) 1 s_osea compProg s_mid h_run0A).trans h_run1
        have h_runB := (oseair_runN_add (1 + n1 + 1) 1 s_osea compProg _ h_runA).trans h_run2
        have h_runC := (oseair_runN_add (1 + n1 + 1 + 1) 1 s_osea compProg _ h_runB).trans h_run3
        have h_run := (oseair_runN_add (1 + n1 + 1 + 1 + 1) 1 s_osea compProg _ h_runC).trans h_run4
        -- §9 memory
        have h_rws1 : ∀ (a n : Nat),
            mirlite.readWordSeq s1.mem a n = mirlite.readWordSeq s_mir.mem a n :=
          fun a n => mirlite_readWordSeq_congr h_find1 n a
        have h_sms1 : SourceMemSim
            (ρa.extendBlock s_mir.mem.addrStart (blockSize τ))
            (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag) s1.mem s_mid.mem := by
          intro a v h_find
          rw [h_find1] at h_find
          rw [h_smem]
          exact SourceMemSim.rename_mono h_incr_a h_incr_t h_sms a v h_find
        have h_rel : ListRel (MemValSim
            (ρa.extendBlock s_mir.mem.addrStart (blockSize τ))
            (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag))
            (mirlite.readWordSeq s1.mem (rs.addr + pathOffset path) (blockSize τ))
            (oseair.readWordSeq s_mid.mem (rs.addr + pathOffset path) (blockSize τ)) :=
          readWordSeq_sim h_id_a' h_sms1 (blockSize τ) (rs.addr + pathOffset path)
        have h_dom : ∀ k,
            k < (mirlite.readWordSeq s1.mem (rs.addr + pathOffset path)
              (blockSize τ)).length →
            (ρa.extendBlock s_mir.mem.addrStart (blockSize τ))
              (s_mir.mem.addrStart + k) = some (s_mir.mem.addrStart + k) := by
          intro k hk
          exact h_ra_dom k (by rw [h_rws1] at hk; simpa using hk)
        have h_sms' := SourceMemSim.writeWordSeq_extend h_id_a' _ _ _ _ _ h_rel h_dom
          h_sms1
        -- §10 rebuild the invariant
        refine ⟨_, _, _, 1 + n1 + 1 + 1 + 1 + 1, h_incr_a, h_incr_t, h_run, ?_⟩
        refine ⟨CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix,
          ⟨prefixCompileState_succ (by rw [h_pc1]; exact h_csAt)
            (by rw [h_pc1]; exact h_stmt) h_stmtOut, ?_⟩, ?_, h_sms',
          h_psim_final, h_id_a', h_wf_t', ?_, ?_, ?_, ?_⟩
        · show s_mid.pc + 1 + 1 + 1 + 1 = _
          rw [h_spc, h_stmtRun]
          simp [emit]
        · have h_lbs1 : LocalBindingSim (ρa.extendBlock s_mir.mem.addrStart (blockSize τ)) (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag) s1.env
              { s_mid with
                  perms := q1,
                  reg := oseair.RegMap.insert s_mid.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg) (obseq.TyVal.PTy, [Val.Ptr rs.allocBase
                (rs.addr - rs.allocBase + pathOffset path)
                rs.allocSize s_mid.perms.NextTag]),
                  pc := s_mid.pc + 1 } (setPlaceInfo
            (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
              [Instr.Assgn (Register.R csPrefix.nextReg)
                (Rhs.Alloc (layoutToTyVal τ))])
            dstLoc.idx.1 (Register.R csPrefix.nextReg, τ)) :=
            LocalBindingSim.insert_fresh_reg h_slbs h_prb1 h_sregmono rfl
          have h_lbs2 : LocalBindingSim (ρa.extendBlock s_mir.mem.addrStart (blockSize τ)) (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag) s1.env
              { s_mid with
                  perms := r',
                  reg := oseair.RegMap.insert
                    (oseair.RegMap.insert s_mid.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg) (obseq.TyVal.PTy, [Val.Ptr rs.allocBase
                (rs.addr - rs.allocBase + pathOffset path)
                rs.allocSize s_mid.perms.NextTag])) (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
                (setPlaceInfo
                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal τ))])
                  dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))).nextReg + 1))
                    (obseq.layoutToTyVal τ, (oseair.readWordSeq s_mid.mem (rs.addr + pathOffset path) (blockSize τ))),
                  mem := oseair.writeWordSeq s_mid.mem s_mir.mem.addrStart (oseair.readWordSeq s_mid.mem (rs.addr + pathOffset path) (blockSize τ)),
                  pc := s_mid.pc + 1 + 1 + 1 + 1 } (setPlaceInfo
            (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
              [Instr.Assgn (Register.R csPrefix.nextReg)
                (Rhs.Alloc (layoutToTyVal τ))])
            dstLoc.idx.1 (Register.R csPrefix.nextReg, τ)) :=
            LocalBindingSim.insert_fresh_reg h_lbs1 h_prb1
              (Nat.le_trans h_sregmono (Nat.le_succ _)) rfl
          intro τ' loc' binding' h_env'
          obtain ⟨reg', base', tag', h_pi', h_entry', h_ra', h_rt', h_nw', h_dom'⟩ :=
            h_lbs2 loc' binding' h_env'
          refine ⟨reg', base', tag', ?_, h_entry', h_ra', h_rt', h_nw', h_dom'⟩
          rw [h_stmtRun, getPlaceInfo_emit, getPlaceInfo_emit, getPlaceInfo_setNextReg,
            getPlaceInfo_emit, getPlaceInfo_setNextReg]
          rw [h_gp]
          exact h_pi'
        · show TagRenameBounded _ perms₃.NextTag r'.NextTag
          rw [sb_write_NextTag h_useMut_src', sb_read_NextTag h_read_src, h_snt1,
            h_perms1, sb_write_NextTag h_useMut_tgt']
          refine TagRenameBounded.mono h_tbd' (Nat.le_refl _) ?_
          refine Nat.le_trans h_snt2 ?_
          rw [← sb_read_NextTag h_read_tgt]
          exact h_ntle
        · simp only [AllocLockstep, mirlite_writeWordSeq_addrStart,
            oseair_writeWordSeq_addrStart, h_smem, h_memstart1]
          show (oseair.allocate s_osea.mem (obseq.typeSize (layoutToTyVal τ))).2.addrStart
            = _
          simp only [oseair.allocate]
          rw [h_addr_eq, h_sz]
        · intro τ' loc' h_none
          have h_none1 : mirlite.Env.lookup s1.env loc' = none := h_none
          rw [← h_s1] at h_none1
          by_cases h_idx : loc'.idx = dstLoc.idx
          · exfalso
            simp only [mirlite.Env.lookup, mirlite.Env.set, h_idx, if_pos rfl] at h_none1
            exact absurd h_none1 (by simp)
          have h_idxv : loc'.idx.1 ≠ dstLoc.idx.1 := fun h => h_idx (Fin.ext h)
          have h_none0 : mirlite.Env.lookup s_mir.env loc' = none := by
            simpa only [mirlite.Env.lookup, mirlite.Env.set, if_neg h_idx] using h_none1
          rw [h_stmtRun, getPlaceInfo_emit, getPlaceInfo_emit, getPlaceInfo_setNextReg,
            getPlaceInfo_emit, getPlaceInfo_setNextReg]
          rw [h_gp, getPlaceInfo_setPlaceInfo_ne _ h_idxv]
          exact h_unmap loc' h_none0
        · intro idx reg'' τ'' h_look
          rw [h_stmtRun] at h_look ⊢
          rw [getPlaceInfo_emit, getPlaceInfo_emit, getPlaceInfo_setNextReg,
            getPlaceInfo_emit, getPlaceInfo_setNextReg] at h_look
          rw [h_gp] at h_look
          refine RegisterBelow.mono ?_ (h_prb1 _ _ _ h_look)
          simp only [emit]
          exact Nat.le_trans h_sregmono (Nat.le_trans (Nat.le_succ _) (Nat.le_succ _))
      · simp at h_w

/-! ## NON-LOCAL destination: the fragment composes TWO place lowerings.

`compileStmtChecked`'s general assign arm runs the rhs pre-phase (the
source lowering AND, since the temp-assignment lowering, the `Load` that
performs the read) BEFORE the destination lowering, then stores. With
both places cleanup-free the whole statement is
`[src code; Load; dst code; RStore]`. -/

theorem compileStmt_copy_chaindst_run
    {Γ : Ctx} {τ : LayoutTy}
    {P : Place Γ (obseq.LayoutTy.PtrL τ)} {src : Place Γ τ}
    {cs : CompilerState}
    {sOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared src)}
    {dOut : ResultWithEvidence PtrResult
      (PlaceToRegEvidence RefKind.Mut (Place.deref P))}
    (h_root : CompilerM.run (ensurePlaceRoot (Place.deref P)) cs = cs)
    (h_sval : CheckedCompilerM.value (placeToRegChecked RefKind.Shared src) cs
      = Except.ok sOut)
    (h_sclean : sOut.result.cleanup = [])
    (h_dval : CheckedCompilerM.value (placeToRegChecked RefKind.Mut (Place.deref P))
      (emit
        { nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) cs).nextReg + 1,
          nextLabel := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) cs).nextLabel,
          code := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) cs).code,
          placeRegMap := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) cs).placeRegMap }
        [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) cs).nextReg)
          (Rhs.Load (layoutToTyVal τ) sOut.result.reg)])
      = Except.ok dOut)
    (h_dclean : dOut.result.cleanup = []) :
    CheckedCompilerM.run
        (compileStmtChecked (Stmt.assign (.deref P) (.copy src))) cs
      = emit (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (Place.deref P))
          (emit
            { nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) cs).nextReg + 1,
              nextLabel := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) cs).nextLabel,
              code := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) cs).code,
              placeRegMap := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) cs).placeRegMap }
            [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) cs).nextReg)
              (Rhs.Load (layoutToTyVal τ) sOut.result.reg)]))
          [Instr.RStore (layoutToTyVal τ)
            (Register.R (CheckedCompilerM.run
              (placeToRegChecked RefKind.Shared src) cs).nextReg)
            dOut.result.reg] := by
  simp only [compileStmtChecked, compileRExprPreChecked,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
    h_root, h_sval]
  simp only [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM,
    cleanupInstrs, h_sclean, emit_nil, List.reverse_nil, List.map_nil,
    List.append_nil]
  split
  · rename_i o h_d
    have h_oeq : dOut = o := Except.ok.inj (h_dval ▸ h_d)
    subst h_oeq
    simp [CompilerM.run, CompilerM.value, emitM, cleanupInstrs, h_dclean, emit_nil]
  · rename_i e h_d
    exact absurd h_d (by rw [h_dval]; simp)

theorem compileStmt_copy_chaindst_value
    {Γ : Ctx} {τ : LayoutTy}
    {P : Place Γ (obseq.LayoutTy.PtrL τ)} {src : Place Γ τ}
    {cs : CompilerState}
    {sOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared src)}
    {dOut : ResultWithEvidence PtrResult
      (PlaceToRegEvidence RefKind.Mut (Place.deref P))}
    (h_root : CompilerM.run (ensurePlaceRoot (Place.deref P)) cs = cs)
    (h_sval : CheckedCompilerM.value (placeToRegChecked RefKind.Shared src) cs
      = Except.ok sOut)
    (h_dval : CheckedCompilerM.value (placeToRegChecked RefKind.Mut (Place.deref P))
      (emit
        { nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) cs).nextReg + 1,
          nextLabel := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) cs).nextLabel,
          code := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) cs).code,
          placeRegMap := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) cs).placeRegMap }
        ([Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) cs).nextReg)
            (Rhs.Load (layoutToTyVal τ) sOut.result.reg)]
          ++ cleanupInstrs sOut.result.cleanup))
      = Except.ok dOut) :
    ∃ so, CheckedCompilerM.value
      (compileStmtChecked (Stmt.assign (.deref P) (.copy src))) cs
      = Except.ok so := by
  simp only [compileStmtChecked, compileRExprPreChecked,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
    h_root, h_sval]
  simp only [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM]
  split
  · exact ⟨_, rfl⟩
  · rename_i e h_d
    exact absurd h_d (by rw [h_dval]; simp)

/-- NON-LOCAL destination, CLOSED 2026-09-03: `*Q := copy src` for a
    canonical-chain destination and source. The first leaf that composes
    TWO mother-lemma calls. The rhs pre-phase lowers the source and the
    `Load` performs the READ; the destination is lowered AFTER that, at
    the post-read permissions — which is mirlite's own order since the
    temp-assignment lowering — and the `RStore` writes. The temporary
    register survives the destination lowering by the mother lemma's
    register-frame conjunct. -/
theorem copy_chaindst_chainsrc_simulation
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {τ : LayoutTy}
    {P : Place Γ (obseq.LayoutTy.PtrL τ)} {src : Place Γ τ}
    (compProg : oseair.Prog)
    (h_dchain : PtrChain (Place.deref P))
    (h_schain : PtrChain src)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    {stmt0 : Stmt Γ}
    (h_stmt : prog.get? s_mir.pc = some stmt0)
    (h_run0 : ∀ cs, CheckedCompilerM.run (compileStmtChecked stmt0) cs
      = CheckedCompilerM.run
          (compileStmtChecked (Stmt.assign (.deref P) (.copy src))) cs)
    (h_val0 : ∀ cs so, CheckedCompilerM.value
        (compileStmtChecked (Stmt.assign (.deref P) (.copy src))) cs
        = Except.ok so →
      ∃ so', CheckedCompilerM.value (compileStmtChecked stmt0) cs
        = Except.ok so')
    (h_step : mirlite.stepStmt MSB s_mir
      (.assign (.deref P) (.copy src)) = .ok s_mir') :
    ∃ (s_osea' : oseair.State MSB) (n : Nat),
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa ρt s_mir' s_osea' := by
  obtain ⟨csPrefix, ⟨h_csAt, h_pc⟩, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_tbd,
    h_alloc, h_unmap, h_prb⟩ := h_inv
  -- §1 invert the source: prepare is a no-op, the source resolves and is
  -- READ, and only THEN does the destination resolve
  simp only [mirlite.stepStmt, mirlite.doAssign] at h_step
  cases h_prep : mirlite.preparePlaceAssign MSB s_mir (Place.deref P) with
  | err msg => rw [h_prep] at h_step; simp at h_step
  | ok s1 =>
  rw [h_prep] at h_step
  have h_s1 : s1 = s_mir ∧
      ∃ r0, mirlite.resolvePlace? s_mir (Place.deref P) = some r0 := by
    simp only [mirlite.preparePlaceAssign] at h_prep
    split at h_prep
    · rename_i r0 h_r0
      cases h_prep
      exact ⟨rfl, r0, h_r0⟩
    · simp [mirlite.allocateRoot] at h_prep
  obtain ⟨h_s1eq, r0, h_resolved⟩ := h_s1
  rw [h_s1eq] at h_step
  simp only [mirlite.evalRExpr] at h_step
  cases h_sres : mirlite.resolvePlaceAcc MSB s_mir src with
  | error e => rw [h_sres] at h_step; simp at h_step
  | ok pr =>
  obtain ⟨rs, permsS⟩ := pr
  rw [h_sres] at h_step
  simp only at h_step
  by_cases h_fit : rs.addr + blockSize τ > rs.allocBase + rs.allocSize
  · rw [if_pos h_fit] at h_step
    simp at h_step
  · rw [if_neg h_fit] at h_step
    cases h_read_src : MSB.read permsS rs.addr (blockSize τ) rs.tag with
    | error e => rw [h_read_src] at h_step; simp at h_step
    | ok perms₂ =>
    rw [h_read_src] at h_step
    simp only at h_step
    cases h_dres : mirlite.resolvePlaceAcc MSB
        { s_mir with perms := perms₂ } (Place.deref P) with
    | error e => rw [h_dres] at h_step; simp at h_step
    | ok pr2 =>
    obtain ⟨rd, permsD⟩ := pr2
    rw [h_dres] at h_step
    simp only at h_step
    -- §2 both places are mapped; the statement compiles
    have h_mappedS : PlaceInputsMapped csPrefix src :=
      placeInputsMapped_of_localBindingSim_resolvePlace h_lbs
        (resolvePlace?_of_resolveAcc h_sres)
    have h_mappedD : PlaceInputsMapped csPrefix (Place.deref P) :=
      placeInputsMapped_of_localBindingSim_resolvePlace h_lbs h_resolved
    have h_root := ensurePlaceRoot_run_eq_of_mapped h_mappedD
    obtain ⟨sOut0, h_sval0⟩ := placeToRegChecked_ok_of_placeInputsMapped
      (cs := csPrefix) (kind := RefKind.Shared) h_mappedS
    have h_prmS : (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).placeRegMap = csPrefix.placeRegMap :=
      h_schain.placeToRegChecked_placeRegMap RefKind.Shared csPrefix
    obtain ⟨dOut0, h_dval0⟩ := placeToRegChecked_ok_of_placeInputsMapped
      (cs := (emit
        { nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg + 1,
          nextLabel := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextLabel,
          code := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).code,
          placeRegMap := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).placeRegMap }
        ([Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg)
            (Rhs.Load (layoutToTyVal τ) sOut0.result.reg)]
          ++ cleanupInstrs sOut0.result.cleanup))) (kind := RefKind.Mut)
      (PlaceInputsMapped.placeRegMap_congr (by simp only [emit]; exact h_prmS)
        _ h_mappedD)
    obtain ⟨stmtOutC, h_stmtOutC⟩ :=
      compileStmt_copy_chaindst_value h_root h_sval0 h_dval0
    obtain ⟨stmtOut, h_stmtOut⟩ := h_val0 csPrefix stmtOutC h_stmtOutC
    -- §3 code inclusion for the SOURCE lowering
    have h_incrS : StateIncr (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix)
        (CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix) := by
      rw [h_run0]
      simp only [compileStmtChecked, compileRExprPreChecked,
        CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
        CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
        CheckedCompilerM.run_pure, CheckedCompilerM.value_pure, h_root, h_sval0]
      simp only [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM]
      refine StateIncr.trans (freshReg_state_incr (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix)) ?_
      split
      · rename_i a h_a
        exact StateIncr.trans
          (emit_state_incr _ ([Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg)
              (Rhs.Load (layoutToTyVal τ) sOut0.result.reg)]
            ++ cleanupInstrs sOut0.result.cleanup))
          (StateIncr.trans
            (CheckedCompilerM.incr (placeToRegChecked RefKind.Mut (Place.deref P))
              (emit
                { nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg + 1,
                  nextLabel := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextLabel,
                  code := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).code,
                  placeRegMap := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).placeRegMap }
                ([Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg)
                    (Rhs.Load (layoutToTyVal τ) sOut0.result.reg)]
                  ++ cleanupInstrs sOut0.result.cleanup)))
            (emit_tower_incr₃ (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (Place.deref P))
            (emit
              { nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg + 1,
                nextLabel := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextLabel,
                code := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).code,
                placeRegMap := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).placeRegMap }
              ([Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg)
                  (Rhs.Load (layoutToTyVal τ) sOut0.result.reg)]
                ++ cleanupInstrs sOut0.result.cleanup)))
              [Instr.RStore (layoutToTyVal τ) (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg) a.result.reg]
              (cleanupInstrs [])
              (cleanupInstrs a.result.cleanup)))
      · exact StateIncr.trans
          (emit_state_incr _ ([Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg)
              (Rhs.Load (layoutToTyVal τ) sOut0.result.reg)]
            ++ cleanupInstrs sOut0.result.cleanup))
          (CheckedCompilerM.incr (placeToRegChecked RefKind.Mut (Place.deref P)) _)
    have h_instS : ∀ q' instr,
        q' < (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextLabel →
        (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).code q' = some instr →
        compProg q' = some instr := by
      intro q' instr h_lt h_code
      refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
      · exact Nat.lt_of_lt_of_le h_lt h_incrS.nextLabel_le
      · rw [h_incrS.code_eq q' h_lt]
        exact h_code
    -- §4 the SOURCE mother lemma
    obtain ⟨sOut, n1, s_mid1, tres, h_sval, h_sclean, h_srun, h_spc, h_smem,
      h_spsim, h_snt1, h_snt2, h_slbs, h_sentry, h_srt, h_snw, h_sle, h_srange,
      h_sbelow, h_sprm, h_sregmono, h_slabmono, h_sframe, -⟩ :=
      ptrChain_lowering_sim h_id_a h_wf_t h_schain RefKind.Shared csPrefix s_osea
        rs permsS h_sres h_tbd h_lbs h_prb h_sms h_psim h_pc h_instS
    have h_cancelS : rs.allocBase + (rs.addr - rs.allocBase) = rs.addr :=
      Nat.add_sub_cancel' h_sle
    have h_ts : obseq.typeSize (layoutToTyVal τ) = blockSize τ := by
      simp [blockSize]
    have h_sOut_eq : sOut = sOut0 := by
      rw [h_sval0] at h_sval
      exact (Except.ok.inj h_sval).symm
    subst h_sOut_eq
    -- §5 code inclusion at the post-`Load` compiler state
    have h_incrCS1 : StateIncr (emit
        { nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg + 1,
          nextLabel := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextLabel,
          code := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).code,
          placeRegMap := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).placeRegMap }
        [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg)
          (Rhs.Load (layoutToTyVal τ) sOut.result.reg)])
        (CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix) := by
      rw [h_run0]
      simp only [compileStmtChecked, compileRExprPreChecked,
        CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
        CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
        CheckedCompilerM.run_pure, CheckedCompilerM.value_pure, h_root, h_sval]
      simp only [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM,
        cleanupInstrs, h_sclean, emit_nil, List.reverse_nil, List.map_nil,
        List.append_nil]
      split
      · rename_i a h_a
        exact StateIncr.trans
          (CheckedCompilerM.incr (placeToRegChecked RefKind.Mut (Place.deref P))
            (emit
              { nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg + 1,
                nextLabel := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextLabel,
                code := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).code,
                placeRegMap := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).placeRegMap }
              [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg)
                (Rhs.Load (layoutToTyVal τ) sOut.result.reg)]))
          (StateIncr.trans
            (emit_state_incr
              (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (Place.deref P))
              (emit
                { nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg + 1,
                  nextLabel := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextLabel,
                  code := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).code,
                  placeRegMap := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).placeRegMap }
                [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg)
                  (Rhs.Load (layoutToTyVal τ) sOut.result.reg)]))
              [Instr.RStore (layoutToTyVal τ)
                (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg) a.result.reg])
            (emit_state_incr
              (emit
                (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (Place.deref P))
              (emit
                { nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg + 1,
                  nextLabel := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextLabel,
                  code := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).code,
                  placeRegMap := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).placeRegMap }
                [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg)
                  (Rhs.Load (layoutToTyVal τ) sOut.result.reg)]))
                [Instr.RStore (layoutToTyVal τ)
                  (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg) a.result.reg])
              (List.map (fun (x : Register × Nat) => Instr.Die x.fst x.snd)
                a.result.cleanup.reverse)))
      · exact CheckedCompilerM.incr (placeToRegChecked RefKind.Mut (Place.deref P)) _
    have h_instD : ∀ q' instr,
        q' < (emit
          { nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg + 1,
            nextLabel := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextLabel,
            code := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).code,
            placeRegMap := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).placeRegMap }
          [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg)
            (Rhs.Load (layoutToTyVal τ) sOut.result.reg)]).nextLabel →
        (emit
          { nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg + 1,
            nextLabel := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextLabel,
            code := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).code,
            placeRegMap := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).placeRegMap }
          [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg)
            (Rhs.Load (layoutToTyVal τ) sOut.result.reg)]).code q' = some instr →
        compProg q' = some instr := by
      intro q' instr h_lt h_code
      refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
      · exact Nat.lt_of_lt_of_le h_lt h_incrCS1.nextLabel_le
      · rw [h_incrCS1.code_eq q' h_lt]
        exact h_code
    -- code inclusion for the DESTINATION lowering's own instructions
    have h_incrDrun : StateIncr (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (Place.deref P))
        (emit
          { nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg + 1,
            nextLabel := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextLabel,
            code := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).code,
            placeRegMap := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).placeRegMap }
          [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg)
            (Rhs.Load (layoutToTyVal τ) sOut.result.reg)]))
        (CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix) := by
      rw [h_run0]
      simp only [compileStmtChecked, compileRExprPreChecked,
        CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
        CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
        CheckedCompilerM.run_pure, CheckedCompilerM.value_pure, h_root, h_sval]
      simp only [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM,
        cleanupInstrs, h_sclean, emit_nil, List.reverse_nil, List.map_nil,
        List.append_nil]
      split
      · rename_i a h_a
        exact StateIncr.trans
          (emit_state_incr (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (Place.deref P))
        (emit
          { nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg + 1,
            nextLabel := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextLabel,
            code := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).code,
            placeRegMap := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).placeRegMap }
          [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg)
            (Rhs.Load (layoutToTyVal τ) sOut.result.reg)]))
            [Instr.RStore (layoutToTyVal τ)
              (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg) a.result.reg])
          (emit_state_incr
            (emit (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (Place.deref P))
        (emit
          { nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg + 1,
            nextLabel := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextLabel,
            code := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).code,
            placeRegMap := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).placeRegMap }
          [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg)
            (Rhs.Load (layoutToTyVal τ) sOut.result.reg)]))
              [Instr.RStore (layoutToTyVal τ)
                (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg) a.result.reg])
            (List.map (fun (x : Register × Nat) => Instr.Die x.fst x.snd)
              a.result.cleanup.reverse))
      · exact StateIncr.refl _
    have h_instDst : ∀ q' instr,
        q' < (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (Place.deref P))
        (emit
          { nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg + 1,
            nextLabel := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextLabel,
            code := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).code,
            placeRegMap := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).placeRegMap }
          [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg)
            (Rhs.Load (layoutToTyVal τ) sOut.result.reg)])).nextLabel →
        (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (Place.deref P))
        (emit
          { nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg + 1,
            nextLabel := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextLabel,
            code := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).code,
            placeRegMap := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).placeRegMap }
          [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg)
            (Rhs.Load (layoutToTyVal τ) sOut.result.reg)])).code q' = some instr →
        compProg q' = some instr := by
      intro q' instr h_lt h_code
      refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
      · exact Nat.lt_of_lt_of_le h_lt h_incrDrun.nextLabel_le
      · rw [h_incrDrun.code_eq q' h_lt]
        exact h_code
    -- §6 the READ: transport, then execute the `Load`
    obtain ⟨p2, h_read_tgt, h_psim2⟩ :=
      sb_read_respects_PermSim h_spsim h_wf_t h_srt h_snw h_read_src
    have h_code1 : compProg s_mid1.pc
        = some (Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg) (Rhs.Load (layoutToTyVal τ) sOut.result.reg)) := by
      rw [h_spc]
      refine h_instD _ _ ?_ ?_
      · simp only [emit, List.length_cons, List.length_nil]
        omega
      · have h := emit_code_at_new
          { nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg + 1,
            nextLabel := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextLabel,
            code := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).code,
            placeRegMap := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).placeRegMap }
          [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg) (Rhs.Load (layoutToTyVal τ) sOut.result.reg)]
          (k := 0) (by simp)
        simpa using h
    have h_read2t : MSB.read s_mid1.perms
        (rs.allocBase + (rs.addr - rs.allocBase))
        (obseq.typeSize (layoutToTyVal τ)) tres = .ok p2 := by
      rw [h_ts, h_cancelS]
      exact h_read_tgt
    have h_run1 := runN_Assgn_Load_ptr_step compProg s_mid1
      (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg) sOut.result.reg (layoutToTyVal τ) h_code1 h_sentry
      (by rw [h_ts]; grind) h_read2t
    rw [h_ts, h_cancelS] at h_run1
    -- §7 the DESTINATION mother lemma, at the post-read states
    have h_prmCS1 : (emit
        { nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg + 1,
          nextLabel := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextLabel,
          code := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).code,
          placeRegMap := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).placeRegMap }
        [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg)
          (Rhs.Load (layoutToTyVal τ) sOut.result.reg)]).placeRegMap = csPrefix.placeRegMap := by
      simp only [emit]
      exact h_sprm
    have h_lbs1 : LocalBindingSim ρa ρt s_mir.env
        { s_mid1 with
          perms := p2,
          reg := oseair.RegMap.insert s_mid1.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg)
            (layoutToTyVal τ, (oseair.readWordSeq s_mid1.mem rs.addr (blockSize τ))),
          pc := s_mid1.pc + 1 } (emit
          { nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg + 1,
            nextLabel := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextLabel,
            code := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).code,
            placeRegMap := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).placeRegMap }
          [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg)
            (Rhs.Load (layoutToTyVal τ) sOut.result.reg)]) := by
      have h_ins : LocalBindingSim ρa ρt s_mir.env
          { s_mid1 with
              perms := p2,
              reg := oseair.RegMap.insert s_mid1.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg)
                (layoutToTyVal τ, (oseair.readWordSeq s_mid1.mem rs.addr (blockSize τ))),
              pc := s_mid1.pc + 1 } csPrefix :=
        LocalBindingSim.insert_fresh_reg h_slbs h_prb h_sregmono rfl
      intro τ' loc' binding' h_env'
      obtain ⟨reg', base', tag', h_pi', h_entry', h_ra', h_rt', h_nw', h_dom'⟩ :=
        h_ins loc' binding' h_env'
      refine ⟨reg', base', tag', ?_, h_entry', h_ra', h_rt', h_nw', h_dom'⟩
      show getPlaceInfo _ loc'.idx.1 = _
      simp only [getPlaceInfo, h_prmCS1]
      exact h_pi'
    have h_prb1 : PlaceRegMapBound (emit
          { nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg + 1,
            nextLabel := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextLabel,
            code := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).code,
            placeRegMap := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).placeRegMap }
          [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg)
            (Rhs.Load (layoutToTyVal τ) sOut.result.reg)]) := by
      intro idx reg τ'' h_look
      have h_cs : getPlaceInfo csPrefix idx = some (reg, τ'') := by
        show csPrefix.placeRegMap.lookup idx = _
        rw [← h_prmCS1]
        exact h_look
      refine RegisterBelow.mono ?_ (h_prb _ _ _ h_cs)
      simp only [emit]
      exact Nat.le_trans h_sregmono (Nat.le_succ _)
    have h_tbd1 : TagRenameBounded ρt perms₂.NextTag p2.NextTag := by
      rw [sb_read_NextTag h_read_src, sb_read_NextTag h_read_tgt, h_snt1]
      exact TagRenameBounded.mono h_tbd (Nat.le_refl _) h_snt2
    obtain ⟨dOut, n2, s_mid2, tresD, h_dval, h_dclean, h_drun, h_dpc, h_dmem,
      h_dpsim, h_dnt1, h_dnt2, h_dlbs, h_dentry, h_drt, h_dnw, h_dle, h_drange,
      h_dbelow, h_dprm, h_dregmono, h_dlabmono, h_dframe, -⟩ :=
      ptrChain_lowering_sim (s_mir := { s_mir with perms := perms₂ })
        (compProg := compProg) h_id_a h_wf_t h_dchain RefKind.Mut (emit
          { nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg + 1,
            nextLabel := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextLabel,
            code := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).code,
            placeRegMap := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).placeRegMap }
          [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg)
            (Rhs.Load (layoutToTyVal τ) sOut.result.reg)])
        { s_mid1 with
          perms := p2,
          reg := oseair.RegMap.insert s_mid1.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg)
            (layoutToTyVal τ, (oseair.readWordSeq s_mid1.mem rs.addr (blockSize τ))),
          pc := s_mid1.pc + 1 } rd permsD h_dres h_tbd1 h_lbs1 h_prb1
        (by
          show SourceMemSim ρa ρt s_mir.mem _
          rw [h_smem]
          exact h_sms)
        h_psim2
        (by
          show s_mid1.pc + 1 = _
          rw [h_spc]
          simp only [emit, List.length_cons, List.length_nil])
        h_instDst
    -- §8 the WRITE: transport, then execute the `RStore`
    have h_stmtRun := (h_run0 csPrefix).trans
      (compileStmt_copy_chaindst_run h_root h_sval h_sclean h_dval h_dclean)
    have h_cancelD : rd.allocBase + (rd.addr - rd.allocBase) = rd.addr :=
      Nat.add_sub_cancel' h_dle
    have h_w := h_step
    simp only [mirlite.writeResolvedPlace] at h_w
    split at h_w
    · simp at h_w
    · rename_i h_nb
      split at h_w
      · rename_i perms₃ h_useMut_src
        cases h_w
        obtain ⟨p3, h_useMut_tgt, h_psim3⟩ :=
          sb_write_respects_PermSim h_dpsim h_wf_t h_drt h_dnw h_useMut_src
        -- the temporary register survives the destination lowering
        have h_regbelow : RegisterBelow
            (emit
              { nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg + 1,
                nextLabel := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextLabel,
                code := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).code,
                placeRegMap := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).placeRegMap }
              [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg)
                (Rhs.Load (layoutToTyVal τ) sOut.result.reg)]).nextReg
            (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg) := by
          show (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg < _
          simp only [emit]
          omega
        have h_vreg : oseair.RegMap.lookup s_mid2.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg)
            = some (layoutToTyVal τ, (oseair.readWordSeq s_mid1.mem rs.addr (blockSize τ))) := by
          rw [h_dframe (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg) h_regbelow]
          exact RegMap.lookup_insert_self _ _ _
        have h_code2 : compProg s_mid2.pc
            = some (Instr.RStore (layoutToTyVal τ) (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg) dOut.result.reg) := by
          rw [h_dpc]
          refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
          · rw [h_stmtRun]
            show _ < _ + 1
            exact Nat.lt_succ_self _
          · rw [h_stmtRun]
            have h := emit_code_at_new
              (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (Place.deref P))
          (emit
            { nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg + 1,
              nextLabel := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextLabel,
              code := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).code,
              placeRegMap := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).placeRegMap }
            [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg)
              (Rhs.Load (layoutToTyVal τ) sOut.result.reg)]))
              [Instr.RStore (layoutToTyVal τ) (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg) dOut.result.reg]
              (k := 0) (by simp)
            simpa using h
        have h_useMut2t : MSB.useMut s_mid2.perms
            (rd.allocBase + (rd.addr - rd.allocBase)) (oseair.readWordSeq s_mid1.mem rs.addr (blockSize τ)).length tresD = .ok p3 := by
          rw [h_cancelD, oseair_readWordSeq_length]
          simpa only [mirlite_readWordSeq_length] using h_useMut_tgt
        have h_wtp : oseair.writeThroughPtr MSB s_mid2 dOut.result.reg (oseair.readWordSeq s_mid1.mem rs.addr (blockSize τ))
            "RStore Invalid Regs"
            = oseair.Result.Ok
              { s_mid2 with
                  perms := p3,
                  mem := oseair.writeWordSeq s_mid2.mem rd.addr (oseair.readWordSeq s_mid1.mem rs.addr (blockSize τ)),
                  pc := s_mid2.pc + 1 } := by
          have h_dl : oseair.RegMap.lookup s_mid2.reg dOut.result.reg
              = some (obseq.TyVal.PTy,
                  [Val.Ptr rd.allocBase (rd.addr - rd.allocBase) rd.allocSize
                    tresD]) := h_dentry
          simp only [oseair.writeThroughPtr, h_dl]
          rw [if_neg (by
            rw [oseair_readWordSeq_length, h_cancelD]
            have h1 := Nat.not_lt.mp h_nb
            simp only [mirlite_readWordSeq_length] at h1
            exact Nat.not_lt.mpr (by grind))]
          rw [h_cancelD] at h_useMut2t
          simp only [h_useMut2t, h_cancelD]
        have h_run2 := runN_RStore_step compProg s_mid2 _
          (layoutToTyVal τ) (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg) dOut.result.reg (oseair.readWordSeq s_mid1.mem rs.addr (blockSize τ))
          _ h_code2 h_vreg h_dentry h_wtp
        have h_runA := (oseair_runN_add n1 1 s_osea compProg s_mid1 h_srun).trans h_run1
        have h_runB := (oseair_runN_add (n1 + 1) n2 s_osea compProg _ h_runA).trans h_drun
        have h_run := (oseair_runN_add (n1 + 1 + n2) 1 s_osea compProg s_mid2 h_runB).trans
          h_run2
        -- §9 memory: the same values land at the same addresses
        have h_memchain : s_mid2.mem = s_osea.mem := by
          rw [h_dmem]
          show s_mid1.mem = _
          exact h_smem
        have h_rel : ListRel (MemValSim ρa ρt)
            (mirlite.readWordSeq s_mir.mem rs.addr (blockSize τ))
            (oseair.readWordSeq s_mid1.mem rs.addr (blockSize τ)) := by
          rw [h_smem]
          exact readWordSeq_sim h_id_a h_sms (blockSize τ) rs.addr
        have h_dom : ∀ k,
            k < (mirlite.readWordSeq s_mir.mem rs.addr (blockSize τ)).length →
            ρa (rd.addr + k) = some (rd.addr + k) := by
          intro k hk
          rw [mirlite_readWordSeq_length] at hk
          have h_lt : rd.addr - rd.allocBase + k < rd.allocSize := by
            have h1 := Nat.not_lt.mp h_nb
            have h2 := h_dle
            simp only [mirlite_readWordSeq_length] at h1
            grind
          obtain ⟨a', ha'⟩ := h_drange _ h_lt
          have h_addr : rd.allocBase + (rd.addr - rd.allocBase + k) = rd.addr + k := by
            have h2 := h_dle
            grind
          rw [h_addr] at ha'
          grind [IdentityOnDomain]
        have h_sms' : SourceMemSim ρa ρt
            (mirlite.writeWordSeq s_mir.mem rd.addr
              (mirlite.readWordSeq s_mir.mem rs.addr (blockSize τ)))
            (oseair.writeWordSeq s_mid2.mem rd.addr (oseair.readWordSeq s_mid1.mem rs.addr (blockSize τ))) := by
          refine SourceMemSim.writeWordSeq_extend h_id_a _ _ _ _ _ h_rel h_dom ?_
          rw [h_memchain]
          exact h_sms
        -- §10 rebuild the invariant
        refine ⟨_, n1 + 1 + n2 + 1, h_run, ?_⟩
        refine ⟨CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix,
          ⟨prefixCompileState_succ h_csAt h_stmt h_stmtOut, ?_⟩, ?_, ?_, h_psim3,
          h_id_a, h_wf_t, ?_, ?_, ?_, ?_⟩
        · show s_mid2.pc + 1 = _
          rw [h_dpc, h_stmtRun]
          simp [emit]
        · intro τ' loc' binding' h_env'
          obtain ⟨reg', base', tag', h_pi', h_entry', h_ra', h_rt', h_nw', h_dom'⟩ :=
            h_dlbs loc' binding' h_env'
          refine ⟨reg', base', tag', ?_, h_entry', h_ra', h_rt', h_nw', h_dom'⟩
          rw [h_stmtRun, getPlaceInfo_emit]
          show _ = _
          simp only [getPlaceInfo, h_dprm]
          exact h_pi'
        · exact h_sms'
        · show TagRenameBounded ρt perms₃.NextTag p3.NextTag
          rw [sb_write_NextTag h_useMut_src, sb_write_NextTag h_useMut_tgt,
            h_dnt1, sb_read_NextTag h_read_src, h_snt1]
          refine TagRenameBounded.mono h_tbd (Nat.le_refl _) ?_
          rw [sb_read_NextTag h_read_tgt] at h_dnt2
          grind
        · simp only [AllocLockstep, mirlite_writeWordSeq_addrStart,
            oseair_writeWordSeq_addrStart, h_memchain]
          exact h_alloc
        · intro τ' loc' h_none
          rw [h_stmtRun, getPlaceInfo_emit]
          show _ = _
          simp only [getPlaceInfo, h_dprm]
          have h_p : (emit
              { nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg + 1,
                nextLabel := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextLabel,
                code := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).code,
                placeRegMap := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).placeRegMap }
              [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg)
                (Rhs.Load (layoutToTyVal τ) sOut.result.reg)]).placeRegMap = csPrefix.placeRegMap := by
            simp only [emit]
            exact h_sprm
          simp only [getPlaceInfo] at h_p ⊢
          rw [h_p]
          exact h_unmap loc' h_none
        · intro idx reg'' τ'' h_look
          rw [h_stmtRun] at h_look ⊢
          rw [getPlaceInfo_emit] at h_look
          have h_p : (emit
              { nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg + 1,
                nextLabel := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextLabel,
                code := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).code,
                placeRegMap := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).placeRegMap }
              [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg)
                (Rhs.Load (layoutToTyVal τ) sOut.result.reg)]).placeRegMap = csPrefix.placeRegMap := by
            simp only [emit]
            exact h_sprm
          have h_cs : getPlaceInfo csPrefix idx = some (reg'', τ'') := by
            show csPrefix.placeRegMap.lookup idx = _
            rw [← h_p, ← h_dprm]
            exact h_look
          refine RegisterBelow.mono ?_ (h_prb _ _ _ h_cs)
          simp only [emit] at h_dregmono ⊢
          grind
      · simp at h_w

/-- RESIDUAL (sorried), NARROWED 2026-09-03 (temp-assignment
    lowering): for a BOUND or UNBOUND LOCAL destination every source
    shape is closed — chain sources by
    `copy_chainsrc_local_simulation` / `copy_fresh_chainsrc_simulation`,
    proj-topped sources by the four `copy_*projchain_*` leaves, all
    reached through the src flatten transfer.

    For a DEREF destination the CHAIN/CHAIN case is now closed by
    `copy_chaindst_chainsrc_simulation` — the first leaf composing TWO
    mother-lemma calls, with the READ between them (which is only
    mirlite's order because of the temp-assignment lowering; the
    event-order obstacle that used to block this class is gone, and d59
    pins the divergence it caused).

    Remaining:
    - a deref destination whose destination or source needs FLATTENING
      first: the compiled transfer for THIS statement shape (deref dst
      with a copy rhs) is not written yet — mechanical, the same
      four-way agree alignment as the others;
    - a PROJECTED destination (`(*p).f := copy s`), which wraps the same
      skeleton in the destination's own `Borrow`/`Die`. -/
theorem copy_place_residual
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {τ : LayoutTy}
    {dst src : Place Γ τ}
    (compProg : oseair.Prog)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    (h_stmt : prog.get? s_mir.pc = some (.assign dst (.copy src)))
    (h_step : mirlite.stepStmt MSB s_mir (.assign dst (.copy src)) = .ok s_mir') :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' := by
  sorry

/-- LEAF SORRY 2 → DISPATCHER 2026-08-28: per-statement simulation for
    `.assign dst (.copy src)`, decomposed by the shapes of the two
    places. Regime L→L (both bound locals, any layout) is CLOSED by
    `copy_local_local_simulation`; the residual shapes are named. -/
theorem CompilerInv_step_copy
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {τ : LayoutTy}
    {dst src : Place Γ τ}
    (compProg : oseair.Prog)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    (h_stmt : prog.get? s_mir.pc = some (.assign dst (.copy src)))
    (h_step : mirlite.stepStmt MSB s_mir (.assign dst (.copy src)) = .ok s_mir') :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' := by
  cases dst with
  | «local» dstLoc =>
      cases src with
      | «local» srcLoc =>
          cases h_envD : mirlite.Env.lookup s_mir.env dstLoc with
          | some bD =>
              -- CLOSED: a bound local source is the base case of the
              -- chain grammar, so the chain-src leaf owns L→L too
              obtain ⟨s_osea', n, h_run, h_inv'⟩ :=
                copy_chainsrc_local_simulation (src := .local srcLoc) compProg
                  (PtrChain.base srcLoc) h_comp h_inv h_stmt
                  (fun _ => rfl) (fun _ so h => ⟨so, h⟩)
                  h_envD h_step
              exact ⟨ρa, ρt, s_osea', n, AddrRenameIncr.refl ρa,
                TagRenameIncr.refl ρt, h_run, h_inv'⟩
          | none =>
              -- CLOSED: fresh destination, chain source (regime B for copy)
              exact copy_fresh_chainsrc_simulation (src := .local srcLoc) compProg
                (PtrChain.base srcLoc) h_comp h_inv h_stmt
                (fun _ => rfl) (fun _ so h => ⟨so, h⟩) h_envD h_step
      | proj sbase ff =>
          cases h_envD : mirlite.Env.lookup s_mir.env dstLoc with
          | some bD =>
              -- FLATTEN the whole src: its normal form is ONE projection
              -- over a canonical chain, which the two collapsed leaves own
              obtain ⟨σ', Bc, path', h_flat, h_chain⟩ :=
                flatten_proj_chainish sbase ff
              rw [stepStmt_assign_copysrc_anyflatten, h_flat] at h_step
              have h_run0 : ∀ cs, CheckedCompilerM.run (compileStmtChecked
                  (Stmt.assign (.local dstLoc) (.copy (.proj sbase ff)))) cs
                  = CheckedCompilerM.run (compileStmtChecked
                      (Stmt.assign (.local dstLoc) (.copy (.proj Bc path')))) cs := by
                intro cs
                rw [compileStmt_copy_srcflatten_run (Place.proj sbase ff) cs, h_flat]
              have h_val0 : ∀ cs so, CheckedCompilerM.value (compileStmtChecked
                  (Stmt.assign (.local dstLoc) (.copy (.proj Bc path')))) cs
                  = Except.ok so →
                  ∃ so', CheckedCompilerM.value (compileStmtChecked
                    (Stmt.assign (.local dstLoc) (.copy (.proj sbase ff)))) cs
                    = Except.ok so' := by
                intro cs so h
                refine compileStmt_copy_srcflatten_value (Place.proj sbase ff) cs ?_
                rw [h_flat]
                exact ⟨so, h⟩
              by_cases h_off : pathOffset path' = 0
              · obtain ⟨s_osea', n, h_run, h_inv'⟩ :=
                  copy_projchain_zero_simulation compProg h_chain h_off h_comp h_inv
                    h_stmt h_run0 h_val0 h_envD h_step
                exact ⟨ρa, ρt, s_osea', n, AddrRenameIncr.refl ρa,
                  TagRenameIncr.refl ρt, h_run, h_inv'⟩
              · obtain ⟨s_osea', n, h_run, h_inv'⟩ :=
                  copy_projchain_offset_simulation compProg h_chain h_off h_comp h_inv
                    h_stmt h_run0 h_val0 h_envD h_step
                exact ⟨ρa, ρt, s_osea', n, AddrRenameIncr.refl ρa,
                  TagRenameIncr.refl ρt, h_run, h_inv'⟩
          | none =>
              -- CLOSED: fresh destination, proj-topped source (regime B)
              obtain ⟨σ', Bc, path', h_flat, h_chain⟩ :=
                flatten_proj_chainish sbase ff
              rw [stepStmt_assign_copysrc_anyflatten, h_flat] at h_step
              have h_run0 : ∀ cs, CheckedCompilerM.run (compileStmtChecked
                  (Stmt.assign (.local dstLoc) (.copy (.proj sbase ff)))) cs
                  = CheckedCompilerM.run (compileStmtChecked
                      (Stmt.assign (.local dstLoc) (.copy (.proj Bc path')))) cs := by
                intro cs
                rw [compileStmt_copy_srcflatten_run (Place.proj sbase ff) cs, h_flat]
              have h_val0 : ∀ cs so, CheckedCompilerM.value (compileStmtChecked
                  (Stmt.assign (.local dstLoc) (.copy (.proj Bc path')))) cs
                  = Except.ok so →
                  ∃ so', CheckedCompilerM.value (compileStmtChecked
                    (Stmt.assign (.local dstLoc) (.copy (.proj sbase ff)))) cs
                    = Except.ok so' := by
                intro cs so h
                refine compileStmt_copy_srcflatten_value (Place.proj sbase ff) cs ?_
                rw [h_flat]
                exact ⟨so, h⟩
              by_cases h_off : pathOffset path' = 0
              · exact copy_fresh_projchain_zero_simulation compProg h_chain h_off
                  h_comp h_inv h_stmt h_run0 h_val0 h_envD h_step
              · exact copy_fresh_projchain_offset_simulation compProg h_chain h_off
                  h_comp h_inv h_stmt h_run0 h_val0 h_envD h_step
      | deref pp =>
          cases h_envD : mirlite.Env.lookup s_mir.env dstLoc with
          | some bD =>
              -- CLOSED: `dst := copy *chain` — flatten-normalized, TOTAL
              rw [stepStmt_assign_copysrc_flatten] at h_step
              obtain ⟨s_osea', n, h_run, h_inv'⟩ :=
                copy_chainsrc_local_simulation (src := .deref (flattenPlace pp))
                  compProg (PtrChain_flatten_deref pp) h_comp h_inv h_stmt
                  (fun cs => compileStmt_copy_derefsrc_flatten_run cs)
                  (fun cs so h => compileStmt_copy_derefsrc_flatten_value cs so h)
                  h_envD h_step
              exact ⟨ρa, ρt, s_osea', n, AddrRenameIncr.refl ρa,
                TagRenameIncr.refl ρt, h_run, h_inv'⟩
          | none =>
              -- CLOSED: fresh destination, deref-chain source
              rw [stepStmt_assign_copysrc_flatten] at h_step
              exact copy_fresh_chainsrc_simulation (src := .deref (flattenPlace pp))
                compProg (PtrChain_flatten_deref pp) h_comp h_inv h_stmt
                (fun cs => compileStmt_copy_derefsrc_flatten_run cs)
                (fun cs so h => compileStmt_copy_derefsrc_flatten_value cs so h)
                h_envD h_step
  | proj _ _ => exact copy_place_residual compProg h_comp h_inv h_stmt h_step
  | deref pp =>
      -- CLOSED when BOTH places are already canonical chains: the
      -- two-mother leaf owns it. (Flattening the pair needs a compiled
      -- transfer for this statement shape, which the residual still
      -- names.)
      by_cases h_dch : PtrChain (Place.deref pp)
      case neg => exact copy_place_residual compProg h_comp h_inv h_stmt h_step
      by_cases h_sch : PtrChain src
      · obtain ⟨s_osea', n, h_run, h_inv'⟩ :=
          copy_chaindst_chainsrc_simulation (P := pp) compProg
            h_dch h_sch h_comp h_inv h_stmt
            (fun _ => rfl) (fun _ so h => ⟨so, h⟩) h_step
        exact ⟨ρa, ρt, s_osea', n, AddrRenameIncr.refl ρa, TagRenameIncr.refl ρt,
          h_run, h_inv'⟩
      · exact copy_place_residual compProg h_comp h_inv h_stmt h_step

end obseq3.proof
