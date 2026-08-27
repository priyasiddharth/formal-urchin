import obseq3.proof.common
import obseq3.proof.permsim_transport

namespace obseq3.proof

open obseq3
open obseq3.compile
open obseq3.oseair (Instr Register Rhs Val)

/-- A layout is never its own pointee: `τ ≠ PtrL τ`. Since `Local` carries
    `Γ.get idx = τ`, this is what makes a `PtrL τ`-typed destination and a
    `τ`-typed source necessarily DISTINCT locals — which the fresh-
    destination regime needs, because mirlite binds the destination before
    resolving the source. -/
theorem layout_ne_ptrL (τ : LayoutTy) : τ ≠ obseq.LayoutTy.PtrL τ := by
  intro h
  have := congrArg sizeOf h
  simp at this

/-- Hence the two locals have different indices. -/
theorem ref_dst_src_idx_ne {Γ : Ctx} {τ : LayoutTy}
    (dstLoc : Local Γ (obseq.LayoutTy.PtrL τ)) (srcLoc : Local Γ τ) :
    srcLoc.idx ≠ dstLoc.idx := by
  intro h
  have hs := srcLoc.hTy
  rw [h, dstLoc.hTy] at hs
  exact layout_ne_ptrL τ hs.symm

/-- Preparing one local's assignment leaves every OTHER local's binding
    alone: either the destination was already bound (the state is
    unchanged) or it was allocated, and `Env.set` only touches its own
    index. Needed twice by the fresh-destination regime, because
    `doAssign` resolves the SOURCE against the post-allocation state. -/
theorem prepare_lookup_ne {Γ : Ctx} {τ σ : LayoutTy}
    {s s' : mirlite.State MSB Γ}
    {dst : Local Γ σ} {other : Local Γ τ}
    (h_ne : other.idx ≠ dst.idx)
    (h : mirlite.preparePlaceAssign MSB s (.local dst) = .ok s') :
    mirlite.Env.lookup s'.env other = mirlite.Env.lookup s.env other := by
  simp only [mirlite.preparePlaceAssign, mirlite.resolvePlace?] at h
  cases h_env : mirlite.Env.lookup s.env dst with
  | some b =>
      rw [h_env] at h
      simp only at h
      injection h with h'
      rw [← h']
  | none =>
      rw [h_env] at h
      simp only [mirlite.allocateRoot, mirlite.allocateBase] at h
      split at h
      · exact absurd h (by simp)
      · injection h with h'
        rw [← h']
        show (mirlite.Env.set s.env dst _) other.idx = _
        simp only [mirlite.Env.set, if_neg h_ne]
        rfl

/-! ## The compiled fragment of a `local := &local` retag -/

/-- The fragment of `dst := &src` when BOTH places are mapped locals: one
    `Borrow` into a fresh temp, then the `RStore` of that pointer into the
    destination. Note there is no `Die`: the borrow's cleanup lives in the
    rhs result, and the `.assign (.local _)` arm never emits it — the
    stored reference must stay alive, which is exactly why this leaf does
    NOT need BRIDGE 1. -/
theorem compileStmt_ref_local_local_run
    {Γ : Ctx} {τ : LayoutTy}
    {dstLoc : Local Γ (obseq.LayoutTy.PtrL τ)} {srcLoc : Local Γ τ}
    {cs : CompilerState} {dstReg srcReg : Register}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = some (dstReg, obseq.LayoutTy.PtrL τ))
    (h_src : getPlaceInfo cs srcLoc.idx.1 = some (srcReg, τ)) :
    CheckedCompilerM.run
        (compileStmtChecked
          (Stmt.assign (.local dstLoc) (.ref kind prot mask (.local srcLoc)))) cs
      = emit (emit { cs with nextReg := cs.nextReg + 1 }
          [Instr.Assgn (Register.R cs.nextReg)
            (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)])
          [Instr.RStore obseq.TyVal.PTy (Register.R cs.nextReg) dstReg] := by
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_existing h_dst
  obtain ⟨h_prun, placeOut, h_pval, h_pres⟩ :=
    placeToRegChecked_local_existing (kind := kind) h_src
  simp [compileStmtChecked, compileRExprToChecked, placeToBorrowRegChecked,
    h_run, h_val, h_prun, h_pval, h_pres]
  simp [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM]

/-- The fragment of `dst := &src` when the DESTINATION is unmapped: the
    root `Alloc` that `ensureLocalRegE` emits, then the `Borrow` into a
    fresh temp, then the `RStore`. Three instructions, and the only ref
    shape whose compiler state grows a `placeRegMap` entry. -/
theorem compileStmt_ref_fresh_local_run
    {Γ : Ctx} {τ : LayoutTy}
    {dstLoc : Local Γ (obseq.LayoutTy.PtrL τ)} {srcLoc : Local Γ τ}
    {cs : CompilerState} {srcReg : Register}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = none)
    (h_src : getPlaceInfo cs srcLoc.idx.1 = some (srcReg, τ)) :
    CheckedCompilerM.run
        (compileStmtChecked
          (Stmt.assign (.local dstLoc) (.ref kind prot mask (.local srcLoc)))) cs
      = emit (emit
          { (setPlaceInfo
              (emit { cs with nextReg := cs.nextReg + 1 }
                [Instr.Assgn (Register.R cs.nextReg)
                  (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))])
              dstLoc.idx.1 (Register.R cs.nextReg, obseq.LayoutTy.PtrL τ)) with
              nextReg := cs.nextReg + 1 + 1 }
          [Instr.Assgn (Register.R (cs.nextReg + 1))
            (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)])
          [Instr.RStore obseq.TyVal.PTy (Register.R (cs.nextReg + 1))
            (Register.R cs.nextReg)] := by
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_fresh (loc := dstLoc) h_dst
  have h_run' : (ensureLocalRegE dstLoc cs).snd.val
      = setPlaceInfo
          (emit { cs with nextReg := cs.nextReg + 1 }
            [Instr.Assgn (Register.R cs.nextReg)
              (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))])
          dstLoc.idx.1 (Register.R cs.nextReg, obseq.LayoutTy.PtrL τ) := h_run
  have h_srcPost : getPlaceInfo
      (setPlaceInfo
        (emit { cs with nextReg := cs.nextReg + 1 }
          [Instr.Assgn (Register.R cs.nextReg)
            (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))])
        dstLoc.idx.1 (Register.R cs.nextReg, obseq.LayoutTy.PtrL τ))
      srcLoc.idx.1 = some (srcReg, τ) := by
    by_cases h_eq : srcLoc.idx.1 = dstLoc.idx.1
    · exfalso
      grind
    · rw [getPlaceInfo_setPlaceInfo_ne _ h_eq, getPlaceInfo_emit]
      exact h_src
  obtain ⟨h_prun, placeOut, h_pval, h_pres⟩ :=
    placeToRegChecked_local_existing (kind := kind) h_srcPost
  simp [compileStmtChecked, compileRExprToChecked, placeToBorrowRegChecked,
    h_run, h_val, h_prun, h_pval, h_pres]
  simp [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM, setPlaceInfo, emit]

/-- The fresh-destination statement lowers. -/
theorem compileStmt_ref_fresh_local_value
    {Γ : Ctx} {τ : LayoutTy}
    {dstLoc : Local Γ (obseq.LayoutTy.PtrL τ)} {srcLoc : Local Γ τ}
    {cs : CompilerState} {srcReg : Register}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = none)
    (h_src : getPlaceInfo cs srcLoc.idx.1 = some (srcReg, τ)) :
    ∃ so, CheckedCompilerM.value
      (compileStmtChecked
        (Stmt.assign (.local dstLoc) (.ref kind prot mask (.local srcLoc)))) cs
      = Except.ok so := by
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_fresh (loc := dstLoc) h_dst
  have h_run' : (ensureLocalRegE dstLoc cs).snd.val
      = setPlaceInfo
          (emit { cs with nextReg := cs.nextReg + 1 }
            [Instr.Assgn (Register.R cs.nextReg)
              (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))])
          dstLoc.idx.1 (Register.R cs.nextReg, obseq.LayoutTy.PtrL τ) := h_run
  have h_srcPost : getPlaceInfo
      (setPlaceInfo
        (emit { cs with nextReg := cs.nextReg + 1 }
          [Instr.Assgn (Register.R cs.nextReg)
            (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))])
        dstLoc.idx.1 (Register.R cs.nextReg, obseq.LayoutTy.PtrL τ))
      srcLoc.idx.1 = some (srcReg, τ) := by
    by_cases h_eq : srcLoc.idx.1 = dstLoc.idx.1
    · exfalso
      grind
    · rw [getPlaceInfo_setPlaceInfo_ne _ h_eq, getPlaceInfo_emit]
      exact h_src
  obtain ⟨h_prun, placeOut, h_pval, h_pres⟩ :=
    placeToRegChecked_local_existing (kind := kind) h_srcPost
  simp only [compileStmtChecked, compileRExprToChecked, placeToBorrowRegChecked,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
    h_run, h_pval]
  exact ⟨_, rfl⟩

/-- The fragment of `dst := &src.f` when `dst` is a mapped local and the
    borrowed place is a PROJECTED field of a mapped local: one `Borrow` at
    the field's offset over the field's length, then the `RStore`. Same
    two instructions as the L→L fragment — projection only moves the
    offset, thanks to the reassociating lowering. -/
theorem compileStmt_ref_proj_local_run
    {Γ : Ctx} {τ σb : LayoutTy}
    {dstLoc : Local Γ (obseq.LayoutTy.PtrL τ)} {srcLoc : Local Γ σb}
    {f : PathTo σb τ}
    {cs : CompilerState} {dstReg srcReg : Register}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = some (dstReg, obseq.LayoutTy.PtrL τ))
    (h_src : getPlaceInfo cs srcLoc.idx.1 = some (srcReg, σb)) :
    CheckedCompilerM.run
        (compileStmtChecked
          (Stmt.assign (.local dstLoc)
            (.ref kind prot mask (.proj (.local srcLoc) f)))) cs
      = emit (emit { cs with nextReg := cs.nextReg + 1 }
          [Instr.Assgn (Register.R cs.nextReg)
            (Rhs.Borrow kind prot mask (blockSize τ) srcReg (pathOffset f))])
          [Instr.RStore obseq.TyVal.PTy (Register.R cs.nextReg) dstReg] := by
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_existing h_dst
  have h_run' : (ensureLocalRegE dstLoc cs).snd.val = cs := h_run
  obtain ⟨h_prun, placeOut, h_pval, h_pres⟩ :=
    placeToRegChecked_local_existing (kind := kind) h_src
  have h_borrow_eq : placeToBorrowRegChecked (Γ := Γ) kind prot mask
      (.proj (.local srcLoc) f)
      = (do
          let baseOut ← placeToRegChecked kind (.local srcLoc)
          let baseRes := baseOut.result
          let offset := pathOffset f
          let tmpReg ← CheckedCompilerM.lift freshRegM
          let _ ← CheckedCompilerM.lift
            (emitM [Instr.Assgn tmpReg (Rhs.Borrow kind prot mask (blockSize τ) baseRes.reg offset)])
          pure {
            result := { reg := tmpReg,
                        cleanup := baseRes.cleanup ++ [(tmpReg, blockSize τ)] },
            evidence := PlaceToBorrowRegEvidence.proj (.local srcLoc) f baseRes tmpReg
              baseOut.evidence
          }) := by simp only [placeToBorrowRegChecked]
  simp [compileStmtChecked, compileRExprToChecked, h_borrow_eq,
    h_run, h_run', h_val, h_prun, h_pval, h_pres]
  simp [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM]

/-- The proj-src statement lowers. -/
theorem compileStmt_ref_proj_local_value
    {Γ : Ctx} {τ σb : LayoutTy}
    {dstLoc : Local Γ (obseq.LayoutTy.PtrL τ)} {srcLoc : Local Γ σb}
    {f : PathTo σb τ}
    {cs : CompilerState} {dstReg srcReg : Register}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = some (dstReg, obseq.LayoutTy.PtrL τ))
    (h_src : getPlaceInfo cs srcLoc.idx.1 = some (srcReg, σb)) :
    ∃ so, CheckedCompilerM.value
      (compileStmtChecked
        (Stmt.assign (.local dstLoc)
          (.ref kind prot mask (.proj (.local srcLoc) f)))) cs
      = Except.ok so := by
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_existing h_dst
  have h_run' : (ensureLocalRegE dstLoc cs).snd.val = cs := h_run
  obtain ⟨h_prun, placeOut, h_pval, h_pres⟩ :=
    placeToRegChecked_local_existing (kind := kind) h_src
  have h_borrow_eq : placeToBorrowRegChecked (Γ := Γ) kind prot mask
      (.proj (.local srcLoc) f)
      = (do
          let baseOut ← placeToRegChecked kind (.local srcLoc)
          let baseRes := baseOut.result
          let offset := pathOffset f
          let tmpReg ← CheckedCompilerM.lift freshRegM
          let _ ← CheckedCompilerM.lift
            (emitM [Instr.Assgn tmpReg (Rhs.Borrow kind prot mask (blockSize τ) baseRes.reg offset)])
          pure {
            result := { reg := tmpReg,
                        cleanup := baseRes.cleanup ++ [(tmpReg, blockSize τ)] },
            evidence := PlaceToBorrowRegEvidence.proj (.local srcLoc) f baseRes tmpReg
              baseOut.evidence
          }) := by simp only [placeToBorrowRegChecked]
  simp only [compileStmtChecked, compileRExprToChecked, h_borrow_eq,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
    h_run, h_pval]
  exact ⟨_, rfl⟩

/-- The statement lowers (its checked value is `ok`) in this regime. -/
theorem compileStmt_ref_local_local_value
    {Γ : Ctx} {τ : LayoutTy}
    {dstLoc : Local Γ (obseq.LayoutTy.PtrL τ)} {srcLoc : Local Γ τ}
    {cs : CompilerState} {dstReg srcReg : Register}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = some (dstReg, obseq.LayoutTy.PtrL τ))
    (h_src : getPlaceInfo cs srcLoc.idx.1 = some (srcReg, τ)) :
    ∃ so, CheckedCompilerM.value
      (compileStmtChecked
        (Stmt.assign (.local dstLoc) (.ref kind prot mask (.local srcLoc)))) cs
      = Except.ok so := by
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_existing h_dst
  obtain ⟨h_prun, placeOut, h_pval, h_pres⟩ :=
    placeToRegChecked_local_existing (kind := kind) h_src
  simp only [compileStmtChecked, compileRExprToChecked, placeToBorrowRegChecked,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
    h_run, h_pval]
  exact ⟨_, rfl⟩

/-! ## Regime L→L: `dstLocal := &srcLocal`, both bound -/

/-- REGIME L→L, CLOSED: a reference to a BOUND local stored into a BOUND
    pointer-typed local. The fragment is `Borrow; RStore` — no `Die`, so
    no BRIDGE 1: the borrow stays alive because it is the stored value.
    This is the first leaf that grows ρt at a USER-visible tag: the
    source's fresh reference tag and the target's are paired by
    `sb_ref_respects_PermSim`, and the stored pointer's `MemValSim` holds
    under that extension with its referent range supplied by the source
    local's `LocalBindingSim` block-domain conjunct. ρa does not grow.

    No size side condition: zero-sized referents are fine. (Until
    2026-08-22 the target's `Rhs.Borrow` bounds check was
    `addr ≥ base + size`, which rejected them while mirlite's `M.ref`
    accepted them — Rust sides with mirlite, `&()` is legal — and this
    regime carried `0 < blockSize τ`. The check is now the range form
    `addr + len > base + size`, the same as `writeThroughPtr`'s, and the
    residual is gone.) -/
theorem ref_local_local_simulation
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {τ : LayoutTy}
    {dstLoc : Local Γ (obseq.LayoutTy.PtrL τ)} {srcLoc : Local Γ τ}
    {bD bS : mirlite.Binding}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (compProg : oseair.Prog)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    (h_stmt : prog.get? s_mir.pc
      = some (.assign (.local dstLoc) (.ref kind prot mask (.local srcLoc))))
    (h_envD : mirlite.Env.lookup s_mir.env dstLoc = some bD)
    (h_envS : mirlite.Env.lookup s_mir.env srcLoc = some bS)
    (h_step : mirlite.stepStmt MSB s_mir
      (.assign (.local dstLoc) (.ref kind prot mask (.local srcLoc))) = .ok s_mir') :
    ∃ (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa ρt' s_mir' s_osea' := by
  obtain ⟨csPrefix, ⟨h_csAt, h_pc⟩, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_tbd,
    h_alloc, h_unmap, h_prb⟩ := h_inv
  obtain ⟨dstReg, baseD, tagD, h_piD, h_entryD, h_raD, h_rtD, h_nwD, -⟩ :=
    h_lbs dstLoc bD h_envD
  obtain ⟨srcReg, baseS, tagS, h_piS, h_entryS, h_raS, h_rtS, h_nwS, h_domS⟩ :=
    h_lbs srcLoc bS h_envS
  have h_baseD : baseD = bD.addr := (h_id_a _ _ h_raD).symm
  have h_baseS : baseS = bS.addr := (h_id_a _ _ h_raS).symm
  subst h_baseD
  subst h_baseS
  -- §1 invert the source step: prepare is a no-op, both locals resolve,
  -- the retag succeeds, the pointer is written
  simp only [mirlite.stepStmt, mirlite.doAssign, mirlite.preparePlaceAssign,
    mirlite.resolvePlace?, h_envD, mirlite.resolvePlaceAcc, h_envS,
    mirlite.evalRExpr] at h_step
  cases h_ref_src : MSB.ref s_mir.perms bS.addr (blockSize τ) bS.tag kind prot mask with
  | error e => rw [h_ref_src] at h_step; simp at h_step
  | ok pr =>
      obtain ⟨perms', freshTag⟩ := pr
      rw [h_ref_src] at h_step
      simp only at h_step
      -- §2 the retag on the target, with ρt extended at the fresh pair
      obtain ⟨tgtPerms, h_ref_tgt, h_fresh_eq, h_incr_t, h_wf_t', h_tbd', h_psim'⟩ :=
        sb_ref_respects_PermSim h_psim h_wf_t h_tbd h_rtS h_nwS h_ref_src
      subst h_fresh_eq
      have h_rt_new : (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag)
          s_mir.perms.NextTag = some s_osea.perms.NextTag :=
        TagRenameMap.extend_self _ _ _
      have h0 : wildcardTag < s_mir.perms.NextTag := (h_tbd _ _ h_wf_t.2).1
      have h_nw_new : (s_mir.perms.NextTag == wildcardTag) = false := by grind
      have h_rtD' : (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag) bD.tag
          = some tagD := h_incr_t _ _ h_rtD
      -- §3 the fragment and its two instructions
      have h_stmtRun := compileStmt_ref_local_local_run (cs := csPrefix) kind prot mask
        h_piD h_piS
      obtain ⟨stmtOut, h_stmtOut⟩ :=
        compileStmt_ref_local_local_value (cs := csPrefix) kind prot mask h_piD h_piS
      have h_code1 : compProg s_osea.pc
          = some (Instr.Assgn (Register.R csPrefix.nextReg)
              (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)) := by
        rw [h_pc]
        refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
        · rw [h_stmtRun]
          simp only [emit, List.length_cons, List.length_nil]
          omega
        · rw [h_stmtRun]
          rw [emit_code_lt_nextLabel _ _ (by
            simp only [emit, List.length_cons, List.length_nil]; omega)]
          have h := emit_code_at_new { csPrefix with nextReg := csPrefix.nextReg + 1 }
            [Instr.Assgn (Register.R csPrefix.nextReg)
              (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)] (k := 0) (by simp)
          simpa using h
      have h_code2 : compProg (s_osea.pc + 1)
          = some (Instr.RStore obseq.TyVal.PTy (Register.R csPrefix.nextReg) dstReg) := by
        rw [h_pc]
        refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
        · rw [h_stmtRun]
          simp only [emit, List.length_cons, List.length_nil]
          omega
        · rw [h_stmtRun]
          simp [emit]
      -- §4 execute the Borrow
      have h_ref_tgt' : MSB.ref s_osea.perms (bS.addr + 0 + 0) (blockSize τ) tagS kind prot mask
          = .ok (tgtPerms, s_osea.perms.NextTag) := by
        simpa using h_ref_tgt
      have h_run1 := runN_Assgn_Borrow_step compProg s_osea
        (Register.R csPrefix.nextReg) srcReg kind prot mask (blockSize τ) 0
        h_code1 h_entryS (by
          show bS.addr + 0 + 0 + blockSize τ ≤ bS.addr + blockSize τ
          simp only [Nat.add_zero]
          exact Nat.le_refl _) h_ref_tgt'
      -- §5 the pointer write: source side destructured, target via BRIDGE 2
      have h_w := h_step
      simp only [mirlite.writeResolvedPlace] at h_w
      split at h_w
      · simp at h_w
      · rename_i h_nb
        split at h_w
        · rename_i perms'' h_useMut_src
          cases h_w
          obtain ⟨p2, h_useMut_tgt, h_psim2⟩ :=
            sb_write_respects_PermSim h_psim' h_wf_t' h_rtD' h_nwD h_useMut_src
          have h_regne : dstReg ≠ Register.R csPrefix.nextReg := by
            cases dstReg with
            | R n =>
                have h_lt := h_prb _ _ _ h_piD
                grind [RegisterBelow]
          -- the post-Borrow register file
          have h_entryD1 : PtrRegisterEntry
              (oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
                (obseq.TyVal.PTy, [Val.Ptr bS.addr (0 + 0) (blockSize τ) s_osea.perms.NextTag]))
              dstReg bD.addr (bD.addr - bD.addr) (blockSize (obseq.LayoutTy.PtrL τ)) tagD := by
            rw [Nat.sub_self]
            show oseair.RegMap.lookup _ _ = _
            rw [RegMap.lookup_insert_ne _ h_regne]
            exact h_entryD
          obtain ⟨h_wtp, h_sms'⟩ :=
            writeThroughPtr_sim (τ := obseq.LayoutTy.PtrL τ)
              (s_osea :=
                { s_osea with
                    perms := tgtPerms,
                    reg := oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
                      (obseq.TyVal.PTy,
                        [Val.Ptr bS.addr (0 + 0) (blockSize τ) s_osea.perms.NextTag]),
                    pc := s_osea.pc + 1 })
              (resolved := { addr := bD.addr, tag := bD.tag, allocBase := bD.addr,
                             allocSize := blockSize (obseq.LayoutTy.PtrL τ) })
              "RStore Invalid Regs"
              [mirlite.MemValue.ptrVal bS.addr (bS.addr - bS.addr) (blockSize τ) s_mir.perms.NextTag]
              [Val.Ptr bS.addr (0 + 0) (blockSize τ) s_osea.perms.NextTag] rfl
              ⟨⟨h_raS, by simp, rfl, h_rt_new, h_nw_new,
                h_domS⟩, trivial⟩
              h_id_a h_entryD1 h_useMut_tgt
              (by exact SourceMemSim.rename_mono (AddrRenameIncr.refl ρa) h_incr_t h_sms)
              (Nat.le_refl _)
              (fun k hk => by
                simp [blockSize, Nat.lt_one_iff] at hk
                subst hk
                exact h_raD)
              h_step
          have h_run2 := runN_RStore_step compProg _ _ obseq.TyVal.PTy
            (Register.R csPrefix.nextReg) dstReg _ _ h_code2
            (RegMap.lookup_insert_self _ _ _)
            (by rw [RegMap.lookup_insert_ne _ h_regne]; exact h_entryD)
            h_wtp
          have h_run := (oseair_runN_add 1 1 s_osea compProg _ h_run1).trans h_run2
          -- §6 rebuild the invariant under the extended ρt
          refine ⟨_, _, 1 + 1, h_incr_t, h_run, ?_⟩
          refine ⟨CheckedCompilerM.run
            (compileStmtChecked
              (Stmt.assign (.local dstLoc) (.ref kind prot mask (.local srcLoc)))) csPrefix,
            ⟨prefixCompileState_succ h_csAt h_stmt h_stmtOut, ?_⟩, ?_, h_sms', h_psim2,
            h_id_a, h_wf_t', ?_, ?_, ?_, ?_⟩
          · -- label agreement at pc+2
            show s_osea.pc + 1 + 1 = _
            rw [h_pc, h_stmtRun]
            simp [emit]
          · -- LocalBindingSim: env unchanged; fresh temp register; ρt grew
            refine LocalBindingSim.placeRegMap_congr ?_
              (LocalBindingSim.insert_fresh_reg
                (LocalBindingSim.rename_mono (AddrRenameIncr.refl ρa) h_incr_t h_lbs)
                h_prb (Nat.le_refl _) rfl)
            rw [h_stmtRun]
            rfl
          · -- TagRenameBounded: the write mints nothing beyond the retag's tag
            show TagRenameBounded _ perms''.NextTag p2.NextTag
            rw [sb_write_NextTag h_useMut_src, sb_write_NextTag h_useMut_tgt]
            exact h_tbd'
          · -- AllocLockstep: stores only
            simp only [AllocLockstep, mirlite_writeWordSeq_addrStart,
              oseair_writeWordSeq_addrStart]
            exact h_alloc
          · -- UnboundLocalsUnmapped: env and placeRegMap both unchanged
            intro τ' loc' h_none
            rw [h_stmtRun, getPlaceInfo_emit, getPlaceInfo_emit]
            exact h_unmap loc' h_none
          · -- PlaceRegMapBound: placeRegMap unchanged, nextReg grew
            intro idx reg τ'' h_look
            rw [h_stmtRun] at h_look ⊢
            rw [getPlaceInfo_emit, getPlaceInfo_emit] at h_look
            refine RegisterBelow.mono ?_ (h_prb _ _ _ h_look)
            simp only [emit]
            omega
        · simp at h_w

/-- REGIME F→L, CLOSED: `&src` stored into an UNBOUND local. mirlite's
    prepare allocates the destination, so the fragment gains a leading
    root `Alloc` and BOTH renames grow — ρa by the identity pair
    (`AllocLockstep` makes the two allocators agree), and ρt TWICE in one
    statement: `sb_own` mints the destination's root tag, then `sb_ref`
    mints the reference tag. The second extension is well-formed because
    the first member hands back the `TagRenameBounded` at the intermediate
    counters, which is exactly the hypothesis the second one takes. -/
theorem ref_fresh_dst_simulation
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {τ : LayoutTy}
    {dstLoc : Local Γ (obseq.LayoutTy.PtrL τ)} {srcLoc : Local Γ τ}
    {bS : mirlite.Binding}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (compProg : oseair.Prog)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    (h_stmt : prog.get? s_mir.pc
      = some (.assign (.local dstLoc) (.ref kind prot mask (.local srcLoc))))
    (h_envD : mirlite.Env.lookup s_mir.env dstLoc = none)
    (h_envS : mirlite.Env.lookup s_mir.env srcLoc = some bS)
    (h_step : mirlite.stepStmt MSB s_mir
      (.assign (.local dstLoc) (.ref kind prot mask (.local srcLoc))) = .ok s_mir') :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' := by
  obtain ⟨csPrefix, ⟨h_csAt, h_pc⟩, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_tbd,
    h_alloc, h_unmap, h_prb⟩ := h_inv
  have h_piD : getPlaceInfo csPrefix dstLoc.idx.1 = none := h_unmap dstLoc h_envD
  obtain ⟨srcReg, baseS, tagS, h_piS, h_entryS, h_raS, h_rtS, h_nwS, h_domS⟩ :=
    h_lbs srcLoc bS h_envS
  have h_baseS : baseS = bS.addr := (h_id_a _ _ h_raS).symm
  subst h_baseS
  have h_idx_ne := ref_dst_src_idx_ne dstLoc srcLoc
  -- §1 the destination allocation
  simp only [mirlite.stepStmt, mirlite.doAssign] at h_step
  cases h_prep : mirlite.preparePlaceAssign MSB s_mir (Place.local dstLoc) with
  | err m => rw [h_prep] at h_step; simp at h_step
  | ok s1 =>
      rw [h_prep] at h_step
      -- invert prepare: the destination was unbound, so `allocateBase` ran
      have h_prep' := h_prep
      simp only [mirlite.preparePlaceAssign, mirlite.resolvePlace?, h_envD,
        mirlite.allocateRoot, mirlite.allocateBase, mirlite.allocate] at h_prep'
      cases h_own_src : MSB.own s_mir.perms s_mir.mem.addrStart
          (blockSize (obseq.LayoutTy.PtrL τ)) with
      | error e => rw [h_own_src] at h_prep'; simp at h_prep'
      | ok pr =>
          obtain ⟨permsOwned, tagD⟩ := pr
          rw [h_own_src] at h_prep'
          injection h_prep' with h_s1
          subst h_s1
          -- §2 resolve the destination (now bound) and the source (untouched)
          have hD1 : mirlite.Env.lookup
              (mirlite.Env.set s_mir.env dstLoc
                { addr := s_mir.mem.addrStart, tag := tagD }) dstLoc
              = some { addr := s_mir.mem.addrStart, tag := tagD } := by
            simp [mirlite.Env.lookup, mirlite.Env.set]
          have hS1 : mirlite.Env.lookup
              (mirlite.Env.set s_mir.env dstLoc
                { addr := s_mir.mem.addrStart, tag := tagD }) srcLoc
              = some bS := by
            simp only [mirlite.Env.lookup, mirlite.Env.set, if_neg h_idx_ne]
            exact h_envS
          simp only [mirlite.resolvePlaceAcc, hD1, mirlite.evalRExpr, hS1] at h_step
          -- §3 the retag on the source place
          cases h_ref_src : MSB.ref permsOwned bS.addr (blockSize τ) bS.tag kind prot mask with
          | error e => rw [h_ref_src] at h_step; simp at h_step
          | ok pr2 =>
              obtain ⟨perms', tagR⟩ := pr2
              rw [h_ref_src] at h_step
              simp only at h_step
              -- §4 FIRST ρt extension: the destination's root tag (sb_own)
              obtain ⟨tgtP1, h_own_tgt, h_tagD_eq, h_incr1, h_wf1, h_tbd1, h_psim1⟩ :=
                sb_own_respects_PermSim h_psim h_wf_t h_tbd h_own_src
              subst h_tagD_eq
              have h_addr_eq : s_osea.mem.addrStart = s_mir.mem.addrStart := h_alloc
              have h_szD : obseq.typeSize (layoutToTyVal (obseq.LayoutTy.PtrL τ))
                  = blockSize (obseq.LayoutTy.PtrL τ) := obseq.typeSize_layoutToTyVal _
              -- the source binding's facts move to the extended ρt
              have h_rtS1 := h_incr1 _ _ h_rtS
              -- §5 SECOND ρt extension: the reference tag (sb_ref), on top
              obtain ⟨tgtP2, h_ref_tgt, h_tagR_eq, h_incr2, h_wf2, h_tbd2, h_psim2⟩ :=
                sb_ref_respects_PermSim h_psim1 h_wf1 h_tbd1 h_rtS1 h_nwS h_ref_src
              subst h_tagR_eq
              have h_incr12 : TagRenameIncr ρt
                  (((ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag).extend
                    permsOwned.NextTag tgtP1.NextTag)) :=
                TagRenameIncr.trans h_incr1 h_incr2
              have h_rt_new : ((ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag).extend
                  permsOwned.NextTag tgtP1.NextTag) permsOwned.NextTag
                  = some tgtP1.NextTag := TagRenameMap.extend_self _ _ _
              have h_rtD_new : ((ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag).extend
                  permsOwned.NextTag tgtP1.NextTag) s_mir.perms.NextTag
                  = some s_osea.perms.NextTag :=
                h_incr2 _ _ (TagRenameMap.extend_self _ _ _)
              have h0 : wildcardTag < s_mir.perms.NextTag := (h_tbd _ _ h_wf_t.2).1
              have h_nwD : (s_mir.perms.NextTag == wildcardTag) = false := by grind
              have h1 : wildcardTag < permsOwned.NextTag := (h_tbd1 _ _ h_wf1.2).1
              have h_nwR : (permsOwned.NextTag == wildcardTag) = false := by grind
              -- §6 ρa grows too, at the identity pair
              have h_incr_a : AddrRenameIncr ρa
                  (ρa.extend s_mir.mem.addrStart s_mir.mem.addrStart) :=
                AddrRenameIncr.extend_id h_id_a _
              have h_id_a' : IdentityOnDomain
                  (ρa.extend s_mir.mem.addrStart s_mir.mem.addrStart) :=
                IdentityOnDomain.extend_id h_id_a _
              have h_ra_new : (ρa.extend s_mir.mem.addrStart s_mir.mem.addrStart)
                  s_mir.mem.addrStart = some s_mir.mem.addrStart :=
                AddrRenameMap.extend_self _ _ _
              have h_raS' := h_incr_a _ _ h_raS
              -- §7 the fragment: Alloc; Borrow; RStore
              have h_stmtRun := compileStmt_ref_fresh_local_run (cs := csPrefix)
                kind prot mask h_piD h_piS
              obtain ⟨stmtOut, h_stmtOut⟩ :=
                compileStmt_ref_fresh_local_value (cs := csPrefix) kind prot mask h_piD h_piS
              have h_code1 : compProg s_osea.pc
                  = some (Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))) := by
                rw [h_pc]
                refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
                · rw [h_stmtRun]
                  simp only [emit, setPlaceInfo, List.length_cons, List.length_nil]
                  omega
                · rw [h_stmtRun]
                  rw [emit_code_lt_nextLabel _ _ (by
                    simp only [emit, setPlaceInfo, List.length_cons, List.length_nil]; omega)]
                  rw [emit_code_lt_nextLabel _ _ (by
                    simp only [emit, setPlaceInfo, List.length_cons, List.length_nil]; omega)]
                  have h := emit_code_at_new { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))] (k := 0) (by simp)
                  simpa [setPlaceInfo] using h
              have h_code2 : compProg (s_osea.pc + 1)
                  = some (Instr.Assgn (Register.R (csPrefix.nextReg + 1))
                      (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)) := by
                rw [h_pc]
                refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
                · rw [h_stmtRun]
                  simp only [emit, setPlaceInfo, List.length_cons, List.length_nil]
                  omega
                · rw [h_stmtRun]
                  rw [emit_code_lt_nextLabel _ _ (by
                    simp only [emit, setPlaceInfo, List.length_cons, List.length_nil]; omega)]
                  have h := emit_code_at_new
                    { (setPlaceInfo
                        (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                          [Instr.Assgn (Register.R csPrefix.nextReg)
                            (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))])
                        dstLoc.idx.1 (Register.R csPrefix.nextReg, obseq.LayoutTy.PtrL τ)) with
                        nextReg := csPrefix.nextReg + 1 + 1 }
                    [Instr.Assgn (Register.R (csPrefix.nextReg + 1))
                      (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)] (k := 0) (by simp)
                  simpa [emit, setPlaceInfo] using h
              have h_code3 : compProg (s_osea.pc + 1 + 1)
                  = some (Instr.RStore obseq.TyVal.PTy (Register.R (csPrefix.nextReg + 1))
                      (Register.R csPrefix.nextReg)) := by
                rw [h_pc]
                refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
                · rw [h_stmtRun]
                  simp only [emit, setPlaceInfo, List.length_cons, List.length_nil]
                  omega
                · rw [h_stmtRun]
                  have h := emit_code_at_new
                    (emit { (setPlaceInfo
                        (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                          [Instr.Assgn (Register.R csPrefix.nextReg)
                            (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))])
                        dstLoc.idx.1 (Register.R csPrefix.nextReg, obseq.LayoutTy.PtrL τ)) with
                        nextReg := csPrefix.nextReg + 1 + 1 }
                      [Instr.Assgn (Register.R (csPrefix.nextReg + 1))
                        (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)])
                    [Instr.RStore obseq.TyVal.PTy (Register.R (csPrefix.nextReg + 1))
                      (Register.R csPrefix.nextReg)] (k := 0) (by simp)
                  simpa [emit, setPlaceInfo] using h
              -- §8 execute Alloc, then Borrow
              have h_own_tgt' : MSB.own s_osea.perms s_osea.mem.addrStart
                  (obseq.typeSize (layoutToTyVal (obseq.LayoutTy.PtrL τ)))
                  = .ok (tgtP1, s_osea.perms.NextTag) := by
                rw [h_szD, h_addr_eq]; exact h_own_tgt
              have h_run1 := runN_Assgn_Alloc_step compProg s_osea
                (Register.R csPrefix.nextReg) (layoutToTyVal (obseq.LayoutTy.PtrL τ))
                h_code1 h_own_tgt'
              have h_regne : srcReg ≠ Register.R csPrefix.nextReg := by
                cases srcReg with
                | R n => have h_lt := h_prb _ _ _ h_piS; grind [RegisterBelow]
              have h_entryS1 : PtrRegisterEntry
                  (oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
                    (obseq.TyVal.PTy, [Val.Ptr s_osea.mem.addrStart 0
                      (obseq.typeSize (layoutToTyVal (obseq.LayoutTy.PtrL τ)))
                      s_osea.perms.NextTag]))
                  srcReg bS.addr 0 (blockSize τ) tagS := by
                show oseair.RegMap.lookup _ _ = _
                rw [RegMap.lookup_insert_ne _ h_regne]
                exact h_entryS
              have h_ref_tgt' : MSB.ref tgtP1 (bS.addr + 0 + 0) (blockSize τ) tagS
                  kind prot mask = .ok (tgtP2, tgtP1.NextTag) := by simpa using h_ref_tgt
              have h_le2 : bS.addr + 0 + 0 + blockSize τ ≤ bS.addr + blockSize τ :=
                Nat.le_of_eq (by simp)
              have h_run2 := runN_Assgn_Borrow_step compProg
                { s_osea with
                    mem := (oseair.allocate s_osea.mem
                      (obseq.typeSize (layoutToTyVal (obseq.LayoutTy.PtrL τ)))).2,
                    perms := tgtP1,
                    reg := oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
                      (obseq.TyVal.PTy, [Val.Ptr s_osea.mem.addrStart 0
                        (obseq.typeSize (layoutToTyVal (obseq.LayoutTy.PtrL τ)))
                        s_osea.perms.NextTag]),
                    pc := s_osea.pc + 1 }
                (Register.R (csPrefix.nextReg + 1)) srcReg kind prot mask (blockSize τ) 0
                h_code2 h_entryS1 h_le2 h_ref_tgt'
              -- §9 the store: source side destructured, target via BRIDGE 2
              have h_w := h_step
              simp only [mirlite.writeResolvedPlace] at h_w
              split at h_w
              · simp at h_w
              · rename_i h_nb
                split at h_w
                · rename_i perms'' h_useMut_src
                  cases h_w
                  obtain ⟨p3, h_useMut_tgt, h_psim3⟩ :=
                    sb_write_respects_PermSim h_psim2 h_wf2 h_rtD_new h_nwD h_useMut_src
                  have h_regne2 : Register.R csPrefix.nextReg
                      ≠ Register.R (csPrefix.nextReg + 1) := by grind
                  have h_entryD2 : PtrRegisterEntry
                      (oseair.RegMap.insert
                        (oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
                          (obseq.TyVal.PTy, [Val.Ptr s_osea.mem.addrStart 0
                            (obseq.typeSize (layoutToTyVal (obseq.LayoutTy.PtrL τ)))
                            s_osea.perms.NextTag]))
                        (Register.R (csPrefix.nextReg + 1))
                        (obseq.TyVal.PTy, [Val.Ptr bS.addr (0 + 0) (blockSize τ)
                          tgtP1.NextTag]))
                      (Register.R csPrefix.nextReg) s_mir.mem.addrStart
                      (s_mir.mem.addrStart - s_mir.mem.addrStart)
                      (blockSize (obseq.LayoutTy.PtrL τ)) s_osea.perms.NextTag := by
                    rw [Nat.sub_self, ← h_addr_eq, ← h_szD]
                    show oseair.RegMap.lookup _ _ = _
                    rw [RegMap.lookup_insert_ne _ h_regne2]
                    exact RegMap.lookup_insert_self _ _ _
                  obtain ⟨h_wtp, h_sms'⟩ :=
                    writeThroughPtr_sim (τ := obseq.LayoutTy.PtrL τ)
                      (s_osea :=
                        { s_osea with
                            mem := (oseair.allocate s_osea.mem
                              (obseq.typeSize (layoutToTyVal (obseq.LayoutTy.PtrL τ)))).2,
                            perms := tgtP2,
                            reg := oseair.RegMap.insert
                              (oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
                                (obseq.TyVal.PTy, [Val.Ptr s_osea.mem.addrStart 0
                                  (obseq.typeSize (layoutToTyVal (obseq.LayoutTy.PtrL τ)))
                                  s_osea.perms.NextTag]))
                              (Register.R (csPrefix.nextReg + 1))
                              (obseq.TyVal.PTy, [Val.Ptr bS.addr (0 + 0) (blockSize τ)
                                tgtP1.NextTag]),
                            pc := s_osea.pc + 1 + 1 })
                      (resolved := { addr := s_mir.mem.addrStart, tag := s_mir.perms.NextTag,
                                     allocBase := s_mir.mem.addrStart,
                                     allocSize := blockSize (obseq.LayoutTy.PtrL τ) })
                      "RStore Invalid Regs"
                      [mirlite.MemValue.ptrVal bS.addr (bS.addr - bS.addr) (blockSize τ)
                        permsOwned.NextTag]
                      [Val.Ptr bS.addr (0 + 0) (blockSize τ) tgtP1.NextTag] rfl
                      ⟨⟨h_raS', by simp, rfl, h_rt_new, h_nwR,
                        fun k hk => ⟨(h_domS k hk).choose,
                          h_incr_a _ _ (h_domS k hk).choose_spec⟩⟩, trivial⟩
                      h_id_a' h_entryD2 h_useMut_tgt
                      (by exact SourceMemSim.rename_mono h_incr_a h_incr12 h_sms)
                      (Nat.le_refl _)
                      (fun k hk => by
                        simp [blockSize, Nat.lt_one_iff] at hk
                        subst hk
                        exact h_ra_new)
                      h_step
                  have h_run3 := runN_RStore_step compProg _ _ obseq.TyVal.PTy
                    (Register.R (csPrefix.nextReg + 1)) (Register.R csPrefix.nextReg) _ _
                    h_code3 (RegMap.lookup_insert_self _ _ _)
                    (by rw [RegMap.lookup_insert_ne _ h_regne2]
                        exact RegMap.lookup_insert_self _ _ _)
                    h_wtp
                  have h_run :=
                    (oseair_runN_add (1 + 1) 1 s_osea compProg _
                      ((oseair_runN_add 1 1 s_osea compProg _ h_run1).trans h_run2)).trans h_run3
                  -- §10 rebuild the invariant under both extended renames
                  refine ⟨_, _, _, 1 + 1 + 1, h_incr_a, h_incr12, h_run, ?_⟩
                  refine ⟨CheckedCompilerM.run
                    (compileStmtChecked
                      (Stmt.assign (.local dstLoc)
                        (.ref kind prot mask (.local srcLoc)))) csPrefix,
                    ⟨prefixCompileState_succ h_csAt h_stmt h_stmtOut, ?_⟩, ?_, h_sms',
                    h_psim3, h_id_a', h_wf2, ?_, ?_, ?_, ?_⟩
                  · -- label agreement at pc+3
                    show s_osea.pc + 1 + 1 + 1 = _
                    rw [h_pc, h_stmtRun]
                    simp [emit, setPlaceInfo]
                  · -- LocalBindingSim: the destination is now bound and mapped;
                    -- the others survive two fresh registers and the new entry
                    intro τ' loc' binding' h_env'
                    by_cases h_idx : loc'.idx = dstLoc.idx
                    · have h_ty : τ' = obseq.LayoutTy.PtrL τ := by
                        rw [← loc'.hTy, h_idx, dstLoc.hTy]
                      subst h_ty
                      have h_b : binding' = { addr := s_mir.mem.addrStart,
                                              tag := s_mir.perms.NextTag } := by
                        grind [mirlite.Env.lookup, mirlite.Env.set]
                      subst h_b
                      refine ⟨Register.R csPrefix.nextReg, s_mir.mem.addrStart,
                        s_osea.perms.NextTag, ?_, ?_, h_ra_new, h_rtD_new, h_nwD, ?_⟩
                      · rw [h_stmtRun, getPlaceInfo_emit, getPlaceInfo_emit,
                          getPlaceInfo_setNextReg,
                          show loc'.idx.1 = dstLoc.idx.1 from congrArg Fin.val h_idx]
                        exact getPlaceInfo_setPlaceInfo_self _ _ _
                      · show oseair.RegMap.lookup _ _ = _
                        rw [← h_addr_eq, ← h_szD, RegMap.lookup_insert_ne _ h_regne2]
                        exact RegMap.lookup_insert_self _ _ _
                      · intro k hk
                        have hk0 : k = 0 := by
                          simp [blockSize, obseq.layoutSize] at hk
                          omega
                        subst hk0
                        exact ⟨s_mir.mem.addrStart, h_ra_new⟩
                    · have h_env'' : mirlite.Env.lookup s_mir.env loc' = some binding' := by
                        grind [mirlite.Env.lookup, mirlite.Env.set]
                      obtain ⟨reg', base', tag', h_pi', h_entry', h_ra', h_rt', h_nw', h_dom'⟩ :=
                        h_lbs loc' binding' h_env''
                      have h_idxv : loc'.idx.1 ≠ dstLoc.idx.1 := by grind [Fin.ext]
                      have h_rne1 : reg' ≠ Register.R csPrefix.nextReg := by
                        cases reg' with
                        | R n => have h_lt := h_prb _ _ _ h_pi'; grind [RegisterBelow]
                      have h_rne2 : reg' ≠ Register.R (csPrefix.nextReg + 1) := by
                        cases reg' with
                        | R n => have h_lt := h_prb _ _ _ h_pi'; grind [RegisterBelow]
                      refine ⟨reg', base', tag', ?_, ?_, h_incr_a _ _ h_ra',
                        h_incr12 _ _ h_rt', h_nw',
                        fun k hk => ⟨(h_dom' k hk).choose,
                          h_incr_a _ _ (h_dom' k hk).choose_spec⟩⟩
                      · rw [h_stmtRun, getPlaceInfo_emit, getPlaceInfo_emit,
                          getPlaceInfo_setNextReg, getPlaceInfo_setPlaceInfo_ne _ h_idxv,
                          getPlaceInfo_emit]
                        exact h_pi'
                      · show oseair.RegMap.lookup _ _ = _
                        rw [RegMap.lookup_insert_ne _ h_rne2,
                          RegMap.lookup_insert_ne _ h_rne1]
                        exact h_entry'
                  · -- TagRenameBounded across the store
                    show TagRenameBounded _ perms''.NextTag p3.NextTag
                    rw [sb_write_NextTag h_useMut_src, sb_write_NextTag h_useMut_tgt]
                    exact h_tbd2
                  · -- AllocLockstep: both machines bumped by the same size, then stored
                    simp only [AllocLockstep, mirlite_writeWordSeq_addrStart,
                      oseair_writeWordSeq_addrStart, mirlite.allocate, oseair.allocate]
                    rw [h_addr_eq, h_szD]
                  · -- UnboundLocalsUnmapped: only the destination became mapped,
                    -- and it is now bound
                    intro τ' loc' h_none
                    by_cases h_idx : loc'.idx = dstLoc.idx
                    · exfalso
                      grind [mirlite.Env.lookup, mirlite.Env.set]
                    · have h_idxv : loc'.idx.1 ≠ dstLoc.idx.1 := by grind [Fin.ext]
                      have h_none' : mirlite.Env.lookup s_mir.env loc' = none := by
                        grind [mirlite.Env.lookup, mirlite.Env.set]
                      rw [h_stmtRun, getPlaceInfo_emit, getPlaceInfo_emit,
                        getPlaceInfo_setNextReg, getPlaceInfo_setPlaceInfo_ne _ h_idxv,
                        getPlaceInfo_emit]
                      exact h_unmap loc' h_none'
                  · -- PlaceRegMapBound: two fresh registers, both below nextReg+2
                    intro idx reg τ'' h_look
                    rw [h_stmtRun] at h_look ⊢
                    rw [getPlaceInfo_emit, getPlaceInfo_emit, getPlaceInfo_setNextReg] at h_look
                    by_cases h_i : idx = dstLoc.idx.1
                    · subst h_i
                      rw [getPlaceInfo_setPlaceInfo_self] at h_look
                      injection h_look with h_look'
                      have : reg = Register.R csPrefix.nextReg :=
                        (congrArg Prod.fst h_look').symm
                      subst this
                      show csPrefix.nextReg < _
                      simp only [emit, setPlaceInfo]
                      omega
                    · rw [getPlaceInfo_setPlaceInfo_ne _ h_i, getPlaceInfo_emit] at h_look
                      refine RegisterBelow.mono ?_ (h_prb _ _ _ h_look)
                      simp only [emit, setPlaceInfo]
                      omega
                · simp at h_w

/-- REGIME P→L, CLOSED: a reference to a PROJECTED FIELD of a bound local,
    stored into a bound local — `q := &mut s.f` (any kind, any offset,
    projections composed by the reassociating lowering). The same two
    instructions as L→L with the offset moved; the target `Borrow`'s
    bounds check is discharged by pure TYPING
    (`PathTo.offset_add_size_le`: a field's range fits its layout), since
    the source's `sb_ref` has no bounds check to transport. The stored
    pointer covers the WHOLE base allocation (mirlite stores
    `allocBase`/`allocSize`), which is exactly why `LocalBindingSim`
    carries the block-domain conjunct over the full block. -/
theorem ref_proj_local_simulation
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {τ σb : LayoutTy}
    {dstLoc : Local Γ (obseq.LayoutTy.PtrL τ)} {srcLoc : Local Γ σb}
    {f : PathTo σb τ}
    {bD bS : mirlite.Binding}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (compProg : oseair.Prog)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    (h_stmt : prog.get? s_mir.pc
      = some (.assign (.local dstLoc)
          (.ref kind prot mask (.proj (.local srcLoc) f))))
    (h_envD : mirlite.Env.lookup s_mir.env dstLoc = some bD)
    (h_envS : mirlite.Env.lookup s_mir.env srcLoc = some bS)
    (h_step : mirlite.stepStmt MSB s_mir
      (.assign (.local dstLoc)
        (.ref kind prot mask (.proj (.local srcLoc) f))) = .ok s_mir') :
    ∃ (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa ρt' s_mir' s_osea' := by
  obtain ⟨csPrefix, ⟨h_csAt, h_pc⟩, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_tbd,
    h_alloc, h_unmap, h_prb⟩ := h_inv
  obtain ⟨dstReg, baseD, tagD, h_piD, h_entryD, h_raD, h_rtD, h_nwD, -⟩ :=
    h_lbs dstLoc bD h_envD
  obtain ⟨srcReg, baseS, tagS, h_piS, h_entryS, h_raS, h_rtS, h_nwS, h_domS⟩ :=
    h_lbs srcLoc bS h_envS
  have h_baseD : baseD = bD.addr := (h_id_a _ _ h_raD).symm
  have h_baseS : baseS = bS.addr := (h_id_a _ _ h_raS).symm
  subst h_baseD
  subst h_baseS
  -- §1 invert the source step: both locals resolve, retag at the FIELD
  simp only [mirlite.stepStmt, mirlite.doAssign, mirlite.preparePlaceAssign,
    mirlite.resolvePlace?, h_envD, mirlite.resolvePlaceAcc, h_envS,
    mirlite.evalRExpr] at h_step
  cases h_ref_src : MSB.ref s_mir.perms (bS.addr + pathOffset f) (blockSize τ)
      bS.tag kind prot mask with
  | error e => rw [h_ref_src] at h_step; simp at h_step
  | ok pr =>
      obtain ⟨perms', freshTag⟩ := pr
      rw [h_ref_src] at h_step
      simp only at h_step
      -- §2 the retag on the target, ρt extended at the fresh pair
      obtain ⟨tgtPerms, h_ref_tgt, h_fresh_eq, h_incr_t, h_wf_t', h_tbd', h_psim'⟩ :=
        sb_ref_respects_PermSim h_psim h_wf_t h_tbd h_rtS h_nwS h_ref_src
      subst h_fresh_eq
      have h_rt_new : (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag)
          s_mir.perms.NextTag = some s_osea.perms.NextTag :=
        TagRenameMap.extend_self _ _ _
      have h0 : wildcardTag < s_mir.perms.NextTag := (h_tbd _ _ h_wf_t.2).1
      have h_nw_new : (s_mir.perms.NextTag == wildcardTag) = false := by grind
      -- §3 the fragment
      have h_stmtRun := compileStmt_ref_proj_local_run (cs := csPrefix) (f := f)
        kind prot mask h_piD h_piS
      obtain ⟨stmtOut, h_stmtOut⟩ :=
        compileStmt_ref_proj_local_value (cs := csPrefix) (f := f) kind prot mask h_piD h_piS
      have h_code1 : compProg s_osea.pc
          = some (Instr.Assgn (Register.R csPrefix.nextReg)
              (Rhs.Borrow kind prot mask (blockSize τ) srcReg (pathOffset f))) := by
        rw [h_pc]
        refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
        · rw [h_stmtRun]
          simp only [emit, List.length_cons, List.length_nil]
          omega
        · rw [h_stmtRun]
          rw [emit_code_lt_nextLabel _ _ (by
            simp only [emit, List.length_cons, List.length_nil]; omega)]
          have h := emit_code_at_new { csPrefix with nextReg := csPrefix.nextReg + 1 }
            [Instr.Assgn (Register.R csPrefix.nextReg)
              (Rhs.Borrow kind prot mask (blockSize τ) srcReg (pathOffset f))]
            (k := 0) (by simp)
          simpa using h
      have h_code2 : compProg (s_osea.pc + 1)
          = some (Instr.RStore obseq.TyVal.PTy (Register.R csPrefix.nextReg) dstReg) := by
        rw [h_pc]
        refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
        · rw [h_stmtRun]
          simp only [emit, List.length_cons, List.length_nil]
          omega
        · rw [h_stmtRun]
          have h := emit_code_at_new
            (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
              [Instr.Assgn (Register.R csPrefix.nextReg)
                (Rhs.Borrow kind prot mask (blockSize τ) srcReg (pathOffset f))])
            [Instr.RStore obseq.TyVal.PTy (Register.R csPrefix.nextReg) dstReg]
            (k := 0) (by simp)
          simpa [emit] using h
      -- §4 execute the Borrow: bounds by TYPING (field fits its layout)
      have h_le2 : bS.addr + 0 + pathOffset f + blockSize τ
          ≤ bS.addr + blockSize σb := by
        have h_fit := PathTo.offset_add_size_le f
        show bS.addr + 0 + pathOffset f + blockSize τ ≤ bS.addr + blockSize σb
        simp only [Nat.add_zero, Nat.add_assoc]
        exact Nat.add_le_add_left h_fit _
      have h_ref_tgt' : MSB.ref s_osea.perms (bS.addr + 0 + pathOffset f)
          (blockSize τ) tagS kind prot mask
          = .ok (tgtPerms, s_osea.perms.NextTag) := by
        simpa using h_ref_tgt
      have h_run1 := runN_Assgn_Borrow_step compProg s_osea
        (Register.R csPrefix.nextReg) srcReg kind prot mask (blockSize τ)
        (pathOffset f) h_code1 h_entryS h_le2 h_ref_tgt'
      -- §5 the pointer store via BRIDGE 2
      have h_w := h_step
      simp only [mirlite.writeResolvedPlace] at h_w
      split at h_w
      · simp at h_w
      · rename_i h_nb
        split at h_w
        · rename_i perms'' h_useMut_src
          cases h_w
          obtain ⟨p2, h_useMut_tgt, h_psim2⟩ :=
            sb_write_respects_PermSim h_psim' h_wf_t'
              (h_incr_t _ _ h_rtD) h_nwD h_useMut_src
          have h_regne : dstReg ≠ Register.R csPrefix.nextReg := by
            cases dstReg with
            | R n =>
                have h_lt := h_prb _ _ _ h_piD
                grind [RegisterBelow]
          have h_entryD1 : PtrRegisterEntry
              (oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
                (obseq.TyVal.PTy, [Val.Ptr bS.addr (0 + pathOffset f) (blockSize σb)
                  s_osea.perms.NextTag]))
              dstReg bD.addr (bD.addr - bD.addr) (blockSize (obseq.LayoutTy.PtrL τ)) tagD := by
            rw [Nat.sub_self]
            show oseair.RegMap.lookup _ _ = _
            rw [RegMap.lookup_insert_ne _ h_regne]
            exact h_entryD
          obtain ⟨h_wtp, h_sms'⟩ :=
            writeThroughPtr_sim (τ := obseq.LayoutTy.PtrL τ)
              (s_osea :=
                { s_osea with
                    perms := tgtPerms,
                    reg := oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
                      (obseq.TyVal.PTy,
                        [Val.Ptr bS.addr (0 + pathOffset f) (blockSize σb)
                          s_osea.perms.NextTag]),
                    pc := s_osea.pc + 1 })
              (resolved := { addr := bD.addr, tag := bD.tag, allocBase := bD.addr,
                             allocSize := blockSize (obseq.LayoutTy.PtrL τ) })
              "RStore Invalid Regs"
              [mirlite.MemValue.ptrVal bS.addr (bS.addr + pathOffset f - bS.addr)
                (blockSize σb) s_mir.perms.NextTag]
              [Val.Ptr bS.addr (0 + pathOffset f) (blockSize σb) s_osea.perms.NextTag] rfl
              ⟨⟨h_raS, by simp [Nat.add_sub_cancel_left], rfl, h_rt_new, h_nw_new,
                fun k hk => ⟨(h_domS k hk).choose,
                  AddrRenameIncr.refl ρa _ _ (h_domS k hk).choose_spec⟩⟩, trivial⟩
              h_id_a h_entryD1 h_useMut_tgt
              (by exact SourceMemSim.rename_mono (AddrRenameIncr.refl ρa) h_incr_t h_sms)
              (Nat.le_refl _)
              (fun k hk => by
                have hk0 : k = 0 := by simpa using hk
                subst hk0
                rw [Nat.add_zero]
                exact h_raD)
              h_step
          have h_run2 := runN_RStore_step compProg _ _ obseq.TyVal.PTy
            (Register.R csPrefix.nextReg) dstReg _ _ h_code2
            (RegMap.lookup_insert_self _ _ _)
            (by rw [RegMap.lookup_insert_ne _ h_regne]; exact h_entryD)
            h_wtp
          have h_run := (oseair_runN_add 1 1 s_osea compProg _ h_run1).trans h_run2
          -- §6 rebuild the invariant under the extended ρt
          refine ⟨_, _, 1 + 1, h_incr_t, h_run, ?_⟩
          refine ⟨CheckedCompilerM.run
            (compileStmtChecked
              (Stmt.assign (.local dstLoc)
                (.ref kind prot mask (.proj (.local srcLoc) f)))) csPrefix,
            ⟨prefixCompileState_succ h_csAt h_stmt h_stmtOut, ?_⟩, ?_, h_sms', h_psim2,
            h_id_a, h_wf_t', ?_, ?_, ?_, ?_⟩
          · show s_osea.pc + 1 + 1 = _
            rw [h_pc, h_stmtRun]
            simp [emit]
          · refine LocalBindingSim.placeRegMap_congr ?_
              (LocalBindingSim.insert_fresh_reg
                (LocalBindingSim.rename_mono (AddrRenameIncr.refl ρa) h_incr_t h_lbs)
                h_prb (Nat.le_refl _) rfl)
            rw [h_stmtRun]
            rfl
          · show TagRenameBounded _ perms''.NextTag p2.NextTag
            rw [sb_write_NextTag h_useMut_src, sb_write_NextTag h_useMut_tgt]
            exact h_tbd'
          · simp only [AllocLockstep, mirlite_writeWordSeq_addrStart,
              oseair_writeWordSeq_addrStart]
            exact h_alloc
          · intro τ' loc' h_none
            rw [h_stmtRun, getPlaceInfo_emit, getPlaceInfo_emit]
            exact h_unmap loc' h_none
          · intro idx reg τ'' h_look
            rw [h_stmtRun] at h_look ⊢
            rw [getPlaceInfo_emit, getPlaceInfo_emit] at h_look
            refine RegisterBelow.mono ?_ (h_prb _ _ _ h_look)
            simp only [emit]
            omega
        · simp at h_w

/-- RESIDUAL (sorried), NARROWED 2026-08-27: what remains after P→L
    closed.
    - DEREF SOURCE (`L := &kind *p`): blocked on a genuine model gap —
      the target `Borrow`'s bounds check needs `offset + blockSize τ ≤
      size` for the LOADED pointer, `MemValSim` carries no pointee-size
      well-formedness, and mirlite's `.ref` has no bounds check to
      transport. Miri DOES require a retag's range to be dereferenceable,
      so the likely fix is the deref-read pattern again: add the missing
      check to mirlite's `.ref` (model decision — see loose-ends).
    - NON-LOCAL DESTINATION: the dst `Borrow(Mut); …; Die` INTERLEAVES
      with the src retag (dst is lowered before the rhs), so BRIDGE 1
      needs a commutation argument for the op between its phases — a new
      proof pattern.
    - proj-of-proj sources / fresh roots: the flattening-transfer and
      regime-B compositions, as elsewhere. -/
theorem ref_place_residual
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {τ : LayoutTy}
    {dst : Place Γ (obseq.LayoutTy.PtrL τ)} {src : Place Γ τ}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (compProg : oseair.Prog)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    (h_stmt : prog.get? s_mir.pc = some (.assign dst (.ref kind prot mask src)))
    (h_step : mirlite.stepStmt MSB s_mir (.assign dst (.ref kind prot mask src)) = .ok s_mir') :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' := by
  sorry

/-- LEAF 3 (the dispatcher): per-statement simulation for
    `.assign dst (.ref kind prot mask src)`, decomposed by the shapes of
    the two places. Regime L→L (both bound locals, any referent size) is
    CLOSED by `ref_local_local_simulation`; the residuals are named. -/
theorem CompilerInv_step_ref
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {τ : LayoutTy}
    {dst : Place Γ (obseq.LayoutTy.PtrL τ)}
    {src : Place Γ τ}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (compProg : oseair.Prog)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    (h_stmt : prog.get? s_mir.pc = some (.assign dst (.ref kind prot mask src)))
    (h_step : mirlite.stepStmt MSB s_mir (.assign dst (.ref kind prot mask src)) = .ok s_mir') :
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
              cases h_envS : mirlite.Env.lookup s_mir.env srcLoc with
              | some bS =>
                  obtain ⟨ρt', s_osea', n, h_incr, h_run, h_inv'⟩ :=
                    ref_local_local_simulation kind prot mask compProg h_comp h_inv
                      h_stmt h_envD h_envS h_step
                  exact ⟨ρa, ρt', s_osea', n, AddrRenameIncr.refl ρa, h_incr, h_run, h_inv'⟩
              | none =>
                  -- `&src` of an unbound local: the source errs at resolution
                  exfalso
                  simp [mirlite.stepStmt, mirlite.doAssign, mirlite.preparePlaceAssign,
                    mirlite.resolvePlace?, h_envD, mirlite.resolvePlaceAcc, h_envS,
                    mirlite.evalRExpr] at h_step
          | none =>
              cases h_envS : mirlite.Env.lookup s_mir.env srcLoc with
              | some bS =>
                  exact ref_fresh_dst_simulation kind prot mask compProg h_comp h_inv
                    h_stmt h_envD h_envS h_step
              | none =>
                  -- `&src` of an unbound local: the source errs at resolution
                  exfalso
                  have h_ne := ref_dst_src_idx_ne dstLoc srcLoc
                  simp only [mirlite.stepStmt, mirlite.doAssign] at h_step
                  cases h_prep : mirlite.preparePlaceAssign MSB s_mir
                      (Place.local dstLoc) with
                  | err m => rw [h_prep] at h_step; simp at h_step
                  | ok s1 =>
                      rw [h_prep] at h_step
                      have hS1 : mirlite.Env.lookup s1.env srcLoc = none := by
                        rw [prepare_lookup_ne h_ne h_prep]; exact h_envS
                      simp only [mirlite.resolvePlaceAcc] at h_step
                      split at h_step
                      · simp at h_step
                      · simp [mirlite.evalRExpr, mirlite.resolvePlaceAcc, hS1] at h_step
      | proj sbase f =>
          cases sbase with
          | «local» srcLoc =>
              cases h_envD : mirlite.Env.lookup s_mir.env dstLoc with
              | some bD =>
                  cases h_envS : mirlite.Env.lookup s_mir.env srcLoc with
                  | some bS =>
                      -- CLOSED: `dst := &kind s.f`
                      obtain ⟨ρt', s_osea', n, h_incr, h_run, h_inv'⟩ :=
                        ref_proj_local_simulation kind prot mask compProg h_comp h_inv
                          h_stmt h_envD h_envS h_step
                      exact ⟨ρa, ρt', s_osea', n, AddrRenameIncr.refl ρa, h_incr,
                        h_run, h_inv'⟩
                  | none =>
                      exfalso
                      simp [mirlite.stepStmt, mirlite.doAssign,
                        mirlite.preparePlaceAssign, mirlite.resolvePlace?, h_envD,
                        mirlite.resolvePlaceAcc, h_envS, mirlite.evalRExpr] at h_step
              | none =>
                  exact ref_place_residual kind prot mask compProg h_comp h_inv
                    h_stmt h_step
          | proj _ _ =>
              exact ref_place_residual kind prot mask compProg h_comp h_inv h_stmt h_step
          | deref _ =>
              exact ref_place_residual kind prot mask compProg h_comp h_inv h_stmt h_step
      | deref _ => exact ref_place_residual kind prot mask compProg h_comp h_inv h_stmt h_step
  | proj _ _ => exact ref_place_residual kind prot mask compProg h_comp h_inv h_stmt h_step
  | deref _ => exact ref_place_residual kind prot mask compProg h_comp h_inv h_stmt h_step

end obseq3.proof
