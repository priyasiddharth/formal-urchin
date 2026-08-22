import obseq3.proof.common

namespace obseq3.proof

open obseq3
open obseq3.compile
open obseq3.oseair (Instr Register Rhs Val)

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
  have h_run' : (ensureLocalRegE dstLoc cs).snd.val = cs := h_run
  simp [compileStmtChecked, compileRExprToChecked, placeToBorrowRegChecked,
    h_run, h_run', h_val, h_prun, h_pval, h_pres]
  simp [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM]

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
  have h_run' : (ensureLocalRegE dstLoc cs).snd.val = cs := h_run
  simp only [compileStmtChecked, compileRExprToChecked, placeToBorrowRegChecked,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
    h_run, h_run', h_pval]
  exact ⟨_, rfl⟩

/-- LEAF SORRY 3 (BLOCKED at the model level): per-statement simulation for
    `.assign dst (.ref kind prot mask src)`.

    Everything the local→local regime needs now EXISTS: the fragment is
    `Borrow; RStore` (`compileStmt_ref_local_local_run` above — note there
    is no `Die`, because the borrow's cleanup is never emitted for a stored
    reference, so this leaf does NOT need BRIDGE 1), the retag transports
    via `sb_ref_respects_PermSim`, the `Borrow` executes via
    `runN_Assgn_Borrow_step`, and the stored pointer's `MemValSim` gets its
    referent-range obligation from the strengthened `LocalBindingSim`.

    What blocks it is the `RStore` step: `oseair.stepWith` guards on
    `srcTy != ty`, and `obseq.TyVal`'s DERIVED `BEq` is opaque to the logic
    — `(TyVal.PTy == TyVal.PTy) = true` is not provable. See the BLOCKER
    note in proof/common.lean §F and loose-ends/parked.md.

    Two further obligations are known and independent of that blocker:
    - ZST divergence: for `blockSize τ = 0` the target's `Rhs.Borrow`
      bounds check (`addr ≥ base + size`) fires while mirlite's `M.ref`
      does not, so the closed regime will carry `0 < blockSize τ` and ZSTs
      become a named residual (they are outside the conformance surface —
      `zst-field-retagging-terminates` is UNSUPPORTED).
    - proj/deref places on either side remain separate regimes. -/
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
  sorry

end obseq3.proof
