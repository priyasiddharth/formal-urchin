import obseq3.proof.common
import obseq3.proof.permsim_transport

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
  simp [compileStmtChecked, compileRExprToChecked, placeToBorrowRegChecked,
    h_run, h_val, h_prun, h_pval, h_pres]
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

/-- RESIDUAL (sorried): `&src` stored into an UNBOUND local — the
    ref analogue of const_write's regime B. Same shape: mirlite's prepare
    allocates the destination and the fragment gains a leading root
    `Alloc`, so BOTH renames grow (ρa by the identity pair via
    `AllocLockstep`, ρt twice — `sb_own` for the root, `sb_ref` for the
    reference). Every piece exists; it is the composition that is owed. -/
theorem ref_fresh_dst_residual
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {τ : LayoutTy}
    {dstLoc : Local Γ (obseq.LayoutTy.PtrL τ)} {srcLoc : Local Γ τ}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (compProg : oseair.Prog)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    (h_stmt : prog.get? s_mir.pc
      = some (.assign (.local dstLoc) (.ref kind prot mask (.local srcLoc))))
    (h_step : mirlite.stepStmt MSB s_mir
      (.assign (.local dstLoc) (.ref kind prot mask (.local srcLoc))) = .ok s_mir') :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' := by
  sorry

/-- RESIDUAL (sorried): a projected or dereferenced place on EITHER side.
    A proj source adds an offset to the `Borrow` (the same shape as
    const_write's regime C); a deref source loads through the spine first
    (`loadSpine_lowering_sim` applies); a non-local destination lowers via
    `placeToRegChecked RefKind.Mut` with a `Die` cleanup, which is where
    BRIDGE 1 finally enters for `ref`. -/
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
          | none => exact ref_fresh_dst_residual kind prot mask compProg h_comp h_inv h_stmt h_step
      | proj _ _ => exact ref_place_residual kind prot mask compProg h_comp h_inv h_stmt h_step
      | deref _ => exact ref_place_residual kind prot mask compProg h_comp h_inv h_stmt h_step
  | proj _ _ => exact ref_place_residual kind prot mask compProg h_comp h_inv h_stmt h_step
  | deref _ => exact ref_place_residual kind prot mask compProg h_comp h_inv h_stmt h_step

end obseq3.proof
