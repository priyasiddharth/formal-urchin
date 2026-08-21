import obseq3.proof.const_write

namespace obseq3.proof

open obseq3
open obseq3.compile
open obseq3.oseair (Instr Register Rhs Val)

/-! # LEAF 5 — per-statement simulation for `.assign dst (.ref …)`

This is the ρt-GROWING statement: both machines mint a fresh tag, the
values differ, and the invariant is re-established under
`ρt.extend srcFresh tgtFresh`. The `sb_ref` transport
(`sb_ref_respects_PermSim`) plus the `TagRenameBound` invariant conjunct
supply the extension; `LocalBindingSim`/`SourceMemSim`/`MemValSim`
transport along `TagRenameIncr` via their `rename_mono` lemmas.

CORE REGIME (closed): `dst` an already-bound local, `src` an
already-bound local of a one-cell layout — `p = &x`. The fragment is
`Assgn tmp (Borrow …)` + `RStore`; the borrow executes via the `sb_ref`
transport, the store via BRIDGE 2 + the `sb_write` transport at the
extended map.

Residual regimes are inline named sorries in the delegation (audited in
proof/compiler.lean): REF-FRESH-DST (unbound destination local — the
regime-B blocker: `sb_own` transport + lockstep allocation),
REF-NONLOCAL-DST (projected/deref'd destination — the regime-C borrow
composition), REF-NONLOCAL-SRC (borrow through a projected/deref'd
source place), REF-WIDE-SRC (multi-cell referent needs the
allocation-domain invariant for `MemValSim`'s range conjunct). -/

/-- Fragment of `dl = &sl` with both locals bound: `Borrow` into a fresh
    temp register, then `RStore` it through the destination register. -/
theorem compileStmt_ref_local_local_run
    {Γ : Ctx} {σ : LayoutTy}
    {dl : Local Γ (obseq.LayoutTy.PtrL σ)} {sl : Local Γ σ}
    {cs : CompilerState} {dstReg srcReg : Register}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (h_d : getPlaceInfo cs dl.idx.1 = some (dstReg, obseq.LayoutTy.PtrL σ))
    (h_s : getPlaceInfo cs sl.idx.1 = some (srcReg, σ)) :
    CheckedCompilerM.run
        (compileStmtChecked (Stmt.assign (.local dl) (.ref kind prot mask (.local sl)))) cs
      = emit (emit { cs with nextReg := cs.nextReg + 1 }
          [Instr.Assgn (Register.R cs.nextReg)
            (Rhs.Borrow kind prot mask (blockSize σ) srcReg 0)])
          [Instr.RStore obseq.TyVal.PTy (Register.R cs.nextReg) dstReg] ∧
    ∃ so, CheckedCompilerM.value
        (compileStmtChecked (Stmt.assign (.local dl) (.ref kind prot mask (.local sl)))) cs
      = Except.ok so := by
  obtain ⟨h_drun, h_dval⟩ := ensureLocalRegE_existing h_d
  obtain ⟨h_srun, srcOut, h_sval, h_sres⟩ :=
    placeToRegChecked_local_existing (kind := kind) h_s
  constructor
  · simp only [compileStmtChecked, compileRExprToChecked, placeToBorrowRegChecked,
      CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
      CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
      CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
      h_drun, h_dval, h_srun, h_sval]
    simp [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM, h_sres, h_dval]
  · cases h_v : CheckedCompilerM.value
        (compileStmtChecked (Stmt.assign (.local dl) (.ref kind prot mask (.local sl)))) cs with
    | ok so => exact ⟨so, rfl⟩
    | error e =>
        exfalso
        simp only [compileStmtChecked, compileRExprToChecked, placeToBorrowRegChecked,
          CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
          CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
          CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
          h_drun, h_dval, h_srun, h_sval] at h_v
        simp [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM] at h_v

/-- CORE REGIME, CLOSED: `dl = &sl` with both locals already bound and a
    one-cell source layout. The FIRST ρt-growing statement simulation:
    ρt extends at the fresh tag pair minted by the two `M.ref` calls. -/
theorem ref_local_local_existing_simulation
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {σ : LayoutTy}
    {dl : Local Γ (obseq.LayoutTy.PtrL σ)} {sl : Local Γ σ}
    {dbind sbind : mirlite.Binding}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (compProg : oseair.Prog)
    (h_bs : blockSize σ = 1)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    (h_stmt : prog.get? s_mir.pc
      = some (.assign (.local dl) (.ref kind prot mask (.local sl))))
    (h_env_d : mirlite.Env.lookup s_mir.env dl = some dbind)
    (h_env_s : mirlite.Env.lookup s_mir.env sl = some sbind)
    (h_step : mirlite.stepStmt MSB s_mir
      (.assign (.local dl) (.ref kind prot mask (.local sl))) = .ok s_mir') :
    ∃ (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa ρt' s_mir' s_osea' := by
  obtain ⟨csPrefix, ⟨h_csAt, h_pc⟩, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_trb, h_prb⟩ := h_inv
  obtain ⟨dstReg, dbase, dtag, h_pi_d, h_entry_d, h_ra_d, h_rt_d, h_nw_d⟩ :=
    h_lbs dl dbind h_env_d
  obtain ⟨srcReg, sbase, stag, h_pi_s, h_entry_s, h_ra_s, h_rt_s, h_nw_s⟩ :=
    h_lbs sl sbind h_env_s
  have h_dbase : dbase = dbind.addr := (h_id_a _ _ h_ra_d).symm
  subst h_dbase
  have h_sbase : sbase = sbind.addr := (h_id_a _ _ h_ra_s).symm
  subst h_sbase
  -- unfold the source step down to the ref event and the final write
  simp only [mirlite.stepStmt, mirlite.doAssign, mirlite.preparePlaceAssign,
    mirlite.resolvePlace?, mirlite.resolvePlaceAcc, mirlite.evalRExpr,
    h_env_d, h_env_s] at h_step
  cases h_ref_src : MSB.ref s_mir.perms sbind.addr (blockSize σ) sbind.tag
      kind prot mask with
  | error e => simp [h_ref_src] at h_step
  | ok pr =>
  obtain ⟨perms1, freshS⟩ := pr
  simp only [h_ref_src] at h_step
  -- h_step is now the writeResolvedPlace equation; destructure a copy
  have h_w := h_step
  simp only [mirlite.writeResolvedPlace] at h_w
  split at h_w
  · simp at h_w
  · rename_i h_nb
    split at h_w
    · rename_i perms2 h_useMut_src
      cases h_w
      -- BRIDGE 3, ref member: the target retag succeeds, ρt extends
      obtain ⟨permsT1, h_ref_tgt, h_freshS, h_snt1, h_tnt1, h_psim1,
          h_wf', h_incr, h_bound1⟩ :=
        sb_ref_respects_PermSim h_psim h_wf_t h_trb h_rt_s h_nw_s.1 h_ref_src
      -- the fresh source tag is positive, so non-wildcard
      have h_freshS_nw : (freshS == wildcardTag) = false := by
        have h_pos := (h_trb _ _ h_wf_t.2).1
        grind [wildcardTag]
      -- fragment
      obtain ⟨h_stmtRun, stmtOut, h_stmtOut⟩ :=
        compileStmt_ref_local_local_run kind prot mask h_pi_d h_pi_s
      have h_code1 : compProg s_osea.pc = some (Instr.Assgn
          (Register.R csPrefix.nextReg)
          (Rhs.Borrow kind prot mask (blockSize σ) srcReg 0)) := by
        rw [h_pc]
        refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
        · rw [h_stmtRun]
          show csPrefix.nextLabel < csPrefix.nextLabel + 1 + 1
          omega
        · rw [h_stmtRun]
          rw [emit_code_lt_nextLabel _ _
            (show csPrefix.nextLabel < csPrefix.nextLabel + 1 from Nat.lt_succ_self _)]
          have h := emit_code_at_new { csPrefix with nextReg := csPrefix.nextReg + 1 }
            [Instr.Assgn (Register.R csPrefix.nextReg)
              (Rhs.Borrow kind prot mask (blockSize σ) srcReg 0)]
            (k := 0) (by simp)
          simpa using h
      have h_code2 : compProg (s_osea.pc + 1) = some
          (Instr.RStore obseq.TyVal.PTy (Register.R csPrefix.nextReg) dstReg) := by
        rw [h_pc]
        refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
        · rw [h_stmtRun]
          show csPrefix.nextLabel + 1 < csPrefix.nextLabel + 1 + 1
          omega
        · rw [h_stmtRun]
          have h := emit_code_at_new
            (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
              [Instr.Assgn (Register.R csPrefix.nextReg)
                (Rhs.Borrow kind prot mask (blockSize σ) srcReg 0)])
            [Instr.RStore obseq.TyVal.PTy (Register.R csPrefix.nextReg) dstReg]
            (k := 0) (by simp)
          simpa [emit] using h
      -- execute the Borrow
      have h_ref_tgt' : MSB.ref s_osea.perms (sbind.addr + 0 + 0) (blockSize σ)
          stag kind prot mask = .ok (permsT1, s_osea.perms.NextTag) := by
        simpa using h_ref_tgt
      have h_lt_s : sbind.addr + 0 + 0 < sbind.addr + blockSize σ := by
        rw [h_bs]
        exact Nat.lt_succ_self _
      have h_run1 := runN_Assgn_Borrow_step compProg s_osea
        (Register.R csPrefix.nextReg) srcReg kind prot mask (blockSize σ) 0
        h_code1 h_entry_s h_lt_s h_ref_tgt'
      -- the destination register survives the fresh insert
      have h_ne_tmp : dstReg ≠ Register.R csPrefix.nextReg := by
        have h_below := h_prb _ _ _ h_pi_d
        cases dstReg with
        | R m =>
            intro h_eq
            injection h_eq with h_eq
            subst h_eq
            exact absurd h_below (Nat.lt_irrefl _)
      have h_entry_d1 : PtrRegisterEntry
          (oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
            (obseq.TyVal.PTy,
              [Val.Ptr sbind.addr (0 + 0) (blockSize σ) s_osea.perms.NextTag]))
          dstReg dbind.addr (dbind.addr - dbind.addr)
          (blockSize (obseq.LayoutTy.PtrL σ)) dtag := by
        show oseair.RegMap.lookup _ dstReg = _
        rw [RegMap.lookup_insert_ne _ h_ne_tmp, Nat.sub_self]
        exact h_entry_d
      -- BRIDGE 3, write member at the extended map
      have h_rt_d' : (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag) dbind.tag
          = some dtag := h_incr _ _ h_rt_d
      obtain ⟨permsT2, h_useMut_tgt, h_psim2⟩ :=
        sb_write_respects_PermSim h_psim1 h_wf' h_rt_d' h_nw_d.1 h_useMut_src
      -- the stored pointer values are related at the extended map
      have h_mvs : MemValSim ρa (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag)
          (mirlite.MemValue.ptrVal sbind.addr (sbind.addr - sbind.addr)
            (blockSize σ) freshS)
          (Val.Ptr sbind.addr (0 + 0) (blockSize σ) s_osea.perms.NextTag) := by
        refine ⟨h_ra_s, by rw [Nat.sub_self], rfl, ?_, h_freshS_nw, ?_⟩
        · rw [h_freshS]
          exact TagRenameMap.extend_self ρt _ _
        · intro k hk
          rw [h_bs, Nat.lt_one_iff] at hk
          subst hk
          exact ⟨sbind.addr, by simpa using h_ra_s⟩
      -- BRIDGE 2: the target store through the destination register
      obtain ⟨h_wtp, h_sms'⟩ :=
        writeThroughPtr_sim (ρa := ρa)
          (ρt := ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag)
          (τ := obseq.LayoutTy.PtrL σ)
          (s_pre := { s_mir with perms := perms1 })
          (s_osea :=
            { s_osea with
                perms := permsT1,
                reg := oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
                  (obseq.TyVal.PTy,
                    [Val.Ptr sbind.addr (0 + 0) (blockSize σ) s_osea.perms.NextTag]),
                pc := s_osea.pc + 1 })
          (resolved :=
            { addr := dbind.addr, tag := dbind.tag, allocBase := dbind.addr,
              allocSize := blockSize (obseq.LayoutTy.PtrL σ) })
          "RStore Invalid Regs"
          [mirlite.MemValue.ptrVal sbind.addr (sbind.addr - sbind.addr)
            (blockSize σ) freshS]
          [Val.Ptr sbind.addr (0 + 0) (blockSize σ) s_osea.perms.NextTag]
          rfl
          ⟨h_mvs, trivial⟩ h_id_a h_entry_d1 h_useMut_tgt
          (SourceMemSim.rename_mono (AddrRenameIncr.refl ρa) h_incr h_sms)
          (Nat.le_refl _)
          (fun k hk => by
            have hk0 : k = 0 := by simp at hk; omega
            subst hk0
            simpa using h_ra_d)
          h_step
      -- execute the RStore
      have h_run2 := runN_RStore_step compProg
        ({ s_osea with
            perms := permsT1,
            reg := oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
              (obseq.TyVal.PTy,
                [Val.Ptr sbind.addr (0 + 0) (blockSize σ) s_osea.perms.NextTag]),
            pc := s_osea.pc + 1 })
        _ obseq.TyVal.PTy obseq.TyVal.PTy (Register.R csPrefix.nextReg) dstReg
        [Val.Ptr sbind.addr (0 + 0) (blockSize σ) s_osea.perms.NextTag]
        h_code2 (RegMap.lookup_insert_self _ _ _) (obseq.TyVal.bne_self _)
          h_entry_d1 h_wtp
      have h_run :=
        (oseair_runN_add 1 1 s_osea compProg _ h_run1).trans h_run2
      -- rebuild the invariant at the extended map
      refine ⟨ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag, _, 1 + 1,
        h_incr, h_run, ?_⟩
      refine ⟨CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.local dl) (.ref kind prot mask (.local sl)))) csPrefix,
        ⟨prefixCompileState_succ h_csAt h_stmt h_stmtOut, ?_⟩, ?_, h_sms', h_psim2,
        h_id_a, h_wf', ?_, ?_⟩
      · -- label agreement at pc + 1
        show s_osea.pc + 1 + 1 = _
        rw [h_pc, h_stmtRun]
        simp [emit]
      · -- LocalBindingSim: fresh register insert, extended map, same placeRegMap
        refine LocalBindingSim.placeRegMap_congr ?_
          (LocalBindingSim.rename_mono (AddrRenameIncr.refl ρa) h_incr
            (LocalBindingSim.insert_fresh_reg h_lbs h_prb (Nat.le_refl _) rfl))
        rw [h_stmtRun]
        simp [emit]
      · -- TagRenameBound at the bumped counters
        show TagRenameBound _ perms2.NextTag permsT2.NextTag
        rw [MSB_useMut_NextTag h_useMut_src, sb_write_NextTag h_useMut_tgt,
          h_snt1, h_tnt1]
        exact h_bound1
      · -- PlaceRegMapBound: placeRegMap unchanged, nextReg grew by one
        intro idx reg τ'' h_look
        rw [h_stmtRun] at h_look ⊢
        simp only [emit] at h_look ⊢
        exact RegisterBelow.mono (Nat.le_succ _) (h_prb _ _ _ h_look)
    · simp at h_w

/-- LEAF 5: per-statement simulation for
    `.assign dst (.ref kind prot mask src)` (v3 signature carries the
    protector flag and freeze mask; both land verbatim in the emitted
    `Borrow`, so no separate faithfulness obligation arises).

    The CORE regime (both places bound one-cell locals) is closed by
    `ref_local_local_existing_simulation`; the other regimes are the
    inline named sorries below (see the module docstring and the audit
    in proof/compiler.lean). -/
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
  | «local» dl =>
      cases src with
      | «local» sl =>
          cases h_env_d : mirlite.Env.lookup s_mir.env dl with
          | none =>
              -- RESIDUAL REF-FRESH-DST: the destination local is unbound;
              -- mirlite's prepare allocates it and the fragment starts with
              -- an `Alloc`. Blocked on the `sb_own` transport member and
              -- the lockstep-allocation conjunct (regime-B blocker).
              sorry
          | some dbind =>
              cases h_env_s : mirlite.Env.lookup s_mir.env sl with
              | none =>
                  -- unbound source: the source step errors, contradiction
                  exfalso
                  simp [mirlite.stepStmt, mirlite.doAssign,
                    mirlite.preparePlaceAssign, mirlite.resolvePlace?,
                    mirlite.resolvePlaceAcc, mirlite.evalRExpr,
                    h_env_d, h_env_s] at h_step
              | some sbind =>
                  by_cases h_bs : blockSize τ = 1
                  · obtain ⟨ρt', s_osea', n, h_incr, h_run, h_inv'⟩ :=
                      ref_local_local_existing_simulation kind prot mask compProg
                        h_bs h_comp h_inv h_stmt h_env_d h_env_s h_step
                    exact ⟨ρa, ρt', s_osea', n, AddrRenameIncr.refl ρa,
                      h_incr, h_run, h_inv'⟩
                  · -- RESIDUAL REF-WIDE-SRC: multi-cell referent — the
                    -- stored pointer's `MemValSim` range conjunct needs
                    -- every referent cell in ρa's domain, which requires
                    -- the (not yet carried) allocation-domain invariant.
                    sorry
      | proj base path =>
          -- RESIDUAL REF-NONLOCAL-SRC: borrow of a projected place —
          -- the source lowering computes the projected register chain
          -- before the `Borrow`; composition with the proj lowering.
          sorry
      | deref ptrPlace =>
          -- RESIDUAL REF-NONLOCAL-SRC: borrow through a dereferenced
          -- place — the source lowering is `Load`s (the spine machinery)
          -- before the `Borrow`.
          sorry
  | proj base path =>
      -- RESIDUAL REF-NONLOCAL-DST: projected destination — dst is
      -- borrow-lowered with cleanup (the regime-C composition).
      sorry
  | deref ptrPlace =>
      -- RESIDUAL REF-NONLOCAL-DST: deref'd destination.
      sorry

end obseq3.proof
