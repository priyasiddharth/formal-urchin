import obseq3.proof.common
import obseq3.proof.permsim_transport

namespace obseq3.proof

open obseq3
open obseq3.compile
open obseq3.oseair (Instr Register Rhs Val)

/-- Fragment of `dl := sl` between two bound locals: a single `Memcpy`
    (the source lowering contributes no code and no cleanup). -/
theorem compileStmt_copy_local_local_run
    {Γ : Ctx} {τ : LayoutTy} {dl sl : Local Γ τ}
    {cs : CompilerState} {dstReg srcReg : Register}
    (h_d : getPlaceInfo cs dl.idx.1 = some (dstReg, τ))
    (h_s : getPlaceInfo cs sl.idx.1 = some (srcReg, τ)) :
    CheckedCompilerM.run
        (compileStmtChecked (Stmt.assign (.local dl) (.copy (.local sl)))) cs
      = emit cs [Instr.Memcpy dstReg srcReg (layoutToTyVal τ)] ∧
    ∃ so, CheckedCompilerM.value
        (compileStmtChecked (Stmt.assign (.local dl) (.copy (.local sl)))) cs
      = Except.ok so := by
  obtain ⟨h_drun, h_dval⟩ := ensureLocalRegE_existing h_d
  obtain ⟨h_srun, srcOut, h_sval, h_sres⟩ :=
    placeToRegChecked_local_existing (kind := RefKind.Shared) h_s
  constructor
  · simp only [compileStmtChecked, compileRExprToChecked,
      CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
      CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
      CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
      h_drun, h_dval, h_srun, h_sval]
    simp [CompilerM.run, CompilerM.value, emitM, cleanupInstrs, h_sres, h_dval]
  · cases h_v : CheckedCompilerM.value
        (compileStmtChecked (Stmt.assign (.local dl) (.copy (.local sl)))) cs with
    | ok so => exact ⟨so, rfl⟩
    | error e =>
        exfalso
        simp only [compileStmtChecked, compileRExprToChecked,
          CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
          CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
          CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
          h_drun, h_dval, h_srun, h_sval] at h_v
        simp [CompilerM.run, CompilerM.value, emitM, cleanupInstrs, h_sres] at h_v

/-- CORE REGIME, CLOSED: `dl := sl` between two already-bound locals.
    Both machines perform the SAME two events in the same order — an SB
    read over the source block, then a write over the destination block —
    and move the same bytes; the target does it in one `Memcpy`. The
    proof's substance is the VALUES: `readWordSeq_sim` (which is why
    `TargetAbsentSim` exists) shows the two machines read
    `MemValSim`-related sequences, including at cells the source has
    never written, where both read `undef`. Renames do not grow: copy
    mints no tag on either machine. -/
theorem copy_local_local_simulation
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {τ : LayoutTy} {dl sl : Local Γ τ}
    {dbind sbind : mirlite.Binding}
    (compProg : oseair.Prog)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    (h_stmt : prog.get? s_mir.pc
      = some (.assign (.local dl) (.copy (.local sl))))
    (h_env_d : mirlite.Env.lookup s_mir.env dl = some dbind)
    (h_env_s : mirlite.Env.lookup s_mir.env sl = some sbind)
    (h_step : mirlite.stepStmt MSB s_mir
      (.assign (.local dl) (.copy (.local sl))) = .ok s_mir') :
    ∃ (s_osea' : oseair.State MSB) (n : Nat),
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa ρt s_mir' s_osea' := by
  obtain ⟨csPrefix, ⟨h_csAt, h_pc⟩, h_lbs, h_sms, h_abs, h_psim, h_id_a, h_wf_t,
    h_trb, h_prb⟩ := h_inv
  obtain ⟨dstReg, dbase, dtag, h_pi_d, h_entry_d, h_ra_d, h_rt_d, h_nw_d, h_dom_d⟩ :=
    h_lbs dl dbind h_env_d
  obtain ⟨srcReg, sbase, stag, h_pi_s, h_entry_s, h_ra_s, h_rt_s, h_nw_s, h_dom_s⟩ :=
    h_lbs sl sbind h_env_s
  have h_dbase : dbase = dbind.addr := (h_id_a _ _ h_ra_d).symm
  subst h_dbase
  have h_sbase : sbase = sbind.addr := (h_id_a _ _ h_ra_s).symm
  subst h_sbase
  -- source: read the source block, then write the destination block
  simp only [mirlite.stepStmt, mirlite.doAssign, mirlite.preparePlaceAssign,
    mirlite.resolvePlace?, mirlite.resolvePlaceAcc, mirlite.evalRExpr,
    h_env_d, h_env_s] at h_step
  cases h_read_src : MSB.read s_mir.perms sbind.addr (blockSize τ) sbind.tag with
  | error e => simp [h_read_src] at h_step
  | ok permsR =>
  simp only [h_read_src] at h_step
  have h_w := h_step
  simp only [mirlite.writeResolvedPlace] at h_w
  split at h_w
  · simp at h_w
  · rename_i h_nb
    split at h_w
    · rename_i perms2 h_useMut_src
      cases h_w
      -- BRIDGE 3: both events transport
      obtain ⟨p2, h_read_tgt, h_psim1⟩ :=
        sb_read_respects_PermSim h_psim h_wf_t h_rt_s h_nw_s h_read_src
      obtain ⟨p3, h_write_tgt, h_psim2⟩ :=
        sb_write_respects_PermSim h_psim1 h_wf_t h_rt_d h_nw_d h_useMut_src
      -- the two machines read related value sequences
      have h_vals : ListRel (MemValSim ρa ρt)
          (mirlite.readWordSeq s_mir.mem sbind.addr (blockSize τ))
          (oseair.readWordSeq s_osea.mem sbind.addr (blockSize τ)) := by
        refine readWordSeq_sim h_id_a h_sms h_abs (blockSize τ) sbind.addr ?_
        intro k hk
        exact h_id_a.dom_self (h_dom_s k hk)
      have h_dom_dst : ∀ k, k < (mirlite.readWordSeq s_mir.mem sbind.addr
          (blockSize τ)).length → ρa (dbind.addr + k) = some (dbind.addr + k) := by
        intro k hk
        rw [mirlite.readWordSeq_length] at hk
        exact h_id_a.dom_self (h_dom_d k hk)
      -- fragment: a single Memcpy
      obtain ⟨h_stmtRun, stmtOut, h_stmtOut⟩ :=
        compileStmt_copy_local_local_run h_pi_d h_pi_s
      have h_code : compProg s_osea.pc
          = some (Instr.Memcpy dstReg srcReg (layoutToTyVal τ)) := by
        rw [h_pc]
        refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
        · rw [h_stmtRun]
          simp [emit]
        · rw [h_stmtRun]
          have h := emit_code_at_new csPrefix
            [Instr.Memcpy dstReg srcReg (layoutToTyVal τ)] (k := 0) (by simp)
          simpa using h
      -- the block sizes the machine uses are the layout's
      have h_ts : obseq.typeSize (layoutToTyVal τ) = blockSize τ := by
        grind [blockSize, obseq.typeSize_layoutToTyVal]
      have h_entry_d' : PtrRegisterEntry s_osea.reg dstReg dbind.addr 0
          (blockSize τ) dtag := h_entry_d
      have h_entry_s' : PtrRegisterEntry s_osea.reg srcReg sbind.addr 0
          (blockSize τ) stag := h_entry_s
      have h_read_tgt' : MSB.read s_osea.perms (sbind.addr + 0)
          (obseq.typeSize (layoutToTyVal τ)) stag = .ok p2 := by
        rw [h_ts]
        simpa using h_read_tgt
      have h_write_tgt' : MSB.useMut p2 (dbind.addr + 0)
          (obseq.typeSize (layoutToTyVal τ)) dtag = .ok p3 := by
        rw [h_ts]
        simpa using h_write_tgt
      have h_run := runN_Memcpy_step compProg s_osea dstReg srcReg
        (layoutToTyVal τ) h_code h_entry_d' h_entry_s'
        (by rw [h_ts]; exact Nat.le_refl _) (by rw [h_ts]; exact Nat.le_refl _)
        h_read_tgt' h_write_tgt'
      rw [h_ts] at h_run
      refine ⟨_, 1, h_run, ?_⟩
      refine ⟨CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.local dl) (.copy (.local sl)))) csPrefix,
        ⟨prefixCompileState_succ h_csAt h_stmt h_stmtOut, ?_⟩, ?_, ?_, ?_, h_psim2,
        h_id_a, h_wf_t, ?_, ?_⟩
      · -- label agreement at pc + 1
        show s_osea.pc + 1 = _
        rw [h_pc, h_stmtRun]
        simp [emit]
      · -- LocalBindingSim: `Memcpy` touches no register
        refine LocalBindingSim.placeRegMap_congr ?_ h_lbs
        rw [h_stmtRun]
        simp [emit]
      · -- SourceMemSim: the moved bytes are related
        simpa using SourceMemSim.writeWordSeq_extend h_id_a _ _ _ _ _ h_vals
          h_dom_dst h_sms
      · -- TargetAbsentSim: a lockstep write of equal-length sequences
        exact TargetAbsentSim.writeWordSeq_extend h_id_a _ _ _ _ _
          (ListRel.length_eq h_vals) h_abs
      · -- TagRenameBound: neither event moves a counter
        show TagRenameBound ρt perms2.NextTag p3.NextTag
        rw [MSB_useMut_NextTag h_useMut_src, MSB_read_NextTag h_read_src,
          sb_write_NextTag h_write_tgt, sb_read_NextTag h_read_tgt]
        exact h_trb
      · -- PlaceRegMapBound: the fragment only emits code
        rw [h_stmtRun]
        exact h_prb
    · simp at h_w

/-- LEAF SORRY 2: per-statement simulation for `.assign dst (.copy src)`.
    Target fragment: `[dst lowering (Mut)] [src lowering (Shared)]
    Memcpy [src cleanup] [dst cleanup]`. Beyond the const-write obligations
    this needs: a `Memcpy` analog of BRIDGE 2 over `blockSize τ` cells
    (source: `M.read` at the src range then the `useMut` write; target:
    `Memcpy`'s read-then-useMut — the same two events); the `M.read`
    transport through `PermSim` (BRIDGE 3 family); and BRIDGE 1 for both
    lowerings' Borrow/Die pairs. Renames grow by `.refl`: copy mints no
    source tag, and all target-internal tags are died. -/
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
  | «local» dl =>
      cases src with
      | «local» sl =>
          cases h_env_d : mirlite.Env.lookup s_mir.env dl with
          | none =>
              -- RESIDUAL COPY-FRESH-DST: the destination local is unbound;
              -- mirlite's prepare allocated it and the fragment starts with
              -- an `Alloc`. Same blocker as regime B (lockstep allocation +
              -- the `sb_own` transport member).
              sorry
          | some dbind =>
              cases h_env_s : mirlite.Env.lookup s_mir.env sl with
              | none =>
                  -- an unbound source makes the source step fail
                  exfalso
                  simp [mirlite.stepStmt, mirlite.doAssign,
                    mirlite.preparePlaceAssign, mirlite.resolvePlace?,
                    mirlite.resolvePlaceAcc, mirlite.evalRExpr,
                    h_env_d, h_env_s] at h_step
              | some sbind =>
                  obtain ⟨s_osea', n, h_run, h_inv'⟩ :=
                    copy_local_local_simulation compProg h_comp h_inv h_stmt
                      h_env_d h_env_s h_step
                  exact ⟨ρa, ρt, s_osea', n, AddrRenameIncr.refl ρa,
                    TagRenameIncr.refl ρt, h_run, h_inv'⟩
      | proj b p =>
          -- RESIDUAL COPY-NONLOCAL-SRC: reading out of a projected place —
          -- the source lowering emits a `Borrow(Shared)` with cleanup, so
          -- the fragment is `Borrow ; Memcpy ; Die` and the cancellation is
          -- READ-flavoured: `sb_ref_use_die_cancels` is stated for
          -- Mut-and-write, so this needs its Shared-and-read sibling.
          sorry
      | deref P =>
          -- RESIDUAL COPY-DEREF-SRC: `y := *p` — the source lowering is the
          -- spine's `Load`s; composes `loadSpine_lowering_sim` with this
          -- proof's `Memcpy` step (no new keystone needed for a pure
          -- spine).
          sorry
  | proj b p =>
      -- RESIDUAL COPY-NONLOCAL-DST: a projected destination is
      -- borrow-lowered with cleanup — regime C's composition, at a
      -- `Memcpy` instead of a `CStore`.
      sorry
  | deref P =>
      -- RESIDUAL COPY-DEREF-DST: `*p := y`; the destination lowering is the
      -- spine's `Load`s followed by the `Memcpy`.
      sorry

end obseq3.proof
