import obseq3.proof.common
import obseq3.proof.permsim_transport
import obseq3.proof.spine

/-!
Per-statement simulation for `.assign dst (.constInit v)` — port of
`obseq2/proof/const_write.lean`. The evidence lemma, the delegation
structure, REGIME A (bound local) and REGIME D1 (deref of a bound
pointer local) are fully proved; the residual regimes (B fresh local,
C projection, D2 proj-pointer place, D3 nested deref) are the audited
sorries — see the audit in `proof/compiler.lean`.
-/

namespace obseq3.proof

open obseq3
open obseq3.compile
open obseq3.oseair (Instr Register Rhs Val)

/-- From `CompilerInv` and a successful destination preparation, the checked
    compiler lowers the constant assignment at the current prefix state.
    v3 delta vs obseq2: the assign-place case runs `ensurePlaceRoot` first;
    under `PlaceInputsMapped` (from `LocalBindingSim` + resolvability) it is
    a no-op on the compiler state (`ensurePlaceRoot_run_eq_of_mapped`). -/
theorem const_write_stmt_evidence
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_pre : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {dst : Place Γ obseq.LayoutTy.NatL}
    (v : Word)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    (h_prep : mirlite.preparePlaceAssign MSB s_mir dst = .ok s_pre) :
    ∃ (csPrefix : CompilerState)
      (stmtOut : ResultWithEvidence Unit (fun _ => StmtEvidence (.assign dst (.constInit v)))),
      csAt cs0 prog s_mir.pc csPrefix ∧
      CheckedCompilerM.value (compileStmtChecked (.assign dst (.constInit v)))
        csPrefix = Except.ok stmtOut := by
  obtain ⟨csPrefix, h_label, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_tbd, h_alloc, h_unmap, h_prb⟩ := h_inv
  rcases h_label with ⟨h_csAt, h_pc⟩
  cases dst with
  | «local» loc =>
      refine ⟨csPrefix, ?_, h_csAt, ?_⟩
      · refine {
        result := (),
          evidence := StmtEvidence.assignLocal loc (.constInit v)
            (CompilerM.value (ensureLocalRegE loc) csPrefix).result
            (CompilerM.value (ensureLocalRegE loc) csPrefix).evidence
            (RExprToEvidence.constInit v)
        }
      · simp [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked, emitM, cleanupInstrs, emit_nil, CompilerM.run]
  | proj base path =>
      cases h_resolved : mirlite.resolvePlace? s_mir (.proj base path) with
      | none =>
          -- fresh-root prepare (aggregate desugar): mirlite allocated the
          -- root; the compiled `ensurePlaceRoot` allocates it too, so the
          -- lowering succeeds at the post-ensure compiler state.
          obtain ⟨dstOut, h_dstOut⟩ := placeToRegChecked_ok_of_placeInputsMapped
            (cs := CompilerM.run (ensurePlaceRoot (Place.proj base path)) csPrefix)
            (kind := RefKind.Mut) (p := .proj base path)
            (ensurePlaceRoot_maps_root _ csPrefix)
          refine ⟨csPrefix, ?_, h_csAt, ?_⟩
          · exact { result := (), evidence := StmtEvidence.assignPlace (.proj base path) (.constInit v) dstOut.result dstOut.evidence (RExprToEvidence.constInit v) }
          · simp [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked, h_dstOut]
      | some resolved =>
          have h_mapped :=
            placeInputsMapped_of_localBindingSim_resolvePlace h_lbs h_resolved
          have h_root := ensurePlaceRoot_run_eq_of_mapped
            (p := Place.proj base path) h_mapped
          rcases placeToRegChecked_ok_of_placeInputsMapped
            (cs := csPrefix) (kind := RefKind.Mut) (p := .proj base path) h_mapped
            with ⟨dstOut, h_dstOut⟩
          refine ⟨csPrefix, ?_, h_csAt, ?_⟩
          · refine {
            result := (),
            evidence := StmtEvidence.assignPlace (.proj base path) (.constInit v) dstOut.result
              dstOut.evidence (RExprToEvidence.constInit v)
          }
          · simp [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked, h_dstOut, h_root]
  | deref ptrPlace =>
      cases h_resolved : mirlite.resolvePlace? s_mir (.deref ptrPlace) with
      | none =>
          simp [mirlite.preparePlaceAssign, mirlite.allocateRoot, h_resolved] at h_prep
      | some resolved =>
          have h_mapped :=
            placeInputsMapped_of_localBindingSim_resolvePlace h_lbs h_resolved
          have h_root := ensurePlaceRoot_run_eq_of_mapped
            (p := Place.deref ptrPlace) h_mapped
          rcases placeToRegChecked_ok_of_placeInputsMapped
            (cs := csPrefix) (kind := RefKind.Mut) (p := .deref ptrPlace) h_mapped
            with ⟨dstOut, h_dstOut⟩
          refine ⟨csPrefix, ?_, h_csAt, ?_⟩
          · refine {
            result := (),
            evidence := StmtEvidence.assignPlace (.deref ptrPlace) (.constInit v) dstOut.result
              dstOut.evidence (RExprToEvidence.constInit v)
          }
          · simp [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked, h_dstOut, h_root]

/-- The compiled fragment of a constant write to an already-mapped local is
    exactly one `CStore` through the mapped register. -/
theorem compileStmt_local_existing_run
    {Γ : Ctx} {loc : Local Γ obseq.LayoutTy.NatL} {cs : CompilerState}
    {reg : Register}
    (v : Word)
    (h : getPlaceInfo cs loc.idx.1 = some (reg, obseq.LayoutTy.NatL)) :
    CheckedCompilerM.run
        (compileStmtChecked (Stmt.assign (.local loc) (.constInit v))) cs
      = emit cs [Instr.CStore obseq.TyVal.NatTy [Val.Dat v] reg] := by
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_existing h
  simp [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked, h_run, h_val]
  simp [CompilerM.run, emitM, cleanupInstrs, emit_nil]

/-- REGIME A, CLOSED: constant write to an already-bound local. The
    fragment is one `CStore`; execution is BRIDGE 2, the permission
    transport is BRIDGE 3, and the renames do not grow. -/
theorem const_write_local_existing_simulation
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {loc : Local Γ obseq.LayoutTy.NatL}
    {binding : mirlite.Binding}
    (compProg : oseair.Prog)
    (v : Word)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    (h_stmt : prog.get? s_mir.pc = some (.assign (.local loc) (.constInit v)))
    (h_env : mirlite.Env.lookup s_mir.env loc = some binding)
    (h_write : mirlite.writeResolvedPlace (τ := obseq.LayoutTy.NatL) MSB s_mir
        { addr := binding.addr, tag := binding.tag, allocBase := binding.addr, allocSize := blockSize obseq.LayoutTy.NatL }
        [mirlite.MemValue.word v] rfl = .ok s_mir') :
    ∃ (s_osea' : oseair.State MSB) (n : Nat),
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa ρt s_mir' s_osea' := by
  obtain ⟨csPrefix, ⟨h_csAt, h_pc⟩, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_tbd, h_alloc, h_unmap, h_prb⟩ := h_inv
  obtain ⟨reg, base, tag, h_pi, h_entry, h_ra, h_rt, h_nw, h_dom⟩ := h_lbs loc binding h_env
  have h_base : base = binding.addr := (h_id_a _ _ h_ra).symm
  subst h_base
  -- source permission step (a copy of h_write, destructured)
  have h_w := h_write
  simp only [mirlite.writeResolvedPlace] at h_w
  split at h_w
  · simp at h_w
  · rename_i h_nb
    split at h_w
    · rename_i perms' h_useMut_src
      cases h_w
      -- BRIDGE 3: the target useMut succeeds with PermSim-related result
      obtain ⟨p2, h_useMut_tgt, h_psim'⟩ :=
        sb_write_respects_PermSim h_psim h_wf_t h_rt h_nw h_useMut_src
      -- compiled fragment and its location
      have h_stmtRun := compileStmt_local_existing_run (cs := csPrefix) v h_pi
      obtain ⟨stmtOut, h_stmtOut⟩ :
          ∃ so, CheckedCompilerM.value
            (compileStmtChecked (Stmt.assign (.local loc) (.constInit v)))
            csPrefix = Except.ok so :=
        ⟨{ result := (), evidence := StmtEvidence.assignLocal loc (.constInit v) (CompilerM.value (ensureLocalRegE loc) csPrefix).result (CompilerM.value (ensureLocalRegE loc) csPrefix).evidence (RExprToEvidence.constInit v) }, by simp [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked, emitM, cleanupInstrs, emit_nil, CompilerM.run]⟩
      have h_code : compProg s_osea.pc
          = some (Instr.CStore obseq.TyVal.NatTy [Val.Dat v] reg) := by
        rw [h_pc]
        refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
        · rw [h_stmtRun]
          simp [emit]
        · rw [h_stmtRun]
          have h_at := emit_code_at_new csPrefix
            [Instr.CStore obseq.TyVal.NatTy [Val.Dat v] reg] (k := 0) (by simp)
          simpa using h_at
      -- entry/useMut in bridge-2 shape
      have h_entry' : PtrRegisterEntry s_osea.reg reg binding.addr
          (binding.addr - binding.addr) (blockSize obseq.LayoutTy.NatL) tag := by
        rw [Nat.sub_self]
        exact h_entry
      have h_useMut' : MSB.useMut s_osea.perms binding.addr
          ([Val.Dat v].length) tag = .ok p2 := h_useMut_tgt
      obtain ⟨h_wtp, h_sms'⟩ :=
        writeThroughPtr_sim (resolved := { addr := binding.addr, tag := binding.tag, allocBase := binding.addr, allocSize := blockSize obseq.LayoutTy.NatL })
          "CStore Invalid Ptr" [mirlite.MemValue.word v] [Val.Dat v] rfl
          ⟨rfl, trivial⟩ h_id_a h_entry' h_useMut' h_sms (Nat.le_refl _)
          (fun k hk => by
            simp [Nat.lt_one_iff] at hk
            subst hk
            exact h_ra)
          h_write
      -- execute
      have h_run : oseair.runN MSB 1 s_osea compProg
          = oseair.Result.Ok { s_osea with perms := p2, mem := oseair.writeWordSeq s_osea.mem binding.addr [Val.Dat v], pc := s_osea.pc + 1 } :=
        runN_CStore_step compProg s_osea _ obseq.TyVal.NatTy [Val.Dat v] reg
          h_code rfl h_wtp
      -- rebuild the invariant
      refine ⟨_, 1, h_run, ?_⟩
      refine ⟨CheckedCompilerM.run
        (compileStmtChecked (Stmt.assign (.local loc) (.constInit v))) csPrefix,
        ⟨prefixCompileState_succ h_csAt h_stmt h_stmtOut, ?_⟩, ?_, ?_, h_psim', h_id_a, h_wf_t,
        ?_, ?_, ?_, ?_⟩
      · -- label agreement at pc+1
        rw [h_stmtRun]
        show s_osea.pc + 1 = (emit csPrefix _).nextLabel
        rw [h_pc]
        simp [emit]
      · -- LocalBindingSim carries over
        intro τ' loc' binding' h_env'
        obtain ⟨reg', base', tag', h_pi', h_entry'', h_ra', h_rt', h_nw', h_dom'⟩ :=
          h_lbs loc' binding' h_env'
        refine ⟨reg', base', tag', ?_, h_entry'', h_ra', h_rt', h_nw', h_dom'⟩
        rw [h_stmtRun]
        exact h_pi'
      · -- SourceMemSim
        exact h_sms'
      · -- TagRenameBounded: a plain write mints on neither machine, so the
        -- counters — and with them the bound — are literally unchanged
        show TagRenameBounded ρt perms'.NextTag p2.NextTag
        rw [sb_write_NextTag h_useMut_src, sb_write_NextTag h_useMut_tgt]
        exact h_tbd
      · -- AllocLockstep: a store moves neither watermark
        simp only [AllocLockstep, mirlite_writeWordSeq_addrStart,
          oseair_writeWordSeq_addrStart]
        exact h_alloc
      · -- UnboundLocalsUnmapped: the fragment only emits code, and the
        -- source env is unchanged
        intro τ' loc' h_none
        rw [h_stmtRun]
        exact h_unmap loc' h_none
      · -- PlaceRegMapBound: the fragment only emits code — `placeRegMap`
        -- and `nextReg` are untouched
        rw [h_stmtRun]
        exact h_prb
    · simp at h_w

/-- REGIME B, CLOSED: constant write to a FRESH local. The destination is
    unbound, so mirlite's `preparePlaceAssign` allocated it and the
    compiled fragment is two instructions — the root `Alloc` that
    `ensurePlaceRoot` emits, then the `CStore`. This is the only regime
    that grows BOTH renames: `AllocLockstep` makes the two allocators hand
    out the same address (so ρa extends by the identity pair) and the
    `sb_own` member mints the root tag on both machines (so ρt extends at
    the fresh pair). -/
theorem const_write_fresh_local_simulation
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_pre s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {loc : Local Γ obseq.LayoutTy.NatL}
    {resolved : mirlite.PlaceRes} {permsD : MSB.State}
    (compProg : oseair.Prog)
    (v : Word)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    (h_stmt : prog.get? s_mir.pc = some (.assign (.local loc) (.constInit v)))
    (h_env : mirlite.Env.lookup s_mir.env loc = none)
    (h_prep : mirlite.preparePlaceAssign MSB s_mir (.local loc) = .ok s_pre)
    (h_res  : mirlite.resolvePlaceAcc MSB s_pre (.local loc) = .ok (resolved, permsD))
    (h_write : mirlite.writeResolvedPlace (τ := obseq.LayoutTy.NatL)
                 MSB { s_pre with perms := permsD } resolved
                 [mirlite.MemValue.word v] rfl = .ok s_mir') :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' := by
  obtain ⟨csPrefix, ⟨h_csAt, h_pc⟩, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_tbd,
    h_alloc, h_unmap, h_prb⟩ := h_inv
  -- the compiler has not mapped this local either (the converse conjunct)
  have h_pi_none : getPlaceInfo csPrefix loc.idx.1 = none := h_unmap loc h_env
  -- §1 invert mirlite's prepare: `resolvePlace?` is none, so `allocateBase` ran
  simp only [mirlite.preparePlaceAssign, mirlite.resolvePlace?, h_env,
    mirlite.allocateRoot, mirlite.allocateBase, mirlite.allocate] at h_prep
  cases h_own_src : MSB.own s_mir.perms s_mir.mem.addrStart
      (blockSize obseq.LayoutTy.NatL) with
  | error e => rw [h_own_src] at h_prep; simp at h_prep
  | ok pr =>
      obtain ⟨permsOwned, tagS⟩ := pr
      rw [h_own_src] at h_prep
      injection h_prep with h_pre
      subst h_pre
      -- §2 resolution of the now-bound local
      have h_lookup_set : mirlite.Env.lookup
          (mirlite.Env.set s_mir.env loc
            { addr := s_mir.mem.addrStart, tag := tagS }) loc
          = some { addr := s_mir.mem.addrStart, tag := tagS } := by
        simp [mirlite.Env.lookup, mirlite.Env.set]
      simp only [mirlite.resolvePlaceAcc, h_lookup_set, Except.ok.injEq,
        Prod.mk.injEq] at h_res
      obtain ⟨h_r1, h_r2⟩ := h_res
      subst h_r1
      subst h_r2
      -- §3 the two ρ extensions
      obtain ⟨tgtPerms, h_own_tgt, h_tagS_eq, h_incr_t, h_wf_t', h_tbd', h_psim'⟩ :=
        sb_own_respects_PermSim h_psim h_wf_t h_tbd h_own_src
      subst h_tagS_eq
      have h_addr_eq : s_osea.mem.addrStart = s_mir.mem.addrStart := h_alloc
      have h_incr_a : AddrRenameIncr ρa (ρa.extend s_mir.mem.addrStart s_mir.mem.addrStart) :=
        AddrRenameIncr.extend_id h_id_a _
      have h_id_a' : IdentityOnDomain (ρa.extend s_mir.mem.addrStart s_mir.mem.addrStart) :=
        IdentityOnDomain.extend_id h_id_a _
      have h_ra_new : (ρa.extend s_mir.mem.addrStart s_mir.mem.addrStart)
          s_mir.mem.addrStart = some s_mir.mem.addrStart :=
        AddrRenameMap.extend_self _ _ _
      have h_rt_new : (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag)
          s_mir.perms.NextTag = some s_osea.perms.NextTag :=
        TagRenameMap.extend_self _ _ _
      have h0 : wildcardTag < s_mir.perms.NextTag := (h_tbd _ _ h_wf_t.2).1
      have h_nw : (s_mir.perms.NextTag == wildcardTag) = false := by grind
      -- §4 the compiled fragment: `Alloc` then `CStore`
      have h_stmtRun := compileStmt_local_fresh_run (cs := csPrefix) v h_pi_none
      obtain ⟨stmtOut, h_stmtOut⟩ :
          ∃ so, CheckedCompilerM.value
            (compileStmtChecked (Stmt.assign (.local loc) (.constInit v)))
            csPrefix = Except.ok so :=
        ⟨{ result := (),
           evidence := StmtEvidence.assignLocal loc (.constInit v)
             (CompilerM.value (ensureLocalRegE loc) csPrefix).result
             (CompilerM.value (ensureLocalRegE loc) csPrefix).evidence
             (RExprToEvidence.constInit v) },
         by simp [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked, emitM, cleanupInstrs, emit_nil, CompilerM.run]⟩
      -- §5 the two instructions, at pc and pc+1
      have h_sz : obseq.typeSize (layoutToTyVal obseq.LayoutTy.NatL)
          = blockSize obseq.LayoutTy.NatL := obseq.typeSize_layoutToTyVal _
      have h_code1 : compProg s_osea.pc
          = some (Instr.Assgn (Register.R csPrefix.nextReg)
              (Rhs.Alloc (layoutToTyVal obseq.LayoutTy.NatL))) := by
        rw [h_pc]
        refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
        · rw [h_stmtRun]
          simp only [emit, setPlaceInfo, List.length_cons, List.length_nil]
          omega
        · rw [h_stmtRun]
          rw [emit_code_lt_nextLabel _ _ (by simp [emit, setPlaceInfo])]
          show (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } _).code _ = _
          have h := emit_code_at_new { csPrefix with nextReg := csPrefix.nextReg + 1 }
            [Instr.Assgn (Register.R csPrefix.nextReg)
              (Rhs.Alloc (layoutToTyVal obseq.LayoutTy.NatL))] (k := 0) (by simp)
          simpa using h
      have h_code2 : compProg (s_osea.pc + 1)
          = some (Instr.CStore obseq.TyVal.NatTy [Val.Dat v]
              (Register.R csPrefix.nextReg)) := by
        rw [h_pc]
        refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
        · rw [h_stmtRun]
          simp only [emit, setPlaceInfo, List.length_cons, List.length_nil]
          omega
        · rw [h_stmtRun]
          have h := emit_code_at_new
            (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
              [Instr.Assgn (Register.R csPrefix.nextReg)
                (Rhs.Alloc (layoutToTyVal obseq.LayoutTy.NatL))])
              loc.idx.1 (Register.R csPrefix.nextReg, obseq.LayoutTy.NatL))
            [Instr.CStore obseq.TyVal.NatTy [Val.Dat v] (Register.R csPrefix.nextReg)]
            (k := 0) (by simp)
          simpa [emit, setPlaceInfo] using h
      -- §6 execute the `Alloc`
      have h_own_tgt' : MSB.own s_osea.perms s_osea.mem.addrStart
          (obseq.typeSize (layoutToTyVal obseq.LayoutTy.NatL))
          = .ok (tgtPerms, s_osea.perms.NextTag) := by
        rw [h_sz, h_addr_eq]
        exact h_own_tgt
      have h_run1 := runN_Assgn_Alloc_step compProg s_osea
        (Register.R csPrefix.nextReg) (layoutToTyVal obseq.LayoutTy.NatL)
        h_code1 h_own_tgt'
      -- §7 the source write, and its target mirror
      have h_w := h_write
      simp only [mirlite.writeResolvedPlace] at h_w
      split at h_w
      · simp at h_w
      · rename_i h_nb
        split at h_w
        · rename_i perms' h_useMut_src
          cases h_w
          obtain ⟨p2, h_useMut_tgt, h_psim2⟩ :=
            sb_write_respects_PermSim h_psim' h_wf_t' h_rt_new h_nw h_useMut_src
          have h_entry1 : PtrRegisterEntry
              (oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
                (obseq.TyVal.PTy, [Val.Ptr s_osea.mem.addrStart 0
                  (obseq.typeSize (layoutToTyVal obseq.LayoutTy.NatL))
                  s_osea.perms.NextTag]))
              (Register.R csPrefix.nextReg) s_mir.mem.addrStart
              (s_mir.mem.addrStart - s_mir.mem.addrStart)
              (blockSize obseq.LayoutTy.NatL) s_osea.perms.NextTag := by
            rw [Nat.sub_self, ← h_addr_eq, ← h_sz]
            exact RegMap.lookup_insert_self _ _ _
          obtain ⟨h_wtp, h_sms'⟩ :=
            writeThroughPtr_sim (τ := obseq.LayoutTy.NatL)
              (s_osea := { s_osea with
                mem := (oseair.allocate s_osea.mem
                  (obseq.typeSize (layoutToTyVal obseq.LayoutTy.NatL))).2,
                perms := tgtPerms,
                reg := oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
                  (obseq.TyVal.PTy, [Val.Ptr s_osea.mem.addrStart 0
                    (obseq.typeSize (layoutToTyVal obseq.LayoutTy.NatL))
                    s_osea.perms.NextTag]),
                pc := s_osea.pc + 1 })
              (resolved := { addr := s_mir.mem.addrStart, tag := s_mir.perms.NextTag,
                             allocBase := s_mir.mem.addrStart,
                             allocSize := blockSize obseq.LayoutTy.NatL })
              "CStore Invalid Ptr" [mirlite.MemValue.word v] [Val.Dat v] rfl
              ⟨rfl, trivial⟩ h_id_a' h_entry1 h_useMut_tgt
              (by exact SourceMemSim.rename_mono h_incr_a h_incr_t h_sms) (Nat.le_refl _)
              (fun k hk => by
                simp [Nat.lt_one_iff] at hk
                subst hk
                exact h_ra_new)
              h_write
          have h_run2 := runN_CStore_step compProg _ _
            obseq.TyVal.NatTy [Val.Dat v] (Register.R csPrefix.nextReg)
            h_code2 rfl h_wtp
          have h_run := (oseair_runN_add 1 1 s_osea compProg _ h_run1).trans h_run2
          -- §8 rebuild the invariant under both extended renames
          refine ⟨_, _, _, 1 + 1, h_incr_a, h_incr_t, h_run, ?_⟩
          refine ⟨CheckedCompilerM.run
            (compileStmtChecked (Stmt.assign (.local loc) (.constInit v))) csPrefix,
            ⟨prefixCompileState_succ h_csAt h_stmt h_stmtOut, ?_⟩, ?_, h_sms', h_psim2,
            h_id_a', h_wf_t', ?_, ?_, ?_, ?_⟩
          · -- label agreement at pc+2
            show s_osea.pc + 1 + 1 = _
            rw [h_pc, h_stmtRun]
            simp [emit, setPlaceInfo]
          · -- LocalBindingSim: the new local is bound and mapped; the old
            -- ones survive the fresh register and the new placeRegMap entry
            intro τ' loc' binding' h_env'
            by_cases h_idx : loc'.idx = loc.idx
            · have h_ty : τ' = obseq.LayoutTy.NatL := by
                rw [← loc'.hTy, h_idx, loc.hTy]
              subst h_ty
              have h_b : binding' = { addr := s_mir.mem.addrStart,
                                      tag := s_mir.perms.NextTag } := by
                grind [mirlite.Env.lookup, mirlite.Env.set]
              subst h_b
              refine ⟨Register.R csPrefix.nextReg, s_mir.mem.addrStart,
                s_osea.perms.NextTag, ?_, ?_, h_ra_new, h_rt_new, h_nw, ?_⟩
              · rw [h_stmtRun, getPlaceInfo_emit,
                  show loc'.idx.1 = loc.idx.1 from congrArg Fin.val h_idx]
                exact getPlaceInfo_setPlaceInfo_self _ _ _
              · show oseair.RegMap.lookup _ _ = _
                rw [← h_addr_eq, ← h_sz]
                exact RegMap.lookup_insert_self _ _ _
              · -- the new local's block is one cell wide, and ρa' maps it
                intro k hk
                simp only [blockSize, obseq.layoutSize, Nat.lt_one_iff] at hk
                subst hk
                exact ⟨s_mir.mem.addrStart, h_ra_new⟩
            · have h_env'' : mirlite.Env.lookup s_mir.env loc' = some binding' := by
                simpa only [mirlite.Env.lookup, mirlite.Env.set, if_neg h_idx]
                  using h_env'
              obtain ⟨reg', base', tag', h_pi', h_entry', h_ra', h_rt', h_nw', h_dom'⟩ :=
                h_lbs loc' binding' h_env''
              have h_idxv : loc'.idx.1 ≠ loc.idx.1 := by grind [Fin.ext]
              have h_regne : reg' ≠ Register.R csPrefix.nextReg := by
                cases reg' with
                | R n =>
                    have h_lt := h_prb _ _ _ h_pi'
                    grind [RegisterBelow]
              refine ⟨reg', base', tag', ?_, ?_, h_incr_a _ _ h_ra',
                h_incr_t _ _ h_rt', h_nw',
                fun k hk => ⟨(h_dom' k hk).choose,
                  h_incr_a _ _ (h_dom' k hk).choose_spec⟩⟩
              · rw [h_stmtRun, getPlaceInfo_emit,
                  getPlaceInfo_setPlaceInfo_ne _ h_idxv]
                exact h_pi'
              · show oseair.RegMap.lookup _ _ = _
                rw [RegMap.lookup_insert_ne _ h_regne]
                exact h_entry'
          · -- TagRenameBounded: the store mints nothing beyond the root tag
            show TagRenameBounded _ perms'.NextTag p2.NextTag
            rw [sb_write_NextTag h_useMut_src, sb_write_NextTag h_useMut_tgt]
            exact h_tbd'
          · -- AllocLockstep: both machines bumped by the same size, then stored
            simp only [AllocLockstep, mirlite_writeWordSeq_addrStart,
              oseair_writeWordSeq_addrStart, mirlite.allocate, oseair.allocate]
            rw [h_addr_eq, h_sz]
          · -- UnboundLocalsUnmapped: only `loc` became mapped, and it is now bound
            intro τ' loc' h_none
            by_cases h_idx : loc'.idx = loc.idx
            · exfalso
              grind [mirlite.Env.lookup, mirlite.Env.set]
            · have h_idxv : loc'.idx.1 ≠ loc.idx.1 := fun h => h_idx (Fin.ext h)
              have h_none' : mirlite.Env.lookup s_mir.env loc' = none := by
                grind [mirlite.Env.lookup, mirlite.Env.set]
              rw [h_stmtRun, getPlaceInfo_emit,
                getPlaceInfo_setPlaceInfo_ne _ h_idxv]
              exact h_unmap loc' h_none'
          · -- PlaceRegMapBound: the new entry is the fresh register itself
            intro idx reg τ'' h_look
            rw [h_stmtRun] at h_look ⊢
            rw [getPlaceInfo_emit] at h_look
            by_cases h_i : idx = loc.idx.1
            · subst h_i
              rw [getPlaceInfo_setPlaceInfo_self] at h_look
              injection h_look with h_look'
              have : reg = Register.R csPrefix.nextReg := (congrArg Prod.fst h_look').symm
              subst this
              show csPrefix.nextReg < _
              simp only [emit, setPlaceInfo]
              grind
            · rw [getPlaceInfo_setPlaceInfo_ne _ h_i] at h_look
              have := h_prb _ _ _ h_look
              refine RegisterBelow.mono ?_ this
              simp only [emit, setPlaceInfo]
              grind
        · simp at h_w

/-- The compiled fragment of a constant write through a dereferenced spine
    place is the spine's `Load`s followed by one more `Load` (of the final
    pointer) and a `CStore` through it — stated over an opaque spine run,
    with the spine's value/cleanup facts supplied by
    `loadSpine_lowering_sim`. -/
theorem compileStmt_deref_run
    {Γ : Ctx} {P : Place Γ (obseq.LayoutTy.PtrL obseq.LayoutTy.NatL)}
    {cs : CompilerState}
    {pOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared P)}
    (v : Word)
    (h_root : CompilerM.run (ensurePlaceRoot (Place.deref P)) cs = cs)
    (h_pval : CheckedCompilerM.value (placeToRegChecked RefKind.Shared P) cs = Except.ok pOut)
    (h_pclean : pOut.result.cleanup = []) :
    CheckedCompilerM.run
        (compileStmtChecked (Stmt.assign (.deref P) (.constInit v))) cs
      = emit (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) cs) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) cs).nextReg + 1 }
          [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) cs).nextReg)
            (Rhs.Load obseq.TyVal.PTy pOut.result.reg)])
          [Instr.CStore obseq.TyVal.NatTy [Val.Dat v]
            (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) cs).nextReg)] := by
  have h_deref_eq : placeToRegChecked (Γ := Γ) RefKind.Mut (.deref P)
      = (do
          let ptrOut ← placeToRegChecked RefKind.Shared P
          let ptrRes := ptrOut.result
          let loadedReg ← CheckedCompilerM.lift freshRegM
          let _ ← CheckedCompilerM.lift
            (emitM [Instr.Assgn loadedReg (Rhs.Load obseq.TyVal.PTy ptrRes.reg)])
          let _ ← CheckedCompilerM.lift (emitM (cleanupInstrs ptrRes.cleanup))
          pure {
            result := { reg := loadedReg, cleanup := [] },
            evidence := PlaceToRegEvidence.deref P ptrRes loadedReg ptrOut.evidence
          }) := by simp only [placeToRegChecked]
  simp only [compileStmtChecked, h_deref_eq, compileRExprToChecked, compileRExprPreChecked,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
    h_root, h_pval]
  simp [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM,
    cleanupInstrs, h_pclean, emit_nil]

/-! ## §C The projected-destination fragments

A projection lowers in one of two ways, and they are structurally very
different. At offset ZERO `placeToRegChecked` returns the base's register
untouched — no instruction, no cleanup — so the fragment is a bare
`CStore`, exactly regime A's. At a NONZERO offset it mints an internal
`Borrow(Mut)` into a fresh temp and records a `Die` in the cleanup, which
the assign arm emits after the store: `Borrow; CStore; Die`. That second
shape is the one BRIDGE 1 exists for. -/

/-- Zero-offset projection off a mapped local: the fragment is one
    `CStore` through the base's own register. -/
theorem compileStmt_proj_zero_run
    {Γ : Ctx} {σ : LayoutTy} {base : Place Γ σ}
    {path : PathTo σ obseq.LayoutTy.NatL} {cs : CompilerState}
    {baseOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Mut base)}
    {reg : Register}
    (h_np : ∀ (σ' : LayoutTy) (b : Place Γ σ') (q : PathTo σ' σ),
      base = b.proj q → False)
    (v : Word)
    (h_off : pathOffset path = 0)
    (h_root : CompilerM.run (ensurePlaceRoot (Place.proj base path)) cs = cs)
    (h_brun : CheckedCompilerM.run (placeToRegChecked RefKind.Mut base) cs = cs)
    (h_bval : CheckedCompilerM.value (placeToRegChecked RefKind.Mut base) cs
      = Except.ok baseOut)
    (h_bres : baseOut.result = { reg := reg, cleanup := [] }) :
    CheckedCompilerM.run
        (compileStmtChecked (Stmt.assign (.proj base path) (.constInit v))) cs
      = emit cs [Instr.CStore obseq.TyVal.NatTy [Val.Dat v] reg] := by
  have h_proj_eq : placeToRegChecked (Γ := Γ) RefKind.Mut (.proj base path)
      = (do
          let baseOut ← placeToRegChecked RefKind.Mut base
          let baseRes := baseOut.result
          let offset := pathOffset path
          if h_offset : offset = 0 then
            pure {
              result := baseRes,
              evidence := PlaceToRegEvidence.projZero base path baseRes
                baseOut.evidence h_offset
            }
          else
            let tmpReg ← CheckedCompilerM.lift freshRegM
            let _ ← CheckedCompilerM.lift
              (emitM [Instr.Assgn tmpReg
                (borrowRhs RefKind.Mut (blockSize obseq.LayoutTy.NatL) baseRes.reg offset)])
            pure {
              result := { reg := tmpReg,
                          cleanup := baseRes.cleanup ++ [(tmpReg, blockSize obseq.LayoutTy.NatL)] },
              evidence := PlaceToRegEvidence.projOffset base path baseRes tmpReg
                baseOut.evidence h_offset
            }) := placeToRegChecked_proj_root_eq path h_np
  simp only [compileStmtChecked, h_proj_eq, compileRExprToChecked, compileRExprPreChecked,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
    h_root, h_brun, h_bval, h_off, dif_pos]
  simp [CompilerM.run, CompilerM.value, emitM, cleanupInstrs, h_bres, emit_nil]

/-- Nonzero-offset projection off a mapped local: `Borrow; CStore; Die`.
    The `Die` is the cleanup the assign arm emits after the rhs — the
    only fragment so far that ends by killing a tag it minted. -/
theorem compileStmt_proj_offset_run
    {Γ : Ctx} {σ : LayoutTy} {base : Place Γ σ}
    {path : PathTo σ obseq.LayoutTy.NatL} {cs : CompilerState}
    {baseOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Mut base)}
    {reg : Register}
    (h_np : ∀ (σ' : LayoutTy) (b : Place Γ σ') (q : PathTo σ' σ),
      base = b.proj q → False)
    (v : Word)
    (h_off : pathOffset path ≠ 0)
    (h_root : CompilerM.run (ensurePlaceRoot (Place.proj base path)) cs = cs)
    (h_brun : CheckedCompilerM.run (placeToRegChecked RefKind.Mut base) cs = cs)
    (h_bval : CheckedCompilerM.value (placeToRegChecked RefKind.Mut base) cs
      = Except.ok baseOut)
    (h_bres : baseOut.result = { reg := reg, cleanup := [] }) :
    CheckedCompilerM.run
        (compileStmtChecked (Stmt.assign (.proj base path) (.constInit v))) cs
      = emit (emit (emit { cs with nextReg := cs.nextReg + 1 }
          [Instr.Assgn (Register.R cs.nextReg)
            (borrowRhs RefKind.Mut (blockSize obseq.LayoutTy.NatL) reg (pathOffset path))])
          [Instr.CStore obseq.TyVal.NatTy [Val.Dat v] (Register.R cs.nextReg)])
          [Instr.Die (Register.R cs.nextReg) (blockSize obseq.LayoutTy.NatL)] := by
  have h_proj_eq : placeToRegChecked (Γ := Γ) RefKind.Mut (.proj base path)
      = (do
          let baseOut ← placeToRegChecked RefKind.Mut base
          let baseRes := baseOut.result
          let offset := pathOffset path
          if h_offset : offset = 0 then
            pure {
              result := baseRes,
              evidence := PlaceToRegEvidence.projZero base path baseRes
                baseOut.evidence h_offset
            }
          else
            let tmpReg ← CheckedCompilerM.lift freshRegM
            let _ ← CheckedCompilerM.lift
              (emitM [Instr.Assgn tmpReg
                (borrowRhs RefKind.Mut (blockSize obseq.LayoutTy.NatL) baseRes.reg offset)])
            pure {
              result := { reg := tmpReg,
                          cleanup := baseRes.cleanup ++ [(tmpReg, blockSize obseq.LayoutTy.NatL)] },
              evidence := PlaceToRegEvidence.projOffset base path baseRes tmpReg
                baseOut.evidence h_offset
            }) := placeToRegChecked_proj_root_eq path h_np
  simp only [compileStmtChecked, h_proj_eq, compileRExprToChecked, compileRExprPreChecked,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
    h_root, h_brun, h_bval, dif_neg h_off]
  simp [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM,
    cleanupInstrs, h_bres, emit_nil]

/-- The fragment of `(*P).path := v` at ZERO offset (`P` a pointer
    place lowering with no cleanup): the projection returns the loaded
    register itself, so the fragment is D-spine's — `[P-code; Load;
    CStore]`. -/
theorem compileStmt_proj_deref_zero_run
    {Γ : Ctx} {σ : LayoutTy}
    {P : Place Γ (obseq.LayoutTy.PtrL σ)} {path : PathTo σ obseq.LayoutTy.NatL}
    {cs : CompilerState}
    {pOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared P)}
    (v : Word)
    (h_o : pathOffset path = 0)
    (h_root : CompilerM.run (ensurePlaceRoot (Place.proj (Place.deref P) path)) cs = cs)
    (h_pval : CheckedCompilerM.value (placeToRegChecked RefKind.Shared P) cs = Except.ok pOut)
    (h_pclean : pOut.result.cleanup = []) :
    CheckedCompilerM.run
        (compileStmtChecked (Stmt.assign (.proj (.deref P) path) (.constInit v))) cs
      = emit (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) cs) with
            nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) cs).nextReg + 1 }
          [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) cs).nextReg)
            (Rhs.Load obseq.TyVal.PTy pOut.result.reg)])
          [Instr.CStore obseq.TyVal.NatTy [Val.Dat v]
            (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) cs).nextReg)] := by
  have h_base_eq : placeToRegChecked (Γ := Γ) RefKind.Mut (.deref P)
      = (do
          let ptrOut ← placeToRegChecked RefKind.Shared P
          let ptrRes := ptrOut.result
          let loadedReg ← CheckedCompilerM.lift freshRegM
          let _ ← CheckedCompilerM.lift
            (emitM [Instr.Assgn loadedReg (Rhs.Load obseq.TyVal.PTy ptrRes.reg)])
          let _ ← CheckedCompilerM.lift (emitM (cleanupInstrs ptrRes.cleanup))
          pure {
            result := { reg := loadedReg, cleanup := [] },
            evidence := PlaceToRegEvidence.deref P ptrRes loadedReg ptrOut.evidence
          }) := by simp only [placeToRegChecked]
  have h_proj_eq := placeToRegChecked_proj_root_eq (Γ := Γ) (kind := RefKind.Mut)
    (base := .deref P) path (fun _ _ _ h => by cases h)
  simp only [compileStmtChecked, h_proj_eq, h_base_eq, compileRExprToChecked,
    compileRExprPreChecked,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
    h_root, h_pval, h_o, dif_pos]
  simp [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM,
    cleanupInstrs, h_pclean, emit_nil]

/-- The fragment of `(*P).path := v` (nonzero offset, `P` a pointer place
    lowering with no cleanup — e.g. a load spine):
    `[P-code; Load; Borrow(Mut); CStore; Die]`. -/
theorem compileStmt_proj_deref_run
    {Γ : Ctx} {σ : LayoutTy}
    {P : Place Γ (obseq.LayoutTy.PtrL σ)} {path : PathTo σ obseq.LayoutTy.NatL}
    {cs : CompilerState}
    {pOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared P)}
    (v : Word)
    (h_off : pathOffset path ≠ 0)
    (h_root : CompilerM.run (ensurePlaceRoot (Place.proj (Place.deref P) path)) cs = cs)
    (h_pval : CheckedCompilerM.value (placeToRegChecked RefKind.Shared P) cs = Except.ok pOut)
    (h_pclean : pOut.result.cleanup = []) :
    CheckedCompilerM.run
        (compileStmtChecked (Stmt.assign (.proj (.deref P) path) (.constInit v))) cs
      = emit (emit (emit
          { (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) cs) with
                nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) cs).nextReg + 1 }
            [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) cs).nextReg)
              (Rhs.Load obseq.TyVal.PTy pOut.result.reg)]) with
            nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) cs).nextReg + 1 + 1 }
          [Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) cs).nextReg + 1))
            (borrowRhs RefKind.Mut (blockSize obseq.LayoutTy.NatL)
              (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) cs).nextReg)
              (pathOffset path))])
          [Instr.CStore obseq.TyVal.NatTy [Val.Dat v]
            (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) cs).nextReg + 1))])
          [Instr.Die (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) cs).nextReg + 1))
            (blockSize obseq.LayoutTy.NatL)] := by
  have h_base_eq : placeToRegChecked (Γ := Γ) RefKind.Mut (.deref P)
      = (do
          let ptrOut ← placeToRegChecked RefKind.Shared P
          let ptrRes := ptrOut.result
          let loadedReg ← CheckedCompilerM.lift freshRegM
          let _ ← CheckedCompilerM.lift
            (emitM [Instr.Assgn loadedReg (Rhs.Load obseq.TyVal.PTy ptrRes.reg)])
          let _ ← CheckedCompilerM.lift (emitM (cleanupInstrs ptrRes.cleanup))
          pure {
            result := { reg := loadedReg, cleanup := [] },
            evidence := PlaceToRegEvidence.deref P ptrRes loadedReg ptrOut.evidence
          }) := by simp only [placeToRegChecked]
  have h_proj_eq := placeToRegChecked_proj_root_eq (Γ := Γ) (kind := RefKind.Mut)
    (base := .deref P) path (fun _ _ _ h => by cases h)
  simp only [compileStmtChecked, h_proj_eq, h_base_eq, compileRExprToChecked, compileRExprPreChecked,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
    h_root, h_pval]
  simp [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM,
    cleanupInstrs, h_pclean, emit_nil, h_off, borrowRhs]
  rfl

/-- The fragment of `*(base.f) := v` (nonzero offset, `base` lowering with
    no cleanup — e.g. a load spine): the pointer FIELD is borrowed Shared,
    loaded through the fresh tag, the temp dies, then the store goes
    through the loaded pointer: `[base-code; Borrow(Shared); Load; Die;
    CStore]`. -/
theorem compileStmt_deref_proj_run
    {Γ : Ctx} {σb : LayoutTy}
    {base : Place Γ σb} {f : PathTo σb (obseq.LayoutTy.PtrL obseq.LayoutTy.NatL)}
    {cs : CompilerState}
    {bOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared base)}
    (v : Word)
    (h_off : pathOffset f ≠ 0)
    (h_np : ∀ (σ' : LayoutTy) (b : Place Γ σ') (q : PathTo σ' σb),
      base = b.proj q → False)
    (h_root : CompilerM.run (ensurePlaceRoot (Place.deref (Place.proj base f))) cs = cs)
    (h_bval : CheckedCompilerM.value (placeToRegChecked RefKind.Shared base) cs
      = Except.ok bOut)
    (h_bclean : bOut.result.cleanup = []) :
    CheckedCompilerM.run
        (compileStmtChecked (Stmt.assign (.deref (.proj base f)) (.constInit v))) cs
      = emit (emit (emit
          { (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared base) cs) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared base) cs).nextReg + 1 }
              [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared base) cs).nextReg)
                (borrowRhs RefKind.Shared (blockSize (obseq.LayoutTy.PtrL obseq.LayoutTy.NatL))
                  bOut.result.reg (pathOffset f))]) with
              nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared base) cs).nextReg + 1 + 1 }
          [Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared base) cs).nextReg + 1))
            (Rhs.Load obseq.TyVal.PTy (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared base) cs).nextReg))])
          [Instr.Die (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared base) cs).nextReg)
            (blockSize (obseq.LayoutTy.PtrL obseq.LayoutTy.NatL))])
          [Instr.CStore obseq.TyVal.NatTy [Val.Dat v]
            (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared base) cs).nextReg + 1))] := by
  have h_proj_eq := placeToRegChecked_proj_root_eq (Γ := Γ) (kind := RefKind.Shared)
    (base := base) f h_np
  have h_bindD : placeToRegChecked (Γ := Γ) RefKind.Mut (.deref (.proj base f))
      = (do
          let ptrOut ← placeToRegChecked RefKind.Shared (.proj base f)
          let ptrRes := ptrOut.result
          let loadedReg ← CheckedCompilerM.lift freshRegM
          let _ ← CheckedCompilerM.lift
            (emitM [Instr.Assgn loadedReg (Rhs.Load obseq.TyVal.PTy ptrRes.reg)])
          let _ ← CheckedCompilerM.lift (emitM (cleanupInstrs ptrRes.cleanup))
          pure {
            result := { reg := loadedReg, cleanup := [] },
            evidence := PlaceToRegEvidence.deref (.proj base f) ptrRes loadedReg ptrOut.evidence
          }) := by simp only [placeToRegChecked]
  simp only [compileStmtChecked, h_bindD, h_proj_eq, compileRExprToChecked, compileRExprPreChecked,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
    h_root, h_bval]
  simp [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM,
    cleanupInstrs, h_bclean, emit_nil, h_off, borrowRhs]
  rfl

/-- REGIME D-proj, CLOSED: constant write through a DEREFERENCED pointer
    FIELD of a bound tuple local — `*(s.f) := v`. The pointer field is
    borrowed Shared, loaded through the fresh tag, and the temp dies
    before the store: the first consumer of BRIDGE 1S
    (`sb_ref_read_die_cancels`), whose net effect is exactly the parent
    read mirlite's `resolvePlaceAcc` performs at the deref. -/
theorem const_write_deref_proj_simulation
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_pre s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {σb : LayoutTy}
    {loc : Local Γ σb} {f : PathTo σb (obseq.LayoutTy.PtrL obseq.LayoutTy.NatL)}
    {binding : mirlite.Binding}
    {resolved : mirlite.PlaceRes} {permsD : MSB.State}
    (compProg : oseair.Prog)
    (v : Word)
    (h_off : pathOffset f ≠ 0)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    (h_stmt : prog.get? s_mir.pc
      = some (.assign (.deref (.proj (.local loc) f)) (.constInit v)))
    (h_env : mirlite.Env.lookup s_mir.env loc = some binding)
    (h_prep : mirlite.preparePlaceAssign MSB s_mir (.deref (.proj (.local loc) f))
      = .ok s_pre)
    (h_res  : mirlite.resolvePlaceAcc MSB s_pre (.deref (.proj (.local loc) f))
      = .ok (resolved, permsD))
    (h_write : mirlite.writeResolvedPlace (τ := obseq.LayoutTy.NatL)
                 MSB { s_pre with perms := permsD } resolved
                 [mirlite.MemValue.word v] rfl = .ok s_mir') :
    ∃ (s_osea' : oseair.State MSB) (n : Nat),
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa ρt s_mir' s_osea' := by
  have h_pre : s_pre = s_mir := by
    simp only [mirlite.preparePlaceAssign] at h_prep
    split at h_prep
    · cases h_prep; rfl
    · simp [mirlite.allocateRoot] at h_prep
  rw [h_pre] at h_res h_write
  obtain ⟨csPrefix, ⟨h_csAt, h_pc⟩, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_tbd,
    h_alloc, h_unmap, h_prb⟩ := h_inv
  obtain ⟨sReg, sBase, sTag, h_piS, h_entryS, h_raS, h_rtS, h_nwS, h_domS⟩ :=
    h_lbs loc binding h_env
  have h_baseS : sBase = binding.addr := (h_id_a _ _ h_raS).symm
  subst h_baseS
  -- source: resolve the local, add the field offset, deref-read
  simp only [mirlite.resolvePlaceAcc, h_env] at h_res
  by_cases h_qb : binding.addr + pathOffset f < binding.addr ∨
      binding.addr + pathOffset f ≥ binding.addr + blockSize σb
  · rw [if_pos h_qb] at h_res
    exact absurd h_res (by simp)
  · rw [if_neg h_qb] at h_res
    cases h_qread : MSB.read s_mir.perms (binding.addr + pathOffset f) 1 binding.tag with
    | error e => simp [h_qread] at h_res
    | ok permsB' =>
    simp only [h_qread] at h_res
    cases h_qfind : mirlite.Mem.find? s_mir.mem (binding.addr + pathOffset f) with
    | none => simp [h_qfind] at h_res
    | some mv =>
    cases mv with
    | undef => simp [h_qfind] at h_res
    | word w => simp [h_qfind] at h_res
    | ptrVal b o sz t =>
    simp only [h_qfind, Except.ok.injEq, Prod.mk.injEq] at h_res
    obtain ⟨h_r1, h_r2⟩ := h_res
    subst h_r1
    subst h_r2
    -- fragment: base is a mapped local, so its lowering is code-free
    have h_resolved : ∃ r0, mirlite.resolvePlace? s_mir
        (.deref (.proj (.local loc) f)) = some r0 := by
      simp only [mirlite.preparePlaceAssign] at h_prep
      split at h_prep
      · rename_i r0 h_r0
        exact ⟨r0, h_r0⟩
      · simp [mirlite.allocateRoot] at h_prep
    obtain ⟨r0, h_resolved⟩ := h_resolved
    have h_mapped : PlaceInputsMapped csPrefix (Place.deref (Place.proj (Place.local loc) f)) :=
      placeInputsMapped_of_localBindingSim_resolvePlace h_lbs h_resolved
    have h_root := ensurePlaceRoot_run_eq_of_mapped h_mapped
    obtain ⟨dstOut, h_dstOut⟩ := placeToRegChecked_ok_of_placeInputsMapped
      (cs := csPrefix) (kind := RefKind.Mut)
      (p := .deref (.proj (.local loc) f)) h_mapped
    obtain ⟨stmtOut, h_stmtOut⟩ : ∃ so, CheckedCompilerM.value
        (compileStmtChecked (Stmt.assign (.deref (.proj (.local loc) f)) (.constInit v)))
        csPrefix = Except.ok so :=
      ⟨{ result := (),
         evidence := StmtEvidence.assignPlace (.deref (.proj (.local loc) f)) (.constInit v)
           dstOut.result dstOut.evidence (RExprToEvidence.constInit v) },
       by simp [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked, h_dstOut, h_root]⟩
    obtain ⟨h_brun, bOut, h_bval, h_bres⟩ :=
      placeToRegChecked_local_existing (kind := RefKind.Shared) h_piS
    have h_stmtRun := compileStmt_deref_proj_run (cs := csPrefix) (bOut := bOut)
      v h_off (fun _ _ _ h => by cases h) h_root h_bval (by rw [h_bres])
    rw [h_brun] at h_stmtRun
    -- the four instructions (base emits nothing, so csPrefix is the anchor)
    have h_len4 : ((emit (emit (emit
        { (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
            [Instr.Assgn (Register.R csPrefix.nextReg)
              (borrowRhs RefKind.Shared (blockSize (obseq.LayoutTy.PtrL obseq.LayoutTy.NatL))
                bOut.result.reg (pathOffset f))]) with
            nextReg := csPrefix.nextReg + 1 + 1 }
        [Instr.Assgn (Register.R (csPrefix.nextReg + 1))
          (Rhs.Load obseq.TyVal.PTy (Register.R csPrefix.nextReg))])
        [Instr.Die (Register.R csPrefix.nextReg)
          (blockSize (obseq.LayoutTy.PtrL obseq.LayoutTy.NatL))])
        [Instr.CStore obseq.TyVal.NatTy [Val.Dat v]
          (Register.R (csPrefix.nextReg + 1))])).nextLabel
        = csPrefix.nextLabel + 4 := by
      simp only [emit, List.length_cons, List.length_nil]
    have h_code1 : compProg s_osea.pc
        = some (Instr.Assgn (Register.R csPrefix.nextReg)
            (borrowRhs RefKind.Shared (blockSize (obseq.LayoutTy.PtrL obseq.LayoutTy.NatL))
              bOut.result.reg (pathOffset f))) := by
      rw [h_pc]
      refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
      · rw [h_stmtRun, h_len4]; omega
      · rw [h_stmtRun]
        rw [emit_code_lt_nextLabel _ _ (by
          simp only [emit, List.length_cons, List.length_nil]; omega)]
        rw [emit_code_lt_nextLabel _ _ (by
          simp only [emit, List.length_cons, List.length_nil]; omega)]
        rw [emit_code_lt_nextLabel _ _ (by
          simp only [emit, List.length_cons, List.length_nil]; omega)]
        have h := emit_code_at_new { csPrefix with nextReg := csPrefix.nextReg + 1 }
          [Instr.Assgn (Register.R csPrefix.nextReg)
            (borrowRhs RefKind.Shared (blockSize (obseq.LayoutTy.PtrL obseq.LayoutTy.NatL))
              bOut.result.reg (pathOffset f))] (k := 0) (by simp)
        simpa using h
    have h_code2 : compProg (s_osea.pc + 1)
        = some (Instr.Assgn (Register.R (csPrefix.nextReg + 1))
            (Rhs.Load obseq.TyVal.PTy (Register.R csPrefix.nextReg))) := by
      rw [h_pc]
      refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
      · rw [h_stmtRun, h_len4]; omega
      · rw [h_stmtRun]
        rw [emit_code_lt_nextLabel _ _ (by
          simp only [emit, List.length_cons, List.length_nil]; omega)]
        rw [emit_code_lt_nextLabel _ _ (by
          simp only [emit, List.length_cons, List.length_nil]; omega)]
        have h := emit_code_at_new
          { (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
              [Instr.Assgn (Register.R csPrefix.nextReg)
                (borrowRhs RefKind.Shared (blockSize (obseq.LayoutTy.PtrL obseq.LayoutTy.NatL))
                  bOut.result.reg (pathOffset f))]) with
              nextReg := csPrefix.nextReg + 1 + 1 }
          [Instr.Assgn (Register.R (csPrefix.nextReg + 1))
            (Rhs.Load obseq.TyVal.PTy (Register.R csPrefix.nextReg))] (k := 0) (by simp)
        simpa [emit] using h
    have h_code3 : compProg (s_osea.pc + 1 + 1)
        = some (Instr.Die (Register.R csPrefix.nextReg)
            (blockSize (obseq.LayoutTy.PtrL obseq.LayoutTy.NatL))) := by
      rw [h_pc]
      refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
      · rw [h_stmtRun, h_len4]; omega
      · rw [h_stmtRun]
        rw [emit_code_lt_nextLabel _ _ (by
          simp only [emit, List.length_cons, List.length_nil]; omega)]
        have h := emit_code_at_new
          (emit { (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
              [Instr.Assgn (Register.R csPrefix.nextReg)
                (borrowRhs RefKind.Shared (blockSize (obseq.LayoutTy.PtrL obseq.LayoutTy.NatL))
                  bOut.result.reg (pathOffset f))]) with
              nextReg := csPrefix.nextReg + 1 + 1 }
            [Instr.Assgn (Register.R (csPrefix.nextReg + 1))
              (Rhs.Load obseq.TyVal.PTy (Register.R csPrefix.nextReg))])
          [Instr.Die (Register.R csPrefix.nextReg)
            (blockSize (obseq.LayoutTy.PtrL obseq.LayoutTy.NatL))] (k := 0) (by simp)
        simpa [emit] using h
    have h_code4 : compProg (s_osea.pc + 1 + 1 + 1)
        = some (Instr.CStore obseq.TyVal.NatTy [Val.Dat v]
            (Register.R (csPrefix.nextReg + 1))) := by
      rw [h_pc]
      refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
      · rw [h_stmtRun, h_len4]; omega
      · rw [h_stmtRun]
        have h := emit_code_at_new
          (emit (emit { (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
              [Instr.Assgn (Register.R csPrefix.nextReg)
                (borrowRhs RefKind.Shared (blockSize (obseq.LayoutTy.PtrL obseq.LayoutTy.NatL))
                  bOut.result.reg (pathOffset f))]) with
              nextReg := csPrefix.nextReg + 1 + 1 }
            [Instr.Assgn (Register.R (csPrefix.nextReg + 1))
              (Rhs.Load obseq.TyVal.PTy (Register.R csPrefix.nextReg))])
            [Instr.Die (Register.R csPrefix.nextReg)
              (blockSize (obseq.LayoutTy.PtrL obseq.LayoutTy.NatL))])
          [Instr.CStore obseq.TyVal.NatTy [Val.Dat v] (Register.R (csPrefix.nextReg + 1))]
          (k := 0) (by simp)
        simpa [emit] using h
    -- §the parent read transports; the target's Shared retag succeeds
    obtain ⟨p2, h_read_tgt, h_psim2⟩ :=
      sb_read_respects_PermSim h_psim h_wf_t h_rtS h_nwS h_qread
    obtain ⟨q1, h_ref_tgt⟩ := sb_ref_Shared_ok_of_sb_read_ok h_read_tgt
    have h_unprot := freshTag_not_protected h_psim h_tbd
    have h0 : wildcardTag < s_osea.perms.NextTag := (h_tbd _ _ h_wf_t.2).2
    have h_ntw : (s_osea.perms.NextTag == wildcardTag) = false := by grind
    -- BRIDGE 1S: ref(Shared); read(t'); die(t') ≡ the parent read
    obtain ⟨q2, q3, qAcc', h_rd1, h_die1, h_rd2, h_sm, h_ex, h_pf, h_ntle⟩ :=
      sb_ref_read_die_cancels h_ntw h_unprot h_ref_tgt
    have h_qAcc : qAcc' = p2 := by
      rw [h_read_tgt] at h_rd2
      injection h_rd2 with h_e
      exact h_e.symm
    subst h_qAcc
    -- §execute the Shared Borrow through the local's register
    have h_le1 : binding.addr + 0 + pathOffset f
        + blockSize (obseq.LayoutTy.PtrL obseq.LayoutTy.NatL)
        ≤ binding.addr + blockSize σb := by
      show binding.addr + 0 + pathOffset f + 1 ≤ binding.addr + blockSize σb
      grind
    have h_entryS' : PtrRegisterEntry s_osea.reg bOut.result.reg binding.addr 0
        (blockSize σb) sTag := by
      rw [h_bres]
      exact h_entryS
    have h_ref_tgt' : MSB.ref s_osea.perms (binding.addr + 0 + pathOffset f)
        (blockSize (obseq.LayoutTy.PtrL obseq.LayoutTy.NatL)) sTag RefKind.Shared false []
        = .ok (q1, s_osea.perms.NextTag) := by
      simpa using h_ref_tgt
    have h_run1 := runN_Assgn_Borrow_step compProg s_osea
      (Register.R csPrefix.nextReg) bOut.result.reg
      RefKind.Shared false [] (blockSize (obseq.LayoutTy.PtrL obseq.LayoutTy.NatL))
      (pathOffset f) h_code1 h_entryS' h_le1 h_ref_tgt'
    -- §execute the Load through the fresh Shared tag (BRIDGE 1S phase 2)
    have h_rd1' : MSB.read q1 (binding.addr + (0 + pathOffset f)) 1
        s_osea.perms.NextTag = .ok q2 := by
      rw [← Nat.add_assoc]
      simpa using h_rd1
    have h_entry_tmp : PtrRegisterEntry
        (oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
                (obseq.TyVal.PTy, [Val.Ptr binding.addr (0 + pathOffset f)
                  (blockSize σb) s_osea.perms.NextTag]))
        (Register.R csPrefix.nextReg) binding.addr (0 + pathOffset f)
        (blockSize σb) s_osea.perms.NextTag :=
      RegMap.lookup_insert_self _ _ _
    have h_off_lt : 0 + pathOffset f < blockSize σb := by grind
    have h_run2 := runN_Assgn_Load_ptr_step compProg
      { s_osea with
          perms := q1,
          reg := oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
                (obseq.TyVal.PTy, [Val.Ptr binding.addr (0 + pathOffset f)
                  (blockSize σb) s_osea.perms.NextTag]),
          pc := s_osea.pc + 1 }
      (Register.R (csPrefix.nextReg + 1)) (Register.R csPrefix.nextReg)
      obseq.TyVal.PTy h_code2 h_entry_tmp h_off_lt
      (by
        show MSB.read q1 (binding.addr + (0 + pathOffset f))
          (obseq.typeSize obseq.TyVal.PTy) s_osea.perms.NextTag = .ok q2
        exact h_rd1')
    -- the loaded cell holds the ρ-renamed stored pointer
    obtain ⟨addr', value', h_ra', h_find_tgt, h_mvs⟩ := h_sms _ _ h_qfind
    have h_addr' : addr' = binding.addr + pathOffset f := (h_id_a _ _ h_ra').symm
    subst h_addr'
    cases value' with
    | Undef => exact h_mvs.elim
    | Dat _ => exact h_mvs.elim
    | Ptr b2 o2 s2 t2 =>
    obtain ⟨h_b, h_o, h_s, h_t, h_tnw, h_range⟩ := h_mvs
    have h_b2 : b2 = b := (h_id_a _ _ h_b).symm
    subst h_b2
    subst h_o
    subst h_s
    have h_rws : oseair.readWordSeq s_osea.mem
        (binding.addr + (0 + pathOffset f))
        (obseq.typeSize obseq.TyVal.PTy) = [Val.Ptr b2 o2 s2 t2] := by
      rw [← Nat.add_assoc, Nat.add_zero]
      show oseair.readWordSeq s_osea.mem (binding.addr + pathOffset f) 1 = _
      simp [oseair.readWordSeq, h_find_tgt]
    -- §execute the Die (BRIDGE 1S phase 3) on the temp
    have h_die1' : MSB.die q2 (binding.addr + (0 + pathOffset f))
        (blockSize (obseq.LayoutTy.PtrL obseq.LayoutTy.NatL)) s_osea.perms.NextTag
        = .ok q3 := by
      rw [← Nat.add_assoc]
      simpa using h_die1
    have h_regne : Register.R (csPrefix.nextReg + 1)
        ≠ Register.R csPrefix.nextReg := by grind
    have h_run3 := runN_Die_step compProg
      { s_osea with
          perms := q2,
          reg := oseair.RegMap.insert
            (oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
              (obseq.TyVal.PTy, [Val.Ptr binding.addr (0 + pathOffset f)
                (blockSize σb) s_osea.perms.NextTag]))
            (Register.R (csPrefix.nextReg + 1))
            (obseq.TyVal.PTy, oseair.readWordSeq s_osea.mem
              (binding.addr + (0 + pathOffset f)) (obseq.typeSize obseq.TyVal.PTy)),
          pc := s_osea.pc + 1 + 1 }
      (Register.R csPrefix.nextReg)
      (blockSize (obseq.LayoutTy.PtrL obseq.LayoutTy.NatL))
      h_code3
      (by
        show oseair.RegMap.lookup _ _ = _
        rw [RegMap.lookup_insert_ne _ (by grind)]
        exact RegMap.lookup_insert_self _ _ _)
      h_die1'
    -- §the source write and BRIDGE 2 through the loaded pointer
    have h_w := h_write
    simp only [mirlite.writeResolvedPlace] at h_w
    split at h_w
    · simp at h_w
    · rename_i h_nb
      split at h_w
      · rename_i perms'' h_useMut_src
        cases h_w
        obtain ⟨p3, h_useMut_tgt, h_psim3⟩ :=
          sb_write_respects_PermSim (by
            obtain ⟨hs, hp, he, hn⟩ := h_psim2
            exact ⟨by rw [h_sm]; exact hs, by rw [h_pf]; exact hp,
                   by rw [h_ex]; exact he, Nat.le_trans hn h_ntle⟩)
            h_wf_t h_t h_tnw h_useMut_src
        have h_entry_loaded : PtrRegisterEntry
            (oseair.RegMap.insert
              (oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
                (obseq.TyVal.PTy, [Val.Ptr binding.addr (0 + pathOffset f)
                  (blockSize σb) s_osea.perms.NextTag]))
              (Register.R (csPrefix.nextReg + 1))
              (obseq.TyVal.PTy, [Val.Ptr b2 o2 s2 t2]))
            (Register.R (csPrefix.nextReg + 1)) b2 (b2 + o2 - b2) s2 t2 := by
          rw [Nat.add_sub_cancel_left]
          exact RegMap.lookup_insert_self _ _ _
        obtain ⟨h_wtp, h_sms'⟩ :=
          writeThroughPtr_sim (τ := obseq.LayoutTy.NatL)
            (s_osea :=
              { s_osea with
                  perms := q3,
                  reg := oseair.RegMap.insert
                    (oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
                      (obseq.TyVal.PTy, [Val.Ptr binding.addr (0 + pathOffset f)
                        (blockSize σb) s_osea.perms.NextTag]))
                    (Register.R (csPrefix.nextReg + 1))
                    (obseq.TyVal.PTy, [Val.Ptr b2 o2 s2 t2]),
                  pc := s_osea.pc + 1 + 1 + 1 })
            (resolved := { addr := b2 + o2, tag := t,
                           allocBase := b2, allocSize := s2 })
            "CStore Invalid Ptr" [mirlite.MemValue.word v] [Val.Dat v] rfl
            ⟨rfl, trivial⟩ h_id_a h_entry_loaded h_useMut_tgt (by exact h_sms)
            (Nat.le_add_right _ _)
            (fun k hk => by
              have hk0 : k = 0 := by simpa using hk
              subst hk0
              have h_o_lt : o2 < s2 := by
                have h1 := Nat.not_lt.mp h_nb
                have h2 : b2 + o2 + 1 ≤ b2 + s2 := by
                  simpa [List.length_cons, List.length_nil] using h1
                exact Nat.lt_of_succ_le (Nat.le_of_add_le_add_left h2)
              obtain ⟨a', ha'⟩ := h_range o2 h_o_lt
              have h_ida := h_id_a _ _ ha'
              rw [← h_ida] at ha'
              rw [Nat.add_zero]
              exact ha')
            h_write
        have h_run4 := runN_CStore_step compProg _ _
          obseq.TyVal.NatTy [Val.Dat v] (Register.R (csPrefix.nextReg + 1))
          h_code4 rfl h_wtp
        rw [h_rws] at h_run2 h_run3
        have h_runA := (oseair_runN_add 1 1 s_osea compProg _ h_run1).trans h_run2
        have h_runB := (oseair_runN_add (1 + 1) 1 s_osea compProg _ h_runA).trans h_run3
        have h_runC := (oseair_runN_add (1 + 1 + 1) 1 s_osea compProg _ h_runB).trans h_run4
        -- §rebuild the invariant (ρa, ρt unchanged: the minted tag died)
        refine ⟨_, 1 + 1 + 1 + 1, h_runC, ?_⟩
        refine ⟨CheckedCompilerM.run
          (compileStmtChecked (Stmt.assign (.deref (.proj (.local loc) f)) (.constInit v))) csPrefix,
          ⟨prefixCompileState_succ h_csAt h_stmt h_stmtOut, ?_⟩, ?_, ?_, h_psim3,
          h_id_a, h_wf_t, ?_, ?_, ?_, ?_⟩
        · -- label agreement at pc+4
          show s_osea.pc + 1 + 1 + 1 + 1 = _
          rw [h_pc, h_stmtRun, h_len4]
        · -- LocalBindingSim: two fresh temps, env unchanged
          intro τ' loc' binding' h_env'
          obtain ⟨reg', base', tag', h_pi', h_entry', h_ra', h_rt', h_nw', h_dom'⟩ :=
            h_lbs loc' binding' h_env'
          have h_rne1 : reg' ≠ Register.R csPrefix.nextReg := by
            cases reg' with
            | R n => have h_lt := h_prb _ _ _ h_pi'; grind [RegisterBelow]
          have h_rne2 : reg' ≠ Register.R (csPrefix.nextReg + 1) := by
            cases reg' with
            | R n => have h_lt := h_prb _ _ _ h_pi'; grind [RegisterBelow]
          refine ⟨reg', base', tag', ?_, ?_, h_ra', h_rt', h_nw', h_dom'⟩
          · rw [h_stmtRun, getPlaceInfo_emit, getPlaceInfo_emit, getPlaceInfo_emit,
              getPlaceInfo_setNextReg, getPlaceInfo_emit, getPlaceInfo_setNextReg]
            exact h_pi'
          · show oseair.RegMap.lookup _ _ = _
            rw [RegMap.lookup_insert_ne _ h_rne2, RegMap.lookup_insert_ne _ h_rne1]
            exact h_entry'
        · -- SourceMemSim: BRIDGE 2's conclusion
          exact h_sms'
        · -- TagRenameBounded: source counter unchanged; target minted then kept +1
          show TagRenameBounded ρt perms''.NextTag p3.NextTag
          rw [sb_write_NextTag h_useMut_src, sb_read_NextTag h_qread]
          refine TagRenameBounded.mono h_tbd (Nat.le_refl _) ?_
          calc s_osea.perms.NextTag
              = _ := (sb_read_NextTag h_read_tgt).symm
            _ ≤ q3.NextTag := h_ntle
            _ = p3.NextTag := (sb_write_NextTag h_useMut_tgt).symm
        · -- AllocLockstep: stores only
          simp only [AllocLockstep, mirlite_writeWordSeq_addrStart,
            oseair_writeWordSeq_addrStart]
          exact h_alloc
        · -- UnboundLocalsUnmapped: placeRegMap untouched
          intro τ' loc' h_none
          rw [h_stmtRun, getPlaceInfo_emit, getPlaceInfo_emit, getPlaceInfo_emit,
            getPlaceInfo_setNextReg, getPlaceInfo_emit, getPlaceInfo_setNextReg]
          exact h_unmap loc' h_none
        · -- PlaceRegMapBound
          intro idx reg'' τ'' h_look
          rw [h_stmtRun] at h_look ⊢
          rw [getPlaceInfo_emit, getPlaceInfo_emit, getPlaceInfo_emit,
            getPlaceInfo_setNextReg, getPlaceInfo_emit, getPlaceInfo_setNextReg] at h_look
          refine RegisterBelow.mono ?_ (h_prb _ _ _ h_look)
          simp only [emit]
          exact Nat.le_trans (Nat.le_succ _) (Nat.le_succ _)
      · simp at h_w

/-- REGIME C-deref-ZERO, CLOSED 2026-08-29: `(*P).f := v` at ZERO
    offset over any load spine — the projection returns the loaded
    register, so this is regime D-spine with the projected resolution
    shape: `[P-code; Load; CStore]`, the write going through the LOADED
    tag at `b + o + 0`. Takes the `stmt0` transfer triple so nested
    projection towers over deref roots flatten into it. -/
theorem const_write_proj_deref_zero_simulation
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_pre s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {σ : LayoutTy}
    {P : Place Γ (obseq.LayoutTy.PtrL σ)} {path : PathTo σ obseq.LayoutTy.NatL}
    {resolved : mirlite.PlaceRes} {permsD : MSB.State}
    (compProg : oseair.Prog)
    (v : Word)
    (h_spine : LoadSpine P)
    (h_o : pathOffset path = 0)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    {stmt0 : Stmt Γ}
    (h_stmt : prog.get? s_mir.pc = some stmt0)
    (h_run0 : ∀ cs, CheckedCompilerM.run (compileStmtChecked stmt0) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.proj (.deref P) path) (.constInit v))) cs)
    (h_val0 : ∀ cs so, CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.proj (.deref P) path) (.constInit v))) cs
        = Except.ok so →
      ∃ so', CheckedCompilerM.value (compileStmtChecked stmt0) cs
        = Except.ok so')
    (h_prep : mirlite.preparePlaceAssign MSB s_mir (.proj (.deref P) path) = .ok s_pre)
    (h_res  : mirlite.resolvePlaceAcc MSB s_pre (.proj (.deref P) path)
      = .ok (resolved, permsD))
    (h_write : mirlite.writeResolvedPlace (τ := obseq.LayoutTy.NatL)
                 MSB { s_pre with perms := permsD } resolved
                 [mirlite.MemValue.word v] rfl = .ok s_mir') :
    ∃ (s_osea' : oseair.State MSB) (n : Nat),
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa ρt s_mir' s_osea' := by
  have h_pre : s_pre = s_mir := by
    simp only [mirlite.preparePlaceAssign] at h_prep
    split at h_prep
    · cases h_prep; rfl
    · simp [mirlite.allocateRoot] at h_prep
  rw [h_pre] at h_res h_write
  obtain ⟨csPrefix, ⟨h_csAt, h_pc⟩, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_tbd,
    h_alloc, h_unmap, h_prb⟩ := h_inv
  simp only [mirlite.resolvePlaceAcc] at h_res
  cases h_dres : mirlite.resolvePlaceAcc MSB s_mir P with
  | error e => simp [h_dres] at h_res
  | ok pr =>
  obtain ⟨pRes, permsP⟩ := pr
  simp only [h_dres] at h_res
  by_cases h_qb : pRes.addr < pRes.allocBase ∨
      pRes.addr ≥ pRes.allocBase + pRes.allocSize
  · rw [if_pos h_qb] at h_res
    exact absurd h_res (by simp)
  · rw [if_neg h_qb] at h_res
    cases h_qread : MSB.read permsP pRes.addr 1 pRes.tag with
    | error e => simp [h_qread] at h_res
    | ok permsP' =>
    simp only [h_qread] at h_res
    cases h_qfind : mirlite.Mem.find? s_mir.mem pRes.addr with
    | none => simp [h_qfind] at h_res
    | some mv =>
    cases mv with
    | undef => simp [h_qfind] at h_res
    | word w => simp [h_qfind] at h_res
    | ptrVal b o sz t =>
    simp only [h_qfind, Except.ok.injEq, Prod.mk.injEq] at h_res
    obtain ⟨h_r1, h_r2⟩ := h_res
    subst h_r1
    subst h_r2
    have h_resolved : ∃ r0, mirlite.resolvePlace? s_mir (.proj (.deref P) path)
        = some r0 := by
      simp only [mirlite.preparePlaceAssign] at h_prep
      split at h_prep
      · rename_i r0 h_r0
        exact ⟨r0, h_r0⟩
      · simp [mirlite.allocateRoot] at h_prep
    obtain ⟨r0, h_resolved⟩ := h_resolved
    have h_mapped : PlaceInputsMapped csPrefix (Place.proj (Place.deref P) path) :=
      placeInputsMapped_of_localBindingSim_resolvePlace h_lbs h_resolved
    have h_root := ensurePlaceRoot_run_eq_of_mapped h_mapped
    obtain ⟨dstOut, h_dstOut⟩ := placeToRegChecked_ok_of_placeInputsMapped
      (cs := csPrefix) (kind := RefKind.Mut)
      (p := .proj (.deref P) path) h_mapped
    obtain ⟨stmtOutC, h_stmtOutC⟩ : ∃ so, CheckedCompilerM.value
        (compileStmtChecked (Stmt.assign (.proj (.deref P) path) (.constInit v)))
        csPrefix = Except.ok so :=
      ⟨{ result := (),
         evidence := StmtEvidence.assignPlace (.proj (.deref P) path) (.constInit v)
           dstOut.result dstOut.evidence (RExprToEvidence.constInit v) },
       by simp [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked, h_dstOut, h_root]⟩
    obtain ⟨stmtOut, h_stmtOut⟩ := h_val0 csPrefix stmtOutC h_stmtOutC
    have h_proj_eq := placeToRegChecked_proj_root_eq (Γ := Γ) (kind := RefKind.Mut)
      (base := .deref P) path (fun _ _ _ h => by cases h)
    have h_bindD : placeToRegChecked (Γ := Γ) RefKind.Mut (.deref P)
        = (do
            let ptrOut ← placeToRegChecked RefKind.Shared P
            let ptrRes := ptrOut.result
            let loadedReg ← CheckedCompilerM.lift freshRegM
            let _ ← CheckedCompilerM.lift
              (emitM [Instr.Assgn loadedReg (Rhs.Load obseq.TyVal.PTy ptrRes.reg)])
            let _ ← CheckedCompilerM.lift (emitM (cleanupInstrs ptrRes.cleanup))
            pure {
              result := { reg := loadedReg, cleanup := [] },
              evidence := PlaceToRegEvidence.deref P ptrRes loadedReg ptrOut.evidence
            }) := by simp only [placeToRegChecked]
    have h_incr0 : StateIncr (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix)
        (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (.deref P)) csPrefix) := by
      rw [h_bindD, CheckedCompilerM.run_bind]
      cases h : CheckedCompilerM.value (placeToRegChecked RefKind.Shared P) csPrefix with
      | ok a => exact CheckedCompilerM.incr _ _
      | error e => exact StateIncr.refl _
    have h_incr1 : StateIncr
        (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (.deref P)) csPrefix)
        (CheckedCompilerM.run (placeToRegChecked RefKind.Mut
          (.proj (.deref P) path)) csPrefix) := by
      rw [h_proj_eq, CheckedCompilerM.run_bind]
      cases h : CheckedCompilerM.value (placeToRegChecked RefKind.Mut (.deref P)) csPrefix with
      | ok a => exact CheckedCompilerM.incr _ _
      | error e => exact StateIncr.refl _
    have h_stmt_bind : compileStmtChecked (Stmt.assign (.proj (.deref P) path) (.constInit v))
        = (do
            let _ ← CheckedCompilerM.lift (ensurePlaceRoot (Place.proj (Place.deref P) path))
            let dstOut ← placeToRegChecked RefKind.Mut (.proj (.deref P) path)
            let dstRes := dstOut.result
            let rhsOut ← compileRExprToChecked dstRes.reg (.constInit v)
            let _ ← CheckedCompilerM.lift (emitM (cleanupInstrs dstRes.cleanup))
            pure {
              result := (),
              evidence := StmtEvidence.assignPlace (.proj (.deref P) path) (.constInit v)
                dstRes dstOut.evidence rhsOut.evidence
            }) := rfl
    have h_incr2 : StateIncr
        (CheckedCompilerM.run (placeToRegChecked RefKind.Mut
          (.proj (.deref P) path)) csPrefix)
        (CheckedCompilerM.run
          (compileStmtChecked (Stmt.assign (.proj (.deref P) path) (.constInit v))) csPrefix) := by
      rw [h_stmt_bind]
      rw [CheckedCompilerM.run_bind]
      simp only [CheckedCompilerM.value_lift, CheckedCompilerM.run_lift, h_root]
      rw [CheckedCompilerM.run_bind]
      cases h : CheckedCompilerM.value
          (placeToRegChecked RefKind.Mut (.proj (.deref P) path)) csPrefix with
      | ok a => exact CheckedCompilerM.incr _ _
      | error e => exact StateIncr.refl _
    have h_instP : ∀ q' instr,
        q' < (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextLabel →
        (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).code q' = some instr →
        compProg q' = some instr := by
      intro q' instr h_lt h_code
      have h_incrP := StateIncr.trans h_incr0 (StateIncr.trans h_incr1 h_incr2)
      refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
      · rw [h_run0 csPrefix]
        exact Nat.lt_of_lt_of_le h_lt h_incrP.nextLabel_le
      · rw [h_run0 csPrefix, h_incrP.code_eq q' h_lt]
        exact h_code
    obtain ⟨pOut, n1, s_mid, ptag, h_pval, h_pclean, h_prun, h_ppc, h_pmem, h_ppsim,
      h_pnt1, h_pnt2, h_plbs, h_pentry, h_prt, h_pnw, h_ple, h_prange, h_pbelow,
      h_pprm, h_pregmono, h_plabmono⟩ :=
      loadSpine_lowering_sim h_id_a h_wf_t h_spine RefKind.Shared csPrefix s_osea
        pRes permsP h_dres h_lbs h_prb h_sms h_psim h_pc h_instP
    rw [show path.offset = 0 from h_o] at h_write
    have h_stmtRunC := compileStmt_proj_deref_zero_run v h_o h_root h_pval h_pclean
    have h_stmtRun := (h_run0 csPrefix).trans h_stmtRunC
    -- pointer-place bounds from the dereferenceable check
    have h_cancel : pRes.allocBase + (pRes.addr - pRes.allocBase) = pRes.addr := by
      grind
    have h_off : pRes.addr - pRes.allocBase < pRes.allocSize := by grind
    -- the final Load
    have h_code1 : compProg s_mid.pc = some (Instr.Assgn
        (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg)
        (Rhs.Load obseq.TyVal.PTy pOut.result.reg)) := by
      rw [h_ppc]
      refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
      · rw [h_stmtRun]
        show (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextLabel < (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextLabel + 1 + 1
        omega
      · rw [h_stmtRun]
        rw [emit_code_lt_nextLabel _ _
          (by show (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextLabel < (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextLabel + 1; omega)]
        have h := emit_code_at_new
          { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg + 1 }
          [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg)
            (Rhs.Load obseq.TyVal.PTy pOut.result.reg)]
          (k := 0) (by simp)
        simpa using h
    obtain ⟨p2, h_read_tgt, h_psim2⟩ :=
      sb_read_respects_PermSim h_ppsim h_wf_t h_prt h_pnw h_qread
    have h_read_tgt' : MSB.read s_mid.perms
        (pRes.allocBase + (pRes.addr - pRes.allocBase)) 1 ptag = .ok p2 := by
      rw [h_cancel]
      exact h_read_tgt
    have h_run1 := runN_Assgn_Load_ptr_step compProg s_mid
      (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg)
      pOut.result.reg obseq.TyVal.PTy h_code1 h_pentry h_off h_read_tgt'
    -- the loaded cell holds the ρ-renamed final pointer
    obtain ⟨addr', value', h_ra', h_find_tgt, h_mvs⟩ := h_sms _ _ h_qfind
    have h_addr' : addr' = pRes.addr := (h_id_a _ _ h_ra').symm
    subst h_addr'
    cases value' with
    | Undef => exact h_mvs.elim
    | Dat _ => exact h_mvs.elim
    | Ptr b2 o2 s2 t2 =>
    obtain ⟨h_b, h_o, h_s, h_t, h_tnw, h_range⟩ := h_mvs
    have h_b2 : b2 = b := (h_id_a _ _ h_b).symm
    subst h_b2
    subst h_o
    subst h_s
    have h_rws : oseair.readWordSeq s_mid.mem
        (pRes.allocBase + (pRes.addr - pRes.allocBase))
        (obseq.typeSize obseq.TyVal.PTy) = [Val.Ptr b2 o2 s2 t2] := by
      rw [h_cancel]
      show oseair.readWordSeq s_mid.mem pRes.addr 1 = _
      rw [h_pmem]
      simp [oseair.readWordSeq, h_find_tgt]
    -- the CStore through the loaded pointer
    have h_code2 : compProg (s_mid.pc + 1) = some (Instr.CStore obseq.TyVal.NatTy
        [Val.Dat v] (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg)) := by
      rw [h_ppc]
      refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
      · rw [h_stmtRun]
        show (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextLabel + 1 < (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextLabel + 1 + 1
        omega
      · rw [h_stmtRun]
        have h := emit_code_at_new
          (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg + 1 }
            [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg)
              (Rhs.Load obseq.TyVal.PTy pOut.result.reg)])
          [Instr.CStore obseq.TyVal.NatTy [Val.Dat v]
            (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg)]
          (k := 0) (by simp)
        simpa [emit] using h
    have h_w := h_write
    simp only [mirlite.writeResolvedPlace] at h_w
    split at h_w
    · simp at h_w
    · rename_i h_nb
      split at h_w
      · rename_i perms' h_useMut_src
        cases h_w
        have h_osz : o2 < s2 := by
          have h1 : b2 + o2 + 1 ≤ b2 + s2 := Nat.le_of_not_lt (by simpa using h_nb)
          exact Nat.lt_of_add_lt_add_left (Nat.lt_of_succ_le h1)
        obtain ⟨p3, h_useMut_tgt, h_psim3⟩ :=
          sb_write_respects_PermSim h_psim2 h_wf_t h_t h_tnw h_useMut_src
        have h_entry1 : PtrRegisterEntry
            (oseair.RegMap.insert s_mid.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg)
              (obseq.TyVal.PTy, oseair.readWordSeq s_mid.mem
                (pRes.allocBase + (pRes.addr - pRes.allocBase))
                (obseq.typeSize obseq.TyVal.PTy)))
            (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg) b2 ((b2 + o2) - b2) s2 t2 := by
          show oseair.RegMap.lookup _ _ = _
          rw [Nat.add_sub_cancel_left, RegMap.lookup_insert_self, h_rws]
        obtain ⟨h_wtp, h_sms'⟩ :=
          writeThroughPtr_sim (ρa := ρa) (ρt := ρt) (τ := obseq.LayoutTy.NatL)
            (s_pre := { s_mir with perms := permsP' })
            (s_osea := ({ s_mid with perms := p2, reg := oseair.RegMap.insert s_mid.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg) (obseq.TyVal.PTy, oseair.readWordSeq s_mid.mem (pRes.allocBase + (pRes.addr - pRes.allocBase)) (obseq.typeSize obseq.TyVal.PTy)), pc := s_mid.pc + 1 } : oseair.State MSB))
            (resolved := { addr := b2 + o2, tag := t, allocBase := b2, allocSize := s2 })
            "CStore Invalid Ptr" [mirlite.MemValue.word v] [Val.Dat v] rfl
            ⟨rfl, trivial⟩ h_id_a h_entry1 h_useMut_tgt
            (by rw [show (({ s_mid with perms := p2, reg := oseair.RegMap.insert s_mid.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg) (obseq.TyVal.PTy, oseair.readWordSeq s_mid.mem (pRes.allocBase + (pRes.addr - pRes.allocBase)) (obseq.typeSize obseq.TyVal.PTy)), pc := s_mid.pc + 1 } : oseair.State MSB)).mem = s_mid.mem from rfl, h_pmem]; exact h_sms)
            (Nat.le_add_right b2 o2)
            (fun k hk => by
              simp [Nat.lt_one_iff] at hk
              subst hk
              obtain ⟨a', h_a'⟩ := h_range o2 h_osz
              have h_ida := h_id_a _ _ h_a'
              rw [← h_ida] at h_a'
              exact h_a')
            h_write
        have h_run2 := runN_CStore_step compProg ({ s_mid with perms := p2, reg := oseair.RegMap.insert s_mid.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg) (obseq.TyVal.PTy, oseair.readWordSeq s_mid.mem (pRes.allocBase + (pRes.addr - pRes.allocBase)) (obseq.typeSize obseq.TyVal.PTy)), pc := s_mid.pc + 1 } : oseair.State MSB) _
          obseq.TyVal.NatTy [Val.Dat v]
          (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg) h_code2 rfl h_wtp
        have h_run :=
          (oseair_runN_add (n1 + 1) 1 s_osea compProg _
            ((oseair_runN_add n1 1 s_osea compProg s_mid h_prun).trans h_run1)).trans h_run2
        refine ⟨_, n1 + 1 + 1, h_run, ?_⟩
        refine ⟨CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix,
            ⟨prefixCompileState_succ h_csAt h_stmt h_stmtOut, ?_⟩, ?_, h_sms', h_psim3,
            h_id_a, h_wf_t, ?_, ?_, ?_, ?_⟩
        · -- label agreement
          show s_mid.pc + 1 + 1 = _
          rw [h_ppc, h_stmtRun]
          simp [emit]
        · -- LocalBindingSim across the fresh load register and the emits
          refine LocalBindingSim.placeRegMap_congr ?_
            (LocalBindingSim.insert_fresh_reg h_plbs h_prb h_pregmono rfl)
          rw [h_stmtRun]
          exact h_pprm
        · -- TagRenameBounded: the spine only READS and the store only WRITES,
          -- so no counter moved anywhere along the fragment
          show TagRenameBounded ρt perms'.NextTag p3.NextTag
          rw [sb_write_NextTag h_useMut_src, sb_write_NextTag h_useMut_tgt,
            sb_read_NextTag h_qread, sb_read_NextTag h_read_tgt, h_pnt1, h_pnt2]
          exact h_tbd
        · -- AllocLockstep: the fragment loads and stores, never allocates
          simp only [AllocLockstep, mirlite_writeWordSeq_addrStart,
            oseair_writeWordSeq_addrStart, h_pmem]
          exact h_alloc
        · -- UnboundLocalsUnmapped: `placeRegMap` is untouched by the
          -- spine's loads and by the store
          intro τ'' loc' h_none
          rw [h_stmtRun]
          simp only [getPlaceInfo, emit]
          rw [h_pprm]
          exact h_unmap loc' h_none
        · -- PlaceRegMapBound
          intro idx reg τ'' h_look
          rw [h_stmtRun] at h_look ⊢
          have h_cs : getPlaceInfo csPrefix idx = some (reg, τ'') := by
            show csPrefix.placeRegMap.lookup idx = _
            rw [← h_pprm]
            exact h_look
          exact RegisterBelow.mono
            (Nat.le_trans h_pregmono (Nat.le_succ _)) (h_prb _ _ _ h_cs)
      · simp at h_w


/-- REGIME C-deref, CLOSED: constant write to a NONZERO-offset projection
    off a DEREFERENCED load spine — `(*p).f := v` and every all-deref
    deepening of `p`. The spine mother lemma delivers the loaded pointer;
    the C1 pattern finishes: `Borrow(Mut); CStore; Die` with the parent
    tag coming from the LOADED pointer (via `MemValSim`) instead of a
    local binding. -/
theorem const_write_proj_deref_simulation
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_pre s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {σ : LayoutTy}
    {P : Place Γ (obseq.LayoutTy.PtrL σ)} {path : PathTo σ obseq.LayoutTy.NatL}
    {resolved : mirlite.PlaceRes} {permsD : MSB.State}
    (compProg : oseair.Prog)
    (v : Word)
    (h_spine : LoadSpine P)
    (h_off : pathOffset path ≠ 0)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    {stmt0 : Stmt Γ}
    (h_stmt : prog.get? s_mir.pc = some stmt0)
    (h_run0 : ∀ cs, CheckedCompilerM.run (compileStmtChecked stmt0) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.proj (.deref P) path) (.constInit v))) cs)
    (h_val0 : ∀ cs so, CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.proj (.deref P) path) (.constInit v))) cs
        = Except.ok so →
      ∃ so', CheckedCompilerM.value (compileStmtChecked stmt0) cs
        = Except.ok so')
    (h_prep : mirlite.preparePlaceAssign MSB s_mir (.proj (.deref P) path) = .ok s_pre)
    (h_res  : mirlite.resolvePlaceAcc MSB s_pre (.proj (.deref P) path)
      = .ok (resolved, permsD))
    (h_write : mirlite.writeResolvedPlace (τ := obseq.LayoutTy.NatL)
                 MSB { s_pre with perms := permsD } resolved
                 [mirlite.MemValue.word v] rfl = .ok s_mir') :
    ∃ (s_osea' : oseair.State MSB) (n : Nat),
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa ρt s_mir' s_osea' := by
  have h_pre : s_pre = s_mir := by
    simp only [mirlite.preparePlaceAssign] at h_prep
    split at h_prep
    · cases h_prep; rfl
    · simp [mirlite.allocateRoot] at h_prep
  rw [h_pre] at h_res h_write
  obtain ⟨csPrefix, ⟨h_csAt, h_pc⟩, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_tbd,
    h_alloc, h_unmap, h_prb⟩ := h_inv
  simp only [mirlite.resolvePlaceAcc] at h_res
  cases h_dres : mirlite.resolvePlaceAcc MSB s_mir P with
  | error e => simp [h_dres] at h_res
  | ok pr =>
  obtain ⟨pRes, permsP⟩ := pr
  simp only [h_dres] at h_res
  by_cases h_qb : pRes.addr < pRes.allocBase ∨
      pRes.addr ≥ pRes.allocBase + pRes.allocSize
  · rw [if_pos h_qb] at h_res
    exact absurd h_res (by simp)
  · rw [if_neg h_qb] at h_res
    cases h_qread : MSB.read permsP pRes.addr 1 pRes.tag with
    | error e => simp [h_qread] at h_res
    | ok permsP' =>
    simp only [h_qread] at h_res
    cases h_qfind : mirlite.Mem.find? s_mir.mem pRes.addr with
    | none => simp [h_qfind] at h_res
    | some mv =>
    cases mv with
    | undef => simp [h_qfind] at h_res
    | word w => simp [h_qfind] at h_res
    | ptrVal b o sz t =>
    simp only [h_qfind, Except.ok.injEq, Prod.mk.injEq] at h_res
    obtain ⟨h_r1, h_r2⟩ := h_res
    subst h_r1
    subst h_r2
    have h_resolved : ∃ r0, mirlite.resolvePlace? s_mir (.proj (.deref P) path)
        = some r0 := by
      simp only [mirlite.preparePlaceAssign] at h_prep
      split at h_prep
      · rename_i r0 h_r0
        exact ⟨r0, h_r0⟩
      · simp [mirlite.allocateRoot] at h_prep
    obtain ⟨r0, h_resolved⟩ := h_resolved
    have h_mapped : PlaceInputsMapped csPrefix (Place.proj (Place.deref P) path) :=
      placeInputsMapped_of_localBindingSim_resolvePlace h_lbs h_resolved
    have h_root := ensurePlaceRoot_run_eq_of_mapped h_mapped
    obtain ⟨dstOut, h_dstOut⟩ := placeToRegChecked_ok_of_placeInputsMapped
      (cs := csPrefix) (kind := RefKind.Mut)
      (p := .proj (.deref P) path) h_mapped
    obtain ⟨stmtOutC, h_stmtOutC⟩ : ∃ so, CheckedCompilerM.value
        (compileStmtChecked (Stmt.assign (.proj (.deref P) path) (.constInit v)))
        csPrefix = Except.ok so :=
      ⟨{ result := (),
         evidence := StmtEvidence.assignPlace (.proj (.deref P) path) (.constInit v)
           dstOut.result dstOut.evidence (RExprToEvidence.constInit v) },
       by simp [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked, h_dstOut, h_root]⟩
    obtain ⟨stmtOut, h_stmtOut⟩ := h_val0 csPrefix stmtOutC h_stmtOutC
    have h_proj_eq := placeToRegChecked_proj_root_eq (Γ := Γ) (kind := RefKind.Mut)
      (base := .deref P) path (fun _ _ _ h => by cases h)
    have h_bindD : placeToRegChecked (Γ := Γ) RefKind.Mut (.deref P)
        = (do
            let ptrOut ← placeToRegChecked RefKind.Shared P
            let ptrRes := ptrOut.result
            let loadedReg ← CheckedCompilerM.lift freshRegM
            let _ ← CheckedCompilerM.lift
              (emitM [Instr.Assgn loadedReg (Rhs.Load obseq.TyVal.PTy ptrRes.reg)])
            let _ ← CheckedCompilerM.lift (emitM (cleanupInstrs ptrRes.cleanup))
            pure {
              result := { reg := loadedReg, cleanup := [] },
              evidence := PlaceToRegEvidence.deref P ptrRes loadedReg ptrOut.evidence
            }) := by simp only [placeToRegChecked]
    have h_incr0 : StateIncr (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix)
        (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (.deref P)) csPrefix) := by
      rw [h_bindD, CheckedCompilerM.run_bind]
      cases h : CheckedCompilerM.value (placeToRegChecked RefKind.Shared P) csPrefix with
      | ok a => exact CheckedCompilerM.incr _ _
      | error e => exact StateIncr.refl _
    have h_incr1 : StateIncr
        (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (.deref P)) csPrefix)
        (CheckedCompilerM.run (placeToRegChecked RefKind.Mut
          (.proj (.deref P) path)) csPrefix) := by
      rw [h_proj_eq, CheckedCompilerM.run_bind]
      cases h : CheckedCompilerM.value (placeToRegChecked RefKind.Mut (.deref P)) csPrefix with
      | ok a => exact CheckedCompilerM.incr _ _
      | error e => exact StateIncr.refl _
    have h_stmt_bind : compileStmtChecked (Stmt.assign (.proj (.deref P) path) (.constInit v))
        = (do
            let _ ← CheckedCompilerM.lift (ensurePlaceRoot (Place.proj (Place.deref P) path))
            let dstOut ← placeToRegChecked RefKind.Mut (.proj (.deref P) path)
            let dstRes := dstOut.result
            let rhsOut ← compileRExprToChecked dstRes.reg (.constInit v)
            let _ ← CheckedCompilerM.lift (emitM (cleanupInstrs dstRes.cleanup))
            pure {
              result := (),
              evidence := StmtEvidence.assignPlace (.proj (.deref P) path) (.constInit v)
                dstRes dstOut.evidence rhsOut.evidence
            }) := rfl
    have h_incr2 : StateIncr
        (CheckedCompilerM.run (placeToRegChecked RefKind.Mut
          (.proj (.deref P) path)) csPrefix)
        (CheckedCompilerM.run
          (compileStmtChecked (Stmt.assign (.proj (.deref P) path) (.constInit v))) csPrefix) := by
      rw [h_stmt_bind]
      rw [CheckedCompilerM.run_bind]
      simp only [CheckedCompilerM.value_lift, CheckedCompilerM.run_lift, h_root]
      rw [CheckedCompilerM.run_bind]
      cases h : CheckedCompilerM.value
          (placeToRegChecked RefKind.Mut (.proj (.deref P) path)) csPrefix with
      | ok a => exact CheckedCompilerM.incr _ _
      | error e => exact StateIncr.refl _
    have h_instP : ∀ q' instr,
        q' < (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextLabel →
        (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).code q' = some instr →
        compProg q' = some instr := by
      intro q' instr h_lt h_code
      have h_incrP := StateIncr.trans h_incr0 (StateIncr.trans h_incr1 h_incr2)
      refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
      · rw [h_run0 csPrefix]
        exact Nat.lt_of_lt_of_le h_lt h_incrP.nextLabel_le
      · rw [h_run0 csPrefix, h_incrP.code_eq q' h_lt]
        exact h_code
    obtain ⟨pOut, n1, s_mid, ptag, h_pval, h_pclean, h_prun, h_ppc, h_pmem, h_ppsim,
      h_pnt1, h_pnt2, h_plbs, h_pentry, h_prt, h_pnw, h_ple, h_prange, h_pbelow,
      h_pprm, h_pregmono, h_plabmono⟩ :=
      loadSpine_lowering_sim h_id_a h_wf_t h_spine RefKind.Shared csPrefix s_osea
        pRes permsP h_dres h_lbs h_prb h_sms h_psim h_pc h_instP
    have h_stmtRunC := compileStmt_proj_deref_run (cs := csPrefix) (pOut := pOut)
      v h_off h_root h_pval h_pclean
    have h_stmtRun := (h_run0 csPrefix).trans h_stmtRunC
    have h_len4 : ((emit (emit (emit
        { (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg + 1 }
            [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg) (Rhs.Load obseq.TyVal.PTy pOut.result.reg)]) with
            nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg + 1 + 1 }
        [Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg + 1))
          (borrowRhs RefKind.Mut (blockSize obseq.LayoutTy.NatL) (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg)
            (pathOffset path))])
        [Instr.CStore obseq.TyVal.NatTy [Val.Dat v] (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg + 1))])
        [Instr.Die (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg + 1)) (blockSize obseq.LayoutTy.NatL)])).nextLabel
        = (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextLabel + 4 := by
      simp only [emit, List.length_cons, List.length_nil]
    have h_code1 : compProg s_mid.pc
        = some (Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg)
            (Rhs.Load obseq.TyVal.PTy pOut.result.reg)) := by
      rw [h_ppc]
      refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
      · rw [h_stmtRun, h_len4]; omega
      · rw [h_stmtRun]
        rw [emit_code_lt_nextLabel _ _ (by
          simp only [emit, List.length_cons, List.length_nil]; omega)]
        rw [emit_code_lt_nextLabel _ _ (by
          simp only [emit, List.length_cons, List.length_nil]; omega)]
        rw [emit_code_lt_nextLabel _ _ (by
          simp only [emit, List.length_cons, List.length_nil]; omega)]
        have h := emit_code_at_new { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg + 1 }
          [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg)
            (Rhs.Load obseq.TyVal.PTy pOut.result.reg)] (k := 0) (by simp)
        simpa using h
    have h_code2 : compProg (s_mid.pc + 1)
        = some (Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg + 1))
            (borrowRhs RefKind.Mut (blockSize obseq.LayoutTy.NatL)
              (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg) (pathOffset path))) := by
      rw [h_ppc]
      refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
      · rw [h_stmtRun, h_len4]; omega
      · rw [h_stmtRun]
        rw [emit_code_lt_nextLabel _ _ (by
          simp only [emit, List.length_cons, List.length_nil]; omega)]
        rw [emit_code_lt_nextLabel _ _ (by
          simp only [emit, List.length_cons, List.length_nil]; omega)]
        have h := emit_code_at_new
          { (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg + 1 }
              [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg)
                (Rhs.Load obseq.TyVal.PTy pOut.result.reg)]) with
              nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg + 1 + 1 }
          [Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg + 1))
            (borrowRhs RefKind.Mut (blockSize obseq.LayoutTy.NatL)
              (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg) (pathOffset path))] (k := 0) (by simp)
        simpa [emit] using h
    have h_code3 : compProg (s_mid.pc + 1 + 1)
        = some (Instr.CStore obseq.TyVal.NatTy [Val.Dat v]
            (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg + 1))) := by
      rw [h_ppc]
      refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
      · rw [h_stmtRun, h_len4]; omega
      · rw [h_stmtRun]
        rw [emit_code_lt_nextLabel _ _ (by
          simp only [emit, List.length_cons, List.length_nil]; omega)]
        have h := emit_code_at_new
          (emit { (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg + 1 }
              [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg)
                (Rhs.Load obseq.TyVal.PTy pOut.result.reg)]) with
              nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg + 1 + 1 }
            [Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg + 1))
              (borrowRhs RefKind.Mut (blockSize obseq.LayoutTy.NatL)
                (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg) (pathOffset path))])
          [Instr.CStore obseq.TyVal.NatTy [Val.Dat v] (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg + 1))]
          (k := 0) (by simp)
        simpa [emit] using h
    have h_code4 : compProg (s_mid.pc + 1 + 1 + 1)
        = some (Instr.Die (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg + 1))
            (blockSize obseq.LayoutTy.NatL)) := by
      rw [h_ppc]
      refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
      · rw [h_stmtRun, h_len4]; omega
      · rw [h_stmtRun]
        have h := emit_code_at_new
          (emit (emit { (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg + 1 }
              [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg)
                (Rhs.Load obseq.TyVal.PTy pOut.result.reg)]) with
              nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg + 1 + 1 }
            [Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg + 1))
              (borrowRhs RefKind.Mut (blockSize obseq.LayoutTy.NatL)
                (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg) (pathOffset path))])
            [Instr.CStore obseq.TyVal.NatTy [Val.Dat v] (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg + 1))])
          [Instr.Die (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg + 1)) (blockSize obseq.LayoutTy.NatL)]
          (k := 0) (by simp)
        simpa [emit] using h
    obtain ⟨p2, h_read_tgt, h_psim2⟩ :=
      sb_read_respects_PermSim h_ppsim h_wf_t h_prt h_pnw h_qread
    have h_cancel : pRes.allocBase + (pRes.addr - pRes.allocBase) = pRes.addr := by
      grind
    have h_offP : pRes.addr - pRes.allocBase < pRes.allocSize := by grind
    have h_read_tgt' : MSB.read s_mid.perms
        (pRes.allocBase + (pRes.addr - pRes.allocBase)) 1 ptag = .ok p2 := by
      rw [h_cancel]; exact h_read_tgt
    have h_run1 := runN_Assgn_Load_ptr_step compProg s_mid
      (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg) pOut.result.reg obseq.TyVal.PTy
      h_code1 h_pentry h_offP h_read_tgt'
    obtain ⟨addr', value', h_ra', h_find_tgt, h_mvs⟩ := h_sms _ _ h_qfind
    have h_addr' : addr' = pRes.addr := (h_id_a _ _ h_ra').symm
    subst h_addr'
    cases value' with
    | Undef => exact h_mvs.elim
    | Dat _ => exact h_mvs.elim
    | Ptr b2 o2 s2 t2 =>
    obtain ⟨h_b, h_o, h_s, h_t, h_tnw, h_range⟩ := h_mvs
    have h_b2 : b2 = b := (h_id_a _ _ h_b).symm
    subst h_b2
    subst h_o
    subst h_s
    have h_rws : oseair.readWordSeq s_mid.mem
        (pRes.allocBase + (pRes.addr - pRes.allocBase))
        (obseq.typeSize obseq.TyVal.PTy) = [Val.Ptr b2 o2 s2 t2] := by
      rw [h_cancel]
      show oseair.readWordSeq s_mid.mem pRes.addr 1 = _
      rw [h_pmem]
      simp [oseair.readWordSeq, h_find_tgt]
    have h_w := h_write
    simp only [mirlite.writeResolvedPlace] at h_w
    split at h_w
    · simp at h_w
    · rename_i h_nb
      split at h_w
      · rename_i perms'' h_useMut_src
        cases h_w
        have h_nb' : b2 + o2 + pathOffset path + 1 ≤ b2 + s2 := by
          have h1 := Nat.not_lt.mp h_nb
          simpa [List.length_cons, List.length_nil, Nat.add_assoc] using h1
        obtain ⟨p3, h_useMut_tgt, h_psim3⟩ :=
          sb_write_respects_PermSim h_psim2 h_wf_t h_t h_tnw h_useMut_src
        obtain ⟨q1, h_ref_tgt⟩ := sb_ref_Mut_ok_of_sb_write_ok h_useMut_tgt
        have h_tbd2 : TagRenameBounded ρt s_mir.perms.NextTag p2.NextTag := by
          rw [sb_read_NextTag h_read_tgt, h_pnt2]
          exact h_tbd
        have h_unprot := freshTag_not_protected h_psim2 (by
          rw [sb_read_NextTag h_qread, h_pnt1]
          exact h_tbd2)
        have h0 : wildcardTag < p2.NextTag := (h_tbd2 _ _ h_wf_t.2).2
        have h_ntw : (p2.NextTag == wildcardTag) = false := by grind
        obtain ⟨q2, q3, qAcc', h_wr1, h_die1, h_wr2, h_sm, h_ex, h_pf, h_ntle⟩ :=
          sb_ref_use_die_cancels h_ntw h_unprot h_ref_tgt
        have h_qAcc : qAcc' = p3 := by
          rw [h_useMut_tgt] at h_wr2
          injection h_wr2 with h_e
          exact h_e.symm
        subst h_qAcc
        have h_entry_loaded : PtrRegisterEntry
            (oseair.RegMap.insert s_mid.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg)
              (obseq.TyVal.PTy, oseair.readWordSeq s_mid.mem
                (pRes.allocBase + (pRes.addr - pRes.allocBase))
                (obseq.typeSize obseq.TyVal.PTy)))
            (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg) b2 o2 s2 t2 := by
          show oseair.RegMap.lookup _ _ = _
          rw [RegMap.lookup_insert_self, h_rws]
        have h_le2 : b2 + o2 + pathOffset path + blockSize obseq.LayoutTy.NatL
            ≤ b2 + s2 := by
          simpa [blockSize] using h_nb'
        have h_ref_tgt' : MSB.ref p2 (b2 + o2 + pathOffset path)
            (blockSize obseq.LayoutTy.NatL) t2 RefKind.Mut false []
            = .ok (q1, p2.NextTag) := h_ref_tgt
        have h_run2 := runN_Assgn_Borrow_step compProg
          { s_mid with
              perms := p2,
              reg := oseair.RegMap.insert s_mid.reg
                (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg)
                (obseq.TyVal.PTy, oseair.readWordSeq s_mid.mem
                  (pRes.allocBase + (pRes.addr - pRes.allocBase))
                  (obseq.typeSize obseq.TyVal.PTy)),
              pc := s_mid.pc + 1 }
          (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg + 1)) (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg)
          RefKind.Mut false [] (blockSize obseq.LayoutTy.NatL) (pathOffset path)
          h_code2 h_entry_loaded h_le2 h_ref_tgt'
        have h_regne : Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg
            ≠ Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg + 1) := by grind
        have h_entry_tmp : PtrRegisterEntry
            (oseair.RegMap.insert
                    (oseair.RegMap.insert s_mid.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg)
                      (obseq.TyVal.PTy, oseair.readWordSeq s_mid.mem
                        (pRes.allocBase + (pRes.addr - pRes.allocBase))
                        (obseq.typeSize obseq.TyVal.PTy)))
                    (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg + 1))
                    (obseq.TyVal.PTy, [Val.Ptr b2 (o2 + pathOffset path) s2 p2.NextTag]))
            (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg + 1)) b2
            (b2 + o2 + pathOffset path - b2) s2 p2.NextTag := by
          have h_oe : b2 + o2 + pathOffset path - b2 = o2 + pathOffset path := by
            simp [Nat.add_assoc]
          rw [h_oe]
          exact RegMap.lookup_insert_self _ _ _
        have h_wr1' : MSB.useMut q1 (b2 + o2 + pathOffset path)
            [Val.Dat v].length p2.NextTag = .ok q2 := by
          simpa using h_wr1
        obtain ⟨h_wtp, h_sms'⟩ :=
          writeThroughPtr_sim (τ := obseq.LayoutTy.NatL)
            (s_osea :=
              { s_mid with
                  perms := q1,
                  reg := oseair.RegMap.insert
                    (oseair.RegMap.insert s_mid.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg)
                      (obseq.TyVal.PTy, oseair.readWordSeq s_mid.mem
                        (pRes.allocBase + (pRes.addr - pRes.allocBase))
                        (obseq.typeSize obseq.TyVal.PTy)))
                    (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg + 1))
                    (obseq.TyVal.PTy, [Val.Ptr b2 (o2 + pathOffset path) s2 p2.NextTag]),
                  pc := s_mid.pc + 1 + 1 })
            (resolved := { addr := b2 + o2 + pathOffset path, tag := t,
                           allocBase := b2, allocSize := s2 })
            "CStore Invalid Ptr" [mirlite.MemValue.word v] [Val.Dat v] rfl
            ⟨rfl, trivial⟩ h_id_a h_entry_tmp
            (by
              show MSB.useMut q1 (b2 + o2 + pathOffset path) [Val.Dat v].length
                p2.NextTag = .ok q2
              exact h_wr1')
            (by
              show SourceMemSim ρa ρt s_mir.mem s_mid.mem
              rw [h_pmem]
              exact h_sms)
            (Nat.le_trans (Nat.le_add_right b2 o2) (Nat.le_add_right _ _))
            (fun k hk => by
              have hk0 : k = 0 := by simpa using hk
              subst hk0
              obtain ⟨a', ha'⟩ := h_range (o2 + pathOffset path)
                (Nat.lt_of_succ_le (by
                  have h1 := h_nb'
                  have h2 : o2 + pathOffset path + 1 ≤ s2 :=
                    Nat.le_of_add_le_add_left (a := b2) (by
                      simpa [Nat.add_assoc] using h1)
                  exact h2))
              have h_ida := h_id_a _ _ ha'
              rw [← h_ida] at ha'
              show ρa (b2 + o2 + pathOffset path + 0)
                = some (b2 + o2 + pathOffset path + 0)
              rw [Nat.add_zero, Nat.add_assoc]
              exact ha')
            h_write
        have h_run3 := runN_CStore_step compProg _ _
          obseq.TyVal.NatTy [Val.Dat v] (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg + 1))
          h_code3 rfl h_wtp
        have h_die1' : MSB.die q2 (b2 + (o2 + pathOffset path))
            (blockSize obseq.LayoutTy.NatL) p2.NextTag = .ok q3 := by
          rw [← Nat.add_assoc]
          simpa using h_die1
        have h_run4 := runN_Die_step compProg
          { s_mid with
              perms := q2,
              reg := oseair.RegMap.insert
                    (oseair.RegMap.insert s_mid.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg)
                      (obseq.TyVal.PTy, oseair.readWordSeq s_mid.mem
                        (pRes.allocBase + (pRes.addr - pRes.allocBase))
                        (obseq.typeSize obseq.TyVal.PTy)))
                    (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg + 1))
                    (obseq.TyVal.PTy, [Val.Ptr b2 (o2 + pathOffset path) s2 p2.NextTag]),
              mem := oseair.writeWordSeq s_mid.mem (b2 + o2 + pathOffset path) [Val.Dat v],
              pc := s_mid.pc + 1 + 1 + 1 }
          (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg + 1)) (blockSize obseq.LayoutTy.NatL)
          h_code4 (RegMap.lookup_insert_self _ _ _) h_die1'
        have h_runA := (oseair_runN_add n1 1 s_osea compProg s_mid h_prun).trans h_run1
        have h_runB := (oseair_runN_add (n1 + 1) 1 s_osea compProg _ h_runA).trans h_run2
        have h_runC := (oseair_runN_add (n1 + 1 + 1) 1 s_osea compProg _ h_runB).trans h_run3
        have h_run := (oseair_runN_add (n1 + 1 + 1 + 1) 1 s_osea compProg _ h_runC).trans h_run4
        have h_psim4 : PermSim ρt perms'' q3 := by
          obtain ⟨hs, hp, he, hn⟩ := h_psim3
          exact ⟨by rw [h_sm]; exact hs, by rw [h_pf]; exact hp,
                 by rw [h_ex]; exact he, Nat.le_trans hn h_ntle⟩
        refine ⟨_, n1 + 1 + 1 + 1 + 1, h_run, ?_⟩
        refine ⟨CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix,
          ⟨prefixCompileState_succ h_csAt h_stmt h_stmtOut, ?_⟩, ?_, ?_, h_psim4,
          h_id_a, h_wf_t, ?_, ?_, ?_, ?_⟩
        · show s_mid.pc + 1 + 1 + 1 + 1 = _
          rw [h_ppc, h_stmtRun, h_len4]
        · have h_lbs1 : LocalBindingSim ρa ρt s_mir.env
              { s_mid with
                  perms := p2,
                  reg := oseair.RegMap.insert s_mid.reg
                    (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg)
                    (obseq.TyVal.PTy, oseair.readWordSeq s_mid.mem
                      (pRes.allocBase + (pRes.addr - pRes.allocBase))
                      (obseq.typeSize obseq.TyVal.PTy)),
                  pc := s_mid.pc + 1 } csPrefix :=
            LocalBindingSim.insert_fresh_reg h_plbs h_prb h_pregmono rfl
          have h_lbs2 : LocalBindingSim ρa ρt s_mir.env
              { s_mid with
                  perms := q1,
                  reg := oseair.RegMap.insert
                    (oseair.RegMap.insert s_mid.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg)
                      (obseq.TyVal.PTy, oseair.readWordSeq s_mid.mem
                        (pRes.allocBase + (pRes.addr - pRes.allocBase))
                        (obseq.typeSize obseq.TyVal.PTy)))
                    (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg + 1))
                    (obseq.TyVal.PTy, [Val.Ptr b2 (o2 + pathOffset path) s2 p2.NextTag]),
                  pc := s_mid.pc + 1 + 1 } csPrefix :=
            LocalBindingSim.insert_fresh_reg h_lbs1 h_prb
              (Nat.le_trans h_pregmono (Nat.le_succ _)) rfl
          intro τ' loc' binding' h_env'
          obtain ⟨reg', base', tag', h_pi', h_entry', h_ra', h_rt', h_nw', h_dom'⟩ :=
            h_lbs2 loc' binding' h_env'
          refine ⟨reg', base', tag', ?_, h_entry', h_ra', h_rt', h_nw', h_dom'⟩
          rw [h_stmtRun, getPlaceInfo_emit, getPlaceInfo_emit, getPlaceInfo_emit,
            getPlaceInfo_setNextReg, getPlaceInfo_emit, getPlaceInfo_setNextReg]
          show (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).placeRegMap.lookup loc'.idx.1 = _
          rw [h_pprm]
          exact h_pi'
        · exact h_sms'
        · show TagRenameBounded ρt perms''.NextTag q3.NextTag
          rw [sb_write_NextTag h_useMut_src, sb_read_NextTag h_qread, h_pnt1]
          refine TagRenameBounded.mono h_tbd (Nat.le_refl _) ?_
          have hA : s_osea.perms.NextTag = p2.NextTag := by
            rw [sb_read_NextTag h_read_tgt, h_pnt2]
          have hB : p2.NextTag ≤ q3.NextTag := by
            rw [← sb_write_NextTag h_useMut_tgt]
            exact h_ntle
          rw [hA]
          exact hB
        · simp only [AllocLockstep, mirlite_writeWordSeq_addrStart,
            oseair_writeWordSeq_addrStart, h_pmem]
          exact h_alloc
        · intro τ' loc' h_none
          rw [h_stmtRun, getPlaceInfo_emit, getPlaceInfo_emit, getPlaceInfo_emit,
            getPlaceInfo_setNextReg, getPlaceInfo_emit, getPlaceInfo_setNextReg]
          show (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).placeRegMap.lookup loc'.idx.1 = none
          rw [h_pprm]
          exact h_unmap loc' h_none
        · intro idx reg'' τ'' h_look
          rw [h_stmtRun] at h_look ⊢
          rw [getPlaceInfo_emit, getPlaceInfo_emit, getPlaceInfo_emit,
            getPlaceInfo_setNextReg, getPlaceInfo_emit, getPlaceInfo_setNextReg] at h_look
          have h_cs : getPlaceInfo csPrefix idx = some (reg'', τ'') := by
            show csPrefix.placeRegMap.lookup idx = _
            rw [← h_pprm]
            exact h_look
          refine RegisterBelow.mono ?_ (h_prb _ _ _ h_cs)
          simp only [emit]
          exact Nat.le_trans h_pregmono (Nat.le_trans (Nat.le_succ _) (Nat.le_succ _))
      · simp at h_w

/-- REGIME C0, CLOSED: constant write to a ZERO-offset projection off a
    bound local. `placeToRegChecked` returns the base's own register, so
    the fragment is a bare `CStore` and this is regime A with a wider
    `allocSize` — the projected place's bounds come from the BASE's
    layout, not from `NatL`. No `Borrow`, hence no BRIDGE 1. -/
theorem const_write_proj_zero_simulation
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {σ : LayoutTy} {loc : Local Γ σ} {path : PathTo σ obseq.LayoutTy.NatL}
    {binding : mirlite.Binding}
    (compProg : oseair.Prog)
    (v : Word)
    (h_off : pathOffset path = 0)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    {stmt0 : Stmt Γ}
    (h_stmt : prog.get? s_mir.pc = some stmt0)
    (h_run0 : ∀ cs, CheckedCompilerM.run (compileStmtChecked stmt0) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.proj (.local loc) path) (.constInit v))) cs)
    (h_val0 : ∀ cs so, CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.proj (.local loc) path) (.constInit v))) cs
        = Except.ok so →
      ∃ so', CheckedCompilerM.value (compileStmtChecked stmt0) cs
        = Except.ok so')
    (h_env : mirlite.Env.lookup s_mir.env loc = some binding)
    (h_write : mirlite.writeResolvedPlace (τ := obseq.LayoutTy.NatL) MSB s_mir
        { addr := binding.addr + pathOffset path, tag := binding.tag,
          allocBase := binding.addr, allocSize := blockSize σ }
        [mirlite.MemValue.word v] rfl = .ok s_mir') :
    ∃ (s_osea' : oseair.State MSB) (n : Nat),
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa ρt s_mir' s_osea' := by
  obtain ⟨csPrefix, ⟨h_csAt, h_pc⟩, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_tbd,
    h_alloc, h_unmap, h_prb⟩ := h_inv
  obtain ⟨reg, base, tag, h_pi, h_entry, h_ra, h_rt, h_nw, h_dom⟩ :=
    h_lbs loc binding h_env
  have h_base : base = binding.addr := (h_id_a _ _ h_ra).symm
  subst h_base
  -- source permission step
  have h_w := h_write
  simp only [mirlite.writeResolvedPlace] at h_w
  split at h_w
  · simp at h_w
  · rename_i h_nb
    split at h_w
    · rename_i perms' h_useMut_src
      cases h_w
      obtain ⟨p2, h_useMut_tgt, h_psim'⟩ :=
        sb_write_respects_PermSim h_psim h_wf_t h_rt h_nw h_useMut_src
      -- the fragment: one CStore through the base's register
      have h_mapped : PlaceInputsMapped csPrefix (Place.proj (Place.local loc) path) :=
        ⟨reg, σ, h_pi⟩
      have h_root := ensurePlaceRoot_run_eq_of_mapped
        (p := Place.proj (Place.local loc) path) h_mapped
      obtain ⟨h_brun, baseOut, h_bval, h_bres⟩ :=
        placeToRegChecked_local_existing (kind := RefKind.Mut) h_pi
      have h_stmtRunC := compileStmt_proj_zero_run (cs := csPrefix) (baseOut := baseOut)
        (fun _ _ _ h => by cases h) v h_off h_root h_brun h_bval h_bres
      have h_stmtRun := (h_run0 csPrefix).trans h_stmtRunC
      obtain ⟨stmtOutC, h_stmtOutC⟩ :
          ∃ so, CheckedCompilerM.value
            (compileStmtChecked (Stmt.assign (.proj (.local loc) path) (.constInit v)))
            csPrefix = Except.ok so := by
        obtain ⟨dstOut, h_dstOut⟩ :=
          placeToRegChecked_ok_of_placeInputsMapped (cs := csPrefix)
            (kind := RefKind.Mut) (p := Place.proj (Place.local loc) path) h_mapped
        exact ⟨{ result := (),
                 evidence := StmtEvidence.assignPlace (.proj (.local loc) path)
                   (.constInit v) dstOut.result dstOut.evidence
                   (RExprToEvidence.constInit v) },
               by simp [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked, h_dstOut, h_root]⟩
      obtain ⟨stmtOut, h_stmtOut⟩ := h_val0 csPrefix stmtOutC h_stmtOutC
      have h_code : compProg s_osea.pc
          = some (Instr.CStore obseq.TyVal.NatTy [Val.Dat v] reg) := by
        rw [h_pc]
        refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
        · rw [h_stmtRun]; simp [emit]
        · rw [h_stmtRun]
          have h := emit_code_at_new csPrefix
            [Instr.CStore obseq.TyVal.NatTy [Val.Dat v] reg] (k := 0) (by simp)
          simpa using h
      -- BRIDGE 2 at the projected address
      have h_entry' : PtrRegisterEntry s_osea.reg reg binding.addr
          (binding.addr + pathOffset path - binding.addr) (blockSize σ) tag := by
        rw [h_off, Nat.add_zero, Nat.sub_self]
        exact h_entry
      obtain ⟨h_wtp, h_sms'⟩ :=
        writeThroughPtr_sim (τ := obseq.LayoutTy.NatL)
          (resolved := { addr := binding.addr + pathOffset path, tag := binding.tag,
                         allocBase := binding.addr, allocSize := blockSize σ })
          "CStore Invalid Ptr" [mirlite.MemValue.word v] [Val.Dat v] rfl
          ⟨rfl, trivial⟩ h_id_a h_entry' h_useMut_tgt h_sms
          (by simp [h_off])
          (fun k hk => by
            simp [Nat.lt_one_iff] at hk
            subst hk
            simpa [h_off] using h_ra)
          h_write
      have h_run := runN_CStore_step compProg s_osea _
        obseq.TyVal.NatTy [Val.Dat v] reg h_code rfl h_wtp
      refine ⟨_, 1, h_run, ?_⟩
      refine ⟨CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix,
        ⟨prefixCompileState_succ h_csAt h_stmt h_stmtOut, ?_⟩, ?_, h_sms', h_psim',
        h_id_a, h_wf_t, ?_, ?_, ?_, ?_⟩
      · show s_osea.pc + 1 = _
        rw [h_stmtRun, h_pc]; simp [emit]
      · intro τ' loc' binding' h_env'
        obtain ⟨reg', base', tag', h_pi', h_entry'', h_ra', h_rt', h_nw', h_dom'⟩ :=
          h_lbs loc' binding' h_env'
        refine ⟨reg', base', tag', ?_, h_entry'', h_ra', h_rt', h_nw', h_dom'⟩
        rw [h_stmtRun, getPlaceInfo_emit]
        exact h_pi'
      · show TagRenameBounded ρt perms'.NextTag p2.NextTag
        rw [sb_write_NextTag h_useMut_src, sb_write_NextTag h_useMut_tgt]
        exact h_tbd
      · simp only [AllocLockstep, mirlite_writeWordSeq_addrStart,
          oseair_writeWordSeq_addrStart]
        exact h_alloc
      · intro τ' loc' h_none
        rw [h_stmtRun, getPlaceInfo_emit]
        exact h_unmap loc' h_none
      · intro idx reg'' τ'' h_look
        rw [h_stmtRun] at h_look ⊢
        rw [getPlaceInfo_emit] at h_look
        exact h_prb _ _ _ h_look
    · simp at h_w

/-- REGIME C1, CLOSED: constant write to a NONZERO-offset projection off
    a bound local. The fragment is `Borrow(Mut); CStore; Die` — the first
    closed regime whose target mints a tag, uses it, and then kills it,
    which is exactly the shape BRIDGE 1 (`sb_ref_use_die_cancels`) was
    proved for: that three-op sequence is equivalent, on the stacks, to
    the bare parent write the source performs.

    Two side conditions BRIDGE 1 needs are DERIVED rather than assumed:
    the retag succeeds because the corresponding write does
    (`sb_ref_Mut_ok_of_sb_write_ok`), and the fresh tag is unprotected
    because ρt's range lies below the counter
    (`freshTag_not_protected`). -/
theorem const_write_proj_offset_simulation
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {σ : LayoutTy} {loc : Local Γ σ} {path : PathTo σ obseq.LayoutTy.NatL}
    {binding : mirlite.Binding}
    (compProg : oseair.Prog)
    (v : Word)
    (h_off : pathOffset path ≠ 0)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    -- the PROGRAM's statement may be a reassociation-equivalent spelling
    -- of the canonical one (nested projections flatten in the lowering);
    -- only its compiled RUN/VALUE matter
    {stmt0 : Stmt Γ}
    (h_stmt : prog.get? s_mir.pc = some stmt0)
    (h_run0 : ∀ cs, CheckedCompilerM.run (compileStmtChecked stmt0) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.proj (.local loc) path) (.constInit v))) cs)
    (h_val0 : ∀ cs so, CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.proj (.local loc) path) (.constInit v))) cs
        = Except.ok so →
      ∃ so', CheckedCompilerM.value (compileStmtChecked stmt0) cs
        = Except.ok so')
    (h_env : mirlite.Env.lookup s_mir.env loc = some binding)
    (h_write : mirlite.writeResolvedPlace (τ := obseq.LayoutTy.NatL) MSB s_mir
        { addr := binding.addr + pathOffset path, tag := binding.tag,
          allocBase := binding.addr, allocSize := blockSize σ }
        [mirlite.MemValue.word v] rfl = .ok s_mir') :
    ∃ (s_osea' : oseair.State MSB) (n : Nat),
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa ρt s_mir' s_osea' := by
  obtain ⟨csPrefix, ⟨h_csAt, h_pc⟩, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_tbd,
    h_alloc, h_unmap, h_prb⟩ := h_inv
  obtain ⟨reg, base, tag, h_pi, h_entry, h_ra, h_rt, h_nw, h_dom⟩ :=
    h_lbs loc binding h_env
  have h_base : base = binding.addr := (h_id_a _ _ h_ra).symm
  subst h_base
  have h_w := h_write
  simp only [mirlite.writeResolvedPlace] at h_w
  split at h_w
  · simp at h_w
  · rename_i h_nb
    split at h_w
    · rename_i perms' h_useMut_src
      cases h_w
      -- the target's DIRECT write (what BRIDGE 1 says the triple equals)
      obtain ⟨qAcc, h_useMut_tgt, h_psim'⟩ :=
        sb_write_respects_PermSim h_psim h_wf_t h_rt h_nw h_useMut_src
      -- the target's retag succeeds, and its fresh tag is usable
      obtain ⟨q1, h_ref_tgt⟩ :=
        sb_ref_Mut_ok_of_sb_write_ok h_useMut_tgt
      have h_unprot := freshTag_not_protected h_psim h_tbd
      have h0 : wildcardTag < s_osea.perms.NextTag := (h_tbd _ _ h_wf_t.2).2
      have h_nt : (s_osea.perms.NextTag == wildcardTag) = false := by grind
      obtain ⟨q2, q3, qAcc', h_wr1, h_die1, h_wr2, h_sm, h_ex, h_pf, h_ntle⟩ :=
        sb_ref_use_die_cancels h_nt h_unprot h_ref_tgt
      -- BRIDGE 1's own direct write is the one BRIDGE 3 produced
      have h_qAcc : qAcc' = qAcc := by
        rw [h_useMut_tgt] at h_wr2
        injection h_wr2 with h_e
        exact h_e.symm
      subst h_qAcc
      -- the fragment: Borrow; CStore; Die
      have h_mapped : PlaceInputsMapped csPrefix (Place.proj (Place.local loc) path) :=
        ⟨reg, σ, h_pi⟩
      have h_root := ensurePlaceRoot_run_eq_of_mapped
        (p := Place.proj (Place.local loc) path) h_mapped
      obtain ⟨h_brun, baseOut, h_bval, h_bres⟩ :=
        placeToRegChecked_local_existing (kind := RefKind.Mut) h_pi
      have h_stmtRunC := compileStmt_proj_offset_run (cs := csPrefix) (baseOut := baseOut)
        (fun _ _ _ h => by cases h) v h_off h_root h_brun h_bval h_bres
      have h_stmtRun := (h_run0 csPrefix).trans h_stmtRunC
      obtain ⟨stmtOutC, h_stmtOutC⟩ :
          ∃ so, CheckedCompilerM.value
            (compileStmtChecked (Stmt.assign (.proj (.local loc) path) (.constInit v)))
            csPrefix = Except.ok so := by
        obtain ⟨dstOut, h_dstOut⟩ :=
          placeToRegChecked_ok_of_placeInputsMapped (cs := csPrefix)
            (kind := RefKind.Mut) (p := Place.proj (Place.local loc) path) h_mapped
        exact ⟨{ result := (),
                 evidence := StmtEvidence.assignPlace (.proj (.local loc) path)
                   (.constInit v) dstOut.result dstOut.evidence
                   (RExprToEvidence.constInit v) },
               by simp [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked, h_dstOut, h_root]⟩
      obtain ⟨stmtOut, h_stmtOut⟩ := h_val0 csPrefix stmtOutC h_stmtOutC
      have h_len3 : ((emit (emit (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
          [Instr.Assgn (Register.R csPrefix.nextReg)
            (borrowRhs RefKind.Mut (blockSize obseq.LayoutTy.NatL) reg (pathOffset path))])
          [Instr.CStore obseq.TyVal.NatTy [Val.Dat v] (Register.R csPrefix.nextReg)])
          [Instr.Die (Register.R csPrefix.nextReg) (blockSize obseq.LayoutTy.NatL)])).nextLabel
          = csPrefix.nextLabel + 3 := by
        simp only [emit, List.length_cons, List.length_nil]
      have h_code1 : compProg s_osea.pc
          = some (Instr.Assgn (Register.R csPrefix.nextReg)
              (borrowRhs RefKind.Mut (blockSize obseq.LayoutTy.NatL) reg (pathOffset path))) := by
        rw [h_pc]
        refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
        · rw [h_stmtRun, h_len3]; omega
        · rw [h_stmtRun]
          rw [emit_code_lt_nextLabel _ _ (by
            simp only [emit, List.length_cons, List.length_nil]; omega)]
          rw [emit_code_lt_nextLabel _ _ (by
            simp only [emit, List.length_cons, List.length_nil]; omega)]
          have h := emit_code_at_new { csPrefix with nextReg := csPrefix.nextReg + 1 }
            [Instr.Assgn (Register.R csPrefix.nextReg)
              (borrowRhs RefKind.Mut (blockSize obseq.LayoutTy.NatL) reg (pathOffset path))]
            (k := 0) (by simp)
          simpa using h
      have h_code2 : compProg (s_osea.pc + 1)
          = some (Instr.CStore obseq.TyVal.NatTy [Val.Dat v]
              (Register.R csPrefix.nextReg)) := by
        rw [h_pc]
        refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
        · rw [h_stmtRun, h_len3]; omega
        · rw [h_stmtRun]
          rw [emit_code_lt_nextLabel _ _ (by
            simp only [emit, List.length_cons, List.length_nil]; omega)]
          have h := emit_code_at_new
            (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
              [Instr.Assgn (Register.R csPrefix.nextReg)
                (borrowRhs RefKind.Mut (blockSize obseq.LayoutTy.NatL) reg (pathOffset path))])
            [Instr.CStore obseq.TyVal.NatTy [Val.Dat v] (Register.R csPrefix.nextReg)]
            (k := 0) (by simp)
          simpa [emit] using h
      have h_code3 : compProg (s_osea.pc + 1 + 1)
          = some (Instr.Die (Register.R csPrefix.nextReg)
              (blockSize obseq.LayoutTy.NatL)) := by
        rw [h_pc]
        refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
        · rw [h_stmtRun, h_len3]; omega
        · rw [h_stmtRun]
          have h := emit_code_at_new
            (emit (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
              [Instr.Assgn (Register.R csPrefix.nextReg)
                (borrowRhs RefKind.Mut (blockSize obseq.LayoutTy.NatL) reg (pathOffset path))])
              [Instr.CStore obseq.TyVal.NatTy [Val.Dat v] (Register.R csPrefix.nextReg)])
            [Instr.Die (Register.R csPrefix.nextReg) (blockSize obseq.LayoutTy.NatL)]
            (k := 0) (by simp)
          simpa [emit] using h
      -- §execute: Borrow, then the store through the fresh tag, then Die
      have h_ref_tgt' : MSB.ref s_osea.perms (binding.addr + 0 + pathOffset path)
          (blockSize obseq.LayoutTy.NatL) tag RefKind.Mut false []
          = .ok (q1, s_osea.perms.NextTag) := by
        simpa using h_ref_tgt
      have h_off_lt : pathOffset path < blockSize σ := by
        have h1 := Nat.not_lt.mp h_nb
        simp only [List.length_cons, List.length_nil, Nat.add_assoc] at h1
        exact Nat.le_of_add_le_add_left h1
      have h_le1 : binding.addr + 0 + pathOffset path + blockSize obseq.LayoutTy.NatL
          ≤ binding.addr + blockSize σ := by
        simp only [Nat.add_zero]
        simpa [blockSize] using Nat.not_lt.mp h_nb
      have h_run1 := runN_Assgn_Borrow_step compProg s_osea
        (Register.R csPrefix.nextReg) reg RefKind.Mut false []
        (blockSize obseq.LayoutTy.NatL) (pathOffset path)
        h_code1 h_entry h_le1 h_ref_tgt'
      have h_off_eq : binding.addr + pathOffset path - binding.addr
          = 0 + pathOffset path := by
        simp
      have h_entry1 : PtrRegisterEntry
          (oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
            (obseq.TyVal.PTy, [Val.Ptr binding.addr (0 + pathOffset path) (blockSize σ)
              s_osea.perms.NextTag]))
          (Register.R csPrefix.nextReg) binding.addr
          (binding.addr + pathOffset path - binding.addr) (blockSize σ)
          s_osea.perms.NextTag := by
        rw [h_off_eq]
        exact RegMap.lookup_insert_self _ _ _
      obtain ⟨h_wtp, h_sms'⟩ :=
        writeThroughPtr_sim (τ := obseq.LayoutTy.NatL)
          (s_osea :=
            { s_osea with
                perms := q1,
                reg := oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
                  (obseq.TyVal.PTy,
                    [Val.Ptr binding.addr (0 + pathOffset path) (blockSize σ)
                      s_osea.perms.NextTag]),
                pc := s_osea.pc + 1 })
          (resolved := { addr := binding.addr + pathOffset path, tag := binding.tag,
                         allocBase := binding.addr, allocSize := blockSize σ })
          "CStore Invalid Ptr" [mirlite.MemValue.word v] [Val.Dat v] rfl
          ⟨rfl, trivial⟩ h_id_a h_entry1 (by simpa using h_wr1) h_sms
          (by simp)
          (fun k hk => by
            have hk0 : k = 0 := by simpa using hk
            subst hk0
            obtain ⟨a', ha'⟩ := h_dom (pathOffset path) h_off_lt
            have h_id := h_id_a _ _ ha'
            rw [h_id] at ha'
            rw [Nat.add_zero, h_id]
            exact ha')
          h_write
      have h_run2 := runN_CStore_step compProg _ _
        obseq.TyVal.NatTy [Val.Dat v] (Register.R csPrefix.nextReg) h_code2 rfl h_wtp
      have h_run3 := runN_Die_step compProg
        { s_osea with
            perms := q2,
            reg := oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
              (obseq.TyVal.PTy,
                [Val.Ptr binding.addr (0 + pathOffset path) (blockSize σ)
                  s_osea.perms.NextTag]),
            mem := oseair.writeWordSeq s_osea.mem (binding.addr + pathOffset path)
              [Val.Dat v],
            pc := s_osea.pc + 1 + 1 }
        (Register.R csPrefix.nextReg) (blockSize obseq.LayoutTy.NatL)
        h_code3 (RegMap.lookup_insert_self _ _ _) (by simpa using h_die1)
      have h_run :=
        (oseair_runN_add (1 + 1) 1 s_osea compProg _
          ((oseair_runN_add 1 1 s_osea compProg _ h_run1).trans h_run2)).trans h_run3
      refine ⟨_, 1 + 1 + 1, h_run, ?_⟩
      -- PermSim across the triple: BRIDGE 1 says the net stack effect is
      -- the bare parent write, which BRIDGE 3 already related
      have h_psim3 : PermSim ρt perms' q3 := by
        obtain ⟨hs, hp, he, hn⟩ := h_psim'
        exact ⟨by rw [h_sm]; exact hs, by rw [h_pf]; exact hp,
               by rw [h_ex]; exact he, Nat.le_trans hn h_ntle⟩
      refine ⟨CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix,
        ⟨prefixCompileState_succ h_csAt h_stmt h_stmtOut, ?_⟩, ?_, h_sms', h_psim3,
        h_id_a, h_wf_t, ?_, ?_, ?_, ?_⟩
      · show s_osea.pc + 1 + 1 + 1 = _
        rw [h_pc, h_stmtRun, h_len3]
      · refine LocalBindingSim.placeRegMap_congr ?_
          (LocalBindingSim.insert_fresh_reg h_lbs h_prb (Nat.le_refl _) rfl)
        rw [h_stmtRun]
        simp [emit]
      · show TagRenameBounded ρt perms'.NextTag q3.NextTag
        rw [sb_write_NextTag h_useMut_src]
        exact TagRenameBounded.mono h_tbd (Nat.le_refl _)
          (Nat.le_trans (Nat.le_of_eq (sb_write_NextTag h_useMut_tgt).symm) h_ntle)
      · simp only [AllocLockstep, mirlite_writeWordSeq_addrStart,
          oseair_writeWordSeq_addrStart]
        exact h_alloc
      · intro τ' loc' h_none
        rw [h_stmtRun, getPlaceInfo_emit, getPlaceInfo_emit, getPlaceInfo_emit,
          getPlaceInfo_setNextReg]
        exact h_unmap loc' h_none
      · intro idx reg'' τ'' h_look
        rw [h_stmtRun] at h_look ⊢
        rw [getPlaceInfo_emit, getPlaceInfo_emit, getPlaceInfo_emit,
          getPlaceInfo_setNextReg] at h_look
        refine RegisterBelow.mono ?_ (h_prb _ _ _ h_look)
        simp only [emit]
        omega
    · simp at h_w

/-- REGIME D (spine), CLOSED: constant write through a dereferenced load
    spine — `*p := v`, `**q := v`, and every deeper all-deref shape at
    once. The spine executes via `loadSpine_lowering_sim`; the final
    pointer is loaded (SB read matched by `resolvePlaceAcc`'s read at this
    level, transported by the `sb_read` BRIDGE-3 member; value recovered
    by `MemValSim` inversion); the `CStore` through it is BRIDGE 2 + the
    `sb_write` member. The fresh-root case is vacuous —
    `preparePlaceAssign` cannot allocate under a deref. -/
theorem const_write_deref_spine_simulation
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_pre s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {ptrPlace : Place Γ (obseq.LayoutTy.PtrL obseq.LayoutTy.NatL)}
    {resolved : mirlite.PlaceRes} {permsD : MSB.State}
    (compProg : oseair.Prog)
    (v : Word)
    (h_spine : LoadSpine ptrPlace)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    {stmt0 : Stmt Γ}
    (h_stmt : prog.get? s_mir.pc = some stmt0)
    (h_run0 : ∀ cs, CheckedCompilerM.run (compileStmtChecked stmt0) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.deref ptrPlace) (.constInit v))) cs)
    (h_val0 : ∀ cs so, CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.deref ptrPlace) (.constInit v))) cs
        = Except.ok so →
      ∃ so', CheckedCompilerM.value (compileStmtChecked stmt0) cs
        = Except.ok so')
    (h_prep : mirlite.preparePlaceAssign MSB s_mir (.deref ptrPlace) = .ok s_pre)
    (h_res  : mirlite.resolvePlaceAcc MSB s_pre (.deref ptrPlace) = .ok (resolved, permsD))
    (h_write : mirlite.writeResolvedPlace (τ := obseq.LayoutTy.NatL)
                 MSB { s_pre with perms := permsD } resolved
                 [mirlite.MemValue.word v] rfl = .ok s_mir') :
    ∃ (s_osea' : oseair.State MSB) (n : Nat),
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa ρt s_mir' s_osea' := by
  have h_pre : s_pre = s_mir ∧
      ∃ r0, mirlite.resolvePlace? s_mir (.deref ptrPlace) = some r0 := by
    simp only [mirlite.preparePlaceAssign] at h_prep
    split at h_prep
    · rename_i r0 h_r0
      cases h_prep
      exact ⟨rfl, r0, h_r0⟩
    · simp [mirlite.allocateRoot] at h_prep
  obtain ⟨h_pre_eq, r0, h_resolved⟩ := h_pre
  rw [h_pre_eq] at h_res h_write
  obtain ⟨csPrefix, ⟨h_csAt, h_pc⟩, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_tbd, h_alloc, h_unmap, h_prb⟩ := h_inv
  have h_mapped : PlaceInputsMapped csPrefix (Place.deref ptrPlace) :=
    placeInputsMapped_of_localBindingSim_resolvePlace h_lbs h_resolved
  have h_root := ensurePlaceRoot_run_eq_of_mapped h_mapped
  obtain ⟨dstOut, h_dstOut⟩ := placeToRegChecked_ok_of_placeInputsMapped
    (cs := csPrefix) (kind := RefKind.Mut) (p := .deref ptrPlace) h_mapped
  obtain ⟨stmtOutC, h_stmtOutC⟩ : ∃ so, CheckedCompilerM.value
      (compileStmtChecked (Stmt.assign (.deref ptrPlace) (.constInit v)))
      csPrefix = Except.ok so :=
    ⟨{ result := (),
       evidence := StmtEvidence.assignPlace (.deref ptrPlace) (.constInit v)
         dstOut.result dstOut.evidence (RExprToEvidence.constInit v) },
     by simp [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked, h_dstOut, h_root]⟩
  obtain ⟨stmtOut, h_stmtOut⟩ := h_val0 csPrefix stmtOutC h_stmtOutC
  -- unfold one resolveAcc level
  simp only [mirlite.resolvePlaceAcc] at h_res
  cases h_qres : mirlite.resolvePlaceAcc MSB s_mir ptrPlace with
  | error e => simp [h_qres] at h_res
  | ok pr =>
  obtain ⟨pRes, permsP⟩ := pr
  simp only [h_qres] at h_res
  by_cases h_qb : pRes.addr < pRes.allocBase ∨
      pRes.addr ≥ pRes.allocBase + pRes.allocSize
  · rw [if_pos h_qb] at h_res
    exact absurd h_res (by simp)
  · rw [if_neg h_qb] at h_res
    cases h_qread : MSB.read permsP pRes.addr 1 pRes.tag with
    | error e => simp [h_qread] at h_res
    | ok permsP' =>
    simp only [h_qread] at h_res
    cases h_qfind : mirlite.Mem.find? s_mir.mem pRes.addr with
    | none => simp [h_qfind] at h_res
    | some mv =>
    cases mv with
    | undef => simp [h_qfind] at h_res
    | word w => simp [h_qfind] at h_res
    | ptrVal b o sz t =>
    simp only [h_qfind, Except.ok.injEq, Prod.mk.injEq] at h_res
    obtain ⟨h_r1, h_r2⟩ := h_res
    subst h_r1
    subst h_r2
    -- the spine's fragment sits inside the statement's fragment
    have h_bindD : placeToRegChecked (Γ := Γ) RefKind.Mut (.deref ptrPlace)
        = (do
            let ptrOut ← placeToRegChecked RefKind.Shared ptrPlace
            let ptrRes := ptrOut.result
            let loadedReg ← CheckedCompilerM.lift freshRegM
            let _ ← CheckedCompilerM.lift
              (emitM [Instr.Assgn loadedReg (Rhs.Load obseq.TyVal.PTy ptrRes.reg)])
            let _ ← CheckedCompilerM.lift (emitM (cleanupInstrs ptrRes.cleanup))
            pure {
              result := { reg := loadedReg, cleanup := [] },
              evidence := PlaceToRegEvidence.deref ptrPlace ptrRes loadedReg ptrOut.evidence
            }) := by simp only [placeToRegChecked]
    have h_stmt_bind : compileStmtChecked (Stmt.assign (.deref ptrPlace) (.constInit v))
        = (do
            let _ ← CheckedCompilerM.lift (ensurePlaceRoot (Place.deref ptrPlace))
            let dstOut ← placeToRegChecked RefKind.Mut (.deref ptrPlace)
            let dstRes := dstOut.result
            let rhsOut ← compileRExprToChecked dstRes.reg (.constInit v)
            let _ ← CheckedCompilerM.lift (emitM (cleanupInstrs dstRes.cleanup))
            pure {
              result := (),
              evidence := StmtEvidence.assignPlace (.deref ptrPlace) (.constInit v)
                dstRes dstOut.evidence rhsOut.evidence
            }) := rfl
    have h_incr0 : StateIncr (CheckedCompilerM.run (placeToRegChecked RefKind.Shared ptrPlace) csPrefix)
        (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (.deref ptrPlace)) csPrefix) := by
      rw [h_bindD, CheckedCompilerM.run_bind]
      cases h : CheckedCompilerM.value (placeToRegChecked RefKind.Shared ptrPlace) csPrefix with
      | ok a => exact CheckedCompilerM.incr _ _
      | error e => exact StateIncr.refl _
    have h_incr1 : StateIncr
        (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (.deref ptrPlace)) csPrefix)
        (CheckedCompilerM.run
          (compileStmtChecked (Stmt.assign (.deref ptrPlace) (.constInit v))) csPrefix) := by
      rw [h_stmt_bind]
      rw [CheckedCompilerM.run_bind]
      simp only [CheckedCompilerM.value_lift, CheckedCompilerM.run_lift, h_root]
      rw [CheckedCompilerM.run_bind]
      cases h : CheckedCompilerM.value
          (placeToRegChecked RefKind.Mut (.deref ptrPlace)) csPrefix with
      | ok a => exact CheckedCompilerM.incr _ _
      | error e => exact StateIncr.refl _
    have h_instP : ∀ q' instr,
        q' < (CheckedCompilerM.run (placeToRegChecked RefKind.Shared ptrPlace) csPrefix).nextLabel →
        (CheckedCompilerM.run (placeToRegChecked RefKind.Shared ptrPlace) csPrefix).code q' = some instr →
        compProg q' = some instr := by
      intro q' instr h_lt h_code
      have h_incrP := StateIncr.trans h_incr0 h_incr1
      refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
      · rw [h_run0 csPrefix]
        exact Nat.lt_of_lt_of_le h_lt h_incrP.nextLabel_le
      · rw [h_run0 csPrefix, h_incrP.code_eq q' h_lt]
        exact h_code
    -- run the spine
    obtain ⟨pOut, n1, s_mid, ptag, h_pval, h_pclean, h_prun, h_ppc, h_pmem, h_ppsim,
      h_pnt1, h_pnt2, h_plbs, h_pentry, h_prt, h_pnw, h_ple, h_prange, h_pbelow,
      h_pprm, h_pregmono, h_plabmono⟩ :=
      loadSpine_lowering_sim h_id_a h_wf_t h_spine RefKind.Shared csPrefix s_osea
        pRes permsP h_qres h_lbs h_prb h_sms h_psim h_pc h_instP
    have h_stmtRunC := compileStmt_deref_run v h_root h_pval h_pclean
    have h_stmtRun := (h_run0 csPrefix).trans h_stmtRunC
    -- pointer-place bounds from the dereferenceable check
    have h_cancel : pRes.allocBase + (pRes.addr - pRes.allocBase) = pRes.addr := by
      grind
    have h_off : pRes.addr - pRes.allocBase < pRes.allocSize := by grind
    -- the final Load
    have h_code1 : compProg s_mid.pc = some (Instr.Assgn
        (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared ptrPlace) csPrefix).nextReg)
        (Rhs.Load obseq.TyVal.PTy pOut.result.reg)) := by
      rw [h_ppc]
      refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
      · rw [h_stmtRun]
        show (CheckedCompilerM.run (placeToRegChecked RefKind.Shared ptrPlace) csPrefix).nextLabel < (CheckedCompilerM.run (placeToRegChecked RefKind.Shared ptrPlace) csPrefix).nextLabel + 1 + 1
        omega
      · rw [h_stmtRun]
        rw [emit_code_lt_nextLabel _ _
          (by show (CheckedCompilerM.run (placeToRegChecked RefKind.Shared ptrPlace) csPrefix).nextLabel < (CheckedCompilerM.run (placeToRegChecked RefKind.Shared ptrPlace) csPrefix).nextLabel + 1; omega)]
        have h := emit_code_at_new
          { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared ptrPlace) csPrefix) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared ptrPlace) csPrefix).nextReg + 1 }
          [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared ptrPlace) csPrefix).nextReg)
            (Rhs.Load obseq.TyVal.PTy pOut.result.reg)]
          (k := 0) (by simp)
        simpa using h
    obtain ⟨p2, h_read_tgt, h_psim2⟩ :=
      sb_read_respects_PermSim h_ppsim h_wf_t h_prt h_pnw h_qread
    have h_read_tgt' : MSB.read s_mid.perms
        (pRes.allocBase + (pRes.addr - pRes.allocBase)) 1 ptag = .ok p2 := by
      rw [h_cancel]
      exact h_read_tgt
    have h_run1 := runN_Assgn_Load_ptr_step compProg s_mid
      (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared ptrPlace) csPrefix).nextReg)
      pOut.result.reg obseq.TyVal.PTy h_code1 h_pentry h_off h_read_tgt'
    -- the loaded cell holds the ρ-renamed final pointer
    obtain ⟨addr', value', h_ra', h_find_tgt, h_mvs⟩ := h_sms _ _ h_qfind
    have h_addr' : addr' = pRes.addr := (h_id_a _ _ h_ra').symm
    subst h_addr'
    cases value' with
    | Undef => exact h_mvs.elim
    | Dat _ => exact h_mvs.elim
    | Ptr b2 o2 s2 t2 =>
    obtain ⟨h_b, h_o, h_s, h_t, h_tnw, h_range⟩ := h_mvs
    have h_b2 : b2 = b := (h_id_a _ _ h_b).symm
    subst h_b2
    subst h_o
    subst h_s
    have h_rws : oseair.readWordSeq s_mid.mem
        (pRes.allocBase + (pRes.addr - pRes.allocBase))
        (obseq.typeSize obseq.TyVal.PTy) = [Val.Ptr b2 o2 s2 t2] := by
      rw [h_cancel]
      show oseair.readWordSeq s_mid.mem pRes.addr 1 = _
      rw [h_pmem]
      simp [oseair.readWordSeq, h_find_tgt]
    -- the CStore through the loaded pointer
    have h_code2 : compProg (s_mid.pc + 1) = some (Instr.CStore obseq.TyVal.NatTy
        [Val.Dat v] (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared ptrPlace) csPrefix).nextReg)) := by
      rw [h_ppc]
      refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
      · rw [h_stmtRun]
        show (CheckedCompilerM.run (placeToRegChecked RefKind.Shared ptrPlace) csPrefix).nextLabel + 1 < (CheckedCompilerM.run (placeToRegChecked RefKind.Shared ptrPlace) csPrefix).nextLabel + 1 + 1
        omega
      · rw [h_stmtRun]
        have h := emit_code_at_new
          (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared ptrPlace) csPrefix) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared ptrPlace) csPrefix).nextReg + 1 }
            [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared ptrPlace) csPrefix).nextReg)
              (Rhs.Load obseq.TyVal.PTy pOut.result.reg)])
          [Instr.CStore obseq.TyVal.NatTy [Val.Dat v]
            (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared ptrPlace) csPrefix).nextReg)]
          (k := 0) (by simp)
        simpa [emit] using h
    have h_w := h_write
    simp only [mirlite.writeResolvedPlace] at h_w
    split at h_w
    · simp at h_w
    · rename_i h_nb
      split at h_w
      · rename_i perms' h_useMut_src
        cases h_w
        have h_osz : o2 < s2 := by
          have h1 : b2 + o2 + 1 ≤ b2 + s2 := Nat.le_of_not_lt (by simpa using h_nb)
          exact Nat.lt_of_add_lt_add_left (Nat.lt_of_succ_le h1)
        obtain ⟨p3, h_useMut_tgt, h_psim3⟩ :=
          sb_write_respects_PermSim h_psim2 h_wf_t h_t h_tnw h_useMut_src
        have h_entry1 : PtrRegisterEntry
            (oseair.RegMap.insert s_mid.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared ptrPlace) csPrefix).nextReg)
              (obseq.TyVal.PTy, oseair.readWordSeq s_mid.mem
                (pRes.allocBase + (pRes.addr - pRes.allocBase))
                (obseq.typeSize obseq.TyVal.PTy)))
            (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared ptrPlace) csPrefix).nextReg) b2 ((b2 + o2) - b2) s2 t2 := by
          show oseair.RegMap.lookup _ _ = _
          rw [Nat.add_sub_cancel_left, RegMap.lookup_insert_self, h_rws]
        obtain ⟨h_wtp, h_sms'⟩ :=
          writeThroughPtr_sim (ρa := ρa) (ρt := ρt) (τ := obseq.LayoutTy.NatL)
            (s_pre := { s_mir with perms := permsP' })
            (s_osea := ({ s_mid with perms := p2, reg := oseair.RegMap.insert s_mid.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared ptrPlace) csPrefix).nextReg) (obseq.TyVal.PTy, oseair.readWordSeq s_mid.mem (pRes.allocBase + (pRes.addr - pRes.allocBase)) (obseq.typeSize obseq.TyVal.PTy)), pc := s_mid.pc + 1 } : oseair.State MSB))
            (resolved := { addr := b2 + o2, tag := t, allocBase := b2, allocSize := s2 })
            "CStore Invalid Ptr" [mirlite.MemValue.word v] [Val.Dat v] rfl
            ⟨rfl, trivial⟩ h_id_a h_entry1 h_useMut_tgt
            (by rw [show (({ s_mid with perms := p2, reg := oseair.RegMap.insert s_mid.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared ptrPlace) csPrefix).nextReg) (obseq.TyVal.PTy, oseair.readWordSeq s_mid.mem (pRes.allocBase + (pRes.addr - pRes.allocBase)) (obseq.typeSize obseq.TyVal.PTy)), pc := s_mid.pc + 1 } : oseair.State MSB)).mem = s_mid.mem from rfl, h_pmem]; exact h_sms)
            (Nat.le_add_right b2 o2)
            (fun k hk => by
              simp [Nat.lt_one_iff] at hk
              subst hk
              obtain ⟨a', h_a'⟩ := h_range o2 h_osz
              have h_ida := h_id_a _ _ h_a'
              rw [← h_ida] at h_a'
              exact h_a')
            h_write
        have h_run2 := runN_CStore_step compProg ({ s_mid with perms := p2, reg := oseair.RegMap.insert s_mid.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared ptrPlace) csPrefix).nextReg) (obseq.TyVal.PTy, oseair.readWordSeq s_mid.mem (pRes.allocBase + (pRes.addr - pRes.allocBase)) (obseq.typeSize obseq.TyVal.PTy)), pc := s_mid.pc + 1 } : oseair.State MSB) _
          obseq.TyVal.NatTy [Val.Dat v]
          (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared ptrPlace) csPrefix).nextReg) h_code2 rfl h_wtp
        have h_run :=
          (oseair_runN_add (n1 + 1) 1 s_osea compProg _
            ((oseair_runN_add n1 1 s_osea compProg s_mid h_prun).trans h_run1)).trans h_run2
        refine ⟨_, n1 + 1 + 1, h_run, ?_⟩
        refine ⟨CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix,
            ⟨prefixCompileState_succ h_csAt h_stmt h_stmtOut, ?_⟩, ?_, h_sms', h_psim3,
            h_id_a, h_wf_t, ?_, ?_, ?_, ?_⟩
        · -- label agreement
          show s_mid.pc + 1 + 1 = _
          rw [h_ppc, h_stmtRun]
          simp [emit]
        · -- LocalBindingSim across the fresh load register and the emits
          refine LocalBindingSim.placeRegMap_congr ?_
            (LocalBindingSim.insert_fresh_reg h_plbs h_prb h_pregmono rfl)
          rw [h_stmtRun]
          exact h_pprm
        · -- TagRenameBounded: the spine only READS and the store only WRITES,
          -- so no counter moved anywhere along the fragment
          show TagRenameBounded ρt perms'.NextTag p3.NextTag
          rw [sb_write_NextTag h_useMut_src, sb_write_NextTag h_useMut_tgt,
            sb_read_NextTag h_qread, sb_read_NextTag h_read_tgt, h_pnt1, h_pnt2]
          exact h_tbd
        · -- AllocLockstep: the fragment loads and stores, never allocates
          simp only [AllocLockstep, mirlite_writeWordSeq_addrStart,
            oseair_writeWordSeq_addrStart, h_pmem]
          exact h_alloc
        · -- UnboundLocalsUnmapped: `placeRegMap` is untouched by the
          -- spine's loads and by the store
          intro τ'' loc' h_none
          rw [h_stmtRun]
          simp only [getPlaceInfo, emit]
          rw [h_pprm]
          exact h_unmap loc' h_none
        · -- PlaceRegMapBound
          intro idx reg τ'' h_look
          rw [h_stmtRun] at h_look ⊢
          have h_cs : getPlaceInfo csPrefix idx = some (reg, τ'') := by
            show csPrefix.placeRegMap.lookup idx = _
            rw [← h_pprm]
            exact h_look
          exact RegisterBelow.mono
            (Nat.le_trans h_pregmono (Nat.le_succ _)) (h_prb _ _ _ h_cs)
      · simp at h_w

/-- RESIDUAL (sorried): DEEP pointer chains — a second segment below the
    first (proj under another deref, proj-of-proj pointer places pending
    the flattening-transfer, zero-offset pointer fields, or a fresh root).
    Everything with ONE proj segment at the top of an otherwise
    local-rooted chain is CLOSED (`const_write_deref_proj_simulation`,
    `const_write_proj_deref_simulation`); the general chain needs the
    pending-cleanup generalization of `loadSpine_lowering_sim` sketched in
    the keystone refactor assessment. -/
theorem const_write_deref_deep_residual
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_pre s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {ptrPlace : Place Γ (obseq.LayoutTy.PtrL obseq.LayoutTy.NatL)}
    {resolved : mirlite.PlaceRes} {permsD : MSB.State}
    (compProg : oseair.Prog)
    (v : Word)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    (h_stmt : prog.get? s_mir.pc = some (.assign (.deref ptrPlace) (.constInit v)))
    (h_prep : mirlite.preparePlaceAssign MSB s_mir (.deref ptrPlace) = .ok s_pre)
    (h_res  : mirlite.resolvePlaceAcc MSB s_pre (.deref ptrPlace) = .ok (resolved, permsD))
    (h_write : mirlite.writeResolvedPlace (τ := obseq.LayoutTy.NatL)
                 MSB { s_pre with perms := permsD } resolved
                 [mirlite.MemValue.word v] rfl = .ok s_mir') :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' := by
  sorry

/-- RESIDUAL REGIME D-proj (sorried): constant write through a deref whose
    pointer place is NOT a load spine — some level is a projection, whose
    lowering emits a `Borrow` with cleanup. Blocked on the `sb_ref`
    transport member, the same blocker as regime C. -/
theorem const_write_deref_nonspine_simulation
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_pre s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {ptrPlace : Place Γ (obseq.LayoutTy.PtrL obseq.LayoutTy.NatL)}
    {resolved : mirlite.PlaceRes} {permsD : MSB.State}
    (compProg : oseair.Prog)
    (v : Word)
    (h_nspine : ¬ LoadSpine ptrPlace)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    (h_stmt : prog.get? s_mir.pc = some (.assign (.deref ptrPlace) (.constInit v)))
    (h_prep : mirlite.preparePlaceAssign MSB s_mir (.deref ptrPlace) = .ok s_pre)
    (h_res  : mirlite.resolvePlaceAcc MSB s_pre (.deref ptrPlace) = .ok (resolved, permsD))
    (h_write : mirlite.writeResolvedPlace (τ := obseq.LayoutTy.NatL)
                 MSB { s_pre with perms := permsD } resolved
                 [mirlite.MemValue.word v] rfl = .ok s_mir') :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' := by
  cases ptrPlace with
  | «local» ploc => exact absurd (LoadSpine.base ploc) h_nspine
  | deref pp =>
      exact const_write_deref_deep_residual compProg v h_comp h_inv h_stmt
        h_prep h_res h_write
  | proj pbase f =>
      cases pbase with
      | «local» bloc =>
          cases h_env : mirlite.Env.lookup s_mir.env bloc with
          | none =>
              exact const_write_deref_deep_residual compProg v h_comp h_inv h_stmt
                h_prep h_res h_write
          | some binding =>
              by_cases h_o : pathOffset f = 0
              · exact const_write_deref_deep_residual compProg v h_comp h_inv h_stmt
                  h_prep h_res h_write
              · -- CLOSED: `*(s.f) := v` — the pointer field of a bound tuple local
                obtain ⟨s_osea', n, h_run, h_inv'⟩ :=
                  const_write_deref_proj_simulation compProg v h_o h_comp h_inv h_stmt
                    h_env h_prep h_res h_write
                exact ⟨ρa, ρt, s_osea', n, AddrRenameIncr.refl ρa, TagRenameIncr.refl ρt,
                  h_run, h_inv'⟩
      | proj b q =>
          exact const_write_deref_deep_residual compProg v h_comp h_inv h_stmt
            h_prep h_res h_write
      | deref ppp =>
          exact const_write_deref_deep_residual compProg v h_comp h_inv h_stmt
            h_prep h_res h_write

/-- RESIDUAL (sorried), NARROWED 2026-08-29: after the flattening
    recursion (nested projection towers reassociate on BOTH machines and
    recurse into the closed leaves, `stmt0`-threaded) and the zero-offset
    deref leaf, what remains routed here:
    - UNBOUND roots (regime-B composition: `allocateRoot` + the closed
      proj endgames on the fresh block);
    - NON-SPINE pointer chains (projections inside the pointer place —
      the deep-chain class shared with `const_write_deref_deep_residual`,
      wanting the pending-cleanup spine generalization). -/
theorem const_write_proj_nonlocal_residual
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_pre s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {σ : LayoutTy} {base : Place Γ σ} {path : PathTo σ obseq.LayoutTy.NatL}
    {resolved : mirlite.PlaceRes} {permsD : MSB.State}
    (compProg : oseair.Prog)
    (v : Word)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    {stmt0 : Stmt Γ}
    (h_stmt : prog.get? s_mir.pc = some stmt0)
    (h_run0 : ∀ cs, CheckedCompilerM.run (compileStmtChecked stmt0) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.proj base path) (.constInit v))) cs)
    (h_val0 : ∀ cs so, CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.proj base path) (.constInit v))) cs
        = Except.ok so →
      ∃ so', CheckedCompilerM.value (compileStmtChecked stmt0) cs
        = Except.ok so')
    (h_prep : mirlite.preparePlaceAssign MSB s_mir (.proj base path) = .ok s_pre)
    (h_res  : mirlite.resolvePlaceAcc MSB s_pre (.proj base path) = .ok (resolved, permsD))
    (h_write : mirlite.writeResolvedPlace (τ := obseq.LayoutTy.NatL)
                 MSB { s_pre with perms := permsD } resolved
                 [mirlite.MemValue.word v] rfl = .ok s_mir') :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' := by
  sorry

/-- REGIME C (dispatcher): constant write to a projected destination,
    split by the projection's OFFSET, which is what decides the shape of
    the lowering. Off a bound local both halves are CLOSED — zero offset
    by `const_write_proj_zero_simulation` (bare `CStore`), nonzero by
    `const_write_proj_offset_simulation` (`Borrow; CStore; Die`, BRIDGE 1).
    A non-local base is the named residual. -/
theorem const_write_proj_simulation
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_pre s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {σ : LayoutTy} {base : Place Γ σ} {path : PathTo σ obseq.LayoutTy.NatL}
    {resolved : mirlite.PlaceRes} {permsD : MSB.State}
    (compProg : oseair.Prog)
    (v : Word)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    {stmt0 : Stmt Γ}
    (h_stmt : prog.get? s_mir.pc = some stmt0)
    (h_run0 : ∀ cs, CheckedCompilerM.run (compileStmtChecked stmt0) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.proj base path) (.constInit v))) cs)
    (h_val0 : ∀ cs so, CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.proj base path) (.constInit v))) cs
        = Except.ok so →
      ∃ so', CheckedCompilerM.value (compileStmtChecked stmt0) cs
        = Except.ok so')
    (h_prep : mirlite.preparePlaceAssign MSB s_mir (.proj base path) = .ok s_pre)
    (h_res  : mirlite.resolvePlaceAcc MSB s_pre (.proj base path) = .ok (resolved, permsD))
    (h_write : mirlite.writeResolvedPlace (τ := obseq.LayoutTy.NatL)
                 MSB { s_pre with perms := permsD } resolved
                 [mirlite.MemValue.word v] rfl = .ok s_mir') :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' := by
  induction base with
  | «local» loc =>
      cases h_env : mirlite.Env.lookup s_mir.env loc with
      | none =>
          exact const_write_proj_nonlocal_residual compProg v h_comp h_inv h_stmt
            h_run0 h_val0 h_prep h_res h_write
      | some binding =>
          -- the destination root is bound, so prepare is a no-op and the
          -- projected place resolves to base + offset
          have h_pre : s_pre = s_mir := by
            simp only [mirlite.preparePlaceAssign, mirlite.resolvePlace?, h_env] at h_prep
            cases h_prep
            rfl
          subst h_pre
          simp only [mirlite.resolvePlaceAcc, h_env, Except.ok.injEq,
            Prod.mk.injEq] at h_res
          obtain ⟨h_r1, h_r2⟩ := h_res
          subst h_r1
          subst h_r2
          by_cases h_off : pathOffset path = 0
          · obtain ⟨s_osea', n, h_run, h_inv'⟩ :=
              const_write_proj_zero_simulation compProg v h_off h_comp h_inv h_stmt
                h_run0 h_val0
                h_env h_write
            exact ⟨ρa, ρt, s_osea', n, AddrRenameIncr.refl ρa, TagRenameIncr.refl ρt,
              h_run, h_inv'⟩
          · obtain ⟨s_osea', n, h_run, h_inv'⟩ :=
              const_write_proj_offset_simulation compProg v h_off h_comp h_inv h_stmt
                h_run0 h_val0
                h_env h_write
            exact ⟨ρa, ρt, s_osea', n, AddrRenameIncr.refl ρa, TagRenameIncr.refl ρt,
              h_run, h_inv'⟩
  | proj b q ih =>
      -- FLATTEN one level: the lowering reassociates, the source cannot
      -- tell the two spellings apart, and the run/value transfer keeps
      -- the PROGRAM's statement (stmt0) fixed through the recursion
      refine ih
        (fun cs => (h_run0 cs).trans
          (compileStmt_assign_proj_assoc_run b q path (.constInit v) cs))
        (fun cs so h => by
          obtain ⟨so', h'⟩ :=
            compileStmt_assign_proj_assoc_value b q path (.constInit v) cs h
          exact h_val0 cs so' h')
        ?_ ?_
      · rw [← preparePlaceAssign_proj_assoc b q path]
        exact h_prep
      · rw [← resolvePlaceAcc_proj_assoc b q path]
        exact h_res
  | deref pp =>
      by_cases h_sp : LoadSpine pp
      · by_cases h_o : pathOffset path = 0
        · -- CLOSED: `(*p).f := v` at ZERO offset over any load spine
          obtain ⟨s_osea', n, h_run, h_inv'⟩ :=
            const_write_proj_deref_zero_simulation compProg v h_sp h_o h_comp h_inv
              h_stmt h_run0 h_val0 h_prep h_res h_write
          exact ⟨ρa, ρt, s_osea', n, AddrRenameIncr.refl ρa, TagRenameIncr.refl ρt,
            h_run, h_inv'⟩
        · -- CLOSED: `(*p).f := v` over any load spine
          -- (the resolution shape matches after unfolding one proj level)
          obtain ⟨s_osea', n, h_run, h_inv'⟩ :=
            const_write_proj_deref_simulation compProg v h_sp h_o h_comp h_inv h_stmt
              h_run0 h_val0
              h_prep h_res h_write
          exact ⟨ρa, ρt, s_osea', n, AddrRenameIncr.refl ρa, TagRenameIncr.refl ρt,
            h_run, h_inv'⟩
      · exact const_write_proj_nonlocal_residual compProg v h_comp h_inv h_stmt
          h_run0 h_val0 h_prep h_res h_write

/-- Regime D, decomposed by the pointer place: load spines (all-deref
    chains over a local — every depth) are CLOSED via
    `const_write_deref_spine_simulation`; a projection anywhere in the
    chain is the named residual sorry above. -/
theorem const_write_deref_simulation
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_pre s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {ptrPlace : Place Γ (obseq.LayoutTy.PtrL obseq.LayoutTy.NatL)}
    {resolved : mirlite.PlaceRes} {permsD : MSB.State}
    (compProg : oseair.Prog)
    (v : Word)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    (h_stmt : prog.get? s_mir.pc = some (.assign (.deref ptrPlace) (.constInit v)))
    (h_prep : mirlite.preparePlaceAssign MSB s_mir (.deref ptrPlace) = .ok s_pre)
    (h_res  : mirlite.resolvePlaceAcc MSB s_pre (.deref ptrPlace) = .ok (resolved, permsD))
    (h_write : mirlite.writeResolvedPlace (τ := obseq.LayoutTy.NatL)
                 MSB { s_pre with perms := permsD } resolved
                 [mirlite.MemValue.word v] rfl = .ok s_mir') :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' := by
  by_cases h_spine : LoadSpine ptrPlace
  · obtain ⟨s_osea', n, h_run, h_inv'⟩ :=
      const_write_deref_spine_simulation compProg v h_spine h_comp h_inv h_stmt
        (fun _ => rfl) (fun _ so h => ⟨so, h⟩)
        h_prep h_res h_write
    exact ⟨ρa, ρt, s_osea', n, AddrRenameIncr.refl ρa, TagRenameIncr.refl ρt,
      h_run, h_inv'⟩
  · exact const_write_deref_nonspine_simulation compProg v h_spine h_comp h_inv
      h_stmt h_prep h_res h_write

/-- Resolved constant-write simulation, decomposed by destination regime:
    regime A (bound local) is CLOSED via
    `const_write_local_existing_simulation`; the residual regimes are the
    named sorries above. -/
theorem const_write_resolved_simulation
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_pre s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {dst : Place Γ obseq.LayoutTy.NatL}
    {resolved : mirlite.PlaceRes} {permsD : MSB.State}
    (compProg : oseair.Prog)
    (v : Word)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    (h_stmt : prog.get? s_mir.pc = some (.assign dst (.constInit v)))
    (h_prep : mirlite.preparePlaceAssign MSB s_mir dst = .ok s_pre)
    (h_res  : mirlite.resolvePlaceAcc MSB s_pre dst = .ok (resolved, permsD))
    (csPrefix : CompilerState)
    (h_csAt : csAt cs0 prog s_mir.pc csPrefix)
    (stmtOut : ResultWithEvidence Unit (fun _ => StmtEvidence (.assign dst (.constInit v))))
    (h_stmtOut :
      CheckedCompilerM.value (compileStmtChecked (.assign dst (.constInit v)))
        csPrefix = Except.ok stmtOut)
    (h_write : mirlite.writeResolvedPlace (τ := obseq.LayoutTy.NatL)
                 MSB { s_pre with perms := permsD } resolved
                 [mirlite.MemValue.word v] rfl = .ok s_mir') :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' := by
  cases dst with
  | «local» loc =>
      cases h_env : mirlite.Env.lookup s_mir.env loc with
      | some binding =>
          have h_pre : s_pre = s_mir := by
            simp only [mirlite.preparePlaceAssign, mirlite.resolvePlace?, h_env] at h_prep
            cases h_prep
            rfl
          subst h_pre
          simp only [mirlite.resolvePlaceAcc, h_env, Except.ok.injEq, Prod.mk.injEq] at h_res
          obtain ⟨h_r1, h_r2⟩ := h_res
          subst h_r1
          subst h_r2
          obtain ⟨s_osea', n, h_run, h_inv'⟩ :=
            const_write_local_existing_simulation compProg v h_comp h_inv h_stmt h_env h_write
          exact ⟨ρa, ρt, s_osea', n, AddrRenameIncr.refl ρa, TagRenameIncr.refl ρt,
            h_run, h_inv'⟩
      | none =>
          exact const_write_fresh_local_simulation compProg v h_comp h_inv h_stmt
            h_env h_prep h_res h_write
  | proj base path =>
      exact const_write_proj_simulation compProg v h_comp h_inv h_stmt
        (fun _ => rfl) (fun _ so h => ⟨so, h⟩)
        h_prep h_res h_write
  | deref ptrPlace =>
      exact const_write_deref_simulation compProg v h_comp h_inv h_stmt
        h_prep h_res h_write

theorem prepare_local_assign_resolves
    {Γ : Ctx} {τ : LayoutTy}
    {s s' : mirlite.State MSB Γ}
    {loc : Local Γ τ}
    (h_prep : mirlite.preparePlaceAssign MSB s (.local loc) = .ok s') :
    ∃ resolved, mirlite.resolvePlace? s' (.local loc) = some resolved := by
  simp only [mirlite.preparePlaceAssign] at h_prep
  split at h_prep
  · rename_i resolved h_res
    cases h_prep
    exact ⟨resolved, h_res⟩
  · simp only [mirlite.allocateRoot, mirlite.allocateBase] at h_prep
    split at h_prep
    · simp at h_prep
    · rename_i permsOwned tag h_own
      cases h_prep
      simp [mirlite.resolvePlace?, mirlite.Env.lookup, mirlite.Env.set]

theorem CompilerInv_step_constWrite
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {dst : Place Γ obseq.LayoutTy.NatL}
    (compProg : oseair.Prog)
    (v : Word)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    (h_stmt : prog.get? s_mir.pc = some (.assign dst (.constInit v)))
    (h_step : mirlite.stepStmt MSB s_mir (.assign dst (.constInit v)) = .ok s_mir') :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' := by
  have h_inv_full := h_inv
  simp only [mirlite.stepStmt, mirlite.doAssign] at h_step
  cases h_prep : mirlite.preparePlaceAssign MSB s_mir dst with
  | err msg =>
      simp [h_prep] at h_step
  | ok s_pre =>
      simp only [h_prep] at h_step
      cases h_res : mirlite.resolvePlaceAcc MSB s_pre dst with
      | error e => simp [h_res] at h_step
      | ok pr =>
          obtain ⟨resolved, permsD⟩ := pr
          simp only [h_res, mirlite.evalRExpr] at h_step
          obtain ⟨csPrefix', stmtOut, h_csAt', h_stmtOut⟩ :=
            const_write_stmt_evidence (s_pre := s_pre) v h_inv_full h_prep
          exact const_write_resolved_simulation compProg v h_comp h_inv_full h_stmt h_prep h_res
            csPrefix' h_csAt' stmtOut h_stmtOut h_step

end obseq3.proof
