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
      · simp [compileStmtChecked, compileRExprToChecked]
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
          · simp [compileStmtChecked, compileRExprToChecked, h_dstOut]
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
          · simp [compileStmtChecked, compileRExprToChecked, h_dstOut, h_root]
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
          · simp [compileStmtChecked, compileRExprToChecked, h_dstOut, h_root]

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
  simp [compileStmtChecked, compileRExprToChecked, h_run, h_val]
  rfl

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
        ⟨{ result := (), evidence := StmtEvidence.assignLocal loc (.constInit v) (CompilerM.value (ensureLocalRegE loc) csPrefix).result (CompilerM.value (ensureLocalRegE loc) csPrefix).evidence (RExprToEvidence.constInit v) }, by simp [compileStmtChecked, compileRExprToChecked]⟩
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
         by simp [compileStmtChecked, compileRExprToChecked]⟩
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

/-- RESIDUAL REGIME C (sorried): constant write to a projected
    destination. The fragment is `[root Alloc?] Borrow(Mut) CStore Die`;
    needs BRIDGE 1 (`sb_ref_use_die_cancels`) composed with BRIDGE 3, and
    the strengthened `CompilerStateWF` (placeRegMap register bound) so the
    fresh temp register cannot collide with stored local registers. -/
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
    (h_stmt : prog.get? s_mir.pc = some (.assign (.proj base path) (.constInit v)))
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
          }) := rfl
  simp only [compileStmtChecked, h_deref_eq, compileRExprToChecked,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
    h_root, h_pval]
  simp [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM,
    cleanupInstrs, h_pclean, emit_nil]

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
    (h_stmt : prog.get? s_mir.pc = some (.assign (.deref ptrPlace) (.constInit v)))
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
  obtain ⟨stmtOut, h_stmtOut⟩ : ∃ so, CheckedCompilerM.value
      (compileStmtChecked (Stmt.assign (.deref ptrPlace) (.constInit v)))
      csPrefix = Except.ok so :=
    ⟨{ result := (),
       evidence := StmtEvidence.assignPlace (.deref ptrPlace) (.constInit v)
         dstOut.result dstOut.evidence (RExprToEvidence.constInit v) },
     by simp [compileStmtChecked, compileRExprToChecked, h_dstOut, h_root]⟩
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
            }) := rfl
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
      · exact Nat.lt_of_lt_of_le h_lt h_incrP.nextLabel_le
      · rw [h_incrP.code_eq q' h_lt]
        exact h_code
    -- run the spine
    obtain ⟨pOut, n1, s_mid, ptag, h_pval, h_pclean, h_prun, h_ppc, h_pmem, h_ppsim,
      h_pnt1, h_pnt2, h_plbs, h_pentry, h_prt, h_pnw, h_ple, h_prange, h_pbelow,
      h_pprm, h_pregmono, h_plabmono⟩ :=
      loadSpine_lowering_sim h_id_a h_wf_t h_spine RefKind.Shared csPrefix s_osea
        pRes permsP h_qres h_lbs h_prb h_sms h_psim h_pc h_instP
    have h_stmtRun := compileStmt_deref_run v h_root h_pval h_pclean
    -- pointer-place bounds from the dereferenceable check
    have h_ge : pRes.allocBase ≤ pRes.addr :=
      Nat.le_of_not_lt (fun h => h_qb (Or.inl h))
    have h_cancel : pRes.allocBase + (pRes.addr - pRes.allocBase) = pRes.addr :=
      Nat.add_sub_cancel' h_ge
    have h_off : pRes.addr - pRes.allocBase < pRes.allocSize := by
      have h : pRes.addr < pRes.allocBase + pRes.allocSize :=
        Nat.lt_of_not_le (fun h => h_qb (Or.inr h))
      rw [← h_cancel] at h
      exact Nat.lt_of_add_lt_add_left h
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
        refine ⟨CheckedCompilerM.run
            (compileStmtChecked (Stmt.assign (.deref ptrPlace) (.constInit v))) csPrefix,
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
  sorry

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
