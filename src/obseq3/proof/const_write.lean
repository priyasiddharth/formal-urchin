import obseq3.proof.common
import obseq3.proof.permsim_transport

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
  obtain ⟨csPrefix, h_label, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_prb⟩ := h_inv
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

/-- Compute `ensureLocalRegE` on an already-mapped local: no compiler-state
    change, and the returned pointer result is the mapped register. -/
theorem ensureLocalRegE_existing
    {Γ : Ctx} {τ : LayoutTy} {loc : Local Γ τ} {cs : CompilerState}
    {reg : Register}
    (h : getPlaceInfo cs loc.idx.1 = some (reg, τ)) :
    CompilerM.run (ensureLocalRegE loc) cs = cs ∧
    (CompilerM.value (ensureLocalRegE loc) cs).result = { reg := reg, cleanup := [] } := by
  unfold CompilerM.run CompilerM.value ensureLocalRegE
  split
  · rename_i reg' layout' h'
    rw [h'] at h
    injection h with h2
    have h_eq : reg' = reg := congrArg Prod.fst h2
    subst h_eq
    exact ⟨rfl, rfl⟩
  · rename_i h'
    rw [h'] at h
    cases h

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

/-- The compiled fragment of a constant write through a bound pointer
    LOCAL is exactly `Load` (of the pointer) then `CStore` (through it):
    the loaded register is the prefix state's `nextReg`, and the compiler
    state advances by one register and two labels. -/
theorem compileStmt_deref_local_run
    {Γ : Ctx} {ploc : Local Γ (obseq.LayoutTy.PtrL obseq.LayoutTy.NatL)}
    {cs : CompilerState} {preg : Register}
    (v : Word)
    (h_pi : getPlaceInfo cs ploc.idx.1
      = some (preg, obseq.LayoutTy.PtrL obseq.LayoutTy.NatL)) :
    CheckedCompilerM.run
        (compileStmtChecked (Stmt.assign (.deref (.local ploc)) (.constInit v))) cs
      = emit (emit { cs with nextReg := cs.nextReg + 1 }
          [Instr.Assgn (Register.R cs.nextReg) (Rhs.Load obseq.TyVal.PTy preg)])
          [Instr.CStore obseq.TyVal.NatTy [Val.Dat v] (Register.R cs.nextReg)] := by
  have h_mapped : PlaceInputsMapped cs (Place.deref (Place.local ploc)) :=
    ⟨preg, _, h_pi⟩
  have h_root := ensurePlaceRoot_run_eq_of_mapped h_mapped
  obtain ⟨h_prun, placeOut, h_pval, h_pres⟩ :=
    placeToRegChecked_local_existing (kind := RefKind.Shared) h_pi
  have h_deref_eq : placeToRegChecked (Γ := Γ) RefKind.Mut (.deref (.local ploc))
      = (do
          let ptrOut ← placeToRegChecked RefKind.Shared (.local ploc)
          let ptrRes := ptrOut.result
          let loadedReg ← CheckedCompilerM.lift freshRegM
          let _ ← CheckedCompilerM.lift
            (emitM [Instr.Assgn loadedReg (Rhs.Load obseq.TyVal.PTy ptrRes.reg)])
          let _ ← CheckedCompilerM.lift (emitM (cleanupInstrs ptrRes.cleanup))
          pure {
            result := { reg := loadedReg, cleanup := [] },
            evidence := PlaceToRegEvidence.deref (.local ploc) ptrRes loadedReg ptrOut.evidence
          }) := rfl
  simp only [compileStmtChecked, h_deref_eq, compileRExprToChecked,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
    h_root, h_pval, h_prun, h_pres]
  simp [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM,
    cleanupInstrs, emit_nil]

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
  obtain ⟨csPrefix, ⟨h_csAt, h_pc⟩, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_prb⟩ := h_inv
  obtain ⟨reg, base, tag, h_pi, h_entry, h_ra, h_rt, h_nw⟩ := h_lbs loc binding h_env
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
        ⟨prefixCompileState_succ h_csAt h_stmt h_stmtOut, ?_⟩, ?_, ?_, h_psim', h_id_a, h_wf_t, ?_⟩
      · -- label agreement at pc+1
        rw [h_stmtRun]
        show s_osea.pc + 1 = (emit csPrefix _).nextLabel
        rw [h_pc]
        simp [emit]
      · -- LocalBindingSim carries over
        intro τ' loc' binding' h_env'
        obtain ⟨reg', base', tag', h_pi', h_entry'', h_ra', h_rt', h_nw'⟩ :=
          h_lbs loc' binding' h_env'
        refine ⟨reg', base', tag', ?_, h_entry'', h_ra', h_rt', h_nw'⟩
        rw [h_stmtRun]
        exact h_pi'
      · -- SourceMemSim
        exact h_sms'
      · -- PlaceRegMapBound: the fragment only emits code — `placeRegMap`
        -- and `nextReg` are untouched
        rw [h_stmtRun]
        exact h_prb
    · simp at h_w

/-- RESIDUAL REGIME B (sorried): constant write to a FRESH local — the
    destination local is unbound, so mirlite's prepare allocated it and
    the compiled fragment starts with an `Alloc`. Needs the lockstep-
    allocation invariant (`s_osea.mem.addrStart = s_mir.mem.addrStart`,
    not yet carried) so ρa extends at the equal fresh address, plus the
    `sb_own` transport member (extends ρt at the fresh pair). -/
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
  sorry

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

/-- REGIME D1, CLOSED: constant write through a dereferenced BOUND pointer
    local (`*p := v` with `p` a local). The fragment is `Load; CStore`:
    the `Load` is matched by the SB read mirlite's `resolvePlaceAcc` now
    performs (the 2026-08-21 deref-read change), transported by the
    `sb_read` BRIDGE-3 member; the loaded value is the ρ-renamed stored
    pointer (`MemValSim` inversion); the `CStore` through it is BRIDGE 2 +
    the `sb_write` BRIDGE-3 member, with the acting tag's non-wildcardness
    and the write range's ρa-domain membership supplied by the strengthened
    `MemValSim` pointer case. The fresh load register cannot clobber a
    bound local's register by `PlaceRegMapBound`. -/
theorem const_write_deref_local_simulation
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_pre s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {ploc : Local Γ (obseq.LayoutTy.PtrL obseq.LayoutTy.NatL)}
    {pbind : mirlite.Binding}
    {resolved : mirlite.PlaceRes} {permsD : MSB.State}
    (compProg : oseair.Prog)
    (v : Word)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    (h_stmt : prog.get? s_mir.pc = some (.assign (.deref (.local ploc)) (.constInit v)))
    (h_env : mirlite.Env.lookup s_mir.env ploc = some pbind)
    (h_prep : mirlite.preparePlaceAssign MSB s_mir (.deref (.local ploc)) = .ok s_pre)
    (h_res  : mirlite.resolvePlaceAcc MSB s_pre (.deref (.local ploc)) = .ok (resolved, permsD))
    (h_write : mirlite.writeResolvedPlace (τ := obseq.LayoutTy.NatL)
                 MSB { s_pre with perms := permsD } resolved
                 [mirlite.MemValue.word v] rfl = .ok s_mir') :
    ∃ (s_osea' : oseair.State MSB) (n : Nat),
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa ρt s_mir' s_osea' := by
  -- prepare is a no-op: a deref destination must already resolve
  have h_pre_eq : s_pre = s_mir := by
    simp only [mirlite.preparePlaceAssign] at h_prep
    split at h_prep
    · cases h_prep; rfl
    · simp [mirlite.allocateRoot] at h_prep
  subst h_pre_eq
  obtain ⟨csPrefix, ⟨h_csAt, h_pc⟩, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_prb⟩ := h_inv
  obtain ⟨preg, pbase, ptag, h_pi, h_pentry, h_pra, h_prt, h_pnw⟩ := h_lbs ploc pbind h_env
  have h_pbase : pbase = pbind.addr := (h_id_a _ _ h_pra).symm
  subst h_pbase
  -- invert the access-resolution: SB read of the pointer cell + its content
  obtain ⟨b, o, sz, t, h_read_src, h_find_src, h_resolved_eq⟩ :=
    resolvePlaceAcc_deref_local_inversion h_env h_res
  subst h_resolved_eq
  -- the target pointer cell holds the ρ-renamed stored pointer
  obtain ⟨addr', value', h_ra', h_find_tgt, h_mvs⟩ := h_sms _ _ h_find_src
  have h_addr' : addr' = pbind.addr := (h_id_a _ _ h_ra').symm
  subst h_addr'
  cases value' with
  | Undef => exact h_mvs.elim
  | Dat _ => exact h_mvs.elim
  | Ptr b' o' s' t' =>
  obtain ⟨h_b, h_o, h_s, h_t, h_tnw, h_range⟩ := h_mvs
  have h_b' : b' = b := (h_id_a _ _ h_b).symm
  subst h_b'
  subst h_o
  subst h_s
  -- BRIDGE 3 (read member): the target Load's permission read succeeds
  obtain ⟨p2, h_read_tgt, h_psim2⟩ :=
    sb_read_respects_PermSim h_psim h_wf_t h_prt h_pnw h_read_src
  -- compiled fragment and its location
  have h_stmtRun := compileStmt_deref_local_run (cs := csPrefix) v h_pi
  have h_mapped : PlaceInputsMapped csPrefix (Place.deref (Place.local ploc)) :=
    ⟨preg, _, h_pi⟩
  have h_root := ensurePlaceRoot_run_eq_of_mapped h_mapped
  obtain ⟨dstOut, h_dstOut⟩ := placeToRegChecked_ok_of_placeInputsMapped
    (cs := csPrefix) (kind := RefKind.Mut) (p := .deref (.local ploc)) h_mapped
  obtain ⟨stmtOut, h_stmtOut⟩ : ∃ so, CheckedCompilerM.value
      (compileStmtChecked (Stmt.assign (.deref (.local ploc)) (.constInit v)))
      csPrefix = Except.ok so :=
    ⟨{ result := (),
       evidence := StmtEvidence.assignPlace (.deref (.local ploc)) (.constInit v)
         dstOut.result dstOut.evidence (RExprToEvidence.constInit v) },
     by simp [compileStmtChecked, compileRExprToChecked, h_dstOut, h_root]⟩
  have h_code1 : compProg s_osea.pc
      = some (Instr.Assgn (Register.R csPrefix.nextReg)
          (Rhs.Load obseq.TyVal.PTy preg)) := by
    rw [h_pc]
    refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
    · rw [h_stmtRun]
      show csPrefix.nextLabel < csPrefix.nextLabel + 1 + 1
      omega
    · rw [h_stmtRun]
      rw [emit_code_lt_nextLabel _ _ (by show csPrefix.nextLabel < csPrefix.nextLabel + 1; omega)]
      have h := emit_code_at_new { csPrefix with nextReg := csPrefix.nextReg + 1 }
        [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Load obseq.TyVal.PTy preg)]
        (k := 0) (by simp)
      simpa using h
  have h_code2 : compProg (s_osea.pc + 1)
      = some (Instr.CStore obseq.TyVal.NatTy [Val.Dat v]
          (Register.R csPrefix.nextReg)) := by
    rw [h_pc]
    refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
    · rw [h_stmtRun]
      show csPrefix.nextLabel + 1 < csPrefix.nextLabel + 1 + 1
      omega
    · rw [h_stmtRun]
      have h := emit_code_at_new
        (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
          [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Load obseq.TyVal.PTy preg)])
        [Instr.CStore obseq.TyVal.NatTy [Val.Dat v] (Register.R csPrefix.nextReg)]
        (k := 0) (by simp)
      simpa [emit] using h
  -- step 1: the Load
  have h_run1 := runN_Assgn_Load_ptr_step compProg s_osea
    (Register.R csPrefix.nextReg) preg obseq.TyVal.PTy
    h_code1 h_pentry (Nat.zero_lt_one) h_read_tgt
  have h_rws : oseair.readWordSeq s_osea.mem (pbind.addr + 0)
      (obseq.typeSize obseq.TyVal.PTy) = [Val.Ptr b' o' s' t'] := by
    show oseair.readWordSeq s_osea.mem pbind.addr 1 = _
    simp [oseair.readWordSeq, h_find_tgt]
  -- destructure the source write for the transport hypotheses
  have h_w := h_write
  simp only [mirlite.writeResolvedPlace] at h_w
  split at h_w
  · simp at h_w
  · rename_i h_nb
    split at h_w
    · rename_i perms' h_useMut_src
      cases h_w
      have h_osz : o' < s' := by
        have h1 : b' + o' + 1 ≤ b' + s' := Nat.le_of_not_lt (by simpa using h_nb)
        exact Nat.lt_of_add_lt_add_left (Nat.lt_of_succ_le h1)
      -- BRIDGE 3 (write member): the CStore's useMut succeeds
      obtain ⟨p3, h_useMut_tgt, h_psim3⟩ :=
        sb_write_respects_PermSim h_psim2 h_wf_t h_t h_tnw h_useMut_src
      -- BRIDGE 2: execute the write through the loaded pointer
      have h_entry1 : PtrRegisterEntry
          (oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
            (obseq.TyVal.PTy, oseair.readWordSeq s_osea.mem (pbind.addr + 0)
              (obseq.typeSize obseq.TyVal.PTy)))
          (Register.R csPrefix.nextReg) b' ((b' + o') - b') s' t' := by
        show oseair.RegMap.lookup (oseair.RegMap.insert _ _ _) _ = _
        rw [Nat.add_sub_cancel_left, RegMap.lookup_insert_self, h_rws]
      obtain ⟨h_wtp, h_sms'⟩ :=
        writeThroughPtr_sim (ρa := ρa) (ρt := ρt) (τ := obseq.LayoutTy.NatL)
          (s_pre := { s_pre with perms := permsD })
          (s_osea := ({ s_osea with perms := p2, reg := oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg) (obseq.TyVal.PTy, oseair.readWordSeq s_osea.mem (pbind.addr + 0) (obseq.typeSize obseq.TyVal.PTy)), pc := s_osea.pc + 1 } : oseair.State MSB))
          (resolved := { addr := b' + o', tag := t, allocBase := b', allocSize := s' })
          "CStore Invalid Ptr" [mirlite.MemValue.word v] [Val.Dat v] rfl
          ⟨rfl, trivial⟩ h_id_a h_entry1 h_useMut_tgt h_sms (Nat.le_add_right b' o')
          (fun k hk => by
            simp [Nat.lt_one_iff] at hk
            subst hk
            obtain ⟨a', h_a'⟩ := h_range o' h_osz
            have h_ida := h_id_a _ _ h_a'
            rw [← h_ida] at h_a'
            exact h_a')
          h_write
      have h_run2 := runN_CStore_step compProg ({ s_osea with perms := p2, reg := oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg) (obseq.TyVal.PTy, oseair.readWordSeq s_osea.mem (pbind.addr + 0) (obseq.typeSize obseq.TyVal.PTy)), pc := s_osea.pc + 1 } : oseair.State MSB) _
        obseq.TyVal.NatTy [Val.Dat v]
        (Register.R csPrefix.nextReg) h_code2 rfl h_wtp
      have h_run :=
        (oseair_runN_add 1 1 s_osea compProg ({ s_osea with perms := p2, reg := oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg) (obseq.TyVal.PTy, oseair.readWordSeq s_osea.mem (pbind.addr + 0) (obseq.typeSize obseq.TyVal.PTy)), pc := s_osea.pc + 1 } : oseair.State MSB) h_run1).trans h_run2
      -- rebuild the invariant
      refine ⟨_, 1 + 1, h_run, ?_⟩
      refine ⟨CheckedCompilerM.run
        (compileStmtChecked (Stmt.assign (.deref (.local ploc)) (.constInit v))) csPrefix,
        ⟨prefixCompileState_succ h_csAt h_stmt h_stmtOut, ?_⟩, ?_, h_sms', h_psim3,
        h_id_a, h_wf_t, ?_⟩
      · -- label agreement at pc+2
        rw [h_stmtRun]
        show s_osea.pc + 1 + 1 = _
        rw [h_pc]
        simp [emit]
      · -- LocalBindingSim: the only register written is the fresh load
        -- register, which `PlaceRegMapBound` keeps clear of bound locals
        rw [h_stmtRun]
        exact LocalBindingSim.insert_fresh_reg h_lbs h_prb (Nat.le_refl _) rfl
      · -- PlaceRegMapBound: the fragment adds no mappings; nextReg grew
        rw [h_stmtRun]
        intro idx reg τ' h_look
        exact RegisterBelow.mono (Nat.le_succ _) (h_prb idx reg τ' h_look)
    · simp at h_w

/-- RESIDUAL REGIME D2 (sorried): constant write through a dereference
    whose pointer PLACE is a projection (`*(s.fld) := v`). The pointer
    lowering emits a `Borrow` with cleanup, so this needs the `sb_ref`
    transport member (extends ρt at the fresh internal tag) composed with
    BRIDGE 1 — the same blocker as regime C. -/
theorem const_write_deref_projPtr_simulation
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_pre s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {σ : LayoutTy} {pbase : Place Γ σ}
    {ppath : PathTo σ (obseq.LayoutTy.PtrL obseq.LayoutTy.NatL)}
    {resolved : mirlite.PlaceRes} {permsD : MSB.State}
    (compProg : oseair.Prog)
    (v : Word)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    (h_stmt : prog.get? s_mir.pc
      = some (.assign (.deref (.proj pbase ppath)) (.constInit v)))
    (h_prep : mirlite.preparePlaceAssign MSB s_mir (.deref (.proj pbase ppath)) = .ok s_pre)
    (h_res  : mirlite.resolvePlaceAcc MSB s_pre (.deref (.proj pbase ppath))
      = .ok (resolved, permsD))
    (h_write : mirlite.writeResolvedPlace (τ := obseq.LayoutTy.NatL)
                 MSB { s_pre with perms := permsD } resolved
                 [mirlite.MemValue.word v] rfl = .ok s_mir') :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' := by
  sorry

/-- RESIDUAL REGIME D3 (sorried): constant write through a NESTED
    dereference (`**q := v`). The pointer lowering is a `Load` spine; each
    level is `runN_Assgn_Load_ptr_step` + the `sb_read` transport +
    `MemValSim` inversion — the D1 machinery — but composing them needs a
    length-generalized spine induction over the pointer place. Mechanical,
    no new SB lemmas. -/
theorem const_write_deref_nested_simulation
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_pre s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {pptr : Place Γ (obseq.LayoutTy.PtrL (obseq.LayoutTy.PtrL obseq.LayoutTy.NatL))}
    {resolved : mirlite.PlaceRes} {permsD : MSB.State}
    (compProg : oseair.Prog)
    (v : Word)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    (h_stmt : prog.get? s_mir.pc
      = some (.assign (.deref (.deref pptr)) (.constInit v)))
    (h_prep : mirlite.preparePlaceAssign MSB s_mir (.deref (.deref pptr)) = .ok s_pre)
    (h_res  : mirlite.resolvePlaceAcc MSB s_pre (.deref (.deref pptr))
      = .ok (resolved, permsD))
    (h_write : mirlite.writeResolvedPlace (τ := obseq.LayoutTy.NatL)
                 MSB { s_pre with perms := permsD } resolved
                 [mirlite.MemValue.word v] rfl = .ok s_mir') :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' := by
  sorry

/-- Regime D, decomposed by the pointer place: D1 (bound pointer local) is
    CLOSED via `const_write_deref_local_simulation` (the fresh-local case
    is vacuous — `preparePlaceAssign` cannot allocate under a deref); the
    residual pointer-place shapes are the named sorries above. -/
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
  cases ptrPlace with
  | «local» ploc =>
      cases h_env : mirlite.Env.lookup s_mir.env ploc with
      | some pbind =>
          -- prepare is a no-op on a resolvable deref, so s_pre.env = s_mir.env
          have h_pre_eq : s_pre = s_mir := by
            simp only [mirlite.preparePlaceAssign] at h_prep
            split at h_prep
            · cases h_prep; rfl
            · simp [mirlite.allocateRoot] at h_prep
          obtain ⟨s_osea', n, h_run, h_inv'⟩ :=
            const_write_deref_local_simulation compProg v h_comp h_inv h_stmt
              h_env h_prep h_res h_write
          exact ⟨ρa, ρt, s_osea', n, AddrRenameIncr.refl ρa, TagRenameIncr.refl ρt,
            h_run, h_inv'⟩
      | none =>
          -- an unbound pointer local cannot resolve: prepare would have to
          -- allocate under a deref, which errors
          have h_pre_eq : s_pre = s_mir := by
            simp only [mirlite.preparePlaceAssign] at h_prep
            split at h_prep
            · cases h_prep; rfl
            · simp [mirlite.allocateRoot] at h_prep
          subst h_pre_eq
          simp [mirlite.resolvePlaceAcc, h_env] at h_res
  | proj pbase ppath =>
      exact const_write_deref_projPtr_simulation compProg v h_comp h_inv h_stmt
        h_prep h_res h_write
  | deref pptr =>
      exact const_write_deref_nested_simulation compProg v h_comp h_inv h_stmt
        h_prep h_res h_write

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
