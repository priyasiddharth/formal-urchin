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

/-! ## §A' The CONSTANT-STORE fragment, generic in the rvalue

    `constInit` and `uninit` differ only in the value list they store:
    both evaluate WITHOUT touching the source state, both lower to a
    single `CStore` with no rhs pre-phase instructions, and both leave
    the destination's own lowering to run from the prefix state. The
    leaves below are therefore stated over an arbitrary rhs, an
    arbitrary destination layout, and a source/target value pair related
    cell-by-cell by `MemValSim`; each rvalue supplies the pair.

    `constInit` gives `[word v]` / `[Val.Dat v]` at `NatL` (width one);
    `uninit` gives `replicate (blockSize τ) undef` /
    `replicate (blockSize τ) Val.Undef` at ANY `τ`, whose `ListRel` is
    free because `MemValSim`'s first clause is `| .undef, _ => True`. -/

/-- REGIME A, generic: a constant store into an already-bound local. The
    fragment is one `CStore`; execution is BRIDGE 2, the permission
    transport is BRIDGE 3, and the renames do not grow. -/
theorem const_store_local_existing_simulation
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {τ : LayoutTy} {loc : Local Γ τ}
    {binding : mirlite.Binding}
    {vs : List mirlite.MemValue} {vs' : List Val}
    (compProg : oseair.Prog) (rhs : RExpr Γ τ)
    (h_len : vs.length = blockSize τ)
    (h_rel : ListRel (MemValSim ρa ρt) vs vs')
    (h_size : vs'.length = obseq.typeSize (layoutToTyVal τ))
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    (h_stmt : prog.get? s_mir.pc = some (.assign (.local loc) rhs))
    (h_run0 : ∀ (cs : CompilerState) (reg : Register),
      getPlaceInfo cs loc.idx.1 = some (reg, τ) →
      CheckedCompilerM.run (compileStmtChecked (Stmt.assign (.local loc) rhs)) cs
        = emit cs [Instr.CStore (layoutToTyVal τ) vs' reg])
    (h_val0 : ∀ cs, ∃ so,
      CheckedCompilerM.value (compileStmtChecked (Stmt.assign (.local loc) rhs)) cs
        = Except.ok so)
    (h_env : mirlite.Env.lookup s_mir.env loc = some binding)
    (h_write : mirlite.writeResolvedPlace (τ := τ) MSB s_mir
        { addr := binding.addr, tag := binding.tag, allocBase := binding.addr,
          allocSize := blockSize τ }
        vs h_len = .ok s_mir') :
    ∃ (s_osea' : oseair.State MSB) (n : Nat),
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa ρt s_mir' s_osea' := by
  obtain ⟨csPrefix, ⟨h_csAt, h_pc⟩, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_tbd,
    h_alloc, h_unmap, h_prb⟩ := h_inv
  obtain ⟨reg, base, tag, h_pi, h_entry, h_ra, h_rt, h_nw, h_dom⟩ := h_lbs loc binding h_env
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
      obtain ⟨p2, h_useMut_tgt, h_psim'⟩ :=
        sb_write_respects_PermSim h_psim h_wf_t h_rt h_nw h_useMut_src
      have h_stmtRun := h_run0 csPrefix reg h_pi
      obtain ⟨stmtOut, h_stmtOut⟩ := h_val0 csPrefix
      have h_code : compProg s_osea.pc
          = some (Instr.CStore (layoutToTyVal τ) vs' reg) := by
        rw [h_pc]
        refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
        · rw [h_stmtRun]
          simp [emit]
        · rw [h_stmtRun]
          have h_at := emit_code_at_new csPrefix
            [Instr.CStore (layoutToTyVal τ) vs' reg] (k := 0) (by simp)
          simpa using h_at
      have h_entry' : PtrRegisterEntry s_osea.reg reg binding.addr
          (binding.addr - binding.addr) (blockSize τ) tag := by
        rw [Nat.sub_self]
        exact h_entry
      have h_useMut' : MSB.useMut s_osea.perms binding.addr vs'.length tag = .ok p2 := by
        rw [← ListRel.length_eq h_rel]
        exact h_useMut_tgt
      obtain ⟨h_wtp, h_sms'⟩ :=
        writeThroughPtr_sim
          (resolved := { addr := binding.addr, tag := binding.tag,
                         allocBase := binding.addr, allocSize := blockSize τ })
          "CStore Invalid Ptr" vs vs' h_len h_rel h_id_a h_entry' h_useMut' h_sms
          (Nat.le_refl _)
          (fun k hk => by
            obtain ⟨a', ha'⟩ := h_dom k (by rw [← h_len]; exact hk)
            have := h_id_a _ _ ha'
            grind)
          h_write
      have h_run : oseair.runN MSB 1 s_osea compProg
          = oseair.Result.Ok { s_osea with perms := p2, mem := oseair.writeWordSeq s_osea.mem binding.addr vs', pc := s_osea.pc + 1 } :=
        runN_CStore_step compProg s_osea _ (layoutToTyVal τ) vs' reg
          h_code h_size h_wtp
      refine ⟨_, 1, h_run, ?_⟩
      refine ⟨CheckedCompilerM.run
        (compileStmtChecked (Stmt.assign (.local loc) rhs)) csPrefix,
        ⟨prefixCompileState_succ h_csAt h_stmt h_stmtOut, ?_⟩, ?_, ?_, h_psim',
        h_id_a, h_wf_t, ?_, ?_, ?_, ?_⟩
      · rw [h_stmtRun]
        show s_osea.pc + 1 = (emit csPrefix _).nextLabel
        rw [h_pc]
        simp [emit]
      · intro τ' loc' binding' h_env'
        obtain ⟨reg', base', tag', h_pi', h_entry'', h_ra', h_rt', h_nw', h_dom'⟩ :=
          h_lbs loc' binding' h_env'
        refine ⟨reg', base', tag', ?_, h_entry'', h_ra', h_rt', h_nw', h_dom'⟩
        rw [h_stmtRun]
        exact h_pi'
      · exact h_sms'
      · show TagRenameBounded ρt perms'.NextTag p2.NextTag
        rw [sb_write_NextTag h_useMut_src, sb_write_NextTag h_useMut_tgt]
        exact h_tbd
      · simp only [AllocLockstep, mirlite_writeWordSeq_addrStart,
          oseair_writeWordSeq_addrStart]
        exact h_alloc
      · intro τ' loc' h_none
        rw [h_stmtRun]
        exact h_unmap loc' h_none
      · rw [h_stmtRun]
        exact h_prb
    · simp at h_w

/-- REGIME A, CLOSED: constant write to an already-bound local — the
    `constInit` instance of `const_store_local_existing_simulation`. -/
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
      CompilerInv cs0 prog ρa ρt s_mir' s_osea' :=
  const_store_local_existing_simulation
    (vs := [mirlite.MemValue.word v]) (vs' := [Val.Dat v]) compProg (.constInit v)
    rfl (by exact ⟨rfl, trivial⟩) rfl h_comp h_inv h_stmt
    (fun cs reg h => compileStmt_local_existing_run (cs := cs) v h)
    (fun cs => ⟨{ result := (), evidence := StmtEvidence.assignLocal loc (.constInit v) (CompilerM.value (ensureLocalRegE loc) cs).result (CompilerM.value (ensureLocalRegE loc) cs).evidence (RExprToEvidence.constInit v) },
      by simp [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked,
        emitM, cleanupInstrs, emit_nil, CompilerM.run]⟩)
    h_env h_write

/-! ## §U The `uninit` instances

    `uninit` stores `blockSize τ` undef cells at ANY layout type. Its
    `ListRel` obligation is free: `MemValSim`'s first clause is
    `| .undef, _ => True`, so an undef source cell refines any target
    value. -/

/-- Two equally long runs of undef refine each other cell-by-cell. -/
theorem ListRel_replicate_undef (ρa : AddrRenameMap) (ρt : TagRenameMap)
    (n : Nat) (v : Val) :
    ListRel (MemValSim ρa ρt) (List.replicate n mirlite.MemValue.undef)
      (List.replicate n v) := by
  induction n with
  | zero => trivial
  | succ n ih =>
      rw [List.replicate_succ, List.replicate_succ]
      exact ⟨trivial, ih⟩

/-- `blockSize` IS the compiled type's cell count. -/
theorem blockSize_eq_typeSize (τ : LayoutTy) :
    blockSize τ = obseq.typeSize (layoutToTyVal τ) := by
  simp [blockSize]

theorem compileStmt_local_uninit_run
    {Γ : Ctx} {τ : LayoutTy} {loc : Local Γ τ} {cs : CompilerState}
    {reg : Register}
    (h : getPlaceInfo cs loc.idx.1 = some (reg, τ)) :
    CheckedCompilerM.run
        (compileStmtChecked (Stmt.assign (.local loc) .uninit)) cs
      = emit cs [Instr.CStore (layoutToTyVal τ)
          (List.replicate (blockSize τ) Val.Undef) reg] := by
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_existing h
  simp [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked, h_run, h_val]
  simp [CompilerM.run, emitM, cleanupInstrs, emit_nil]

/-- REGIME A for `uninit`: undef-fill of an already-bound local. -/
theorem uninit_local_existing_simulation
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {τ : LayoutTy} {loc : Local Γ τ}
    {binding : mirlite.Binding}
    (compProg : oseair.Prog)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    (h_stmt : prog.get? s_mir.pc = some (.assign (.local loc) .uninit))
    (h_env : mirlite.Env.lookup s_mir.env loc = some binding)
    (h_write : mirlite.writeResolvedPlace (τ := τ) MSB s_mir
        { addr := binding.addr, tag := binding.tag, allocBase := binding.addr,
          allocSize := blockSize τ }
        (List.replicate (blockSize τ) mirlite.MemValue.undef)
        List.length_replicate = .ok s_mir') :
    ∃ (s_osea' : oseair.State MSB) (n : Nat),
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa ρt s_mir' s_osea' :=
  const_store_local_existing_simulation
    (vs := List.replicate (blockSize τ) mirlite.MemValue.undef)
    (vs' := List.replicate (blockSize τ) Val.Undef) compProg .uninit
    List.length_replicate (ListRel_replicate_undef ρa ρt _ _)
    (List.length_replicate.trans (blockSize_eq_typeSize τ))
    h_comp h_inv h_stmt
    (fun cs reg h => compileStmt_local_uninit_run (cs := cs) h)
    (fun cs => ⟨{ result := (), evidence := StmtEvidence.assignLocal loc .uninit (CompilerM.value (ensureLocalRegE loc) cs).result (CompilerM.value (ensureLocalRegE loc) cs).evidence RExprToEvidence.uninit },
      by simp [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked,
        emitM, cleanupInstrs, emit_nil, CompilerM.run]⟩)
    h_env h_write

/-- REGIME B, CLOSED: constant write to a FRESH local. The destination is
    unbound, so mirlite's `preparePlaceAssign` allocated it and the
    compiled fragment is two instructions — the root `Alloc` that
    `ensurePlaceRoot` emits, then the `CStore`. This is the only regime
    that grows BOTH renames: `AllocLockstep` makes the two allocators hand
    out the same address (so ρa extends by the identity pair) and the
    `sb_own` member mints the root tag on both machines (so ρt extends at
    the fresh pair). -/
theorem const_store_fresh_local_simulation
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_pre s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {τ : LayoutTy} {loc : Local Γ τ}
    {resolved : mirlite.PlaceRes} {permsD : MSB.State}
    {vs : List mirlite.MemValue} {vs' : List Val}
    (compProg : oseair.Prog) (rhs : RExpr Γ τ)
    (h_len : vs.length = blockSize τ)
    (h_rel : ∀ (ρa' : AddrRenameMap) (ρt' : TagRenameMap),
      ListRel (MemValSim ρa' ρt') vs vs')
    (h_size : vs'.length = obseq.typeSize (layoutToTyVal τ))
    (h_run0 : ∀ cs, getPlaceInfo cs loc.idx.1 = none →
      CheckedCompilerM.run (compileStmtChecked (Stmt.assign (.local loc) rhs)) cs
        = emit (setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 }
              [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal τ))])
            loc.idx.1 (Register.R cs.nextReg, τ))
          [Instr.CStore (layoutToTyVal τ) vs' (Register.R cs.nextReg)])
    (h_val0 : ∀ cs, ∃ so,
      CheckedCompilerM.value (compileStmtChecked (Stmt.assign (.local loc) rhs)) cs
        = Except.ok so)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    (h_stmt : prog.get? s_mir.pc = some (.assign (.local loc) rhs))
    (h_env : mirlite.Env.lookup s_mir.env loc = none)
    (h_prep : mirlite.preparePlaceAssign MSB s_mir (.local loc) = .ok s_pre)
    (h_res  : mirlite.resolvePlaceAcc MSB s_pre (.local loc) = .ok (resolved, permsD))
    (h_write : mirlite.writeResolvedPlace (τ := τ)
                 MSB { s_pre with perms := permsD } resolved
                 vs h_len = .ok s_mir') :
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
      (blockSize τ) with
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
      have h_incr_a : AddrRenameIncr ρa
          (ρa.extendBlock s_mir.mem.addrStart (blockSize τ)) :=
        AddrRenameIncr.extendBlock h_id_a _ _
      have h_id_a' : IdentityOnDomain
          (ρa.extendBlock s_mir.mem.addrStart (blockSize τ)) :=
        IdentityOnDomain.extendBlock h_id_a _ _
      have h_ra_new : (ρa.extendBlock s_mir.mem.addrStart (blockSize τ))
          s_mir.mem.addrStart = some s_mir.mem.addrStart :=
        AddrRenameMap.extendBlock_base _ _ _
      have h_rt_new : (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag)
          s_mir.perms.NextTag = some s_osea.perms.NextTag :=
        TagRenameMap.extend_self _ _ _
      have h0 : wildcardTag < s_mir.perms.NextTag := (h_tbd _ _ h_wf_t.2).1
      have h_nw : (s_mir.perms.NextTag == wildcardTag) = false := by grind
      -- §4 the compiled fragment: `Alloc` then `CStore`
      have h_stmtRun := h_run0 csPrefix h_pi_none
      obtain ⟨stmtOut, h_stmtOut⟩ := h_val0 csPrefix
      -- §5 the two instructions, at pc and pc+1
      have h_sz : obseq.typeSize (layoutToTyVal τ)
          = blockSize τ := obseq.typeSize_layoutToTyVal _
      have h_code1 : compProg s_osea.pc
          = some (Instr.Assgn (Register.R csPrefix.nextReg)
              (Rhs.Alloc (layoutToTyVal τ))) := by
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
              (Rhs.Alloc (layoutToTyVal τ))] (k := 0) (by simp)
          simpa using h
      have h_code2 : compProg (s_osea.pc + 1)
          = some (Instr.CStore (layoutToTyVal τ) vs'
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
                (Rhs.Alloc (layoutToTyVal τ))])
              loc.idx.1 (Register.R csPrefix.nextReg, τ))
            [Instr.CStore (layoutToTyVal τ) vs' (Register.R csPrefix.nextReg)]
            (k := 0) (by simp)
          simpa [emit, setPlaceInfo] using h
      -- §6 execute the `Alloc`
      have h_own_tgt' : MSB.own s_osea.perms s_osea.mem.addrStart
          (obseq.typeSize (layoutToTyVal τ))
          = .ok (tgtPerms, s_osea.perms.NextTag) := by
        rw [h_sz, h_addr_eq]
        exact h_own_tgt
      have h_run1 := runN_Assgn_Alloc_step compProg s_osea
        (Register.R csPrefix.nextReg) (layoutToTyVal τ)
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
                  (obseq.typeSize (layoutToTyVal τ))
                  s_osea.perms.NextTag]))
              (Register.R csPrefix.nextReg) s_mir.mem.addrStart
              (s_mir.mem.addrStart - s_mir.mem.addrStart)
              (blockSize τ) s_osea.perms.NextTag := by
            rw [Nat.sub_self, ← h_addr_eq, ← h_sz]
            exact RegMap.lookup_insert_self _ _ _
          have h_useMut_tgt' : MSB.useMut tgtPerms s_mir.mem.addrStart vs'.length
              s_osea.perms.NextTag = .ok p2 := by
            rw [← ListRel.length_eq (h_rel ρa ρt)]
            exact h_useMut_tgt
          obtain ⟨h_wtp, h_sms'⟩ :=
            writeThroughPtr_sim (τ := τ)
              (s_osea := { s_osea with
                mem := (oseair.allocate s_osea.mem
                  (obseq.typeSize (layoutToTyVal τ))).2,
                perms := tgtPerms,
                reg := oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
                  (obseq.TyVal.PTy, [Val.Ptr s_osea.mem.addrStart 0
                    (obseq.typeSize (layoutToTyVal τ))
                    s_osea.perms.NextTag]),
                pc := s_osea.pc + 1 })
              (resolved := { addr := s_mir.mem.addrStart, tag := s_mir.perms.NextTag,
                             allocBase := s_mir.mem.addrStart,
                             allocSize := blockSize τ })
              "CStore Invalid Ptr" vs vs' h_len (h_rel _ _) h_id_a' h_entry1 h_useMut_tgt'
              (by exact SourceMemSim.rename_mono h_incr_a h_incr_t h_sms) (Nat.le_refl _)
              (fun k hk =>
                AddrRenameMap.extendBlock_mem (by rw [← h_len]; exact hk))
              h_write
          have h_run2 := runN_CStore_step compProg _ _
            (layoutToTyVal τ) vs' (Register.R csPrefix.nextReg)
            h_code2 h_size h_wtp
          have h_run := (oseair_runN_add 1 1 s_osea compProg _ h_run1).trans h_run2
          -- §8 rebuild the invariant under both extended renames
          refine ⟨_, _, _, 1 + 1, h_incr_a, h_incr_t, h_run, ?_⟩
          refine ⟨CheckedCompilerM.run
            (compileStmtChecked (Stmt.assign (.local loc) rhs)) csPrefix,
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
            · have h_ty : τ' = τ := by
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
              · -- the WHOLE fresh block is in ρa's domain, by `extendBlock`
                exact fun k hk => ⟨_, AddrRenameMap.extendBlock_mem hk⟩
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

/-- REGIME B, CLOSED: constant write to a FRESH local — the `constInit`
    instance of `const_store_fresh_local_simulation`. -/
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
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' :=
  const_store_fresh_local_simulation
    (vs := [mirlite.MemValue.word v]) (vs' := [Val.Dat v])
    compProg (.constInit v) rfl (fun _ _ => by exact ⟨rfl, trivial⟩) rfl
    (fun cs h => compileStmt_local_fresh_run (cs := cs) v h)
    (fun cs => ⟨{ result := (), evidence := StmtEvidence.assignLocal loc (.constInit v) (CompilerM.value (ensureLocalRegE loc) cs).result (CompilerM.value (ensureLocalRegE loc) cs).evidence (RExprToEvidence.constInit v) },
      by simp [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked,
        emitM, cleanupInstrs, emit_nil, CompilerM.run]⟩)
    h_comp h_inv h_stmt h_env h_prep h_res h_write

/-- The compiled fragment for an undef-fill of a FRESH local: the root
    `Alloc` that `ensurePlaceRoot` emits, then the wide `CStore`. -/
theorem compileStmt_local_fresh_uninit_run
    {Γ : Ctx} {τ : LayoutTy} {loc : Local Γ τ} {cs : CompilerState}
    (h : getPlaceInfo cs loc.idx.1 = none) :
    CheckedCompilerM.run
        (compileStmtChecked (Stmt.assign (.local loc) .uninit)) cs
      = emit
          (setPlaceInfo
            (emit { cs with nextReg := cs.nextReg + 1 }
              [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal τ))])
            loc.idx.1 (Register.R cs.nextReg, τ))
          [Instr.CStore (layoutToTyVal τ)
            (List.replicate (blockSize τ) Val.Undef) (Register.R cs.nextReg)] := by
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_fresh (loc := loc) h
  have h_pi : getPlaceInfo
      (setPlaceInfo
        (emit { cs with nextReg := cs.nextReg + 1 }
          [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal τ))])
        loc.idx.1 (Register.R cs.nextReg, τ))
      loc.idx.1 = some (Register.R cs.nextReg, τ) :=
    getPlaceInfo_setPlaceInfo_self _ _ _
  simp [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked,
    CompilerM.run_bind, CompilerM.run_pure, h_run, h_val,
    placeToRegChecked, h_pi]
  simp [CompilerM.run, CompilerM.value, emitM, cleanupInstrs, emit_nil]

/-- REGIME B for `uninit`: undef-fill of a FRESH local. Unlike the
    single-cell `constInit` instance, ρa extends over the WHOLE
    `blockSize τ` block (`extendBlock`), not at the base alone. -/
theorem uninit_fresh_local_simulation
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_pre s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {τ : LayoutTy} {loc : Local Γ τ}
    {resolved : mirlite.PlaceRes} {permsD : MSB.State}
    (compProg : oseair.Prog)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    (h_stmt : prog.get? s_mir.pc = some (.assign (.local loc) .uninit))
    (h_env : mirlite.Env.lookup s_mir.env loc = none)
    (h_prep : mirlite.preparePlaceAssign MSB s_mir (.local loc) = .ok s_pre)
    (h_res  : mirlite.resolvePlaceAcc MSB s_pre (.local loc) = .ok (resolved, permsD))
    (h_write : mirlite.writeResolvedPlace (τ := τ)
                 MSB { s_pre with perms := permsD } resolved
                 (List.replicate (blockSize τ) mirlite.MemValue.undef)
                 List.length_replicate = .ok s_mir') :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' :=
  const_store_fresh_local_simulation
    (vs := List.replicate (blockSize τ) mirlite.MemValue.undef)
    (vs' := List.replicate (blockSize τ) Val.Undef)
    compProg .uninit List.length_replicate
    (fun ρa' ρt' => ListRel_replicate_undef ρa' ρt' _ _)
    (List.length_replicate.trans (blockSize_eq_typeSize τ))
    (fun cs h => compileStmt_local_fresh_uninit_run (cs := cs) h)
    (fun cs => ⟨{ result := (), evidence := StmtEvidence.assignLocal loc .uninit (CompilerM.value (ensureLocalRegE loc) cs).result (CompilerM.value (ensureLocalRegE loc) cs).evidence RExprToEvidence.uninit },
      by simp [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked,
        emitM, cleanupInstrs, emit_nil, CompilerM.run]⟩)
    h_comp h_inv h_stmt h_env h_prep h_res h_write

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

theorem compileStmt_proj_zero_uninit_run
    {Γ : Ctx} {σ : LayoutTy} {base : Place Γ σ}
    {τ : LayoutTy} {path : PathTo σ τ} {cs : CompilerState}
    {baseOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Mut base)}
    {reg : Register}
    (h_np : ∀ (σ' : LayoutTy) (b : Place Γ σ') (q : PathTo σ' σ),
      base = b.proj q → False)
    (h_off : pathOffset path = 0)
    (h_root : CompilerM.run (ensurePlaceRoot (Place.proj base path)) cs = cs)
    (h_brun : CheckedCompilerM.run (placeToRegChecked RefKind.Mut base) cs = cs)
    (h_bval : CheckedCompilerM.value (placeToRegChecked RefKind.Mut base) cs
      = Except.ok baseOut)
    (h_bres : baseOut.result = { reg := reg, cleanup := [] }) :
    CheckedCompilerM.run
        (compileStmtChecked (Stmt.assign (.proj base path) .uninit)) cs
      = emit cs [Instr.CStore (layoutToTyVal τ) (List.replicate (blockSize τ) Val.Undef) reg] := by
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
                (borrowRhs RefKind.Mut (blockSize τ) baseRes.reg offset)])
            pure {
              result := { reg := tmpReg,
                          cleanup := baseRes.cleanup ++ [(tmpReg, blockSize τ)] },
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

theorem compileStmt_proj_offset_uninit_run
    {Γ : Ctx} {σ : LayoutTy} {base : Place Γ σ}
    {τ : LayoutTy} {path : PathTo σ τ} {cs : CompilerState}
    {baseOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Mut base)}
    {reg : Register}
    (h_np : ∀ (σ' : LayoutTy) (b : Place Γ σ') (q : PathTo σ' σ),
      base = b.proj q → False)
    (h_off : pathOffset path ≠ 0)
    (h_root : CompilerM.run (ensurePlaceRoot (Place.proj base path)) cs = cs)
    (h_brun : CheckedCompilerM.run (placeToRegChecked RefKind.Mut base) cs = cs)
    (h_bval : CheckedCompilerM.value (placeToRegChecked RefKind.Mut base) cs
      = Except.ok baseOut)
    (h_bres : baseOut.result = { reg := reg, cleanup := [] }) :
    CheckedCompilerM.run
        (compileStmtChecked (Stmt.assign (.proj base path) .uninit)) cs
      = emit (emit (emit { cs with nextReg := cs.nextReg + 1 }
          [Instr.Assgn (Register.R cs.nextReg)
            (borrowRhs RefKind.Mut (blockSize τ) reg (pathOffset path))])
          [Instr.CStore (layoutToTyVal τ) (List.replicate (blockSize τ) Val.Undef) (Register.R cs.nextReg)])
          [Instr.Die (Register.R cs.nextReg) (blockSize τ)] := by
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
                (borrowRhs RefKind.Mut (blockSize τ) baseRes.reg offset)])
            pure {
              result := { reg := tmpReg,
                          cleanup := baseRes.cleanup ++ [(tmpReg, blockSize τ)] },
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

/-- The fragment of `(*P).path := v` at ZERO offset, over the OPAQUE
    run of the pointer-place lowering `Mut (.deref P)` — the projection
    passes the loaded register through, so the statement adds one
    `CStore` (the chain-dst shape). -/
theorem compileStmt_proj_deref_zero_run
    {Γ : Ctx} {σ : LayoutTy}
    {P : Place Γ (obseq.LayoutTy.PtrL σ)} {path : PathTo σ obseq.LayoutTy.NatL}
    {cs : CompilerState}
    {dOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Mut (.deref P))}
    (v : Word)
    (h_o : pathOffset path = 0)
    (h_root : CompilerM.run (ensurePlaceRoot (Place.proj (Place.deref P) path)) cs = cs)
    (h_dval : CheckedCompilerM.value (placeToRegChecked RefKind.Mut (.deref P)) cs
      = Except.ok dOut)
    (h_dclean : dOut.result.cleanup = []) :
    CheckedCompilerM.run
        (compileStmtChecked (Stmt.assign (.proj (.deref P) path) (.constInit v))) cs
      = emit (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (.deref P)) cs)
          [Instr.CStore obseq.TyVal.NatTy [Val.Dat v] dOut.result.reg] := by
  have h_proj_eq := placeToRegChecked_proj_root_eq (Γ := Γ) (kind := RefKind.Mut)
    (base := .deref P) path (fun _ _ _ h => by cases h)
  simp only [compileStmtChecked, h_proj_eq, compileRExprToChecked,
    compileRExprPreChecked,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
    h_root, h_dval, h_o, dif_pos]
  simp [CompilerM.run, CompilerM.value, emitM, cleanupInstrs, h_dclean, emit_nil]

/-- The zero-offset projected statement lowers. -/
theorem compileStmt_proj_deref_zero_value
    {Γ : Ctx} {σ : LayoutTy}
    {P : Place Γ (obseq.LayoutTy.PtrL σ)} {path : PathTo σ obseq.LayoutTy.NatL}
    {cs : CompilerState}
    {dOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Mut (.deref P))}
    (v : Word)
    (h_o : pathOffset path = 0)
    (h_root : CompilerM.run (ensurePlaceRoot (Place.proj (Place.deref P) path)) cs = cs)
    (h_dval : CheckedCompilerM.value (placeToRegChecked RefKind.Mut (.deref P)) cs
      = Except.ok dOut) :
    ∃ so, CheckedCompilerM.value
      (compileStmtChecked (Stmt.assign (.proj (.deref P) path) (.constInit v))) cs
      = Except.ok so := by
  have h_proj_eq := placeToRegChecked_proj_root_eq (Γ := Γ) (kind := RefKind.Mut)
    (base := .deref P) path (fun _ _ _ h => by cases h)
  simp only [compileStmtChecked, h_proj_eq, compileRExprToChecked,
    compileRExprPreChecked,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
    h_root, h_dval, h_o, dif_pos]
  exact ⟨_, rfl⟩

/-- The fragment of `(*P).path := v` (nonzero offset), over the OPAQUE
    run of `Mut (.deref P)`: `[dst-code; Borrow(Mut); CStore; Die]` —
    the depth-1 BRIDGE 1 shape over the mother lemma's register. -/
theorem compileStmt_proj_deref_run
    {Γ : Ctx} {σ : LayoutTy}
    {P : Place Γ (obseq.LayoutTy.PtrL σ)} {path : PathTo σ obseq.LayoutTy.NatL}
    {cs : CompilerState}
    {dOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Mut (.deref P))}
    (v : Word)
    (h_off : pathOffset path ≠ 0)
    (h_root : CompilerM.run (ensurePlaceRoot (Place.proj (Place.deref P) path)) cs = cs)
    (h_dval : CheckedCompilerM.value (placeToRegChecked RefKind.Mut (.deref P)) cs
      = Except.ok dOut)
    (h_dclean : dOut.result.cleanup = []) :
    CheckedCompilerM.run
        (compileStmtChecked (Stmt.assign (.proj (.deref P) path) (.constInit v))) cs
      = emit (emit (emit
          { (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (.deref P)) cs) with
              nextReg := (CheckedCompilerM.run
                (placeToRegChecked RefKind.Mut (.deref P)) cs).nextReg + 1 }
          [Instr.Assgn (Register.R (CheckedCompilerM.run
              (placeToRegChecked RefKind.Mut (.deref P)) cs).nextReg)
            (borrowRhs RefKind.Mut (blockSize obseq.LayoutTy.NatL)
              dOut.result.reg (pathOffset path))])
          [Instr.CStore obseq.TyVal.NatTy [Val.Dat v]
            (Register.R (CheckedCompilerM.run
              (placeToRegChecked RefKind.Mut (.deref P)) cs).nextReg)])
          [Instr.Die (Register.R (CheckedCompilerM.run
              (placeToRegChecked RefKind.Mut (.deref P)) cs).nextReg)
            (blockSize obseq.LayoutTy.NatL)] := by
  have h_proj_eq := placeToRegChecked_proj_root_eq (Γ := Γ) (kind := RefKind.Mut)
    (base := .deref P) path (fun _ _ _ h => by cases h)
  simp only [compileStmtChecked, h_proj_eq, compileRExprToChecked,
    compileRExprPreChecked,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
    h_root, h_dval]
  simp [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM,
    cleanupInstrs, h_dclean, emit_nil, h_off, borrowRhs]

/-- The nonzero-offset projected statement lowers. -/
theorem compileStmt_proj_deref_value
    {Γ : Ctx} {σ : LayoutTy}
    {P : Place Γ (obseq.LayoutTy.PtrL σ)} {path : PathTo σ obseq.LayoutTy.NatL}
    {cs : CompilerState}
    {dOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Mut (.deref P))}
    (v : Word)
    (h_off : pathOffset path ≠ 0)
    (h_root : CompilerM.run (ensurePlaceRoot (Place.proj (Place.deref P) path)) cs = cs)
    (h_dval : CheckedCompilerM.value (placeToRegChecked RefKind.Mut (.deref P)) cs
      = Except.ok dOut) :
    ∃ so, CheckedCompilerM.value
      (compileStmtChecked (Stmt.assign (.proj (.deref P) path) (.constInit v))) cs
      = Except.ok so := by
  have h_proj_eq := placeToRegChecked_proj_root_eq (Γ := Γ) (kind := RefKind.Mut)
    (base := .deref P) path (fun _ _ _ h => by cases h)
  simp only [compileStmtChecked, h_proj_eq, compileRExprToChecked,
    compileRExprPreChecked,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
    h_root, h_dval, dif_neg h_off]
  exact ⟨_, rfl⟩

/-- REGIME C-deref-ZERO, COLLAPSED 2026-08-29 (2026-08-29: onto the
    mother lemma): `(*P).f := v` at ZERO offset for ANY canonical chain
    `*P` — the projection passes the loaded register through, so the
    mother lemma at `Mut` on `.deref P` delivers the write register and
    the statement adds one `CStore`, exactly the chain-dst endgame with
    the resolution carrying a `+ 0` the record η-rule erases. Takes the
    `stmt0` transfer triple so flattening recursions land here. -/
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
    (h_chain : PtrChain (Place.deref P))
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
  have h_pre : s_pre = s_mir ∧
      ∃ r0, mirlite.resolvePlace? s_mir (.proj (.deref P) path) = some r0 := by
    simp only [mirlite.preparePlaceAssign] at h_prep
    split at h_prep
    · rename_i r0 h_r0
      cases h_prep
      exact ⟨rfl, r0, h_r0⟩
    · simp [mirlite.allocateRoot] at h_prep
  obtain ⟨h_pre_eq, r0, h_resolved⟩ := h_pre
  rw [h_pre_eq] at h_res h_write
  obtain ⟨csPrefix, ⟨h_csAt, h_pc⟩, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_tbd,
    h_alloc, h_unmap, h_prb⟩ := h_inv
  -- open ONE projection layer of the source resolution, keeping the
  -- chain's own resolution opaque for the mother lemma
  cases h_dres : mirlite.resolvePlaceAcc MSB s_mir (Place.deref P) with
  | error e =>
      rw [resolvePlaceAcc_proj_base_err h_dres] at h_res
      simp at h_res
  | ok pr =>
  obtain ⟨rd, permsP⟩ := pr
  rw [resolvePlaceAcc_proj_base_ok h_dres] at h_res
  simp only [Except.ok.injEq, Prod.mk.injEq] at h_res
  obtain ⟨h_r1, h_r2⟩ := h_res
  subst h_r1
  subst h_r2
  -- at zero offset the projected resolution IS the chain's
  have h_resolved_eq : ({ rd with addr := rd.addr + PathTo.offset path }
      : mirlite.PlaceRes) = rd := by
    have h_o' : PathTo.offset path = 0 := h_o
    simp [h_o']
  rw [h_resolved_eq] at h_write
  -- compiled-side scaffolding
  have h_mapped : PlaceInputsMapped csPrefix (Place.proj (Place.deref P) path) :=
    placeInputsMapped_of_localBindingSim_resolvePlace h_lbs h_resolved
  have h_mappedD : PlaceInputsMapped csPrefix (Place.deref P) := h_mapped
  have h_root := ensurePlaceRoot_run_eq_of_mapped h_mapped
  obtain ⟨dstOut0, h_dval0⟩ := placeToRegChecked_ok_of_placeInputsMapped
    (cs := csPrefix) (kind := RefKind.Mut) h_mappedD
  obtain ⟨stmtOutC, h_stmtOutC⟩ := compileStmt_proj_deref_zero_value v h_o h_root h_dval0
  obtain ⟨stmtOut, h_stmtOut⟩ := h_val0 csPrefix stmtOutC h_stmtOutC
  have h_proj_eq := placeToRegChecked_proj_root_eq (Γ := Γ) (kind := RefKind.Mut)
    (base := .deref P) path (fun _ _ _ h => by cases h)
  have h_incr1 : StateIncr
      (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (.deref P)) csPrefix)
      (CheckedCompilerM.run (placeToRegChecked RefKind.Mut
        (.proj (.deref P) path)) csPrefix) := by
    rw [h_proj_eq, CheckedCompilerM.run_bind]
    cases h : CheckedCompilerM.value (placeToRegChecked RefKind.Mut (.deref P)) csPrefix with
    | ok a => exact CheckedCompilerM.incr _ _
    | error e => exact StateIncr.refl _
  have h_incr2 : StateIncr
      (CheckedCompilerM.run (placeToRegChecked RefKind.Mut
        (.proj (.deref P) path)) csPrefix)
      (CheckedCompilerM.run
        (compileStmtChecked (Stmt.assign (.proj (.deref P) path) (.constInit v))) csPrefix) := by
    rw [show compileStmtChecked (Stmt.assign (.proj (.deref P) path) (.constInit v))
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
            }) from rfl]
    rw [CheckedCompilerM.run_bind]
    simp only [CheckedCompilerM.value_lift, CheckedCompilerM.run_lift, h_root]
    rw [CheckedCompilerM.run_bind]
    cases h : CheckedCompilerM.value
        (placeToRegChecked RefKind.Mut (.proj (.deref P) path)) csPrefix with
    | ok a => exact CheckedCompilerM.incr _ _
    | error e => exact StateIncr.refl _
  have h_instD : ∀ q' instr,
      q' < (CheckedCompilerM.run
        (placeToRegChecked RefKind.Mut (.deref P)) csPrefix).nextLabel →
      (CheckedCompilerM.run
        (placeToRegChecked RefKind.Mut (.deref P)) csPrefix).code q'
        = some instr →
      compProg q' = some instr := by
    intro q' instr h_lt h_code
    have h_incrS := StateIncr.trans h_incr1 h_incr2
    refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
    · rw [h_run0]
      exact Nat.lt_of_lt_of_le h_lt h_incrS.nextLabel_le
    · rw [h_run0, h_incrS.code_eq q' h_lt]
      exact h_code
  obtain ⟨dOut, n1, s_mid, tres, h_dval, h_dclean, h_drun, h_dpc, h_dmem, h_dpsim,
    h_dnt1, h_dnt2, h_dlbs, h_dentry, h_drt, h_dnw, h_dle, h_drange, h_dbelow,
    h_dprm, h_dregmono, h_dlabmono, -, -⟩ :=
    ptrChain_lowering_sim h_id_a h_wf_t h_chain RefKind.Mut csPrefix s_osea
      rd permsP h_dres h_tbd h_lbs h_prb h_sms h_psim h_pc h_instD
  have h_stmtRunC := compileStmt_proj_deref_zero_run v h_o h_root h_dval h_dclean
  have h_stmtRun := (h_run0 csPrefix).trans h_stmtRunC
  have h_code : compProg s_mid.pc
      = some (Instr.CStore obseq.TyVal.NatTy [Val.Dat v] dOut.result.reg) := by
    rw [h_dpc]
    refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
    · rw [h_stmtRun]
      show _ < _ + 1
      exact Nat.lt_succ_self _
    · rw [h_stmtRun]
      have h := emit_code_at_new
        (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (.deref P)) csPrefix)
        [Instr.CStore obseq.TyVal.NatTy [Val.Dat v] dOut.result.reg]
        (k := 0) (by simp)
      simpa using h
  have h_w := h_write
  simp only [mirlite.writeResolvedPlace] at h_w
  split at h_w
  · simp at h_w
  · rename_i h_nb
    split at h_w
    · rename_i perms2 h_useMut_src
      cases h_w
      obtain ⟨p3, h_useMut_tgt, h_psim3⟩ :=
        sb_write_respects_PermSim h_dpsim h_wf_t h_drt h_dnw h_useMut_src
      obtain ⟨h_wtp, h_sms'⟩ :=
        writeThroughPtr_sim (τ := obseq.LayoutTy.NatL)
          (s_osea := s_mid) (resolved := rd)
          "CStore Invalid Ptr" [mirlite.MemValue.word v] [Val.Dat v] rfl
          ⟨rfl, trivial⟩ h_id_a h_dentry h_useMut_tgt
          (by rw [h_dmem]; exact h_sms)
          h_dle
          (fun k hk => by
            have hk0 : k = 0 := by simpa using hk
            subst hk0
            have h_lt : rd.addr - rd.allocBase < rd.allocSize := by
              grind
            obtain ⟨a', ha'⟩ := h_drange _ h_lt
            have h_eq := h_id_a _ _ ha'
            have h_cancel : rd.allocBase + (rd.addr - rd.allocBase)
                = rd.addr := Nat.add_sub_cancel' h_dle
            grind)
          h_write
      have h_run2 := runN_CStore_step compProg s_mid _
        obseq.TyVal.NatTy [Val.Dat v] dOut.result.reg h_code rfl h_wtp
      refine ⟨_, n1 + 1,
        (oseair_runN_add n1 1 s_osea compProg s_mid h_drun).trans h_run2, ?_⟩
      refine ⟨CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix,
        ⟨prefixCompileState_succ h_csAt h_stmt h_stmtOut, ?_⟩, ?_, h_sms', h_psim3,
        h_id_a, h_wf_t, ?_, ?_, ?_, ?_⟩
      · show s_mid.pc + 1 = _
        rw [h_dpc, h_stmtRun]
        simp [emit]
      · intro τ'' loc' binding' h_env'
        obtain ⟨reg', base', tag', h_pi', h_entry', h_ra', h_rt', h_nw', h_dom'⟩ :=
          h_dlbs loc' binding' h_env'
        refine ⟨reg', base', tag', ?_, h_entry', h_ra', h_rt', h_nw', h_dom'⟩
        rw [h_stmtRun, getPlaceInfo_emit]
        show (CheckedCompilerM.run
          (placeToRegChecked RefKind.Mut (.deref P)) csPrefix).placeRegMap.lookup
            loc'.idx.1 = _
        rw [h_dprm]
        exact h_pi'
      · show TagRenameBounded _ perms2.NextTag p3.NextTag
        rw [sb_write_NextTag h_useMut_src, h_dnt1, sb_write_NextTag h_useMut_tgt]
        exact TagRenameBounded.mono h_tbd (Nat.le_refl _) h_dnt2
      · simp only [AllocLockstep, mirlite_writeWordSeq_addrStart,
          oseair_writeWordSeq_addrStart, h_dmem]
        exact h_alloc
      · intro τ'' loc' h_none
        rw [h_stmtRun, getPlaceInfo_emit]
        show (CheckedCompilerM.run
          (placeToRegChecked RefKind.Mut (.deref P)) csPrefix).placeRegMap.lookup
            loc'.idx.1 = none
        rw [h_dprm]
        exact h_unmap loc' h_none
      · intro idx reg'' τ'' h_look
        rw [h_stmtRun] at h_look ⊢
        rw [getPlaceInfo_emit] at h_look
        have h_prm2 : (CheckedCompilerM.run
            (placeToRegChecked RefKind.Mut (.deref P)) csPrefix).placeRegMap
            = csPrefix.placeRegMap := h_dprm
        have h_cs : getPlaceInfo csPrefix idx = some (reg'', τ'') := by
          show csPrefix.placeRegMap.lookup idx = _
          rw [← h_prm2]
          exact h_look
        refine RegisterBelow.mono ?_ (h_prb _ _ _ h_cs)
        simp only [emit]
        exact h_dregmono
    · simp at h_w


/-- REGIME C-deref, COLLAPSED 2026-08-29 onto the mother lemma:
    `(*P).f := v` at NONZERO offset for ANY canonical chain `*P`. The
    mother lemma at `Mut` on `.deref P` delivers the base pointer
    register; the statement adds `Borrow(Mut); CStore; Die` — the
    BRIDGE 1 endgame (`sb_ref_use_die_cancels`) through the fresh tag,
    with the Borrow's bound supplied by the source WRITE's own bounds
    check. Takes the `stmt0` transfer triple. -/
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
    (h_chain : PtrChain (Place.deref P))
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
  have h_pre : s_pre = s_mir ∧
      ∃ r0, mirlite.resolvePlace? s_mir (.proj (.deref P) path) = some r0 := by
    simp only [mirlite.preparePlaceAssign] at h_prep
    split at h_prep
    · rename_i r0 h_r0
      cases h_prep
      exact ⟨rfl, r0, h_r0⟩
    · simp [mirlite.allocateRoot] at h_prep
  obtain ⟨h_pre_eq, r0, h_resolved⟩ := h_pre
  rw [h_pre_eq] at h_res h_write
  obtain ⟨csPrefix, ⟨h_csAt, h_pc⟩, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_tbd,
    h_alloc, h_unmap, h_prb⟩ := h_inv
  cases h_dres : mirlite.resolvePlaceAcc MSB s_mir (Place.deref P) with
  | error e =>
      rw [resolvePlaceAcc_proj_base_err h_dres] at h_res
      simp at h_res
  | ok pr =>
  obtain ⟨rd, permsP⟩ := pr
  rw [resolvePlaceAcc_proj_base_ok h_dres] at h_res
  simp only [Except.ok.injEq, Prod.mk.injEq] at h_res
  obtain ⟨h_r1, h_r2⟩ := h_res
  subst h_r1
  subst h_r2
  have h_po : pathOffset path = PathTo.offset path := rfl
  -- compiled-side scaffolding
  have h_mapped : PlaceInputsMapped csPrefix (Place.proj (Place.deref P) path) :=
    placeInputsMapped_of_localBindingSim_resolvePlace h_lbs h_resolved
  have h_mappedD : PlaceInputsMapped csPrefix (Place.deref P) := h_mapped
  have h_root := ensurePlaceRoot_run_eq_of_mapped h_mapped
  obtain ⟨dstOut0, h_dval0⟩ := placeToRegChecked_ok_of_placeInputsMapped
    (cs := csPrefix) (kind := RefKind.Mut) h_mappedD
  obtain ⟨stmtOutC, h_stmtOutC⟩ := compileStmt_proj_deref_value v h_off h_root h_dval0
  obtain ⟨stmtOut, h_stmtOut⟩ := h_val0 csPrefix stmtOutC h_stmtOutC
  have h_proj_eq := placeToRegChecked_proj_root_eq (Γ := Γ) (kind := RefKind.Mut)
    (base := .deref P) path (fun _ _ _ h => by cases h)
  have h_incr1 : StateIncr
      (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (.deref P)) csPrefix)
      (CheckedCompilerM.run (placeToRegChecked RefKind.Mut
        (.proj (.deref P) path)) csPrefix) := by
    rw [h_proj_eq, CheckedCompilerM.run_bind]
    cases h : CheckedCompilerM.value (placeToRegChecked RefKind.Mut (.deref P)) csPrefix with
    | ok a => exact CheckedCompilerM.incr _ _
    | error e => exact StateIncr.refl _
  have h_incr2 : StateIncr
      (CheckedCompilerM.run (placeToRegChecked RefKind.Mut
        (.proj (.deref P) path)) csPrefix)
      (CheckedCompilerM.run
        (compileStmtChecked (Stmt.assign (.proj (.deref P) path) (.constInit v))) csPrefix) := by
    rw [show compileStmtChecked (Stmt.assign (.proj (.deref P) path) (.constInit v))
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
            }) from rfl]
    rw [CheckedCompilerM.run_bind]
    simp only [CheckedCompilerM.value_lift, CheckedCompilerM.run_lift, h_root]
    rw [CheckedCompilerM.run_bind]
    cases h : CheckedCompilerM.value
        (placeToRegChecked RefKind.Mut (.proj (.deref P) path)) csPrefix with
    | ok a => exact CheckedCompilerM.incr _ _
    | error e => exact StateIncr.refl _
  have h_instD : ∀ q' instr,
      q' < (CheckedCompilerM.run
        (placeToRegChecked RefKind.Mut (.deref P)) csPrefix).nextLabel →
      (CheckedCompilerM.run
        (placeToRegChecked RefKind.Mut (.deref P)) csPrefix).code q'
        = some instr →
      compProg q' = some instr := by
    intro q' instr h_lt h_code
    have h_incrS := StateIncr.trans h_incr1 h_incr2
    refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
    · rw [h_run0]
      exact Nat.lt_of_lt_of_le h_lt h_incrS.nextLabel_le
    · rw [h_run0, h_incrS.code_eq q' h_lt]
      exact h_code
  obtain ⟨dOut, n1, s_mid, tres, h_dval, h_dclean, h_drun, h_dpc, h_dmem, h_dpsim,
    h_dnt1, h_dnt2, h_dlbs, h_dentry, h_drt, h_dnw, h_dle, h_drange, h_dbelow,
    h_dprm, h_dregmono, h_dlabmono, -, -⟩ :=
    ptrChain_lowering_sim h_id_a h_wf_t h_chain RefKind.Mut csPrefix s_osea
      rd permsP h_dres h_tbd h_lbs h_prb h_sms h_psim h_pc h_instD
  have h_stmtRunC := compileStmt_proj_deref_run v h_off h_root h_dval h_dclean
  have h_stmtRun := (h_run0 csPrefix).trans h_stmtRunC
  -- the three compiled instructions after the dst lowering
  have h_code1 : compProg s_mid.pc
      = some (Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (Place.deref P)) csPrefix).nextReg)
          (borrowRhs RefKind.Mut (blockSize obseq.LayoutTy.NatL) dOut.result.reg (pathOffset path))) := by
    rw [h_dpc]
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
        { (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (Place.deref P)) csPrefix) with
            nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (Place.deref P)) csPrefix).nextReg + 1 }
        [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (Place.deref P)) csPrefix).nextReg)
          (borrowRhs RefKind.Mut (blockSize obseq.LayoutTy.NatL) dOut.result.reg (pathOffset path))]
        (k := 0) (by simp)
      simpa using h
  have h_code2 : compProg (s_mid.pc + 1)
      = some (Instr.CStore obseq.TyVal.NatTy [Val.Dat v]
          (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (Place.deref P)) csPrefix).nextReg)) := by
    rw [h_dpc]
    refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
    · rw [h_stmtRun]
      simp only [emit, List.length_cons, List.length_nil]
      omega
    · rw [h_stmtRun]
      rw [emit_code_lt_nextLabel _ _ (by
        simp only [emit, List.length_cons, List.length_nil]; omega)]
      have h := emit_code_at_new
        (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (Place.deref P)) csPrefix) with
            nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (Place.deref P)) csPrefix).nextReg + 1 }
          [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (Place.deref P)) csPrefix).nextReg)
            (borrowRhs RefKind.Mut (blockSize obseq.LayoutTy.NatL) dOut.result.reg (pathOffset path))])
        [Instr.CStore obseq.TyVal.NatTy [Val.Dat v]
          (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (Place.deref P)) csPrefix).nextReg)]
        (k := 0) (by simp)
      simpa [emit] using h
  have h_code3 : compProg (s_mid.pc + 1 + 1)
      = some (Instr.Die (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (Place.deref P)) csPrefix).nextReg)
          (blockSize obseq.LayoutTy.NatL)) := by
    rw [h_dpc]
    refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
    · rw [h_stmtRun]
      simp only [emit, List.length_cons, List.length_nil]
      omega
    · rw [h_stmtRun]
      have h := emit_code_at_new
        (emit (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (Place.deref P)) csPrefix) with
            nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (Place.deref P)) csPrefix).nextReg + 1 }
          [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (Place.deref P)) csPrefix).nextReg)
            (borrowRhs RefKind.Mut (blockSize obseq.LayoutTy.NatL) dOut.result.reg (pathOffset path))])
          [Instr.CStore obseq.TyVal.NatTy [Val.Dat v]
            (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (Place.deref P)) csPrefix).nextReg)])
        [Instr.Die (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (Place.deref P)) csPrefix).nextReg)
          (blockSize obseq.LayoutTy.NatL)]
        (k := 0) (by simp)
      simpa [emit] using h
  -- source write facts
  have h_w := h_write
  simp only [mirlite.writeResolvedPlace] at h_w
  split at h_w
  · simp at h_w
  · rename_i h_nb
    split at h_w
    · rename_i perms'' h_useMut_src
      cases h_w
      obtain ⟨p3, h_useMut_tgt, h_psim3⟩ :=
        sb_write_respects_PermSim h_dpsim h_wf_t h_drt h_dnw h_useMut_src
      obtain ⟨q1, h_ref_tgt⟩ := sb_ref_Mut_ok_of_sb_write_ok h_useMut_tgt
      have h_tbd2 : TagRenameBounded ρt permsP.NextTag s_mid.perms.NextTag := by
        rw [h_dnt1]
        exact TagRenameBounded.mono h_tbd (Nat.le_refl _) h_dnt2
      have h_unprot := freshTag_not_protected h_dpsim h_tbd2
      have h0 : wildcardTag < s_mid.perms.NextTag := (h_tbd2 _ _ h_wf_t.2).2
      have h_ntw : (s_mid.perms.NextTag == wildcardTag) = false := by grind
      obtain ⟨q2, q3, qAcc', h_wr1, h_die1, h_wr2, h_sm, h_ex, h_pf, h_ntle⟩ :=
        sb_ref_use_die_cancels h_ntw h_unprot h_ref_tgt
      have h_qAcc : qAcc' = p3 := by grind
      subst h_qAcc
      have h_cancel : rd.allocBase + (rd.addr - rd.allocBase) = rd.addr :=
        Nat.add_sub_cancel' h_dle
      have h_nb' : rd.addr + PathTo.offset path + 1 ≤ rd.allocBase + rd.allocSize := by
        have h1 := Nat.not_lt.mp h_nb
        simpa using h1
      have h_le2 : rd.allocBase + (rd.addr - rd.allocBase) + PathTo.offset path
          + blockSize obseq.LayoutTy.NatL ≤ rd.allocBase + rd.allocSize := by
        rw [h_cancel]
        simpa [blockSize] using h_nb'
      have h_ref_tgt' : MSB.ref s_mid.perms
          (rd.allocBase + (rd.addr - rd.allocBase) + PathTo.offset path)
          (blockSize obseq.LayoutTy.NatL) tres RefKind.Mut false []
          = .ok (q1, s_mid.perms.NextTag) := by
        rw [h_cancel]
        exact h_ref_tgt
      have h_run1 := runN_Assgn_Borrow_step compProg s_mid
        (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (Place.deref P)) csPrefix).nextReg)
        dOut.result.reg RefKind.Mut false [] (blockSize obseq.LayoutTy.NatL) (PathTo.offset path)
        h_code1 h_dentry h_le2 h_ref_tgt'
      have h_entry_tmp : PtrRegisterEntry
          (oseair.RegMap.insert s_mid.reg
            (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (Place.deref P)) csPrefix).nextReg)
            (obseq.TyVal.PTy, [Val.Ptr rd.allocBase (rd.addr - rd.allocBase + PathTo.offset path)
              rd.allocSize s_mid.perms.NextTag]))
          (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (Place.deref P)) csPrefix).nextReg)
          rd.allocBase (rd.addr + PathTo.offset path - rd.allocBase) rd.allocSize
          s_mid.perms.NextTag := by
        have h_oe : rd.addr + PathTo.offset path - rd.allocBase
            = rd.addr - rd.allocBase + PathTo.offset path :=
          Nat.sub_add_comm h_dle
        rw [h_oe]
        exact RegMap.lookup_insert_self _ _ _
      have h_wr1' : MSB.useMut q1 (rd.addr + PathTo.offset path)
          [Val.Dat v].length s_mid.perms.NextTag = .ok q2 := by
        simpa using h_wr1
      obtain ⟨h_wtp, h_sms'⟩ :=
        writeThroughPtr_sim (τ := obseq.LayoutTy.NatL)
          (s_osea :=
            { s_mid with
                perms := q1,
                reg := oseair.RegMap.insert s_mid.reg
                  (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (Place.deref P)) csPrefix).nextReg)
                  (obseq.TyVal.PTy, [Val.Ptr rd.allocBase (rd.addr - rd.allocBase + PathTo.offset path)
                    rd.allocSize s_mid.perms.NextTag]),
                pc := s_mid.pc + 1 })
          (resolved := { rd with addr := rd.addr + PathTo.offset path })
          "CStore Invalid Ptr" [mirlite.MemValue.word v] [Val.Dat v] rfl
          ⟨rfl, trivial⟩ h_id_a h_entry_tmp
          (by
            show MSB.useMut q1 (rd.addr + PathTo.offset path) [Val.Dat v].length
              s_mid.perms.NextTag = .ok q2
            exact h_wr1')
          (by
            show SourceMemSim ρa ρt s_mir.mem s_mid.mem
            rw [h_dmem]
            exact h_sms)
          (Nat.le_trans h_dle (Nat.le_add_right _ _))
          (fun k hk => by
            have hk0 : k = 0 := by simpa using hk
            subst hk0
            have h_lt : rd.addr - rd.allocBase + PathTo.offset path < rd.allocSize := by
              have h2 := Nat.sub_add_comm (m := PathTo.offset path) h_dle
              grind
            obtain ⟨a', ha'⟩ := h_drange _ h_lt
            have h_eq := h_id_a _ _ ha'
            have h_cancel2 : rd.allocBase + (rd.addr - rd.allocBase + PathTo.offset path)
                = rd.addr + PathTo.offset path := by
              rw [← Nat.add_assoc, h_cancel]
            show ρa (rd.addr + PathTo.offset path + 0)
              = some (rd.addr + PathTo.offset path + 0)
            rw [Nat.add_zero, ← h_cancel2, h_eq]
            rw [h_eq] at ha'
            exact ha')
          h_write
      have h_run2 := runN_CStore_step compProg _ _
        obseq.TyVal.NatTy [Val.Dat v]
        (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (Place.deref P)) csPrefix).nextReg)
        h_code2 rfl h_wtp
      have h_die1' : MSB.die q2
          (rd.allocBase + (rd.addr - rd.allocBase + PathTo.offset path))
          (blockSize obseq.LayoutTy.NatL) s_mid.perms.NextTag = .ok q3 := by
        rw [← Nat.add_assoc, h_cancel]
        simpa using h_die1
      have h_run3 := runN_Die_step compProg
        { s_mid with
            perms := q2,
            reg := oseair.RegMap.insert s_mid.reg
              (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (Place.deref P)) csPrefix).nextReg)
              (obseq.TyVal.PTy, [Val.Ptr rd.allocBase (rd.addr - rd.allocBase + PathTo.offset path)
                rd.allocSize s_mid.perms.NextTag]),
            mem := oseair.writeWordSeq s_mid.mem (rd.addr + PathTo.offset path) [Val.Dat v],
            pc := s_mid.pc + 1 + 1 }
        (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (Place.deref P)) csPrefix).nextReg)
        (blockSize obseq.LayoutTy.NatL)
        h_code3 (RegMap.lookup_insert_self _ _ _) h_die1'
      have h_runA := (oseair_runN_add n1 1 s_osea compProg s_mid h_drun).trans h_run1
      have h_runB := (oseair_runN_add (n1 + 1) 1 s_osea compProg _ h_runA).trans h_run2
      have h_run := (oseair_runN_add (n1 + 1 + 1) 1 s_osea compProg _ h_runB).trans h_run3
      have h_psim4 : PermSim ρt perms'' q3 := by
        obtain ⟨hs, hp, he, hn⟩ := h_psim3
        exact ⟨by rw [h_sm]; exact hs, by rw [h_pf]; exact hp,
               by rw [h_ex]; exact he, Nat.le_trans hn h_ntle⟩
      refine ⟨_, n1 + 1 + 1 + 1, h_run, ?_⟩
      refine ⟨CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix,
        ⟨prefixCompileState_succ h_csAt h_stmt h_stmtOut, ?_⟩, ?_, ?_, h_psim4,
        h_id_a, h_wf_t, ?_, ?_, ?_, ?_⟩
      · show s_mid.pc + 1 + 1 + 1 = _
        rw [h_dpc, h_stmtRun]
        simp [emit]
      · have h_lbs1 : LocalBindingSim ρa ρt s_mir.env
            { s_mid with
                perms := q1,
                reg := oseair.RegMap.insert s_mid.reg
                  (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (Place.deref P)) csPrefix).nextReg)
                  (obseq.TyVal.PTy, [Val.Ptr rd.allocBase (rd.addr - rd.allocBase + PathTo.offset path)
                    rd.allocSize s_mid.perms.NextTag]),
                pc := s_mid.pc + 1 } csPrefix :=
          LocalBindingSim.insert_fresh_reg h_dlbs h_prb h_dregmono rfl
        intro τ' loc' binding' h_env'
        obtain ⟨reg', base', tag', h_pi', h_entry', h_ra', h_rt', h_nw', h_dom'⟩ :=
          h_lbs1 loc' binding' h_env'
        refine ⟨reg', base', tag', ?_, h_entry', h_ra', h_rt', h_nw', h_dom'⟩
        rw [h_stmtRun, getPlaceInfo_emit, getPlaceInfo_emit, getPlaceInfo_emit,
          getPlaceInfo_setNextReg]
        show (CheckedCompilerM.run
          (placeToRegChecked RefKind.Mut (Place.deref P)) csPrefix).placeRegMap.lookup
            loc'.idx.1 = _
        rw [h_dprm]
        exact h_pi'
      · exact h_sms'
      · show TagRenameBounded ρt perms''.NextTag q3.NextTag
        rw [sb_write_NextTag h_useMut_src, h_dnt1]
        refine TagRenameBounded.mono h_tbd (Nat.le_refl _) ?_
        have hB : s_mid.perms.NextTag ≤ q3.NextTag := by
          rw [← sb_write_NextTag h_useMut_tgt]
          exact h_ntle
        exact Nat.le_trans h_dnt2 hB
      · simp only [AllocLockstep, mirlite_writeWordSeq_addrStart,
          oseair_writeWordSeq_addrStart, h_dmem]
        exact h_alloc
      · intro τ' loc' h_none
        rw [h_stmtRun, getPlaceInfo_emit, getPlaceInfo_emit, getPlaceInfo_emit,
          getPlaceInfo_setNextReg]
        show (CheckedCompilerM.run
          (placeToRegChecked RefKind.Mut (Place.deref P)) csPrefix).placeRegMap.lookup
            loc'.idx.1 = none
        rw [h_dprm]
        exact h_unmap loc' h_none
      · intro idx reg'' τ'' h_look
        rw [h_stmtRun] at h_look ⊢
        rw [getPlaceInfo_emit, getPlaceInfo_emit, getPlaceInfo_emit,
          getPlaceInfo_setNextReg] at h_look
        have h_cs : getPlaceInfo csPrefix idx = some (reg'', τ'') := by
          show csPrefix.placeRegMap.lookup idx = _
          rw [← h_dprm]
          exact h_look
        refine RegisterBelow.mono ?_ (h_prb _ _ _ h_cs)
        simp only [emit]
        exact Nat.le_trans h_dregmono (Nat.le_succ _)
    · simp at h_w


/-- REGIME C0, CLOSED: constant write to a ZERO-offset projection off a
    bound local. `placeToRegChecked` returns the base's own register, so
    the fragment is a bare `CStore` and this is regime A with a wider
    `allocSize` — the projected place's bounds come from the BASE's
    layout, not from `NatL`. No `Borrow`, hence no BRIDGE 1. -/
theorem const_store_proj_zero_simulation
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {σ τ : LayoutTy} {loc : Local Γ σ} {path : PathTo σ τ}
    {binding : mirlite.Binding}
    {vs : List mirlite.MemValue} {vs' : List Val}
    (compProg : oseair.Prog) (rhs : RExpr Γ τ)
    (h_len : vs.length = blockSize τ)
    (h_rel : ListRel (MemValSim ρa ρt) vs vs')
    (h_size : vs'.length = obseq.typeSize (layoutToTyVal τ))
    (h_frag : ∀ (cs : CompilerState) (reg : Register),
      getPlaceInfo cs loc.idx.1 = some (reg, σ) →
      CheckedCompilerM.run
          (compileStmtChecked (Stmt.assign (.proj (.local loc) path) rhs)) cs
        = emit cs [Instr.CStore (layoutToTyVal τ) vs' reg])
    (h_fragval : ∀ (cs : CompilerState) (reg : Register),
      getPlaceInfo cs loc.idx.1 = some (reg, σ) →
      ∃ so, CheckedCompilerM.value
        (compileStmtChecked (Stmt.assign (.proj (.local loc) path) rhs)) cs
          = Except.ok so)
    (h_off : pathOffset path = 0)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    {stmt0 : Stmt Γ}
    (h_stmt : prog.get? s_mir.pc = some stmt0)
    (h_run0 : ∀ cs, CheckedCompilerM.run (compileStmtChecked stmt0) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.proj (.local loc) path) rhs)) cs)
    (h_val0 : ∀ cs so, CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.proj (.local loc) path) rhs)) cs
        = Except.ok so →
      ∃ so', CheckedCompilerM.value (compileStmtChecked stmt0) cs
        = Except.ok so')
    (h_env : mirlite.Env.lookup s_mir.env loc = some binding)
    (h_write : mirlite.writeResolvedPlace (τ := τ) MSB s_mir
        { addr := binding.addr + pathOffset path, tag := binding.tag,
          allocBase := binding.addr, allocSize := blockSize σ }
        vs h_len = .ok s_mir') :
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
      have h_stmtRun := (h_run0 csPrefix).trans (h_frag csPrefix reg h_pi)
      obtain ⟨stmtOutC, h_stmtOutC⟩ := h_fragval csPrefix reg h_pi
      obtain ⟨stmtOut, h_stmtOut⟩ := h_val0 csPrefix stmtOutC h_stmtOutC
      have h_code : compProg s_osea.pc
          = some (Instr.CStore (layoutToTyVal τ) vs' reg) := by
        rw [h_pc]
        refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
        · rw [h_stmtRun]; simp [emit]
        · rw [h_stmtRun]
          have h := emit_code_at_new csPrefix
            [Instr.CStore (layoutToTyVal τ) vs' reg] (k := 0) (by simp)
          simpa using h
      -- BRIDGE 2 at the projected address
      have h_entry' : PtrRegisterEntry s_osea.reg reg binding.addr
          (binding.addr + pathOffset path - binding.addr) (blockSize σ) tag := by
        rw [h_off, Nat.add_zero, Nat.sub_self]
        exact h_entry
      have h_useMut_tgt' : MSB.useMut s_osea.perms (binding.addr + pathOffset path)
          vs'.length tag = .ok p2 := by
        rw [← ListRel.length_eq h_rel]
        exact h_useMut_tgt
      have h_fit : pathOffset path + blockSize τ ≤ blockSize σ :=
        PathTo.offset_add_size_le path
      obtain ⟨h_wtp, h_sms'⟩ :=
        writeThroughPtr_sim (τ := τ)
          (resolved := { addr := binding.addr + pathOffset path, tag := binding.tag,
                         allocBase := binding.addr, allocSize := blockSize σ })
          "CStore Invalid Ptr" vs vs' h_len h_rel h_id_a h_entry' h_useMut_tgt' h_sms
          (by simp [h_off])
          (fun k hk => by
            have hk' : k < blockSize σ := by
              rw [h_len] at hk
              omega
            obtain ⟨a', ha'⟩ := h_dom k hk'
            have h_eq := h_id_a _ _ ha'
            show ρa (binding.addr + pathOffset path + k) = _
            rw [h_off, Nat.add_zero]
            grind)
          h_write
      have h_run := runN_CStore_step compProg s_osea _
        (layoutToTyVal τ) vs' reg h_code h_size h_wtp
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

/-- Zero-offset projected constant write — the `constInit` instance. -/
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
      CompilerInv cs0 prog ρa ρt s_mir' s_osea' :=
  const_store_proj_zero_simulation
    (vs := [mirlite.MemValue.word v]) (vs' := [Val.Dat v])
    compProg (.constInit v) rfl (by exact ⟨rfl, trivial⟩) rfl
    (fun cs reg h => by
      obtain ⟨h_brun, baseOut, h_bval, h_bres⟩ :=
        placeToRegChecked_local_existing (kind := RefKind.Mut) h
      exact compileStmt_proj_zero_run (cs := cs) (baseOut := baseOut)
        (fun _ _ _ hh => by cases hh) v h_off
        (ensurePlaceRoot_run_eq_of_mapped ⟨reg, σ, h⟩) h_brun h_bval h_bres)
    (fun cs reg h => by
      have h_mapped : PlaceInputsMapped cs (Place.proj (Place.local loc) path) :=
        ⟨reg, σ, h⟩
      obtain ⟨dstOut, h_dstOut⟩ :=
        placeToRegChecked_ok_of_placeInputsMapped (cs := cs)
          (kind := RefKind.Mut) (p := Place.proj (Place.local loc) path) h_mapped
      exact ⟨{ result := (), evidence := StmtEvidence.assignPlace (.proj (.local loc) path) (.constInit v) dstOut.result dstOut.evidence (RExprToEvidence.constInit v) },
        by simp [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked,
          h_dstOut, ensurePlaceRoot_run_eq_of_mapped h_mapped]⟩)
    h_off h_comp h_inv h_stmt h_run0 h_val0 h_env h_write

/-- Zero-offset projected undef-fill — the `uninit` instance. -/
theorem uninit_proj_zero_simulation
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {σ τ : LayoutTy} {loc : Local Γ σ} {path : PathTo σ τ}
    {binding : mirlite.Binding}
    (compProg : oseair.Prog)
    (h_off : pathOffset path = 0)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    {stmt0 : Stmt Γ}
    (h_stmt : prog.get? s_mir.pc = some stmt0)
    (h_run0 : ∀ cs, CheckedCompilerM.run (compileStmtChecked stmt0) cs
      = CheckedCompilerM.run
          (compileStmtChecked (Stmt.assign (.proj (.local loc) path) .uninit)) cs)
    (h_val0 : ∀ cs so, CheckedCompilerM.value
        (compileStmtChecked (Stmt.assign (.proj (.local loc) path) .uninit)) cs
        = Except.ok so →
      ∃ so', CheckedCompilerM.value (compileStmtChecked stmt0) cs
        = Except.ok so')
    (h_env : mirlite.Env.lookup s_mir.env loc = some binding)
    (h_write : mirlite.writeResolvedPlace (τ := τ) MSB s_mir
        { addr := binding.addr + pathOffset path, tag := binding.tag,
          allocBase := binding.addr, allocSize := blockSize σ }
        (List.replicate (blockSize τ) mirlite.MemValue.undef)
        List.length_replicate = .ok s_mir') :
    ∃ (s_osea' : oseair.State MSB) (n : Nat),
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa ρt s_mir' s_osea' :=
  const_store_proj_zero_simulation
    (vs := List.replicate (blockSize τ) mirlite.MemValue.undef)
    (vs' := List.replicate (blockSize τ) Val.Undef)
    compProg .uninit List.length_replicate (ListRel_replicate_undef ρa ρt _ _)
    (List.length_replicate.trans (blockSize_eq_typeSize τ))
    (fun cs reg h => by
      obtain ⟨h_brun, baseOut, h_bval, h_bres⟩ :=
        placeToRegChecked_local_existing (kind := RefKind.Mut) h
      exact compileStmt_proj_zero_uninit_run (cs := cs) (baseOut := baseOut)
        (fun _ _ _ hh => by cases hh) h_off
        (ensurePlaceRoot_run_eq_of_mapped ⟨reg, σ, h⟩) h_brun h_bval h_bres)
    (fun cs reg h => by
      have h_mapped : PlaceInputsMapped cs (Place.proj (Place.local loc) path) :=
        ⟨reg, σ, h⟩
      obtain ⟨dstOut, h_dstOut⟩ :=
        placeToRegChecked_ok_of_placeInputsMapped (cs := cs)
          (kind := RefKind.Mut) (p := Place.proj (Place.local loc) path) h_mapped
      exact ⟨{ result := (), evidence := StmtEvidence.assignPlace (.proj (.local loc) path) .uninit dstOut.result dstOut.evidence RExprToEvidence.uninit },
        by simp [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked,
          h_dstOut, ensurePlaceRoot_run_eq_of_mapped h_mapped]⟩)
    h_off h_comp h_inv h_stmt h_run0 h_val0 h_env h_write

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
theorem const_store_proj_offset_simulation
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {σ τ : LayoutTy} {loc : Local Γ σ} {path : PathTo σ τ}
    {binding : mirlite.Binding}
    {vs : List mirlite.MemValue} {vs' : List Val}
    (compProg : oseair.Prog) (rhs : RExpr Γ τ)
    (h_len : vs.length = blockSize τ)
    (h_rel : ListRel (MemValSim ρa ρt) vs vs')
    (h_size : vs'.length = obseq.typeSize (layoutToTyVal τ))
    (h_frag : ∀ (cs : CompilerState) (reg : Register),
      getPlaceInfo cs loc.idx.1 = some (reg, σ) →
      CheckedCompilerM.run
          (compileStmtChecked (Stmt.assign (.proj (.local loc) path) rhs)) cs
        = emit (emit (emit { cs with nextReg := cs.nextReg + 1 }
            [Instr.Assgn (Register.R cs.nextReg)
              (borrowRhs RefKind.Mut (blockSize τ) reg (pathOffset path))])
            [Instr.CStore (layoutToTyVal τ) vs' (Register.R cs.nextReg)])
            [Instr.Die (Register.R cs.nextReg) (blockSize τ)])
    (h_fragval : ∀ (cs : CompilerState) (reg : Register),
      getPlaceInfo cs loc.idx.1 = some (reg, σ) →
      ∃ so, CheckedCompilerM.value
        (compileStmtChecked (Stmt.assign (.proj (.local loc) path) rhs)) cs
          = Except.ok so)
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
            (Stmt.assign (.proj (.local loc) path) rhs)) cs)
    (h_val0 : ∀ cs so, CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.proj (.local loc) path) rhs)) cs
        = Except.ok so →
      ∃ so', CheckedCompilerM.value (compileStmtChecked stmt0) cs
        = Except.ok so')
    (h_env : mirlite.Env.lookup s_mir.env loc = some binding)
    (h_write : mirlite.writeResolvedPlace (τ := τ) MSB s_mir
        { addr := binding.addr + pathOffset path, tag := binding.tag,
          allocBase := binding.addr, allocSize := blockSize σ }
        vs h_len = .ok s_mir') :
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
        grind
      subst h_qAcc
      -- the fragment: Borrow; CStore; Die
      have h_stmtRun := (h_run0 csPrefix).trans (h_frag csPrefix reg h_pi)
      obtain ⟨stmtOutC, h_stmtOutC⟩ := h_fragval csPrefix reg h_pi
      obtain ⟨stmtOut, h_stmtOut⟩ := h_val0 csPrefix stmtOutC h_stmtOutC
      have h_len3 : ((emit (emit (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
          [Instr.Assgn (Register.R csPrefix.nextReg)
            (borrowRhs RefKind.Mut (blockSize τ) reg (pathOffset path))])
          [Instr.CStore (layoutToTyVal τ) vs' (Register.R csPrefix.nextReg)])
          [Instr.Die (Register.R csPrefix.nextReg) (blockSize τ)])).nextLabel
          = csPrefix.nextLabel + 3 := by
        simp only [emit, List.length_cons, List.length_nil]
      have h_code1 : compProg s_osea.pc
          = some (Instr.Assgn (Register.R csPrefix.nextReg)
              (borrowRhs RefKind.Mut (blockSize τ) reg (pathOffset path))) := by
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
              (borrowRhs RefKind.Mut (blockSize τ) reg (pathOffset path))]
            (k := 0) (by simp)
          simpa using h
      have h_code2 : compProg (s_osea.pc + 1)
          = some (Instr.CStore (layoutToTyVal τ) vs'
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
                (borrowRhs RefKind.Mut (blockSize τ) reg (pathOffset path))])
            [Instr.CStore (layoutToTyVal τ) vs' (Register.R csPrefix.nextReg)]
            (k := 0) (by simp)
          simpa [emit] using h
      have h_code3 : compProg (s_osea.pc + 1 + 1)
          = some (Instr.Die (Register.R csPrefix.nextReg)
              (blockSize τ)) := by
        rw [h_pc]
        refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
        · rw [h_stmtRun, h_len3]; omega
        · rw [h_stmtRun]
          have h := emit_code_at_new
            (emit (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
              [Instr.Assgn (Register.R csPrefix.nextReg)
                (borrowRhs RefKind.Mut (blockSize τ) reg (pathOffset path))])
              [Instr.CStore (layoutToTyVal τ) vs' (Register.R csPrefix.nextReg)])
            [Instr.Die (Register.R csPrefix.nextReg) (blockSize τ)]
            (k := 0) (by simp)
          simpa [emit] using h
      -- §execute: Borrow, then the store through the fresh tag, then Die
      have h_ref_tgt' : MSB.ref s_osea.perms (binding.addr + 0 + pathOffset path)
          (blockSize τ) tag RefKind.Mut false []
          = .ok (q1, s_osea.perms.NextTag) := by
        rw [← h_len]
        simpa using h_ref_tgt
      have h_bnd := Nat.not_lt.mp h_nb
      have h_off_lt : ∀ k, k < vs.length → pathOffset path + k < blockSize σ := by
        intro k hk
        omega
      have h_le1 : binding.addr + 0 + pathOffset path + blockSize τ
          ≤ binding.addr + blockSize σ := by
        rw [Nat.add_zero, ← h_len]
        exact h_bnd
      have h_run1 := runN_Assgn_Borrow_step compProg s_osea
        (Register.R csPrefix.nextReg) reg RefKind.Mut false []
        (blockSize τ) (pathOffset path)
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
        writeThroughPtr_sim (τ := τ)
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
          "CStore Invalid Ptr" vs vs' h_len h_rel h_id_a h_entry1
          (by rw [← ListRel.length_eq h_rel]; simpa using h_wr1) h_sms
          (by simp)
          (fun k hk => by
            obtain ⟨a', ha'⟩ := h_dom (pathOffset path + k) (h_off_lt k hk)
            have h_id := h_id_a _ _ ha'
            show ρa (binding.addr + pathOffset path + k) = _
            grind)
          h_write
      have h_run2 := runN_CStore_step compProg _ _
        (layoutToTyVal τ) vs' (Register.R csPrefix.nextReg) h_code2 h_size h_wtp
      have h_run3 := runN_Die_step compProg
        { s_osea with
            perms := q2,
            reg := oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
              (obseq.TyVal.PTy,
                [Val.Ptr binding.addr (0 + pathOffset path) (blockSize σ)
                  s_osea.perms.NextTag]),
            mem := oseair.writeWordSeq s_osea.mem (binding.addr + pathOffset path)
              vs',
            pc := s_osea.pc + 1 + 1 }
        (Register.R csPrefix.nextReg) (blockSize τ)
        h_code3 (RegMap.lookup_insert_self _ _ _)
          (by rw [← h_len]; simpa using h_die1)
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

/-- Nonzero-offset projected constant write — the `constInit` instance. -/
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
    {stmt0 : Stmt Γ}
    (h_stmt : prog.get? s_mir.pc = some stmt0)
    (h_run0 : ∀ cs, CheckedCompilerM.run (compileStmtChecked stmt0) cs
      = CheckedCompilerM.run
          (compileStmtChecked (Stmt.assign (.proj (.local loc) path) (.constInit v))) cs)
    (h_val0 : ∀ cs so, CheckedCompilerM.value
        (compileStmtChecked (Stmt.assign (.proj (.local loc) path) (.constInit v))) cs
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
      CompilerInv cs0 prog ρa ρt s_mir' s_osea' :=
  const_store_proj_offset_simulation
    (vs := [mirlite.MemValue.word v]) (vs' := [Val.Dat v])
    compProg (.constInit v) rfl (by exact ⟨rfl, trivial⟩) rfl
    (fun cs reg h => by
      obtain ⟨h_brun, baseOut, h_bval, h_bres⟩ :=
        placeToRegChecked_local_existing (kind := RefKind.Mut) h
      exact compileStmt_proj_offset_run (cs := cs) (baseOut := baseOut)
        (fun _ _ _ hh => by cases hh) v h_off
        (ensurePlaceRoot_run_eq_of_mapped ⟨reg, _, h⟩) h_brun h_bval h_bres)
    (fun cs reg h => by
      have h_mapped : PlaceInputsMapped cs (Place.proj (Place.local loc) path) :=
        ⟨reg, _, h⟩
      obtain ⟨dstOut, h_dstOut⟩ :=
        placeToRegChecked_ok_of_placeInputsMapped (cs := cs)
          (kind := RefKind.Mut) (p := Place.proj (Place.local loc) path) h_mapped
      exact ⟨{ result := (), evidence := StmtEvidence.assignPlace (.proj (.local loc) path) (.constInit v) dstOut.result dstOut.evidence (RExprToEvidence.constInit v) },
        by simp [compileStmtChecked, compileRExprPreChecked,
          h_dstOut, ensurePlaceRoot_run_eq_of_mapped h_mapped]⟩)
    h_off h_comp h_inv h_stmt h_run0 h_val0 h_env h_write

/-- Nonzero-offset projected undef-fill — the `uninit` instance; the projection's own `Borrow(Mut)`/`Die` still collapses by BRIDGE 1. -/
theorem uninit_proj_offset_simulation
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {σ τ : LayoutTy} {loc : Local Γ σ} {path : PathTo σ τ}
    {binding : mirlite.Binding}
    (compProg : oseair.Prog)
    -- (no value operand)
    (h_off : pathOffset path ≠ 0)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    {stmt0 : Stmt Γ}
    (h_stmt : prog.get? s_mir.pc = some stmt0)
    (h_run0 : ∀ cs, CheckedCompilerM.run (compileStmtChecked stmt0) cs
      = CheckedCompilerM.run
          (compileStmtChecked (Stmt.assign (.proj (.local loc) path) .uninit)) cs)
    (h_val0 : ∀ cs so, CheckedCompilerM.value
        (compileStmtChecked (Stmt.assign (.proj (.local loc) path) .uninit)) cs
        = Except.ok so →
      ∃ so', CheckedCompilerM.value (compileStmtChecked stmt0) cs
        = Except.ok so')
    (h_env : mirlite.Env.lookup s_mir.env loc = some binding)
    (h_write : mirlite.writeResolvedPlace (τ := τ) MSB s_mir
        { addr := binding.addr + pathOffset path, tag := binding.tag,
          allocBase := binding.addr, allocSize := blockSize σ }
        (List.replicate (blockSize τ) mirlite.MemValue.undef)
        List.length_replicate = .ok s_mir') :
    ∃ (s_osea' : oseair.State MSB) (n : Nat),
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa ρt s_mir' s_osea' :=
  const_store_proj_offset_simulation
    (vs := List.replicate (blockSize τ) mirlite.MemValue.undef) (vs' := List.replicate (blockSize τ) Val.Undef)
    compProg .uninit List.length_replicate (ListRel_replicate_undef ρa ρt _ _) (List.length_replicate.trans (blockSize_eq_typeSize τ))
    (fun cs reg h => by
      obtain ⟨h_brun, baseOut, h_bval, h_bres⟩ :=
        placeToRegChecked_local_existing (kind := RefKind.Mut) h
      exact compileStmt_proj_offset_uninit_run (cs := cs) (baseOut := baseOut)
        (fun _ _ _ hh => by cases hh) h_off
        (ensurePlaceRoot_run_eq_of_mapped ⟨reg, _, h⟩) h_brun h_bval h_bres)
    (fun cs reg h => by
      have h_mapped : PlaceInputsMapped cs (Place.proj (Place.local loc) path) :=
        ⟨reg, _, h⟩
      obtain ⟨dstOut, h_dstOut⟩ :=
        placeToRegChecked_ok_of_placeInputsMapped (cs := cs)
          (kind := RefKind.Mut) (p := Place.proj (Place.local loc) path) h_mapped
      exact ⟨{ result := (), evidence := StmtEvidence.assignPlace (.proj (.local loc) path) .uninit dstOut.result dstOut.evidence RExprToEvidence.uninit },
        by simp [compileStmtChecked, compileRExprPreChecked,
          h_dstOut, ensurePlaceRoot_run_eq_of_mapped h_mapped]⟩)
    h_off h_comp h_inv h_stmt h_run0 h_val0 h_env h_write

/-! ## The FRESH projected-destination fragments (regime B-proj): the
    root `Alloc` that `ensurePlaceRoot` emits for an unmapped root,
    then the C0/C1 shapes over the fresh register. -/

theorem compileStmt_proj_fresh_zero_run
    {Γ : Ctx} {σ : LayoutTy} {loc : Local Γ σ}
    {path : PathTo σ obseq.LayoutTy.NatL} {cs : CompilerState}
    (v : Word)
    (h_off : pathOffset path = 0)
    (h : getPlaceInfo cs loc.idx.1 = none) :
    CheckedCompilerM.run
        (compileStmtChecked (Stmt.assign (.proj (.local loc) path) (.constInit v))) cs
      = emit
          (setPlaceInfo
            (emit { cs with nextReg := cs.nextReg + 1 }
              [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
            loc.idx.1 (Register.R cs.nextReg, σ))
          [Instr.CStore obseq.TyVal.NatTy [Val.Dat v] (Register.R cs.nextReg)] := by
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_fresh (loc := loc) h
  have h_pi : getPlaceInfo
      (setPlaceInfo
        (emit { cs with nextReg := cs.nextReg + 1 }
          [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
        loc.idx.1 (Register.R cs.nextReg, σ))
      loc.idx.1 = some (Register.R cs.nextReg, σ) :=
    getPlaceInfo_setPlaceInfo_self _ _ _
  have h_proj_eq := placeToRegChecked_proj_root_eq (Γ := Γ) (kind := RefKind.Mut)
    (base := .local loc) path (fun _ _ _ h => by cases h)
  have h_root : CompilerM.run
      (ensurePlaceRoot (Place.proj (Place.local loc) path)) cs
      = setPlaceInfo
          (emit { cs with nextReg := cs.nextReg + 1 }
            [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
          loc.idx.1 (Register.R cs.nextReg, σ) := by
    show CompilerM.run (do let _ ← ensureLocalRegE loc; pure ()) cs = _
    simp [CompilerM.run_bind, CompilerM.run_pure, h_run]
  obtain ⟨h_brun, baseOut, h_bval, h_bres⟩ :=
    placeToRegChecked_local_existing (kind := RefKind.Mut) h_pi
  simp only [compileStmtChecked, h_proj_eq, compileRExprToChecked, compileRExprPreChecked,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
    h_root, h_brun, h_bval, h_off, dif_pos]
  simp [CompilerM.run, CompilerM.value, emitM, cleanupInstrs, h_bres, emit_nil]

theorem compileStmt_proj_fresh_offset_run
    {Γ : Ctx} {σ : LayoutTy} {loc : Local Γ σ}
    {path : PathTo σ obseq.LayoutTy.NatL} {cs : CompilerState}
    (v : Word)
    (h_off : pathOffset path ≠ 0)
    (h : getPlaceInfo cs loc.idx.1 = none) :
    CheckedCompilerM.run
        (compileStmtChecked (Stmt.assign (.proj (.local loc) path) (.constInit v))) cs
      = emit (emit (emit
          { (setPlaceInfo
              (emit { cs with nextReg := cs.nextReg + 1 }
                [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
              loc.idx.1 (Register.R cs.nextReg, σ)) with
              nextReg := cs.nextReg + 1 + 1 }
          [Instr.Assgn (Register.R (cs.nextReg + 1))
            (borrowRhs RefKind.Mut (blockSize obseq.LayoutTy.NatL)
              (Register.R cs.nextReg) (pathOffset path))])
          [Instr.CStore obseq.TyVal.NatTy [Val.Dat v] (Register.R (cs.nextReg + 1))])
          [Instr.Die (Register.R (cs.nextReg + 1)) (blockSize obseq.LayoutTy.NatL)] := by
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_fresh (loc := loc) h
  have h_pi : getPlaceInfo
      (setPlaceInfo
        (emit { cs with nextReg := cs.nextReg + 1 }
          [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
        loc.idx.1 (Register.R cs.nextReg, σ))
      loc.idx.1 = some (Register.R cs.nextReg, σ) :=
    getPlaceInfo_setPlaceInfo_self _ _ _
  have h_proj_eq := placeToRegChecked_proj_root_eq (Γ := Γ) (kind := RefKind.Mut)
    (base := .local loc) path (fun _ _ _ h => by cases h)
  have h_root : CompilerM.run
      (ensurePlaceRoot (Place.proj (Place.local loc) path)) cs
      = setPlaceInfo
          (emit { cs with nextReg := cs.nextReg + 1 }
            [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
          loc.idx.1 (Register.R cs.nextReg, σ) := by
    show CompilerM.run (do let _ ← ensureLocalRegE loc; pure ()) cs = _
    simp [CompilerM.run_bind, CompilerM.run_pure, h_run]
  obtain ⟨h_brun, baseOut, h_bval, h_bres⟩ :=
    placeToRegChecked_local_existing (kind := RefKind.Mut) h_pi
  simp only [compileStmtChecked, h_proj_eq, compileRExprToChecked, compileRExprPreChecked,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
    h_root, h_brun, h_bval]
  simp [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM,
    cleanupInstrs, h_bres, emit_nil, h_off, borrowRhs]
  rfl

/-- The fresh projected statement lowers (either offset). -/
theorem compileStmt_proj_fresh_value
    {Γ : Ctx} {σ : LayoutTy} {loc : Local Γ σ}
    {path : PathTo σ obseq.LayoutTy.NatL} {cs : CompilerState}
    (v : Word)
    (h : getPlaceInfo cs loc.idx.1 = none) :
    ∃ so, CheckedCompilerM.value
      (compileStmtChecked (Stmt.assign (.proj (.local loc) path) (.constInit v))) cs
      = Except.ok so := by
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_fresh (loc := loc) h
  have h_pi : getPlaceInfo
      (setPlaceInfo
        (emit { cs with nextReg := cs.nextReg + 1 }
          [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
        loc.idx.1 (Register.R cs.nextReg, σ))
      loc.idx.1 = some (Register.R cs.nextReg, σ) :=
    getPlaceInfo_setPlaceInfo_self _ _ _
  have h_proj_eq := placeToRegChecked_proj_root_eq (Γ := Γ) (kind := RefKind.Mut)
    (base := .local loc) path (fun _ _ _ h => by cases h)
  have h_root : CompilerM.run
      (ensurePlaceRoot (Place.proj (Place.local loc) path)) cs
      = setPlaceInfo
          (emit { cs with nextReg := cs.nextReg + 1 }
            [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
          loc.idx.1 (Register.R cs.nextReg, σ) := by
    show CompilerM.run (do let _ ← ensureLocalRegE loc; pure ()) cs = _
    simp [CompilerM.run_bind, CompilerM.run_pure, h_run]
  obtain ⟨h_brun, baseOut, h_bval, h_bres⟩ :=
    placeToRegChecked_local_existing (kind := RefKind.Mut) h_pi
  simp only [compileStmtChecked, h_proj_eq, compileRExprToChecked, compileRExprPreChecked,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
    h_root, h_brun, h_bval]
  by_cases h_off : pathOffset path = 0
  · simp only [h_off, dif_pos]
    exact ⟨_, rfl⟩
  · simp only [dif_neg h_off,
      CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
      CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
      CheckedCompilerM.run_pure, CheckedCompilerM.value_pure]
    exact ⟨_, rfl⟩

/-- REGIME B-proj: constant write to a projection over a FRESH root —
    `s.f := v` with `s` unbound. mirlite's `preparePlaceAssign`
    allocates the whole σ-sized root; the compiled fragment is the root
    `Alloc` from `ensurePlaceRoot`, then the C0/C1 shape over the fresh
    register. Both renames extend: ρa by the IDENTITY over the ENTIRE
    fresh block (`extendIdRange` — the block-domain conjunct and the
    projected write need every cell, not just the base), ρt at the
    minted root tag. -/
theorem const_write_proj_fresh_simulation
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_pre s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {σ : LayoutTy} {loc : Local Γ σ} {path : PathTo σ obseq.LayoutTy.NatL}
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
            (Stmt.assign (.proj (.local loc) path) (.constInit v))) cs)
    (h_val0 : ∀ cs so, CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.proj (.local loc) path) (.constInit v))) cs
        = Except.ok so →
      ∃ so', CheckedCompilerM.value (compileStmtChecked stmt0) cs
        = Except.ok so')
    (h_env : mirlite.Env.lookup s_mir.env loc = none)
    (h_prep : mirlite.preparePlaceAssign MSB s_mir (.proj (.local loc) path) = .ok s_pre)
    (h_res  : mirlite.resolvePlaceAcc MSB s_pre (.proj (.local loc) path)
      = .ok (resolved, permsD))
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
  have h_pi_none : getPlaceInfo csPrefix loc.idx.1 = none := h_unmap loc h_env
  -- §1 invert mirlite's prepare: the projected place does not resolve
  -- (its root is unbound), so `allocateRoot` allocated the σ-sized root
  simp only [mirlite.preparePlaceAssign, mirlite.resolvePlace?, h_env,
    mirlite.allocateRoot, mirlite.allocateBase, mirlite.allocate] at h_prep
  cases h_own_src : MSB.own s_mir.perms s_mir.mem.addrStart (blockSize σ) with
  | error e => rw [h_own_src] at h_prep; simp at h_prep
  | ok pr =>
  obtain ⟨permsOwned, tagS⟩ := pr
  rw [h_own_src] at h_prep
  injection h_prep with h_pre
  subst h_pre
  -- §2 resolution of the projected place over the now-bound root
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
  have h_incr_a :=
    AddrRenameIncr.extendIdRange h_id_a s_mir.mem.addrStart (blockSize σ)
  have h_id_a' :=
    IdentityOnDomain.extendIdRange h_id_a s_mir.mem.addrStart (blockSize σ)
  have h_ra_dom : ∀ k, k < blockSize σ →
      (ρa.extendIdRange s_mir.mem.addrStart (blockSize σ))
        (s_mir.mem.addrStart + k) = some (s_mir.mem.addrStart + k) :=
    fun k hk => AddrRenameMap.extendIdRange_mem (Nat.le_add_right _ _)
      (Nat.add_lt_add_left hk _)
  have h_rt_new : (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag)
      s_mir.perms.NextTag = some s_osea.perms.NextTag :=
    TagRenameMap.extend_self _ _ _
  have h0 : wildcardTag < s_mir.perms.NextTag := (h_tbd _ _ h_wf_t.2).1
  have h_nw : (s_mir.perms.NextTag == wildcardTag) = false := by grind
  -- the NatL leaf of the path fits inside the root's block
  have h_fit : pathOffset path + 1 ≤ blockSize σ := by
    have h := PathTo.offset_add_size_le path
    simpa [blockSize, obseq.layoutSize] using h
  -- §4 the statement lowers
  obtain ⟨stmtOutC, h_stmtOutC⟩ :=
    compileStmt_proj_fresh_value (loc := loc) (path := path) v h_pi_none
  obtain ⟨stmtOut, h_stmtOut⟩ := h_val0 csPrefix stmtOutC h_stmtOutC
  have h_sz : obseq.typeSize (layoutToTyVal σ) = blockSize σ :=
    obseq.typeSize_layoutToTyVal _
  have h_own_tgt' : MSB.own s_osea.perms s_osea.mem.addrStart
      (obseq.typeSize (layoutToTyVal σ))
      = .ok (tgtPerms, s_osea.perms.NextTag) := by
    rw [h_sz, h_addr_eq]
    exact h_own_tgt
  by_cases h_off : pathOffset path = 0
  · -- ZERO offset: `[Alloc; CStore]`, the write at the block base
    have h_stmtRun := (h_run0 csPrefix).trans
      (compileStmt_proj_fresh_zero_run (cs := csPrefix) v h_off h_pi_none)
    -- normalize the projected resolution onto the block base
    have h_o' : PathTo.offset path = 0 := h_off
    have h_req : ({ addr := s_mir.mem.addrStart + PathTo.offset path,
                    tag := s_mir.perms.NextTag,
                    allocBase := s_mir.mem.addrStart,
                    allocSize := blockSize σ } : mirlite.PlaceRes)
        = { addr := s_mir.mem.addrStart, tag := s_mir.perms.NextTag,
            allocBase := s_mir.mem.addrStart, allocSize := blockSize σ } := by
      simp [h_o']
    rw [h_req] at h_write
    -- §5 the two instructions
    have h_code1 : compProg s_osea.pc
        = some (Instr.Assgn (Register.R csPrefix.nextReg)
            (Rhs.Alloc (layoutToTyVal σ))) := by
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
            (Rhs.Alloc (layoutToTyVal σ))] (k := 0) (by simp)
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
              (Rhs.Alloc (layoutToTyVal σ))])
            loc.idx.1 (Register.R csPrefix.nextReg, σ))
          [Instr.CStore obseq.TyVal.NatTy [Val.Dat v] (Register.R csPrefix.nextReg)]
          (k := 0) (by simp)
        simpa [emit, setPlaceInfo] using h
    -- §6 execute the `Alloc`
    have h_run1 := runN_Assgn_Alloc_step compProg s_osea
      (Register.R csPrefix.nextReg) (layoutToTyVal σ)
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
                (obseq.typeSize (layoutToTyVal σ))
                s_osea.perms.NextTag]))
            (Register.R csPrefix.nextReg) s_mir.mem.addrStart
            (s_mir.mem.addrStart - s_mir.mem.addrStart)
            (blockSize σ) s_osea.perms.NextTag := by
          rw [Nat.sub_self, ← h_addr_eq, ← h_sz]
          exact RegMap.lookup_insert_self _ _ _
        obtain ⟨h_wtp, h_sms'⟩ :=
          writeThroughPtr_sim (τ := obseq.LayoutTy.NatL)
            (s_osea := { s_osea with
              mem := (oseair.allocate s_osea.mem
                (obseq.typeSize (layoutToTyVal σ))).2,
              perms := tgtPerms,
              reg := oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
                (obseq.TyVal.PTy, [Val.Ptr s_osea.mem.addrStart 0
                  (obseq.typeSize (layoutToTyVal σ))
                  s_osea.perms.NextTag]),
              pc := s_osea.pc + 1 })
            (resolved := { addr := s_mir.mem.addrStart, tag := s_mir.perms.NextTag,
                           allocBase := s_mir.mem.addrStart,
                           allocSize := blockSize σ })
            "CStore Invalid Ptr" [mirlite.MemValue.word v] [Val.Dat v] rfl
            ⟨rfl, trivial⟩ h_id_a' h_entry1 h_useMut_tgt
            (by exact SourceMemSim.rename_mono h_incr_a h_incr_t h_sms) (Nat.le_refl _)
            (fun k hk => by
              simp [Nat.lt_one_iff] at hk
              subst hk
              simpa using h_ra_dom 0 (by omega))
            h_write
        have h_run2 := runN_CStore_step compProg _ _
          obseq.TyVal.NatTy [Val.Dat v] (Register.R csPrefix.nextReg)
          h_code2 rfl h_wtp
        have h_run := (oseair_runN_add 1 1 s_osea compProg _ h_run1).trans h_run2
        -- §8 rebuild the invariant under both extended renames
        refine ⟨_, _, _, 1 + 1, h_incr_a, h_incr_t, h_run, ?_⟩
        refine ⟨CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix,
          ⟨prefixCompileState_succ h_csAt h_stmt h_stmtOut, ?_⟩, ?_, h_sms', h_psim2,
          h_id_a', h_wf_t', ?_, ?_, ?_, ?_⟩
        · show s_osea.pc + 1 + 1 = _
          rw [h_pc, h_stmtRun]
          simp [emit, setPlaceInfo]
        · intro τ' loc' binding' h_env'
          by_cases h_idx : loc'.idx = loc.idx
          · have h_ty : τ' = σ := by
              rw [← loc'.hTy, h_idx, loc.hTy]
            subst h_ty
            have h_b : binding' = { addr := s_mir.mem.addrStart,
                                    tag := s_mir.perms.NextTag } := by
              grind [mirlite.Env.lookup, mirlite.Env.set]
            subst h_b
            refine ⟨Register.R csPrefix.nextReg, s_mir.mem.addrStart,
              s_osea.perms.NextTag, ?_, ?_, ?_, h_rt_new, h_nw, ?_⟩
            · rw [h_stmtRun, getPlaceInfo_emit,
                show loc'.idx.1 = loc.idx.1 from congrArg Fin.val h_idx]
              exact getPlaceInfo_setPlaceInfo_self _ _ _
            · show oseair.RegMap.lookup _ _ = _
              rw [← h_addr_eq, ← h_sz]
              exact RegMap.lookup_insert_self _ _ _
            · simpa using h_ra_dom 0 (by omega)
            · intro k hk
              exact ⟨s_mir.mem.addrStart + k, h_ra_dom k hk⟩
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
        · show TagRenameBounded _ perms'.NextTag p2.NextTag
          rw [sb_write_NextTag h_useMut_src, sb_write_NextTag h_useMut_tgt]
          exact h_tbd'
        · simp only [AllocLockstep, mirlite_writeWordSeq_addrStart,
            oseair_writeWordSeq_addrStart, mirlite.allocate, oseair.allocate]
          rw [h_addr_eq, h_sz]
        · intro τ' loc' h_none
          by_cases h_idx : loc'.idx = loc.idx
          · exfalso
            grind [mirlite.Env.lookup, mirlite.Env.set]
          · have h_idxv : loc'.idx.1 ≠ loc.idx.1 := fun h => h_idx (Fin.ext h)
            have h_none' : mirlite.Env.lookup s_mir.env loc' = none := by
              grind [mirlite.Env.lookup, mirlite.Env.set]
            rw [h_stmtRun, getPlaceInfo_emit,
              getPlaceInfo_setPlaceInfo_ne _ h_idxv]
            exact h_unmap loc' h_none'
        · intro idx reg τ'' h_look
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
  · -- NONZERO offset: `[Alloc; Borrow(Mut); CStore; Die]` — the C1
    -- endgame (BRIDGE 1) over the fresh block
    have h_stmtRun := (h_run0 csPrefix).trans
      (compileStmt_proj_fresh_offset_run (cs := csPrefix) v h_off h_pi_none)
    -- §5' the four instructions
    have h_code1 : compProg s_osea.pc
        = some (Instr.Assgn (Register.R csPrefix.nextReg)
            (Rhs.Alloc (layoutToTyVal σ))) := by
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
        rw [emit_code_lt_nextLabel _ _ (by
          simp only [emit, setPlaceInfo, List.length_cons, List.length_nil]; omega)]
        show (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } _).code _ = _
        have h := emit_code_at_new { csPrefix with nextReg := csPrefix.nextReg + 1 }
          [Instr.Assgn (Register.R csPrefix.nextReg)
            (Rhs.Alloc (layoutToTyVal σ))] (k := 0) (by simp)
        simpa using h
    have h_code2 : compProg (s_osea.pc + 1)
        = some (Instr.Assgn (Register.R (csPrefix.nextReg + 1))
            (borrowRhs RefKind.Mut (blockSize obseq.LayoutTy.NatL)
              (Register.R csPrefix.nextReg) (pathOffset path))) := by
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
        have h := emit_code_at_new
          { (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
              [Instr.Assgn (Register.R csPrefix.nextReg)
                (Rhs.Alloc (layoutToTyVal σ))])
              loc.idx.1 (Register.R csPrefix.nextReg, σ)) with
              nextReg := csPrefix.nextReg + 1 + 1 }
          [Instr.Assgn (Register.R (csPrefix.nextReg + 1))
            (borrowRhs RefKind.Mut (blockSize obseq.LayoutTy.NatL)
              (Register.R csPrefix.nextReg) (pathOffset path))]
          (k := 0) (by simp)
        simpa [emit, setPlaceInfo] using h
    have h_code3 : compProg (s_osea.pc + 1 + 1)
        = some (Instr.CStore obseq.TyVal.NatTy [Val.Dat v]
            (Register.R (csPrefix.nextReg + 1))) := by
      rw [h_pc]
      refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
      · rw [h_stmtRun]
        simp only [emit, setPlaceInfo, List.length_cons, List.length_nil]
        omega
      · rw [h_stmtRun]
        rw [emit_code_lt_nextLabel _ _ (by
          simp only [emit, setPlaceInfo, List.length_cons, List.length_nil]; omega)]
        have h := emit_code_at_new
          (emit { (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
              [Instr.Assgn (Register.R csPrefix.nextReg)
                (Rhs.Alloc (layoutToTyVal σ))])
              loc.idx.1 (Register.R csPrefix.nextReg, σ)) with
              nextReg := csPrefix.nextReg + 1 + 1 }
            [Instr.Assgn (Register.R (csPrefix.nextReg + 1))
              (borrowRhs RefKind.Mut (blockSize obseq.LayoutTy.NatL)
                (Register.R csPrefix.nextReg) (pathOffset path))])
          [Instr.CStore obseq.TyVal.NatTy [Val.Dat v]
            (Register.R (csPrefix.nextReg + 1))]
          (k := 0) (by simp)
        simpa [emit, setPlaceInfo] using h
    have h_code4 : compProg (s_osea.pc + 1 + 1 + 1)
        = some (Instr.Die (Register.R (csPrefix.nextReg + 1))
            (blockSize obseq.LayoutTy.NatL)) := by
      rw [h_pc]
      refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
      · rw [h_stmtRun]
        simp only [emit, setPlaceInfo, List.length_cons, List.length_nil]
        omega
      · rw [h_stmtRun]
        have h := emit_code_at_new
          (emit (emit { (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
              [Instr.Assgn (Register.R csPrefix.nextReg)
                (Rhs.Alloc (layoutToTyVal σ))])
              loc.idx.1 (Register.R csPrefix.nextReg, σ)) with
              nextReg := csPrefix.nextReg + 1 + 1 }
            [Instr.Assgn (Register.R (csPrefix.nextReg + 1))
              (borrowRhs RefKind.Mut (blockSize obseq.LayoutTy.NatL)
                (Register.R csPrefix.nextReg) (pathOffset path))])
            [Instr.CStore obseq.TyVal.NatTy [Val.Dat v]
              (Register.R (csPrefix.nextReg + 1))])
          [Instr.Die (Register.R (csPrefix.nextReg + 1))
            (blockSize obseq.LayoutTy.NatL)]
          (k := 0) (by simp)
        simpa [emit, setPlaceInfo] using h
    -- §6' execute the `Alloc`
    have h_run1 := runN_Assgn_Alloc_step compProg s_osea
      (Register.R csPrefix.nextReg) (layoutToTyVal σ)
      h_code1 h_own_tgt'
    -- §7' the source write, transported, then BRIDGE 1
    have h_w := h_write
    simp only [mirlite.writeResolvedPlace] at h_w
    split at h_w
    · simp at h_w
    · rename_i h_nb
      split at h_w
      · rename_i perms' h_useMut_src
        cases h_w
        obtain ⟨p3, h_useMut_tgt, h_psim2⟩ :=
          sb_write_respects_PermSim h_psim' h_wf_t' h_rt_new h_nw h_useMut_src
        obtain ⟨q1, h_ref_tgt⟩ := sb_ref_Mut_ok_of_sb_write_ok h_useMut_tgt
        have h_unprot := freshTag_not_protected h_psim' h_tbd'
        have h0' : wildcardTag < tgtPerms.NextTag := (h_tbd' _ _ h_wf_t'.2).2
        have h_ntw : (tgtPerms.NextTag == wildcardTag) = false := by grind
        obtain ⟨q2, q3, qAcc', h_wr1, h_die1, h_wr2, h_sm, h_ex, h_pf, h_ntle⟩ :=
          sb_ref_use_die_cancels h_ntw h_unprot h_ref_tgt
        have h_qAcc : qAcc' = p3 := by grind
        subst h_qAcc
        -- §8' the Borrow through the fresh root register
        have h_entry1 : PtrRegisterEntry
            (oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
              (obseq.TyVal.PTy, [Val.Ptr s_osea.mem.addrStart 0
                (obseq.typeSize (layoutToTyVal σ))
                s_osea.perms.NextTag]))
            (Register.R csPrefix.nextReg) s_mir.mem.addrStart 0
            (blockSize σ) s_osea.perms.NextTag := by
          rw [← h_addr_eq, ← h_sz]
          exact RegMap.lookup_insert_self _ _ _
        have h_bs : blockSize obseq.LayoutTy.NatL = 1 := rfl
        have h_le : s_mir.mem.addrStart + 0 + pathOffset path
            + blockSize obseq.LayoutTy.NatL
            ≤ s_mir.mem.addrStart + blockSize σ := by
          rw [h_bs]
          have := h_fit
          grind
        have h_ref' : MSB.ref tgtPerms
            (s_mir.mem.addrStart + 0 + pathOffset path)
            (blockSize obseq.LayoutTy.NatL) s_osea.perms.NextTag RefKind.Mut false []
            = .ok (q1, tgtPerms.NextTag) := by
          rw [Nat.add_zero]
          exact h_ref_tgt
        have h_run2 := runN_Assgn_Borrow_step compProg
          { s_osea with
              mem := (oseair.allocate s_osea.mem
                (obseq.typeSize (layoutToTyVal σ))).2,
              perms := tgtPerms,
              reg := oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
                (obseq.TyVal.PTy, [Val.Ptr s_osea.mem.addrStart 0
                  (obseq.typeSize (layoutToTyVal σ))
                  s_osea.perms.NextTag]),
              pc := s_osea.pc + 1 }
          (Register.R (csPrefix.nextReg + 1)) (Register.R csPrefix.nextReg)
          RefKind.Mut false [] (blockSize obseq.LayoutTy.NatL) (pathOffset path)
          h_code2 h_entry1 h_le h_ref'
        -- §9' the CStore through the fresh borrow
        have h_entry_tmp : PtrRegisterEntry
            (oseair.RegMap.insert
              (oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
                (obseq.TyVal.PTy, [Val.Ptr s_osea.mem.addrStart 0
                  (obseq.typeSize (layoutToTyVal σ))
                  s_osea.perms.NextTag]))
              (Register.R (csPrefix.nextReg + 1))
              (obseq.TyVal.PTy, [Val.Ptr s_mir.mem.addrStart (0 + pathOffset path)
                (blockSize σ) tgtPerms.NextTag]))
            (Register.R (csPrefix.nextReg + 1)) s_mir.mem.addrStart
            (s_mir.mem.addrStart + PathTo.offset path - s_mir.mem.addrStart)
            (blockSize σ) tgtPerms.NextTag := by
          have h_oe : s_mir.mem.addrStart + PathTo.offset path - s_mir.mem.addrStart
              = 0 + pathOffset path := by
            grind
          rw [h_oe]
          exact RegMap.lookup_insert_self _ _ _
        obtain ⟨h_wtp, h_sms'⟩ :=
          writeThroughPtr_sim (τ := obseq.LayoutTy.NatL)
            (s_osea := { s_osea with
                mem := (oseair.allocate s_osea.mem
                  (obseq.typeSize (layoutToTyVal σ))).2,
                perms := q1,
                reg := oseair.RegMap.insert
                  (oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
                    (obseq.TyVal.PTy, [Val.Ptr s_osea.mem.addrStart 0
                      (obseq.typeSize (layoutToTyVal σ))
                      s_osea.perms.NextTag]))
                  (Register.R (csPrefix.nextReg + 1))
                  (obseq.TyVal.PTy, [Val.Ptr s_mir.mem.addrStart (0 + pathOffset path)
                    (blockSize σ) tgtPerms.NextTag]),
                pc := s_osea.pc + 1 + 1 })
            (resolved := { addr := s_mir.mem.addrStart + PathTo.offset path,
                           tag := s_mir.perms.NextTag,
                           allocBase := s_mir.mem.addrStart,
                           allocSize := blockSize σ })
            "CStore Invalid Ptr" [mirlite.MemValue.word v] [Val.Dat v] rfl
            ⟨rfl, trivial⟩ h_id_a' h_entry_tmp
            (by
              show MSB.useMut q1 (s_mir.mem.addrStart + PathTo.offset path)
                [Val.Dat v].length tgtPerms.NextTag = .ok q2
              simpa using h_wr1)
            (by exact SourceMemSim.rename_mono h_incr_a h_incr_t h_sms)
            (Nat.le_add_right _ _)
            (fun k hk => by
              simp [Nat.lt_one_iff] at hk
              subst hk
              have h_lt : pathOffset path < blockSize σ := by omega
              simpa using h_ra_dom (pathOffset path) h_lt)
            h_write
        have h_run3 := runN_CStore_step compProg _ _
          obseq.TyVal.NatTy [Val.Dat v] (Register.R (csPrefix.nextReg + 1))
          h_code3 rfl h_wtp
        -- §10' the Die
        have h_die1' : MSB.die q2 (s_mir.mem.addrStart + (0 + pathOffset path))
            (blockSize obseq.LayoutTy.NatL) tgtPerms.NextTag = .ok q3 := by
          simpa using h_die1
        have h_run4 := runN_Die_step compProg
          { s_osea with
              mem := oseair.writeWordSeq
                (oseair.allocate s_osea.mem
                  (obseq.typeSize (layoutToTyVal σ))).2
                (s_mir.mem.addrStart + PathTo.offset path) [Val.Dat v],
              perms := q2,
              reg := oseair.RegMap.insert
                  (oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
                    (obseq.TyVal.PTy, [Val.Ptr s_osea.mem.addrStart 0
                      (obseq.typeSize (layoutToTyVal σ))
                      s_osea.perms.NextTag]))
                  (Register.R (csPrefix.nextReg + 1))
                  (obseq.TyVal.PTy, [Val.Ptr s_mir.mem.addrStart (0 + pathOffset path)
                    (blockSize σ) tgtPerms.NextTag]),
              pc := s_osea.pc + 1 + 1 + 1 }
          (Register.R (csPrefix.nextReg + 1)) (blockSize obseq.LayoutTy.NatL)
          h_code4 (RegMap.lookup_insert_self _ _ _) h_die1'
        have h_runA := (oseair_runN_add 1 1 s_osea compProg _ h_run1).trans h_run2
        have h_runB := (oseair_runN_add (1 + 1) 1 s_osea compProg _ h_runA).trans h_run3
        have h_run := (oseair_runN_add (1 + 1 + 1) 1 s_osea compProg _ h_runB).trans h_run4
        have h_psim4 : PermSim (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag)
            perms' q3 := by
          obtain ⟨hs, hp, he, hn⟩ := h_psim2
          exact ⟨by rw [h_sm]; exact hs, by rw [h_pf]; exact hp,
                 by rw [h_ex]; exact he, Nat.le_trans hn h_ntle⟩
        -- §11' rebuild the invariant under both extended renames
        refine ⟨_, _, _, 1 + 1 + 1 + 1, h_incr_a, h_incr_t, h_run, ?_⟩
        refine ⟨CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix,
          ⟨prefixCompileState_succ h_csAt h_stmt h_stmtOut, ?_⟩, ?_, h_sms', h_psim4,
          h_id_a', h_wf_t', ?_, ?_, ?_, ?_⟩
        · show s_osea.pc + 1 + 1 + 1 + 1 = _
          rw [h_pc, h_stmtRun]
          simp [emit, setPlaceInfo]
        · intro τ' loc' binding' h_env'
          by_cases h_idx : loc'.idx = loc.idx
          · have h_ty : τ' = σ := by
              rw [← loc'.hTy, h_idx, loc.hTy]
            subst h_ty
            have h_b : binding' = { addr := s_mir.mem.addrStart,
                                    tag := s_mir.perms.NextTag } := by
              grind [mirlite.Env.lookup, mirlite.Env.set]
            subst h_b
            refine ⟨Register.R csPrefix.nextReg, s_mir.mem.addrStart,
              s_osea.perms.NextTag, ?_, ?_, ?_, h_rt_new, h_nw, ?_⟩
            · rw [h_stmtRun, getPlaceInfo_emit, getPlaceInfo_emit, getPlaceInfo_emit,
                getPlaceInfo_setNextReg,
                show loc'.idx.1 = loc.idx.1 from congrArg Fin.val h_idx]
              exact getPlaceInfo_setPlaceInfo_self _ _ _
            · show oseair.RegMap.lookup _ _ = _
              rw [RegMap.lookup_insert_ne _ (by grind :
                Register.R csPrefix.nextReg ≠ Register.R (csPrefix.nextReg + 1))]
              rw [← h_addr_eq, ← h_sz]
              exact RegMap.lookup_insert_self _ _ _
            · simpa using h_ra_dom 0 (by omega)
            · intro k hk
              exact ⟨s_mir.mem.addrStart + k, h_ra_dom k hk⟩
          · have h_env'' : mirlite.Env.lookup s_mir.env loc' = some binding' := by
              simpa only [mirlite.Env.lookup, mirlite.Env.set, if_neg h_idx]
                using h_env'
            obtain ⟨reg', base', tag', h_pi', h_entry', h_ra', h_rt', h_nw', h_dom'⟩ :=
              h_lbs loc' binding' h_env''
            have h_idxv : loc'.idx.1 ≠ loc.idx.1 := by grind [Fin.ext]
            have h_regne1 : reg' ≠ Register.R csPrefix.nextReg := by
              cases reg' with
              | R n =>
                  have h_lt := h_prb _ _ _ h_pi'
                  grind [RegisterBelow]
            have h_regne2 : reg' ≠ Register.R (csPrefix.nextReg + 1) := by
              cases reg' with
              | R n =>
                  have h_lt := h_prb _ _ _ h_pi'
                  grind [RegisterBelow]
            refine ⟨reg', base', tag', ?_, ?_, h_incr_a _ _ h_ra',
              h_incr_t _ _ h_rt', h_nw',
              fun k hk => ⟨(h_dom' k hk).choose,
                h_incr_a _ _ (h_dom' k hk).choose_spec⟩⟩
            · rw [h_stmtRun, getPlaceInfo_emit, getPlaceInfo_emit, getPlaceInfo_emit,
                getPlaceInfo_setNextReg, getPlaceInfo_setPlaceInfo_ne _ h_idxv]
              exact h_pi'
            · show oseair.RegMap.lookup _ _ = _
              rw [RegMap.lookup_insert_ne _ h_regne2,
                RegMap.lookup_insert_ne _ h_regne1]
              exact h_entry'
        · show TagRenameBounded _ perms'.NextTag q3.NextTag
          rw [sb_write_NextTag h_useMut_src]
          refine TagRenameBounded.mono h_tbd' (Nat.le_refl _) ?_
          rw [← sb_write_NextTag h_useMut_tgt]
          exact h_ntle
        · simp only [AllocLockstep, mirlite_writeWordSeq_addrStart,
            oseair_writeWordSeq_addrStart, mirlite.allocate, oseair.allocate]
          rw [h_addr_eq, h_sz]
        · intro τ' loc' h_none
          by_cases h_idx : loc'.idx = loc.idx
          · exfalso
            grind [mirlite.Env.lookup, mirlite.Env.set]
          · have h_idxv : loc'.idx.1 ≠ loc.idx.1 := fun h => h_idx (Fin.ext h)
            have h_none' : mirlite.Env.lookup s_mir.env loc' = none := by
              grind [mirlite.Env.lookup, mirlite.Env.set]
            rw [h_stmtRun, getPlaceInfo_emit, getPlaceInfo_emit, getPlaceInfo_emit,
              getPlaceInfo_setNextReg, getPlaceInfo_setPlaceInfo_ne _ h_idxv]
            exact h_unmap loc' h_none'
        · intro idx reg τ'' h_look
          rw [h_stmtRun] at h_look ⊢
          rw [getPlaceInfo_emit, getPlaceInfo_emit, getPlaceInfo_emit,
            getPlaceInfo_setNextReg] at h_look
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

/-! ## Regime D over full chains: the dst ITSELF is a `PtrChain`

`PtrChain (.deref ptrPlace)` covers both the all-spine pointer places
(via `.deref`) and proj-topped ones over chain bases (via `.derefProj`),
so ONE leaf gated on the whole dst subsumes the D-spine leaf and the
depth-1 `*(s.f) := v` leaf: `ptrChain_lowering_sim` called at `Mut` on
the dst performs everything up to (and including) the final `Load`, and
the statement adds one `CStore`. -/

theorem compileStmt_derefdst_run
    {Γ : Ctx} {P : Place Γ (obseq.LayoutTy.PtrL obseq.LayoutTy.NatL)}
    {cs : CompilerState}
    {dOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Mut (.deref P))}
    (v : Word)
    (h_root : CompilerM.run (ensurePlaceRoot (Place.deref P)) cs = cs)
    (h_dval : CheckedCompilerM.value (placeToRegChecked RefKind.Mut (.deref P)) cs
      = Except.ok dOut)
    (h_dclean : dOut.result.cleanup = []) :
    CheckedCompilerM.run
        (compileStmtChecked (Stmt.assign (.deref P) (.constInit v))) cs
      = emit (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (.deref P)) cs)
          [Instr.CStore obseq.TyVal.NatTy [Val.Dat v] dOut.result.reg] := by
  simp only [compileStmtChecked, compileRExprPreChecked,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
    h_root, h_dval]
  simp [CompilerM.run, CompilerM.value, emitM, cleanupInstrs, h_dclean, emit_nil]

/-- The chain-dst statement lowers. -/
theorem compileStmt_derefdst_value
    {Γ : Ctx} {P : Place Γ (obseq.LayoutTy.PtrL obseq.LayoutTy.NatL)}
    {cs : CompilerState}
    {dOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Mut (.deref P))}
    (v : Word)
    (h_root : CompilerM.run (ensurePlaceRoot (Place.deref P)) cs = cs)
    (h_dval : CheckedCompilerM.value (placeToRegChecked RefKind.Mut (.deref P)) cs
      = Except.ok dOut) :
    ∃ so, CheckedCompilerM.value
      (compileStmtChecked (Stmt.assign (.deref P) (.constInit v))) cs
      = Except.ok so := by
  simp only [compileStmtChecked, compileRExprPreChecked,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
    h_root, h_dval]
  exact ⟨_, rfl⟩

/-- REGIME D over full chains, CLOSED 2026-08-29: `*P := v` for every
    dst that is a `PtrChain` — all-deref spines AND proj-topped pointer
    places over chain bases (`*((*q).f) := v`, `*(s.f) := v`) in one
    leaf. The mother lemma at `Mut` on the WHOLE dst delivers the
    loaded pointer register; the statement adds one `CStore` (BRIDGE 2). -/
theorem const_write_deref_chain_simulation
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_pre s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {ptrPlace : Place Γ (obseq.LayoutTy.PtrL obseq.LayoutTy.NatL)}
    {resolved : mirlite.PlaceRes} {permsD : MSB.State}
    (compProg : oseair.Prog)
    (v : Word)
    (h_chain : PtrChain (Place.deref ptrPlace))
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
  obtain ⟨csPrefix, ⟨h_csAt, h_pc⟩, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_tbd,
    h_alloc, h_unmap, h_prb⟩ := h_inv
  have h_mapped : PlaceInputsMapped csPrefix (Place.deref ptrPlace) :=
    placeInputsMapped_of_localBindingSim_resolvePlace h_lbs h_resolved
  have h_root := ensurePlaceRoot_run_eq_of_mapped h_mapped
  obtain ⟨dstOut0, h_dval0⟩ := placeToRegChecked_ok_of_placeInputsMapped
    (cs := csPrefix) (kind := RefKind.Mut) h_mapped
  obtain ⟨stmtOutC, h_stmtOutC⟩ := compileStmt_derefdst_value v h_root h_dval0
  obtain ⟨stmtOut, h_stmtOut⟩ := h_val0 csPrefix stmtOutC h_stmtOutC
  have h_incrS : StateIncr
      (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (.deref ptrPlace)) csPrefix)
      (CheckedCompilerM.run
        (compileStmtChecked
          (Stmt.assign (.deref ptrPlace) (.constInit v))) csPrefix) := by
    simp only [compileStmtChecked, compileRExprPreChecked,
      CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
      CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
      CheckedCompilerM.run_pure, CheckedCompilerM.value_pure, h_root]
    split
    · simp only [CompilerM.run, emitM]
      exact StateIncr.trans (emit_state_incr _ _)
        (StateIncr.trans (emit_state_incr _ _) (emit_state_incr _ _))
    · exact StateIncr.refl _
  have h_instD : ∀ q' instr,
      q' < (CheckedCompilerM.run
        (placeToRegChecked RefKind.Mut (.deref ptrPlace)) csPrefix).nextLabel →
      (CheckedCompilerM.run
        (placeToRegChecked RefKind.Mut (.deref ptrPlace)) csPrefix).code q'
        = some instr →
      compProg q' = some instr := by
    intro q' instr h_lt h_code
    refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
    · rw [h_run0]
      exact Nat.lt_of_lt_of_le h_lt h_incrS.nextLabel_le
    · rw [h_run0, h_incrS.code_eq q' h_lt]
      exact h_code
  obtain ⟨dOut, n1, s_mid, tres, h_dval, h_dclean, h_drun, h_dpc, h_dmem, h_dpsim,
    h_dnt1, h_dnt2, h_dlbs, h_dentry, h_drt, h_dnw, h_dle, h_drange, h_dbelow,
    h_dprm, h_dregmono, h_dlabmono, -, -⟩ :=
    ptrChain_lowering_sim h_id_a h_wf_t h_chain RefKind.Mut csPrefix s_osea
      resolved permsD h_res h_tbd h_lbs h_prb h_sms h_psim h_pc h_instD
  have h_stmtRunC := compileStmt_derefdst_run v h_root h_dval h_dclean
  have h_stmtRun := (h_run0 csPrefix).trans h_stmtRunC
  have h_code : compProg s_mid.pc
      = some (Instr.CStore obseq.TyVal.NatTy [Val.Dat v] dOut.result.reg) := by
    rw [h_dpc]
    refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
    · rw [h_stmtRun]
      show _ < _ + 1
      exact Nat.lt_succ_self _
    · rw [h_stmtRun]
      have h := emit_code_at_new
        (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (.deref ptrPlace)) csPrefix)
        [Instr.CStore obseq.TyVal.NatTy [Val.Dat v] dOut.result.reg]
        (k := 0) (by simp)
      simpa using h
  have h_w := h_write
  simp only [mirlite.writeResolvedPlace] at h_w
  split at h_w
  · simp at h_w
  · rename_i h_nb
    split at h_w
    · rename_i perms2 h_useMut_src
      cases h_w
      obtain ⟨p3, h_useMut_tgt, h_psim3⟩ :=
        sb_write_respects_PermSim h_dpsim h_wf_t h_drt h_dnw h_useMut_src
      obtain ⟨h_wtp, h_sms'⟩ :=
        writeThroughPtr_sim (τ := obseq.LayoutTy.NatL)
          (s_osea := s_mid) (resolved := resolved)
          "CStore Invalid Ptr" [mirlite.MemValue.word v] [Val.Dat v] rfl
          ⟨rfl, trivial⟩ h_id_a h_dentry h_useMut_tgt
          (by rw [h_dmem]; exact h_sms)
          h_dle
          (fun k hk => by
            have hk0 : k = 0 := by simpa using hk
            subst hk0
            have h_lt : resolved.addr - resolved.allocBase < resolved.allocSize := by
              grind
            obtain ⟨a', ha'⟩ := h_drange _ h_lt
            have h_eq := h_id_a _ _ ha'
            have h_cancel : resolved.allocBase + (resolved.addr - resolved.allocBase)
                = resolved.addr := Nat.add_sub_cancel' h_dle
            grind)
          h_write
      have h_run2 := runN_CStore_step compProg s_mid _
        obseq.TyVal.NatTy [Val.Dat v] dOut.result.reg h_code rfl h_wtp
      refine ⟨_, n1 + 1,
        (oseair_runN_add n1 1 s_osea compProg s_mid h_drun).trans h_run2, ?_⟩
      refine ⟨CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix,
        ⟨prefixCompileState_succ h_csAt h_stmt h_stmtOut, ?_⟩, ?_, h_sms', h_psim3,
        h_id_a, h_wf_t, ?_, ?_, ?_, ?_⟩
      · show s_mid.pc + 1 = _
        rw [h_dpc, h_stmtRun]
        simp [emit]
      · intro τ'' loc' binding' h_env'
        obtain ⟨reg', base', tag', h_pi', h_entry', h_ra', h_rt', h_nw', h_dom'⟩ :=
          h_dlbs loc' binding' h_env'
        refine ⟨reg', base', tag', ?_, h_entry', h_ra', h_rt', h_nw', h_dom'⟩
        rw [h_stmtRun, getPlaceInfo_emit]
        show (CheckedCompilerM.run
          (placeToRegChecked RefKind.Mut (.deref ptrPlace)) csPrefix).placeRegMap.lookup
            loc'.idx.1 = _
        rw [h_dprm]
        exact h_pi'
      · show TagRenameBounded _ perms2.NextTag p3.NextTag
        rw [sb_write_NextTag h_useMut_src, h_dnt1, sb_write_NextTag h_useMut_tgt]
        exact TagRenameBounded.mono h_tbd (Nat.le_refl _) h_dnt2
      · simp only [AllocLockstep, mirlite_writeWordSeq_addrStart,
          oseair_writeWordSeq_addrStart, h_dmem]
        exact h_alloc
      · intro τ'' loc' h_none
        rw [h_stmtRun, getPlaceInfo_emit]
        show (CheckedCompilerM.run
          (placeToRegChecked RefKind.Mut (.deref ptrPlace)) csPrefix).placeRegMap.lookup
            loc'.idx.1 = none
        rw [h_dprm]
        exact h_unmap loc' h_none
      · intro idx reg'' τ'' h_look
        rw [h_stmtRun] at h_look ⊢
        rw [getPlaceInfo_emit] at h_look
        have h_prm2 : (CheckedCompilerM.run
            (placeToRegChecked RefKind.Mut (.deref ptrPlace)) csPrefix).placeRegMap
            = csPrefix.placeRegMap := h_dprm
        have h_cs : getPlaceInfo csPrefix idx = some (reg'', τ'') := by
          show csPrefix.placeRegMap.lookup idx = _
          rw [← h_prm2]
          exact h_look
        refine RegisterBelow.mono ?_ (h_prb _ _ _ h_cs)
        simp only [emit]
        exact h_dregmono
    · simp at h_w

/-! ## Flatten transfer for the projected-over-deref constant-write dst:
    the rhs compiles to one `CStore` at the dst result's register plus
    its cleanups, and the flatten agree lemma equates both across the
    reassociation. (Stated at the concrete `.proj (.deref pp) path`
    shape so `compileStmtChecked`'s match reduces — a variable dst is
    stuck on the `.local` arm.) -/

theorem compileStmt_const_projderef_flatten_run
    {Γ : Ctx} {σ : LayoutTy}
    (pp : Place Γ (obseq.LayoutTy.PtrL σ)) (path : PathTo σ obseq.LayoutTy.NatL)
    (v : Word) (cs : CompilerState) :
    CheckedCompilerM.run
        (compileStmtChecked
          (Stmt.assign (.proj (.deref pp) path) (.constInit v))) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.proj (.deref (flattenPlace pp)) path)
              (.constInit v))) cs := by
  obtain ⟨h_agr, h_agv⟩ := placeToRegChecked_flatten_agree
    (Place.proj (Place.deref pp) path)
    RefKind.Mut (CompilerM.run (ensurePlaceRoot (Place.proj (Place.deref pp) path)) cs)
  rw [show flattenPlace (Place.proj (Place.deref pp) path)
      = Place.proj (Place.deref (flattenPlace pp)) path from rfl] at h_agr h_agv
  have h_er : ensurePlaceRoot (Place.proj (Place.deref (flattenPlace pp)) path)
      = ensurePlaceRoot (Place.proj (Place.deref pp) path) := by
    rw [show Place.proj (Place.deref (flattenPlace pp)) path
        = flattenPlace (Place.proj (Place.deref pp) path) from rfl]
    exact ensurePlaceRoot_flatten (Place.proj (Place.deref pp) path)
  simp only [compileStmtChecked, compileRExprPreChecked,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure, h_er]
  cases hF : CheckedCompilerM.value
      (placeToRegChecked RefKind.Mut (Place.proj (Place.deref (flattenPlace pp)) path))
      (CompilerM.run (ensurePlaceRoot (Place.proj (Place.deref pp) path)) cs) with
  | error eF =>
      cases hO : CheckedCompilerM.value
          (placeToRegChecked RefKind.Mut (Place.proj (Place.deref pp) path))
          (CompilerM.run (ensurePlaceRoot (Place.proj (Place.deref pp) path)) cs) with
      | error eO =>
          simp only [hF, hO]
          exact h_agr.symm
      | ok oO =>
          exfalso
          rw [hF, hO] at h_agv
          simp [Except.map] at h_agv
  | ok oF =>
      cases hO : CheckedCompilerM.value
          (placeToRegChecked RefKind.Mut (Place.proj (Place.deref pp) path))
          (CompilerM.run (ensurePlaceRoot (Place.proj (Place.deref pp) path)) cs) with
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

theorem compileStmt_const_projderef_flatten_value
    {Γ : Ctx} {σ : LayoutTy}
    (pp : Place Γ (obseq.LayoutTy.PtrL σ)) (path : PathTo σ obseq.LayoutTy.NatL)
    (v : Word) (cs : CompilerState) :
    ∀ so, CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.proj (.deref (flattenPlace pp)) path)
            (.constInit v))) cs
      = Except.ok so →
    ∃ so', CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.proj (.deref pp) path) (.constInit v))) cs
      = Except.ok so' := by
  intro so h_so
  obtain ⟨h_agr, h_agv⟩ := placeToRegChecked_flatten_agree
    (Place.proj (Place.deref pp) path)
    RefKind.Mut (CompilerM.run (ensurePlaceRoot (Place.proj (Place.deref pp) path)) cs)
  rw [show flattenPlace (Place.proj (Place.deref pp) path)
      = Place.proj (Place.deref (flattenPlace pp)) path from rfl] at h_agr h_agv
  have h_er : ensurePlaceRoot (Place.proj (Place.deref (flattenPlace pp)) path)
      = ensurePlaceRoot (Place.proj (Place.deref pp) path) := by
    rw [show Place.proj (Place.deref (flattenPlace pp)) path
        = flattenPlace (Place.proj (Place.deref pp) path) from rfl]
    exact ensurePlaceRoot_flatten (Place.proj (Place.deref pp) path)
  simp only [compileStmtChecked, compileRExprPreChecked,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure, h_er] at h_so ⊢
  cases hO : CheckedCompilerM.value
      (placeToRegChecked RefKind.Mut (Place.proj (Place.deref pp) path))
      (CompilerM.run (ensurePlaceRoot (Place.proj (Place.deref pp) path)) cs) with
  | error eO =>
      exfalso
      cases hF : CheckedCompilerM.value
          (placeToRegChecked RefKind.Mut (Place.proj (Place.deref (flattenPlace pp)) path))
          (CompilerM.run (ensurePlaceRoot (Place.proj (Place.deref pp) path)) cs) with
      | error eF =>
          rw [hF] at h_so
          simp at h_so
      | ok oF =>
          rw [hF, hO] at h_agv
          simp [Except.map] at h_agv
  | ok oO =>
      simp only [hO]
      exact ⟨_, rfl⟩

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
          -- REGIME B-proj: fresh root, closed
          exact const_write_proj_fresh_simulation compProg v h_comp h_inv h_stmt
            h_run0 h_val0 h_env h_prep h_res h_write
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
      -- flatten-normalize the WHOLE dst: the flattened pointer place is
      -- ALWAYS a canonical chain, so the two C-deref leaves are TOTAL here
      have h_chain := PtrChain_flatten_deref pp
      have h_run0' : ∀ cs, CheckedCompilerM.run (compileStmtChecked stmt0) cs
          = CheckedCompilerM.run
              (compileStmtChecked
                (Stmt.assign (.proj (.deref (flattenPlace pp)) path)
                  (.constInit v))) cs :=
        fun cs => (h_run0 cs).trans
          (compileStmt_const_projderef_flatten_run pp path v cs)
      have h_val0' : ∀ cs so, CheckedCompilerM.value
          (compileStmtChecked
            (Stmt.assign (.proj (.deref (flattenPlace pp)) path)
              (.constInit v))) cs = Except.ok so →
          ∃ so', CheckedCompilerM.value (compileStmtChecked stmt0) cs
            = Except.ok so' := by
        intro cs so h
        obtain ⟨so', h'⟩ := compileStmt_const_projderef_flatten_value
          pp path v cs so h
        exact h_val0 cs so' h'
      have h_prep' : mirlite.preparePlaceAssign MSB s_mir
          (.proj (.deref (flattenPlace pp)) path) = .ok s_pre := by
        rw [show Place.proj (Place.deref (flattenPlace pp)) path
            = flattenPlace (Place.proj (Place.deref pp) path) from rfl,
          preparePlaceAssign_flatten]
        exact h_prep
      have h_res' : mirlite.resolvePlaceAcc MSB s_pre
          (.proj (.deref (flattenPlace pp)) path) = .ok (resolved, permsD) := by
        rw [show Place.proj (Place.deref (flattenPlace pp)) path
            = flattenPlace (Place.proj (Place.deref pp) path) from rfl,
          resolvePlaceAcc_flatten]
        exact h_res
      by_cases h_o : pathOffset path = 0
      · obtain ⟨s_osea', n, h_run, h_inv'⟩ :=
          const_write_proj_deref_zero_simulation compProg v h_chain h_o h_comp h_inv
            h_stmt h_run0' h_val0' h_prep' h_res' h_write
        exact ⟨ρa, ρt, s_osea', n, AddrRenameIncr.refl ρa, TagRenameIncr.refl ρt,
          h_run, h_inv'⟩
      · obtain ⟨s_osea', n, h_run, h_inv'⟩ :=
          const_write_proj_deref_simulation compProg v h_chain h_o h_comp h_inv
            h_stmt h_run0' h_val0' h_prep' h_res' h_write
        exact ⟨ρa, ρt, s_osea', n, AddrRenameIncr.refl ρa, TagRenameIncr.refl ρt,
          h_run, h_inv'⟩

/-! ## Flatten transfer for regime D: every deref dst normalizes into
    the chain grammar, so the chain leaf serves ALL of them. -/

theorem compileStmt_derefdst_flatten_run
    {Γ : Ctx} {P : Place Γ (obseq.LayoutTy.PtrL obseq.LayoutTy.NatL)}
    (v : Word) (cs : CompilerState) :
    CheckedCompilerM.run
        (compileStmtChecked (Stmt.assign (.deref P) (.constInit v))) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.deref (flattenPlace P)) (.constInit v))) cs := by
  obtain ⟨h_agr, h_agv⟩ := placeToRegChecked_flatten_agree (Place.deref P)
    RefKind.Mut (CompilerM.run (ensurePlaceRoot (Place.deref P)) cs)
  rw [show flattenPlace (Place.deref P) = Place.deref (flattenPlace P) from rfl]
    at h_agr h_agv
  have h_er : ensurePlaceRoot (Place.deref (flattenPlace P))
      = ensurePlaceRoot (Place.deref P) := ensurePlaceRoot_flatten (Place.deref P)
  simp only [compileStmtChecked, compileRExprPreChecked,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure, h_er]
  cases hF : CheckedCompilerM.value
      (placeToRegChecked RefKind.Mut (Place.deref (flattenPlace P)))
      (CompilerM.run (ensurePlaceRoot (Place.deref P)) cs) with
  | error eF =>
      cases hO : CheckedCompilerM.value
          (placeToRegChecked RefKind.Mut (Place.deref P))
          (CompilerM.run (ensurePlaceRoot (Place.deref P)) cs) with
      | error eO =>
          simp only [hF, hO]
          exact h_agr.symm
      | ok oO =>
          exfalso
          rw [hF, hO] at h_agv
          simp [Except.map] at h_agv
  | ok oF =>
      cases hO : CheckedCompilerM.value
          (placeToRegChecked RefKind.Mut (Place.deref P))
          (CompilerM.run (ensurePlaceRoot (Place.deref P)) cs) with
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

theorem compileStmt_derefdst_flatten_value
    {Γ : Ctx} {P : Place Γ (obseq.LayoutTy.PtrL obseq.LayoutTy.NatL)}
    (v : Word) (cs : CompilerState) :
    ∀ so, CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.deref (flattenPlace P)) (.constInit v))) cs
      = Except.ok so →
    ∃ so', CheckedCompilerM.value
        (compileStmtChecked (Stmt.assign (.deref P) (.constInit v))) cs
      = Except.ok so' := by
  intro so h_so
  obtain ⟨h_agr, h_agv⟩ := placeToRegChecked_flatten_agree (Place.deref P)
    RefKind.Mut (CompilerM.run (ensurePlaceRoot (Place.deref P)) cs)
  rw [show flattenPlace (Place.deref P) = Place.deref (flattenPlace P) from rfl]
    at h_agr h_agv
  have h_er : ensurePlaceRoot (Place.deref (flattenPlace P))
      = ensurePlaceRoot (Place.deref P) := ensurePlaceRoot_flatten (Place.deref P)
  simp only [compileStmtChecked, compileRExprPreChecked,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure, h_er] at h_so ⊢
  cases hO : CheckedCompilerM.value
      (placeToRegChecked RefKind.Mut (Place.deref P))
      (CompilerM.run (ensurePlaceRoot (Place.deref P)) cs) with
  | error eO =>
      exfalso
      cases hF : CheckedCompilerM.value
          (placeToRegChecked RefKind.Mut (Place.deref (flattenPlace P)))
          (CompilerM.run (ensurePlaceRoot (Place.deref P)) cs) with
      | error eF =>
          rw [hF] at h_so
          simp at h_so
      | ok oF =>
          rw [hF, hO] at h_agv
          simp [Except.map] at h_agv
  | ok oO =>
      simp only [hO]
      exact ⟨_, rfl⟩

/-- Regime D, decomposed by whether the WHOLE dst is a canonical chain:
    `PtrChain (.deref ptrPlace)` — all-deref spines AND proj-topped
    pointer places over chain bases — is CLOSED via
    `const_write_deref_chain_simulation`; the rest (proj-of-proj,
    non-chain interiors, unbound roots) is the named residual above. -/
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
  obtain ⟨s_osea', n, h_run, h_inv'⟩ :=
    const_write_deref_chain_simulation (ptrPlace := flattenPlace ptrPlace)
      compProg v (PtrChain_flatten_deref ptrPlace) h_comp h_inv h_stmt
      (fun cs => compileStmt_derefdst_flatten_run v cs)
      (fun cs so h => compileStmt_derefdst_flatten_value v cs so h)
      (by
        rw [show Place.deref (flattenPlace ptrPlace)
          = flattenPlace (Place.deref ptrPlace) from rfl,
          preparePlaceAssign_flatten]
        exact h_prep)
      (by
        rw [show Place.deref (flattenPlace ptrPlace)
          = flattenPlace (Place.deref ptrPlace) from rfl,
          resolvePlaceAcc_flatten]
        exact h_res)
      h_write
  exact ⟨ρa, ρt, s_osea', n, AddrRenameIncr.refl ρa, TagRenameIncr.refl ρt,
    h_run, h_inv'⟩

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
      simp only [h_prep, mirlite.evalRExpr] at h_step
      cases h_res : mirlite.resolvePlaceAcc MSB s_pre dst with
      | error e => simp [h_res] at h_step
      | ok pr =>
          obtain ⟨resolved, permsD⟩ := pr
          simp only [h_res] at h_step
          obtain ⟨csPrefix', stmtOut, h_csAt', h_stmtOut⟩ :=
            const_write_stmt_evidence (s_pre := s_pre) v h_inv_full h_prep
          exact const_write_resolved_simulation compProg v h_comp h_inv_full h_stmt h_prep h_res
            csPrefix' h_csAt' stmtOut h_stmtOut h_step

end obseq3.proof
