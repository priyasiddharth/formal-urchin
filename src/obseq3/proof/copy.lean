import obseq3.proof.common
import obseq3.proof.permsim_transport
import obseq3.proof.spine

namespace obseq3.proof

/-! ### Ambient binders

    The data every simulation leaf and fragment-transfer lemma
    quantifies over. These are IMPLICIT and every leaf's conclusion
    mentions them, so Lean includes them automatically — no `include` is
    needed, and because they were already the leading binders the
    explicit argument order is unchanged.

    A theorem that binds its own `{Γ : Ctx}` shadows these cleanly and
    picks up none of them. -/
variable {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
variable {ρa : AddrRenameMap} {ρt : TagRenameMap}
variable {s_mir s_mir' : mirlite.State MSB Γ}
variable {s_osea : oseair.State MSB}


open obseq3
open obseq3.compile
open obseq3.oseair (Instr Register Rhs Val)

/-! ## The generic read packages

A read-then-store rvalue's SOURCE half, abstracted over the rvalue: what
the compiled `Assgn tmp (mk srcReg)` leaves behind, given only that the
mirlite evaluation succeeded. `ReadPkgLowered` is the chain-class source
(one instruction after the source lowering); `ReadPkgProjOffset` is the
projected source at a nonzero offset (`Borrow; Assgn; Die`). Each is the
∀-closure of the corresponding copy package with the mirlite inversion
residue (`h_sres`/`h_fit`/`h_read_src`) replaced by the evaluation itself,
and the post-read target state left abstract — which is all the write
seams ever look at. The rvalue instances (`copy_readpkg_*`, and the cast
packages) do their own inversion. -/

def ReadPkgLowered {Γ : Ctx} {τs τ : LayoutTy} (compProg : oseair.Prog)
    (rhs : RExpr Γ τ) (src : Place Γ τs) (mk : Register → Rhs) : Prop :=
  ∀ (ρa : AddrRenameMap) (ρt : TagRenameMap)
    (sM : mirlite.State MSB Γ) (sA : oseair.State MSB) (csA : CompilerState),
    IdentityOnDomain ρa → TagRenameWF ρt →
    TagRenameBounded ρt sM.perms.NextTag sA.perms.NextTag →
    LocalBindingSim ρa ρt sM.env sA csA →
    PlaceRegMapBound csA →
    SourceMemSim ρa ρt sM.mem sA.mem →
    AllocLockstep ρa sM.mem sA.mem →
    PermSim ρt sM.perms sA.perms →
    sA.pc = csA.nextLabel →
    ∀ (output : mirlite.EvalOutput MSB Γ τ),
      mirlite.evalRExpr MSB sM rhs = .ok output →
    PlaceInputsMapped csA src ∧
    ∀ (sOut0 : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared src)),
      CheckedCompilerM.value (placeToRegChecked RefKind.Shared src) csA = Except.ok sOut0 →
      (∀ q instr, q < (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextLabel → (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).code q = some instr → compProg q = some instr) →
      (∀ q instr,
        q < (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg + 1 }
          ([Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg) (mk sOut0.result.reg)]
            ++ cleanupInstrs sOut0.result.cleanup)).nextLabel →
        (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg + 1 }
          ([Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg) (mk sOut0.result.reg)]
            ++ cleanupInstrs sOut0.result.cleanup)).code q = some instr →
        compProg q = some instr) →
      sOut0.result.cleanup = [] ∧
      ∃ (nR : Nat) (sR : oseair.State MSB) (perms₂ : MSB.State) (vals : List Val),
        output.state = { sM with perms := perms₂ } ∧
        vals.length = blockSize τ ∧
        oseair.runN MSB nR sA compProg = oseair.Result.Ok sR ∧
        (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg) (mk sOut0.result.reg)]).placeRegMap = csA.placeRegMap ∧
        csA.nextReg ≤ (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg) (mk sOut0.result.reg)]).nextReg ∧
        LocalBindingSim ρa ρt sM.env sR (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg) (mk sOut0.result.reg)]) ∧
        PermSim ρt perms₂ sR.perms ∧
        TagRenameBounded ρt perms₂.NextTag sR.perms.NextTag ∧
        sR.mem = sA.mem ∧
        sR.pc = (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg) (mk sOut0.result.reg)]).nextLabel ∧
        oseair.RegMap.lookup sR.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg) = some (layoutToTyVal τ, vals) ∧
        RegisterBelow (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg) (mk sOut0.result.reg)]).nextReg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg) ∧
        ListRel (MemValSim ρa ρt) output.values vals

def ReadPkgProjOffset {Γ : Ctx} {τs σs τ : LayoutTy} (compProg : oseair.Prog)
    (rhs : RExpr Γ τ) (B : Place Γ σs) (spath : PathTo σs τs) (mk : Register → Rhs) : Prop :=
  ∀ (ρa : AddrRenameMap) (ρt : TagRenameMap)
    (sM : mirlite.State MSB Γ) (sA : oseair.State MSB) (csA : CompilerState),
    IdentityOnDomain ρa → TagRenameWF ρt →
    TagRenameBounded ρt sM.perms.NextTag sA.perms.NextTag →
    LocalBindingSim ρa ρt sM.env sA csA →
    PlaceRegMapBound csA →
    SourceMemSim ρa ρt sM.mem sA.mem →
    AllocLockstep ρa sM.mem sA.mem →
    PermSim ρt sM.perms sA.perms →
    sA.pc = csA.nextLabel →
    ∀ (output : mirlite.EvalOutput MSB Γ τ),
      mirlite.evalRExpr MSB sM rhs = .ok output →
    PlaceInputsMapped csA (Place.proj B spath) ∧
    ∀ (sOut0 : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared B)),
      CheckedCompilerM.value (placeToRegChecked RefKind.Shared B) csA = Except.ok sOut0 →
    ∀ (sOutP : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared (Place.proj B spath))),
      sOutP.result.reg = Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg →
      sOutP.result.cleanup = sOut0.result.cleanup ++ [(Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg, blockSize τs)] →
      CodeIncluded compProg (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA) →
      CodeIncluded compProg (emit { (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg) (borrowRhs RefKind.Shared (blockSize τs) sOut0.result.reg (pathOffset spath))]) with nextReg := (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg) (borrowRhs RefKind.Shared (blockSize τs) sOut0.result.reg (pathOffset spath))]).nextReg + 1 }
        ([Instr.Assgn (Register.R (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg) (borrowRhs RefKind.Shared (blockSize τs) sOut0.result.reg (pathOffset spath))]).nextReg) (mk sOutP.result.reg)]
          ++ cleanupInstrs sOutP.result.cleanup)) →
      sOut0.result.cleanup = [] ∧
      ∃ (nR : Nat) (sR : oseair.State MSB) (perms₂ : MSB.State) (vals : List Val),
        output.state = { sM with perms := perms₂ } ∧
        vals.length = blockSize τ ∧
        oseair.runN MSB nR sA compProg = oseair.Result.Ok sR ∧
        (emit { (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg) (borrowRhs RefKind.Shared (blockSize τs) sOut0.result.reg (pathOffset spath))]) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1 + 1 } [Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1)) (mk (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)), Instr.Die (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg) (blockSize τs)]).placeRegMap = csA.placeRegMap ∧
        csA.nextReg ≤ (emit { (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg) (borrowRhs RefKind.Shared (blockSize τs) sOut0.result.reg (pathOffset spath))]) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1 + 1 } [Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1)) (mk (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)), Instr.Die (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg) (blockSize τs)]).nextReg ∧
        LocalBindingSim ρa ρt sM.env sR (emit { (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg) (borrowRhs RefKind.Shared (blockSize τs) sOut0.result.reg (pathOffset spath))]) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1 + 1 } [Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1)) (mk (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)), Instr.Die (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg) (blockSize τs)]) ∧
        PermSim ρt perms₂ sR.perms ∧
        TagRenameBounded ρt perms₂.NextTag sR.perms.NextTag ∧
        sR.mem = sA.mem ∧
        sR.pc = (emit { (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg) (borrowRhs RefKind.Shared (blockSize τs) sOut0.result.reg (pathOffset spath))]) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1 + 1 } [Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1)) (mk (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)), Instr.Die (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg) (blockSize τs)]).nextLabel ∧
        oseair.RegMap.lookup sR.reg (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1)) = some (layoutToTyVal τ, vals) ∧
        RegisterBelow (emit { (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg) (borrowRhs RefKind.Shared (blockSize τs) sOut0.result.reg (pathOffset spath))]) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1 + 1 } [Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1)) (mk (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)), Instr.Die (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg) (blockSize τs)]).nextReg (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1)) ∧
        ListRel (MemValSim ρa ρt) output.values vals

/-- `copy_derefdst_incrs` for a LOCAL destination. The local arm of
    `compileStmtChecked` has a different shape -- `ensureLocalRegE` first
    (which for an unbound root emits the `Alloc`), then the rvalue is
    compiled straight into the local's register: no destination
    lowering, no destination cleanup. Two facts, not three. `csE` is the
    post-`ensureLocalRegE` state the source lowering starts from. -/
theorem readrhs_localdst_incrs
    {τ τs : LayoutTy} {loc : Local Γ τ} {src : Place Γ τs}
    {stmt0 : Stmt Γ} (cs : CompilerState)
    {csE : CompilerState} (h_erun : CompilerM.run (ensureLocalRegE loc) cs = csE)
    {sOut0 : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared src)}
    {rhs : RExpr Γ τ} {mk : Register → Rhs}
    (h_shape : ReadRhsShape rhs src mk)
    (h_sval0 : CheckedCompilerM.value (placeToRegChecked RefKind.Shared src) csE
      = Except.ok sOut0)
    {csS : CompilerState}
    (h_srun : CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csE = csS)
    (h_run0 : CheckedCompilerM.run (compileStmtChecked stmt0) cs
      = CheckedCompilerM.run
          (compileStmtChecked (Stmt.assign (.local loc) rhs)) cs) :
    StateIncr csS (CheckedCompilerM.run (compileStmtChecked stmt0) cs) ∧
    StateIncr (emit { csS with nextReg := csS.nextReg + 1 }
        ([Instr.Assgn (Register.R csS.nextReg) (mk sOut0.result.reg)]
          ++ cleanupInstrs sOut0.result.cleanup))
        (CheckedCompilerM.run (compileStmtChecked stmt0) cs) := by
  obtain ⟨ev, h_rhs⟩ := id h_shape
  rw [h_run0]
  simp only [compileStmtChecked, compileRExprToChecked, h_rhs, readRhsPre, csMonad, h_erun, h_sval0]
  simp only [csRun]
  rw [h_srun]
  generalize hR : emit { csS with nextReg := csS.nextReg + 1 }
      ([Instr.Assgn (Register.R csS.nextReg) (mk sOut0.result.reg)]
        ++ cleanupInstrs sOut0.result.cleanup) = csR
  have hSR : StateIncr csS csR := by
    rw [← hR]
    exact StateIncr.trans (freshReg_state_incr csS) (emit_state_incr _ _)
  exact ⟨StateIncr.trans hSR (StateIncr.trans (emit_state_incr _ _) (emit_state_incr _ _)),
    StateIncr.trans (emit_state_incr _ _) (emit_state_incr _ _)⟩


/-- The fragment of `dst := copy src` for a mapped local dst and ANY
    source place, stated over the OPAQUE run of the source lowering:
    the src-lowering code (whatever it emits — the mother lemma owns
    it), then the READ into a fresh register (`Load`), then the write
    (`RStore`). The read-before-write shape is rustc's; see
    notes/2026-08-29-copy-nonlocal-dst-order.md. -/
theorem compileStmt_readrhs_chainsrc_run
    {Γ : Ctx} {τ τs : LayoutTy}
    {dstLoc : Local Γ τ}
    {src : Place Γ τs}
    {cs : CompilerState} {dstReg : Register}
    {sOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared src)}
    {rhs : RExpr Γ τ} {mk : Register → Rhs}
    (h_shape : ReadRhsShape rhs src mk)
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = some (dstReg, τ))
    (h_sval : CheckedCompilerM.value (placeToRegChecked RefKind.Shared src) cs
      = Except.ok sOut)
    (h_sclean : sOut.result.cleanup = []) :
    CheckedCompilerM.run
        (compileStmtChecked
          (Stmt.assign (.local dstLoc) rhs)) cs
      = emit (emit
          { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) cs) with
              nextReg := (CheckedCompilerM.run
                (placeToRegChecked RefKind.Shared src) cs).nextReg + 1 }
          [Instr.Assgn (Register.R (CheckedCompilerM.run
              (placeToRegChecked RefKind.Shared src) cs).nextReg)
            (mk sOut.result.reg)])
          [Instr.RStore (obseq.layoutToTyVal τ)
            (Register.R (CheckedCompilerM.run
              (placeToRegChecked RefKind.Shared src) cs).nextReg) dstReg] := by
  obtain ⟨ev, h_rhs⟩ := id h_shape
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_existing h_dst
  have h_run' : (ensureLocalRegE dstLoc cs).snd.val = cs := h_run
  simp [compileStmtChecked, compileRExprToChecked, h_rhs, readRhsPre, h_run, h_run', h_val, h_sval]
  simp [csRun, cleanupInstrs, h_sclean, emit_nil]

/-- The chain-src copy lowers. -/
theorem compileStmt_readrhs_chainsrc_value
    {Γ : Ctx} {τ τs : LayoutTy}
    {dstLoc : Local Γ τ}
    {src : Place Γ τs}
    {cs : CompilerState} {dstReg : Register}
    {sOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared src)}
    {rhs : RExpr Γ τ} {mk : Register → Rhs}
    (h_shape : ReadRhsShape rhs src mk)
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = some (dstReg, τ))
    (h_sval : CheckedCompilerM.value (placeToRegChecked RefKind.Shared src) cs
      = Except.ok sOut) :
    ∃ so, CheckedCompilerM.value
      (compileStmtChecked
        (Stmt.assign (.local dstLoc) rhs)) cs
      = Except.ok so := by
  obtain ⟨ev, h_rhs⟩ := id h_shape
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_existing h_dst
  simp only [compileStmtChecked, compileRExprToChecked, h_rhs, readRhsPre, csMonad, h_run, h_sval]
  exact ⟨_, rfl⟩

/-! ## Flatten transfer for the copy-src shape -/

theorem compileRExprToChecked_readrhs_flatten_run
    {Γ : Ctx} {τ τs : LayoutTy} {P : Place Γ (obseq.LayoutTy.PtrL τs)}
    {rhs rhs2 : RExpr Γ τ} {mk : Register → Rhs}
    (h_shape : ReadRhsShape rhs (.deref P) mk)
    (h_shape2 : ReadRhsShape rhs2 (.deref (flattenPlace P)) mk)
    (r : Register) (cs : CompilerState) :
    CheckedCompilerM.run
        (compileRExprToChecked r rhs) cs
      = CheckedCompilerM.run
          (compileRExprToChecked r rhs2) cs := by
  obtain ⟨ev, h_rhs⟩ := id h_shape
  obtain ⟨ev2, h_rhs2⟩ := id h_shape2
  obtain ⟨h_agr, h_agv⟩ :=
    placeToRegChecked_flatten_agree (Place.deref P) RefKind.Shared cs
  rw [show flattenPlace (Place.deref P) = Place.deref (flattenPlace P) from rfl]
    at h_agr h_agv
  simp only [csMonad, compileRExprToChecked, h_rhs, h_rhs2, readRhsPre]
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

theorem compileRExprToChecked_readrhs_flatten_valunit
    {Γ : Ctx} {τ τs : LayoutTy} {P : Place Γ (obseq.LayoutTy.PtrL τs)}
    {rhs rhs2 : RExpr Γ τ} {mk : Register → Rhs}
    (h_shape : ReadRhsShape rhs (.deref P) mk)
    (h_shape2 : ReadRhsShape rhs2 (.deref (flattenPlace P)) mk)
    (r : Register) (cs : CompilerState) :
    (CheckedCompilerM.value
        (compileRExprToChecked r rhs) cs).map
      (fun _ => ())
      = (CheckedCompilerM.value
          (compileRExprToChecked r rhs2) cs).map
        (fun _ => ()) := by
  obtain ⟨ev, h_rhs⟩ := id h_shape
  obtain ⟨ev2, h_rhs2⟩ := id h_shape2
  obtain ⟨h_agr, h_agv⟩ :=
    placeToRegChecked_flatten_agree (Place.deref P) RefKind.Shared cs
  rw [show flattenPlace (Place.deref P) = Place.deref (flattenPlace P) from rfl]
    at h_agr h_agv
  simp only [csMonad, compileRExprToChecked, h_rhs, h_rhs2, readRhsPre]
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

theorem compileStmt_readrhs_derefsrc_flatten_run
    {Γ : Ctx} {τ τs : LayoutTy}
    {dstLoc : Local Γ τ} {P : Place Γ (obseq.LayoutTy.PtrL τs)}
    {rhs rhs2 : RExpr Γ τ} {mk : Register → Rhs}
    (h_shape : ReadRhsShape rhs (.deref P) mk)
    (h_shape2 : ReadRhsShape rhs2 (.deref (flattenPlace P)) mk)
    (cs : CompilerState) :
    CheckedCompilerM.run
        (compileStmtChecked
          (Stmt.assign (.local dstLoc) rhs)) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.local dstLoc) rhs2)) cs := by
  simp only [csMonad, compileStmtChecked]
  have h_run := compileRExprToChecked_readrhs_flatten_run (h_shape := h_shape) (h_shape2 := h_shape2)
    ((ensureLocalRegE dstLoc).value cs).result.reg
    (CompilerM.run (ensureLocalRegE dstLoc) cs)
  have h_val := compileRExprToChecked_readrhs_flatten_valunit (h_shape := h_shape) (h_shape2 := h_shape2)
    ((ensureLocalRegE dstLoc).value cs).result.reg
    (CompilerM.run (ensureLocalRegE dstLoc) cs)
  cases hO : CheckedCompilerM.value
      (compileRExprToChecked ((ensureLocalRegE dstLoc).value cs).result.reg
        rhs)
      (CompilerM.run (ensureLocalRegE dstLoc) cs) with
  | error eO =>
      cases hF : CheckedCompilerM.value
          (compileRExprToChecked ((ensureLocalRegE dstLoc).value cs).result.reg
            rhs2)
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
            rhs2)
          (CompilerM.run (ensureLocalRegE dstLoc) cs) with
      | error eF =>
          exfalso
          rw [hO, hF] at h_val
          simp [Except.map] at h_val
      | ok oF =>
          simp only [hO, hF]
          exact h_run

theorem compileStmt_readrhs_derefsrc_flatten_value
    {Γ : Ctx} {τ τs : LayoutTy}
    {dstLoc : Local Γ τ} {P : Place Γ (obseq.LayoutTy.PtrL τs)}
    {rhs rhs2 : RExpr Γ τ} {mk : Register → Rhs}
    (h_shape : ReadRhsShape rhs (.deref P) mk)
    (h_shape2 : ReadRhsShape rhs2 (.deref (flattenPlace P)) mk)
    (cs : CompilerState) :
    ∀ so, CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.local dstLoc) rhs2)) cs
      = Except.ok so →
    ∃ so', CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.local dstLoc) rhs)) cs
      = Except.ok so' := by
  intro so h_so
  have h_val := compileRExprToChecked_readrhs_flatten_valunit (h_shape := h_shape) (h_shape2 := h_shape2)
    ((ensureLocalRegE dstLoc).value cs).result.reg
    (CompilerM.run (ensureLocalRegE dstLoc) cs)
  simp only [csMonad, compileStmtChecked] at h_so ⊢
  cases hO : CheckedCompilerM.value
      (compileRExprToChecked ((ensureLocalRegE dstLoc).value cs).result.reg
        rhs)
      (CompilerM.run (ensureLocalRegE dstLoc) cs) with
  | error eO =>
      exfalso
      cases hF : CheckedCompilerM.value
          (compileRExprToChecked ((ensureLocalRegE dstLoc).value cs).result.reg
            rhs2)
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

/-! ## Proj-topped sources over CHAIN bases: fragments over the opaque
    base lowering. `placeToRegChecked Shared (.proj B path)` runs B's
    code (the mother lemma owns it), then passes the register through
    at offset zero or mints a `Borrow(Shared)` otherwise; the statement
    adds the `Memcpy` and the cleanup `Die`. -/

theorem compileStmt_readrhs_projchain_zero_run
    {Γ : Ctx} {τ τs σb : LayoutTy}
    {dstLoc : Local Γ τ} {B : Place Γ σb} {path : PathTo σb τs}
    {cs : CompilerState} {dstReg : Register}
    {bOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared B)}
    {rhs : RExpr Γ τ} {mk : Register → Rhs}
    (h_shape : ReadRhsShape rhs (.proj B path) mk)
    (h_np : ∀ (σ' : LayoutTy) (b : Place Γ σ') (q : PathTo σ' σb), B = b.proj q → False)
    (h_off : pathOffset path = 0)
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = some (dstReg, τ))
    (h_bval : CheckedCompilerM.value (placeToRegChecked RefKind.Shared B) cs
      = Except.ok bOut)
    (h_bclean : bOut.result.cleanup = []) :
    CheckedCompilerM.run
        (compileStmtChecked
          (Stmt.assign (.local dstLoc) rhs)) cs
      = emit (emit
          { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs) with
              nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg + 1 }
          [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg)
            (mk bOut.result.reg)])
          [Instr.RStore (obseq.layoutToTyVal τ)
            (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg) dstReg] := by
  obtain ⟨ev, h_rhs⟩ := id h_shape
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_existing h_dst
  have h_run' : (ensureLocalRegE dstLoc cs).snd.val = cs := h_run
  have h_proj_eq := placeToRegChecked_proj_root_eq (Γ := Γ)
    (kind := RefKind.Shared) (base := B) path h_np
  simp only [compileStmtChecked, compileRExprToChecked, h_rhs, readRhsPre, csMonad, h_proj_eq, h_run, h_run', h_val, h_bval,
    h_off, dif_pos]
  simp [csRun, cleanupInstrs, h_bclean, emit_nil]

theorem compileStmt_readrhs_projchain_zero_value
    {Γ : Ctx} {τ τs σb : LayoutTy}
    {dstLoc : Local Γ τ} {B : Place Γ σb} {path : PathTo σb τs}
    {cs : CompilerState} {dstReg : Register}
    {bOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared B)}
    {rhs : RExpr Γ τ} {mk : Register → Rhs}
    (h_shape : ReadRhsShape rhs (.proj B path) mk)
    (h_np : ∀ (σ' : LayoutTy) (b : Place Γ σ') (q : PathTo σ' σb), B = b.proj q → False)
    (h_off : pathOffset path = 0)
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = some (dstReg, τ))
    (h_bval : CheckedCompilerM.value (placeToRegChecked RefKind.Shared B) cs
      = Except.ok bOut) :
    ∃ so, CheckedCompilerM.value
      (compileStmtChecked
        (Stmt.assign (.local dstLoc) rhs)) cs
      = Except.ok so := by
  obtain ⟨ev, h_rhs⟩ := id h_shape
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_existing h_dst
  have h_proj_eq := placeToRegChecked_proj_root_eq (Γ := Γ)
    (kind := RefKind.Shared) (base := B) path h_np
  simp only [compileStmtChecked, compileRExprToChecked, h_rhs, readRhsPre, csMonad, h_proj_eq, h_run, h_bval, h_off, dif_pos]
  exact ⟨_, rfl⟩

theorem compileStmt_readrhs_projchain_offset_run
    {Γ : Ctx} {τ τs σb : LayoutTy}
    {dstLoc : Local Γ τ} {B : Place Γ σb} {path : PathTo σb τs}
    {cs : CompilerState} {dstReg : Register}
    {bOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared B)}
    {rhs : RExpr Γ τ} {mk : Register → Rhs}
    (h_shape : ReadRhsShape rhs (.proj B path) mk)
    (h_np : ∀ (σ' : LayoutTy) (b : Place Γ σ') (q : PathTo σ' σb), B = b.proj q → False)
    (h_off : pathOffset path ≠ 0)
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = some (dstReg, τ))
    (h_bval : CheckedCompilerM.value (placeToRegChecked RefKind.Shared B) cs
      = Except.ok bOut)
    (h_bclean : bOut.result.cleanup = []) :
    CheckedCompilerM.run
        (compileStmtChecked
          (Stmt.assign (.local dstLoc) rhs)) cs
      = emit (emit
          { (emit
              { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs) with
                  nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg + 1 }
              [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg)
                (borrowRhs RefKind.Shared (blockSize τs) bOut.result.reg
                  (pathOffset path))]) with
              nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg + 1 + 1 }
          [Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg + 1))
            (mk
              (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg)),
           Instr.Die (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg) (blockSize τs)])
          [Instr.RStore (obseq.layoutToTyVal τ)
            (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg + 1)) dstReg] := by
  obtain ⟨ev, h_rhs⟩ := id h_shape
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_existing h_dst
  have h_run' : (ensureLocalRegE dstLoc cs).snd.val = cs := h_run
  have h_proj_eq := placeToRegChecked_proj_root_eq (Γ := Γ)
    (kind := RefKind.Shared) (base := B) path h_np
  simp only [compileStmtChecked, compileRExprToChecked, h_rhs, readRhsPre, csMonad, h_proj_eq, h_run, h_run', h_val, h_bval]
  simp [csRun, cleanupInstrs, h_bclean, emit_nil, h_off, borrowRhs]
  rfl

theorem compileStmt_readrhs_projchain_offset_value
    {Γ : Ctx} {τ τs σb : LayoutTy}
    {dstLoc : Local Γ τ} {B : Place Γ σb} {path : PathTo σb τs}
    {cs : CompilerState} {dstReg : Register}
    {bOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared B)}
    {rhs : RExpr Γ τ} {mk : Register → Rhs}
    (h_shape : ReadRhsShape rhs (.proj B path) mk)
    (h_np : ∀ (σ' : LayoutTy) (b : Place Γ σ') (q : PathTo σ' σb), B = b.proj q → False)
    (h_off : pathOffset path ≠ 0)
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = some (dstReg, τ))
    (h_bval : CheckedCompilerM.value (placeToRegChecked RefKind.Shared B) cs
      = Except.ok bOut) :
    ∃ so, CheckedCompilerM.value
      (compileStmtChecked
        (Stmt.assign (.local dstLoc) rhs)) cs
      = Except.ok so := by
  obtain ⟨ev, h_rhs⟩ := id h_shape
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_existing h_dst
  have h_proj_eq := placeToRegChecked_proj_root_eq (Γ := Γ)
    (kind := RefKind.Shared) (base := B) path h_np
  simp only [compileStmtChecked, compileRExprToChecked, h_rhs, readRhsPre, csMonad, h_proj_eq, h_run, h_bval, dif_neg h_off]
  exact ⟨_, rfl⟩

/-- REGIME P0→L over CHAIN bases, COLLAPSED 2026-08-29: `dst := copy
    B.f` at ZERO offset for ANY canonical chain base `B` — a bound
    local (the old P0→L), a deref chain (`y := copy (*p).f` at offset
    0), any depth. The projection passes the base register through, so
    this is the chain-src leaf with a `+ 0` on the resolution. -/
theorem copy_projchain_zero_simulation
    {τ τs σb : LayoutTy}
    {dstLoc : Local Γ τ} {B : Place Γ σb} {path : PathTo σb τs}
    {bD : mirlite.Binding}
    {rhs : RExpr Γ τ} {mk : Register → Rhs}
    (compProg : oseair.Prog)
    (h_shape : ReadRhsShape rhs (.proj B path) mk)
    (h_pkg : ReadPkgLowered compProg rhs (.proj B path) mk)
    (h_chain : PtrChain B)
    (h_off : pathOffset path = 0)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    {stmt0 : Stmt Γ}
    (h_stmt : prog.get? s_mir.pc = some stmt0)
    (h_run0 : ∀ cs, CheckedCompilerM.run (compileStmtChecked stmt0) cs
      = CheckedCompilerM.run
          (compileStmtChecked (Stmt.assign (.local dstLoc) rhs)) cs)
    (h_val0 : ∀ cs so, CheckedCompilerM.value
        (compileStmtChecked (Stmt.assign (.local dstLoc) rhs)) cs
        = Except.ok so →
      ∃ so', CheckedCompilerM.value (compileStmtChecked stmt0) cs
        = Except.ok so')
    (h_envD : mirlite.Env.lookup s_mir.env dstLoc = some bD)
    (h_step : mirlite.stepStmt MSB s_mir
      (.assign (.local dstLoc) rhs) = .ok s_mir') :
    ∃ (s_osea' : oseair.State MSB) (n : Nat),
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa ρt s_mir' s_osea' := by
  obtain ⟨csPrefix, ⟨h_csAt, h_pc⟩, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_tbd,
    h_alloc, h_unmap, h_prb⟩ := h_inv
  obtain ⟨dstReg, baseD, tagD, h_piD, h_entryD, h_raD, h_rtD, h_nwD, h_domD⟩ :=
    h_lbs dstLoc bD h_envD
  have h_baseD : baseD = bD.addr := (h_id_a _ _ h_raD).symm
  subst h_baseD
  have h_np := h_chain.not_proj
  -- §1 the destination is a BOUND local, so `preparePlaceAssign` is a no-op
  simp only [mirlite.stepStmt, mirlite.doAssign] at h_step
  cases h_prep : mirlite.preparePlaceAssign MSB s_mir (Place.local dstLoc) with
  | err msg => rw [h_prep] at h_step; simp at h_step
  | ok s1 =>
  rw [h_prep] at h_step
  have h_s1 : s1 = s_mir := by
    simp only [mirPrep, h_envD] at h_prep
    grind
  rw [h_s1] at h_step
  simp only at h_step
  -- §2 the source read, behind the rvalue's package
  cases h_eval : mirlite.evalRExpr MSB s_mir rhs with
  | err e => rw [h_eval] at h_step; simp at h_step
  | ok output =>
    rw [h_eval] at h_step
    simp only at h_step
    obtain ⟨h_mappedP, h_pkg'⟩ :=
      h_pkg _ _ s_mir s_osea csPrefix h_id_a h_wf_t h_tbd h_lbs h_prb h_sms h_alloc
        h_psim h_pc output h_eval
    have h_mappedB : PlaceInputsMapped csPrefix B := h_mappedP
    -- §3 compiler scaffolding: at zero offset the projection lowers as its base
    obtain ⟨sOut0, h_sval0⟩ := placeToRegChecked_ok_of_placeInputsMapped
      (cs := csPrefix) (kind := RefKind.Shared) h_mappedB
    obtain ⟨stmtOutC, h_stmtOutC⟩ :=
      compileStmt_readrhs_projchain_zero_value (h_shape := h_shape) h_np h_off h_piD
        h_sval0
    obtain ⟨stmtOut, h_stmtOut⟩ := h_val0 csPrefix stmtOutC h_stmtOutC
    obtain ⟨h_erun, -⟩ := ensureLocalRegE_existing h_piD
    have h_pv0 := placeToRegChecked_proj_zero_value (kind := RefKind.Shared)
      path h_np h_off h_sval0
    have h_pr0 := placeToRegChecked_proj_zero_run (kind := RefKind.Shared)
      path h_np h_off csPrefix
    obtain ⟨h_incrS, h_incrD⟩ :=
      readrhs_localdst_incrs (h_shape := h_shape) csPrefix h_erun h_pv0 h_pr0
        (h_run0 csPrefix)
    have h_instS :=
      (CodeIncluded.of_stmt h_comp h_csAt h_stmt h_stmtOut).mono h_incrS
    have h_instD :=
      (CodeIncluded.of_stmt h_comp h_csAt h_stmt h_stmtOut).mono h_incrD
    -- §4 the SOURCE package, at the projected place
    obtain ⟨h_sclean, nR, sR, perms₂, vals, h_ost, h_vlen, h_runR, h_prmR,
      h_regmonoR, h_lbsR, h_psimR, h_tbdR, h_smem, h_pcR, h_vregR, h_vbelow,
      h_valsRel⟩ :=
      h_pkg' _ h_pv0 (by rw [h_pr0]; exact h_instS) (by rw [h_pr0]; exact h_instD)
    rw [h_pr0] at h_prmR h_regmonoR h_lbsR h_pcR h_vbelow h_vregR
    have h_sclean0 : sOut0.result.cleanup = [] := h_sclean
    rw [h_ost] at h_step
    simp only [mirlite.resolvePlaceAcc, h_envD] at h_step
    -- the destination register still holds the root at the post-read state
    obtain ⟨dstReg2, baseD2, tagD2, h_piD2, h_entryD2, h_raD2, h_rtD2,
      h_nwD2, -⟩ := h_lbsR dstLoc bD h_envD
    have h_piD2' : getPlaceInfo csPrefix dstLoc.idx.1 = some (dstReg2, τ) := by
      show csPrefix.placeRegMap.lookup _ = _
      rw [← h_prmR]
      exact h_piD2
    have h_dr2 : dstReg2 = dstReg := by grind
    have h_baseD2 : baseD2 = bD.addr := (h_id_a _ _ h_raD2).symm
    have h_tag2 : tagD2 = tagD := by
      rw [h_rtD] at h_rtD2
      exact (Option.some.inj h_rtD2).symm
    rw [h_dr2, h_baseD2, h_tag2] at h_entryD2
    -- §5 the BOUND-root write seam at offset zero
    exact copy_bound_write_after_read (τ := τ) (dbase := bD.addr) (dtag := bD.tag)
      (dsize := blockSize τ) compProg h_comp h_stmt h_csAt h_stmtOut h_id_a h_wf_t
      h_unmap h_prb (dstReg := dstReg) 0 h_rtD  h_domD 0
      (by simp) h_runR h_entryD2 (by rw [h_smem]; exact h_sms)
      (by rw [h_smem]; exact h_alloc) h_prmR h_regmonoR h_lbsR h_psimR h_tbdR
      h_pcR h_vregR h_vbelow h_vlen
      (by
        rw [projDstTail_zero]
        exact (h_run0 csPrefix).trans
          (compileStmt_readrhs_projchain_zero_run (h_shape := h_shape) h_np h_off h_piD
            h_sval0 h_sclean0))
      output.values_len (by simp) rfl rfl rfl h_valsRel h_step

theorem copy_projchain_offset_simulation
    {τ τs σb : LayoutTy}
    {dstLoc : Local Γ τ} {B : Place Γ σb} {path : PathTo σb τs}
    {bD : mirlite.Binding}
    {rhs : RExpr Γ τ} {mk : Register → Rhs}
    (compProg : oseair.Prog)
    (h_shape : ReadRhsShape rhs (.proj B path) mk)
    (h_pkg : ReadPkgProjOffset compProg rhs B path mk)
    (h_chain : PtrChain B)
    (h_off : pathOffset path ≠ 0)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    {stmt0 : Stmt Γ}
    (h_stmt : prog.get? s_mir.pc = some stmt0)
    (h_run0 : ∀ cs, CheckedCompilerM.run (compileStmtChecked stmt0) cs
      = CheckedCompilerM.run
          (compileStmtChecked (Stmt.assign (.local dstLoc) rhs)) cs)
    (h_val0 : ∀ cs so, CheckedCompilerM.value
        (compileStmtChecked (Stmt.assign (.local dstLoc) rhs)) cs
        = Except.ok so →
      ∃ so', CheckedCompilerM.value (compileStmtChecked stmt0) cs
        = Except.ok so')
    (h_envD : mirlite.Env.lookup s_mir.env dstLoc = some bD)
    (h_step : mirlite.stepStmt MSB s_mir
      (.assign (.local dstLoc) rhs) = .ok s_mir') :
    ∃ (s_osea' : oseair.State MSB) (n : Nat),
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa ρt s_mir' s_osea' := by
  obtain ⟨csPrefix, ⟨h_csAt, h_pc⟩, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_tbd,
    h_alloc, h_unmap, h_prb⟩ := h_inv
  obtain ⟨dstReg, baseD, tagD, h_piD, h_entryD, h_raD, h_rtD, h_nwD, h_domD⟩ :=
    h_lbs dstLoc bD h_envD
  have h_baseD : baseD = bD.addr := (h_id_a _ _ h_raD).symm
  subst h_baseD
  have h_np := h_chain.not_proj
  -- §1 the destination is a BOUND local, so `preparePlaceAssign` is a no-op
  simp only [mirlite.stepStmt, mirlite.doAssign] at h_step
  cases h_prep : mirlite.preparePlaceAssign MSB s_mir (Place.local dstLoc) with
  | err msg => rw [h_prep] at h_step; simp at h_step
  | ok s1 =>
  rw [h_prep] at h_step
  have h_s1 : s1 = s_mir := by
    simp only [mirPrep, h_envD] at h_prep
    grind
  rw [h_s1] at h_step
  simp only at h_step
  -- §2 the source read, behind the rvalue's package
  cases h_eval : mirlite.evalRExpr MSB s_mir rhs with
  | err e => rw [h_eval] at h_step; simp at h_step
  | ok output =>
    rw [h_eval] at h_step
    simp only at h_step
    obtain ⟨h_mappedP, h_pkg'⟩ :=
      h_pkg _ _ s_mir s_osea csPrefix h_id_a h_wf_t h_tbd h_lbs h_prb h_sms h_alloc
        h_psim h_pc output h_eval
    have h_mappedB : PlaceInputsMapped csPrefix B := h_mappedP
    -- §3 compiler scaffolding: the projection's own `Borrow`/`Die` bracket
    obtain ⟨sOut0, h_sval0⟩ := placeToRegChecked_ok_of_placeInputsMapped
      (cs := csPrefix) (kind := RefKind.Shared) h_mappedB
    obtain ⟨stmtOutC, h_stmtOutC⟩ :=
      compileStmt_readrhs_projchain_offset_value (h_shape := h_shape) h_np h_off
        h_piD h_sval0
    obtain ⟨stmtOut, h_stmtOut⟩ := h_val0 csPrefix stmtOutC h_stmtOutC
    obtain ⟨h_erun, -⟩ := ensureLocalRegE_existing h_piD
    obtain ⟨sOutP, h_svalP, h_regP, h_clP⟩ :=
      placeToRegChecked_proj_offset_value (kind := RefKind.Shared) path h_np h_off
        h_sval0
    obtain ⟨h_incrS', h_incrD⟩ :=
      readrhs_localdst_incrs (h_shape := h_shape) csPrefix h_erun h_svalP
        (placeToRegChecked_proj_offset_run (kind := RefKind.Shared) path h_np h_off
          h_sval0) (h_run0 csPrefix)
    have h_incrS : StateIncr
        (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix)
        (CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix) :=
      StateIncr.trans
        (StateIncr.trans (freshReg_state_incr _) (emit_state_incr _ _)) h_incrS'
    have h_instS :=
      (CodeIncluded.of_stmt h_comp h_csAt h_stmt h_stmtOut).mono h_incrS
    have h_instD :=
      (CodeIncluded.of_stmt h_comp h_csAt h_stmt h_stmtOut).mono h_incrD
    -- §4 the SOURCE package: Borrow off the base, the rvalue's step, Die
    obtain ⟨h_sclean, nR, sR, perms₂, vals, h_ost, h_vlen, h_runR, h_prmR,
      h_regmonoR, h_lbsR, h_psimR, h_tbdR, h_smem, h_pcR, h_vregR, h_vbelow,
      h_valsRel⟩ :=
      h_pkg' sOut0 h_sval0 _ h_regP h_clP h_instS h_instD
    rw [h_ost] at h_step
    simp only [mirlite.resolvePlaceAcc, h_envD] at h_step
    -- the destination register still holds the root at the post-read state
    obtain ⟨dstReg2, baseD2, tagD2, h_piD2, h_entryD2, h_raD2, h_rtD2,
      h_nwD2, -⟩ := h_lbsR dstLoc bD h_envD
    have h_piD2' : getPlaceInfo csPrefix dstLoc.idx.1 = some (dstReg2, τ) := by
      show csPrefix.placeRegMap.lookup _ = _
      rw [← h_prmR]
      exact h_piD2
    have h_dr2 : dstReg2 = dstReg := by grind
    have h_baseD2 : baseD2 = bD.addr := (h_id_a _ _ h_raD2).symm
    have h_tag2 : tagD2 = tagD := by
      rw [h_rtD] at h_rtD2
      exact (Option.some.inj h_rtD2).symm
    rw [h_dr2, h_baseD2, h_tag2] at h_entryD2
    -- §5 the BOUND-root write seam at offset zero
    exact copy_bound_write_after_read (τ := τ) (dbase := bD.addr) (dtag := bD.tag)
      (dsize := blockSize τ) compProg h_comp h_stmt h_csAt h_stmtOut h_id_a h_wf_t
      h_unmap h_prb (dstReg := dstReg) 0 h_rtD  h_domD 0
      (by simp) h_runR h_entryD2 (by rw [h_smem]; exact h_sms)
      (by rw [h_smem]; exact h_alloc) h_prmR h_regmonoR h_lbsR h_psimR h_tbdR
      h_pcR h_vregR h_vbelow h_vlen
      (by
        rw [projDstTail_zero]
        exact (h_run0 csPrefix).trans
          (compileStmt_readrhs_projchain_offset_run (h_shape := h_shape) h_np h_off h_piD
            h_sval0 h_sclean))
      output.values_len (by simp) rfl rfl rfl h_valsRel h_step

/-! ## Flatten transfer for a copy source of ANY shape -/

theorem compileRExprToChecked_readrhs_anyflatten_run
    {Γ : Ctx} {τ τs : LayoutTy} (src : Place Γ τs)
    (r : Register) (cs : CompilerState)
    {rhs rhs2 : RExpr Γ τ} {mk : Register → Rhs}
    (h_shape : ReadRhsShape rhs src mk)
    (h_shape2 : ReadRhsShape rhs2 (flattenPlace src) mk) :
    CheckedCompilerM.run (compileRExprToChecked r rhs) cs
      = CheckedCompilerM.run
          (compileRExprToChecked r rhs2) cs := by
  obtain ⟨ev, h_rhs⟩ := id h_shape
  obtain ⟨ev2, h_rhs2⟩ := id h_shape2
  obtain ⟨h_agr, h_agv⟩ := placeToRegChecked_flatten_agree src RefKind.Shared cs
  simp only [csMonad, compileRExprToChecked, h_rhs, h_rhs2, readRhsPre]
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

theorem compileRExprToChecked_readrhs_anyflatten_valunit
    {Γ : Ctx} {τ τs : LayoutTy} (src : Place Γ τs)
    (r : Register) (cs : CompilerState)
    {rhs rhs2 : RExpr Γ τ} {mk : Register → Rhs}
    (h_shape : ReadRhsShape rhs src mk)
    (h_shape2 : ReadRhsShape rhs2 (flattenPlace src) mk) :
    (CheckedCompilerM.value (compileRExprToChecked r rhs) cs).map
      (fun _ => ())
      = (CheckedCompilerM.value
          (compileRExprToChecked r rhs2) cs).map
        (fun _ => ()) := by
  obtain ⟨ev, h_rhs⟩ := id h_shape
  obtain ⟨ev2, h_rhs2⟩ := id h_shape2
  obtain ⟨h_agr, h_agv⟩ := placeToRegChecked_flatten_agree src RefKind.Shared cs
  simp only [csMonad, compileRExprToChecked, h_rhs, h_rhs2, readRhsPre]
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

theorem compileStmt_readrhs_srcflatten_run
    {Γ : Ctx} {τ τs : LayoutTy} {dstLoc : Local Γ τ} (src : Place Γ τs)
    (cs : CompilerState)
    {rhs rhs2 : RExpr Γ τ} {mk : Register → Rhs}
    (h_shape : ReadRhsShape rhs src mk)
    (h_shape2 : ReadRhsShape rhs2 (flattenPlace src) mk) :
    CheckedCompilerM.run
        (compileStmtChecked (Stmt.assign (.local dstLoc) rhs)) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.local dstLoc) rhs2)) cs := by
  obtain ⟨ev, h_rhs⟩ := id h_shape
  obtain ⟨ev2, h_rhs2⟩ := id h_shape2
  simp only [csMonad, compileStmtChecked]
  have h_run := compileRExprToChecked_readrhs_anyflatten_run
    (h_shape := h_shape) (h_shape2 := h_shape2) src
    ((ensureLocalRegE dstLoc).value cs).result.reg
    (CompilerM.run (ensureLocalRegE dstLoc) cs)
  have h_val := compileRExprToChecked_readrhs_anyflatten_valunit
    (h_shape := h_shape) (h_shape2 := h_shape2) src
    ((ensureLocalRegE dstLoc).value cs).result.reg
    (CompilerM.run (ensureLocalRegE dstLoc) cs)
  cases hO : CheckedCompilerM.value
      (compileRExprToChecked ((ensureLocalRegE dstLoc).value cs).result.reg
        rhs)
      (CompilerM.run (ensureLocalRegE dstLoc) cs) with
  | error eO =>
      cases hF : CheckedCompilerM.value
          (compileRExprToChecked ((ensureLocalRegE dstLoc).value cs).result.reg
            rhs2)
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
            rhs2)
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
theorem compileStmt_readrhs_srcflatten_value
    {Γ : Ctx} {τ τs : LayoutTy} {dstLoc : Local Γ τ} (src : Place Γ τs)
    (cs : CompilerState)
    {rhs rhs2 : RExpr Γ τ} {mk : Register → Rhs}
    (h_shape : ReadRhsShape rhs src mk)
    (h_shape2 : ReadRhsShape rhs2 (flattenPlace src) mk)
    (h_ex : ∃ so, CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.local dstLoc) rhs2)) cs
      = Except.ok so) :
    ∃ so', CheckedCompilerM.value
        (compileStmtChecked (Stmt.assign (.local dstLoc) rhs)) cs
      = Except.ok so' := by
  obtain ⟨ev, h_rhs⟩ := id h_shape
  obtain ⟨ev2, h_rhs2⟩ := id h_shape2
  obtain ⟨so, h_so⟩ := h_ex
  have h_val := compileRExprToChecked_readrhs_anyflatten_valunit
    (h_shape := h_shape) (h_shape2 := h_shape2) src
    ((ensureLocalRegE dstLoc).value cs).result.reg
    (CompilerM.run (ensureLocalRegE dstLoc) cs)
  simp only [csMonad, compileStmtChecked] at h_so ⊢
  cases hO : CheckedCompilerM.value
      (compileRExprToChecked ((ensureLocalRegE dstLoc).value cs).result.reg
        rhs)
      (CompilerM.run (ensureLocalRegE dstLoc) cs) with
  | error eO =>
      exfalso
      cases hF : CheckedCompilerM.value
          (compileRExprToChecked ((ensureLocalRegE dstLoc).value cs).result.reg
            rhs2)
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

theorem compileStmt_readrhs_fresh_chainsrc_run
    {Γ : Ctx} {τ τs : LayoutTy}
    {dstLoc : Local Γ τ} {src : Place Γ τs}
    {cs : CompilerState}
    {sOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared src)}
    {rhs : RExpr Γ τ} {mk : Register → Rhs}
    (h_shape : ReadRhsShape rhs src mk)
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = none)
    (h_sval : CheckedCompilerM.value (placeToRegChecked RefKind.Shared src)
      (setPlaceInfo
        (emit { cs with nextReg := cs.nextReg + 1 }
          [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal τ))])
        dstLoc.idx.1 (Register.R cs.nextReg, τ))
      = Except.ok sOut)
    (h_sclean : sOut.result.cleanup = []) :
    CheckedCompilerM.run
        (compileStmtChecked (Stmt.assign (.local dstLoc) rhs)) cs
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
            (mk sOut.result.reg)])
          [Instr.RStore (obseq.layoutToTyVal τ)
            (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src)
          (setPlaceInfo
            (emit { cs with nextReg := cs.nextReg + 1 }
              [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal τ))])
            dstLoc.idx.1 (Register.R cs.nextReg, τ))).nextReg) (Register.R cs.nextReg)] := by
  obtain ⟨ev, h_rhs⟩ := id h_shape
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_fresh (loc := dstLoc) h_dst
  simp only [compileStmtChecked, compileRExprToChecked, h_rhs, readRhsPre, csMonad, h_run, h_val, h_sval]
  simp [csRun, cleanupInstrs, h_sclean, emit_nil]

theorem compileStmt_readrhs_fresh_chainsrc_value
    {Γ : Ctx} {τ τs : LayoutTy}
    {dstLoc : Local Γ τ} {src : Place Γ τs}
    {cs : CompilerState}
    {sOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared src)}
    {rhs : RExpr Γ τ} {mk : Register → Rhs}
    (h_shape : ReadRhsShape rhs src mk)
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = none)
    (h_sval : CheckedCompilerM.value (placeToRegChecked RefKind.Shared src)
      (setPlaceInfo
        (emit { cs with nextReg := cs.nextReg + 1 }
          [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal τ))])
        dstLoc.idx.1 (Register.R cs.nextReg, τ))
      = Except.ok sOut) :
    ∃ so, CheckedCompilerM.value
      (compileStmtChecked (Stmt.assign (.local dstLoc) rhs)) cs
      = Except.ok so := by
  obtain ⟨ev, h_rhs⟩ := id h_shape
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_fresh (loc := dstLoc) h_dst
  simp only [compileStmtChecked, compileRExprToChecked, h_rhs, readRhsPre, csMonad, h_run, h_sval]
  exact ⟨_, rfl⟩

/-- The SOURCE package for `copy` of a chain-class source: lower the
    source, transport the read, execute the `Load`. Its conclusion is
    exactly the post-read bundle `copy_chainwrite_after_read` consumes,
    so a leaf is source-package → seam → wrap.

    Stated over an abstract start `(sM, sA, csA)` — the mirlite state
    the source resolves in, and the target state/compiler state the
    source lowering starts from — NOT the ambient `s_mir`/`s_osea`/
    `csPrefix`: a fresh-destination leaf calls it at its post-`Alloc`
    states, under its extended renames, exactly as a bound-destination
    leaf calls it at the statement's prefix. The two code-inclusion
    facts it needs come in as hypotheses (from `copy_*_incrs`), the
    second in its symbolic-cleanup form because the source cleanup is
    only known empty once the mother has run. -/
theorem copy_chainsrc_read
    {τ : LayoutTy} {src : Place Γ τ}
    (compProg : oseair.Prog) (h_slower : LoweringSimAny compProg src)
    (sM : mirlite.State MSB Γ) (sA : oseair.State MSB) (csA : CompilerState)
    (h_id_a : IdentityOnDomain ρa) (h_wf_t : TagRenameWF ρt)
    (h_tbd : TagRenameBounded ρt sM.perms.NextTag sA.perms.NextTag)
    (h_lbs : LocalBindingSim ρa ρt sM.env sA csA)
    (h_prb : PlaceRegMapBound csA)
    (h_sms : SourceMemSim ρa ρt sM.mem sA.mem)
    (h_psim : PermSim ρt sM.perms sA.perms)
    (h_pc : sA.pc = csA.nextLabel)
    {rs : mirlite.PlaceRes} {permsS perms₂ : MSB.State}
    (h_sres : mirlite.resolvePlaceAcc MSB sM src = .ok (rs, permsS))
    (h_fit : ¬ (rs.addr + blockSize τ > rs.allocBase + rs.allocSize))
    (h_read_src : MSB.read permsS rs.addr (blockSize τ) rs.tag = .ok perms₂)
    {sOut0 : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared src)}
    (h_sval0 : CheckedCompilerM.value (placeToRegChecked RefKind.Shared src) csA
      = Except.ok sOut0)
    (h_instS : ∀ q instr,
      q < (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextLabel →
      (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).code q = some instr →
      compProg q = some instr)
    (h_instD : ∀ q instr,
      q < (emit
        { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA) with
          nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg + 1 }
        ([Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg)
            (Rhs.Load (layoutToTyVal τ) sOut0.result.reg)]
          ++ cleanupInstrs sOut0.result.cleanup)).nextLabel →
      (emit
        { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA) with
          nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg + 1 }
        ([Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg)
            (Rhs.Load (layoutToTyVal τ) sOut0.result.reg)]
          ++ cleanupInstrs sOut0.result.cleanup)).code q = some instr →
      compProg q = some instr) :
    sOut0.result.cleanup = [] ∧
    ∃ (n1 : Nat) (s_mid1 : oseair.State MSB) (p2 : MSB.State),
      oseair.runN MSB (n1 + 1) sA compProg = oseair.Result.Ok
        { s_mid1 with
          perms := p2,
          reg := oseair.RegMap.insert s_mid1.reg
            (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg)
            (layoutToTyVal τ, (oseair.readWordSeq s_mid1.mem rs.addr (blockSize τ))),
          pc := s_mid1.pc + 1 } ∧
      (emit
        { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA) with
          nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg + 1 }
        [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg)
          (Rhs.Load (layoutToTyVal τ) sOut0.result.reg)]).placeRegMap = csA.placeRegMap ∧
      csA.nextReg ≤ (emit
        { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA) with
          nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg + 1 }
        [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg)
          (Rhs.Load (layoutToTyVal τ) sOut0.result.reg)]).nextReg ∧
      LocalBindingSim ρa ρt sM.env
        { s_mid1 with
          perms := p2,
          reg := oseair.RegMap.insert s_mid1.reg
            (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg)
            (layoutToTyVal τ, (oseair.readWordSeq s_mid1.mem rs.addr (blockSize τ))),
          pc := s_mid1.pc + 1 }
        (emit
          { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA) with
            nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg + 1 }
          [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg)
            (Rhs.Load (layoutToTyVal τ) sOut0.result.reg)]) ∧
      PermSim ρt perms₂ p2 ∧
      TagRenameBounded ρt perms₂.NextTag p2.NextTag ∧
      s_mid1.mem = sA.mem ∧
      s_mid1.pc = (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextLabel ∧
      s_mid1.pc + 1 = (emit
        { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA) with
          nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg + 1 }
        [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg)
          (Rhs.Load (layoutToTyVal τ) sOut0.result.reg)]).nextLabel ∧
      RegisterBelow (emit
        { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA) with
          nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg + 1 }
        [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg)
          (Rhs.Load (layoutToTyVal τ) sOut0.result.reg)]).nextReg
        (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg) ∧
      ListRel (MemValSim ρa ρt)
        (mirlite.readWordSeq sM.mem rs.addr (blockSize τ))
        (oseair.readWordSeq s_mid1.mem rs.addr (blockSize τ)) := by
  -- the source mother
  obtain ⟨sOut, n1, s_mid1, tres, h_sval, h_sclean, h_srun, h_spc, h_smem,
    h_spsim, h_snt1, h_snt2, h_slbs, h_sentry, h_srt, h_sle, h_srange,
    h_sbelow, h_sprm, h_sregmono, h_slabmono, h_sframe, -⟩ :=
    h_slower _ _ _ h_id_a h_wf_t RefKind.Shared csA sA
      rs permsS h_sres h_tbd h_lbs h_prb h_sms h_psim h_pc h_instS
  have h_cancelS := resolvedAddr_cancel h_sle
  have h_ts : obseq.typeSize (layoutToTyVal τ) = blockSize τ := by
    simp [blockSize]
  have h_sOut_eq : sOut = sOut0 := by
    rw [h_sval0] at h_sval
    exact (Except.ok.inj h_sval).symm
  subst h_sOut_eq
  refine ⟨h_sclean, n1, s_mid1, ?_⟩
  -- code inclusion at the post-Load state, cleanup now known empty
  have h_instD' : ∀ q instr,
      q < (emit
        { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA) with
          nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg + 1 }
        [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg)
          (Rhs.Load (layoutToTyVal τ) sOut.result.reg)]).nextLabel →
      (emit
        { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA) with
          nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg + 1 }
        [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg)
          (Rhs.Load (layoutToTyVal τ) sOut.result.reg)]).code q = some instr →
      compProg q = some instr := by
    simpa only [csCleanup, h_sclean, List.append_nil] using h_instD
  -- the READ: transport, then execute the `Load`
  obtain ⟨p2, h_read_tgt, h_psim2⟩ :=
    sb_read_respects_PermSim h_spsim h_wf_t h_srt h_read_src
  have h_code1 : compProg s_mid1.pc
      = some (Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg)
          (Rhs.Load (layoutToTyVal τ) sOut.result.reg)) := by
    rw [h_spc]
    refine h_instD' _ _ ?_ ?_
    · simp only [emit, List.length_cons, List.length_nil]
      omega
    · have h := emit_code_at_new
        { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA) with
          nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg + 1 }
        [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg)
          (Rhs.Load (layoutToTyVal τ) sOut.result.reg)]
        (k := 0) (by simp)
      simpa using h
  have h_read2t : MSB.read s_mid1.perms
      (rs.allocBase + (rs.addr - rs.allocBase))
      (obseq.typeSize (layoutToTyVal τ)) tres = .ok p2 := by
    rw [h_ts, h_cancelS]
    exact h_read_tgt
  have h_run1 := runN_Assgn_Load_ptr_step compProg s_mid1
    (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg) sOut.result.reg
    (layoutToTyVal τ) h_code1 h_sentry (by rw [h_ts]; grind) h_read2t
  rw [h_ts, h_cancelS] at h_run1
  refine ⟨p2, oseair_runN_trans h_srun h_run1,
    (by simp only [emit]; exact h_sprm),
    (by simp only [emit]; exact Nat.le_trans h_sregmono (Nat.le_succ _)),
    ?_, h_psim2,
    (by rw [sb_read_NextTag h_read_src, sb_read_NextTag h_read_tgt, h_snt1]
        exact TagRenameBounded.mono h_tbd (Nat.le_refl _) h_snt2),
    h_smem, h_spc,
    (by rw [h_spc]; simp only [emit, List.length_cons, List.length_nil]),
    (by show _ < _; simp only [emit]; omega),
    (by rw [h_smem]; exact readWordSeq_sim h_id_a h_sms (blockSize τ) rs.addr)⟩
  -- the post-Load LocalBindingSim: the fresh temp is above every mapped register
  have h_ins : LocalBindingSim ρa ρt sM.env
      { s_mid1 with
          perms := p2,
          reg := oseair.RegMap.insert s_mid1.reg
            (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg)
            (layoutToTyVal τ, (oseair.readWordSeq s_mid1.mem rs.addr (blockSize τ))),
          pc := s_mid1.pc + 1 } csA :=
    LocalBindingSim.insert_fresh_reg h_slbs h_prb h_sregmono rfl
  intro τ' loc' binding' h_env'
  obtain ⟨reg', base', tag', h_pi', h_entry', h_ra', h_rt', h_nw', h_dom'⟩ :=
    h_ins loc' binding' h_env'
  refine ⟨reg', base', tag', ?_, h_entry', h_ra', h_rt', h_nw', h_dom'⟩
  show getPlaceInfo _ loc'.idx.1 = _
  simp only [getPlaceInfo, emit]
  rw [h_sprm]
  exact h_pi'

/-- **The projected-source read, at an ABSTRACT start state** — the
    second of copy's two source packages, and the twin of
    `copy_chainsrc_read` for a source projected at a NONZERO offset.

    The compiled shape is three instructions rather than one: the
    projection's own `Borrow` off the chain base, the `Load` through it,
    and the `Die` that retires it (BRIDGE 1S on the mirlite side — the
    borrow is taken, read through, and retired before the destination
    lowering starts). The output bundle is the one
    `copy_chainwrite_after_read` consumes, so a leaf on this source is
    again a package call, a seam call, and nothing else.

    Like the chain package this is stated at an abstract
    `(sM, sA, csA)`, which is what lets the FRESH families call it at
    their post-`Alloc` states. -/
theorem copy_projsrc_offset_read
    {τ σs : LayoutTy} {B : Place Γ σs} {spath : PathTo σs τ}
    (compProg : oseair.Prog) (h_slower : LoweringSimAny compProg B)
    (sM : mirlite.State MSB Γ) (sA : oseair.State MSB) (csA : CompilerState)
    (h_id_a : IdentityOnDomain ρa) (h_wf_t : TagRenameWF ρt)
    (h_tbd : TagRenameBounded ρt sM.perms.NextTag sA.perms.NextTag)
    (h_lbs : LocalBindingSim ρa ρt sM.env sA csA)
    (h_prb : PlaceRegMapBound csA)
    (h_sms : SourceMemSim ρa ρt sM.mem sA.mem)
    (h_psim : PermSim ρt sM.perms sA.perms)
    (h_pc : sA.pc = csA.nextLabel)
    {rs : mirlite.PlaceRes} {permsS perms₂ : MSB.State}
    (h_sres : mirlite.resolvePlaceAcc MSB sM B = .ok (rs, permsS))
    (h_fit : ¬ (rs.addr + PathTo.offset spath + blockSize τ
      > rs.allocBase + rs.allocSize))
    (h_read_src : MSB.read permsS (rs.addr + PathTo.offset spath)
      (blockSize τ) rs.tag = .ok perms₂)
    {sOut0 : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared B)}
    (h_sval0 : CheckedCompilerM.value (placeToRegChecked RefKind.Shared B) csA
      = Except.ok sOut0)
    {sOutP : ResultWithEvidence PtrResult
      (PlaceToRegEvidence RefKind.Shared (Place.proj B spath))}
    (h_regP : sOutP.result.reg = Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)
    (h_clP : sOutP.result.cleanup
      = sOut0.result.cleanup ++ [(Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg, blockSize τ)])
    (h_instS : CodeIncluded compProg (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA))
    (h_instCS : CodeIncluded compProg (emit
        { (emit
        { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1 }
        [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)
          (borrowRhs RefKind.Shared (blockSize τ) sOut0.result.reg (pathOffset spath))]) with
          nextReg := (emit
        { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1 }
        [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)
          (borrowRhs RefKind.Shared (blockSize τ) sOut0.result.reg (pathOffset spath))]).nextReg + 1 }
        ([Instr.Assgn (Register.R (emit
        { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1 }
        [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)
          (borrowRhs RefKind.Shared (blockSize τ) sOut0.result.reg (pathOffset spath))]).nextReg)
            (Rhs.Load (layoutToTyVal τ) sOutP.result.reg)]
          ++ cleanupInstrs sOutP.result.cleanup))) :
    sOut0.result.cleanup = [] ∧
    ∃ (n : Nat) (s_mid1 : oseair.State MSB) (q3 : MSB.State),
      oseair.runN MSB n sA compProg = oseair.Result.Ok
        { s_mid1 with
          perms := q3,
          reg := (oseair.RegMap.insert (oseair.RegMap.insert s_mid1.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)
              (obseq.TyVal.PTy, [Val.Ptr rs.allocBase (rs.addr - rs.allocBase + pathOffset spath)
                rs.allocSize s_mid1.perms.NextTag])) (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1))
            (layoutToTyVal τ, (oseair.readWordSeq s_mid1.mem (rs.addr + pathOffset spath) (blockSize τ)))),
          pc := s_mid1.pc + 1 + 1 + 1 } ∧
      (emit
        { (emit
        { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1 }
        [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)
          (borrowRhs RefKind.Shared (blockSize τ) sOut0.result.reg (pathOffset spath))]) with
          nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1 + 1 }
        [Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1))
            (Rhs.Load (layoutToTyVal τ) (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)),
          Instr.Die (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg) (blockSize τ)]).placeRegMap = csA.placeRegMap ∧
      csA.nextReg ≤ (emit
        { (emit
        { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1 }
        [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)
          (borrowRhs RefKind.Shared (blockSize τ) sOut0.result.reg (pathOffset spath))]) with
          nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1 + 1 }
        [Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1))
            (Rhs.Load (layoutToTyVal τ) (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)),
          Instr.Die (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg) (blockSize τ)]).nextReg ∧
      LocalBindingSim ρa ρt sM.env
        { s_mid1 with
          perms := q3,
          reg := (oseair.RegMap.insert (oseair.RegMap.insert s_mid1.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)
              (obseq.TyVal.PTy, [Val.Ptr rs.allocBase (rs.addr - rs.allocBase + pathOffset spath)
                rs.allocSize s_mid1.perms.NextTag])) (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1))
            (layoutToTyVal τ, (oseair.readWordSeq s_mid1.mem (rs.addr + pathOffset spath) (blockSize τ)))),
          pc := s_mid1.pc + 1 + 1 + 1 }
        (emit
        { (emit
        { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1 }
        [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)
          (borrowRhs RefKind.Shared (blockSize τ) sOut0.result.reg (pathOffset spath))]) with
          nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1 + 1 }
        [Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1))
            (Rhs.Load (layoutToTyVal τ) (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)),
          Instr.Die (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg) (blockSize τ)]) ∧
      PermSim ρt perms₂ q3 ∧
      TagRenameBounded ρt perms₂.NextTag q3.NextTag ∧
      s_mid1.mem = sA.mem ∧
      s_mid1.pc = (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextLabel ∧
      s_mid1.pc + 1 + 1 + 1 = (emit
        { (emit
        { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1 }
        [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)
          (borrowRhs RefKind.Shared (blockSize τ) sOut0.result.reg (pathOffset spath))]) with
          nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1 + 1 }
        [Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1))
            (Rhs.Load (layoutToTyVal τ) (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)),
          Instr.Die (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg) (blockSize τ)]).nextLabel ∧
      RegisterBelow (emit
        { (emit
        { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1 }
        [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)
          (borrowRhs RefKind.Shared (blockSize τ) sOut0.result.reg (pathOffset spath))]) with
          nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1 + 1 }
        [Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1))
            (Rhs.Load (layoutToTyVal τ) (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)),
          Instr.Die (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg) (blockSize τ)]).nextReg (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1)) ∧
      ListRel (MemValSim ρa ρt)
        (mirlite.readWordSeq sM.mem (rs.addr + pathOffset spath) (blockSize τ))
        (oseair.readWordSeq s_mid1.mem (rs.addr + pathOffset spath)
          (blockSize τ)) := by
  -- the source mother, on the chain BASE
  obtain ⟨sOut, n1, s_mid1, tres, h_sval, h_sclean, h_srun, h_spc, h_smem,
    h_spsim, h_snt1, h_snt2, h_slbs, h_sentry, h_srt, h_sle, h_srange,
    h_sbelow, h_sprm, h_sregmono, h_slabmono, h_sframe, -⟩ :=
    h_slower _ _ _ h_id_a h_wf_t RefKind.Shared csA sA
      rs permsS h_sres h_tbd h_lbs h_prb h_sms h_psim h_pc h_instS
  have h_cancelS := resolvedAddr_cancel h_sle
  have h_ts : obseq.typeSize (layoutToTyVal τ) = blockSize τ := by
    simp [blockSize]
  have h_sOut_eq : sOut = sOut0 := by
    rw [h_sval0] at h_sval
    exact (Except.ok.inj h_sval).symm
  subst h_sOut_eq
  refine ⟨h_sclean, ?_⟩
  -- code inclusion at the post-`Die` state: the projection's own `Die` is
  -- all that is left of the symbolic cleanup once the chain's is empty
  have h_instCS2 : CodeIncluded compProg
      (emit
        { (emit
        { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1 }
        [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)
          (borrowRhs RefKind.Shared (blockSize τ) sOut.result.reg (pathOffset spath))]) with
          nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1 + 1 }
        [Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1))
            (Rhs.Load (layoutToTyVal τ) (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)),
          Instr.Die (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg) (blockSize τ)]) := by
    have h := h_instCS
    rw [h_regP, h_clP] at h
    simp only [csCleanup, h_sclean, List.nil_append, List.append_nil,
      List.reverse_cons, List.map_cons] at h
    csnorm at h ⊢
    exact h
  -- BRIDGE 1S: the borrow is taken, read through, and retired
  obtain ⟨p2, h_read_tgt, h_psim2⟩ :=
    sb_read_respects_PermSim h_spsim h_wf_t h_srt h_read_src
  have h_tbd2 : TagRenameBounded ρt permsS.NextTag s_mid1.perms.NextTag := by
    rw [h_snt1]
    exact TagRenameBounded.mono h_tbd (Nat.le_refl _) h_snt2
  obtain ⟨q1, q2, q3, h_ref_tgt, h_rd1, h_die1, h_psim2q, h_ntle⟩ :=
    bridge1S_of_read h_spsim h_wf_t h_tbd2 h_read_tgt h_psim2
  -- the three source instructions
  have h_code1 : compProg s_mid1.pc
      = some (Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)
          (borrowRhs RefKind.Shared (blockSize τ) sOut.result.reg
            (pathOffset spath))) := by
    rw [h_spc]
    refine h_instCS2 _ _ ?_ ?_
    · simp only [emit, List.length_cons, List.length_nil]
      omega
    · rw [emit_code_lt_nextLabel _ _ (by
        simp only [emit, List.length_cons, List.length_nil]; omega)]
      have h := emit_code_at_new
        { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1 }
        [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)
          (borrowRhs RefKind.Shared (blockSize τ) sOut.result.reg
            (pathOffset spath))]
        (k := 0) (by simp)
      simpa using h
  have h_code2 : compProg (s_mid1.pc + 1)
      = some (Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1))
          (Rhs.Load (layoutToTyVal τ) (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg))) := by
    rw [h_spc]
    refine h_instCS2 _ _ ?_ ?_
    · simp only [emit, List.length_cons, List.length_nil]
      omega
    · have h := emit_code_at_new
        { (emit
        { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1 }
        [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)
          (borrowRhs RefKind.Shared (blockSize τ) sOut.result.reg (pathOffset spath))]) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1 + 1 }
        [Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1))
            (Rhs.Load (layoutToTyVal τ) (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)),
          Instr.Die (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg) (blockSize τ)]
        (k := 0) (by simp)
      simpa [emit] using h
  have h_code3 : compProg (s_mid1.pc + 1 + 1)
      = some (Instr.Die (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg) (blockSize τ)) := by
    rw [h_spc]
    refine h_instCS2 _ _ ?_ ?_
    · simp only [emit, List.length_cons, List.length_nil]
      omega
    · have h := emit_code_at_new
        { (emit
        { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1 }
        [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)
          (borrowRhs RefKind.Shared (blockSize τ) sOut.result.reg (pathOffset spath))]) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1 + 1 }
        [Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1))
            (Rhs.Load (layoutToTyVal τ) (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)),
          Instr.Die (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg) (blockSize τ)]
        (k := 1) (by simp)
      simpa [emit] using h
  have h_le1 : rs.allocBase + (rs.addr - rs.allocBase) + pathOffset spath
      + blockSize τ ≤ rs.allocBase + rs.allocSize := by
    rw [h_cancelS]
    have := Nat.not_lt.mp h_fit
    grind
  have h_ref_tgt' : MSB.ref s_mid1.perms
      (rs.allocBase + (rs.addr - rs.allocBase) + pathOffset spath)
      (blockSize τ) tres RefKind.Shared false []
      = .ok (q1, s_mid1.perms.NextTag) := by
    rw [h_cancelS]
    exact h_ref_tgt
  have h_run1 := runN_Assgn_Borrow_step compProg s_mid1
    (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg) sOut.result.reg RefKind.Shared false []
    (blockSize τ) (pathOffset spath) h_code1 h_sentry h_le1 h_ref_tgt'
  have h_bentry : PtrRegisterEntry (oseair.RegMap.insert s_mid1.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)
              (obseq.TyVal.PTy, [Val.Ptr rs.allocBase (rs.addr - rs.allocBase + pathOffset spath)
                rs.allocSize s_mid1.perms.NextTag]))
      (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg) rs.allocBase
      (rs.addr - rs.allocBase + pathOffset spath) rs.allocSize
      s_mid1.perms.NextTag :=
    RegMap.lookup_insert_self _ _ _
  have h_read2 : MSB.read q1
      (rs.allocBase + (rs.addr - rs.allocBase + pathOffset spath))
      (obseq.typeSize (layoutToTyVal τ)) s_mid1.perms.NextTag = .ok q2 := by
    rw [h_ts, ← Nat.add_assoc, h_cancelS]
    exact h_rd1
  have h_run2 := runN_Assgn_Load_ptr_step compProg
    { s_mid1 with perms := q1, reg := (oseair.RegMap.insert s_mid1.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)
              (obseq.TyVal.PTy, [Val.Ptr rs.allocBase (rs.addr - rs.allocBase + pathOffset spath)
                rs.allocSize s_mid1.perms.NextTag])), pc := s_mid1.pc + 1 }
    (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1)) (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)
    (layoutToTyVal τ) h_code2 h_bentry (by rw [h_ts]; grind) h_read2
  rw [h_ts, ← Nat.add_assoc, h_cancelS] at h_run2
  have h_regbv : (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)
      ≠ (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1)) := by
    intro h_eq
    injection h_eq with h_eq'
    omega
  have h_bentry2 : oseair.RegMap.lookup (oseair.RegMap.insert (oseair.RegMap.insert s_mid1.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)
              (obseq.TyVal.PTy, [Val.Ptr rs.allocBase (rs.addr - rs.allocBase + pathOffset spath)
                rs.allocSize s_mid1.perms.NextTag])) (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1))
            (layoutToTyVal τ, (oseair.readWordSeq s_mid1.mem (rs.addr + pathOffset spath) (blockSize τ))))
      (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)
      = some (obseq.TyVal.PTy, [Val.Ptr rs.allocBase
          (rs.addr - rs.allocBase + pathOffset spath)
          rs.allocSize s_mid1.perms.NextTag]) := by
    rw [RegMap.lookup_insert_ne _ h_regbv]
    exact h_bentry
  have h_die1' : MSB.die q2
      (rs.allocBase + (rs.addr - rs.allocBase + pathOffset spath))
      (blockSize τ) s_mid1.perms.NextTag = .ok q3 := by
    rw [← Nat.add_assoc, h_cancelS]
    exact h_die1
  have h_run3 := runN_Die_step compProg
    { s_mid1 with perms := q2, reg := (oseair.RegMap.insert (oseair.RegMap.insert s_mid1.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)
              (obseq.TyVal.PTy, [Val.Ptr rs.allocBase (rs.addr - rs.allocBase + pathOffset spath)
                rs.allocSize s_mid1.perms.NextTag])) (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1))
            (layoutToTyVal τ, (oseair.readWordSeq s_mid1.mem (rs.addr + pathOffset spath) (blockSize τ)))), pc := s_mid1.pc + 1 + 1 }
    (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg) (blockSize τ) h_code3 h_bentry2 h_die1'
  -- the post-`Die` binding simulation: both temporaries are fresh
  have h_prmCS2 : (emit
        { (emit
        { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1 }
        [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)
          (borrowRhs RefKind.Shared (blockSize τ) sOut.result.reg (pathOffset spath))]) with
          nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1 + 1 }
        [Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1))
            (Rhs.Load (layoutToTyVal τ) (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)),
          Instr.Die (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg) (blockSize τ)]).placeRegMap = csA.placeRegMap := by
    simp only [emit]
    exact h_sprm
  have h_lbsB : LocalBindingSim ρa ρt sM.env
      { s_mid1 with perms := q1, reg := (oseair.RegMap.insert s_mid1.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)
              (obseq.TyVal.PTy, [Val.Ptr rs.allocBase (rs.addr - rs.allocBase + pathOffset spath)
                rs.allocSize s_mid1.perms.NextTag])), pc := s_mid1.pc + 1 } csA :=
    LocalBindingSim.insert_fresh_reg h_slbs h_prb h_sregmono rfl
  have h_lbsV : LocalBindingSim ρa ρt sM.env
      { s_mid1 with
          perms := q3,
          reg := (oseair.RegMap.insert (oseair.RegMap.insert s_mid1.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)
              (obseq.TyVal.PTy, [Val.Ptr rs.allocBase (rs.addr - rs.allocBase + pathOffset spath)
                rs.allocSize s_mid1.perms.NextTag])) (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1))
            (layoutToTyVal τ, (oseair.readWordSeq s_mid1.mem (rs.addr + pathOffset spath) (blockSize τ)))),
          pc := s_mid1.pc + 1 + 1 + 1 } csA :=
    LocalBindingSim.insert_fresh_reg h_lbsB h_prb
      (Nat.le_trans h_sregmono (Nat.le_succ _)) rfl
  refine ⟨_, s_mid1, q3,
    oseair_runN_trans (oseair_runN_trans (oseair_runN_trans h_srun h_run1) h_run2)
      h_run3,
    h_prmCS2, (by simp only [emit]; omega), ?_, h_psim2q,
    (by rw [sb_read_NextTag h_read_src, h_snt1]
        refine TagRenameBounded.mono h_tbd (Nat.le_refl _) ?_
        refine Nat.le_trans h_snt2 ?_
        rw [← sb_read_NextTag h_read_tgt]
        exact h_ntle),
    h_smem, h_spc,
    (by rw [h_spc]; simp only [emit, List.length_cons, List.length_nil]),
    (by show _ < _; simp only [emit]; omega),
    (by rw [h_smem]
        exact readWordSeq_sim h_id_a h_sms (blockSize τ) _)⟩
  intro τ' loc' binding' h_env'
  obtain ⟨reg', base', tag', h_pi', h_entry', h_ra', h_rt', h_nw', h_dom'⟩ :=
    h_lbsV loc' binding' h_env'
  refine ⟨reg', base', tag', ?_, h_entry', h_ra', h_rt', h_nw', h_dom'⟩
  show getPlaceInfo _ loc'.idx.1 = _
  simp only [getPlaceInfo, emit]
  rw [h_sprm]
  exact h_pi'

/-- Every chain-class read package is a value package: the rvalue's whole
    compiled contribution is the source lowering plus its one
    instruction, so the single code-inclusion obligation covers both of
    the ones the read package asks for. -/
theorem ValuePkg.of_readPkgLowered
    {σ τ : LayoutTy} {rhs : RExpr Γ τ} {src : Place Γ σ} {mk : Register → Rhs}
    (compProg : oseair.Prog)
    (h_shape : ReadRhsShape rhs src mk)
    (h_pkg : ReadPkgLowered compProg rhs src mk) :
    ValuePkg compProg rhs := by
  intro ρa ρt sM sA csA h_id_a h_wf_t h_tbd h_lbs h_prb h_sms h_alloc h_psim h_pc
    output h_eval
  obtain ⟨ev, h_rhs⟩ := id h_shape
  obtain ⟨h_mapped, h_pkg'⟩ :=
    h_pkg ρa ρt sM sA csA h_id_a h_wf_t h_tbd h_lbs h_prb h_sms h_alloc h_psim h_pc
      output h_eval
  obtain ⟨sOut0, h_sval0⟩ := placeToRegChecked_ok_of_placeInputsMapped
    (cs := csA) (kind := RefKind.Shared) h_mapped
  -- the rvalue's own code, named once
  have h_prerun : CheckedCompilerM.run (compileRExprPreChecked rhs) csA
      = emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA) with
          nextReg := (CheckedCompilerM.run
            (placeToRegChecked RefKind.Shared src) csA).nextReg + 1 }
        ([Instr.Assgn (Register.R (CheckedCompilerM.run
            (placeToRegChecked RefKind.Shared src) csA).nextReg) (mk sOut0.result.reg)]
          ++ cleanupInstrs sOut0.result.cleanup) := by
    simp only [h_rhs, readRhsPre, csMonad, csRun, h_sval0]
  rw [h_rhs]
  simp only [readRhsPre, csMonad, csRun, h_sval0]
  refine ⟨Register.R (CheckedCompilerM.run
      (placeToRegChecked RefKind.Shared src) csA).nextReg, _, rfl, fun _ => rfl, rfl, ?_⟩
  intro h_code
  obtain ⟨h_sclean, nR, sR, perms₂, vals, h_ost, h_vlen, h_runR, h_prmR,
    h_regmonoR, h_lbsR, h_psimR, h_tbdR, h_smem, h_pcR, h_vregR, h_vbelow,
    h_valsRel⟩ :=
    h_pkg' sOut0 h_sval0
      (h_code.mono (StateIncr.trans (freshReg_state_incr _) (emit_state_incr _ _)))
      h_code
  -- with the source cleanup empty the two spellings of the tower agree
  simp only [csCleanup, h_sclean, List.append_nil]
  exact ⟨ρt, nR, sR, perms₂, vals, TagRenameIncr.refl ρt, h_wf_t, h_ost, h_vlen,
    h_runR, h_prmR, h_regmonoR, h_lbsR, h_psimR, h_tbdR, h_smem, h_pcR, h_vregR,
    h_vbelow, h_valsRel⟩

/-- copy's chain-class read package, as an instance of the generic one. -/
theorem copy_readpkg_lowered {τ : LayoutTy} {src : Place Γ τ}
    (compProg : oseair.Prog) (h_slower : LoweringSimAny compProg src) :
    ReadPkgLowered compProg (.copy src) src (Rhs.Load (layoutToTyVal τ)) := by
  intro ρa ρt sM sA csA h_id_a h_wf_t h_tbd h_lbs h_prb h_sms h_alloc h_psim h_pc
    output h_eval
  simp only [mirlite.evalRExpr] at h_eval
  cases h_sres : mirlite.resolvePlaceAcc MSB sM src with
  | error e => rw [h_sres] at h_eval; simp at h_eval
  | ok pr =>
  obtain ⟨rs, permsS⟩ := pr
  rw [h_sres] at h_eval
  simp only at h_eval
  by_cases h_fit : rs.addr + blockSize τ > rs.allocBase + rs.allocSize
  · rw [if_pos h_fit] at h_eval
    simp at h_eval
  · rw [if_neg h_fit] at h_eval
    cases h_read_src : MSB.read permsS rs.addr (blockSize τ) rs.tag with
    | error e => rw [h_read_src] at h_eval; simp at h_eval
    | ok perms₂ =>
    rw [h_read_src] at h_eval
    injection h_eval with h_out
    subst h_out
    refine ⟨placeInputsMapped_of_localBindingSim_resolvePlace h_lbs
        (resolvePlace?_of_resolveAcc h_sres), ?_⟩
    intro sOut0 h_sval0 h_instS h_instD
    obtain ⟨h_sclean, n1, s_mid1, p2, h_runR, h_prmR, h_regmonoR, h_lbsR, h_psimR,
      h_tbdR, h_smem, h_spc, h_pcR, h_vbelow, h_rel⟩ :=
      copy_chainsrc_read compProg h_slower sM sA csA h_id_a h_wf_t h_tbd h_lbs h_prb
        h_sms h_psim h_pc h_sres h_fit h_read_src h_sval0 h_instS h_instD
    exact ⟨h_sclean, n1 + 1, _, perms₂, _, rfl, (by rw [oseair_readWordSeq_length]),
      h_runR, h_prmR, h_regmonoR, h_lbsR, h_psimR, h_tbdR, h_smem, h_pcR,
      RegMap.lookup_insert_self _ _ _, h_vbelow, h_rel⟩

/-- copy's projected-source read package, as an instance of the generic one. -/
theorem copy_readpkg_projoffset {τ σs : LayoutTy} {B : Place Γ σs} {spath : PathTo σs τ}
    (compProg : oseair.Prog) (h_slower : LoweringSimAny compProg B) :
    ReadPkgProjOffset compProg (.copy (.proj B spath)) B spath (Rhs.Load (layoutToTyVal τ)) := by
  intro ρa ρt sM sA csA h_id_a h_wf_t h_tbd h_lbs h_prb h_sms h_alloc h_psim h_pc
    output h_eval
  simp only [mirlite.evalRExpr] at h_eval
  cases h_sres : mirlite.resolvePlaceAcc MSB sM B with
  | error e =>
      rw [resolvePlaceAcc_proj_base_err h_sres] at h_eval
      simp at h_eval
  | ok pr =>
  obtain ⟨rs, permsS⟩ := pr
  rw [resolvePlaceAcc_proj_base_ok h_sres] at h_eval
  simp only [gt_iff_lt] at h_eval
  by_cases h_fit : rs.allocBase + rs.allocSize < rs.addr + PathTo.offset spath + blockSize τ
  · rw [if_pos h_fit] at h_eval
    simp at h_eval
  · rw [if_neg h_fit] at h_eval
    cases h_read_src : MSB.read permsS (rs.addr + PathTo.offset spath) (blockSize τ) rs.tag with
    | error e => rw [h_read_src] at h_eval; simp at h_eval
    | ok perms₂ =>
    rw [h_read_src] at h_eval
    injection h_eval with h_out
    subst h_out
    refine ⟨placeInputsMapped_of_localBindingSim_resolvePlace h_lbs
        (resolvePlace?_of_resolveAcc (resolvePlaceAcc_proj_base_ok (path := spath) h_sres)), ?_⟩
    intro sOut0 h_sval0 sOutP h_regP h_clP h_instS h_instCS
    obtain ⟨h_sclean, n1, s_mid1, q3, h_runR, h_prmR, h_regmonoR, h_lbsR, h_psimR,
      h_tbdR, h_smem, h_spc, h_pcR, h_vbelow, h_rel⟩ :=
      copy_projsrc_offset_read compProg h_slower sM sA csA h_id_a h_wf_t h_tbd
        h_lbs h_prb h_sms h_psim h_pc h_sres h_fit h_read_src h_sval0 h_regP h_clP
        h_instS h_instCS
    exact ⟨h_sclean, n1, _, perms₂, _, rfl, (by rw [oseair_readWordSeq_length]),
      h_runR, h_prmR, h_regmonoR, h_lbsR, h_psimR, h_tbdR, h_smem, h_pcR,
      RegMap.lookup_insert_self _ _ _, h_vbelow, h_rel⟩

/-- The three code-inclusion facts every `*chain := copy src` leaf needs,
    proven ONCE, generic in the source. Each says a compiler state along
    the statement's lowering is below the statement's final state:
    after the source lowering, after the `Load` (with the source's
    cleanup kept SYMBOLIC — it is not known to be empty until the source
    mother has run), and after the destination lowering. Every leaf used
    to re-prove all three by unfolding the whole statement (~120 lines);
    the unfolding mentions the destination, so this is per destination
    constructor, but the source is only ever the opaque term
    `run (placeToRegChecked Shared src) cs`. -/
theorem readrhs_derefdst_incrs
    {τ τs : LayoutTy} {P : Place Γ (obseq.LayoutTy.PtrL τ)} {src : Place Γ τs}
    {stmt0 : Stmt Γ} (cs : CompilerState)
    {sOut0 : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared src)}
    {rhs : RExpr Γ τ} {mk : Register → Rhs}
    (h_shape : ReadRhsShape rhs src mk)
    (h_sval0 : CheckedCompilerM.value (placeToRegChecked RefKind.Shared src) cs
      = Except.ok sOut0)
    {csS : CompilerState}
    (h_srun : CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) cs = csS)
    (h_root : CompilerM.run (ensurePlaceRoot (Place.deref P)) cs = cs)
    (h_run0 : CheckedCompilerM.run (compileStmtChecked stmt0) cs
      = CheckedCompilerM.run
          (compileStmtChecked (Stmt.assign (.deref P) rhs)) cs) :
    StateIncr csS
        (CheckedCompilerM.run (compileStmtChecked stmt0) cs) ∧
    StateIncr (emit
        { csS with
          nextReg := csS.nextReg + 1 }
        ([Instr.Assgn (Register.R csS.nextReg)
            (mk sOut0.result.reg)]
          ++ cleanupInstrs sOut0.result.cleanup))
        (CheckedCompilerM.run (compileStmtChecked stmt0) cs) ∧
    StateIncr (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (Place.deref P))
        (emit
          { csS with
            nextReg := csS.nextReg + 1 }
          ([Instr.Assgn (Register.R csS.nextReg)
              (mk sOut0.result.reg)]
            ++ cleanupInstrs sOut0.result.cleanup)))
        (CheckedCompilerM.run (compileStmtChecked stmt0) cs) := by
  obtain ⟨ev, h_rhs⟩ := id h_shape
  rw [h_run0]
  simp only [compileStmtChecked, compileRExprToChecked, h_rhs, readRhsPre, csMonad, h_root, h_sval0]
  simp only [csRun]
  rw [h_srun]
  -- name the post-Load state once
  generalize hR : emit { csS with nextReg := csS.nextReg + 1 }
      ([Instr.Assgn (Register.R csS.nextReg) (mk sOut0.result.reg)]
        ++ cleanupInstrs sOut0.result.cleanup) = csR
  have hSR : StateIncr csS csR := by
    rw [← hR]
    exact StateIncr.trans (freshReg_state_incr csS) (emit_state_incr _ _)
  have hRD : StateIncr csR (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (Place.deref P)) csR) :=
    CheckedCompilerM.incr _ _
  split
  · rename_i a h_a
    have hD : StateIncr (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (Place.deref P)) csR)
        (emit (emit (emit (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (Place.deref P)) csR)
          [Instr.RStore (layoutToTyVal τ) (Register.R csS.nextReg) a.result.reg])
          (cleanupInstrs [])) (cleanupInstrs a.result.cleanup)) :=
      emit_tower_incr₃ _ _ _ _
    exact ⟨StateIncr.trans hSR (StateIncr.trans hRD hD), StateIncr.trans hRD hD, hD⟩
  · exact ⟨StateIncr.trans hSR hRD, hRD, StateIncr.refl _⟩

/-- The three code-inclusion facts for a PROJECTED destination over a
    chain base, at ANY offset: after the source lowering, after the
    rvalue's own instruction, and after the destination BASE's lowering
    (the projection's own `Borrow` belongs to the write tail, so the
    third fact is the same statement at either offset). -/
theorem readrhs_projdst_incrs
    {τ τs σb : LayoutTy} {dbase : Place Γ σb} {path : PathTo σb τ} {src : Place Γ τs}
    {stmt0 : Stmt Γ} (cs : CompilerState)
    {sOut0 : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared src)}
    {rhs : RExpr Γ τ} {mk : Register → Rhs}
    (h_shape : ReadRhsShape rhs src mk)
    (h_sval0 : CheckedCompilerM.value (placeToRegChecked RefKind.Shared src) cs
      = Except.ok sOut0)
    {csS : CompilerState}
    (h_srun : CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) cs = csS)
    (h_np : ∀ (σ' : LayoutTy) (b : Place Γ σ') (q : PathTo σ' σb), dbase = b.proj q → False)
    (h_root : CompilerM.run (ensurePlaceRoot (Place.proj dbase path)) cs = cs)
    (h_run0 : CheckedCompilerM.run (compileStmtChecked stmt0) cs
      = CheckedCompilerM.run
          (compileStmtChecked (Stmt.assign (.proj dbase path) rhs)) cs) :
    StateIncr csS
        (CheckedCompilerM.run (compileStmtChecked stmt0) cs) ∧
    StateIncr (emit
        { csS with nextReg := csS.nextReg + 1 }
        ([Instr.Assgn (Register.R csS.nextReg) (mk sOut0.result.reg)]
          ++ cleanupInstrs sOut0.result.cleanup))
        (CheckedCompilerM.run (compileStmtChecked stmt0) cs) ∧
    StateIncr (CheckedCompilerM.run (placeToRegChecked RefKind.Mut dbase)
        (emit
          { csS with nextReg := csS.nextReg + 1 }
          ([Instr.Assgn (Register.R csS.nextReg) (mk sOut0.result.reg)]
            ++ cleanupInstrs sOut0.result.cleanup)))
        (CheckedCompilerM.run (compileStmtChecked stmt0) cs) := by
  obtain ⟨ev, h_rhs⟩ := id h_shape
  have hBase : ∀ cs' : CompilerState,
      StateIncr (CheckedCompilerM.run (placeToRegChecked RefKind.Mut dbase) cs')
        (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (Place.proj dbase path)) cs') := by
    intro cs'
    rw [placeToRegChecked_proj_root_eq (kind := RefKind.Mut) (base := dbase) path h_np]
    simp only [csMonad, csRun]
    repeat' split
    all_goals first
      | exact StateIncr.refl _
      | exact StateIncr.trans (freshReg_state_incr _) (emit_state_incr _ _)
      | exact emit_state_incr _ _
  rw [h_run0]
  simp only [compileStmtChecked, compileRExprToChecked, h_rhs, readRhsPre, csMonad, h_root, h_sval0]
  simp only [csRun]
  rw [h_srun]
  generalize hR : emit { csS with nextReg := csS.nextReg + 1 }
      ([Instr.Assgn (Register.R csS.nextReg) (mk sOut0.result.reg)]
        ++ cleanupInstrs sOut0.result.cleanup) = csR
  have hSR : StateIncr csS csR := by
    rw [← hR]
    exact StateIncr.trans (freshReg_state_incr csS) (emit_state_incr _ _)
  have hRD : StateIncr csR
      (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (Place.proj dbase path)) csR) :=
    CheckedCompilerM.incr _ _
  have hBD := hBase csR
  split
  · rename_i a h_a
    have hD : StateIncr
        (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (Place.proj dbase path)) csR)
        (emit (emit (emit
          (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (Place.proj dbase path)) csR)
          [Instr.RStore (layoutToTyVal τ) (Register.R csS.nextReg) a.result.reg])
          (cleanupInstrs [])) (cleanupInstrs a.result.cleanup)) :=
      emit_tower_incr₃ _ _ _ _
    exact ⟨StateIncr.trans hSR (StateIncr.trans hRD hD), StateIncr.trans hRD hD,
      StateIncr.trans hBD hD⟩
  · exact ⟨StateIncr.trans hSR hRD, hRD, hBD⟩

/-- `copy_derefdst_incrs` for a ZERO-offset projected destination over a
    chain: the same three facts, with the destination lowering rewritten
    to its base by `placeToRegChecked_proj_zero_run`. The original docstring:
    The three code-inclusion facts every `*chain := copy src` leaf needs,
    proven ONCE, generic in the source. Each says a compiler state along
    the statement's lowering is below the statement's final state:
    after the source lowering, after the `Load` (with the source's
    cleanup kept SYMBOLIC — it is not known to be empty until the source
    mother has run), and after the destination lowering. Every leaf used
    to re-prove all three by unfolding the whole statement (~120 lines);
    the unfolding mentions the destination, so this is per destination
    constructor, but the source is only ever the opaque term
    `run (placeToRegChecked Shared src) cs`. -/
theorem readrhs_projzerodst_incrs
    {τ τs σb : LayoutTy} {dbase : Place Γ σb} {path : PathTo σb τ} {src : Place Γ τs}
    {stmt0 : Stmt Γ} (cs : CompilerState)
    {sOut0 : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared src)}
    {rhs : RExpr Γ τ} {mk : Register → Rhs}
    (h_shape : ReadRhsShape rhs src mk)
    (h_sval0 : CheckedCompilerM.value (placeToRegChecked RefKind.Shared src) cs
      = Except.ok sOut0)
    {csS : CompilerState}
    (h_srun : CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) cs = csS)
    (h_np : ∀ (σ' : LayoutTy) (b : Place Γ σ') (q : PathTo σ' σb), dbase = b.proj q → False)
    (h_o : pathOffset path = 0)
    (h_root : CompilerM.run (ensurePlaceRoot (Place.proj dbase path)) cs = cs)
    (h_run0 : CheckedCompilerM.run (compileStmtChecked stmt0) cs
      = CheckedCompilerM.run
          (compileStmtChecked (Stmt.assign (.proj dbase path) rhs)) cs) :
    StateIncr csS
        (CheckedCompilerM.run (compileStmtChecked stmt0) cs) ∧
    StateIncr (emit
        { csS with
          nextReg := csS.nextReg + 1 }
        ([Instr.Assgn (Register.R csS.nextReg)
            (mk sOut0.result.reg)]
          ++ cleanupInstrs sOut0.result.cleanup))
        (CheckedCompilerM.run (compileStmtChecked stmt0) cs) ∧
    StateIncr (CheckedCompilerM.run (placeToRegChecked RefKind.Mut dbase)
        (emit
          { csS with
            nextReg := csS.nextReg + 1 }
          ([Instr.Assgn (Register.R csS.nextReg)
              (mk sOut0.result.reg)]
            ++ cleanupInstrs sOut0.result.cleanup)))
        (CheckedCompilerM.run (compileStmtChecked stmt0) cs) := by
  obtain ⟨ev, h_rhs⟩ := id h_shape
  rw [h_run0]
  simp only [compileStmtChecked, compileRExprToChecked, h_rhs, readRhsPre, csMonad, h_root, h_sval0]
  rw [placeToRegChecked_proj_zero_run path h_np h_o]
  simp only [csRun]
  rw [h_srun]
  -- name the post-Load state once
  generalize hR : emit { csS with nextReg := csS.nextReg + 1 }
      ([Instr.Assgn (Register.R csS.nextReg) (mk sOut0.result.reg)]
        ++ cleanupInstrs sOut0.result.cleanup) = csR
  have hSR : StateIncr csS csR := by
    rw [← hR]
    exact StateIncr.trans (freshReg_state_incr csS) (emit_state_incr _ _)
  have hRD : StateIncr csR (CheckedCompilerM.run (placeToRegChecked RefKind.Mut dbase) csR) :=
    CheckedCompilerM.incr _ _
  split
  · rename_i a h_a
    have hD : StateIncr (CheckedCompilerM.run (placeToRegChecked RefKind.Mut dbase) csR)
        (emit (emit (emit (CheckedCompilerM.run (placeToRegChecked RefKind.Mut dbase) csR)
          [Instr.RStore (layoutToTyVal τ) (Register.R csS.nextReg) a.result.reg])
          (cleanupInstrs [])) (cleanupInstrs a.result.cleanup)) :=
      emit_tower_incr₃ _ _ _ _
    exact ⟨StateIncr.trans hSR (StateIncr.trans hRD hD), StateIncr.trans hRD hD, hD⟩
  · exact ⟨StateIncr.trans hSR hRD, hRD, StateIncr.refl _⟩


/-- REGIME B for copy, CLOSED 2026-08-29: `dst := copy src` where the
    DESTINATION LOCAL IS UNBOUND — the statement's own execution
    allocates it. mirlite's `preparePlaceAssign` allocates the τ-sized
    root and binds it BEFORE the source is read, and `ensurePlaceRoot`
    emits the matching root `Alloc`; the source lowering then runs in
    the post-allocation states on both machines (the mother lemma is
    called at the extended renames), and one `Memcpy` finishes. Any
    aliasing (`y := copy y`) is rejected source-side by the overlap
    guard, since the destination resolves after the allocation. -/
theorem copy_fresh_chainsrc_simulation
    {τ τs : LayoutTy}
    {dstLoc : Local Γ τ} {src : Place Γ τs}
    {rhs : RExpr Γ τ} {mk : Register → Rhs}
    (compProg : oseair.Prog)
    (h_shape : ReadRhsShape rhs src mk)
    (h_pkg : ReadPkgLowered compProg rhs src mk)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    {stmt0 : Stmt Γ}
    (h_stmt : prog.get? s_mir.pc = some stmt0)
    (h_run0 : ∀ cs, CheckedCompilerM.run (compileStmtChecked stmt0) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.local dstLoc) rhs)) cs)
    (h_val0 : ∀ cs so, CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.local dstLoc) rhs)) cs
        = Except.ok so →
      ∃ so', CheckedCompilerM.value (compileStmtChecked stmt0) cs
        = Except.ok so')
    (h_envD : mirlite.Env.lookup s_mir.env dstLoc = none)
    (h_step : mirlite.stepStmt MSB s_mir
      (.assign (.local dstLoc) rhs) = .ok s_mir') :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' := by
  obtain ⟨csPrefix, ⟨h_csAt, h_pc⟩, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_tbd,
    h_alloc, h_unmap, h_prb⟩ := h_inv
  have h_pi_none : getPlaceInfo csPrefix dstLoc.idx.1 = none := h_unmap dstLoc h_envD
  -- §1 the destination local is unbound, so the statement allocates its
  -- root before it reads
  simp only [mirlite.stepStmt, mirlite.doAssign] at h_step
  cases h_prep : mirlite.preparePlaceAssign MSB s_mir (Place.local dstLoc) with
  | err msg => rw [h_prep] at h_step; simp at h_step
  | ok s1 =>
  rw [h_prep] at h_step
  rw [show mirlite.preparePlaceAssign MSB s_mir (Place.local dstLoc)
      = mirlite.allocateBase MSB s_mir dstLoc from by
    simp only [mirPrep, mirAlloc, h_envD]] at h_prep
  -- §2 the allocation prologue: both roots, both renames, and the
  -- post-`Alloc` states a source package starts from
  have h_incr_a :=
    AddrRenameIncr.extendBlock h_id_a s_mir.mem.addrStart (blockSize τ)
  have h_id_a' :=
    IdentityOnDomain.extendBlock h_id_a s_mir.mem.addrStart (blockSize τ)
  have h_ra_dom : ∀ k, k < blockSize τ →
      (ρa.extendBlock s_mir.mem.addrStart (blockSize τ))
        (s_mir.mem.addrStart + k) = some (s_mir.mem.addrStart + k) :=
    fun _ hk => AddrRenameMap.extendBlock_mem hk
  obtain ⟨permsOwned, tgtPerms, h_own_tgt', h_perms1, h_pc1, h_env1,
    h_lookup_set, h_memstart1, h_allocs1, h_find1, h_incr_t, h_wf_t', h_tbd', h_psim',
    h_erun, h_prb1, h_lbs1⟩ :=
    copy_freshroot_prologue h_envD h_prep h_wf_t h_tbd h_psim h_alloc
      h_lbs h_prb h_pi_none h_incr_a (AddrRenameMap.extendBlock_base _ _ _)
      h_ra_dom
  have h_addr_eq : s_osea.mem.addrStart = s_mir.mem.addrStart := h_alloc.1
  have h_sz : obseq.typeSize (layoutToTyVal τ) = blockSize τ :=
    obseq.typeSize_layoutToTyVal _
  -- §3 the source read, kept OPAQUE behind the rvalue's package
  simp only at h_step
  cases h_eval : mirlite.evalRExpr MSB s1 rhs with
  | err e => rw [h_eval] at h_step; simp at h_step
  | ok output =>
    rw [h_eval] at h_step
    simp only at h_step
    obtain ⟨h_mappedS, h_pkg'⟩ :=
      h_pkg _ _ s1
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
          dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))
        h_id_a' h_wf_t' (by rw [h_perms1]; exact h_tbd') h_lbs1 h_prb1
        (by
          intro a v h_find
          rw [h_find1] at h_find
          exact SourceMemSim.rename_mono h_incr_a h_incr_t h_sms a v h_find)
        (AllocLockstep.of_alloc h_alloc h_incr_a h_sz h_memstart1 h_allocs1)
        (by rw [h_perms1]; exact h_psim')
        (by
          show s_osea.pc + 1 = _
          rw [h_pc]
          simp only [emit, setPlaceInfo, List.length_cons, List.length_nil])
        output h_eval
    obtain ⟨sOut0, h_sval0⟩ := placeToRegChecked_ok_of_placeInputsMapped
      (cs := setPlaceInfo
          (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
            [Instr.Assgn (Register.R csPrefix.nextReg)
              (Rhs.Alloc (layoutToTyVal τ))])
          dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))
      (kind := RefKind.Shared) h_mappedS
    -- §5 the statement value and code inclusion for the source lowering
    obtain ⟨stmtOutC, h_stmtOutC⟩ :=
      compileStmt_readrhs_fresh_chainsrc_value (h_shape := h_shape) h_pi_none h_sval0
    obtain ⟨stmtOut, h_stmtOut⟩ := h_val0 csPrefix stmtOutC h_stmtOutC
    obtain ⟨h_incrS, h_incrL'⟩ :=
      readrhs_localdst_incrs (h_shape := h_shape) csPrefix h_erun h_sval0 rfl (h_run0 csPrefix)
    have h_instS :=
      (CodeIncluded.of_stmt h_comp h_csAt h_stmt h_stmtOut).mono h_incrS
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
    -- §7 the SOURCE package at the post-allocation states, under the
    -- extended renames: mother, read transport, the rvalue's instruction
    obtain ⟨h_sclean, nR, s_mid, perms₂, vals, h_ost, h_vlen, h_runR, h_prmR,
      h_regmonoR, h_lbsR, h_psimR, h_tbdR, h_smem, h_pcR, h_vregR, h_vbelow, h_rel⟩ :=
      h_pkg' sOut0 h_sval0 h_instS
        ((CodeIncluded.of_stmt h_comp h_csAt h_stmt h_stmtOut).mono h_incrL')
    rw [h_ost] at h_step
    simp only [mirlite.resolvePlaceAcc, h_lookup_set] at h_step
    have h_stmtRun := (h_run0 csPrefix).trans
      (compileStmt_readrhs_fresh_chainsrc_run (h_shape := h_shape) h_pi_none h_sval0 h_sclean)
    -- §8-§11 the fresh-root WRITE seam: the `RStore` through the root,
    -- the memory extension, and the whole invariant rebuild
    exact copy_freshroot_write_after_read compProg h_comp h_stmt h_csAt h_stmtOut
      h_sms h_unmap h_lookup_set h_env1 h_pc1 h_memstart1 h_allocs1 h_alloc h_find1
      h_addr_eq h_sz h_run0' h_incr_a h_incr_t h_id_a' h_wf_t' h_ra_dom h_prb1
      h_runR h_prmR h_regmonoR h_lbsR h_psimR h_tbdR h_smem h_pcR
      h_vregR h_vlen h_stmtRun output.values_len (Nat.le_refl _) rfl rfl h_rel h_step
/-! ## FRESH destination with a PROJ-TOPPED source: the root `Alloc`,
    then the base lowering, then the projection's own shape. -/

theorem compileStmt_readrhs_fresh_projchain_zero_run
    {Γ : Ctx} {τ τs σb : LayoutTy}
    {dstLoc : Local Γ τ} {B : Place Γ σb} {path : PathTo σb τs}
    {cs : CompilerState}
    {bOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared B)}
    {rhs : RExpr Γ τ} {mk : Register → Rhs}
    (h_shape : ReadRhsShape rhs (.proj B path) mk)
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
          (Stmt.assign (.local dstLoc) rhs)) cs
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
            dstLoc.idx.1 (Register.R cs.nextReg, τ))).nextReg) (mk bOut.result.reg)])
          [Instr.RStore (obseq.layoutToTyVal τ) (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
          (setPlaceInfo
            (emit { cs with nextReg := cs.nextReg + 1 }
              [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal τ))])
            dstLoc.idx.1 (Register.R cs.nextReg, τ))).nextReg) (Register.R cs.nextReg)] := by
  obtain ⟨ev, h_rhs⟩ := id h_shape
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_fresh (loc := dstLoc) h_dst
  have h_proj_eq := placeToRegChecked_proj_root_eq (Γ := Γ)
    (kind := RefKind.Shared) (base := B) path h_np
  simp only [compileStmtChecked, compileRExprToChecked, h_rhs, readRhsPre, csMonad, h_proj_eq, h_run, h_val, h_bval, h_off,
    dif_pos]
  simp [csRun, cleanupInstrs, h_bclean, emit_nil]

theorem compileStmt_readrhs_fresh_projchain_zero_value
    {Γ : Ctx} {τ τs σb : LayoutTy}
    {dstLoc : Local Γ τ} {B : Place Γ σb} {path : PathTo σb τs}
    {cs : CompilerState}
    {bOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared B)}
    {rhs : RExpr Γ τ} {mk : Register → Rhs}
    (h_shape : ReadRhsShape rhs (.proj B path) mk)
    (h_np : ∀ (σ' : LayoutTy) (b : Place Γ σ') (q : PathTo σ' σb), B = b.proj q → False)
    (h_off : pathOffset path = 0)
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = none)
    (h_bval : CheckedCompilerM.value (placeToRegChecked RefKind.Shared B)
      (setPlaceInfo
        (emit { cs with nextReg := cs.nextReg + 1 }
          [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal τ))])
        dstLoc.idx.1 (Register.R cs.nextReg, τ)) = Except.ok bOut) :
    ∃ so, CheckedCompilerM.value
      (compileStmtChecked (Stmt.assign (.local dstLoc) rhs)) cs
      = Except.ok so := by
  obtain ⟨ev, h_rhs⟩ := id h_shape
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_fresh (loc := dstLoc) h_dst
  have h_proj_eq := placeToRegChecked_proj_root_eq (Γ := Γ)
    (kind := RefKind.Shared) (base := B) path h_np
  simp only [compileStmtChecked, compileRExprToChecked, h_rhs, readRhsPre, csMonad, h_proj_eq, h_run, h_bval, h_off, dif_pos]
  exact ⟨_, rfl⟩

theorem compileStmt_readrhs_fresh_projchain_offset_run
    {Γ : Ctx} {τ τs σb : LayoutTy}
    {dstLoc : Local Γ τ} {B : Place Γ σb} {path : PathTo σb τs}
    {cs : CompilerState}
    {bOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared B)}
    {rhs : RExpr Γ τ} {mk : Register → Rhs}
    (h_shape : ReadRhsShape rhs (.proj B path) mk)
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
          (Stmt.assign (.local dstLoc) rhs)) cs
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
                (borrowRhs RefKind.Shared (blockSize τs) bOut.result.reg
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
              dstLoc.idx.1 (Register.R cs.nextReg, τ))).nextReg + 1)) (mk (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
            (setPlaceInfo
              (emit { cs with nextReg := cs.nextReg + 1 }
                [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal τ))])
              dstLoc.idx.1 (Register.R cs.nextReg, τ))).nextReg)),
           Instr.Die (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
            (setPlaceInfo
              (emit { cs with nextReg := cs.nextReg + 1 }
                [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal τ))])
              dstLoc.idx.1 (Register.R cs.nextReg, τ))).nextReg) (blockSize τs)])
          [Instr.RStore (obseq.layoutToTyVal τ) (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
            (setPlaceInfo
              (emit { cs with nextReg := cs.nextReg + 1 }
                [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal τ))])
              dstLoc.idx.1 (Register.R cs.nextReg, τ))).nextReg + 1)) (Register.R cs.nextReg)] := by
  obtain ⟨ev, h_rhs⟩ := id h_shape
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_fresh (loc := dstLoc) h_dst
  have h_proj_eq := placeToRegChecked_proj_root_eq (Γ := Γ)
    (kind := RefKind.Shared) (base := B) path h_np
  simp only [compileStmtChecked, compileRExprToChecked, h_rhs, readRhsPre, csMonad, h_proj_eq, h_run, h_val, h_bval]
  simp [csRun, cleanupInstrs, h_bclean, emit_nil, h_off, borrowRhs]
  rfl

theorem compileStmt_readrhs_fresh_projchain_offset_value
    {Γ : Ctx} {τ τs σb : LayoutTy}
    {dstLoc : Local Γ τ} {B : Place Γ σb} {path : PathTo σb τs}
    {cs : CompilerState}
    {bOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared B)}
    {rhs : RExpr Γ τ} {mk : Register → Rhs}
    (h_shape : ReadRhsShape rhs (.proj B path) mk)
    (h_np : ∀ (σ' : LayoutTy) (b : Place Γ σ') (q : PathTo σ' σb), B = b.proj q → False)
    (h_off : pathOffset path ≠ 0)
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = none)
    (h_bval : CheckedCompilerM.value (placeToRegChecked RefKind.Shared B)
      (setPlaceInfo
        (emit { cs with nextReg := cs.nextReg + 1 }
          [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal τ))])
        dstLoc.idx.1 (Register.R cs.nextReg, τ)) = Except.ok bOut) :
    ∃ so, CheckedCompilerM.value
      (compileStmtChecked (Stmt.assign (.local dstLoc) rhs)) cs
      = Except.ok so := by
  obtain ⟨ev, h_rhs⟩ := id h_shape
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_fresh (loc := dstLoc) h_dst
  have h_proj_eq := placeToRegChecked_proj_root_eq (Γ := Γ)
    (kind := RefKind.Shared) (base := B) path h_np
  simp only [compileStmtChecked, compileRExprToChecked, h_rhs, readRhsPre, csMonad, h_proj_eq, h_run, h_bval, dif_neg h_off]
  exact ⟨_, rfl⟩

/-- REGIME B for copy with a PROJ-TOPPED source at ZERO offset,
    CLOSED 2026-08-29: `dst := copy B.f` with an UNBOUND destination and
    `pathOffset f = 0`. The projection passes the base register through,
    so this is the chain-source regime B with a `+ 0` on the source
    resolution. -/
theorem copy_fresh_projchain_zero_simulation
    {τ τs σb : LayoutTy}
    {dstLoc : Local Γ τ} {B : Place Γ σb} {path : PathTo σb τs}
    {rhs : RExpr Γ τ} {mk : Register → Rhs}
    (compProg : oseair.Prog)
    (h_shape : ReadRhsShape rhs (.proj B path) mk)
    (h_pkg : ReadPkgLowered compProg rhs (.proj B path) mk)
    (h_chain : PtrChain B)
    (h_off : pathOffset path = 0)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    {stmt0 : Stmt Γ}
    (h_stmt : prog.get? s_mir.pc = some stmt0)
    (h_run0 : ∀ cs, CheckedCompilerM.run (compileStmtChecked stmt0) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.local dstLoc) rhs)) cs)
    (h_val0 : ∀ cs so, CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.local dstLoc) rhs)) cs
        = Except.ok so →
      ∃ so', CheckedCompilerM.value (compileStmtChecked stmt0) cs
        = Except.ok so')
    (h_envD : mirlite.Env.lookup s_mir.env dstLoc = none)
    (h_step : mirlite.stepStmt MSB s_mir
      (.assign (.local dstLoc) rhs) = .ok s_mir') :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' := by
  obtain ⟨csPrefix, ⟨h_csAt, h_pc⟩, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_tbd,
    h_alloc, h_unmap, h_prb⟩ := h_inv
  have h_pi_none : getPlaceInfo csPrefix dstLoc.idx.1 = none := h_unmap dstLoc h_envD
  -- §1 the destination local is unbound, so the statement allocates its
  -- root before it reads
  simp only [mirlite.stepStmt, mirlite.doAssign] at h_step
  cases h_prep : mirlite.preparePlaceAssign MSB s_mir (Place.local dstLoc) with
  | err msg => rw [h_prep] at h_step; simp at h_step
  | ok s1 =>
  rw [h_prep] at h_step
  rw [show mirlite.preparePlaceAssign MSB s_mir (Place.local dstLoc)
      = mirlite.allocateBase MSB s_mir dstLoc from by
    simp only [mirPrep, mirAlloc, h_envD]] at h_prep
  -- §2 the allocation prologue: both roots, both renames, and the
  -- post-`Alloc` states a source package starts from
  have h_incr_a :=
    AddrRenameIncr.extendBlock h_id_a s_mir.mem.addrStart (blockSize τ)
  have h_id_a' :=
    IdentityOnDomain.extendBlock h_id_a s_mir.mem.addrStart (blockSize τ)
  have h_ra_dom : ∀ k, k < blockSize τ →
      (ρa.extendBlock s_mir.mem.addrStart (blockSize τ))
        (s_mir.mem.addrStart + k) = some (s_mir.mem.addrStart + k) :=
    fun _ hk => AddrRenameMap.extendBlock_mem hk
  obtain ⟨permsOwned, tgtPerms, h_own_tgt', h_perms1, h_pc1, h_env1,
    h_lookup_set, h_memstart1, h_allocs1, h_find1, h_incr_t, h_wf_t', h_tbd', h_psim',
    h_erun, h_prb1, h_lbs1⟩ :=
    copy_freshroot_prologue h_envD h_prep h_wf_t h_tbd h_psim h_alloc
      h_lbs h_prb h_pi_none h_incr_a (AddrRenameMap.extendBlock_base _ _ _)
      h_ra_dom
  have h_addr_eq : s_osea.mem.addrStart = s_mir.mem.addrStart := h_alloc.1
  have h_sz : obseq.typeSize (layoutToTyVal τ) = blockSize τ :=
    obseq.typeSize_layoutToTyVal _
  -- §3 the source read, kept OPAQUE behind the rvalue's package
  simp only at h_step
  have h_np := h_chain.not_proj
  have h_o' : PathTo.offset path = 0 := h_off
  cases h_eval : mirlite.evalRExpr MSB s1 rhs with
  | err e => rw [h_eval] at h_step; simp at h_step
  | ok output =>
    rw [h_eval] at h_step
    simp only at h_step
    obtain ⟨h_mappedP, h_pkg'⟩ :=
      h_pkg _ _ s1
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
          dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))
        h_id_a' h_wf_t' (by rw [h_perms1]; exact h_tbd') h_lbs1 h_prb1
        (by
          intro a v h_find
          rw [h_find1] at h_find
          exact SourceMemSim.rename_mono h_incr_a h_incr_t h_sms a v h_find)
        (AllocLockstep.of_alloc h_alloc h_incr_a h_sz h_memstart1 h_allocs1)
        (by rw [h_perms1]; exact h_psim')
        (by
          show s_osea.pc + 1 = _
          rw [h_pc]
          simp only [emit, setPlaceInfo, List.length_cons, List.length_nil])
        output h_eval
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
    -- §5 the statement value and code inclusion for the source lowering
    obtain ⟨stmtOutC, h_stmtOutC⟩ :=
      compileStmt_readrhs_fresh_projchain_zero_value (h_shape := h_shape) h_np h_off h_pi_none h_sval0
    obtain ⟨stmtOut, h_stmtOut⟩ := h_val0 csPrefix stmtOutC h_stmtOutC
    have h_pv0 := placeToRegChecked_proj_zero_value (kind := RefKind.Shared)
      path h_np h_off h_sval0
    have h_pr0 := placeToRegChecked_proj_zero_run (kind := RefKind.Shared)
      path h_np h_off
      (setPlaceInfo
        (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
          [Instr.Assgn (Register.R csPrefix.nextReg)
            (Rhs.Alloc (layoutToTyVal τ))])
        dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))
    obtain ⟨h_incrS, h_incrL'⟩ :=
      readrhs_localdst_incrs (h_shape := h_shape) csPrefix h_erun h_pv0 h_pr0 (h_run0 csPrefix)
    have h_instS :=
      (CodeIncluded.of_stmt h_comp h_csAt h_stmt h_stmtOut).mono h_incrS
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
    -- §7 the SOURCE package at the post-allocation states, under the
    -- extended renames -- at zero offset the projection resolves, and
    -- lowers, exactly as its chain base does
    obtain ⟨h_sclean, nR, s_mid, perms₂, vals, h_ost, h_vlen, h_runR, h_prmR,
      h_regmonoR, h_lbsR, h_psimR, h_tbdR, h_smem, h_pcR, h_vregR, h_vbelow, h_rel⟩ :=
      h_pkg' _ h_pv0 (by rw [h_pr0]; exact h_instS)
        (by rw [h_pr0]
            exact (CodeIncluded.of_stmt h_comp h_csAt h_stmt h_stmtOut).mono
              h_incrL')
    rw [h_ost] at h_step
    simp only [mirlite.resolvePlaceAcc, h_lookup_set] at h_step
    rw [h_pr0] at h_prmR h_regmonoR h_lbsR h_pcR h_vbelow h_vregR
    have h_sclean0 : sOut0.result.cleanup = [] := h_sclean
    have h_stmtRun := (h_run0 csPrefix).trans
      (compileStmt_readrhs_fresh_projchain_zero_run (h_shape := h_shape) h_np h_off h_pi_none h_sval0
        h_sclean0)
    -- §8-§11 the fresh-root WRITE seam: the `RStore` through the root,
    -- the memory extension, and the whole invariant rebuild
    exact copy_freshroot_write_after_read compProg h_comp h_stmt h_csAt h_stmtOut
      h_sms h_unmap h_lookup_set h_env1 h_pc1 h_memstart1 h_allocs1 h_alloc h_find1
      h_addr_eq h_sz h_run0' h_incr_a h_incr_t h_id_a' h_wf_t' h_ra_dom h_prb1
      h_runR h_prmR h_regmonoR h_lbsR h_psimR h_tbdR h_smem h_pcR
      h_vregR h_vlen h_stmtRun output.values_len (Nat.le_refl _) rfl rfl h_rel h_step
/-- REGIME B for copy with a PROJ-TOPPED source at NONZERO offset,
    CLOSED 2026-08-29: `dst := copy B.f` with an UNBOUND destination.
    The root `Alloc` runs first and the mother lemma is called at the
    post-allocation states under both extended renames (regime B's
    prefix); the ending is the projection's `Borrow(Shared); Memcpy;
    Die`, with the destination's `useMut` sliding between BRIDGE 1S's
    phases by the overlap guard's disjointness. -/
theorem copy_fresh_projchain_offset_simulation
    {τ τs σb : LayoutTy}
    {dstLoc : Local Γ τ} {B : Place Γ σb} {path : PathTo σb τs}
    {rhs : RExpr Γ τ} {mk : Register → Rhs}
    (compProg : oseair.Prog)
    (h_shape : ReadRhsShape rhs (.proj B path) mk)
    (h_pkg : ReadPkgProjOffset compProg rhs B path mk)
    (h_chain : PtrChain B)
    (h_off : pathOffset path ≠ 0)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    {stmt0 : Stmt Γ}
    (h_stmt : prog.get? s_mir.pc = some stmt0)
    (h_run0 : ∀ cs, CheckedCompilerM.run (compileStmtChecked stmt0) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.local dstLoc) rhs)) cs)
    (h_val0 : ∀ cs so, CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.local dstLoc) rhs)) cs
        = Except.ok so →
      ∃ so', CheckedCompilerM.value (compileStmtChecked stmt0) cs
        = Except.ok so')
    (h_envD : mirlite.Env.lookup s_mir.env dstLoc = none)
    (h_step : mirlite.stepStmt MSB s_mir
      (.assign (.local dstLoc) rhs) = .ok s_mir') :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' := by
  obtain ⟨csPrefix, ⟨h_csAt, h_pc⟩, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_tbd,
    h_alloc, h_unmap, h_prb⟩ := h_inv
  have h_pi_none : getPlaceInfo csPrefix dstLoc.idx.1 = none := h_unmap dstLoc h_envD
  -- §1 the destination local is unbound, so the statement allocates its
  -- root before it reads
  simp only [mirlite.stepStmt, mirlite.doAssign] at h_step
  cases h_prep : mirlite.preparePlaceAssign MSB s_mir (Place.local dstLoc) with
  | err msg => rw [h_prep] at h_step; simp at h_step
  | ok s1 =>
  rw [h_prep] at h_step
  rw [show mirlite.preparePlaceAssign MSB s_mir (Place.local dstLoc)
      = mirlite.allocateBase MSB s_mir dstLoc from by
    simp only [mirPrep, mirAlloc, h_envD]] at h_prep
  -- §2 the allocation prologue: both roots, both renames, and the
  -- post-`Alloc` states a source package starts from
  have h_incr_a :=
    AddrRenameIncr.extendBlock h_id_a s_mir.mem.addrStart (blockSize τ)
  have h_id_a' :=
    IdentityOnDomain.extendBlock h_id_a s_mir.mem.addrStart (blockSize τ)
  have h_ra_dom : ∀ k, k < blockSize τ →
      (ρa.extendBlock s_mir.mem.addrStart (blockSize τ))
        (s_mir.mem.addrStart + k) = some (s_mir.mem.addrStart + k) :=
    fun _ hk => AddrRenameMap.extendBlock_mem hk
  obtain ⟨permsOwned, tgtPerms, h_own_tgt', h_perms1, h_pc1, h_env1,
    h_lookup_set, h_memstart1, h_allocs1, h_find1, h_incr_t, h_wf_t', h_tbd', h_psim',
    h_erun, h_prb1, h_lbs1⟩ :=
    copy_freshroot_prologue h_envD h_prep h_wf_t h_tbd h_psim h_alloc
      h_lbs h_prb h_pi_none h_incr_a (AddrRenameMap.extendBlock_base _ _ _)
      h_ra_dom
  have h_addr_eq : s_osea.mem.addrStart = s_mir.mem.addrStart := h_alloc.1
  have h_sz : obseq.typeSize (layoutToTyVal τ) = blockSize τ :=
    obseq.typeSize_layoutToTyVal _
  -- §3 the source read, kept OPAQUE behind the rvalue's package
  simp only at h_step
  have h_np := h_chain.not_proj
  cases h_eval : mirlite.evalRExpr MSB s1 rhs with
  | err e => rw [h_eval] at h_step; simp at h_step
  | ok output =>
    rw [h_eval] at h_step
    simp only at h_step
    obtain ⟨h_mappedP, h_pkg'⟩ :=
      h_pkg _ _ s1
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
          dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))
        h_id_a' h_wf_t' (by rw [h_perms1]; exact h_tbd') h_lbs1 h_prb1
        (by
          intro a v h_find
          rw [h_find1] at h_find
          exact SourceMemSim.rename_mono h_incr_a h_incr_t h_sms a v h_find)
        (AllocLockstep.of_alloc h_alloc h_incr_a h_sz h_memstart1 h_allocs1)
        (by rw [h_perms1]; exact h_psim')
        (by
          show s_osea.pc + 1 = _
          rw [h_pc]
          simp only [emit, setPlaceInfo, List.length_cons, List.length_nil])
        output h_eval
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
    -- §5 the statement value and code inclusion for the source lowering
    obtain ⟨stmtOutC, h_stmtOutC⟩ :=
      compileStmt_readrhs_fresh_projchain_offset_value (h_shape := h_shape) h_np h_off h_pi_none h_sval0
    obtain ⟨stmtOut, h_stmtOut⟩ := h_val0 csPrefix stmtOutC h_stmtOutC
    obtain ⟨sOutP, h_svalP, h_regP, h_clP⟩ :=
      placeToRegChecked_proj_offset_value (kind := RefKind.Shared) path h_np h_off
        h_sval0
    obtain ⟨h_incrS', h_incrL'⟩ :=
      readrhs_localdst_incrs (h_shape := h_shape) csPrefix h_erun h_svalP
        (placeToRegChecked_proj_offset_run (kind := RefKind.Shared) path h_np h_off
          h_sval0) (h_run0 csPrefix)
    have h_incrS : StateIncr
        (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
          (setPlaceInfo
          (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
            [Instr.Assgn (Register.R csPrefix.nextReg)
              (Rhs.Alloc (layoutToTyVal τ))])
          dstLoc.idx.1 (Register.R csPrefix.nextReg, τ)))
        (CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix) :=
      StateIncr.trans (StateIncr.trans (freshReg_state_incr _) (emit_state_incr _ _))
        h_incrS'
    have h_instS :=
      (CodeIncluded.of_stmt h_comp h_csAt h_stmt h_stmtOut).mono h_incrS
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
    -- §7 the SOURCE package at the post-allocation states, under the
    -- extended renames: mother, BRIDGE 1S, Borrow/Assgn/Die
    obtain ⟨h_sclean, nR, s_mid, perms₂, vals, h_ost, h_vlen, h_runR, h_prmR,
      h_regmonoR, h_lbsR, h_psimR, h_tbdR, h_smem, h_pcR, h_vregR, h_vbelow, h_rel⟩ :=
      h_pkg' sOut0 h_sval0 _ h_regP h_clP h_instS
        ((CodeIncluded.of_stmt h_comp h_csAt h_stmt h_stmtOut).mono h_incrL')
    rw [h_ost] at h_step
    simp only [mirlite.resolvePlaceAcc, h_lookup_set] at h_step
    have h_stmtRun := (h_run0 csPrefix).trans
      (compileStmt_readrhs_fresh_projchain_offset_run (h_shape := h_shape) h_np h_off h_pi_none h_sval0
        h_sclean)
    have h_ts : obseq.typeSize (obseq.layoutToTyVal τ) = blockSize τ := by
      simp [blockSize]
    -- §8-§11 the fresh-root WRITE seam: the `RStore` through the root,
    -- the memory extension, and the whole invariant rebuild
    exact copy_freshroot_write_after_read compProg h_comp h_stmt h_csAt h_stmtOut
      h_sms h_unmap h_lookup_set h_env1 h_pc1 h_memstart1 h_allocs1 h_alloc h_find1
      h_addr_eq h_sz h_run0' h_incr_a h_incr_t h_id_a' h_wf_t' h_ra_dom h_prb1
      h_runR h_prmR h_regmonoR h_lbsR h_psimR h_tbdR h_smem h_pcR
      h_vregR h_vlen h_stmtRun output.values_len (Nat.le_refl _) rfl rfl h_rel h_step
/-! ## NON-LOCAL destination: the fragment composes TWO place lowerings.

`compileStmtChecked`'s general assign arm runs the rhs pre-phase (the
source lowering AND, since the temp-assignment lowering, the `Load` that
performs the read) BEFORE the destination lowering, then stores. With
both places cleanup-free the whole statement is
`[src code; Load; dst code; RStore]`. -/

/-! ## A PROJ-topped source under a chain destination: at zero offset
    the projection passes the base's register (and its cleanup) through,
    so the tower is the chain/chain one with `B` in the source slot. -/

theorem compileStmt_readrhs_chaindst_projsrc_zero_run
    {Γ : Ctx} {τ τs σs : LayoutTy}
    {P : Place Γ (obseq.LayoutTy.PtrL τ)} {B : Place Γ σs}
    {spath : PathTo σs τs}
    {cs : CompilerState}
    {sOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared B)}
    {dOut : ResultWithEvidence PtrResult
      (PlaceToRegEvidence RefKind.Mut (Place.deref P))}
    {rhs : RExpr Γ τ} {mk : Register → Rhs}
    (h_shape : ReadRhsShape rhs (.proj B spath) mk)
    (h_chainB : PtrChain B)
    (h_o : pathOffset spath = 0)
    (h_root : CompilerM.run (ensurePlaceRoot (Place.deref P)) cs = cs)
    (h_sval : CheckedCompilerM.value (placeToRegChecked RefKind.Shared B) cs
      = Except.ok sOut)
    (h_sclean : sOut.result.cleanup = [])
    (h_dval : CheckedCompilerM.value (placeToRegChecked RefKind.Mut (Place.deref P))
      (emit
        { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs) with
          nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg + 1 }
        [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg)
          (mk sOut.result.reg)])
      = Except.ok dOut)
    (h_dclean : dOut.result.cleanup = []) :
    CheckedCompilerM.run
        (compileStmtChecked (Stmt.assign (.deref P) rhs)) cs
      = emit (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (Place.deref P))
          (emit
            { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs) with
              nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg + 1 }
            [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg)
              (mk sOut.result.reg)]))
          [Instr.RStore (layoutToTyVal τ)
            (Register.R (CheckedCompilerM.run
              (placeToRegChecked RefKind.Shared B) cs).nextReg)
            dOut.result.reg] := by
  obtain ⟨ev, h_rhs⟩ := id h_shape
  have h_pv := placeToRegChecked_proj_zero_value (kind := RefKind.Shared)
    spath (PtrChain.not_proj h_chainB) h_o h_sval
  have h_pr := placeToRegChecked_proj_zero_run (kind := RefKind.Shared)
    spath (PtrChain.not_proj h_chainB) h_o cs
  simp only [compileStmtChecked, compileRExprToChecked, h_rhs, readRhsPre, csMonad, h_root, h_pv, h_pr]
  simp only [csCleanup, csRun, h_sclean, emit_nil, List.append_nil]
  split
  · rename_i o h_d
    have h_oeq : dOut = o := Except.ok.inj (h_dval ▸ h_d)
    subst h_oeq
    simp [CompilerM.run, CompilerM.value, emitM, cleanupInstrs, h_dclean, emit_nil]
  · rename_i e h_d
    exact absurd h_d (by rw [h_dval]; simp)

theorem compileStmt_readrhs_chaindst_projsrc_zero_value
    {Γ : Ctx} {τ τs σs : LayoutTy}
    {P : Place Γ (obseq.LayoutTy.PtrL τ)} {B : Place Γ σs}
    {spath : PathTo σs τs}
    {cs : CompilerState}
    {sOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared B)}
    {dOut : ResultWithEvidence PtrResult
      (PlaceToRegEvidence RefKind.Mut (Place.deref P))}
    {rhs : RExpr Γ τ} {mk : Register → Rhs}
    (h_shape : ReadRhsShape rhs (.proj B spath) mk)
    (h_chainB : PtrChain B)
    (h_o : pathOffset spath = 0)
    (h_root : CompilerM.run (ensurePlaceRoot (Place.deref P)) cs = cs)
    (h_sval : CheckedCompilerM.value (placeToRegChecked RefKind.Shared B) cs
      = Except.ok sOut)
    (h_dval : CheckedCompilerM.value (placeToRegChecked RefKind.Mut (Place.deref P))
      (emit
        { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs) with
          nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg + 1 }
        ([Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg)
            (mk sOut.result.reg)]
          ++ cleanupInstrs sOut.result.cleanup))
      = Except.ok dOut) :
    ∃ so, CheckedCompilerM.value
      (compileStmtChecked (Stmt.assign (.deref P) rhs)) cs
      = Except.ok so := by
  obtain ⟨ev, h_rhs⟩ := id h_shape
  have h_pv := placeToRegChecked_proj_zero_value (kind := RefKind.Shared)
    spath (PtrChain.not_proj h_chainB) h_o h_sval
  have h_pr := placeToRegChecked_proj_zero_run (kind := RefKind.Shared)
    spath (PtrChain.not_proj h_chainB) h_o cs
  simp only [compileStmtChecked, compileRExprToChecked, h_rhs, readRhsPre, csMonad, h_root, h_pv, h_pr]
  simp only [csRun]
  split
  · exact ⟨_, rfl⟩
  · rename_i e h_d
    exact absurd h_d (by rw [h_dval]; simp)

/-! ## Chain destination with a PROJ-TOPPED source at NONZERO offset.
    The source tower is three instructions, not one: the projection's
    own `Borrow(Shared)` at `CS0.nextReg`, the copy's `Load` into
    `CS0.nextReg + 1`, and the projection's cleanup `Die`. The
    destination lowers only after that, so the `RStore` reads the
    loaded temporary. -/

theorem compileStmt_readrhs_chaindst_projsrc_offset_run
    {Γ : Ctx} {τ τs σs : LayoutTy}
    {P : Place Γ (obseq.LayoutTy.PtrL τ)} {B : Place Γ σs}
    {spath : PathTo σs τs}
    {cs : CompilerState}
    {bOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared B)}
    {dOut : ResultWithEvidence PtrResult
      (PlaceToRegEvidence RefKind.Mut (Place.deref P))}
    {rhs : RExpr Γ τ} {mk : Register → Rhs}
    (h_shape : ReadRhsShape rhs (.proj B spath) mk)
    (h_np : ∀ (σ' : LayoutTy) (b : Place Γ σ') (q : PathTo σ' σs),
      B = b.proj q → False)
    (h_o : pathOffset spath ≠ 0)
    (h_root : CompilerM.run (ensurePlaceRoot (Place.deref P)) cs = cs)
    (h_bval : CheckedCompilerM.value (placeToRegChecked RefKind.Shared B) cs
      = Except.ok bOut)
    (h_bclean : bOut.result.cleanup = [])
    (h_dval : CheckedCompilerM.value (placeToRegChecked RefKind.Mut (Place.deref P))
      (emit
        { (emit
            { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs) with
                nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg + 1 }
            [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg)
              (borrowRhs RefKind.Shared (blockSize τs) bOut.result.reg (pathOffset spath))]) with
            nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg + 1 + 1 }
        [Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg + 1))
          (mk
            (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg)),
         Instr.Die (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg)
           (blockSize τs)])
      = Except.ok dOut)
    (h_dclean : dOut.result.cleanup = []) :
    CheckedCompilerM.run
        (compileStmtChecked (Stmt.assign (.deref P) rhs)) cs
      = emit (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (Place.deref P))
          (emit
            { (emit
                { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs) with
                    nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg + 1 }
                [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg)
                  (borrowRhs RefKind.Shared (blockSize τs) bOut.result.reg (pathOffset spath))]) with
                nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg + 1 + 1 }
            [Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg + 1))
              (mk
                (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg)),
             Instr.Die (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg)
               (blockSize τs)]))
          [Instr.RStore (layoutToTyVal τ)
            (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg + 1))
            dOut.result.reg] := by
  obtain ⟨ev, h_rhs⟩ := id h_shape
  have h_proj_eq := placeToRegChecked_proj_root_eq (Γ := Γ)
    (kind := RefKind.Shared) (base := B) spath h_np
  simp only [compileStmtChecked, compileRExprToChecked, h_rhs, readRhsPre, csMonad, h_proj_eq, h_root, h_bval, dif_neg h_o]
  simp only [csCleanup, csRun, h_bclean, List.nil_append, List.reverse_cons, List.nil_append,
    List.map_cons]
  split
  · rename_i o h_d
    have h_d' : CheckedCompilerM.value (placeToRegChecked RefKind.Mut (Place.deref P))
        (emit
        { (emit
            { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs) with
                nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg + 1 }
            [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg)
              (borrowRhs RefKind.Shared (blockSize τs) bOut.result.reg (pathOffset spath))]) with
            nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg + 1 + 1 }
        [Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg + 1))
          (mk
            (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg)),
         Instr.Die (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg)
           (blockSize τs)]) = Except.ok o := h_d
    have h_oeq : dOut = o := Except.ok.inj (h_dval.symm.trans h_d')
    subst h_oeq
    simp only [csCleanup, CompilerM.run, CompilerM.value, emitM, h_dclean, emit_nil]
    rfl
  · rename_i e h_d
    have h_d' : CheckedCompilerM.value (placeToRegChecked RefKind.Mut (Place.deref P))
        (emit
        { (emit
            { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs) with
                nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg + 1 }
            [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg)
              (borrowRhs RefKind.Shared (blockSize τs) bOut.result.reg (pathOffset spath))]) with
            nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg + 1 + 1 }
        [Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg + 1))
          (mk
            (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg)),
         Instr.Die (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg)
           (blockSize τs)]) = Except.error e := h_d
    exact absurd (h_dval.symm.trans h_d') (by simp)

theorem compileStmt_readrhs_chaindst_projsrc_offset_value
    {Γ : Ctx} {τ τs σs : LayoutTy}
    {P : Place Γ (obseq.LayoutTy.PtrL τ)} {B : Place Γ σs}
    {spath : PathTo σs τs}
    {cs : CompilerState}
    {bOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared B)}
    {dOut : ResultWithEvidence PtrResult
      (PlaceToRegEvidence RefKind.Mut (Place.deref P))}
    {rhs : RExpr Γ τ} {mk : Register → Rhs}
    (h_shape : ReadRhsShape rhs (.proj B spath) mk)
    (h_np : ∀ (σ' : LayoutTy) (b : Place Γ σ') (q : PathTo σ' σs),
      B = b.proj q → False)
    (h_o : pathOffset spath ≠ 0)
    (h_root : CompilerM.run (ensurePlaceRoot (Place.deref P)) cs = cs)
    (h_bval : CheckedCompilerM.value (placeToRegChecked RefKind.Shared B) cs
      = Except.ok bOut)
    (h_dval : CheckedCompilerM.value (placeToRegChecked RefKind.Mut (Place.deref P))
      (emit
        { (emit
            { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs) with
                nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg + 1 }
            [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg)
              (borrowRhs RefKind.Shared (blockSize τs) bOut.result.reg (pathOffset spath))]) with
            nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg + 1 + 1 }
        ([Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg + 1))
            (mk
              (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg))]
          ++ cleanupInstrs (bOut.result.cleanup
              ++ [(Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg,
                   blockSize τs)])))
      = Except.ok dOut) :
    ∃ so, CheckedCompilerM.value
      (compileStmtChecked (Stmt.assign (.deref P) rhs)) cs
      = Except.ok so := by
  obtain ⟨ev, h_rhs⟩ := id h_shape
  have h_proj_eq := placeToRegChecked_proj_root_eq (Γ := Γ)
    (kind := RefKind.Shared) (base := B) spath h_np
  simp only [compileStmtChecked, compileRExprToChecked, h_rhs, readRhsPre, csMonad, h_proj_eq, h_root, h_bval, dif_neg h_o]
  simp only [csRun]
  split
  · exact ⟨_, rfl⟩
  · rename_i e h_d
    have h_d' : CheckedCompilerM.value (placeToRegChecked RefKind.Mut (Place.deref P))
        (emit
        { (emit
            { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs) with
                nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg + 1 }
            [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg)
              (borrowRhs RefKind.Shared (blockSize τs) bOut.result.reg (pathOffset spath))]) with
            nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg + 1 + 1 }
        ([Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg + 1))
            (mk
              (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg))]
          ++ cleanupInstrs (bOut.result.cleanup
              ++ [(Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg,
                   blockSize τs)]))) = Except.error e := h_d
    exact absurd (h_dval.symm.trans h_d') (by simp)

theorem compileStmt_readrhs_chaindst_run
    {Γ : Ctx} {τ τs : LayoutTy}
    {P : Place Γ (obseq.LayoutTy.PtrL τ)} {src : Place Γ τs}
    {cs : CompilerState}
    {sOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared src)}
    {dOut : ResultWithEvidence PtrResult
      (PlaceToRegEvidence RefKind.Mut (Place.deref P))}
    {rhs : RExpr Γ τ} {mk : Register → Rhs}
    (h_shape : ReadRhsShape rhs src mk)
    (h_root : CompilerM.run (ensurePlaceRoot (Place.deref P)) cs = cs)
    (h_sval : CheckedCompilerM.value (placeToRegChecked RefKind.Shared src) cs
      = Except.ok sOut)
    (h_sclean : sOut.result.cleanup = [])
    (h_dval : CheckedCompilerM.value (placeToRegChecked RefKind.Mut (Place.deref P))
      (emit
        { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) cs) with
          nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) cs).nextReg + 1 }
        [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) cs).nextReg)
          (mk sOut.result.reg)])
      = Except.ok dOut)
    (h_dclean : dOut.result.cleanup = []) :
    CheckedCompilerM.run
        (compileStmtChecked (Stmt.assign (.deref P) rhs)) cs
      = emit (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (Place.deref P))
          (emit
            { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) cs) with
              nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) cs).nextReg + 1 }
            [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) cs).nextReg)
              (mk sOut.result.reg)]))
          [Instr.RStore (layoutToTyVal τ)
            (Register.R (CheckedCompilerM.run
              (placeToRegChecked RefKind.Shared src) cs).nextReg)
            dOut.result.reg] := by
  obtain ⟨ev, h_rhs⟩ := id h_shape
  simp only [compileStmtChecked, compileRExprToChecked, h_rhs, readRhsPre, csMonad, h_root, h_sval]
  simp only [csCleanup, csRun, h_sclean, emit_nil, List.append_nil]
  split
  · rename_i o h_d
    have h_oeq : dOut = o := Except.ok.inj (h_dval ▸ h_d)
    subst h_oeq
    simp [CompilerM.run, CompilerM.value, emitM, cleanupInstrs, h_dclean, emit_nil]
  · rename_i e h_d
    exact absurd h_d (by rw [h_dval]; simp)

theorem compileStmt_readrhs_chaindst_value
    {Γ : Ctx} {τ τs : LayoutTy}
    {P : Place Γ (obseq.LayoutTy.PtrL τ)} {src : Place Γ τs}
    {cs : CompilerState}
    {sOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared src)}
    {dOut : ResultWithEvidence PtrResult
      (PlaceToRegEvidence RefKind.Mut (Place.deref P))}
    {rhs : RExpr Γ τ} {mk : Register → Rhs}
    (h_shape : ReadRhsShape rhs src mk)
    (h_root : CompilerM.run (ensurePlaceRoot (Place.deref P)) cs = cs)
    (h_sval : CheckedCompilerM.value (placeToRegChecked RefKind.Shared src) cs
      = Except.ok sOut)
    (h_dval : CheckedCompilerM.value (placeToRegChecked RefKind.Mut (Place.deref P))
      (emit
        { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) cs) with
          nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) cs).nextReg + 1 }
        ([Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) cs).nextReg)
            (mk sOut.result.reg)]
          ++ cleanupInstrs sOut.result.cleanup))
      = Except.ok dOut) :
    ∃ so, CheckedCompilerM.value
      (compileStmtChecked (Stmt.assign (.deref P) rhs)) cs
      = Except.ok so := by
  obtain ⟨ev, h_rhs⟩ := id h_shape
  simp only [compileStmtChecked, compileRExprToChecked, h_rhs, readRhsPre, csMonad, h_root, h_sval]
  simp only [csRun]
  split
  · exact ⟨_, rfl⟩
  · rename_i e h_d
    exact absurd h_d (by rw [h_dval]; simp)

/-! ## Flatten transfer for a DEREF destination with a copy rhs. Two
    single-split steps compose: flatten the SOURCE (the destination
    lowering is then the same place at equal states), then flatten the
    DESTINATION (the source pre-phase is untouched). -/

theorem compileStmt_readrhs_derefdst_srcflatten_run
    {Γ : Ctx} {τ τs : LayoutTy}
    (pp : Place Γ (obseq.LayoutTy.PtrL τ)) (src : Place Γ τs) (cs : CompilerState)
    {rhs rhs2 : RExpr Γ τ} {mk : Register → Rhs}
    (h_shape : ReadRhsShape rhs src mk)
    (h_shape2 : ReadRhsShape rhs2 (flattenPlace src) mk) :
    CheckedCompilerM.run
        (compileStmtChecked (Stmt.assign (.deref pp) rhs)) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.deref pp) rhs2)) cs := by
  obtain ⟨ev, h_rhs⟩ := id h_shape
  obtain ⟨ev2, h_rhs2⟩ := id h_shape2
  obtain ⟨h_sagr, h_sagv⟩ := placeToRegChecked_flatten_agree src RefKind.Shared (CompilerM.run (ensurePlaceRoot (Place.deref pp)) cs)
  simp only [compileStmtChecked, compileRExprToChecked, h_rhs, h_rhs2, readRhsPre, csMonad]
  cases hO : CheckedCompilerM.value (placeToRegChecked RefKind.Shared src) (CompilerM.run (ensurePlaceRoot (Place.deref pp)) cs) with
  | error eO =>
      cases hF : CheckedCompilerM.value
          (placeToRegChecked RefKind.Shared (flattenPlace src)) (CompilerM.run (ensurePlaceRoot (Place.deref pp)) cs) with
      | error eF =>
          simp only [hO, hF]
          exact h_sagr.symm
      | ok oF =>
          exfalso
          rw [hO, hF] at h_sagv
          simp [Except.map] at h_sagv
  | ok oO =>
      cases hF : CheckedCompilerM.value
          (placeToRegChecked RefKind.Shared (flattenPlace src)) (CompilerM.run (ensurePlaceRoot (Place.deref pp)) cs) with
      | error eF =>
          exfalso
          rw [hO, hF] at h_sagv
          simp [Except.map] at h_sagv
      | ok oF =>
          have h_sres : oF.result = oO.result := by
            rw [hO, hF] at h_sagv
            simpa [Except.map] using h_sagv
          simp only [hO, hF, h_sres, h_sagr]

theorem compileStmt_readrhs_derefdst_srcflatten_value
    {Γ : Ctx} {τ τs : LayoutTy}
    (pp : Place Γ (obseq.LayoutTy.PtrL τ)) (src : Place Γ τs) (cs : CompilerState)
    {rhs rhs2 : RExpr Γ τ} {mk : Register → Rhs}
    (h_shape : ReadRhsShape rhs src mk)
    (h_shape2 : ReadRhsShape rhs2 (flattenPlace src) mk)
    (h_ex : ∃ so, CheckedCompilerM.value
        (compileStmtChecked (Stmt.assign (.deref pp) rhs2)) cs
      = Except.ok so) :
    ∃ so', CheckedCompilerM.value
        (compileStmtChecked (Stmt.assign (.deref pp) rhs)) cs
      = Except.ok so' := by
  obtain ⟨ev, h_rhs⟩ := id h_shape
  obtain ⟨ev2, h_rhs2⟩ := id h_shape2
  obtain ⟨so, h_so⟩ := h_ex
  obtain ⟨h_sagr, h_sagv⟩ := placeToRegChecked_flatten_agree src RefKind.Shared (CompilerM.run (ensurePlaceRoot (Place.deref pp)) cs)
  simp only [compileStmtChecked, compileRExprToChecked, h_rhs, h_rhs2, readRhsPre, csMonad] at h_so ⊢
  cases hO : CheckedCompilerM.value (placeToRegChecked RefKind.Shared src) (CompilerM.run (ensurePlaceRoot (Place.deref pp)) cs) with
  | error eO =>
      exfalso
      cases hF : CheckedCompilerM.value
          (placeToRegChecked RefKind.Shared (flattenPlace src)) (CompilerM.run (ensurePlaceRoot (Place.deref pp)) cs) with
      | error eF =>
          rw [hF] at h_so
          simp at h_so
      | ok oF =>
          rw [hO, hF] at h_sagv
          simp [Except.map] at h_sagv
  | ok oO =>
      cases hF : CheckedCompilerM.value
          (placeToRegChecked RefKind.Shared (flattenPlace src)) (CompilerM.run (ensurePlaceRoot (Place.deref pp)) cs) with
      | error eF =>
          exfalso
          rw [hO, hF] at h_sagv
          simp [Except.map] at h_sagv
      | ok oF =>
          have h_sres : oF.result = oO.result := by
            rw [hO, hF] at h_sagv
            simpa [Except.map] using h_sagv
          simp only [hO]
          rw [hF] at h_so
          simp only [h_sres, h_sagr] at h_so
          split
          · exact ⟨_, rfl⟩
          · rename_i eDO h_dO
            exfalso
            simp only [h_dO] at h_so
            simp at h_so

theorem compileStmt_readrhs_derefdst_dstflatten_run
    {Γ : Ctx} {τ τs : LayoutTy}
    (pp : Place Γ (obseq.LayoutTy.PtrL τ)) (src : Place Γ τs) (cs : CompilerState)
    {rhs : RExpr Γ τ} {mk : Register → Rhs}
    (h_shape : ReadRhsShape rhs src mk) :
    CheckedCompilerM.run
        (compileStmtChecked (Stmt.assign (.deref pp) rhs)) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.deref (flattenPlace pp)) rhs)) cs := by
  obtain ⟨ev, h_rhs⟩ := id h_shape
  have h_er : ensurePlaceRoot (Place.deref (flattenPlace pp))
      = ensurePlaceRoot (Place.deref pp) := ensurePlaceRoot_flatten (Place.deref pp)
  simp only [compileStmtChecked, compileRExprToChecked, h_rhs, readRhsPre, csMonad, h_er]
  cases hS : CheckedCompilerM.value (placeToRegChecked RefKind.Shared src) (CompilerM.run (ensurePlaceRoot (Place.deref pp)) cs) with
  | error eS => simp only [hS]
  | ok oS =>
      simp only [csRun, hS]
      obtain ⟨h_dagr, h_dagv⟩ := placeToRegChecked_flatten_agree
        (Place.deref pp) RefKind.Mut (emit
          { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) (ensurePlaceRoot (Place.deref pp) cs).snd.val) with
            nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) (ensurePlaceRoot (Place.deref pp) cs).snd.val).nextReg + 1 }
          ([Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) (ensurePlaceRoot (Place.deref pp) cs).snd.val).nextReg)
              (mk oS.result.reg)]
            ++ cleanupInstrs oS.result.cleanup))
      rw [show flattenPlace (Place.deref pp) = Place.deref (flattenPlace pp) from rfl]
        at h_dagr h_dagv
      cases hDO : CheckedCompilerM.value (placeToRegChecked RefKind.Mut (Place.deref pp))
          (emit
            { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) (ensurePlaceRoot (Place.deref pp) cs).snd.val) with
              nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) (ensurePlaceRoot (Place.deref pp) cs).snd.val).nextReg + 1 }
            ([Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) (ensurePlaceRoot (Place.deref pp) cs).snd.val).nextReg)
                (mk oS.result.reg)]
              ++ cleanupInstrs oS.result.cleanup)) with
      | error eDO =>
          cases hDF : CheckedCompilerM.value
              (placeToRegChecked RefKind.Mut (Place.deref (flattenPlace pp)))
              (emit
                { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) (ensurePlaceRoot (Place.deref pp) cs).snd.val) with
                  nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) (ensurePlaceRoot (Place.deref pp) cs).snd.val).nextReg + 1 }
                ([Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) (ensurePlaceRoot (Place.deref pp) cs).snd.val).nextReg)
                    (mk oS.result.reg)]
                  ++ cleanupInstrs oS.result.cleanup)) with
          | error eDF =>
              exact h_dagr.symm
          | ok oDF =>
              exfalso
              rw [hDO, hDF] at h_dagv
              simp [Except.map] at h_dagv
      | ok oDO =>
          cases hDF : CheckedCompilerM.value
              (placeToRegChecked RefKind.Mut (Place.deref (flattenPlace pp)))
              (emit
                { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) (ensurePlaceRoot (Place.deref pp) cs).snd.val) with
                  nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) (ensurePlaceRoot (Place.deref pp) cs).snd.val).nextReg + 1 }
                ([Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) (ensurePlaceRoot (Place.deref pp) cs).snd.val).nextReg)
                    (mk oS.result.reg)]
                  ++ cleanupInstrs oS.result.cleanup)) with
          | error eDF =>
              exfalso
              rw [hDO, hDF] at h_dagv
              simp [Except.map] at h_dagv
          | ok oDF =>
              have h_dres : oDF.result = oDO.result := by
                rw [hDO, hDF] at h_dagv
                simpa [Except.map] using h_dagv
              simp only [h_dres, h_dagr]

theorem compileStmt_readrhs_derefdst_dstflatten_value
    {Γ : Ctx} {τ τs : LayoutTy}
    (pp : Place Γ (obseq.LayoutTy.PtrL τ)) (src : Place Γ τs) (cs : CompilerState)
    {rhs : RExpr Γ τ} {mk : Register → Rhs}
    (h_shape : ReadRhsShape rhs src mk)
    (h_ex : ∃ so, CheckedCompilerM.value
        (compileStmtChecked (Stmt.assign (.deref (flattenPlace pp)) rhs)) cs
      = Except.ok so) :
    ∃ so', CheckedCompilerM.value
        (compileStmtChecked (Stmt.assign (.deref pp) rhs)) cs
      = Except.ok so' := by
  obtain ⟨ev, h_rhs⟩ := id h_shape
  obtain ⟨so, h_so⟩ := h_ex
  have h_er : ensurePlaceRoot (Place.deref (flattenPlace pp))
      = ensurePlaceRoot (Place.deref pp) := ensurePlaceRoot_flatten (Place.deref pp)
  simp only [compileStmtChecked, compileRExprToChecked, h_rhs, readRhsPre, csMonad, h_er] at h_so ⊢
  cases hS : CheckedCompilerM.value (placeToRegChecked RefKind.Shared src) (CompilerM.run (ensurePlaceRoot (Place.deref pp)) cs) with
  | error eS =>
      exfalso
      rw [hS] at h_so
      simp at h_so
  | ok oS =>
      rw [hS] at h_so
      simp only [csRun, hS]
        at h_so ⊢
      obtain ⟨h_dagr, h_dagv⟩ := placeToRegChecked_flatten_agree
        (Place.deref pp) RefKind.Mut (emit
          { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) (ensurePlaceRoot (Place.deref pp) cs).snd.val) with
            nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) (ensurePlaceRoot (Place.deref pp) cs).snd.val).nextReg + 1 }
          ([Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) (ensurePlaceRoot (Place.deref pp) cs).snd.val).nextReg)
              (mk oS.result.reg)]
            ++ cleanupInstrs oS.result.cleanup))
      rw [show flattenPlace (Place.deref pp) = Place.deref (flattenPlace pp) from rfl]
        at h_dagr h_dagv
      split
      · exact ⟨_, rfl⟩
      · rename_i eDO h_dO
        exfalso
        cases h_dF : CheckedCompilerM.value
            (placeToRegChecked RefKind.Mut (Place.deref (flattenPlace pp)))
            (emit
              { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) (ensurePlaceRoot (Place.deref pp) cs).snd.val) with
                nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) (ensurePlaceRoot (Place.deref pp) cs).snd.val).nextReg + 1 }
              ([Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) (ensurePlaceRoot (Place.deref pp) cs).snd.val).nextReg)
                  (mk oS.result.reg)]
                ++ cleanupInstrs oS.result.cleanup)) with
        | ok oDF =>
            rw [h_dO, h_dF] at h_dagv
            simp [Except.map] at h_dagv
        | error eDF =>
            simp only [h_dF] at h_so
            simp at h_so

/-- NON-LOCAL destination, CLOSED 2026-08-30: `*Q := copy src` for a
    canonical-chain destination and source. The first leaf that composes
    TWO mother-lemma calls. The rhs pre-phase lowers the source and the
    `Load` performs the READ; the destination is lowered AFTER that, at
    the post-read permissions — which is mirlite's own order since the
    temp-assignment lowering — and the `RStore` writes. The temporary
    register survives the destination lowering by the mother lemma's
    register-frame conjunct. -/
theorem copy_chaindst_chainsrc_simulation
    {τ τs : LayoutTy}
    {P : Place Γ (obseq.LayoutTy.PtrL τ)} {src : Place Γ τs}
    {rhs : RExpr Γ τ} {mk : Register → Rhs}
    (compProg : oseair.Prog)
    (h_shape : ReadRhsShape rhs src mk)
    (h_pkg : ReadPkgLowered compProg rhs src mk)
    (h_prmS : ∀ cs, (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) cs).placeRegMap
      = cs.placeRegMap)
    (h_dchain : PtrChain (Place.deref P))
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    {stmt0 : Stmt Γ}
    (h_stmt : prog.get? s_mir.pc = some stmt0)
    (h_run0 : ∀ cs, CheckedCompilerM.run (compileStmtChecked stmt0) cs
      = CheckedCompilerM.run
          (compileStmtChecked (Stmt.assign (.deref P) rhs)) cs)
    (h_val0 : ∀ cs so, CheckedCompilerM.value
        (compileStmtChecked (Stmt.assign (.deref P) rhs)) cs
        = Except.ok so →
      ∃ so', CheckedCompilerM.value (compileStmtChecked stmt0) cs
        = Except.ok so')
    (h_step : mirlite.stepStmt MSB s_mir
      (.assign (.deref P) rhs) = .ok s_mir') :
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
  simp only at h_step
  cases h_eval : mirlite.evalRExpr MSB s_mir rhs with
  | err e => rw [h_eval] at h_step; simp at h_step
  | ok output =>
    rw [h_eval] at h_step
    simp only at h_step
    obtain ⟨h_mappedS, h_pkg'⟩ :=
      h_pkg _ _ s_mir s_osea csPrefix h_id_a h_wf_t h_tbd h_lbs h_prb h_sms h_alloc
        h_psim h_pc output h_eval
    -- §2 both places are mapped; the statement compiles
    have h_mappedD : PlaceInputsMapped csPrefix (Place.deref P) :=
      placeInputsMapped_of_localBindingSim_resolvePlace h_lbs h_resolved
    have h_root := ensurePlaceRoot_run_eq_of_mapped h_mappedD
    obtain ⟨sOut0, h_sval0⟩ := placeToRegChecked_ok_of_placeInputsMapped
      (cs := csPrefix) (kind := RefKind.Shared) h_mappedS
    have h_prmS0 : (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).placeRegMap = csPrefix.placeRegMap :=
      h_prmS csPrefix
    obtain ⟨dOut0, h_dval0⟩ := placeToRegChecked_ok_of_placeInputsMapped
      (cs := (emit
        { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix) with
          nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg + 1 }
        ([Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg)
            (mk sOut0.result.reg)]
          ++ cleanupInstrs sOut0.result.cleanup))) (kind := RefKind.Mut)
      (PlaceInputsMapped.placeRegMap_congr (by simp only [emit]; exact h_prmS0)
        _ h_mappedD)
    obtain ⟨stmtOutC, h_stmtOutC⟩ :=
      compileStmt_readrhs_chaindst_value (h_shape := h_shape) h_root h_sval0 h_dval0
    obtain ⟨stmtOut, h_stmtOut⟩ := h_val0 csPrefix stmtOutC h_stmtOutC
    -- §3 code inclusion for the SOURCE lowering (the three facts, once)
    obtain ⟨h_incrS, h_incrCS1', h_incrDrun'⟩ :=
      readrhs_derefdst_incrs (h_shape := h_shape) csPrefix h_sval0 rfl h_root (h_run0 csPrefix)
    have h_instS :=
      (CodeIncluded.of_stmt h_comp h_csAt h_stmt h_stmtOut).mono h_incrS
    -- §4-§6 the SOURCE package: mother, read transport, the rvalue's step
    obtain ⟨h_sclean, nR, s_mid1, perms₂, vals, h_ost, h_vlen, h_runR, h_prmR,
      h_regmonoR, h_lbsR, h_psimR, h_tbdR, h_smem, h_pcR, h_vregR, h_vbelow, h_valsRel⟩ :=
      h_pkg' sOut0 h_sval0 h_instS
        ((CodeIncluded.of_stmt h_comp h_csAt h_stmt h_stmtOut).mono h_incrCS1')
    rw [h_ost] at h_step
    simp only at h_step
    cases h_dres : mirlite.resolvePlaceAcc MSB
        { s_mir with perms := perms₂ } (Place.deref P) with
    | error e => rw [h_dres] at h_step; simp at h_step
    | ok pr2 =>
    obtain ⟨rd, permsD⟩ := pr2
    rw [h_dres] at h_step
    simp only at h_step
    -- code inclusion for the DESTINATION lowering's own instructions
    have h_incrDrun : StateIncr (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (Place.deref P))
        (emit
          { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix) with
            nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg + 1 }
          [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg)
            (mk sOut0.result.reg)]))
        (CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix) := by
      simpa only [csCleanup, h_sclean, List.append_nil] using h_incrDrun'
    have h_instDst :=
      (CodeIncluded.of_stmt h_comp h_csAt h_stmt h_stmtOut).mono h_incrDrun
    -- §7-§10: the destination half, shared with every other source shape
    exact copy_chainwrite_after_read compProg h_dchain h_comp h_stmt h_csAt
      h_stmtOut h_id_a h_wf_t h_sms h_alloc h_unmap h_prb
      h_dres output.values_len h_step
      h_runR h_prmR h_regmonoR h_lbsR h_psimR h_tbdR h_smem h_pcR
      h_vregR h_vbelow h_vlen h_valsRel
      h_instDst
      (fun dOut h_dval h_dclean => (h_run0 csPrefix).trans
        (compileStmt_readrhs_chaindst_run (h_shape := h_shape) h_root h_sval0 h_sclean h_dval h_dclean))

/-- REGIME copy, chain destination with a PROJ-TOPPED source at ZERO
    offset (`*p := copy s.f` with the field at offset 0): the source
    projection passes the chain's register and cleanup through, so this
    is the two-mother skeleton with the READ one layer deeper. Takes the
    `stmt0` transfer triple. -/
theorem copy_chaindst_projsrc_zero_simulation
    {τ τs σs : LayoutTy}
    {P : Place Γ (obseq.LayoutTy.PtrL τ)} {B : Place Γ σs}
    {spath : PathTo σs τs}
    {rhs : RExpr Γ τ} {mk : Register → Rhs}
    (compProg : oseair.Prog)
    (h_shape : ReadRhsShape rhs (.proj B spath) mk)
    (h_pkg : ReadPkgLowered compProg rhs (.proj B spath) mk)
    (h_dchain : PtrChain (Place.deref P))
    (h_schain : PtrChain B)
    (h_o : pathOffset spath = 0)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    {stmt0 : Stmt Γ}
    (h_stmt : prog.get? s_mir.pc = some stmt0)
    (h_run0 : ∀ cs, CheckedCompilerM.run (compileStmtChecked stmt0) cs
      = CheckedCompilerM.run
          (compileStmtChecked (Stmt.assign (.deref P) rhs)) cs)
    (h_val0 : ∀ cs so, CheckedCompilerM.value
        (compileStmtChecked (Stmt.assign (.deref P) rhs)) cs
        = Except.ok so →
      ∃ so', CheckedCompilerM.value (compileStmtChecked stmt0) cs
        = Except.ok so')
    (h_step : mirlite.stepStmt MSB s_mir
      (.assign (.deref P) rhs) = .ok s_mir') :
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
  simp only at h_step
  have h_o' : PathTo.offset spath = 0 := h_o
  cases h_eval : mirlite.evalRExpr MSB s_mir rhs with
  | err e => rw [h_eval] at h_step; simp at h_step
  | ok output =>
    rw [h_eval] at h_step
    simp only at h_step
    obtain ⟨h_mappedP, h_pkg'⟩ :=
      h_pkg _ _ s_mir s_osea csPrefix h_id_a h_wf_t h_tbd h_lbs h_prb h_sms h_alloc
        h_psim h_pc output h_eval
    have h_mappedS : PlaceInputsMapped csPrefix B := h_mappedP
    -- §2 both places are mapped; the statement compiles
    have h_mappedD : PlaceInputsMapped csPrefix (Place.deref P) :=
      placeInputsMapped_of_localBindingSim_resolvePlace h_lbs h_resolved
    have h_root := ensurePlaceRoot_run_eq_of_mapped h_mappedD
    obtain ⟨sOut0, h_sval0⟩ := placeToRegChecked_ok_of_placeInputsMapped
      (cs := csPrefix) (kind := RefKind.Shared) h_mappedS
    have h_pv0 := placeToRegChecked_proj_zero_value (kind := RefKind.Shared)
      spath (PtrChain.not_proj h_schain) h_o h_sval0
    have h_pr0 := placeToRegChecked_proj_zero_run (kind := RefKind.Shared)
      spath (PtrChain.not_proj h_schain) h_o csPrefix
    have h_prmS : (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).placeRegMap = csPrefix.placeRegMap :=
      h_schain.placeToRegChecked_placeRegMap RefKind.Shared csPrefix
    obtain ⟨dOut0, h_dval0⟩ := placeToRegChecked_ok_of_placeInputsMapped
      (cs := (emit
        { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix) with
          nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg + 1 }
        ([Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg)
            (mk sOut0.result.reg)]
          ++ cleanupInstrs sOut0.result.cleanup))) (kind := RefKind.Mut)
      (PlaceInputsMapped.placeRegMap_congr (by simp only [emit]; exact h_prmS)
        _ h_mappedD)
    obtain ⟨stmtOutC, h_stmtOutC⟩ :=
      compileStmt_readrhs_chaindst_projsrc_zero_value (h_shape := h_shape) h_schain h_o h_root h_sval0 h_dval0
    obtain ⟨stmtOut, h_stmtOut⟩ := h_val0 csPrefix stmtOutC h_stmtOutC
    -- §3 code inclusion for the SOURCE lowering (the three facts, once)
    obtain ⟨h_incrS, h_incrCS1', h_incrDrun'⟩ :=
      readrhs_derefdst_incrs (h_shape := h_shape) csPrefix h_pv0 h_pr0 h_root (h_run0 csPrefix)
    have h_instS :=
      (CodeIncluded.of_stmt h_comp h_csAt h_stmt h_stmtOut).mono h_incrS
    -- §4-§6 the SOURCE package at the PROJECTED place -- its lowering is the
    -- base's at zero offset -- then its outputs moved onto the base's tower
    obtain ⟨h_sclean, nR, s_mid1, perms₂, vals, h_ost, h_vlen, h_runR, h_prmR,
      h_regmonoR, h_lbsR, h_psimR, h_tbdR, h_smem, h_pcR, h_vregR, h_vbelow, h_valsRel⟩ :=
      h_pkg' _ h_pv0 (by rw [h_pr0]; exact h_instS)
        (by rw [h_pr0]
            exact (CodeIncluded.of_stmt h_comp h_csAt h_stmt h_stmtOut).mono h_incrCS1')
    rw [h_pr0] at h_prmR h_regmonoR h_lbsR h_pcR h_vbelow h_vregR
    rw [h_ost] at h_step
    simp only at h_step
    cases h_dres : mirlite.resolvePlaceAcc MSB
        { s_mir with perms := perms₂ } (Place.deref P) with
    | error e => rw [h_dres] at h_step; simp at h_step
    | ok pr2 =>
    obtain ⟨rd, permsD⟩ := pr2
    rw [h_dres] at h_step
    simp only at h_step
    -- the package's cleanup fact is about the PROJECTED evidence; its result
    -- is the base's, so the fact transports by defeq
    have h_sclean0 : sOut0.result.cleanup = [] := h_sclean
    -- code inclusion for the DESTINATION lowering's own instructions
    have h_incrDrun : StateIncr (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (Place.deref P))
        (emit
          { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix) with
            nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg + 1 }
          [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg)
            (mk sOut0.result.reg)]))
        (CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix) := by
      simpa only [csCleanup, h_sclean0, List.append_nil] using h_incrDrun'
    have h_instDst :=
      (CodeIncluded.of_stmt h_comp h_csAt h_stmt h_stmtOut).mono h_incrDrun
    -- §7-§10: the destination half, shared with every other source shape
    exact copy_chainwrite_after_read compProg h_dchain h_comp h_stmt h_csAt
      h_stmtOut h_id_a h_wf_t h_sms h_alloc h_unmap h_prb
      h_dres output.values_len h_step
      h_runR h_prmR h_regmonoR h_lbsR h_psimR h_tbdR h_smem h_pcR
      h_vregR h_vbelow h_vlen h_valsRel
      h_instDst
      (fun dOut h_dval h_dclean => (h_run0 csPrefix).trans
        (compileStmt_readrhs_chaindst_projsrc_zero_run (h_shape := h_shape) h_schain h_o h_root
          h_sval0 h_sclean0 h_dval h_dclean))

/-- Fresh projected destination, chain source: `Alloc; <chain>; Load;` then the
    destination tail at the projection's offset — one lemma for both offsets. -/
theorem compileStmt_readrhs_projlocal_fresh_run
    {Γ : Ctx} {τ τs σ : LayoutTy} {loc : Local Γ σ}
    {path : PathTo σ τ} {src : Place Γ τs} {cs : CompilerState}
    {sOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared src)}
    {rhs : RExpr Γ τ} {mk : Register → Rhs}
    (h_shape : ReadRhsShape rhs src mk)
    (h_pi : getPlaceInfo cs loc.idx.1 = none)
    (h_sval : CheckedCompilerM.value (placeToRegChecked RefKind.Shared src) (setPlaceInfo
          (emit { cs with nextReg := cs.nextReg + 1 }
            [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
          loc.idx.1 (Register.R cs.nextReg, σ))
      = Except.ok sOut)
    (h_sclean : sOut.result.cleanup = [])
    (h_dpi : getPlaceInfo (emit
          { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) (setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 } [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R cs.nextReg, σ))) with
            nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) (setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 } [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R cs.nextReg, σ))).nextReg + 1 }
          [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) (setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 } [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R cs.nextReg, σ))).nextReg)
            (mk sOut.result.reg)]) loc.idx.1 = some (Register.R cs.nextReg, σ)) :
    CheckedCompilerM.run
        (compileStmtChecked (Stmt.assign (.proj (.local loc) path) rhs)) cs
      = projDstTail (emit
          { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) (setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 } [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R cs.nextReg, σ))) with
            nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) (setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 } [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R cs.nextReg, σ))).nextReg + 1 }
          [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) (setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 } [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R cs.nextReg, σ))).nextReg)
            (mk sOut.result.reg)])
          (pathOffset path) (blockSize τ) (layoutToTyVal τ)
          (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) (setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 } [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R cs.nextReg, σ))).nextReg) (Register.R cs.nextReg) := by
  obtain ⟨ev, h_rhs⟩ := id h_shape
  obtain ⟨h_run, -⟩ := ensureLocalRegE_fresh (loc := loc) h_pi
  have h_proj_eq := placeToRegChecked_proj_root_eq (Γ := Γ) (kind := RefKind.Mut)
    (base := .local loc) path (fun _ _ _ h => by cases h)
  have h_root : CompilerM.run
      (ensurePlaceRoot (Place.proj (Place.local loc) path)) cs = (setPlaceInfo
          (emit { cs with nextReg := cs.nextReg + 1 }
            [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
          loc.idx.1 (Register.R cs.nextReg, σ)) := by
    show CompilerM.run (do let _ ← ensureLocalRegE loc; pure ()) cs = _
    simp [CompilerM.run_bind, CompilerM.run_pure, h_run]
  obtain ⟨h_brun, baseOut, h_bval, h_bres⟩ :=
    placeToRegChecked_local_existing (kind := RefKind.Mut) h_dpi
  by_cases h_off : pathOffset path = 0
  · rw [h_off, projDstTail_zero]
    simp only [compileStmtChecked, compileRExprToChecked, h_rhs, readRhsPre, csMonad, h_proj_eq, h_root, h_sval]
    simp only [csCleanup, csRun, h_sclean, List.append_nil, emit_nil]
    rw [h_brun, h_bval]
    simp [h_off, dif_pos, CompilerM.run, CompilerM.value, emitM, cleanupInstrs,
      h_bres, emit_nil]
  · rw [projDstTail_pos _ h_off]
    simp only [compileStmtChecked, compileRExprToChecked, h_rhs, readRhsPre, csMonad, h_proj_eq, h_root, h_sval]
    simp only [csCleanup, csRun, h_sclean, List.append_nil, emit_nil]
    rw [h_brun, h_bval]
    simp [csRun, cleanupInstrs, h_bres, emit_nil, h_off, borrowRhs]
    try rfl

/-- REGIME copy, chain destination with a PROJ-TOPPED source at NONZERO
    offset (`*p := copy s.f` with the field off zero). The source
    projection mints its own `Borrow(Shared)`, the copy `Load`s through
    it, and the projection's cleanup `Die` retires it — all BEFORE the
    destination lowers, so BRIDGE 1S (`sb_ref_read_die_cancels`) is
    contiguous and the destination mother lemma simply runs at the
    post-`Die` states. Takes the `stmt0` transfer triple. -/
theorem copy_chaindst_projsrc_offset_simulation
    {τ τs σs : LayoutTy}
    {P : Place Γ (obseq.LayoutTy.PtrL τ)} {B : Place Γ σs}
    {spath : PathTo σs τs}
    {rhs : RExpr Γ τ} {mk : Register → Rhs}
    (compProg : oseair.Prog)
    (h_shape : ReadRhsShape rhs (.proj B spath) mk)
    (h_pkg : ReadPkgProjOffset compProg rhs B spath mk)
    (h_dchain : PtrChain (Place.deref P))
    (h_schain : PtrChain B)
    (h_o : pathOffset spath ≠ 0)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    {stmt0 : Stmt Γ}
    (h_stmt : prog.get? s_mir.pc = some stmt0)
    (h_run0 : ∀ cs, CheckedCompilerM.run (compileStmtChecked stmt0) cs
      = CheckedCompilerM.run
          (compileStmtChecked (Stmt.assign (.deref P) rhs)) cs)
    (h_val0 : ∀ cs so, CheckedCompilerM.value
        (compileStmtChecked (Stmt.assign (.deref P) rhs)) cs
        = Except.ok so →
      ∃ so', CheckedCompilerM.value (compileStmtChecked stmt0) cs
        = Except.ok so')
    (h_step : mirlite.stepStmt MSB s_mir
      (.assign (.deref P) rhs) = .ok s_mir') :
    ∃ (s_osea' : oseair.State MSB) (n : Nat),
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa ρt s_mir' s_osea' := by
  have h_np := h_schain.not_proj
  obtain ⟨csPrefix, ⟨h_csAt, h_pc⟩, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_tbd,
    h_alloc, h_unmap, h_prb⟩ := h_inv
  -- §1 invert the source: prepare is a no-op, the PROJECTED source
  -- resolves and is READ at its offset, and only THEN does the
  -- destination resolve
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
  simp only at h_step
  cases h_eval : mirlite.evalRExpr MSB s_mir rhs with
  | err e => rw [h_eval] at h_step; simp at h_step
  | ok output =>
    rw [h_eval] at h_step
    simp only at h_step
    obtain ⟨h_mappedP, h_pkg'⟩ :=
      h_pkg _ _ s_mir s_osea csPrefix h_id_a h_wf_t h_tbd h_lbs h_prb h_sms h_alloc
        h_psim h_pc output h_eval
    have h_mappedS : PlaceInputsMapped csPrefix B := h_mappedP
    -- §2 both places are mapped; the statement compiles
    have h_mappedD : PlaceInputsMapped csPrefix (Place.deref P) :=
      placeInputsMapped_of_localBindingSim_resolvePlace h_lbs h_resolved
    have h_root := ensurePlaceRoot_run_eq_of_mapped h_mappedD
    obtain ⟨sOut0, h_sval0⟩ := placeToRegChecked_ok_of_placeInputsMapped
      (cs := csPrefix) (kind := RefKind.Shared) h_mappedS
    have h_prmS : (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).placeRegMap = csPrefix.placeRegMap :=
      h_schain.placeToRegChecked_placeRegMap RefKind.Shared csPrefix
    obtain ⟨dOut0, h_dval0⟩ := placeToRegChecked_ok_of_placeInputsMapped
      (cs := 
                (emit
                  { (emit
                    { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix) with
                        nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg + 1 }
                    [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg)
                      (borrowRhs RefKind.Shared (blockSize τs) sOut0.result.reg (pathOffset spath))]) with
                      nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg + 1 + 1 }
                  ([Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg + 1)) (mk (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg))]
                    ++ cleanupInstrs (sOut0.result.cleanup ++ [((Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg), blockSize τs)])))) (kind := RefKind.Mut)
      (PlaceInputsMapped.placeRegMap_congr (by simp only [emit]; exact h_prmS)
        _ h_mappedD)
    obtain ⟨stmtOutC, h_stmtOutC⟩ :=
      compileStmt_readrhs_chaindst_projsrc_offset_value (h_shape := h_shape) h_np h_o h_root h_sval0 h_dval0
    obtain ⟨stmtOut, h_stmtOut⟩ := h_val0 csPrefix stmtOutC h_stmtOutC
    -- §3 code inclusion for the SOURCE lowering: the three facts, once,
    -- with the projection's Borrow supplied by the nonzero-offset equations
    obtain ⟨sOutP, h_svalP, h_regP, h_clP⟩ :=
      placeToRegChecked_proj_offset_value (kind := RefKind.Shared) spath h_np h_o h_sval0
    obtain ⟨h_incrS', h_incrCS1', h_incrDrun'⟩ :=
      readrhs_derefdst_incrs (h_shape := h_shape) csPrefix h_svalP
        (placeToRegChecked_proj_offset_run (kind := RefKind.Shared) spath h_np h_o h_sval0)
        h_root (h_run0 csPrefix)
    have h_incrS : StateIncr (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix)
        (CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix) :=
      StateIncr.trans (StateIncr.trans (freshReg_state_incr _) (emit_state_incr _ _)) h_incrS'
    have h_instS :=
      (CodeIncluded.of_stmt h_comp h_csAt h_stmt h_stmtOut).mono h_incrS
    -- §4-§7 the SOURCE package: mother, BRIDGE 1S, and the three
    -- instructions -- Borrow off the base, the rvalue's step, Die
    obtain ⟨h_sclean, nR, s_mid1, perms₂, vals, h_ost, h_vlen, h_runR, h_prmR,
      h_regmonoR, h_lbsR, h_psimR, h_tbdR, h_smem, h_pcR, h_vregR, h_vbelow, h_valsRel⟩ :=
      h_pkg' sOut0 h_sval0 _ h_regP h_clP h_instS
        ((CodeIncluded.of_stmt h_comp h_csAt h_stmt h_stmtOut).mono h_incrCS1')
    rw [h_ost] at h_step
    simp only at h_step
    cases h_dres : mirlite.resolvePlaceAcc MSB
        { s_mir with perms := perms₂ } (Place.deref P) with
    | error e => rw [h_dres] at h_step; simp at h_step
    | ok pr2 =>
    obtain ⟨rd, permsD⟩ := pr2
    rw [h_dres] at h_step
    simp only at h_step
    exact copy_chainwrite_after_read compProg h_dchain h_comp h_stmt h_csAt
      h_stmtOut h_id_a h_wf_t h_sms h_alloc h_unmap h_prb
      h_dres output.values_len h_step
      h_runR h_prmR h_regmonoR h_lbsR h_psimR h_tbdR h_smem h_pcR
      h_vregR h_vbelow h_vlen h_valsRel
      -- code inclusion for the DESTINATION lowering's own instructions,
      -- transported onto the post-`Die` tower the package landed on
      ((CodeIncluded.of_stmt h_comp h_csAt h_stmt h_stmtOut).mono
        (by have h := h_incrDrun'
            rw [h_regP, h_clP] at h
            simp only [csCleanup, h_sclean, List.nil_append, List.append_nil,
              List.reverse_cons, List.map_cons] at h
            csnorm at h ⊢
            exact h))
      (fun dOut h_dval h_dclean => (h_run0 csPrefix).trans
        (compileStmt_readrhs_chaindst_projsrc_offset_run (h_shape := h_shape) h_np h_o h_root h_sval0
          h_sclean h_dval h_dclean))

/-! ## Fresh root under a PROJECTED LOCAL destination with a copy rhs.
    `ensurePlaceRoot` allocates the root BEFORE the rhs pre-phase runs,
    so the source lowering and the `Load` sit on top of the `Alloc`, and
    the destination lowering is the fresh root's own register. -/

theorem compileStmt_readrhs_projlocal_fresh_value
    {Γ : Ctx} {τ τs σ : LayoutTy} {loc : Local Γ σ}
    {path : PathTo σ τ} {src : Place Γ τs} {cs : CompilerState}
    {sOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared src)}
    {rhs : RExpr Γ τ} {mk : Register → Rhs}
    (h_shape : ReadRhsShape rhs src mk)
    (h_pi : getPlaceInfo cs loc.idx.1 = none)
    (h_sval : CheckedCompilerM.value (placeToRegChecked RefKind.Shared src) (setPlaceInfo
          (emit { cs with nextReg := cs.nextReg + 1 }
            [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
          loc.idx.1 (Register.R cs.nextReg, σ))
      = Except.ok sOut)
    (h_dpi : getPlaceInfo (emit
          { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) (setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 } [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R cs.nextReg, σ))) with
            nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) (setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 } [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R cs.nextReg, σ))).nextReg + 1 }
          ([Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) (setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 } [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R cs.nextReg, σ))).nextReg)
            (mk sOut.result.reg)]
            ++ cleanupInstrs sOut.result.cleanup)) loc.idx.1 = some (Register.R cs.nextReg, σ)) :
    ∃ so, CheckedCompilerM.value
      (compileStmtChecked (Stmt.assign (.proj (.local loc) path) rhs)) cs
      = Except.ok so := by
  obtain ⟨ev, h_rhs⟩ := id h_shape
  obtain ⟨h_run, -⟩ := ensureLocalRegE_fresh (loc := loc) h_pi
  have h_proj_eq := placeToRegChecked_proj_root_eq (Γ := Γ) (kind := RefKind.Mut)
    (base := .local loc) path (fun _ _ _ h => by cases h)
  have h_root : CompilerM.run
      (ensurePlaceRoot (Place.proj (Place.local loc) path)) cs = (setPlaceInfo
          (emit { cs with nextReg := cs.nextReg + 1 }
            [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
          loc.idx.1 (Register.R cs.nextReg, σ)) := by
    show CompilerM.run (do let _ ← ensureLocalRegE loc; pure ()) cs = _
    simp [CompilerM.run_bind, CompilerM.run_pure, h_run]
  obtain ⟨h_brun, baseOut, h_bval, h_bres⟩ :=
    placeToRegChecked_local_existing (kind := RefKind.Mut) h_dpi
  simp only [compileStmtChecked, compileRExprToChecked, h_rhs, readRhsPre, csMonad, h_proj_eq, h_root, h_sval]
  simp only [csRun]
  rw [h_bval]
  by_cases h_off : pathOffset path = 0
  · simp only [h_off, dif_pos]
    exact ⟨_, rfl⟩
  · simp only [dif_neg h_off,
      CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
      CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
      CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
      CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM]
    exact ⟨_, rfl⟩

/-- Fresh projected destination, projected-chain source at nonzero source offset:
    one lemma for both DESTINATION offsets. -/
theorem compileStmt_readrhs_projlocal_fresh_projsrc_offset_run
    {Γ : Ctx} {τ τs σ σs : LayoutTy} {loc : Local Γ σ} {dpath : PathTo σ τ}
    {B : Place Γ σs} {spath : PathTo σs τs} {cs : CompilerState}
    {bOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared B)}
    {rhs : RExpr Γ τ} {mk : Register → Rhs}
    (h_shape : ReadRhsShape rhs (.proj B spath) mk)
    (h_npS : ∀ (σ' : LayoutTy) (b : Place Γ σ') (q : PathTo σ' σs),
      B = b.proj q → False)
    (h_so : pathOffset spath ≠ 0)
    (h_pi : getPlaceInfo cs loc.idx.1 = none)
    (h_bval : CheckedCompilerM.value (placeToRegChecked RefKind.Shared B) (setPlaceInfo
          (emit { cs with nextReg := cs.nextReg + 1 }
            [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
          loc.idx.1 (Register.R cs.nextReg, σ))
      = Except.ok bOut)
    (h_bclean : bOut.result.cleanup = [])
    (h_dpi : getPlaceInfo (emit
          { (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 } [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R cs.nextReg, σ))) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 } [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R cs.nextReg, σ))).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 } [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R cs.nextReg, σ))).nextReg) (borrowRhs RefKind.Shared (blockSize τs) bOut.result.reg (pathOffset spath))]) with
            nextReg := (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 } [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R cs.nextReg, σ))) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 } [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R cs.nextReg, σ))).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 } [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R cs.nextReg, σ))).nextReg) (borrowRhs RefKind.Shared (blockSize τs) bOut.result.reg (pathOffset spath))]).nextReg + 1 }
          [Instr.Assgn (Register.R (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 } [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R cs.nextReg, σ))) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 } [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R cs.nextReg, σ))).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 } [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R cs.nextReg, σ))).nextReg) (borrowRhs RefKind.Shared (blockSize τs) bOut.result.reg (pathOffset spath))]).nextReg) (mk (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 } [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R cs.nextReg, σ))).nextReg)),
           Instr.Die (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 } [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R cs.nextReg, σ))).nextReg) (blockSize τs)]) loc.idx.1 = some (Register.R cs.nextReg, σ)) :
    CheckedCompilerM.run
        (compileStmtChecked
          (Stmt.assign (.proj (.local loc) dpath) rhs)) cs
      = projDstTail (emit
          { (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 } [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R cs.nextReg, σ))) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 } [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R cs.nextReg, σ))).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 } [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R cs.nextReg, σ))).nextReg) (borrowRhs RefKind.Shared (blockSize τs) bOut.result.reg (pathOffset spath))]) with
            nextReg := (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 } [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R cs.nextReg, σ))) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 } [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R cs.nextReg, σ))).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 } [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R cs.nextReg, σ))).nextReg) (borrowRhs RefKind.Shared (blockSize τs) bOut.result.reg (pathOffset spath))]).nextReg + 1 }
          [Instr.Assgn (Register.R (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 } [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R cs.nextReg, σ))) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 } [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R cs.nextReg, σ))).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 } [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R cs.nextReg, σ))).nextReg) (borrowRhs RefKind.Shared (blockSize τs) bOut.result.reg (pathOffset spath))]).nextReg) (mk (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 } [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R cs.nextReg, σ))).nextReg)),
           Instr.Die (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 } [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R cs.nextReg, σ))).nextReg) (blockSize τs)])
          (pathOffset dpath) (blockSize τ) (layoutToTyVal τ)
          (Register.R (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 } [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R cs.nextReg, σ))) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 } [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R cs.nextReg, σ))).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 } [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R cs.nextReg, σ))).nextReg) (borrowRhs RefKind.Shared (blockSize τs) bOut.result.reg (pathOffset spath))]).nextReg) (Register.R cs.nextReg) := by
  obtain ⟨ev, h_rhs⟩ := id h_shape
  obtain ⟨h_run, -⟩ := ensureLocalRegE_fresh (loc := loc) h_pi
  have h_proj_eqS := placeToRegChecked_proj_root_eq (Γ := Γ)
    (kind := RefKind.Shared) (base := B) spath h_npS
  have h_proj_eqD := placeToRegChecked_proj_root_eq (Γ := Γ)
    (kind := RefKind.Mut) (base := Place.local loc) dpath (fun _ _ _ h => by cases h)
  have h_root : CompilerM.run
      (ensurePlaceRoot (Place.proj (Place.local loc) dpath)) cs = (setPlaceInfo
          (emit { cs with nextReg := cs.nextReg + 1 }
            [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
          loc.idx.1 (Register.R cs.nextReg, σ)) := by
    show CompilerM.run (do let _ ← ensureLocalRegE loc; pure ()) cs = _
    simp [CompilerM.run_bind, CompilerM.run_pure, h_run]
  obtain ⟨h_brun, baseOut, h_bval2, h_bres⟩ :=
    placeToRegChecked_local_existing (kind := RefKind.Mut) h_dpi
  by_cases h_do : pathOffset dpath = 0
  · rw [h_do, projDstTail_zero]
    simp only [compileStmtChecked, compileRExprToChecked, h_rhs, readRhsPre, csMonad, h_proj_eqS, h_proj_eqD, h_root, h_bval, dif_neg h_so]
    simp only [csCleanup, csRun, h_bclean, List.nil_append, List.cons_append, List.append_nil,
      List.reverse_cons, List.map_cons]
    simp only [csMonad, h_bval2, h_brun, h_do, dif_pos]
    simp only [csCleanup, CompilerM.run, CompilerM.value, emitM, h_bres, emit_nil]
  · rw [projDstTail_pos _ h_do]
    simp only [compileStmtChecked, compileRExprToChecked, h_rhs, readRhsPre, csMonad, h_proj_eqS, h_proj_eqD, h_root, h_bval, dif_neg h_so]
    simp only [csCleanup, csRun, h_bclean, List.nil_append, List.cons_append, List.append_nil,
      List.reverse_cons, List.map_cons]
    simp only [csMonad, h_bval2, h_brun, dif_neg h_do]
    simp [csRun, cleanupInstrs, h_bres, emit_nil, borrowRhs]
    try rfl

/-- Fresh projected root, ANY destination offset: the zero and nonzero
    leaves shared everything up to `h_incrS1V` verbatim (422 of 488
    lines, measured), so they are one theorem with the offset case split
    exactly at the first genuinely forked tactic. The nonzero branch is
    the `Borrow(Mut)`/`RStore`/`Die` write; the zero branch stores
    through the root register directly. -/
theorem copy_projlocal_fresh_simulation
    {τ τs σ : LayoutTy}
    {loc : Local Γ σ} {path : PathTo σ τ} {src : Place Γ τs}
    {rhs : RExpr Γ τ} {mk : Register → Rhs}
    (compProg : oseair.Prog)
    (h_shape : ReadRhsShape rhs src mk)
    (h_pkg : ReadPkgLowered compProg rhs src mk)
    (h_sprm0 : ∀ cs, (CheckedCompilerM.run
      (placeToRegChecked RefKind.Shared src) cs).placeRegMap = cs.placeRegMap)
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
    (h_envD : mirlite.Env.lookup s_mir.env loc = none)
    (h_step : mirlite.stepStmt MSB s_mir
      (.assign (.proj (.local loc) path) rhs) = .ok s_mir') :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' := by
  obtain ⟨ev, h_rhs⟩ := id h_shape
  obtain ⟨csPrefix, ⟨h_csAt, h_pc⟩, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_tbd,
    h_alloc, h_unmap, h_prb⟩ := h_inv
  have h_pi_none : getPlaceInfo csPrefix loc.idx.1 = none := h_unmap loc h_envD
  -- §1 the projected place does not resolve (its root is unbound), so
  -- `preparePlaceAssign` allocated the whole σ-sized root
  simp only [mirlite.stepStmt, mirlite.doAssign] at h_step
  cases h_prep : mirlite.preparePlaceAssign MSB s_mir
      (Place.proj (Place.local loc) path) with
  | err msg => rw [h_prep] at h_step; simp at h_step
  | ok s1 =>
  rw [h_prep] at h_step
  rw [show mirlite.preparePlaceAssign MSB s_mir (Place.proj (Place.local loc) path)
      = mirlite.allocateBase MSB s_mir loc from by
    simp only [mirPrep, mirAlloc, h_envD]] at h_prep
  -- §2 the allocation prologue: both roots, both renames, and the
  -- post-`Alloc` states a source package starts from
  have h_incr_a :=
    AddrRenameIncr.extendBlock h_id_a s_mir.mem.addrStart (blockSize σ)
  have h_id_a' :=
    IdentityOnDomain.extendBlock h_id_a s_mir.mem.addrStart (blockSize σ)
  have h_ra_dom : ∀ k, k < blockSize σ →
      (ρa.extendBlock s_mir.mem.addrStart (blockSize σ))
        (s_mir.mem.addrStart + k) = some (s_mir.mem.addrStart + k) :=
    fun _ hk => AddrRenameMap.extendBlock_mem hk
  obtain ⟨permsOwned, tgtPerms, h_own_tgt', h_perms1, h_pc1, h_env1,
    h_lookup_set, h_memstart1, h_allocs1, h_find1, h_incr_t, h_wf_t', h_tbd', h_psim',
    h_erunL, h_prb1, h_lbs1⟩ :=
    copy_freshroot_prologue h_envD h_prep h_wf_t h_tbd h_psim h_alloc
      h_lbs h_prb h_pi_none h_incr_a (AddrRenameMap.extendBlock_base _ _ _)
      h_ra_dom
  have h_addr_eq : s_osea.mem.addrStart = s_mir.mem.addrStart := h_alloc.1
  -- §3 the source read, kept OPAQUE behind the rvalue's package
  simp only at h_step
  cases h_eval : mirlite.evalRExpr MSB s1 rhs with
  | err e => rw [h_eval] at h_step; simp at h_step
  | ok output =>
    rw [h_eval] at h_step
    simp only at h_step
    obtain ⟨h_mappedS, h_pkg'⟩ :=
      h_pkg _ _ s1
        { s_osea with
            mem := (oseair.allocate s_osea.mem
              (obseq.typeSize (layoutToTyVal σ))).2,
            perms := tgtPerms,
            reg := oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
              (obseq.TyVal.PTy, [Val.Ptr s_osea.mem.addrStart 0
                (obseq.typeSize (layoutToTyVal σ)) s_osea.perms.NextTag]),
            pc := s_osea.pc + 1 }
        (setPlaceInfo
          (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
            [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
          loc.idx.1 (Register.R csPrefix.nextReg, σ))
        h_id_a' h_wf_t' (by rw [h_perms1]; exact h_tbd') h_lbs1 h_prb1
        (by
          intro a v h_find
          rw [h_find1] at h_find
          exact SourceMemSim.rename_mono h_incr_a h_incr_t h_sms a v h_find)
        (AllocLockstep.of_alloc h_alloc h_incr_a (obseq.typeSize_layoutToTyVal _) h_memstart1 h_allocs1)
        (by rw [h_perms1]; exact h_psim')
        (by
          show s_osea.pc + 1 = _
          rw [h_pc]
          simp only [emit, setPlaceInfo, List.length_cons, List.length_nil])
        output h_eval
    -- §4 the compiled prefix: the root `Alloc` and the post-alloc state
    have h_erun : CompilerM.run (ensurePlaceRoot (Place.proj (Place.local loc) path))
        csPrefix = (setPlaceInfo
          (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
            [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
          loc.idx.1 (Register.R csPrefix.nextReg, σ)) := by
      show CompilerM.run (do let _ ← ensureLocalRegE loc; pure ()) csPrefix = _
      simp [CompilerM.run_bind, CompilerM.run_pure,
        (ensureLocalRegE_fresh (loc := loc) h_pi_none).1]
    have h_pi_new : getPlaceInfo (setPlaceInfo
          (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
            [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
          loc.idx.1 (Register.R csPrefix.nextReg, σ)) loc.idx.1
        = some (Register.R csPrefix.nextReg, σ) :=
      getPlaceInfo_setPlaceInfo_self _ _ _
    have h_sz : obseq.typeSize (layoutToTyVal σ) = blockSize σ :=
      obseq.typeSize_layoutToTyVal _
    -- §5 the statement value and code inclusion for the source lowering
    obtain ⟨sOut0, h_sval0⟩ := placeToRegChecked_ok_of_placeInputsMapped
      (cs := (setPlaceInfo
          (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
            [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
          loc.idx.1 (Register.R csPrefix.nextReg, σ))) (kind := RefKind.Shared)
      h_mappedS
    have h_prmS : (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R csPrefix.nextReg, σ))).placeRegMap = (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R csPrefix.nextReg, σ)).placeRegMap :=
      h_sprm0 (setPlaceInfo
          (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
            [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
          loc.idx.1 (Register.R csPrefix.nextReg, σ))
    have h_dpi0 : getPlaceInfo (emit
          { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R csPrefix.nextReg, σ))) with
            nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R csPrefix.nextReg, σ))).nextReg + 1 }
          ([Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R csPrefix.nextReg, σ))).nextReg)
            (mk sOut0.result.reg)]
            ++ cleanupInstrs sOut0.result.cleanup)) loc.idx.1
        = some (Register.R csPrefix.nextReg, σ) := by
      show (emit _ _).placeRegMap.lookup _ = _
      simp only [emit]
      show (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R csPrefix.nextReg, σ))).placeRegMap.lookup _ = _
      rw [h_prmS]
      exact h_pi_new
    obtain ⟨stmtOutC, h_stmtOutC⟩ :=
      compileStmt_readrhs_projlocal_fresh_value (h_shape := h_shape) h_pi_none h_sval0 h_dpi0
    obtain ⟨stmtOut, h_stmtOut⟩ := h_val0 csPrefix stmtOutC h_stmtOutC
    -- the source tower is a GROUND prefix; the destination side is the
    -- short chain (see durable/transport-compiled-states-by-defeq)
    have h_incrPre : StateIncr (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R csPrefix.nextReg, σ))) (emit
          { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R csPrefix.nextReg, σ))) with
            nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R csPrefix.nextReg, σ))).nextReg + 1 }
          ([Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R csPrefix.nextReg, σ))).nextReg)
            (mk sOut0.result.reg)]
            ++ cleanupInstrs sOut0.result.cleanup)) :=
      StateIncr.trans (freshReg_state_incr (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R csPrefix.nextReg, σ))))
        (emit_state_incr _
          ([Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R csPrefix.nextReg, σ))).nextReg)
              (mk sOut0.result.reg)]
            ++ cleanupInstrs sOut0.result.cleanup))
    obtain ⟨h_brun0, baseOut0, h_bval0, h_bres0⟩ :=
      placeToRegChecked_local_existing (kind := RefKind.Mut) h_dpi0
    have h_incrS1V : StateIncr (emit
          { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R csPrefix.nextReg, σ))) with
            nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R csPrefix.nextReg, σ))).nextReg + 1 }
          ([Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R csPrefix.nextReg, σ))).nextReg)
            (mk sOut0.result.reg)]
            ++ cleanupInstrs sOut0.result.cleanup))
        (CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix) := by
      rw [h_run0]
      have h_proj_eq := placeToRegChecked_proj_root_eq (Γ := Γ) (kind := RefKind.Mut)
        (base := Place.local loc) path (fun _ _ _ h => by cases h)
      simp only [compileStmtChecked, compileRExprToChecked, h_rhs, readRhsPre, csMonad, h_proj_eq, h_erun, h_sval0]
      simp only [csRun]
      by_cases h_o : pathOffset path = 0
      · simp only [csMonad, h_bval0, h_brun0, h_o, dif_pos]
        simp only [csCleanup, CompilerM.run, CompilerM.value, emitM, h_bres0, emit_nil]
        exact emit_state_incr _ _
      · simp only [csMonad, h_bval0, h_brun0, h_o, dif_pos]
        simp only [csCleanup, csRun, h_bres0, List.nil_append, List.reverse_cons, List.map_cons]
        exact StateIncr.trans (freshReg_state_incr _)
          (StateIncr.trans (emit_state_incr _ _)
            (StateIncr.trans (emit_state_incr _ _)
              (StateIncr.trans (emit_state_incr _ _) (emit_state_incr _ _))))
    have h_incrS : StateIncr (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R csPrefix.nextReg, σ)))
        (CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix) :=
      StateIncr.trans h_incrPre h_incrS1V
    have h_instS :=
      (CodeIncluded.of_stmt h_comp h_csAt h_stmt h_stmtOut).mono h_incrS
    -- §6 execute the `Alloc`
    have hFragA := ((CodeIncluded.of_stmt h_comp h_csAt h_stmt h_stmtOut).mono
      (StateIncr.trans (CheckedCompilerM.incr _ _) h_incrS)).fragmentOf
      (base := csPrefix.nextLabel) rfl rfl
    have h_code0 : compProg s_osea.pc
        = some (Instr.Assgn (Register.R csPrefix.nextReg)
            (Rhs.Alloc (layoutToTyVal σ))) := by
      rw [h_pc]; exact hFragA.instrAt 0 rfl rfl
    have h_runAlloc := runN_Assgn_Alloc_step compProg s_osea
      (Register.R csPrefix.nextReg) (layoutToTyVal σ) h_code0 h_own_tgt'
    -- §7 the SOURCE package at the post-allocation states, under the
    -- extended renames: mother, read transport, the rvalue's step
    obtain ⟨h_sclean, nR, s_mid, perms₂, vals, h_ost, h_vlen, h_runR, h_prmR,
      h_regmonoR, h_lbsR, h_psimR, h_tbdR, h_smem, h_pcR, h_vregR, h_vbelow, h_rel⟩ :=
      h_pkg' sOut0 h_sval0 h_instS
        ((CodeIncluded.of_stmt h_comp h_csAt h_stmt h_stmtOut).mono h_incrS1V)
    rw [h_ost] at h_step
    simp only [mirlite.resolvePlaceAcc, h_lookup_set] at h_step
    have h_dpi : getPlaceInfo (emit
        { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src)
        (setPlaceInfo
          (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
            [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
          loc.idx.1 (Register.R csPrefix.nextReg, σ))) with
          nextReg := ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared src)
        (setPlaceInfo
          (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
            [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
          loc.idx.1 (Register.R csPrefix.nextReg, σ)))).nextReg + 1 }
        [Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared src)
        (setPlaceInfo
          (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
            [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
          loc.idx.1 (Register.R csPrefix.nextReg, σ)))).nextReg)
          (mk sOut0.result.reg)]) loc.idx.1
        = some (Register.R csPrefix.nextReg, σ) := by
      show ((emit
        { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src)
        (setPlaceInfo
          (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
            [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
          loc.idx.1 (Register.R csPrefix.nextReg, σ))) with
          nextReg := ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared src)
        (setPlaceInfo
          (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
            [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
          loc.idx.1 (Register.R csPrefix.nextReg, σ)))).nextReg + 1 }
        [Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared src)
        (setPlaceInfo
          (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
            [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
          loc.idx.1 (Register.R csPrefix.nextReg, σ)))).nextReg)
          (mk sOut0.result.reg)])).placeRegMap.lookup _ = _
      rw [h_prmR]
      exact h_pi_new
    have h_stmtRun := (h_run0 csPrefix).trans
      (compileStmt_readrhs_projlocal_fresh_run (h_shape := h_shape) h_pi_none h_sval0 h_sclean h_dpi)
    -- §8-§11 the fresh WRITE seam at the projection's offset: a σ-sized root,
    -- a τ-sized value
    exact copy_fresh_write_after_read
      (τ := τ)
      (csR := emit
        { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src)
        (setPlaceInfo
          (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
            [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
          loc.idx.1 (Register.R csPrefix.nextReg, σ))) with
          nextReg := ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared src)
        (setPlaceInfo
          (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
            [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
          loc.idx.1 (Register.R csPrefix.nextReg, σ)))).nextReg + 1 }
        [Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared src)
        (setPlaceInfo
          (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
            [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
          loc.idx.1 (Register.R csPrefix.nextReg, σ)))).nextReg)
          (mk sOut0.result.reg)])
      (vreg := Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared src)
        (setPlaceInfo
          (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
            [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
          loc.idx.1 (Register.R csPrefix.nextReg, σ)))).nextReg)
      (mvals := output.values)
      compProg h_comp h_stmt h_csAt h_stmtOut h_sms h_unmap
      h_lookup_set h_env1 h_pc1 h_memstart1 h_allocs1 h_alloc h_find1 h_addr_eq h_sz h_runAlloc
      h_incr_a h_incr_t h_id_a' h_wf_t' h_ra_dom h_prb1 (pathOffset path)
      (PathTo.offset_add_size_le path)
      h_runR h_prmR h_regmonoR h_lbsR h_psimR h_tbdR h_smem h_pcR
      h_vregR h_vbelow h_vlen
      h_stmtRun
      output.values_len rfl rfl rfl rfl h_rel h_step
/-! ## Fresh root under a PROJECTED LOCAL destination, with a
    PROJ-TOPPED source at NONZERO offset. The root `Alloc` comes first,
    then the source projection's `Borrow(Shared)`, the copy's `Load`,
    and the source projection's cleanup `Die`; only then does the
    destination lower. -/

theorem compileStmt_readrhs_projlocal_fresh_projsrc_offset_value
    {Γ : Ctx} {τ τs σ σs : LayoutTy} {loc : Local Γ σ} {dpath : PathTo σ τ}
    {B : Place Γ σs} {spath : PathTo σs τs} {cs : CompilerState}
    {bOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared B)}
    {rhs : RExpr Γ τ} {mk : Register → Rhs}
    (h_shape : ReadRhsShape rhs (.proj B spath) mk)
    (h_npS : ∀ (σ' : LayoutTy) (b : Place Γ σ') (q : PathTo σ' σs),
      B = b.proj q → False)
    (h_so : pathOffset spath ≠ 0)
    (h_pi : getPlaceInfo cs loc.idx.1 = none)
    (h_bval : CheckedCompilerM.value (placeToRegChecked RefKind.Shared B) (setPlaceInfo
          (emit { cs with nextReg := cs.nextReg + 1 }
            [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
          loc.idx.1 (Register.R cs.nextReg, σ))
      = Except.ok bOut)
    (h_dpi : getPlaceInfo (emit
          { (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 } [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R cs.nextReg, σ))) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 } [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R cs.nextReg, σ))).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 } [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R cs.nextReg, σ))).nextReg) (borrowRhs RefKind.Shared (blockSize τs) bOut.result.reg (pathOffset spath))]) with
            nextReg := (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 } [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R cs.nextReg, σ))) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 } [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R cs.nextReg, σ))).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 } [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R cs.nextReg, σ))).nextReg) (borrowRhs RefKind.Shared (blockSize τs) bOut.result.reg (pathOffset spath))]).nextReg + 1 }
          ([Instr.Assgn (Register.R (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 } [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R cs.nextReg, σ))) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 } [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R cs.nextReg, σ))).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 } [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R cs.nextReg, σ))).nextReg) (borrowRhs RefKind.Shared (blockSize τs) bOut.result.reg (pathOffset spath))]).nextReg) (mk (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 } [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R cs.nextReg, σ))).nextReg))]
            ++ cleanupInstrs (bOut.result.cleanup ++ [((Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 } [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R cs.nextReg, σ))).nextReg), blockSize τs)]))) loc.idx.1 = some (Register.R cs.nextReg, σ)) :
    ∃ so, CheckedCompilerM.value
      (compileStmtChecked
        (Stmt.assign (.proj (.local loc) dpath) rhs)) cs
      = Except.ok so := by
  obtain ⟨ev, h_rhs⟩ := id h_shape
  obtain ⟨h_run, -⟩ := ensureLocalRegE_fresh (loc := loc) h_pi
  have h_proj_eqS := placeToRegChecked_proj_root_eq (Γ := Γ)
    (kind := RefKind.Shared) (base := B) spath h_npS
  have h_proj_eqD := placeToRegChecked_proj_root_eq (Γ := Γ)
    (kind := RefKind.Mut) (base := Place.local loc) dpath (fun _ _ _ h => by cases h)
  have h_root : CompilerM.run
      (ensurePlaceRoot (Place.proj (Place.local loc) dpath)) cs = (setPlaceInfo
          (emit { cs with nextReg := cs.nextReg + 1 }
            [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
          loc.idx.1 (Register.R cs.nextReg, σ)) := by
    show CompilerM.run (do let _ ← ensureLocalRegE loc; pure ()) cs = _
    simp [CompilerM.run_bind, CompilerM.run_pure, h_run]
  obtain ⟨h_brun, baseOut, h_bval2, h_bres⟩ :=
    placeToRegChecked_local_existing (kind := RefKind.Mut) h_dpi
  simp only [compileStmtChecked, compileRExprToChecked, h_rhs, readRhsPre, csMonad, h_proj_eqS, h_proj_eqD, h_root, h_bval, dif_neg h_so]
  simp only [csRun]
  simp only [h_bval2]
  by_cases h_do : pathOffset dpath = 0
  · simp only [h_do, dif_pos]
    exact ⟨_, rfl⟩
  · simp only [dif_neg h_do,
      CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
      CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
      CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
      CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM]
    exact ⟨_, rfl⟩

/-- Fresh projected root, PROJECTED source at nonzero offset, ANY
    destination offset — the destination-offset twin pair merged the same
    way as `copy_projlocal_fresh_simulation`: identical through
    `h_incrS1V` (194 shared lines), forked exactly there. -/
theorem copy_projlocal_fresh_projsrc_simulation
    {τ τs σ σs : LayoutTy}
    {loc : Local Γ σ} {path : PathTo σ τ}
    {B : Place Γ σs} {spath : PathTo σs τs}
    {rhs : RExpr Γ τ} {mk : Register → Rhs}
    (compProg : oseair.Prog)
    (h_shape : ReadRhsShape rhs (.proj B spath) mk)
    (h_pkg : ReadPkgProjOffset compProg rhs B spath mk)
    (h_schain : PtrChain B)
    (h_so : pathOffset spath ≠ 0)
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
    (h_envD : mirlite.Env.lookup s_mir.env loc = none)
    (h_step : mirlite.stepStmt MSB s_mir
      (.assign (.proj (.local loc) path) rhs) = .ok s_mir') :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' := by
  obtain ⟨ev, h_rhs⟩ := id h_shape
  obtain ⟨csPrefix, ⟨h_csAt, h_pc⟩, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_tbd,
    h_alloc, h_unmap, h_prb⟩ := h_inv
  have h_pi_none : getPlaceInfo csPrefix loc.idx.1 = none := h_unmap loc h_envD
  -- §1 the projected place does not resolve (its root is unbound), so
  -- `preparePlaceAssign` allocated the whole σ-sized root
  simp only [mirlite.stepStmt, mirlite.doAssign] at h_step
  cases h_prep : mirlite.preparePlaceAssign MSB s_mir
      (Place.proj (Place.local loc) path) with
  | err msg => rw [h_prep] at h_step; simp at h_step
  | ok s1 =>
  rw [h_prep] at h_step
  rw [show mirlite.preparePlaceAssign MSB s_mir (Place.proj (Place.local loc) path)
      = mirlite.allocateBase MSB s_mir loc from by
    simp only [mirPrep, mirAlloc, h_envD]] at h_prep
  -- §2 the allocation prologue: both roots, both renames, and the
  -- post-`Alloc` states a source package starts from
  have h_incr_a :=
    AddrRenameIncr.extendBlock h_id_a s_mir.mem.addrStart (blockSize σ)
  have h_id_a' :=
    IdentityOnDomain.extendBlock h_id_a s_mir.mem.addrStart (blockSize σ)
  have h_ra_dom : ∀ k, k < blockSize σ →
      (ρa.extendBlock s_mir.mem.addrStart (blockSize σ))
        (s_mir.mem.addrStart + k) = some (s_mir.mem.addrStart + k) :=
    fun _ hk => AddrRenameMap.extendBlock_mem hk
  obtain ⟨permsOwned, tgtPerms, h_own_tgt', h_perms1, h_pc1, h_env1,
    h_lookup_set, h_memstart1, h_allocs1, h_find1, h_incr_t, h_wf_t', h_tbd', h_psim',
    h_erunL, h_prb1, h_lbs1⟩ :=
    copy_freshroot_prologue h_envD h_prep h_wf_t h_tbd h_psim h_alloc
      h_lbs h_prb h_pi_none h_incr_a (AddrRenameMap.extendBlock_base _ _ _)
      h_ra_dom
  have h_addr_eq : s_osea.mem.addrStart = s_mir.mem.addrStart := h_alloc.1
  -- §3 the source read, kept OPAQUE behind the rvalue's package
  simp only at h_step
  have h_np := h_schain.not_proj
  cases h_eval : mirlite.evalRExpr MSB s1 rhs with
  | err e => rw [h_eval] at h_step; simp at h_step
  | ok output =>
    rw [h_eval] at h_step
    simp only at h_step
    obtain ⟨h_mappedP, h_pkg'⟩ :=
      h_pkg _ _ s1
        { s_osea with
            mem := (oseair.allocate s_osea.mem
              (obseq.typeSize (layoutToTyVal σ))).2,
            perms := tgtPerms,
            reg := oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
              (obseq.TyVal.PTy, [Val.Ptr s_osea.mem.addrStart 0
                (obseq.typeSize (layoutToTyVal σ)) s_osea.perms.NextTag]),
            pc := s_osea.pc + 1 }
        (setPlaceInfo
          (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
            [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
          loc.idx.1 (Register.R csPrefix.nextReg, σ))
        h_id_a' h_wf_t' (by rw [h_perms1]; exact h_tbd') h_lbs1 h_prb1
        (by
          intro a v h_find
          rw [h_find1] at h_find
          exact SourceMemSim.rename_mono h_incr_a h_incr_t h_sms a v h_find)
        (AllocLockstep.of_alloc h_alloc h_incr_a (obseq.typeSize_layoutToTyVal _) h_memstart1 h_allocs1)
        (by rw [h_perms1]; exact h_psim')
        (by
          show s_osea.pc + 1 = _
          rw [h_pc]
          simp only [emit, setPlaceInfo, List.length_cons, List.length_nil])
        output h_eval
    have h_mappedB : PlaceInputsMapped
        (setPlaceInfo
          (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
            [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
          loc.idx.1 (Register.R csPrefix.nextReg, σ)) B := h_mappedP
    -- §4 the compiled prefix: the root `Alloc` and the post-alloc state
    have h_erun : CompilerM.run (ensurePlaceRoot (Place.proj (Place.local loc) path))
        csPrefix = (setPlaceInfo
          (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
            [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
          loc.idx.1 (Register.R csPrefix.nextReg, σ)) := by
      show CompilerM.run (do let _ ← ensureLocalRegE loc; pure ()) csPrefix = _
      simp [CompilerM.run_bind, CompilerM.run_pure,
        (ensureLocalRegE_fresh (loc := loc) h_pi_none).1]
    have h_pi_new : getPlaceInfo (setPlaceInfo
          (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
            [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
          loc.idx.1 (Register.R csPrefix.nextReg, σ)) loc.idx.1
        = some (Register.R csPrefix.nextReg, σ) :=
      getPlaceInfo_setPlaceInfo_self _ _ _
    have h_sz : obseq.typeSize (layoutToTyVal σ) = blockSize σ :=
      obseq.typeSize_layoutToTyVal _
    -- §5 the statement value and code inclusion for the source lowering
    obtain ⟨sOut0, h_sval0⟩ := placeToRegChecked_ok_of_placeInputsMapped
      (cs := (setPlaceInfo
          (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
            [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
          loc.idx.1 (Register.R csPrefix.nextReg, σ))) (kind := RefKind.Shared)
      h_mappedB
    have h_prmS : (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R csPrefix.nextReg, σ))).placeRegMap = (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R csPrefix.nextReg, σ)).placeRegMap :=
      h_schain.placeToRegChecked_placeRegMap RefKind.Shared (setPlaceInfo
          (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
            [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
          loc.idx.1 (Register.R csPrefix.nextReg, σ))
    have h_dpi0 : getPlaceInfo (emit
          { (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R csPrefix.nextReg, σ))) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R csPrefix.nextReg, σ))).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R csPrefix.nextReg, σ))).nextReg) (borrowRhs RefKind.Shared (blockSize τs) sOut0.result.reg (pathOffset spath))]) with
            nextReg := (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R csPrefix.nextReg, σ))) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R csPrefix.nextReg, σ))).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R csPrefix.nextReg, σ))).nextReg) (borrowRhs RefKind.Shared (blockSize τs) sOut0.result.reg (pathOffset spath))]).nextReg + 1 } ([Instr.Assgn (Register.R (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R csPrefix.nextReg, σ))) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R csPrefix.nextReg, σ))).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R csPrefix.nextReg, σ))).nextReg) (borrowRhs RefKind.Shared (blockSize τs) sOut0.result.reg (pathOffset spath))]).nextReg) (mk (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R csPrefix.nextReg, σ))).nextReg))] ++ cleanupInstrs (sOut0.result.cleanup ++ [((Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R csPrefix.nextReg, σ))).nextReg), blockSize τs)]))) loc.idx.1
        = some (Register.R csPrefix.nextReg, σ) := by
      show (emit _ _).placeRegMap.lookup _ = _
      simp only [emit]
      show (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R csPrefix.nextReg, σ))).placeRegMap.lookup _ = _
      rw [h_prmS]
      exact h_pi_new
    obtain ⟨stmtOutC, h_stmtOutC⟩ :=
      compileStmt_readrhs_projlocal_fresh_projsrc_offset_value (h_shape := h_shape) h_schain.not_proj h_so
        h_pi_none h_sval0 h_dpi0
    obtain ⟨stmtOut, h_stmtOut⟩ := h_val0 csPrefix stmtOutC h_stmtOutC
    -- the source tower is a GROUND prefix; the destination side is the
    -- short chain (see durable/transport-compiled-states-by-defeq)
    have h_incrPre : StateIncr (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R csPrefix.nextReg, σ))) (emit
          { (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R csPrefix.nextReg, σ))) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R csPrefix.nextReg, σ))).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R csPrefix.nextReg, σ))).nextReg) (borrowRhs RefKind.Shared (blockSize τs) sOut0.result.reg (pathOffset spath))]) with
            nextReg := (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R csPrefix.nextReg, σ))) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R csPrefix.nextReg, σ))).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R csPrefix.nextReg, σ))).nextReg) (borrowRhs RefKind.Shared (blockSize τs) sOut0.result.reg (pathOffset spath))]).nextReg + 1 } ([Instr.Assgn (Register.R (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R csPrefix.nextReg, σ))) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R csPrefix.nextReg, σ))).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R csPrefix.nextReg, σ))).nextReg) (borrowRhs RefKind.Shared (blockSize τs) sOut0.result.reg (pathOffset spath))]).nextReg) (mk (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R csPrefix.nextReg, σ))).nextReg))] ++ cleanupInstrs (sOut0.result.cleanup ++ [((Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R csPrefix.nextReg, σ))).nextReg), blockSize τs)]))) :=
      StateIncr.trans (freshReg_state_incr (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R csPrefix.nextReg, σ))))
        (StateIncr.trans
          (emit_state_incr _
            [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R csPrefix.nextReg, σ))).nextReg)
              (borrowRhs RefKind.Shared (blockSize τs) sOut0.result.reg (pathOffset spath))])
          (StateIncr.trans (freshReg_state_incr (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R csPrefix.nextReg, σ))) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R csPrefix.nextReg, σ))).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R csPrefix.nextReg, σ))).nextReg) (borrowRhs RefKind.Shared (blockSize τs) sOut0.result.reg (pathOffset spath))]))
            (emit_state_incr _
              ([Instr.Assgn (Register.R (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R csPrefix.nextReg, σ))) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R csPrefix.nextReg, σ))).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R csPrefix.nextReg, σ))).nextReg) (borrowRhs RefKind.Shared (blockSize τs) sOut0.result.reg (pathOffset spath))]).nextReg) (mk (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R csPrefix.nextReg, σ))).nextReg))]
                ++ cleanupInstrs (sOut0.result.cleanup ++ [(Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R csPrefix.nextReg, σ))).nextReg, blockSize τs)])))))
    obtain ⟨h_brun0, baseOut0, h_bval0, h_bres0⟩ :=
      placeToRegChecked_local_existing (kind := RefKind.Mut) h_dpi0
    have h_incrS1V : StateIncr (emit
          { (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R csPrefix.nextReg, σ))) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R csPrefix.nextReg, σ))).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R csPrefix.nextReg, σ))).nextReg) (borrowRhs RefKind.Shared (blockSize τs) sOut0.result.reg (pathOffset spath))]) with
            nextReg := (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R csPrefix.nextReg, σ))) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R csPrefix.nextReg, σ))).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R csPrefix.nextReg, σ))).nextReg) (borrowRhs RefKind.Shared (blockSize τs) sOut0.result.reg (pathOffset spath))]).nextReg + 1 } ([Instr.Assgn (Register.R (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R csPrefix.nextReg, σ))) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R csPrefix.nextReg, σ))).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R csPrefix.nextReg, σ))).nextReg) (borrowRhs RefKind.Shared (blockSize τs) sOut0.result.reg (pathOffset spath))]).nextReg) (mk (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R csPrefix.nextReg, σ))).nextReg))] ++ cleanupInstrs (sOut0.result.cleanup ++ [((Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R csPrefix.nextReg, σ))).nextReg), blockSize τs)])))
        (CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix) := by
      rw [h_run0]
      have h_proj_eq := placeToRegChecked_proj_root_eq (Γ := Γ) (kind := RefKind.Mut)
        (base := Place.local loc) path (fun _ _ _ h => by cases h)
      simp only [compileStmtChecked, compileRExprToChecked, h_rhs, readRhsPre, csMonad, h_proj_eq,
        placeToRegChecked_proj_root_eq (Γ := Γ) (kind := RefKind.Shared) (base := B) spath h_schain.not_proj,
        h_erun, h_sval0, dif_neg h_so]
      simp only [csRun]
      by_cases h_o : pathOffset path = 0
      · simp only [csMonad, h_bval0, h_brun0, h_o, dif_pos]
        simp only [csCleanup, CompilerM.run, CompilerM.value, emitM, h_bres0, emit_nil]
        exact emit_state_incr _ _
      · simp only [csMonad, h_bval0, h_brun0, dif_neg h_o]
        simp only [csCleanup, CompilerM.run, CompilerM.value, emitM, h_bres0, emit_nil]
        exact StateIncr.trans (freshReg_state_incr _)
          (StateIncr.trans (emit_state_incr _ _)
            (StateIncr.trans (emit_state_incr _ _) (emit_state_incr _ _)))
    have h_incrS : StateIncr (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) loc.idx.1 (Register.R csPrefix.nextReg, σ)))
        (CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix) :=
      StateIncr.trans h_incrPre h_incrS1V
    have h_instS :=
      (CodeIncluded.of_stmt h_comp h_csAt h_stmt h_stmtOut).mono h_incrS
    -- §6 execute the `Alloc`
    have hFragA := ((CodeIncluded.of_stmt h_comp h_csAt h_stmt h_stmtOut).mono
      (StateIncr.trans (CheckedCompilerM.incr _ _) h_incrS)).fragmentOf
      (base := csPrefix.nextLabel) rfl rfl
    have h_code0 : compProg s_osea.pc
        = some (Instr.Assgn (Register.R csPrefix.nextReg)
            (Rhs.Alloc (layoutToTyVal σ))) := by
      rw [h_pc]; exact hFragA.instrAt 0 rfl rfl
    have h_runAlloc := runN_Assgn_Alloc_step compProg s_osea
      (Register.R csPrefix.nextReg) (layoutToTyVal σ) h_code0 h_own_tgt'
    obtain ⟨sOutP, h_svalP, h_regP, h_clP⟩ :=
      placeToRegChecked_proj_offset_value (kind := RefKind.Shared) spath h_np h_so
        h_sval0
    -- §7 the SOURCE package at the post-allocation states: mother,
    -- BRIDGE 1S, and the projection's Borrow / rvalue step / Die
    obtain ⟨h_sclean, nR, s_mid, perms₂, vals, h_ost, h_vlen, h_runR, h_prmR,
      h_regmonoR, h_lbsR, h_psimR, h_tbdR, h_smem, h_pcR, h_vregR, h_vbelow, h_rel⟩ :=
      h_pkg' sOut0 h_sval0 _ h_regP h_clP h_instS
        (by
          rw [h_regP, h_clP]
          exact (CodeIncluded.of_stmt h_comp h_csAt h_stmt h_stmtOut).mono
            h_incrS1V)
    rw [h_ost] at h_step
    simp only [mirlite.resolvePlaceAcc, h_lookup_set] at h_step
    have h_dpi : getPlaceInfo (emit
          { (emit
          { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
          (setPlaceInfo
            (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
              [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
            loc.idx.1 (Register.R csPrefix.nextReg, σ))) with nextReg := ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
          (setPlaceInfo
            (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
              [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
            loc.idx.1 (Register.R csPrefix.nextReg, σ)))).nextReg + 1 }
          [Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
          (setPlaceInfo
            (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
              [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
            loc.idx.1 (Register.R csPrefix.nextReg, σ)))).nextReg)
            (borrowRhs RefKind.Shared (blockSize τs) sOut0.result.reg
              (pathOffset spath))]) with
            nextReg := ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
          (setPlaceInfo
            (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
              [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
            loc.idx.1 (Register.R csPrefix.nextReg, σ)))).nextReg + 1 + 1 }
          [Instr.Assgn (Register.R (((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
          (setPlaceInfo
            (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
              [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
            loc.idx.1 (Register.R csPrefix.nextReg, σ)))).nextReg + 1))
              (mk (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
          (setPlaceInfo
            (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
              [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
            loc.idx.1 (Register.R csPrefix.nextReg, σ)))).nextReg)),
            Instr.Die (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
          (setPlaceInfo
            (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
              [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
            loc.idx.1 (Register.R csPrefix.nextReg, σ)))).nextReg) (blockSize τs)]) loc.idx.1
        = some (Register.R csPrefix.nextReg, σ) := by
      show getPlaceInfo (emit _ _) loc.idx.1 = _
      rw [getPlaceInfo_emit]
      show ((emit
          { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
          (setPlaceInfo
            (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
              [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
            loc.idx.1 (Register.R csPrefix.nextReg, σ))) with nextReg := ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
          (setPlaceInfo
            (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
              [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
            loc.idx.1 (Register.R csPrefix.nextReg, σ)))).nextReg + 1 }
          [Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
          (setPlaceInfo
            (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
              [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
            loc.idx.1 (Register.R csPrefix.nextReg, σ)))).nextReg)
            (borrowRhs RefKind.Shared (blockSize τs) sOut0.result.reg
              (pathOffset spath))])).placeRegMap.lookup _ = _
      simp only [emit]
      show (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B)
        (setPlaceInfo
          (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
            [Instr.Assgn (Register.R csPrefix.nextReg)
              (Rhs.Alloc (layoutToTyVal σ))])
          loc.idx.1 (Register.R csPrefix.nextReg, σ))).placeRegMap.lookup _ = _
      rw [h_prmS]
      exact h_pi_new
    have h_stmtRun := (h_run0 csPrefix).trans
      (compileStmt_readrhs_projlocal_fresh_projsrc_offset_run (h_shape := h_shape) h_schain.not_proj
        h_so h_pi_none h_sval0 h_sclean h_dpi)
    -- §8-§11 the fresh-root WRITE seam
    exact copy_fresh_write_after_read
      (τ := τ)
      (mvals := output.values)
      compProg h_comp h_stmt h_csAt h_stmtOut h_sms h_unmap
      h_lookup_set h_env1 h_pc1 h_memstart1 h_allocs1 h_alloc h_find1 h_addr_eq h_sz h_runAlloc
      h_incr_a h_incr_t h_id_a' h_wf_t' h_ra_dom h_prb1 (pathOffset path)
      (PathTo.offset_add_size_le path)
      h_runR h_prmR h_regmonoR h_lbsR h_psimR h_tbdR h_smem h_pcR
      h_vregR h_vbelow h_vlen
      h_stmtRun
      output.values_len rfl rfl rfl rfl h_rel h_step
/-! ## Flatten transfers under a PROJECTED deref destination: the same
    two single-place splits, with the projection riding along. -/

theorem compileStmt_readrhs_projdst_srcflatten_run
    {Γ : Ctx} {τ τs σ : LayoutTy}
    (dbase : Place Γ σ) (path : PathTo σ τ)
    (src : Place Γ τs) (cs : CompilerState)
    {rhs rhs2 : RExpr Γ τ} {mk : Register → Rhs}
    (h_shape : ReadRhsShape rhs src mk)
    (h_shape2 : ReadRhsShape rhs2 (flattenPlace src) mk) :
    CheckedCompilerM.run
        (compileStmtChecked (Stmt.assign (Place.proj (dbase) path) rhs)) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (Place.proj (dbase) path) rhs2)) cs := by
  obtain ⟨ev, h_rhs⟩ := id h_shape
  obtain ⟨ev2, h_rhs2⟩ := id h_shape2
  obtain ⟨h_sagr, h_sagv⟩ := placeToRegChecked_flatten_agree src RefKind.Shared (CompilerM.run (ensurePlaceRoot (Place.proj (dbase) path)) cs)
  simp only [compileStmtChecked, compileRExprToChecked, h_rhs, h_rhs2, readRhsPre, csMonad]
  cases hO : CheckedCompilerM.value (placeToRegChecked RefKind.Shared src) (CompilerM.run (ensurePlaceRoot (Place.proj (dbase) path)) cs) with
  | error eO =>
      cases hF : CheckedCompilerM.value
          (placeToRegChecked RefKind.Shared (flattenPlace src)) (CompilerM.run (ensurePlaceRoot (Place.proj (dbase) path)) cs) with
      | error eF =>
          simp only [hO, hF]
          exact h_sagr.symm
      | ok oF =>
          exfalso
          rw [hO, hF] at h_sagv
          simp [Except.map] at h_sagv
  | ok oO =>
      cases hF : CheckedCompilerM.value
          (placeToRegChecked RefKind.Shared (flattenPlace src)) (CompilerM.run (ensurePlaceRoot (Place.proj (dbase) path)) cs) with
      | error eF =>
          exfalso
          rw [hO, hF] at h_sagv
          simp [Except.map] at h_sagv
      | ok oF =>
          have h_sres : oF.result = oO.result := by
            rw [hO, hF] at h_sagv
            simpa [Except.map] using h_sagv
          simp only [hO, hF, h_sres, h_sagr]

theorem compileStmt_readrhs_projdst_srcflatten_value
    {Γ : Ctx} {τ τs σ : LayoutTy}
    (dbase : Place Γ σ) (path : PathTo σ τ)
    (src : Place Γ τs) (cs : CompilerState)
    {rhs rhs2 : RExpr Γ τ} {mk : Register → Rhs}
    (h_shape : ReadRhsShape rhs src mk)
    (h_shape2 : ReadRhsShape rhs2 (flattenPlace src) mk)
    (h_ex : ∃ so, CheckedCompilerM.value
        (compileStmtChecked (Stmt.assign (Place.proj (dbase) path) rhs2)) cs
      = Except.ok so) :
    ∃ so', CheckedCompilerM.value
        (compileStmtChecked (Stmt.assign (Place.proj (dbase) path) rhs)) cs
      = Except.ok so' := by
  obtain ⟨ev, h_rhs⟩ := id h_shape
  obtain ⟨ev2, h_rhs2⟩ := id h_shape2
  obtain ⟨so, h_so⟩ := h_ex
  obtain ⟨h_sagr, h_sagv⟩ := placeToRegChecked_flatten_agree src RefKind.Shared (CompilerM.run (ensurePlaceRoot (Place.proj (dbase) path)) cs)
  simp only [compileStmtChecked, compileRExprToChecked, h_rhs, h_rhs2, readRhsPre, csMonad] at h_so ⊢
  cases hO : CheckedCompilerM.value (placeToRegChecked RefKind.Shared src) (CompilerM.run (ensurePlaceRoot (Place.proj (dbase) path)) cs) with
  | error eO =>
      exfalso
      cases hF : CheckedCompilerM.value
          (placeToRegChecked RefKind.Shared (flattenPlace src)) (CompilerM.run (ensurePlaceRoot (Place.proj (dbase) path)) cs) with
      | error eF =>
          rw [hF] at h_so
          simp at h_so
      | ok oF =>
          rw [hO, hF] at h_sagv
          simp [Except.map] at h_sagv
  | ok oO =>
      cases hF : CheckedCompilerM.value
          (placeToRegChecked RefKind.Shared (flattenPlace src)) (CompilerM.run (ensurePlaceRoot (Place.proj (dbase) path)) cs) with
      | error eF =>
          exfalso
          rw [hO, hF] at h_sagv
          simp [Except.map] at h_sagv
      | ok oF =>
          have h_sres : oF.result = oO.result := by
            rw [hO, hF] at h_sagv
            simpa [Except.map] using h_sagv
          simp only [hO]
          rw [hF] at h_so
          simp only [h_sres, h_sagr] at h_so
          split
          · exact ⟨_, rfl⟩
          · rename_i eDO h_dO
            exfalso
            simp only [h_dO] at h_so
            simp at h_so

theorem compileStmt_readrhs_projderefdst_dstflatten_run
    {Γ : Ctx} {τ τs σ : LayoutTy}
    (pp : Place Γ (obseq.LayoutTy.PtrL σ)) (path : PathTo σ τ)
    (src : Place Γ τs) (cs : CompilerState)
    {rhs : RExpr Γ τ} {mk : Register → Rhs}
    (h_shape : ReadRhsShape rhs src mk) :
    CheckedCompilerM.run
        (compileStmtChecked (Stmt.assign (Place.proj (Place.deref pp) path) rhs)) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (Place.proj (Place.deref (flattenPlace pp)) path) rhs)) cs := by
  obtain ⟨ev, h_rhs⟩ := id h_shape
  have h_er : ensurePlaceRoot (Place.proj (Place.deref (flattenPlace pp)) path)
      = ensurePlaceRoot (Place.proj (Place.deref pp) path) := ensurePlaceRoot_flatten (Place.proj (Place.deref pp) path)
  simp only [compileStmtChecked, compileRExprToChecked, h_rhs, readRhsPre, csMonad, h_er]
  cases hS : CheckedCompilerM.value (placeToRegChecked RefKind.Shared src) (CompilerM.run (ensurePlaceRoot (Place.proj (Place.deref pp) path)) cs) with
  | error eS => simp only [hS]
  | ok oS =>
      simp only [csRun, hS]
      obtain ⟨h_dagr, h_dagv⟩ := placeToRegChecked_flatten_agree
        (Place.proj (Place.deref pp) path) RefKind.Mut (emit
          { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) (ensurePlaceRoot (Place.proj (Place.deref pp) path) cs).snd.val) with
            nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) (ensurePlaceRoot (Place.proj (Place.deref pp) path) cs).snd.val).nextReg + 1 }
          ([Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) (ensurePlaceRoot (Place.proj (Place.deref pp) path) cs).snd.val).nextReg)
              (mk oS.result.reg)]
            ++ cleanupInstrs oS.result.cleanup))
      rw [show flattenPlace (Place.proj (Place.deref pp) path) = Place.proj (Place.deref (flattenPlace pp)) path from rfl]
        at h_dagr h_dagv
      cases hDO : CheckedCompilerM.value (placeToRegChecked RefKind.Mut (Place.proj (Place.deref pp) path))
          (emit
            { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) (ensurePlaceRoot (Place.proj (Place.deref pp) path) cs).snd.val) with
              nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) (ensurePlaceRoot (Place.proj (Place.deref pp) path) cs).snd.val).nextReg + 1 }
            ([Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) (ensurePlaceRoot (Place.proj (Place.deref pp) path) cs).snd.val).nextReg)
                (mk oS.result.reg)]
              ++ cleanupInstrs oS.result.cleanup)) with
      | error eDO =>
          cases hDF : CheckedCompilerM.value
              (placeToRegChecked RefKind.Mut (Place.proj (Place.deref (flattenPlace pp)) path))
              (emit
                { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) (ensurePlaceRoot (Place.proj (Place.deref pp) path) cs).snd.val) with
                  nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) (ensurePlaceRoot (Place.proj (Place.deref pp) path) cs).snd.val).nextReg + 1 }
                ([Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) (ensurePlaceRoot (Place.proj (Place.deref pp) path) cs).snd.val).nextReg)
                    (mk oS.result.reg)]
                  ++ cleanupInstrs oS.result.cleanup)) with
          | error eDF =>
              exact h_dagr.symm
          | ok oDF =>
              exfalso
              rw [hDO, hDF] at h_dagv
              simp [Except.map] at h_dagv
      | ok oDO =>
          cases hDF : CheckedCompilerM.value
              (placeToRegChecked RefKind.Mut (Place.proj (Place.deref (flattenPlace pp)) path))
              (emit
                { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) (ensurePlaceRoot (Place.proj (Place.deref pp) path) cs).snd.val) with
                  nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) (ensurePlaceRoot (Place.proj (Place.deref pp) path) cs).snd.val).nextReg + 1 }
                ([Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) (ensurePlaceRoot (Place.proj (Place.deref pp) path) cs).snd.val).nextReg)
                    (mk oS.result.reg)]
                  ++ cleanupInstrs oS.result.cleanup)) with
          | error eDF =>
              exfalso
              rw [hDO, hDF] at h_dagv
              simp [Except.map] at h_dagv
          | ok oDF =>
              have h_dres : oDF.result = oDO.result := by
                rw [hDO, hDF] at h_dagv
                simpa [Except.map] using h_dagv
              simp only [h_dres, h_dagr]

theorem compileStmt_readrhs_projderefdst_dstflatten_value
    {Γ : Ctx} {τ τs σ : LayoutTy}
    (pp : Place Γ (obseq.LayoutTy.PtrL σ)) (path : PathTo σ τ)
    (src : Place Γ τs) (cs : CompilerState)
    {rhs : RExpr Γ τ} {mk : Register → Rhs}
    (h_shape : ReadRhsShape rhs src mk)
    (h_ex : ∃ so, CheckedCompilerM.value
        (compileStmtChecked (Stmt.assign (Place.proj (Place.deref (flattenPlace pp)) path) rhs)) cs
      = Except.ok so) :
    ∃ so', CheckedCompilerM.value
        (compileStmtChecked (Stmt.assign (Place.proj (Place.deref pp) path) rhs)) cs
      = Except.ok so' := by
  obtain ⟨ev, h_rhs⟩ := id h_shape
  obtain ⟨so, h_so⟩ := h_ex
  have h_er : ensurePlaceRoot (Place.proj (Place.deref (flattenPlace pp)) path)
      = ensurePlaceRoot (Place.proj (Place.deref pp) path) := ensurePlaceRoot_flatten (Place.proj (Place.deref pp) path)
  simp only [compileStmtChecked, compileRExprToChecked, h_rhs, readRhsPre, csMonad, h_er] at h_so ⊢
  cases hS : CheckedCompilerM.value (placeToRegChecked RefKind.Shared src) (CompilerM.run (ensurePlaceRoot (Place.proj (Place.deref pp) path)) cs) with
  | error eS =>
      exfalso
      rw [hS] at h_so
      simp at h_so
  | ok oS =>
      rw [hS] at h_so
      simp only [csRun, hS]
        at h_so ⊢
      obtain ⟨h_dagr, h_dagv⟩ := placeToRegChecked_flatten_agree
        (Place.proj (Place.deref pp) path) RefKind.Mut (emit
          { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) (ensurePlaceRoot (Place.proj (Place.deref pp) path) cs).snd.val) with
            nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) (ensurePlaceRoot (Place.proj (Place.deref pp) path) cs).snd.val).nextReg + 1 }
          ([Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) (ensurePlaceRoot (Place.proj (Place.deref pp) path) cs).snd.val).nextReg)
              (mk oS.result.reg)]
            ++ cleanupInstrs oS.result.cleanup))
      rw [show flattenPlace (Place.proj (Place.deref pp) path) = Place.proj (Place.deref (flattenPlace pp)) path from rfl]
        at h_dagr h_dagv
      split
      · exact ⟨_, rfl⟩
      · rename_i eDO h_dO
        exfalso
        cases h_dF : CheckedCompilerM.value
            (placeToRegChecked RefKind.Mut (Place.proj (Place.deref (flattenPlace pp)) path))
            (emit
              { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) (ensurePlaceRoot (Place.proj (Place.deref pp) path) cs).snd.val) with
                nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) (ensurePlaceRoot (Place.proj (Place.deref pp) path) cs).snd.val).nextReg + 1 }
              ([Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) (ensurePlaceRoot (Place.proj (Place.deref pp) path) cs).snd.val).nextReg)
                  (mk oS.result.reg)]
                ++ cleanupInstrs oS.result.cleanup)) with
        | ok oDF =>
            rw [h_dO, h_dF] at h_dagv
            simp [Except.map] at h_dagv
        | error eDF =>
            simp only [h_dF] at h_so
            simp at h_so


/-! ## PROJECTED destination over a chain: the destination lowering adds
    a `Borrow(Mut)` and a cleanup `Die` around the same two-mother
    skeleton. Zero offset passes the register through. -/

theorem compileStmt_readrhs_projdst_zero_run
    {Γ : Ctx} {τ τs σb : LayoutTy}
    {dbase : Place Γ σb} {path : PathTo σb τ}
    {src : Place Γ τs}
    {cs : CompilerState}
    {sOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared src)}
    {dOut : ResultWithEvidence PtrResult
      (PlaceToRegEvidence RefKind.Mut (dbase))}
    {rhs : RExpr Γ τ} {mk : Register → Rhs}
    (h_shape : ReadRhsShape rhs src mk)
    (h_np : ∀ (σ' : LayoutTy) (b : Place Γ σ') (q : PathTo σ' σb),
      dbase = b.proj q → False)
    (h_off : pathOffset path = 0)
    (h_root : CompilerM.run
      (ensurePlaceRoot (Place.proj dbase path)) cs = cs)
    (h_sval : CheckedCompilerM.value (placeToRegChecked RefKind.Shared src) cs
      = Except.ok sOut)
    (h_sclean : sOut.result.cleanup = [])
    (h_dval : CheckedCompilerM.value (placeToRegChecked RefKind.Mut (dbase))
      (emit
        { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) cs) with
          nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) cs).nextReg + 1 }
        [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) cs).nextReg)
          (mk sOut.result.reg)]) = Except.ok dOut)
    (h_dclean : dOut.result.cleanup = []) :
    CheckedCompilerM.run
        (compileStmtChecked
          (Stmt.assign (.proj dbase path) rhs)) cs
      = emit (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (dbase))
      (emit
        { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) cs) with
          nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) cs).nextReg + 1 }
        [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) cs).nextReg)
          (mk sOut.result.reg)]))
          [Instr.RStore (layoutToTyVal τ) (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) cs).nextReg)
            dOut.result.reg] := by
  obtain ⟨ev, h_rhs⟩ := id h_shape
  have h_proj_eq := placeToRegChecked_proj_root_eq (Γ := Γ) (kind := RefKind.Mut)
    (base := dbase) path h_np
  simp only [compileStmtChecked, compileRExprToChecked, h_rhs, readRhsPre, csMonad, h_proj_eq, h_root, h_sval]
  simp only [csCleanup, csRun, h_sclean, emit_nil, List.append_nil]
  rw [h_dval]
  simp [h_off, dif_pos, CompilerM.run, CompilerM.value, emitM, cleanupInstrs,
    h_dclean, emit_nil]

theorem compileStmt_readrhs_projdst_zero_value
    {Γ : Ctx} {τ τs σb : LayoutTy}
    {dbase : Place Γ σb} {path : PathTo σb τ}
    {src : Place Γ τs}
    {cs : CompilerState}
    {sOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared src)}
    {dOut : ResultWithEvidence PtrResult
      (PlaceToRegEvidence RefKind.Mut (dbase))}
    {rhs : RExpr Γ τ} {mk : Register → Rhs}
    (h_shape : ReadRhsShape rhs src mk)
    (h_np : ∀ (σ' : LayoutTy) (b : Place Γ σ') (q : PathTo σ' σb),
      dbase = b.proj q → False)
    (h_off : pathOffset path = 0)
    (h_root : CompilerM.run
      (ensurePlaceRoot (Place.proj dbase path)) cs = cs)
    (h_sval : CheckedCompilerM.value (placeToRegChecked RefKind.Shared src) cs
      = Except.ok sOut)
    (h_dval : CheckedCompilerM.value (placeToRegChecked RefKind.Mut (dbase))
      (emit
        { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) cs) with
          nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) cs).nextReg + 1 }
        ([Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) cs).nextReg)
            (mk sOut.result.reg)]
          ++ cleanupInstrs sOut.result.cleanup))
      = Except.ok dOut) :
    ∃ so, CheckedCompilerM.value
      (compileStmtChecked (Stmt.assign (.proj dbase path) rhs)) cs
      = Except.ok so := by
  obtain ⟨ev, h_rhs⟩ := id h_shape
  have h_proj_eq := placeToRegChecked_proj_root_eq (Γ := Γ) (kind := RefKind.Mut)
    (base := dbase) path h_np
  simp only [compileStmtChecked, compileRExprToChecked, h_rhs, readRhsPre, csMonad, h_proj_eq, h_root, h_sval]
  simp only [csRun]
  split
  · exact ⟨_, rfl⟩
  · rename_i e h_d
    exact absurd h_d (by rw [h_dval]; simp [h_off])

/-- Nonzero offset: the destination lowering adds `Borrow(Mut)` before
    the `RStore` and its `Die` after — the BRIDGE 1 sandwich. -/
theorem compileStmt_readrhs_projdst_offset_run
    {Γ : Ctx} {τ τs σb : LayoutTy}
    {dbase : Place Γ σb} {path : PathTo σb τ}
    {src : Place Γ τs}
    {cs : CompilerState}
    {sOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared src)}
    {dOut : ResultWithEvidence PtrResult
      (PlaceToRegEvidence RefKind.Mut (dbase))}
    {rhs : RExpr Γ τ} {mk : Register → Rhs}
    (h_shape : ReadRhsShape rhs src mk)
    (h_np : ∀ (σ' : LayoutTy) (b : Place Γ σ') (q : PathTo σ' σb),
      dbase = b.proj q → False)
    (h_off : pathOffset path ≠ 0)
    (h_root : CompilerM.run
      (ensurePlaceRoot (Place.proj dbase path)) cs = cs)
    (h_sval : CheckedCompilerM.value (placeToRegChecked RefKind.Shared src) cs
      = Except.ok sOut)
    (h_sclean : sOut.result.cleanup = [])
    (h_dval : CheckedCompilerM.value (placeToRegChecked RefKind.Mut (dbase))
      (emit
        { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) cs) with
          nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) cs).nextReg + 1 }
        [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) cs).nextReg)
          (mk sOut.result.reg)])
      = Except.ok dOut)
    (h_dclean : dOut.result.cleanup = []) :
    CheckedCompilerM.run
        (compileStmtChecked
          (Stmt.assign (.proj dbase path) rhs)) cs
      = emit (emit (emit
          { (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (dbase))
            (emit
              { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) cs) with
                nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) cs).nextReg + 1 }
              [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) cs).nextReg)
                (mk sOut.result.reg)])) with
              nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (dbase))
                (emit
                  { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) cs) with
                    nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) cs).nextReg + 1 }
                  [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) cs).nextReg)
                    (mk sOut.result.reg)])).nextReg + 1 }
          [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (dbase))
              (emit
                { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) cs) with
                  nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) cs).nextReg + 1 }
                [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) cs).nextReg)
                  (mk sOut.result.reg)])).nextReg)
            (borrowRhs RefKind.Mut (blockSize τ) dOut.result.reg
              (pathOffset path))])
          [Instr.RStore (layoutToTyVal τ) (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) cs).nextReg)
            (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (dbase))
              (emit
                { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) cs) with
                  nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) cs).nextReg + 1 }
                [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) cs).nextReg)
                  (mk sOut.result.reg)])).nextReg)])
          [Instr.Die (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (dbase))
              (emit
                { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) cs) with
                  nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) cs).nextReg + 1 }
                [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) cs).nextReg)
                  (mk sOut.result.reg)])).nextReg) (blockSize τ)] := by
  obtain ⟨ev, h_rhs⟩ := id h_shape
  have h_proj_eq := placeToRegChecked_proj_root_eq (Γ := Γ) (kind := RefKind.Mut)
    (base := dbase) path h_np
  simp only [compileStmtChecked, compileRExprToChecked, h_rhs, readRhsPre, csMonad, h_proj_eq, h_root, h_sval]
  simp only [csCleanup, csRun, h_sclean, emit_nil, List.append_nil]
  rw [h_dval]
  simp [csRun, cleanupInstrs, h_dclean, emit_nil, h_off, borrowRhs]

/-- The nonzero-offset projected copy statement lowers. -/
theorem compileStmt_readrhs_projdst_offset_value
    {Γ : Ctx} {τ τs σb : LayoutTy}
    {dbase : Place Γ σb} {path : PathTo σb τ}
    {src : Place Γ τs}
    {cs : CompilerState}
    {sOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared src)}
    {dOut : ResultWithEvidence PtrResult
      (PlaceToRegEvidence RefKind.Mut (dbase))}
    {rhs : RExpr Γ τ} {mk : Register → Rhs}
    (h_shape : ReadRhsShape rhs src mk)
    (h_np : ∀ (σ' : LayoutTy) (b : Place Γ σ') (q : PathTo σ' σb),
      dbase = b.proj q → False)
    (h_off : pathOffset path ≠ 0)
    (h_root : CompilerM.run
      (ensurePlaceRoot (Place.proj dbase path)) cs = cs)
    (h_sval : CheckedCompilerM.value (placeToRegChecked RefKind.Shared src) cs
      = Except.ok sOut)
    (h_dval : CheckedCompilerM.value (placeToRegChecked RefKind.Mut (dbase))
      (emit
        { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) cs) with
          nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) cs).nextReg + 1 }
        ([Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) cs).nextReg)
            (mk sOut.result.reg)]
          ++ cleanupInstrs sOut.result.cleanup))
      = Except.ok dOut) :
    ∃ so, CheckedCompilerM.value
      (compileStmtChecked (Stmt.assign (.proj dbase path) rhs)) cs
      = Except.ok so := by
  obtain ⟨ev, h_rhs⟩ := id h_shape
  have h_proj_eq := placeToRegChecked_proj_root_eq (Γ := Γ) (kind := RefKind.Mut)
    (base := dbase) path h_np
  simp only [compileStmtChecked, compileRExprToChecked, h_rhs, readRhsPre, csMonad, h_proj_eq, h_root, h_sval]
  simp only [csRun]
  rw [h_dval]
  simp only [csRun, csMonad, dif_neg h_off]
  exact ⟨_, rfl⟩

/-! ## PROJECTED destination with a PROJ-TOPPED source at NONZERO
    offset. The source projection's `Borrow(Shared)`, the copy's
    `Load`, and the source projection's cleanup `Die` all sit in the rhs
    pre-phase; only then does the destination lower. At a zero
    destination offset the store goes straight through the base
    register, at a nonzero one through the destination projection's own
    `Borrow(Mut)`, killed after. -/

theorem compileStmt_readrhs_projdst_zero_projsrc_offset_run
    {Γ : Ctx} {τ τs σb σs : LayoutTy}
    {dbase : Place Γ σb} {dpath : PathTo σb τ}
    {B : Place Γ σs} {spath : PathTo σs τs}
    {cs : CompilerState}
    {bOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared B)}
    {dOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Mut dbase)}
    {rhs : RExpr Γ τ} {mk : Register → Rhs}
    (h_shape : ReadRhsShape rhs (.proj B spath) mk)
    (h_npD : ∀ (σ' : LayoutTy) (b : Place Γ σ') (q : PathTo σ' σb),
      dbase = b.proj q → False)
    (h_npS : ∀ (σ' : LayoutTy) (b : Place Γ σ') (q : PathTo σ' σs),
      B = b.proj q → False)
    (h_do : pathOffset dpath = 0)
    (h_so : pathOffset spath ≠ 0)
    (h_root : CompilerM.run (ensurePlaceRoot (Place.proj dbase dpath)) cs = cs)
    (h_bval : CheckedCompilerM.value (placeToRegChecked RefKind.Shared B) cs
      = Except.ok bOut)
    (h_bclean : bOut.result.cleanup = [])
    (h_dval : CheckedCompilerM.value (placeToRegChecked RefKind.Mut dbase)
      (emit
          { (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg) (borrowRhs RefKind.Shared (blockSize τs) bOut.result.reg (pathOffset spath))]) with
            nextReg := (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg) (borrowRhs RefKind.Shared (blockSize τs) bOut.result.reg (pathOffset spath))]).nextReg + 1 }
          [Instr.Assgn (Register.R (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs) with
                  nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg + 1 }
                [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg)
                  (borrowRhs RefKind.Shared (blockSize τs) bOut.result.reg (pathOffset spath))]).nextReg) (mk (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg)),
           Instr.Die (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg) (blockSize τs)]) = Except.ok dOut)
    (h_dclean : dOut.result.cleanup = []) :
    CheckedCompilerM.run
        (compileStmtChecked
          (Stmt.assign (.proj dbase dpath) rhs)) cs
      = emit (CheckedCompilerM.run (placeToRegChecked RefKind.Mut dbase)
          (emit
            { (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg) (borrowRhs RefKind.Shared (blockSize τs) bOut.result.reg (pathOffset spath))]) with
              nextReg := (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg) (borrowRhs RefKind.Shared (blockSize τs) bOut.result.reg (pathOffset spath))]).nextReg + 1 }
            [Instr.Assgn (Register.R (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs) with
                    nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg + 1 }
                  [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg)
                    (borrowRhs RefKind.Shared (blockSize τs) bOut.result.reg (pathOffset spath))]).nextReg) (mk (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg)),
             Instr.Die (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg) (blockSize τs)]))
          [Instr.RStore (layoutToTyVal τ) (Register.R (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs) with
                  nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg + 1 }
                [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg)
                  (borrowRhs RefKind.Shared (blockSize τs) bOut.result.reg (pathOffset spath))]).nextReg) dOut.result.reg] := by
  obtain ⟨ev, h_rhs⟩ := id h_shape
  have h_proj_eqS := placeToRegChecked_proj_root_eq (Γ := Γ)
    (kind := RefKind.Shared) (base := B) spath h_npS
  have h_proj_eqD := placeToRegChecked_proj_root_eq (Γ := Γ)
    (kind := RefKind.Mut) (base := dbase) dpath h_npD
  simp only [compileStmtChecked, compileRExprToChecked, h_rhs, readRhsPre, csMonad, h_proj_eqS, h_proj_eqD, h_root, h_bval, dif_neg h_so]
  simp only [csCleanup, csRun, h_bclean, List.nil_append, List.cons_append, List.append_nil,
    List.reverse_cons, List.map_cons]
  simp only [csMonad, h_dval, h_do, dif_pos]
  simp only [csCleanup, CompilerM.run, CompilerM.value, emitM, h_dclean, emit_nil]

theorem compileStmt_readrhs_projdst_offset_projsrc_offset_run
    {Γ : Ctx} {τ τs σb σs : LayoutTy}
    {dbase : Place Γ σb} {dpath : PathTo σb τ}
    {B : Place Γ σs} {spath : PathTo σs τs}
    {cs : CompilerState}
    {bOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared B)}
    {dOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Mut dbase)}
    {rhs : RExpr Γ τ} {mk : Register → Rhs}
    (h_shape : ReadRhsShape rhs (.proj B spath) mk)
    (h_npD : ∀ (σ' : LayoutTy) (b : Place Γ σ') (q : PathTo σ' σb),
      dbase = b.proj q → False)
    (h_npS : ∀ (σ' : LayoutTy) (b : Place Γ σ') (q : PathTo σ' σs),
      B = b.proj q → False)
    (h_do : pathOffset dpath ≠ 0)
    (h_so : pathOffset spath ≠ 0)
    (h_root : CompilerM.run (ensurePlaceRoot (Place.proj dbase dpath)) cs = cs)
    (h_bval : CheckedCompilerM.value (placeToRegChecked RefKind.Shared B) cs
      = Except.ok bOut)
    (h_bclean : bOut.result.cleanup = [])
    (h_dval : CheckedCompilerM.value (placeToRegChecked RefKind.Mut dbase)
      (emit
          { (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg) (borrowRhs RefKind.Shared (blockSize τs) bOut.result.reg (pathOffset spath))]) with
            nextReg := (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg) (borrowRhs RefKind.Shared (blockSize τs) bOut.result.reg (pathOffset spath))]).nextReg + 1 }
          [Instr.Assgn (Register.R (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs) with
                  nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg + 1 }
                [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg)
                  (borrowRhs RefKind.Shared (blockSize τs) bOut.result.reg (pathOffset spath))]).nextReg) (mk (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg)),
           Instr.Die (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg) (blockSize τs)]) = Except.ok dOut)
    (h_dclean : dOut.result.cleanup = []) :
    CheckedCompilerM.run
        (compileStmtChecked
          (Stmt.assign (.proj dbase dpath) rhs)) cs
      = emit (emit (emit
          { (CheckedCompilerM.run (placeToRegChecked RefKind.Mut dbase)
            (emit
              { (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg) (borrowRhs RefKind.Shared (blockSize τs) bOut.result.reg (pathOffset spath))]) with
                nextReg := (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg) (borrowRhs RefKind.Shared (blockSize τs) bOut.result.reg (pathOffset spath))]).nextReg + 1 }
              [Instr.Assgn (Register.R (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs) with
                      nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg + 1 }
                    [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg)
                      (borrowRhs RefKind.Shared (blockSize τs) bOut.result.reg (pathOffset spath))]).nextReg) (mk (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg)),
               Instr.Die (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg) (blockSize τs)])) with
              nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Mut dbase)
            (emit
              { (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg) (borrowRhs RefKind.Shared (blockSize τs) bOut.result.reg (pathOffset spath))]) with
                nextReg := (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg) (borrowRhs RefKind.Shared (blockSize τs) bOut.result.reg (pathOffset spath))]).nextReg + 1 }
              [Instr.Assgn (Register.R (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs) with
                      nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg + 1 }
                    [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg)
                      (borrowRhs RefKind.Shared (blockSize τs) bOut.result.reg (pathOffset spath))]).nextReg) (mk (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg)),
               Instr.Die (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg) (blockSize τs)])).nextReg + 1 }
          [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Mut dbase)
            (emit
              { (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg) (borrowRhs RefKind.Shared (blockSize τs) bOut.result.reg (pathOffset spath))]) with
                nextReg := (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg) (borrowRhs RefKind.Shared (blockSize τs) bOut.result.reg (pathOffset spath))]).nextReg + 1 }
              [Instr.Assgn (Register.R (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs) with
                      nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg + 1 }
                    [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg)
                      (borrowRhs RefKind.Shared (blockSize τs) bOut.result.reg (pathOffset spath))]).nextReg) (mk (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg)),
               Instr.Die (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg) (blockSize τs)])).nextReg)
            (borrowRhs RefKind.Mut (blockSize τ) dOut.result.reg
              (pathOffset dpath))])
          [Instr.RStore (layoutToTyVal τ) (Register.R (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs) with
                  nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg + 1 }
                [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg)
                  (borrowRhs RefKind.Shared (blockSize τs) bOut.result.reg (pathOffset spath))]).nextReg) (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Mut dbase)
            (emit
              { (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg) (borrowRhs RefKind.Shared (blockSize τs) bOut.result.reg (pathOffset spath))]) with
                nextReg := (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg) (borrowRhs RefKind.Shared (blockSize τs) bOut.result.reg (pathOffset spath))]).nextReg + 1 }
              [Instr.Assgn (Register.R (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs) with
                      nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg + 1 }
                    [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg)
                      (borrowRhs RefKind.Shared (blockSize τs) bOut.result.reg (pathOffset spath))]).nextReg) (mk (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg)),
               Instr.Die (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg) (blockSize τs)])).nextReg)])
          [Instr.Die (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Mut dbase)
            (emit
              { (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg) (borrowRhs RefKind.Shared (blockSize τs) bOut.result.reg (pathOffset spath))]) with
                nextReg := (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg) (borrowRhs RefKind.Shared (blockSize τs) bOut.result.reg (pathOffset spath))]).nextReg + 1 }
              [Instr.Assgn (Register.R (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs) with
                      nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg + 1 }
                    [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg)
                      (borrowRhs RefKind.Shared (blockSize τs) bOut.result.reg (pathOffset spath))]).nextReg) (mk (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg)),
               Instr.Die (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg) (blockSize τs)])).nextReg) (blockSize τ)] := by
  obtain ⟨ev, h_rhs⟩ := id h_shape
  have h_proj_eqS := placeToRegChecked_proj_root_eq (Γ := Γ)
    (kind := RefKind.Shared) (base := B) spath h_npS
  have h_proj_eqD := placeToRegChecked_proj_root_eq (Γ := Γ)
    (kind := RefKind.Mut) (base := dbase) dpath h_npD
  simp only [compileStmtChecked, compileRExprToChecked, h_rhs, readRhsPre, csMonad, h_proj_eqS, h_proj_eqD, h_root, h_bval, dif_neg h_so]
  simp only [csCleanup, csRun, h_bclean, List.nil_append, List.cons_append, List.append_nil,
    List.reverse_cons, List.map_cons]
  simp only [csMonad, h_dval, dif_neg h_do]
  simp [csRun, cleanupInstrs, h_dclean, emit_nil, borrowRhs]

theorem compileStmt_readrhs_projdst_projsrc_offset_value
    {Γ : Ctx} {τ τs σb σs : LayoutTy}
    {dbase : Place Γ σb} {dpath : PathTo σb τ}
    {B : Place Γ σs} {spath : PathTo σs τs}
    {cs : CompilerState}
    {bOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared B)}
    {dOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Mut dbase)}
    {rhs : RExpr Γ τ} {mk : Register → Rhs}
    (h_shape : ReadRhsShape rhs (.proj B spath) mk)
    (h_npD : ∀ (σ' : LayoutTy) (b : Place Γ σ') (q : PathTo σ' σb),
      dbase = b.proj q → False)
    (h_npS : ∀ (σ' : LayoutTy) (b : Place Γ σ') (q : PathTo σ' σs),
      B = b.proj q → False)
    (h_so : pathOffset spath ≠ 0)
    (h_root : CompilerM.run (ensurePlaceRoot (Place.proj dbase dpath)) cs = cs)
    (h_bval : CheckedCompilerM.value (placeToRegChecked RefKind.Shared B) cs
      = Except.ok bOut)
    (h_dval : CheckedCompilerM.value (placeToRegChecked RefKind.Mut dbase)
      (emit
          { (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg) (borrowRhs RefKind.Shared (blockSize τs) bOut.result.reg (pathOffset spath))]) with
            nextReg := (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg) (borrowRhs RefKind.Shared (blockSize τs) bOut.result.reg (pathOffset spath))]).nextReg + 1 }
          ([Instr.Assgn (Register.R (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs) with
                  nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg + 1 }
                [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg)
                  (borrowRhs RefKind.Shared (blockSize τs) bOut.result.reg (pathOffset spath))]).nextReg) (mk (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg))]
            ++ cleanupInstrs (bOut.result.cleanup ++ [((Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) cs).nextReg), blockSize τs)]))) = Except.ok dOut) :
    ∃ so, CheckedCompilerM.value
      (compileStmtChecked
        (Stmt.assign (.proj dbase dpath) rhs)) cs
      = Except.ok so := by
  obtain ⟨ev, h_rhs⟩ := id h_shape
  have h_proj_eqS := placeToRegChecked_proj_root_eq (Γ := Γ)
    (kind := RefKind.Shared) (base := B) spath h_npS
  have h_proj_eqD := placeToRegChecked_proj_root_eq (Γ := Γ)
    (kind := RefKind.Mut) (base := dbase) dpath h_npD
  simp only [compileStmtChecked, compileRExprToChecked, h_rhs, readRhsPre, csMonad, h_proj_eqS, h_proj_eqD, h_root, h_bval, dif_neg h_so]
  simp only [csRun]
  simp only [h_dval]
  by_cases h_do : pathOffset dpath = 0
  · simp only [h_do, dif_pos]
    exact ⟨_, rfl⟩
  · simp only [dif_neg h_do,
      CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
      CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
      CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
      CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM]
    exact ⟨_, rfl⟩

theorem copy_projdst_zero_projsrc_offset_simulation
    {τ τs σb σs : LayoutTy}
    {dbase : Place Γ σb} {dpath : PathTo σb τ} {B : Place Γ σs}
    {spath : PathTo σs τs}
    {rhs : RExpr Γ τ} {mk : Register → Rhs}
    (compProg : oseair.Prog)
    (h_shape : ReadRhsShape rhs (.proj B spath) mk)
    (h_pkg : ReadPkgProjOffset compProg rhs B spath mk)
    (h_dchain : PtrChain dbase)
    (h_npD : ∀ (σ' : LayoutTy) (b : Place Γ σ') (q : PathTo σ' σb),
      dbase = b.proj q → False)
    (h_do : pathOffset dpath = 0)
    (h_bound : ∀ s, mirlite.preparePlaceAssign MSB s_mir (Place.proj dbase dpath)
        = .ok s →
      s = s_mir ∧ ∃ r0,
        mirlite.resolvePlace? s_mir (Place.proj dbase dpath) = some r0)
    (h_schain : PtrChain B)
    (h_o : pathOffset spath ≠ 0)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    {stmt0 : Stmt Γ}
    (h_stmt : prog.get? s_mir.pc = some stmt0)
    (h_run0 : ∀ cs, CheckedCompilerM.run (compileStmtChecked stmt0) cs
      = CheckedCompilerM.run
          (compileStmtChecked (Stmt.assign (.proj dbase dpath) rhs)) cs)
    (h_val0 : ∀ cs so, CheckedCompilerM.value
        (compileStmtChecked (Stmt.assign (.proj dbase dpath) rhs)) cs
        = Except.ok so →
      ∃ so', CheckedCompilerM.value (compileStmtChecked stmt0) cs
        = Except.ok so')
    (h_step : mirlite.stepStmt MSB s_mir
      (.assign (.proj dbase dpath) rhs) = .ok s_mir') :
    ∃ (s_osea' : oseair.State MSB) (n : Nat),
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa ρt s_mir' s_osea' := by
  have h_np := h_schain.not_proj
  have h_proj_eqD := placeToRegChecked_proj_root_eq (Γ := Γ) (kind := RefKind.Mut)
    (base := dbase) dpath h_npD
  obtain ⟨csPrefix, ⟨h_csAt, h_pc⟩, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_tbd,
    h_alloc, h_unmap, h_prb⟩ := h_inv
  -- §1 invert: prepare is a no-op for a bound root; the rvalue runs, and
  -- only THEN does the destination resolve
  simp only [mirlite.stepStmt, mirlite.doAssign] at h_step
  cases h_prep : mirlite.preparePlaceAssign MSB s_mir (Place.proj dbase dpath) with
  | err msg => rw [h_prep] at h_step; simp at h_step
  | ok s1 =>
  rw [h_prep] at h_step
  obtain ⟨h_s1eq, r0, h_resolved⟩ := h_bound s1 h_prep
  rw [h_s1eq] at h_step
  simp only at h_step
  cases h_eval : mirlite.evalRExpr MSB s_mir rhs with
  | err e => rw [h_eval] at h_step; simp at h_step
  | ok output =>
    rw [h_eval] at h_step
    simp only at h_step
    obtain ⟨h_mappedP2, h_pkg'⟩ :=
      h_pkg _ _ s_mir s_osea csPrefix h_id_a h_wf_t h_tbd h_lbs h_prb h_sms h_alloc
        h_psim h_pc output h_eval
    have h_mappedS : PlaceInputsMapped csPrefix B := h_mappedP2
    -- §2 both places are mapped; the statement compiles
    have h_mappedP : PlaceInputsMapped csPrefix (Place.proj dbase dpath) :=
      placeInputsMapped_of_localBindingSim_resolvePlace h_lbs h_resolved
    have h_mappedD : PlaceInputsMapped csPrefix dbase := h_mappedP
    have h_root := ensurePlaceRoot_run_eq_of_mapped h_mappedP
    obtain ⟨sOut0, h_sval0⟩ := placeToRegChecked_ok_of_placeInputsMapped
      (cs := csPrefix) (kind := RefKind.Shared) h_mappedS
    have h_prmS : (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).placeRegMap = csPrefix.placeRegMap :=
      h_schain.placeToRegChecked_placeRegMap RefKind.Shared csPrefix
    obtain ⟨dOut0, h_dval0⟩ := placeToRegChecked_ok_of_placeInputsMapped
      (cs := (emit
        { (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix) with
              nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg + 1 }
            [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg)
              (borrowRhs RefKind.Shared (blockSize τs) sOut0.result.reg (pathOffset spath))]) with
            nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg + 1 + 1 }
        ([Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg + 1))
            (mk (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg))]
          ++ cleanupInstrs (sOut0.result.cleanup
              ++ [((Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg), blockSize τs)])))) (kind := RefKind.Mut)
      (PlaceInputsMapped.placeRegMap_congr (by simp only [emit]; exact h_prmS)
        _ h_mappedD)
    -- the destination lowering's value, in the spelling the StateIncr
    -- towers normalize to (read out of a `trace_state`, not guessed)
    obtain ⟨stmtOutC, h_stmtOutC⟩ :=
      compileStmt_readrhs_projdst_projsrc_offset_value (h_shape := h_shape) h_npD h_np h_o h_root
        h_sval0 h_dval0
    obtain ⟨stmtOut, h_stmtOut⟩ := h_val0 csPrefix stmtOutC h_stmtOutC
    -- §3 code inclusion for the SOURCE lowering: the three facts, once,
    -- with the projection's Borrow supplied by the nonzero-offset equations
    obtain ⟨sOutP, h_svalP, h_regP, h_clP⟩ :=
      placeToRegChecked_proj_offset_value (kind := RefKind.Shared) spath h_np h_o h_sval0
    obtain ⟨h_incrS', h_incrCS1', h_incrDrun'⟩ :=
      readrhs_projdst_incrs (h_shape := h_shape) csPrefix h_svalP
        (placeToRegChecked_proj_offset_run (kind := RefKind.Shared) spath h_np h_o h_sval0)
        h_npD h_root (h_run0 csPrefix)
    have h_incrS : StateIncr (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix)
        (CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix) :=
      StateIncr.trans (StateIncr.trans (freshReg_state_incr _) (emit_state_incr _ _)) h_incrS'
    have h_instS :=
      (CodeIncluded.of_stmt h_comp h_csAt h_stmt h_stmtOut).mono h_incrS
    -- §4-§7 the SOURCE package: mother, BRIDGE 1S, and the three
    -- instructions -- Borrow off the base, the rvalue's step, Die
    obtain ⟨h_sclean, nR, s_mid1, perms₂, vals, h_ost, h_vlen, h_runR, h_prmR,
      h_regmonoR, h_lbsR, h_psimR, h_tbdR, h_smem, h_pcR, h_vregR, h_vbelow,
      h_valsRel⟩ :=
      h_pkg' sOut0 h_sval0 _ h_regP h_clP h_instS
        ((CodeIncluded.of_stmt h_comp h_csAt h_stmt h_stmtOut).mono h_incrCS1')
    rw [h_ost] at h_step
    simp only at h_step
    cases h_dres : mirlite.resolvePlaceAcc MSB
        { s_mir with perms := perms₂ } dbase with
    | error e => rw [resolvePlaceAcc_proj_base_err h_dres] at h_step; simp at h_step
    | ok pr2 =>
    obtain ⟨rd, permsD⟩ := pr2
    rw [resolvePlaceAcc_proj_base_ok h_dres] at h_step
    simp only at h_step
    have h_resolved_eq : ({ rd with addr := rd.addr + PathTo.offset dpath }
        : mirlite.PlaceRes) = rd := by
      have h_o' : PathTo.offset dpath = 0 := h_do
      simp [h_o']
    rw [h_resolved_eq] at h_step
    exact copy_chainwrite_after_read compProg h_dchain h_comp h_stmt h_csAt
      h_stmtOut h_id_a h_wf_t h_sms h_alloc h_unmap h_prb
      h_dres output.values_len h_step
      h_runR h_prmR h_regmonoR h_lbsR h_psimR h_tbdR h_smem h_pcR
      h_vregR h_vbelow h_vlen h_valsRel
      -- code inclusion for the DESTINATION lowering's own instructions,
      -- transported onto the post-`Die` tower the package landed on
      ((CodeIncluded.of_stmt h_comp h_csAt h_stmt h_stmtOut).mono
        (by have h := h_incrDrun'
            rw [h_regP, h_clP] at h
            simp only [csCleanup, h_sclean, List.nil_append, List.append_nil,
              List.reverse_cons, List.map_cons] at h
            csnorm at h ⊢
            exact h))
      (fun dOut h_dval h_dclean => (h_run0 csPrefix).trans
        (compileStmt_readrhs_projdst_zero_projsrc_offset_run (h_shape := h_shape) h_npD h_np h_do h_o h_root
          h_sval0 h_sclean h_dval h_dclean))

theorem copy_projdst_offset_projsrc_offset_simulation
    {τ τs σb σs : LayoutTy}
    {dbase : Place Γ σb} {dpath : PathTo σb τ} {B : Place Γ σs}
    {spath : PathTo σs τs}
    {rhs : RExpr Γ τ} {mk : Register → Rhs}
    (compProg : oseair.Prog)
    (h_shape : ReadRhsShape rhs (.proj B spath) mk)
    (h_pkg : ReadPkgProjOffset compProg rhs B spath mk)
    (h_dchain : PtrChain dbase)
    (h_npD : ∀ (σ' : LayoutTy) (b : Place Γ σ') (q : PathTo σ' σb),
      dbase = b.proj q → False)
    (h_do : pathOffset dpath ≠ 0)
    (h_bound : ∀ s, mirlite.preparePlaceAssign MSB s_mir (Place.proj dbase dpath)
        = .ok s →
      s = s_mir ∧ ∃ r0,
        mirlite.resolvePlace? s_mir (Place.proj dbase dpath) = some r0)
    (h_schain : PtrChain B)
    (h_o : pathOffset spath ≠ 0)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    {stmt0 : Stmt Γ}
    (h_stmt : prog.get? s_mir.pc = some stmt0)
    (h_run0 : ∀ cs, CheckedCompilerM.run (compileStmtChecked stmt0) cs
      = CheckedCompilerM.run
          (compileStmtChecked (Stmt.assign (.proj dbase dpath) rhs)) cs)
    (h_val0 : ∀ cs so, CheckedCompilerM.value
        (compileStmtChecked (Stmt.assign (.proj dbase dpath) rhs)) cs
        = Except.ok so →
      ∃ so', CheckedCompilerM.value (compileStmtChecked stmt0) cs
        = Except.ok so')
    (h_step : mirlite.stepStmt MSB s_mir
      (.assign (.proj dbase dpath) rhs) = .ok s_mir') :
    ∃ (s_osea' : oseair.State MSB) (n : Nat),
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa ρt s_mir' s_osea' := by
  have h_np := h_schain.not_proj
  have h_proj_eqD := placeToRegChecked_proj_root_eq (Γ := Γ) (kind := RefKind.Mut)
    (base := dbase) dpath h_npD
  obtain ⟨csPrefix, ⟨h_csAt, h_pc⟩, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_tbd,
    h_alloc, h_unmap, h_prb⟩ := h_inv
  -- §1 invert: prepare is a no-op for a bound root; the rvalue runs, and
  -- only THEN does the destination resolve
  simp only [mirlite.stepStmt, mirlite.doAssign] at h_step
  cases h_prep : mirlite.preparePlaceAssign MSB s_mir (Place.proj dbase dpath) with
  | err msg => rw [h_prep] at h_step; simp at h_step
  | ok s1 =>
  rw [h_prep] at h_step
  obtain ⟨h_s1eq, r0, h_resolved⟩ := h_bound s1 h_prep
  rw [h_s1eq] at h_step
  simp only at h_step
  cases h_eval : mirlite.evalRExpr MSB s_mir rhs with
  | err e => rw [h_eval] at h_step; simp at h_step
  | ok output =>
    rw [h_eval] at h_step
    simp only at h_step
    obtain ⟨h_mappedP2, h_pkg'⟩ :=
      h_pkg _ _ s_mir s_osea csPrefix h_id_a h_wf_t h_tbd h_lbs h_prb h_sms h_alloc
        h_psim h_pc output h_eval
    have h_mappedS : PlaceInputsMapped csPrefix B := h_mappedP2
    -- §2 both places are mapped; the statement compiles
    have h_mappedP : PlaceInputsMapped csPrefix (Place.proj dbase dpath) :=
      placeInputsMapped_of_localBindingSim_resolvePlace h_lbs h_resolved
    have h_mappedD : PlaceInputsMapped csPrefix dbase := h_mappedP
    have h_root := ensurePlaceRoot_run_eq_of_mapped h_mappedP
    obtain ⟨sOut0, h_sval0⟩ := placeToRegChecked_ok_of_placeInputsMapped
      (cs := csPrefix) (kind := RefKind.Shared) h_mappedS
    have h_prmS : (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).placeRegMap = csPrefix.placeRegMap :=
      h_schain.placeToRegChecked_placeRegMap RefKind.Shared csPrefix
    obtain ⟨dOut0, h_dval0⟩ := placeToRegChecked_ok_of_placeInputsMapped
      (cs := (emit
        { (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix) with
              nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg + 1 }
            [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg)
              (borrowRhs RefKind.Shared (blockSize τs) sOut0.result.reg (pathOffset spath))]) with
            nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg + 1 + 1 }
        ([Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg + 1))
            (mk (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg))]
          ++ cleanupInstrs (sOut0.result.cleanup
              ++ [((Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix).nextReg), blockSize τs)])))) (kind := RefKind.Mut)
      (PlaceInputsMapped.placeRegMap_congr (by simp only [emit]; exact h_prmS)
        _ h_mappedD)
    -- the destination lowering's value, in the spelling the StateIncr
    -- towers normalize to (read out of a `trace_state`, not guessed)
    obtain ⟨stmtOutC, h_stmtOutC⟩ :=
      compileStmt_readrhs_projdst_projsrc_offset_value (h_shape := h_shape) h_npD h_np h_o h_root
        h_sval0 h_dval0
    obtain ⟨stmtOut, h_stmtOut⟩ := h_val0 csPrefix stmtOutC h_stmtOutC
    -- §3 code inclusion for the SOURCE lowering: the three facts, once,
    -- with the projection's Borrow supplied by the nonzero-offset equations
    obtain ⟨sOutP, h_svalP, h_regP, h_clP⟩ :=
      placeToRegChecked_proj_offset_value (kind := RefKind.Shared) spath h_np h_o h_sval0
    obtain ⟨h_incrS', h_incrCS1', h_incrDrun'⟩ :=
      readrhs_projdst_incrs (h_shape := h_shape) csPrefix h_svalP
        (placeToRegChecked_proj_offset_run (kind := RefKind.Shared) spath h_np h_o h_sval0)
        h_npD h_root (h_run0 csPrefix)
    have h_incrS : StateIncr (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csPrefix)
        (CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix) :=
      StateIncr.trans (StateIncr.trans (freshReg_state_incr _) (emit_state_incr _ _)) h_incrS'
    have h_instS :=
      (CodeIncluded.of_stmt h_comp h_csAt h_stmt h_stmtOut).mono h_incrS
    -- §4-§7 the SOURCE package: mother, BRIDGE 1S, and the three
    -- instructions -- Borrow off the base, the rvalue's step, Die
    obtain ⟨h_sclean, nR, s_mid1, perms₂, vals, h_ost, h_vlen, h_runR, h_prmR,
      h_regmonoR, h_lbsR, h_psimR, h_tbdR, h_smem, h_pcR, h_vregR, h_vbelow,
      h_valsRel⟩ :=
      h_pkg' sOut0 h_sval0 _ h_regP h_clP h_instS
        ((CodeIncluded.of_stmt h_comp h_csAt h_stmt h_stmtOut).mono h_incrCS1')
    rw [h_ost] at h_step
    simp only at h_step
    cases h_dres : mirlite.resolvePlaceAcc MSB
        { s_mir with perms := perms₂ } dbase with
    | error e => rw [resolvePlaceAcc_proj_base_err h_dres] at h_step; simp at h_step
    | ok pr2 =>
    obtain ⟨rd, permsD⟩ := pr2
    rw [resolvePlaceAcc_proj_base_ok h_dres] at h_step
    simp only at h_step
    exact copy_chain_write_after_read compProg h_dchain h_comp h_stmt h_csAt
      h_stmtOut h_id_a h_wf_t h_sms h_alloc h_unmap h_prb
      h_dres (pathOffset dpath) output.values_len h_step
      h_runR h_prmR h_regmonoR h_lbsR h_psimR h_tbdR h_smem h_pcR
      h_vregR h_vbelow h_vlen h_valsRel
      -- code inclusion for the DESTINATION lowering's own instructions,
      -- transported onto the post-`Die` tower the package landed on
      ((CodeIncluded.of_stmt h_comp h_csAt h_stmt h_stmtOut).mono
        (by have h := h_incrDrun'
            rw [h_regP, h_clP] at h
            simp only [csCleanup, h_sclean, List.nil_append, List.append_nil,
              List.reverse_cons, List.map_cons] at h
            csnorm at h ⊢
            exact h))
      (fun dOut h_dval h_dclean => by
        rw [projDstTail_pos _ h_do]
        exact (h_run0 csPrefix).trans
          (compileStmt_readrhs_projdst_offset_projsrc_offset_run (h_shape := h_shape)
            h_npD h_np h_do h_o h_root h_sval0 h_sclean h_dval h_dclean))

/-- REGIME copy, PROJECTED destination at ZERO offset: `(*P).f := copy src`
    where the projection lands at offset 0, so the destination lowering
    passes the chain's own register through. Two mother-lemma calls (the
    source at `Shared`, the destination chain at `Mut`) around the
    temp-register `Load`/`RStore` pair; the projection contributes only a
    `+ 0` on the resolved address. Takes the `stmt0` transfer triple. -/
theorem copy_projdst_zero_chainsrc_simulation
    {τ τs σb : LayoutTy}
    {dbase : Place Γ σb} {path : PathTo σb τ}
    {src : Place Γ τs}
    {rhs : RExpr Γ τ} {mk : Register → Rhs}
    (compProg : oseair.Prog)
    (h_shape : ReadRhsShape rhs src mk)
    (h_pkg : ReadPkgLowered compProg rhs src mk)
    (h_dchain : PtrChain dbase)
    (h_bound : ∀ s, mirlite.preparePlaceAssign MSB s_mir (Place.proj dbase path)
        = .ok s →
      s = s_mir ∧ ∃ r0,
        mirlite.resolvePlace? s_mir (Place.proj dbase path) = some r0)
    (h_o : pathOffset path = 0)
    (h_sprm0 : ∀ cs, (CheckedCompilerM.run
      (placeToRegChecked RefKind.Shared src) cs).placeRegMap = cs.placeRegMap)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    {stmt0 : Stmt Γ}
    (h_stmt : prog.get? s_mir.pc = some stmt0)
    (h_run0 : ∀ cs, CheckedCompilerM.run (compileStmtChecked stmt0) cs
      = CheckedCompilerM.run
          (compileStmtChecked (Stmt.assign (.proj dbase path) rhs)) cs)
    (h_val0 : ∀ cs so, CheckedCompilerM.value
        (compileStmtChecked (Stmt.assign (.proj dbase path) rhs)) cs
        = Except.ok so →
      ∃ so', CheckedCompilerM.value (compileStmtChecked stmt0) cs
        = Except.ok so')
    (h_step : mirlite.stepStmt MSB s_mir
      (.assign (.proj dbase path) rhs) = .ok s_mir') :
    ∃ (s_osea' : oseair.State MSB) (n : Nat),
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa ρt s_mir' s_osea' := by
  obtain ⟨csPrefix, ⟨h_csAt, h_pc⟩, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_tbd,
    h_alloc, h_unmap, h_prb⟩ := h_inv
  -- §1 invert the source: prepare is a no-op, the source resolves and is
  -- READ, and only THEN does the destination resolve
  simp only [mirlite.stepStmt, mirlite.doAssign] at h_step
  cases h_prep : mirlite.preparePlaceAssign MSB s_mir
      (Place.proj (dbase) path) with
  | err msg => rw [h_prep] at h_step; simp at h_step
  | ok s1 =>
  rw [h_prep] at h_step
  have h_s1 := h_bound s1 h_prep
  obtain ⟨h_s1eq, r0, h_resolved⟩ := h_s1
  rw [h_s1eq] at h_step
  simp only at h_step
  cases h_eval : mirlite.evalRExpr MSB s_mir rhs with
  | err e => rw [h_eval] at h_step; simp at h_step
  | ok output =>
    rw [h_eval] at h_step
    simp only at h_step
    obtain ⟨h_mappedS, h_pkg'⟩ :=
      h_pkg _ _ s_mir s_osea csPrefix h_id_a h_wf_t h_tbd h_lbs h_prb h_sms h_alloc
        h_psim h_pc output h_eval
    -- §2 both places are mapped; the statement compiles
    have h_mapped : PlaceInputsMapped csPrefix (Place.proj (dbase) path) :=
      placeInputsMapped_of_localBindingSim_resolvePlace h_lbs h_resolved
    have h_mappedD : PlaceInputsMapped csPrefix (dbase) := h_mapped
    have h_root := ensurePlaceRoot_run_eq_of_mapped h_mapped
    have h_proj_eq := placeToRegChecked_proj_root_eq (Γ := Γ) (kind := RefKind.Mut)
      (base := dbase) path h_dchain.not_proj
    obtain ⟨sOut0, h_sval0⟩ := placeToRegChecked_ok_of_placeInputsMapped
      (cs := csPrefix) (kind := RefKind.Shared) h_mappedS
    have h_prmS : (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).placeRegMap = csPrefix.placeRegMap :=
      h_sprm0 csPrefix
    obtain ⟨dOut0, h_dval0⟩ := placeToRegChecked_ok_of_placeInputsMapped
      (cs := (emit
        { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix) with
          nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg + 1 }
        ([Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg)
            (mk sOut0.result.reg)]
          ++ cleanupInstrs sOut0.result.cleanup))) (kind := RefKind.Mut)
      (PlaceInputsMapped.placeRegMap_congr (by simp only [emit]; exact h_prmS)
        _ h_mappedD)
    obtain ⟨stmtOutC, h_stmtOutC⟩ :=
      compileStmt_readrhs_projdst_zero_value (h_shape := h_shape) h_dchain.not_proj h_o h_root
        h_sval0 h_dval0
    obtain ⟨stmtOut, h_stmtOut⟩ := h_val0 csPrefix stmtOutC h_stmtOutC
    -- §3 code inclusion for the SOURCE lowering (the three facts, once)
    obtain ⟨h_incrS, h_incrCS1', h_incrDrun'⟩ :=
      readrhs_projzerodst_incrs (h_shape := h_shape) csPrefix h_sval0 rfl h_dchain.not_proj h_o h_root (h_run0 csPrefix)
    have h_instS :=
      (CodeIncluded.of_stmt h_comp h_csAt h_stmt h_stmtOut).mono h_incrS
    -- §4-§6 the SOURCE package: mother, read transport, the rvalue's step
    obtain ⟨h_sclean, nR, s_mid1, perms₂, vals, h_ost, h_vlen, h_runR, h_prmR,
      h_regmonoR, h_lbsR, h_psimR, h_tbdR, h_smem, h_pcR, h_vregR, h_vbelow, h_valsRel⟩ :=
      h_pkg' sOut0 h_sval0 h_instS
        ((CodeIncluded.of_stmt h_comp h_csAt h_stmt h_stmtOut).mono h_incrCS1')
    rw [h_ost] at h_step
    simp only at h_step
    cases h_dres : mirlite.resolvePlaceAcc MSB
        { s_mir with perms := perms₂ } (dbase) with
    | error e => rw [resolvePlaceAcc_proj_base_err h_dres] at h_step; simp at h_step
    | ok pr2 =>
    obtain ⟨rd, permsD⟩ := pr2
    rw [resolvePlaceAcc_proj_base_ok h_dres] at h_step
    simp only at h_step
    have h_resolved_eq : ({ rd with addr := rd.addr + PathTo.offset path }
        : mirlite.PlaceRes) = rd := by
      have h_o' : PathTo.offset path = 0 := h_o
      simp [h_o']
    rw [h_resolved_eq] at h_step
    -- code inclusion for the DESTINATION lowering's own instructions
    have h_incrDrun : StateIncr (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (dbase))
        (emit
          { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix) with
            nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg + 1 }
          [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg)
            (mk sOut0.result.reg)]))
        (CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix) := by
      simpa only [csCleanup, h_sclean, List.append_nil] using h_incrDrun'
    have h_instDst :=
      (CodeIncluded.of_stmt h_comp h_csAt h_stmt h_stmtOut).mono h_incrDrun
    -- §7-§10: the destination half, shared with every other source shape
    exact copy_chainwrite_after_read compProg h_dchain h_comp h_stmt h_csAt
      h_stmtOut h_id_a h_wf_t h_sms h_alloc h_unmap h_prb
      h_dres output.values_len h_step
      h_runR h_prmR h_regmonoR h_lbsR h_psimR h_tbdR h_smem h_pcR
      h_vregR h_vbelow h_vlen h_valsRel
      h_instDst
      (fun dOut h_dval h_dclean => (h_run0 csPrefix).trans
        (compileStmt_readrhs_projdst_zero_run (h_shape := h_shape) h_dchain.not_proj h_o h_root
          h_sval0 h_sclean h_dval h_dclean))

theorem copy_projdst_offset_chainsrc_simulation
    {τ τs σb : LayoutTy}
    {dbase : Place Γ σb} {path : PathTo σb τ}
    {src : Place Γ τs}
    {rhs : RExpr Γ τ} {mk : Register → Rhs}
    (compProg : oseair.Prog)
    (h_shape : ReadRhsShape rhs src mk)
    (h_pkg : ReadPkgLowered compProg rhs src mk)
    (h_dchain : PtrChain dbase)
    (h_bound : ∀ s, mirlite.preparePlaceAssign MSB s_mir (Place.proj dbase path)
        = .ok s →
      s = s_mir ∧ ∃ r0,
        mirlite.resolvePlace? s_mir (Place.proj dbase path) = some r0)
    (h_o : pathOffset path ≠ 0)
    (h_sprm0 : ∀ cs, (CheckedCompilerM.run
      (placeToRegChecked RefKind.Shared src) cs).placeRegMap = cs.placeRegMap)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    {stmt0 : Stmt Γ}
    (h_stmt : prog.get? s_mir.pc = some stmt0)
    (h_run0 : ∀ cs, CheckedCompilerM.run (compileStmtChecked stmt0) cs
      = CheckedCompilerM.run
          (compileStmtChecked (Stmt.assign (.proj dbase path) rhs)) cs)
    (h_val0 : ∀ cs so, CheckedCompilerM.value
        (compileStmtChecked (Stmt.assign (.proj dbase path) rhs)) cs
        = Except.ok so →
      ∃ so', CheckedCompilerM.value (compileStmtChecked stmt0) cs
        = Except.ok so')
    (h_step : mirlite.stepStmt MSB s_mir
      (.assign (.proj dbase path) rhs) = .ok s_mir') :
    ∃ (s_osea' : oseair.State MSB) (n : Nat),
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa ρt s_mir' s_osea' := by
  obtain ⟨csPrefix, ⟨h_csAt, h_pc⟩, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_tbd,
    h_alloc, h_unmap, h_prb⟩ := h_inv
  -- §1 invert the source: prepare is a no-op, the source resolves and is
  -- READ, and only THEN does the destination resolve
  simp only [mirlite.stepStmt, mirlite.doAssign] at h_step
  cases h_prep : mirlite.preparePlaceAssign MSB s_mir
      (Place.proj (dbase) path) with
  | err msg => rw [h_prep] at h_step; simp at h_step
  | ok s1 =>
  rw [h_prep] at h_step
  have h_s1 := h_bound s1 h_prep
  obtain ⟨h_s1eq, r0, h_resolved⟩ := h_s1
  rw [h_s1eq] at h_step
  simp only at h_step
  cases h_eval : mirlite.evalRExpr MSB s_mir rhs with
  | err e => rw [h_eval] at h_step; simp at h_step
  | ok output =>
    rw [h_eval] at h_step
    simp only at h_step
    obtain ⟨h_mappedS, h_pkg'⟩ :=
      h_pkg _ _ s_mir s_osea csPrefix h_id_a h_wf_t h_tbd h_lbs h_prb h_sms h_alloc
        h_psim h_pc output h_eval
    -- §2 both places are mapped; the statement compiles
    have h_mapped : PlaceInputsMapped csPrefix (Place.proj (dbase) path) :=
      placeInputsMapped_of_localBindingSim_resolvePlace h_lbs h_resolved
    have h_mappedD : PlaceInputsMapped csPrefix (dbase) := h_mapped
    have h_root := ensurePlaceRoot_run_eq_of_mapped h_mapped
    have h_proj_eq := placeToRegChecked_proj_root_eq (Γ := Γ) (kind := RefKind.Mut)
      (base := dbase) path h_dchain.not_proj
    obtain ⟨sOut0, h_sval0⟩ := placeToRegChecked_ok_of_placeInputsMapped
      (cs := csPrefix) (kind := RefKind.Shared) h_mappedS
    have h_prmS : (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).placeRegMap = csPrefix.placeRegMap :=
      h_sprm0 csPrefix
    obtain ⟨dOut0, h_dval0⟩ := placeToRegChecked_ok_of_placeInputsMapped
      (cs := (emit
        { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix) with
          nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg + 1 }
        ([Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg)
            (mk sOut0.result.reg)]
          ++ cleanupInstrs sOut0.result.cleanup))) (kind := RefKind.Mut)
      (PlaceInputsMapped.placeRegMap_congr (by simp only [emit]; exact h_prmS)
        _ h_mappedD)
    obtain ⟨stmtOutC, h_stmtOutC⟩ :=
      compileStmt_readrhs_projdst_offset_value (h_shape := h_shape) h_dchain.not_proj h_o h_root
        h_sval0 h_dval0
    obtain ⟨stmtOut, h_stmtOut⟩ := h_val0 csPrefix stmtOutC h_stmtOutC
    -- §3 code inclusion for the SOURCE lowering (the three facts, once)
    obtain ⟨h_incrS, h_incrCS1', h_incrDrun'⟩ :=
      readrhs_projdst_incrs (h_shape := h_shape) csPrefix h_sval0 rfl h_dchain.not_proj h_root (h_run0 csPrefix)
    have h_instS :=
      (CodeIncluded.of_stmt h_comp h_csAt h_stmt h_stmtOut).mono h_incrS
    -- §4-§6 the SOURCE package: mother, read transport, the rvalue's step
    obtain ⟨h_sclean, nR, s_mid1, perms₂, vals, h_ost, h_vlen, h_runR, h_prmR,
      h_regmonoR, h_lbsR, h_psimR, h_tbdR, h_smem, h_pcR, h_vregR, h_vbelow, h_valsRel⟩ :=
      h_pkg' sOut0 h_sval0 h_instS
        ((CodeIncluded.of_stmt h_comp h_csAt h_stmt h_stmtOut).mono h_incrCS1')
    rw [h_ost] at h_step
    simp only at h_step
    cases h_dres : mirlite.resolvePlaceAcc MSB
        { s_mir with perms := perms₂ } (dbase) with
    | error e => rw [resolvePlaceAcc_proj_base_err h_dres] at h_step; simp at h_step
    | ok pr2 =>
    obtain ⟨rd, permsD⟩ := pr2
    rw [resolvePlaceAcc_proj_base_ok h_dres] at h_step
    simp only at h_step
    -- code inclusion for the DESTINATION lowering's own instructions
    have h_incrDrun : StateIncr (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (dbase))
        (emit
          { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix) with
            nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg + 1 }
          [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csPrefix).nextReg)
            (mk sOut0.result.reg)]))
        (CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix) := by
      simpa only [csCleanup, h_sclean, List.append_nil] using h_incrDrun'
    have h_instDst :=
      (CodeIncluded.of_stmt h_comp h_csAt h_stmt h_stmtOut).mono h_incrDrun
    -- §7-§10: the destination half -- mother, then the projected write tail
    exact copy_chain_write_after_read compProg h_dchain h_comp h_stmt h_csAt
      h_stmtOut h_id_a h_wf_t h_sms h_alloc h_unmap h_prb
      h_dres (pathOffset path) output.values_len h_step
      h_runR h_prmR h_regmonoR h_lbsR h_psimR h_tbdR h_smem h_pcR
      h_vregR h_vbelow h_vlen h_valsRel
      h_instDst
      (fun dOut h_dval h_dclean => by
        rw [projDstTail_pos _ h_o]
        exact (h_run0 csPrefix).trans
          (compileStmt_readrhs_projdst_offset_run (h_shape := h_shape) h_dchain.not_proj h_o
            h_root h_sval0 h_sclean h_dval h_dclean))

theorem copy_projdst_simulation
    {τ τs σ : LayoutTy} {base : Place Γ σ} {path : PathTo σ τ} {src : Place Γ τs}
    {rhs rhs2 : RExpr Γ τ} {mk : Register → Rhs}
    (compProg : oseair.Prog)
    (h_shape : ReadRhsShape rhs src mk)
    (h_shape2 : ReadRhsShape rhs2 (flattenPlace src) mk)
    (h_evflat : ∀ (s : mirlite.State MSB Γ) (dst : Place Γ τ),
      mirlite.stepStmt MSB s (.assign dst rhs)
        = mirlite.stepStmt MSB s (.assign dst rhs2))
    (h_pkg2 : ReadPkgLowered compProg rhs2 (flattenPlace src) mk)
    (h_sprm0 : ∀ cs, (CheckedCompilerM.run
      (placeToRegChecked RefKind.Shared (flattenPlace src)) cs).placeRegMap
      = cs.placeRegMap)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    {stmt0 : Stmt Γ}
    (h_stmt : prog.get? s_mir.pc = some stmt0)
    (h_run0 : ∀ cs, CheckedCompilerM.run (compileStmtChecked stmt0) cs
      = CheckedCompilerM.run
          (compileStmtChecked (Stmt.assign (.proj base path) rhs)) cs)
    (h_val0 : ∀ cs so, CheckedCompilerM.value
        (compileStmtChecked (Stmt.assign (.proj base path) rhs)) cs
        = Except.ok so →
      ∃ so', CheckedCompilerM.value (compileStmtChecked stmt0) cs
        = Except.ok so')
    (h_step : mirlite.stepStmt MSB s_mir
      (.assign (.proj base path) rhs) = .ok s_mir') :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' := by
  induction base with
  | «local» loc =>
      cases h_envD : mirlite.Env.lookup s_mir.env loc with
      | some bD =>
          -- CLOSED: a BOUND local root is the base case of the chain
          -- grammar, so the two base-generic proj-dst leaves own it
          have h_r0 : ∃ r0, mirlite.resolvePlace? s_mir
              (Place.proj (Place.local loc) path) = some r0 := by
            simp [mirlite.resolvePlace?, h_envD]
          have h_bound : ∀ s, mirlite.preparePlaceAssign MSB s_mir
              (Place.proj (Place.local loc) path) = .ok s →
              s = s_mir ∧ ∃ r0, mirlite.resolvePlace? s_mir
                (Place.proj (Place.local loc) path) = some r0 := by
            intro s h_prep
            obtain ⟨r0, hr0⟩ := h_r0
            simp only [mirlite.preparePlaceAssign, hr0] at h_prep
            injection h_prep with h_eq
            exact ⟨h_eq.symm, r0, hr0⟩
          rw [h_evflat] at h_step
          have h_run0' : ∀ cs, CheckedCompilerM.run (compileStmtChecked stmt0) cs
              = CheckedCompilerM.run (compileStmtChecked
                  (Stmt.assign (.proj (Place.local loc) path)
                    rhs2)) cs :=
            fun cs => (h_run0 cs).trans
              (compileStmt_readrhs_projdst_srcflatten_run (h_shape := h_shape) (h_shape2 := h_shape2) (Place.local loc) path src cs)
          have h_val0' : ∀ cs so, CheckedCompilerM.value (compileStmtChecked
              (Stmt.assign (.proj (Place.local loc) path)
                rhs2)) cs = Except.ok so →
              ∃ so', CheckedCompilerM.value (compileStmtChecked stmt0) cs
                = Except.ok so' := by
            intro cs so h
            obtain ⟨so2, h2⟩ := compileStmt_readrhs_projdst_srcflatten_value (h_shape := h_shape) (h_shape2 := h_shape2)
              (Place.local loc) path src cs ⟨so, h⟩
            exact h_val0 cs so2 h2
          by_cases h_o : pathOffset path = 0
          · obtain ⟨s_osea', n, h_run, h_inv'⟩ :=
              copy_projdst_zero_chainsrc_simulation (dbase := Place.local loc)
                (path := path) (src := flattenPlace src) compProg
                h_shape2 h_pkg2 (PtrChain.base loc) h_bound h_o
                h_sprm0
                h_comp h_inv h_stmt
                h_run0' h_val0' h_step
            exact ⟨ρa, ρt, s_osea', n, AddrRenameIncr.refl ρa,
              TagRenameIncr.refl ρt, h_run, h_inv'⟩
          · obtain ⟨s_osea', n, h_run, h_inv'⟩ :=
              copy_projdst_offset_chainsrc_simulation (dbase := Place.local loc)
                (path := path) (src := flattenPlace src) compProg
                h_shape2 h_pkg2 (PtrChain.base loc) h_bound h_o
                h_sprm0
                h_comp h_inv h_stmt
                h_run0' h_val0' h_step
            exact ⟨ρa, ρt, s_osea', n, AddrRenameIncr.refl ρa,
              TagRenameIncr.refl ρt, h_run, h_inv'⟩
      | none =>
          -- an UNBOUND root allocates before the rhs runs (regime B-proj)
          rw [h_evflat] at h_step
          have h_run0' : ∀ cs, CheckedCompilerM.run (compileStmtChecked stmt0) cs
              = CheckedCompilerM.run (compileStmtChecked
                  (Stmt.assign (.proj (Place.local loc) path)
                    rhs2)) cs :=
            fun cs => (h_run0 cs).trans
              (compileStmt_readrhs_projdst_srcflatten_run (h_shape := h_shape) (h_shape2 := h_shape2) (Place.local loc) path src cs)
          have h_val0' : ∀ cs so, CheckedCompilerM.value (compileStmtChecked
              (Stmt.assign (.proj (Place.local loc) path)
                rhs2)) cs = Except.ok so →
              ∃ so', CheckedCompilerM.value (compileStmtChecked stmt0) cs
                = Except.ok so' := by
            intro cs so h
            obtain ⟨so2, h2⟩ := compileStmt_readrhs_projdst_srcflatten_value (h_shape := h_shape) (h_shape2 := h_shape2)
              (Place.local loc) path src cs ⟨so, h⟩
            exact h_val0 cs so2 h2
          exact copy_projlocal_fresh_simulation (src := flattenPlace src)
            compProg h_shape2 h_pkg2 h_sprm0
            h_comp h_inv h_stmt h_run0' h_val0' h_envD h_step
  | proj b q ih =>
      refine ih
        (fun cs => (h_run0 cs).trans
          (compileStmt_assign_proj_assoc_run b q path rhs cs))
        (fun cs so h => by
          obtain ⟨so', h'⟩ :=
            compileStmt_assign_proj_assoc_value b q path rhs cs h
          exact h_val0 cs so' h')
        ?_
      rw [← stepStmt_assign_dst_proj_assoc s_mir b q path rhs]
      exact h_step
  | deref pp =>
      by_cases h_o : pathOffset path = 0
      · -- FLATTEN both places, then the proj-zero two-mother leaf
        rw [stepStmt_assign_dstflatten, h_evflat] at h_step
        rw [show flattenPlace (Place.proj (Place.deref pp) path)
            = Place.proj (Place.deref (flattenPlace pp)) path from rfl] at h_step
        obtain ⟨s_osea', n, h_run, h_inv'⟩ :=
          copy_projdst_zero_chainsrc_simulation
            (dbase := Place.deref (flattenPlace pp))
            (path := path) (src := flattenPlace src) compProg
            h_shape2 h_pkg2 (PtrChain_flatten_deref pp)
            (fun s h_prep => by
              simp only [mirlite.preparePlaceAssign] at h_prep
              split at h_prep
              · rename_i r0 h_r0
                cases h_prep
                exact ⟨rfl, r0, h_r0⟩
              · simp [mirlite.allocateRoot] at h_prep)
            h_o
                h_sprm0
                h_comp h_inv h_stmt
            (fun cs => (h_run0 cs).trans
              ((compileStmt_readrhs_projdst_srcflatten_run (h_shape := h_shape) (h_shape2 := h_shape2) (Place.deref pp) path src cs).trans
                (compileStmt_readrhs_projderefdst_dstflatten_run (h_shape := h_shape2) pp path
                  (flattenPlace src) cs)))
            (fun cs so h => by
              obtain ⟨so2, h2⟩ :=
                compileStmt_readrhs_projdst_srcflatten_value (h_shape := h_shape) (h_shape2 := h_shape2) (Place.deref pp) path src cs
                  (compileStmt_readrhs_projderefdst_dstflatten_value (h_shape := h_shape2) pp path
                    (flattenPlace src) cs ⟨so, h⟩)
              exact h_val0 cs so2 h2)
            h_step
        exact ⟨ρa, ρt, s_osea', n, AddrRenameIncr.refl ρa, TagRenameIncr.refl ρt,
          h_run, h_inv'⟩
      · -- nonzero offset: the same skeleton inside the projection's own
        -- `Borrow`/`Die`
        rw [stepStmt_assign_dstflatten, h_evflat] at h_step
        rw [show flattenPlace (Place.proj (Place.deref pp) path)
            = Place.proj (Place.deref (flattenPlace pp)) path from rfl] at h_step
        obtain ⟨s_osea', n, h_run, h_inv'⟩ :=
          copy_projdst_offset_chainsrc_simulation
            (dbase := Place.deref (flattenPlace pp))
            (path := path) (src := flattenPlace src) compProg
            h_shape2 h_pkg2 (PtrChain_flatten_deref pp)
            (fun s h_prep => by
              simp only [mirlite.preparePlaceAssign] at h_prep
              split at h_prep
              · rename_i r0 h_r0
                cases h_prep
                exact ⟨rfl, r0, h_r0⟩
              · simp [mirlite.allocateRoot] at h_prep)
            h_o
                h_sprm0
                h_comp h_inv h_stmt
            (fun cs => (h_run0 cs).trans
              ((compileStmt_readrhs_projdst_srcflatten_run (h_shape := h_shape) (h_shape2 := h_shape2) (Place.deref pp) path src cs).trans
                (compileStmt_readrhs_projderefdst_dstflatten_run (h_shape := h_shape2) pp path
                  (flattenPlace src) cs)))
            (fun cs so h => by
              obtain ⟨so2, h2⟩ :=
                compileStmt_readrhs_projdst_srcflatten_value (h_shape := h_shape) (h_shape2 := h_shape2) (Place.deref pp) path src cs
                  (compileStmt_readrhs_projderefdst_dstflatten_value (h_shape := h_shape2) pp path
                    (flattenPlace src) cs ⟨so, h⟩)
              exact h_val0 cs so2 h2)
            h_step
        exact ⟨ρa, ρt, s_osea', n, AddrRenameIncr.refl ρa, TagRenameIncr.refl ρt,
          h_run, h_inv'⟩

/-- Every PROJECTED destination whose flattened SOURCE is a projection
    at NONZERO offset, by recursion on the destination's BASE place —
    the mirror of `copy_projdst_simulation` for the one source shape
    that cannot supply a `LoweringSim` package (its lowering emits a
    `Borrow(Shared)` and leaves a cleanup `Die`, so the READ has to be
    bracketed by BRIDGE 1S inside the leaf). Nested projections peel
    with the associativity transfers; a deref base flattens first. -/
theorem copy_projdst_projsrc_offset_simulation
    {τ τs σ σs : LayoutTy} {base : Place Γ σ} {path : PathTo σ τ}
    {B : Place Γ σs} {spath : PathTo σs τs}
    {rhs : RExpr Γ τ} {mk : Register → Rhs}
    (compProg : oseair.Prog)
    (h_shape : ReadRhsShape rhs (.proj B spath) mk)
    (h_pkg : ReadPkgProjOffset compProg rhs B spath mk)
    (h_schain : PtrChain B)
    (h_o : pathOffset spath ≠ 0)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    {stmt0 : Stmt Γ}
    (h_stmt : prog.get? s_mir.pc = some stmt0)
    (h_run0 : ∀ cs, CheckedCompilerM.run (compileStmtChecked stmt0) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.proj base path) rhs)) cs)
    (h_val0 : ∀ cs so, CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.proj base path) rhs)) cs
        = Except.ok so →
      ∃ so', CheckedCompilerM.value (compileStmtChecked stmt0) cs
        = Except.ok so')
    (h_step : mirlite.stepStmt MSB s_mir
      (.assign (.proj base path) rhs) = .ok s_mir') :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' := by
  induction base with
  | «local» loc =>
      cases h_envD : mirlite.Env.lookup s_mir.env loc with
      | some bD =>
          have h_r0 : ∃ r0, mirlite.resolvePlace? s_mir
              (Place.proj (Place.local loc) path) = some r0 := by
            simp [mirlite.resolvePlace?, h_envD]
          have h_bound : ∀ s, mirlite.preparePlaceAssign MSB s_mir
              (Place.proj (Place.local loc) path) = .ok s →
              s = s_mir ∧ ∃ r0, mirlite.resolvePlace? s_mir
                (Place.proj (Place.local loc) path) = some r0 := by
            intro s h_prep
            obtain ⟨r0, hr0⟩ := h_r0
            simp only [mirlite.preparePlaceAssign, hr0] at h_prep
            injection h_prep with h_eq
            exact ⟨h_eq.symm, r0, hr0⟩
          by_cases h_do : pathOffset path = 0
          · obtain ⟨s_osea', n, h_run, h_inv'⟩ :=
              copy_projdst_zero_projsrc_offset_simulation
                (dbase := Place.local loc) (dpath := path) (B := B) (spath := spath)
                compProg h_shape h_pkg (PtrChain.base loc) (fun _ _ _ h => by cases h) h_do
                h_bound h_schain h_o h_comp h_inv h_stmt h_run0 h_val0 h_step
            exact ⟨ρa, ρt, s_osea', n, AddrRenameIncr.refl ρa,
              TagRenameIncr.refl ρt, h_run, h_inv'⟩
          · obtain ⟨s_osea', n, h_run, h_inv'⟩ :=
              copy_projdst_offset_projsrc_offset_simulation
                (dbase := Place.local loc) (dpath := path) (B := B) (spath := spath)
                compProg h_shape h_pkg (PtrChain.base loc) (fun _ _ _ h => by cases h) h_do
                h_bound h_schain h_o h_comp h_inv h_stmt h_run0 h_val0 h_step
            exact ⟨ρa, ρt, s_osea', n, AddrRenameIncr.refl ρa,
              TagRenameIncr.refl ρt, h_run, h_inv'⟩
      | none =>
          -- an UNBOUND root allocates before the rhs runs (regime B-proj);
          -- closed at ZERO destination offset, residual at nonzero
          exact copy_projlocal_fresh_projsrc_simulation
            (B := B) (spath := spath) compProg h_shape h_pkg h_schain h_o h_comp h_inv
            h_stmt h_run0 h_val0 h_envD h_step
  | proj b q ih =>
      refine ih
        (fun cs => (h_run0 cs).trans
          (compileStmt_assign_proj_assoc_run b q path rhs cs))
        (fun cs so h => by
          obtain ⟨so', h'⟩ :=
            compileStmt_assign_proj_assoc_value b q path rhs cs h
          exact h_val0 cs so' h')
        ?_
      rw [← stepStmt_assign_dst_proj_assoc s_mir b q path rhs]
      exact h_step
  | deref pp =>
      rw [stepStmt_assign_dstflatten] at h_step
      rw [show flattenPlace (Place.proj (Place.deref pp) path)
          = Place.proj (Place.deref (flattenPlace pp)) path from rfl] at h_step
      by_cases h_do : pathOffset path = 0
      · obtain ⟨s_osea', n, h_run, h_inv'⟩ :=
          copy_projdst_zero_projsrc_offset_simulation
            (dbase := Place.deref (flattenPlace pp)) (dpath := path)
            (B := B) (spath := spath) compProg h_shape h_pkg
            (PtrChain_flatten_deref pp) (fun _ _ _ h => by cases h) h_do
            (fun s h_prep => by
              simp only [mirlite.preparePlaceAssign] at h_prep
              split at h_prep
              · rename_i r0 h_r0
                cases h_prep
                exact ⟨rfl, r0, h_r0⟩
              · simp [mirlite.allocateRoot] at h_prep)
            h_schain h_o h_comp h_inv h_stmt
            (fun cs => (h_run0 cs).trans
              (compileStmt_readrhs_projderefdst_dstflatten_run (h_shape := h_shape) pp path
                (Place.proj B spath) cs))
            (fun cs so h => by
              obtain ⟨so2, h2⟩ :=
                compileStmt_readrhs_projderefdst_dstflatten_value (h_shape := h_shape) pp path
                  (Place.proj B spath) cs ⟨so, h⟩
              exact h_val0 cs so2 h2)
            h_step
        exact ⟨ρa, ρt, s_osea', n, AddrRenameIncr.refl ρa, TagRenameIncr.refl ρt,
          h_run, h_inv'⟩
      · obtain ⟨s_osea', n, h_run, h_inv'⟩ :=
          copy_projdst_offset_projsrc_offset_simulation
            (dbase := Place.deref (flattenPlace pp)) (dpath := path)
            (B := B) (spath := spath) compProg h_shape h_pkg
            (PtrChain_flatten_deref pp) (fun _ _ _ h => by cases h) h_do
            (fun s h_prep => by
              simp only [mirlite.preparePlaceAssign] at h_prep
              split at h_prep
              · rename_i r0 h_r0
                cases h_prep
                exact ⟨rfl, r0, h_r0⟩
              · simp [mirlite.allocateRoot] at h_prep)
            h_schain h_o h_comp h_inv h_stmt
            (fun cs => (h_run0 cs).trans
              (compileStmt_readrhs_projderefdst_dstflatten_run (h_shape := h_shape) pp path
                (Place.proj B spath) cs))
            (fun cs so h => by
              obtain ⟨so2, h2⟩ :=
                compileStmt_readrhs_projderefdst_dstflatten_value (h_shape := h_shape) pp path
                  (Place.proj B spath) cs ⟨so, h⟩
              exact h_val0 cs so2 h2)
            h_step
        exact ⟨ρa, ρt, s_osea', n, AddrRenameIncr.refl ρa, TagRenameIncr.refl ρt,
          h_run, h_inv'⟩

/-- The source-flattening bridge, at a LOCAL destination. Every
    dispatch branch whose source flattens to a projection needs the
    same pair — the compiled run agrees at the two spellings, and a
    compiled value at the normal form yields one at the original — so
    state it once, parameterised by the normal form. -/
theorem copy_local_srcflat_bridge {Γ : Ctx} {τ τs σ' : LayoutTy}
    {dstLoc : Local Γ τ} (src : Place Γ τs) {B : Place Γ σ'} {path' : PathTo σ' τs}
    {rhs rhs2 : RExpr Γ τ} {mk : Register → Rhs}
    (h_shape : ReadRhsShape rhs src mk)
    (h_shape2 : ReadRhsShape rhs2 (Place.proj B path') mk)
    (h_flat : flattenPlace src = Place.proj B path') :
    (∀ cs, CheckedCompilerM.run
        (compileStmtChecked (Stmt.assign (.local dstLoc) rhs)) cs
      = CheckedCompilerM.run (compileStmtChecked
          (Stmt.assign (.local dstLoc) rhs2)) cs)
    ∧ (∀ cs so, CheckedCompilerM.value (compileStmtChecked
        (Stmt.assign (.local dstLoc) rhs2)) cs = Except.ok so →
        ∃ so', CheckedCompilerM.value (compileStmtChecked
          (Stmt.assign (.local dstLoc) rhs)) cs = Except.ok so') := by
  have h_shape2' : ReadRhsShape rhs2 (flattenPlace src) mk := by
    rw [h_flat]; exact h_shape2
  exact ⟨fun cs => compileStmt_readrhs_srcflatten_run
      (h_shape := h_shape) (h_shape2 := h_shape2') src cs,
    fun cs so h => compileStmt_readrhs_srcflatten_value
      (h_shape := h_shape) (h_shape2 := h_shape2') src cs ⟨so, h⟩⟩

/-- The same bridge at a DEREF destination, where BOTH places flatten.
    `X` is the source's normal form; pass `rfl` when it is literally
    `flattenPlace src`. -/
theorem copy_derefdst_flat_bridge {Γ : Ctx} {τ τs : LayoutTy}
    (pp : Place Γ (obseq.LayoutTy.PtrL τ)) (src : Place Γ τs)
    {X : Place Γ τs} {rhs rhs2 : RExpr Γ τ} {mk : Register → Rhs}
    (h_shape : ReadRhsShape rhs src mk)
    (h_shape2 : ReadRhsShape rhs2 X mk)
    (h_seq : flattenPlace src = X) :
    (∀ cs, CheckedCompilerM.run
        (compileStmtChecked (Stmt.assign (.deref pp) rhs)) cs
      = CheckedCompilerM.run (compileStmtChecked
          (Stmt.assign (.deref (flattenPlace pp)) rhs2)) cs)
    ∧ (∀ cs so, CheckedCompilerM.value (compileStmtChecked
        (Stmt.assign (.deref (flattenPlace pp)) rhs2)) cs = Except.ok so →
        ∃ so', CheckedCompilerM.value (compileStmtChecked
          (Stmt.assign (.deref pp) rhs)) cs = Except.ok so') := by
  subst h_seq
  refine ⟨fun cs => ?_, fun cs so h => ?_⟩
  · exact (compileStmt_readrhs_derefdst_srcflatten_run (h_shape := h_shape)
      (h_shape2 := h_shape2) pp src cs).trans
      (compileStmt_readrhs_derefdst_dstflatten_run (h_shape := h_shape2) pp
        (flattenPlace src) cs)
  · exact compileStmt_readrhs_derefdst_srcflatten_value (h_shape := h_shape)
      (h_shape2 := h_shape2) pp src cs
      (compileStmt_readrhs_derefdst_dstflatten_value (h_shape := h_shape2) pp
        (flattenPlace src) cs ⟨so, h⟩)

/-- Everything a read-then-store rvalue must supply for the generic
    per-statement dispatcher: the compiled shape at every source place,
    that flattening the source does not change the mirlite step, and the
    two read packages (chain-class sources and projected sources at a
    nonzero offset). `copy`, `exposeAddr` and `fromExposed` differ only
    in these four fields. -/
structure ReadRhsFamily {Γ : Ctx} {σ τ : LayoutTy} (compProg : oseair.Prog)
    (rhsOf : Place Γ σ → RExpr Γ τ) (mk : Register → Rhs) : Prop where
  shape : ∀ src, ReadRhsShape (rhsOf src) src mk
  stepFlat : ∀ (s : mirlite.State MSB Γ) (dst : Place Γ τ) (src : Place Γ σ),
    mirlite.stepStmt MSB s (.assign dst (rhsOf src))
      = mirlite.stepStmt MSB s (.assign dst (rhsOf (flattenPlace src)))
  pkgLowered : ∀ (src : Place Γ σ), LoweringSimAny compProg src →
    ReadPkgLowered compProg (rhsOf src) src mk
  pkgProjOffset : ∀ {σs : LayoutTy} (B : Place Γ σs) (spath : PathTo σs σ),
    LoweringSimAny compProg B →
    (∀ (σ' : LayoutTy) (b : Place Γ σ') (q : PathTo σ' σs), B = b.proj q → False) →
    pathOffset spath ≠ 0 →
    ReadPkgProjOffset compProg (rhsOf (.proj B spath)) B spath mk

/-- LEAF SORRY 2 → DISPATCHER 2026-08-28: per-statement simulation for
    `.assign dst (.copy src)`, decomposed by the shapes of the two
    places. Regime L→L (both bound locals, any layout) is CLOSED by
    `copy_local_local_simulation`; the residual shapes are named. -/
theorem CompilerInv_step_readrhs
    {σ τ : LayoutTy}
    {dst : Place Γ τ} {src : Place Γ σ}
    {rhsOf : Place Γ σ → RExpr Γ τ} {mk : Register → Rhs}
    (compProg : oseair.Prog)
    (F : ReadRhsFamily compProg rhsOf mk)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    (h_stmt : prog.get? s_mir.pc = some (.assign dst (rhsOf src)))
    (h_step : mirlite.stepStmt MSB s_mir (.assign dst (rhsOf src)) = .ok s_mir') :
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
              obtain ⟨_, s_osea', n, h_incr_t, h_run, h_inv'⟩ :=
                storereg_local_simulation compProg
                  (ValuePkg.of_readPkgLowered compProg (F.shape _)
                    (F.pkgLowered _ (PtrChain.base srcLoc).loweringSimAny))
                  h_comp h_inv h_stmt
                  (fun _ => rfl) (fun _ so h => ⟨so, h⟩)
                  h_envD h_step
              exact ⟨ρa, _, s_osea', n, AddrRenameIncr.refl ρa,
                h_incr_t, h_run, h_inv'⟩
          | none =>
              -- CLOSED: fresh destination, chain source (regime B for copy)
              exact copy_fresh_chainsrc_simulation (src := .local srcLoc) compProg
                (F.shape _)
                (F.pkgLowered _ (PtrChain.base srcLoc).loweringSimAny)
                h_comp h_inv h_stmt
                (fun _ => rfl) (fun _ so h => ⟨so, h⟩) h_envD h_step
      | proj sbase ff =>
          -- FLATTEN the whole src BEFORE the destination split: its normal
          -- form is ONE projection over a canonical chain, and both env
          -- cases hand that same normal form to their collapsed leaves
          obtain ⟨σ', Bc, path', h_flat, h_chain⟩ := flatten_proj_chainish sbase ff
          rw [F.stepFlat, h_flat] at h_step
          obtain ⟨h_run0, h_val0⟩ := copy_local_srcflat_bridge (dstLoc := dstLoc) _ (F.shape _)
            (F.shape _) h_flat
          cases h_envD : mirlite.Env.lookup s_mir.env dstLoc with
          | some bD =>
              by_cases h_off : pathOffset path' = 0
              · obtain ⟨s_osea', n, h_run, h_inv'⟩ :=
                  copy_projchain_zero_simulation compProg (F.shape _)
                    (F.pkgLowered _
                      (LoweringSimAny.projZero h_chain.not_proj h_off
                        h_chain.loweringSimAny))
                    h_chain h_off h_comp h_inv
                    h_stmt h_run0 h_val0 h_envD h_step
                exact ⟨ρa, ρt, s_osea', n, AddrRenameIncr.refl ρa,
                  TagRenameIncr.refl ρt, h_run, h_inv'⟩
              · obtain ⟨s_osea', n, h_run, h_inv'⟩ :=
                  copy_projchain_offset_simulation compProg (F.shape _)
                    (F.pkgProjOffset _ _ h_chain.loweringSimAny
                      h_chain.not_proj h_off)
                    h_chain h_off h_comp h_inv
                    h_stmt h_run0 h_val0 h_envD h_step
                exact ⟨ρa, ρt, s_osea', n, AddrRenameIncr.refl ρa,
                  TagRenameIncr.refl ρt, h_run, h_inv'⟩
          | none =>
              -- CLOSED: fresh destination, proj-topped source (regime B)
              by_cases h_off : pathOffset path' = 0
              · exact copy_fresh_projchain_zero_simulation compProg
                  (F.shape _)
                  (F.pkgLowered _
                    (LoweringSimAny.projZero h_chain.not_proj h_off
                      h_chain.loweringSimAny))
                  h_chain h_off
                  h_comp h_inv h_stmt h_run0 h_val0 h_envD h_step
              · exact copy_fresh_projchain_offset_simulation compProg
                  (F.shape _)
                  (F.pkgProjOffset _ _ h_chain.loweringSimAny
                    h_chain.not_proj h_off)
                  h_chain h_off
                  h_comp h_inv h_stmt h_run0 h_val0 h_envD h_step
      | deref pp =>
          cases h_envD : mirlite.Env.lookup s_mir.env dstLoc with
          | some bD =>
              -- CLOSED: `dst := copy *chain` — flatten-normalized, TOTAL
              rw [F.stepFlat] at h_step
              obtain ⟨_, s_osea', n, h_incr_t, h_run, h_inv'⟩ :=
                storereg_local_simulation compProg
                  (ValuePkg.of_readPkgLowered compProg (F.shape _)
                    (F.pkgLowered _ (PtrChain_flatten_deref pp).loweringSimAny))
                  h_comp h_inv h_stmt
                  (fun cs => compileStmt_readrhs_derefsrc_flatten_run (h_shape := F.shape _) (h_shape2 := F.shape _) cs)
                  (fun cs so h => compileStmt_readrhs_derefsrc_flatten_value (h_shape := F.shape _) (h_shape2 := F.shape _) cs so h)
                  h_envD h_step
              exact ⟨ρa, _, s_osea', n, AddrRenameIncr.refl ρa,
                h_incr_t, h_run, h_inv'⟩
          | none =>
              -- CLOSED: fresh destination, deref-chain source
              rw [F.stepFlat] at h_step
              exact copy_fresh_chainsrc_simulation (src := .deref (flattenPlace pp))
                compProg (F.shape _)
                (F.pkgLowered _ (PtrChain_flatten_deref pp).loweringSimAny)
                h_comp h_inv h_stmt
                (fun cs => compileStmt_readrhs_derefsrc_flatten_run (h_shape := F.shape _) (h_shape2 := F.shape _) cs)
                (fun cs so h => compileStmt_readrhs_derefsrc_flatten_value (h_shape := F.shape _) (h_shape2 := F.shape _) cs so h)
                h_envD h_step
  | proj dbase dpath =>
      -- the recursion peels any nesting first; the source only has to
      -- SUPPLY the lowering package, which a chain does and a
      -- zero-offset projection over a chain does too
      rcases flatten_chainish src with h_sch | ⟨σs, B, spath, h_seq, h_B⟩
      · exact copy_projdst_simulation (base := dbase) (path := dpath)
          (src := src) compProg (F.shape _) (F.shape _)
          (fun s dst => F.stepFlat s dst src)
          (F.pkgLowered _ h_sch.loweringSimAny)
          (fun cs => h_sch.placeToRegChecked_placeRegMap RefKind.Shared cs)
          h_comp h_inv h_stmt (fun _ => rfl) (fun _ so h => ⟨so, h⟩) h_step
      · by_cases h_o : pathOffset spath = 0
        · refine copy_projdst_simulation (base := dbase) (path := dpath)
            (src := src) compProg (F.shape _) (F.shape _)
            (fun s dst => F.stepFlat s dst src) ?_ ?_
            h_comp h_inv h_stmt (fun _ => rfl) (fun _ so h => ⟨so, h⟩) h_step
          · refine F.pkgLowered _ ?_
            rw [h_seq]
            exact LoweringSimAny.projZero h_B.not_proj h_o h_B.loweringSimAny
          · rw [h_seq]
            exact projZero_placeRegMap h_B.not_proj h_o
              (fun cs => h_B.placeToRegChecked_placeRegMap RefKind.Shared cs)
        · rw [F.stepFlat, h_seq] at h_step
          exact copy_projdst_projsrc_offset_simulation (base := dbase)
            (path := dpath) (B := B) (spath := spath) compProg
            (F.shape _)
            (F.pkgProjOffset _ _ h_B.loweringSimAny h_B.not_proj h_o)
            h_B h_o
            h_comp h_inv h_stmt
            (fun cs =>
              (compileStmt_readrhs_projdst_srcflatten_run (h_shape := F.shape _) (h_shape2 := F.shape _) dbase dpath src cs).trans
                (by rw [h_seq]))
            (fun cs so h => by
              refine compileStmt_readrhs_projdst_srcflatten_value (h_shape := F.shape _) (h_shape2 := F.shape _) dbase dpath src cs ?_
              rw [h_seq]
              exact ⟨so, h⟩)
            h_step
  | deref pp =>
      -- FLATTEN both places, then the two-mother leaf owns every
      -- spelling whose flattened source is a chain
      rcases flatten_chainish src with h_sch | ⟨σs, B, spath, h_seq, h_B⟩
      · rw [stepStmt_assign_dstflatten, F.stepFlat] at h_step
        rw [show flattenPlace (Place.deref pp) = Place.deref (flattenPlace pp) from rfl]
          at h_step
        obtain ⟨s_osea', n, h_run, h_inv'⟩ :=
          copy_chaindst_chainsrc_simulation (P := flattenPlace pp)
            (src := flattenPlace src) compProg
            (F.shape _)
            (F.pkgLowered _ h_sch.loweringSimAny)
            (fun cs => h_sch.placeToRegChecked_placeRegMap RefKind.Shared cs)
            (PtrChain_flatten_deref pp) h_comp h_inv h_stmt
            (copy_derefdst_flat_bridge pp src (F.shape _) (F.shape _) rfl).1
            (copy_derefdst_flat_bridge pp src (F.shape _) (F.shape _) rfl).2
            h_step
        exact ⟨ρa, ρt, s_osea', n, AddrRenameIncr.refl ρa, TagRenameIncr.refl ρt,
          h_run, h_inv'⟩
      · -- the flattened source is PROJ-topped over a chain
        by_cases h_o : pathOffset spath = 0
        · rw [stepStmt_assign_dstflatten, F.stepFlat] at h_step
          rw [show flattenPlace (Place.deref pp) = Place.deref (flattenPlace pp) from rfl,
            h_seq] at h_step
          obtain ⟨s_osea', n, h_run, h_inv'⟩ :=
            copy_chaindst_projsrc_zero_simulation (P := flattenPlace pp) (B := B)
              (spath := spath) compProg (F.shape _)
              (F.pkgLowered _
                (LoweringSimAny.projZero h_B.not_proj h_o h_B.loweringSimAny))
              (PtrChain_flatten_deref pp) h_B h_o
              h_comp h_inv h_stmt
              (copy_derefdst_flat_bridge pp src (F.shape _) (F.shape _) h_seq).1
              (copy_derefdst_flat_bridge pp src (F.shape _) (F.shape _) h_seq).2
              h_step
          exact ⟨ρa, ρt, s_osea', n, AddrRenameIncr.refl ρa, TagRenameIncr.refl ρt,
            h_run, h_inv'⟩
        · rw [stepStmt_assign_dstflatten, F.stepFlat] at h_step
          rw [show flattenPlace (Place.deref pp) = Place.deref (flattenPlace pp) from rfl,
            h_seq] at h_step
          obtain ⟨s_osea', n, h_run, h_inv'⟩ :=
            copy_chaindst_projsrc_offset_simulation (P := flattenPlace pp) (B := B)
              (spath := spath) compProg (F.shape _)
              (F.pkgProjOffset _ _ h_B.loweringSimAny h_B.not_proj h_o)
              (PtrChain_flatten_deref pp) h_B h_o
              h_comp h_inv h_stmt
              (copy_derefdst_flat_bridge pp src (F.shape _) (F.shape _) h_seq).1
              (copy_derefdst_flat_bridge pp src (F.shape _) (F.shape _) h_seq).2
              h_step
          exact ⟨ρa, ρt, s_osea', n, AddrRenameIncr.refl ρa, TagRenameIncr.refl ρt,
            h_run, h_inv'⟩

/-- `copy` is a read-then-store family: its source place carries its own
    layout, and the instruction it emits is the `Load`. -/
theorem copy_readRhsFamily {Γ : Ctx} {τ : LayoutTy} (compProg : oseair.Prog) :
    ReadRhsFamily (Γ := Γ) compProg (fun src => RExpr.copy (τ := τ) src)
      (Rhs.Load (layoutToTyVal τ)) where
  shape := fun src => readRhsShape_copy src
  stepFlat := fun s dst src => stepStmt_assign_copysrc_anyflatten s dst src
  pkgLowered := fun _ h => copy_readpkg_lowered compProg h
  pkgProjOffset := fun _ _ h _ _ => copy_readpkg_projoffset compProg h

theorem CompilerInv_step_copy
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
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' :=
  CompilerInv_step_readrhs compProg (copy_readRhsFamily compProg) h_comp h_inv
    h_stmt h_step

end obseq3.proof
