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
    · grind [emit]
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
    (by grind [emit]),
    (by grind [emit]),
    ?_, h_psim2,
    (by rw [sb_read_NextTag h_read_src, sb_read_NextTag h_read_tgt, h_snt1]
        exact TagRenameBounded.mono h_tbd (Nat.le_refl _) h_snt2),
    h_smem, h_spc,
    (by rw [h_spc]; simp only [emit, List.length_cons, List.length_nil]),
    (by grind [emit]),
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
    · grind [emit]
    · rw [emit_code_lt_nextLabel _ _ (by
        grind [emit])]
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
    · grind [emit]
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
    · grind [emit]
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
    grind
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
    h_prmCS2, (by grind [emit]), ?_, h_psim2q,
    (by rw [sb_read_NextTag h_read_src, h_snt1]
        refine TagRenameBounded.mono h_tbd (Nat.le_refl _) ?_
        refine Nat.le_trans h_snt2 ?_
        rw [← sb_read_NextTag h_read_tgt]
        exact h_ntle),
    h_smem, h_spc,
    (by rw [h_spc]; simp only [emit, List.length_cons, List.length_nil]),
    (by grind [emit]),
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
    (h_prmS : ∀ cs, (CheckedCompilerM.run
      (placeToRegChecked RefKind.Shared src) cs).placeRegMap = cs.placeRegMap)
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
  refine ⟨fun d => Instr.RStore (layoutToTyVal τ) (Register.R
      (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg) d,
    _, rfl, fun _ => rfl, rfl,
    by simp only [emit]; exact h_prmS csA, ?_⟩
  intro h_code
  obtain ⟨h_sclean, nR, sR, perms₂, vals, h_ost, h_vlen, h_runR, h_prmR,
    h_regmonoR, h_lbsR, h_psimR, h_tbdR, h_smem, h_pcR, h_vregR, h_vbelow,
    h_valsRel⟩ :=
    h_pkg' sOut0 h_sval0
      (h_code.mono (StateIncr.trans (freshReg_state_incr _) (emit_state_incr _ _)))
      h_code
  -- with the source cleanup empty the two spellings of the tower agree
  simp only [csCleanup, h_sclean, List.append_nil]
  have h_execR := StoreStep.rstore compProg sR _ (layoutToTyVal τ) _ vals
    h_vregR h_vbelow
  exact ⟨ρt, nR, sR, perms₂, vals, TagRenameIncr.refl ρt, h_wf_t, h_ost, h_vlen,
    h_runR, h_prmR, h_regmonoR, h_lbsR, h_psimR, h_tbdR, h_smem, h_pcR, h_execR,
    h_valsRel⟩

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

/-- Every projected-source read package is a value package too: the
    projection's `Borrow`, the rvalue's instruction and the `Die` that
    retires the borrow all live inside `compileRExprPreChecked rhs`, so
    the single code-inclusion obligation covers all three. -/
theorem ValuePkg.of_readPkgProjOffset
    {σs τs τ : LayoutTy} {rhs : RExpr Γ τ} {B : Place Γ σs} {spath : PathTo σs τs}
    {mk : Register → Rhs}
    (compProg : oseair.Prog)
    (h_shape : ReadRhsShape rhs (.proj B spath) mk)
    (h_np : ∀ (σ' : LayoutTy) (b : Place Γ σ') (q : PathTo σ' σs),
      B = b.proj q → False)
    (h_o : pathOffset spath ≠ 0)
    (h_prmB : ∀ cs, (CheckedCompilerM.run
      (placeToRegChecked RefKind.Shared B) cs).placeRegMap = cs.placeRegMap)
    (h_pkg : ReadPkgProjOffset compProg rhs B spath mk) :
    ValuePkg compProg rhs := by
  intro ρa ρt sM sA csA h_id_a h_wf_t h_tbd h_lbs h_prb h_sms h_alloc h_psim h_pc
    output h_eval
  obtain ⟨ev, h_rhs⟩ := id h_shape
  obtain ⟨h_mapped, h_pkg'⟩ :=
    h_pkg ρa ρt sM sA csA h_id_a h_wf_t h_tbd h_lbs h_prb h_sms h_alloc h_psim h_pc
      output h_eval
  have h_mappedB : PlaceInputsMapped csA B := h_mapped
  obtain ⟨sOut0, h_sval0⟩ := placeToRegChecked_ok_of_placeInputsMapped
    (cs := csA) (kind := RefKind.Shared) h_mappedB
  obtain ⟨sOutP, h_svalP, h_regP, h_clP⟩ :=
    placeToRegChecked_proj_offset_value (kind := RefKind.Shared) spath h_np h_o
      h_sval0
  have h_prun := placeToRegChecked_proj_offset_run (kind := RefKind.Shared) spath
    h_np h_o h_sval0
  rw [h_rhs]
  simp only [readRhsPre, csMonad, csRun, h_svalP]
  refine ⟨fun d => Instr.RStore (layoutToTyVal τ) (Register.R
      (CheckedCompilerM.run
        (placeToRegChecked RefKind.Shared (Place.proj B spath)) csA).nextReg) d,
    _, rfl, fun _ => rfl, rfl,
    by rw [h_prun]; simp only [emit]; exact h_prmB csA, ?_⟩
  intro h_code
  rw [h_prun] at h_code
  obtain ⟨h_sclean, nR, sR, perms₂, vals, h_ost, h_vlen, h_runR, h_prmR,
    h_regmonoR, h_lbsR, h_psimR, h_tbdR, h_smem, h_pcR, h_vregR, h_vbelow,
    h_valsRel⟩ :=
    h_pkg' sOut0 h_sval0 sOutP h_regP h_clP
      (by
        refine h_code.mono ?_
        exact StateIncr.trans
          (StateIncr.trans (freshReg_state_incr _) (emit_state_incr _ _))
          (StateIncr.trans (freshReg_state_incr _) (emit_state_incr _ _)))
      h_code
  rw [h_prun, h_regP, h_clP]
  simp only [csCleanup, h_sclean, List.nil_append, List.append_nil,
    List.reverse_cons, List.map_cons, List.map_nil, List.cons_append]
  csnorm at h_vregR h_vbelow h_prmR h_regmonoR h_lbsR h_pcR ⊢
  have h_execR := StoreStep.rstore compProg sR _ (layoutToTyVal τ) _ vals
    h_vregR h_vbelow
  exact ⟨ρt, nR, sR, perms₂, vals, TagRenameIncr.refl ρt, h_wf_t, h_ost, h_vlen,
    h_runR, h_prmR, h_regmonoR, h_lbsR, h_psimR, h_tbdR, h_smem, h_pcR, h_execR,
    h_valsRel⟩

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





/-! ## FRESH destination with a PROJ-TOPPED source: the root `Alloc`,
    then the base lowering, then the projection's own shape. -/





/-! ## NON-LOCAL destination: the fragment composes TWO place lowerings.

`compileStmtChecked`'s general assign arm runs the rhs pre-phase (the
source lowering AND, since the temp-assignment lowering, the `Load` that
performs the read) BEFORE the destination lowering, then stores. With
both places cleanup-free the whole statement is
`[src code; Load; dst code; RStore]`. -/

/-! ## A PROJ-topped source under a chain destination: at zero offset
    the projection passes the base's register (and its cleanup) through,
    so the tower is the chain/chain one with `B` in the source slot. -/



/-! ## Chain destination with a PROJ-TOPPED source at NONZERO offset.
    The source tower is three instructions, not one: the projection's
    own `Borrow(Shared)` at `CS0.nextReg`, the copy's `Load` into
    `CS0.nextReg + 1`, and the projection's cleanup `Die`. The
    destination lowers only after that, so the `RStore` reads the
    loaded temporary. -/





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


/-! ## Fresh root under a PROJECTED LOCAL destination with a copy rhs.
    `ensurePlaceRoot` allocates the root BEFORE the rhs pre-phase runs,
    so the source lowering and the `Load` sit on top of the `Alloc`, and
    the destination lowering is the fresh root's own register. -/



/-! ## Fresh root under a PROJECTED LOCAL destination, with a
    PROJ-TOPPED source at NONZERO offset. The root `Alloc` comes first,
    then the source projection's `Borrow(Shared)`, the copy's `Load`,
    and the source projection's cleanup `Die`; only then does the
    destination lower. -/


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




/-! ## PROJECTED destination over a chain: the destination lowering adds
    a `Borrow(Mut)` and a cleanup `Die` around the same two-mother
    skeleton. Zero offset passes the register through. -/





/-! ## PROJECTED destination with a PROJ-TOPPED source at NONZERO
    offset. The source projection's `Borrow(Shared)`, the copy's
    `Load`, and the source projection's cleanup `Die` all sit in the rhs
    pre-phase; only then does the destination lower. At a zero
    destination offset the store goes straight through the base
    register, at a nonzero one through the destination projection's own
    `Borrow(Mut)`, killed after. -/










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
                    ((PtrChain.base srcLoc).placeToRegChecked_placeRegMap _)
                    (F.pkgLowered _ (PtrChain.base srcLoc).loweringSimAny))
                  h_comp h_inv h_stmt
                  (fun _ => rfl) (fun _ so h => ⟨so, h⟩)
                  h_envD h_step
              exact ⟨ρa, _, s_osea', n, AddrRenameIncr.refl ρa,
                h_incr_t, h_run, h_inv'⟩
          | none =>
              -- CLOSED: fresh destination, chain source (regime B for copy)
              exact storereg_localfresh_simulation compProg
                (ValuePkg.of_readPkgLowered compProg (F.shape _)
                  ((PtrChain.base srcLoc).placeToRegChecked_placeRegMap _)
                  (F.pkgLowered _ (PtrChain.base srcLoc).loweringSimAny))
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
              · obtain ⟨_, s_osea', n, h_incr_t, h_run, h_inv'⟩ :=
                  storereg_local_simulation compProg
                    (ValuePkg.of_readPkgLowered compProg (F.shape _)
                      (projZero_placeRegMap h_chain.not_proj h_off
                        (h_chain.placeToRegChecked_placeRegMap _))
                      (F.pkgLowered _
                        (LoweringSimAny.projZero h_chain.not_proj h_off
                          h_chain.loweringSimAny)))
                    h_comp h_inv h_stmt h_run0 h_val0 h_envD h_step
                exact ⟨ρa, _, s_osea', n, AddrRenameIncr.refl ρa,
                  h_incr_t, h_run, h_inv'⟩
              · obtain ⟨_, s_osea', n, h_incr_t, h_run, h_inv'⟩ :=
                  storereg_local_simulation compProg
                    (ValuePkg.of_readPkgProjOffset compProg (F.shape _)
                      h_chain.not_proj h_off
                      (h_chain.placeToRegChecked_placeRegMap _)
                      (F.pkgProjOffset _ _ h_chain.loweringSimAny
                        h_chain.not_proj h_off))
                    h_comp h_inv h_stmt h_run0 h_val0 h_envD h_step
                exact ⟨ρa, _, s_osea', n, AddrRenameIncr.refl ρa,
                  h_incr_t, h_run, h_inv'⟩
          | none =>
              -- CLOSED: fresh destination, proj-topped source (regime B)
              by_cases h_off : pathOffset path' = 0
              · exact storereg_localfresh_simulation compProg
                  (ValuePkg.of_readPkgLowered compProg (F.shape _)
                    (projZero_placeRegMap h_chain.not_proj h_off
                      (h_chain.placeToRegChecked_placeRegMap _))
                    (F.pkgLowered _
                      (LoweringSimAny.projZero h_chain.not_proj h_off
                        h_chain.loweringSimAny)))
                  h_comp h_inv h_stmt h_run0 h_val0 h_envD h_step
              · exact storereg_localfresh_simulation compProg
                  (ValuePkg.of_readPkgProjOffset compProg (F.shape _)
                    h_chain.not_proj h_off
                    (h_chain.placeToRegChecked_placeRegMap _)
                    (F.pkgProjOffset _ _ h_chain.loweringSimAny
                      h_chain.not_proj h_off))
                  h_comp h_inv h_stmt h_run0 h_val0 h_envD h_step
      | deref pp =>
          cases h_envD : mirlite.Env.lookup s_mir.env dstLoc with
          | some bD =>
              -- CLOSED: `dst := copy *chain` — flatten-normalized, TOTAL
              rw [F.stepFlat] at h_step
              obtain ⟨_, s_osea', n, h_incr_t, h_run, h_inv'⟩ :=
                storereg_local_simulation compProg
                  (ValuePkg.of_readPkgLowered compProg (F.shape _)
                    ((PtrChain_flatten_deref pp).placeToRegChecked_placeRegMap _)
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
              exact storereg_localfresh_simulation compProg
                (ValuePkg.of_readPkgLowered compProg (F.shape _)
                  ((PtrChain_flatten_deref pp).placeToRegChecked_placeRegMap _)
                  (F.pkgLowered _ (PtrChain_flatten_deref pp).loweringSimAny))
                h_comp h_inv h_stmt
                (fun cs => compileStmt_readrhs_derefsrc_flatten_run (h_shape := F.shape _) (h_shape2 := F.shape _) cs)
                (fun cs so h => compileStmt_readrhs_derefsrc_flatten_value (h_shape := F.shape _) (h_shape2 := F.shape _) cs so h)
                h_envD h_step
  | proj dbase dpath =>
      -- the recursion peels any nesting first; the source only has to
      -- SUPPLY the lowering package, which a chain does and a
      -- zero-offset projection over a chain does too
      rcases flatten_chainish src with h_sch | ⟨σs, B, spath, h_seq, h_B⟩
      · rw [F.stepFlat] at h_step
        exact storereg_projdst_recursion (base := dbase) (path := dpath) compProg
          (ValuePkg.of_readPkgLowered compProg (F.shape _)
            (h_sch.placeToRegChecked_placeRegMap _)
            (F.pkgLowered _ h_sch.loweringSimAny))
          h_comp h_inv h_stmt
          (fun cs => compileStmt_readrhs_projdst_srcflatten_run
            (h_shape := F.shape _) (h_shape2 := F.shape _) dbase dpath src cs)
          (fun cs so h => compileStmt_readrhs_projdst_srcflatten_value
            (h_shape := F.shape _) (h_shape2 := F.shape _) dbase dpath src cs
            ⟨so, h⟩)
          h_step
      · by_cases h_o : pathOffset spath = 0
        · rw [F.stepFlat] at h_step
          refine storereg_projdst_recursion (base := dbase) (path := dpath) compProg
            (ValuePkg.of_readPkgLowered compProg (F.shape _) ?_ ?_)
            h_comp h_inv h_stmt
            (fun cs => compileStmt_readrhs_projdst_srcflatten_run
              (h_shape := F.shape _) (h_shape2 := F.shape _) dbase dpath src cs)
            (fun cs so h => compileStmt_readrhs_projdst_srcflatten_value
              (h_shape := F.shape _) (h_shape2 := F.shape _) dbase dpath src cs
              ⟨so, h⟩)
            h_step
          · rw [h_seq]
            exact projZero_placeRegMap h_B.not_proj h_o
              (fun cs => h_B.placeToRegChecked_placeRegMap RefKind.Shared cs)
          · refine F.pkgLowered _ ?_
            rw [h_seq]
            exact LoweringSimAny.projZero h_B.not_proj h_o h_B.loweringSimAny
        · rw [F.stepFlat, h_seq] at h_step
          exact storereg_projdst_recursion (base := dbase) (path := dpath) compProg
            (ValuePkg.of_readPkgProjOffset compProg (F.shape _)
              h_B.not_proj h_o (h_B.placeToRegChecked_placeRegMap _)
              (F.pkgProjOffset _ _ h_B.loweringSimAny h_B.not_proj h_o))
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
        obtain ⟨_, s_osea', n, h_incr_t, h_run, h_inv'⟩ :=
          storereg_chaindst_simulation (P := flattenPlace pp) compProg
            (ValuePkg.of_readPkgLowered compProg (F.shape _)
              (h_sch.placeToRegChecked_placeRegMap _)
              (F.pkgLowered _ h_sch.loweringSimAny))
            (PtrChain_flatten_deref pp) h_comp h_inv h_stmt
            (copy_derefdst_flat_bridge pp src (F.shape _) (F.shape _) rfl).1
            (copy_derefdst_flat_bridge pp src (F.shape _) (F.shape _) rfl).2
            h_step
        exact ⟨ρa, _, s_osea', n, AddrRenameIncr.refl ρa, h_incr_t,
          h_run, h_inv'⟩
      · -- the flattened source is PROJ-topped over a chain
        by_cases h_o : pathOffset spath = 0
        · rw [stepStmt_assign_dstflatten, F.stepFlat] at h_step
          rw [show flattenPlace (Place.deref pp) = Place.deref (flattenPlace pp) from rfl,
            h_seq] at h_step
          obtain ⟨_, s_osea', n, h_incr_t, h_run, h_inv'⟩ :=
            storereg_chaindst_simulation (P := flattenPlace pp) compProg
              (ValuePkg.of_readPkgLowered compProg (F.shape _)
                (projZero_placeRegMap h_B.not_proj h_o
                  (h_B.placeToRegChecked_placeRegMap _))
                (F.pkgLowered _
                  (LoweringSimAny.projZero h_B.not_proj h_o h_B.loweringSimAny)))
              (PtrChain_flatten_deref pp)
              h_comp h_inv h_stmt
              (copy_derefdst_flat_bridge pp src (F.shape _) (F.shape _) h_seq).1
              (copy_derefdst_flat_bridge pp src (F.shape _) (F.shape _) h_seq).2
              h_step
          exact ⟨ρa, _, s_osea', n, AddrRenameIncr.refl ρa, h_incr_t,
            h_run, h_inv'⟩
        · rw [stepStmt_assign_dstflatten, F.stepFlat] at h_step
          rw [show flattenPlace (Place.deref pp) = Place.deref (flattenPlace pp) from rfl,
            h_seq] at h_step
          obtain ⟨_, s_osea', n, h_incr_t, h_run, h_inv'⟩ :=
            storereg_chaindst_simulation (P := flattenPlace pp) compProg
              (ValuePkg.of_readPkgProjOffset compProg (F.shape _)
                h_B.not_proj h_o (h_B.placeToRegChecked_placeRegMap _)
                (F.pkgProjOffset _ _ h_B.loweringSimAny h_B.not_proj h_o))
              (PtrChain_flatten_deref pp)
              h_comp h_inv h_stmt
              (copy_derefdst_flat_bridge pp src (F.shape _) (F.shape _) h_seq).1
              (copy_derefdst_flat_bridge pp src (F.shape _) (F.shape _) h_seq).2
              h_step
          exact ⟨ρa, _, s_osea', n, AddrRenameIncr.refl ρa, h_incr_t,
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
