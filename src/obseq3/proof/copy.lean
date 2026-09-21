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
    (rhs : RExpr Γ τ) (src : Place Γ τs) (mk : Register → Rhs)
    (post : Register → List Instr) : Prop :=
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
            ++ cleanupInstrs sOut0.result.cleanup ++ post (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg))).nextLabel →
        (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg + 1 }
          ([Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg) (mk sOut0.result.reg)]
            ++ cleanupInstrs sOut0.result.cleanup ++ post (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg))).code q = some instr →
        compProg q = some instr) →
      sOut0.result.cleanup = [] ∧
      ∃ (ρt' : TagRenameMap) (nR : Nat) (sR : oseair.State MSB)
        (perms₂ : MSB.State) (vals : List Val),
        TagRenameIncr ρt ρt' ∧
        TagRenameWF ρt' ∧
        output.state = { sM with perms := perms₂ } ∧
        vals.length = blockSize τ ∧
        oseair.runN MSB nR sA compProg = oseair.Result.Ok sR ∧
        (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg + 1 } ([Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg) (mk sOut0.result.reg)] ++ post (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg))).placeRegMap = csA.placeRegMap ∧
        csA.nextReg ≤ (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg + 1 } ([Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg) (mk sOut0.result.reg)] ++ post (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg))).nextReg ∧
        LocalBindingSim ρa ρt' sM.env sR (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg + 1 } ([Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg) (mk sOut0.result.reg)] ++ post (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg))) ∧
        PermSim ρt' perms₂ sR.perms ∧
        TagRenameBounded ρt' perms₂.NextTag sR.perms.NextTag ∧
        sR.mem = sA.mem ∧
        sR.pc = (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg + 1 } ([Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg) (mk sOut0.result.reg)] ++ post (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg))).nextLabel ∧
        oseair.RegMap.lookup sR.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg) = some (layoutToTyVal τ, vals) ∧
        RegisterBelow (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg + 1 } ([Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg) (mk sOut0.result.reg)] ++ post (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg))).nextReg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg) ∧
        ListRel (MemValSim ρa ρt') output.values vals

def ReadPkgProjOffset {Γ : Ctx} {τs σs τ : LayoutTy} (compProg : oseair.Prog)
    (rhs : RExpr Γ τ) (B : Place Γ σs) (spath : PathTo σs τs) (mk : Register → Rhs)
    (post : Register → List Instr) : Prop :=
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
          ++ cleanupInstrs sOutP.result.cleanup ++ post (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1)))) →
      sOut0.result.cleanup = [] ∧
      ∃ (ρt' : TagRenameMap) (nR : Nat) (sR : oseair.State MSB)
        (perms₂ : MSB.State) (vals : List Val),
        TagRenameIncr ρt ρt' ∧
        TagRenameWF ρt' ∧
        output.state = { sM with perms := perms₂ } ∧
        vals.length = blockSize τ ∧
        oseair.runN MSB nR sA compProg = oseair.Result.Ok sR ∧
        (emit { (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg) (borrowRhs RefKind.Shared (blockSize τs) sOut0.result.reg (pathOffset spath))]) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1 + 1 } ([Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1)) (mk (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)), Instr.Die (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg) (blockSize τs)] ++ post (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1)))).placeRegMap = csA.placeRegMap ∧
        csA.nextReg ≤ (emit { (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg) (borrowRhs RefKind.Shared (blockSize τs) sOut0.result.reg (pathOffset spath))]) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1 + 1 } ([Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1)) (mk (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)), Instr.Die (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg) (blockSize τs)] ++ post (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1)))).nextReg ∧
        LocalBindingSim ρa ρt' sM.env sR (emit { (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg) (borrowRhs RefKind.Shared (blockSize τs) sOut0.result.reg (pathOffset spath))]) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1 + 1 } ([Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1)) (mk (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)), Instr.Die (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg) (blockSize τs)] ++ post (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1)))) ∧
        PermSim ρt' perms₂ sR.perms ∧
        TagRenameBounded ρt' perms₂.NextTag sR.perms.NextTag ∧
        sR.mem = sA.mem ∧
        sR.pc = (emit { (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg) (borrowRhs RefKind.Shared (blockSize τs) sOut0.result.reg (pathOffset spath))]) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1 + 1 } ([Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1)) (mk (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)), Instr.Die (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg) (blockSize τs)] ++ post (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1)))).nextLabel ∧
        oseair.RegMap.lookup sR.reg (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1)) = some (layoutToTyVal τ, vals) ∧
        RegisterBelow (emit { (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg) (borrowRhs RefKind.Shared (blockSize τs) sOut0.result.reg (pathOffset spath))]) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1 + 1 } ([Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1)) (mk (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg)), Instr.Die (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg) (blockSize τs)] ++ post (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1)))).nextReg (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared B) csA).nextReg + 1)) ∧
        ListRel (MemValSim ρa ρt') output.values vals





/-! ## Flatten transfer for the copy-src shape -/

/-! ## Proj-topped sources over CHAIN bases: fragments over the opaque
    base lowering. `placeToRegChecked Shared (.proj B path)` runs B's
    code (the mother lemma owns it), then passes the register through
    at offset zero or mints a `Borrow(Shared)` otherwise; the statement
    adds the `Memcpy` and the cleanup `Die`. -/






/-! ## Flatten transfer for a copy source of ANY shape -/

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
    (h_init : (mirlite.readWordSeq sM.mem rs.addr (blockSize τ)).any
      (fun v => v == mirlite.MemValue.undef) = false)
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
    (by rw [h_ts, h_cancelS, h_smem]
        exact noUndef_transport (readWordSeq_sim h_id_a h_sms _ _) h_init)
  rw [h_ts, h_cancelS] at h_run1
  refine ⟨p2, oseair_runN_trans h_srun h_run1,
    (by grind [emit]),
    (by grind [emit]),
    ?_, h_psim2,
    (by rw [sb_read_NextTag h_read_src, sb_read_NextTag h_read_tgt, h_snt1]
        exact TagRenameBounded.mono h_tbd (Nat.le_refl _) h_snt2),
    h_smem, h_spc,
    (by rw [h_spc]; simp only [emit, List.append_nil, List.length_cons, List.length_nil]),
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
    (h_init : (mirlite.readWordSeq sM.mem (rs.addr + PathTo.offset spath) (blockSize τ)).any
      (fun v => v == mirlite.MemValue.undef) = false)
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
    (by rw [h_ts, ← Nat.add_assoc, h_cancelS]
        show (oseair.readWordSeq s_mid1.mem _ _).any _ = false
        rw [h_smem]
        exact noUndef_transport (readWordSeq_sim h_id_a h_sms _ _) h_init)
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
    (by rw [h_spc]; simp only [emit, List.append_nil, List.length_cons, List.length_nil]),
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
    {σ τ : LayoutTy} {rhs : RExpr Γ τ} {src : Place Γ σ} {mk : Register → Rhs} {post : Register → List Instr}
    (compProg : oseair.Prog)
    (h_shape : ReadRhsShape rhs src mk post)
    (h_prmS : ∀ cs, (CheckedCompilerM.run
      (placeToRegChecked RefKind.Shared src) cs).placeRegMap = cs.placeRegMap)
    (h_pkg : ReadPkgLowered compProg rhs src mk post) :
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
          ++ cleanupInstrs sOut0.result.cleanup
          ++ post (Register.R (CheckedCompilerM.run
            (placeToRegChecked RefKind.Shared src) csA).nextReg)) := by
    simp only [h_rhs, readRhsPre, csMonad, csRun, h_sval0]
  rw [h_rhs]
  simp only [readRhsPre, csMonad, csRun, h_sval0]
  refine ⟨fun d => Instr.RStore (layoutToTyVal τ) (Register.R
      (CheckedCompilerM.run (placeToRegChecked RefKind.Shared src) csA).nextReg) d,
    _, rfl, fun _ => rfl, rfl,
    by simp only [emit]; exact h_prmS csA, ?_⟩
  intro h_code
  obtain ⟨h_sclean, ρt', nR, sR, perms₂, vals, h_incrT, h_wfT, h_ost, h_vlen,
    h_runR, h_prmR, h_regmonoR, h_lbsR, h_psimR, h_tbdR, h_smem, h_pcR, h_vregR,
    h_vbelow, h_valsRel⟩ :=
    h_pkg' sOut0 h_sval0
      (h_code.mono (StateIncr.trans (freshReg_state_incr _) (emit_state_incr _ _)))
      h_code
  -- with the source cleanup empty the two spellings of the tower agree
  simp only [csCleanup, h_sclean, List.append_nil]
  have h_execR := StoreStep.rstore compProg sR _ (layoutToTyVal τ) _ vals
    h_vregR h_vbelow
  exact ⟨ρt', nR, sR, perms₂, vals, h_incrT, h_wfT, h_ost, h_vlen,
    h_runR, h_prmR, h_regmonoR, h_lbsR, h_psimR, h_tbdR, h_smem, h_pcR, h_execR,
    h_valsRel⟩

/-- copy's chain-class read package, as an instance of the generic one. -/
theorem copy_readpkg_lowered {τ : LayoutTy} {src : Place Γ τ}
    (compProg : oseair.Prog) (h_slower : LoweringSimAny compProg src) :
    ReadPkgLowered compProg (.copy src) src (Rhs.Load (layoutToTyVal τ)) (fun _ => []) := by
  intro ρa ρt sM sA csA h_id_a h_wf_t h_tbd h_lbs h_prb h_sms h_alloc h_psim h_pc
    output h_eval
  simp only [mirlite.evalRExpr, mirlite.evalCopy] at h_eval
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
    simp only at h_eval
    split at h_eval
    · simp at h_eval
    rename_i h_init0
    have h_init : (mirlite.readWordSeq sM.mem rs.addr (blockSize τ)).any
        (fun v => v == mirlite.MemValue.undef) = false := by simpa using h_init0
    injection h_eval with h_out
    subst h_out
    refine ⟨placeInputsMapped_of_localBindingSim_resolvePlace h_lbs
        (resolvePlace?_of_resolveAcc h_sres), ?_⟩
    intro sOut0 h_sval0 h_instS h_instD
    simp only [List.append_nil] at h_instD
    obtain ⟨h_sclean, n1, s_mid1, p2, h_runR, h_prmR, h_regmonoR, h_lbsR, h_psimR,
      h_tbdR, h_smem, h_spc, h_pcR, h_vbelow, h_rel⟩ :=
      copy_chainsrc_read compProg h_slower sM sA csA h_id_a h_wf_t h_tbd h_lbs h_prb
        h_sms h_psim h_pc h_sres h_fit h_read_src h_init h_sval0 h_instS h_instD
    exact ⟨h_sclean, ρt, n1 + 1, _, perms₂, _, TagRenameIncr.refl ρt, h_wf_t, rfl,
      (by rw [oseair_readWordSeq_length]),
      h_runR, h_prmR, h_regmonoR, h_lbsR, h_psimR, h_tbdR, h_smem, h_pcR,
      RegMap.lookup_insert_self _ _ _, h_vbelow, h_rel⟩

/-- Every projected-source read package is a value package too: the
    projection's `Borrow`, the rvalue's instruction and the `Die` that
    retires the borrow all live inside `compileRExprPreChecked rhs`, so
    the single code-inclusion obligation covers all three. -/
theorem ValuePkg.of_readPkgProjOffset
    {σs τs τ : LayoutTy} {rhs : RExpr Γ τ} {B : Place Γ σs} {spath : PathTo σs τs}
    {mk : Register → Rhs} {post : Register → List Instr}
    (compProg : oseair.Prog)
    (h_shape : ReadRhsShape rhs (.proj B spath) mk post)
    (h_np : ∀ (σ' : LayoutTy) (b : Place Γ σ') (q : PathTo σ' σs),
      B = b.proj q → False)
    (h_o : pathOffset spath ≠ 0)
    (h_prmB : ∀ cs, (CheckedCompilerM.run
      (placeToRegChecked RefKind.Shared B) cs).placeRegMap = cs.placeRegMap)
    (h_pkg : ReadPkgProjOffset compProg rhs B spath mk post) :
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
  obtain ⟨h_sclean, ρt', nR, sR, perms₂, vals, h_incrT, h_wfT, h_ost, h_vlen,
    h_runR, h_prmR, h_regmonoR, h_lbsR, h_psimR, h_tbdR, h_smem, h_pcR, h_vregR,
    h_vbelow, h_valsRel⟩ :=
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
  exact ⟨ρt', nR, sR, perms₂, vals, h_incrT, h_wfT, h_ost, h_vlen,
    h_runR, h_prmR, h_regmonoR, h_lbsR, h_psimR, h_tbdR, h_smem, h_pcR, h_execR,
    h_valsRel⟩

/-! ## The read package with its REGISTER exposed

`ValuePkg` hides the register the rvalue leaves its value in, behind
`StoreStep` — a destination leaf only stores it. A GUARD reads it: the
`SkipIf` compares the loaded discriminant. `ReadRegPkg` is the same
package with `lookup sR.reg tmp = some (ty, vals)` in the conclusion,
where `tmp` is the register the read-then-store lowering allocates, and
its two constructors are `ValuePkg`'s minus the final `StoreStep`. -/
def ReadRegPkg {Γ : Ctx} {σ τ : LayoutTy} (compProg : oseair.Prog)
    (rhs : RExpr Γ τ) (src : Place Γ σ) : Prop :=
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
      ∃ (pOut : RhsPre Γ τ rhs),
      CheckedCompilerM.value (compileRExprPreChecked rhs) csA = Except.ok pOut ∧
      (CheckedCompilerM.run (compileRExprPreChecked rhs) csA).placeRegMap
        = csA.placeRegMap ∧
      (CodeIncluded compProg (CheckedCompilerM.run (compileRExprPreChecked rhs) csA) →
        ∃ (ρt' : TagRenameMap) (nR : Nat) (sR : oseair.State MSB)
          (perms₂ : MSB.State) (vals : List Val),
          TagRenameIncr ρt ρt' ∧
          TagRenameWF ρt' ∧
          output.state = { sM with perms := perms₂ } ∧
          vals.length = blockSize τ ∧
          oseair.runN MSB nR sA compProg = oseair.Result.Ok sR ∧
          csA.nextReg
            ≤ (CheckedCompilerM.run (compileRExprPreChecked rhs) csA).nextReg ∧
          LocalBindingSim ρa ρt' sM.env sR
            (CheckedCompilerM.run (compileRExprPreChecked rhs) csA) ∧
          PermSim ρt' perms₂ sR.perms ∧
          TagRenameBounded ρt' perms₂.NextTag sR.perms.NextTag ∧
          sR.mem = sA.mem ∧
          sR.pc = (CheckedCompilerM.run (compileRExprPreChecked rhs) csA).nextLabel ∧
          oseair.RegMap.lookup sR.reg (Register.R (CheckedCompilerM.run
            (placeToRegChecked RefKind.Shared src) csA).nextReg)
            = some (layoutToTyVal τ, vals) ∧
          ListRel (MemValSim ρa ρt') output.values vals)

theorem ReadRegPkg.of_readPkgLowered
    {σ τ : LayoutTy} {rhs : RExpr Γ τ} {src : Place Γ σ} {mk : Register → Rhs} {post : Register → List Instr}
    (compProg : oseair.Prog)
    (h_shape : ReadRhsShape rhs src mk post)
    (h_prmS : ∀ cs, (CheckedCompilerM.run
      (placeToRegChecked RefKind.Shared src) cs).placeRegMap = cs.placeRegMap)
    (h_pkg : ReadPkgLowered compProg rhs src mk post) :
    ReadRegPkg compProg rhs src := by
  intro ρa ρt sM sA csA h_id_a h_wf_t h_tbd h_lbs h_prb h_sms h_alloc h_psim h_pc
    output h_eval
  obtain ⟨ev, h_rhs⟩ := id h_shape
  obtain ⟨h_mapped, h_pkg'⟩ :=
    h_pkg ρa ρt sM sA csA h_id_a h_wf_t h_tbd h_lbs h_prb h_sms h_alloc h_psim h_pc
      output h_eval
  obtain ⟨sOut0, h_sval0⟩ := placeToRegChecked_ok_of_placeInputsMapped
    (cs := csA) (kind := RefKind.Shared) h_mapped
  rw [h_rhs]
  simp only [readRhsPre, csMonad, csRun, h_sval0]
  refine ⟨_, rfl, by simp only [emit]; exact h_prmS csA, ?_⟩
  intro h_code
  obtain ⟨h_sclean, ρt', nR, sR, perms₂, vals, h_incrT, h_wfT, h_ost, h_vlen,
    h_runR, h_prmR, h_regmonoR, h_lbsR, h_psimR, h_tbdR, h_smem, h_pcR, h_vregR,
    h_vbelow, h_valsRel⟩ :=
    h_pkg' sOut0 h_sval0
      (h_code.mono (StateIncr.trans (freshReg_state_incr _) (emit_state_incr _ _)))
      h_code
  simp only [csCleanup, h_sclean, List.append_nil]
  exact ⟨ρt', nR, sR, perms₂, vals, h_incrT, h_wfT, h_ost, h_vlen,
    h_runR, h_regmonoR, h_lbsR, h_psimR, h_tbdR, h_smem, h_pcR, h_vregR, h_valsRel⟩

theorem ReadRegPkg.of_readPkgProjOffset
    {σs τs τ : LayoutTy} {rhs : RExpr Γ τ} {B : Place Γ σs} {spath : PathTo σs τs}
    {mk : Register → Rhs} {post : Register → List Instr}
    (compProg : oseair.Prog)
    (h_shape : ReadRhsShape rhs (.proj B spath) mk post)
    (h_np : ∀ (σ' : LayoutTy) (b : Place Γ σ') (q : PathTo σ' σs),
      B = b.proj q → False)
    (h_o : pathOffset spath ≠ 0)
    (h_prmB : ∀ cs, (CheckedCompilerM.run
      (placeToRegChecked RefKind.Shared B) cs).placeRegMap = cs.placeRegMap)
    (h_pkg : ReadPkgProjOffset compProg rhs B spath mk post) :
    ReadRegPkg compProg rhs (.proj B spath) := by
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
  refine ⟨_, rfl, by rw [h_prun]; simp only [emit]; exact h_prmB csA, ?_⟩
  intro h_code
  rw [h_prun] at h_code
  obtain ⟨h_sclean, ρt', nR, sR, perms₂, vals, h_incrT, h_wfT, h_ost, h_vlen,
    h_runR, h_prmR, h_regmonoR, h_lbsR, h_psimR, h_tbdR, h_smem, h_pcR, h_vregR,
    h_vbelow, h_valsRel⟩ :=
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
  exact ⟨ρt', nR, sR, perms₂, vals, h_incrT, h_wfT, h_ost, h_vlen,
    h_runR, h_regmonoR, h_lbsR, h_psimR, h_tbdR, h_smem, h_pcR, h_vregR, h_valsRel⟩

/-- copy's projected-source read package, as an instance of the generic one. -/
theorem copy_readpkg_projoffset {τ σs : LayoutTy} {B : Place Γ σs} {spath : PathTo σs τ}
    (compProg : oseair.Prog) (h_slower : LoweringSimAny compProg B) :
    ReadPkgProjOffset compProg (.copy (.proj B spath)) B spath (Rhs.Load (layoutToTyVal τ)) (fun _ => []) := by
  intro ρa ρt sM sA csA h_id_a h_wf_t h_tbd h_lbs h_prb h_sms h_alloc h_psim h_pc
    output h_eval
  simp only [mirlite.evalRExpr, mirlite.evalCopy] at h_eval
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
    simp only at h_eval
    split at h_eval
    · simp at h_eval
    rename_i h_init0
    have h_init : (mirlite.readWordSeq sM.mem (rs.addr + PathTo.offset spath) (blockSize τ)).any
        (fun v => v == mirlite.MemValue.undef) = false := by simpa using h_init0
    injection h_eval with h_out
    subst h_out
    refine ⟨placeInputsMapped_of_localBindingSim_resolvePlace h_lbs
        (resolvePlace?_of_resolveAcc (resolvePlaceAcc_proj_base_ok (path := spath) h_sres)), ?_⟩
    intro sOut0 h_sval0 sOutP h_regP h_clP h_instS h_instCS
    simp only [List.append_nil] at h_instCS
    obtain ⟨h_sclean, n1, s_mid1, q3, h_runR, h_prmR, h_regmonoR, h_lbsR, h_psimR,
      h_tbdR, h_smem, h_spc, h_pcR, h_vbelow, h_rel⟩ :=
      copy_projsrc_offset_read compProg h_slower sM sA csA h_id_a h_wf_t h_tbd
        h_lbs h_prb h_sms h_psim h_pc h_sres h_fit h_read_src h_init h_sval0 h_regP h_clP
        h_instS h_instCS
    exact ⟨h_sclean, ρt, n1, _, perms₂, _, TagRenameIncr.refl ρt, h_wf_t, rfl,
      (by rw [oseair_readWordSeq_length]),
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










/-- `copy` of ANY place, flattened, as a register-exposing read package:
    the chain / zero-offset / nonzero-offset split the read-then-store
    dispatcher performs, done once. This is the discriminant read of
    `assignIf`. -/
theorem copy_readRegPkg_flat {τ : LayoutTy} (compProg : oseair.Prog)
    (src : Place Γ τ) :
    ReadRegPkg compProg (RExpr.copy (flattenPlace src)) (flattenPlace src) := by
  rcases flatten_chainish src with h_ch | ⟨σs, B, spath, h_seq, h_B⟩
  · exact ReadRegPkg.of_readPkgLowered compProg (readRhsShape_copy _)
      (h_ch.placeToRegChecked_placeRegMap _)
      (copy_readpkg_lowered compProg h_ch.loweringSimAny)
  · rw [h_seq]
    by_cases h_o : pathOffset spath = 0
    · exact ReadRegPkg.of_readPkgLowered compProg (readRhsShape_copy _)
        (projZero_placeRegMap h_B.not_proj h_o
          (fun cs => h_B.placeToRegChecked_placeRegMap RefKind.Shared cs))
        (copy_readpkg_lowered compProg
          (LoweringSimAny.projZero h_B.not_proj h_o h_B.loweringSimAny))
    · exact ReadRegPkg.of_readPkgProjOffset compProg (readRhsShape_copy _)
        h_B.not_proj h_o (h_B.placeToRegChecked_placeRegMap _)
        (copy_readpkg_projoffset compProg h_B.loweringSimAny)

/-- Everything a read-then-store rvalue must supply for the generic
    per-statement dispatcher: the compiled shape at every source place,
    that flattening the source does not change the mirlite step, and the
    two read packages (chain-class sources and projected sources at a
    nonzero offset). `copy`, `exposeAddr` and `fromExposed` differ only
    in these four fields. -/
structure ReadRhsFamily {Γ : Ctx} {σ τ : LayoutTy} (compProg : oseair.Prog)
    (rhsOf : Place Γ σ → RExpr Γ τ) (mk : Register → Rhs)
    (post : Register → List Instr) : Prop where
  shape : ∀ src, ReadRhsShape (rhsOf src) src mk post
  stepFlat : ∀ (s : mirlite.State MSB Γ) (dst : Place Γ τ) (src : Place Γ σ),
    mirlite.stepStmt MSB s (.assign dst (rhsOf src))
      = mirlite.stepStmt MSB s (.assign dst (rhsOf (flattenPlace src)))
  pkgLowered : ∀ (src : Place Γ σ), LoweringSimAny compProg src →
    ReadPkgLowered compProg (rhsOf src) src mk post
  pkgProjOffset : ∀ {σs : LayoutTy} (B : Place Γ σs) (spath : PathTo σs σ),
    LoweringSimAny compProg B →
    (∀ (σ' : LayoutTy) (b : Place Γ σ') (q : PathTo σ' σs), B = b.proj q → False) →
    pathOffset spath ≠ 0 →
    ReadPkgProjOffset compProg (rhsOf (.proj B spath)) B spath mk post

/-- A read-then-store pre-phase sees its source only through the shared
    place lowering, which agrees under flattening: the two shapes give the
    same run, store and post-cleanup. Stated at any `X` the flattened
    source is known to equal, so a caller never rewrites under the
    evidence-indexed binders. -/
theorem readRhsShape_flatten_pre {σ τ : LayoutTy} {rhs rhs2 : RExpr Γ τ} {src X : Place Γ σ}
    {mk : Register → Rhs} {post : Register → List Instr}
    (h1 : ReadRhsShape rhs src mk post) (hX : flattenPlace src = X)
    (h2 : ReadRhsShape rhs2 X mk post) (cs : CompilerState) :
    CheckedCompilerM.run (compileRExprPreChecked rhs) cs
      = CheckedCompilerM.run (compileRExprPreChecked rhs2) cs ∧
    (CheckedCompilerM.value (compileRExprPreChecked rhs) cs).map
        (fun p => (p.store, p.postCleanup))
      = (CheckedCompilerM.value (compileRExprPreChecked rhs2) cs).map
        (fun p => (p.store, p.postCleanup)) := by
  subst hX
  obtain ⟨ev1, e1⟩ := h1
  obtain ⟨ev2, e2⟩ := h2
  obtain ⟨h_agr, h_agv⟩ := placeToRegChecked_flatten_agree src RefKind.Shared cs
  rw [e1, e2]
  simp only [readRhsPre, csMonad]
  rcases exceptMap_agree h_agv with ⟨eF, eO, hF, hO⟩ | ⟨oF, oO, hF, hO, h_res⟩
  · have h_e : eF = eO := by
      rw [hF, hO] at h_agv
      simpa [Except.map] using h_agv
    subst h_e
    simp only [hF, hO]
    exact ⟨h_agr.symm, rfl⟩
  · constructor
    · simp only [hF, hO, h_res, h_agr]
    · simp only [hF, hO, h_res, h_agr, Except.map]

/-- LEAF SORRY 2 → DISPATCHER 2026-08-28: per-statement simulation for
    `.assign dst (.copy src)`, decomposed by the shapes of the two
    places. Regime L→L (both bound locals, any layout) is CLOSED by
    `copy_local_local_simulation`; the residual shapes are named. -/
theorem assignStep_readrhs
    {σ τ : LayoutTy}
    {dst : Place Γ τ} {src : Place Γ σ}
    {rhsOf : Place Γ σ → RExpr Γ τ} {mk : Register → Rhs} {post : Register → List Instr}
    (compProg : oseair.Prog)
    (F : ReadRhsFamily compProg rhsOf mk post)
    {csStart : CompilerState}
    (h_invAt : InvAt ρa ρt s_mir s_osea csStart)
    (hF : (∃ so, CheckedCompilerM.value
        (compileStmtChecked (.assign dst (rhsOf src))) csStart = Except.ok so) →
      StmtFrame compProg cs0 prog s_mir.pc
        (CheckedCompilerM.run (compileStmtChecked (.assign dst (rhsOf src))) csStart))
    (h_step : mirlite.stepStmt MSB s_mir (.assign dst (rhsOf src)) = .ok s_mir') :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' := by
  -- one congruence for every destination and every normal form of the source
  have h_cong : ∀ {X : Place Γ σ} (hX : flattenPlace src = X) (d : Place Γ τ),
      (∀ cs, CheckedCompilerM.run (compileStmtChecked (.assign d (rhsOf src))) cs
        = CheckedCompilerM.run (compileStmtChecked (.assign d (rhsOf X))) cs) ∧
      (∀ cs so, CheckedCompilerM.value (compileStmtChecked (.assign d (rhsOf X))) cs
          = Except.ok so →
        ∃ so', CheckedCompilerM.value (compileStmtChecked (.assign d (rhsOf src))) cs
          = Except.ok so') :=
    fun {X} hX d => compileAssignChecked_congr_pre d (rhsOf src) (rhsOf X)
      (fun cs => (readRhsShape_flatten_pre (F.shape src) hX (F.shape X) cs).1)
      (fun cs => (readRhsShape_flatten_pre (F.shape src) hX (F.shape X) cs).2)
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
                  h_invAt (StmtFrame.congr hF
                  (fun _ => rfl) (fun _ so h => ⟨so, h⟩))
                  h_envD h_step
              exact ⟨ρa, _, s_osea', n, AddrRenameIncr.refl ρa,
                h_incr_t, h_run, h_inv'⟩
          | none =>
              -- CLOSED: fresh destination, chain source (regime B for copy)
              exact storereg_localfresh_simulation compProg
                (ValuePkg.of_readPkgLowered compProg (F.shape _)
                  ((PtrChain.base srcLoc).placeToRegChecked_placeRegMap _)
                  (F.pkgLowered _ (PtrChain.base srcLoc).loweringSimAny))
                h_invAt (StmtFrame.congr hF
                (fun _ => rfl) (fun _ so h => ⟨so, h⟩)) h_envD h_step
      | proj sbase ff =>
          -- FLATTEN the whole src BEFORE the destination split: its normal
          -- form is ONE projection over a canonical chain, and both env
          -- cases hand that same normal form to their collapsed leaves
          obtain ⟨σ', Bc, path', h_flat, h_chain⟩ := flatten_proj_chainish sbase ff
          rw [F.stepFlat, h_flat] at h_step
          obtain ⟨h_run0, h_val0⟩ := h_cong h_flat (.local dstLoc)
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
                    h_invAt (StmtFrame.congr hF h_run0 h_val0) h_envD h_step
                exact ⟨ρa, _, s_osea', n, AddrRenameIncr.refl ρa,
                  h_incr_t, h_run, h_inv'⟩
              · obtain ⟨_, s_osea', n, h_incr_t, h_run, h_inv'⟩ :=
                  storereg_local_simulation compProg
                    (ValuePkg.of_readPkgProjOffset compProg (F.shape _)
                      h_chain.not_proj h_off
                      (h_chain.placeToRegChecked_placeRegMap _)
                      (F.pkgProjOffset _ _ h_chain.loweringSimAny
                        h_chain.not_proj h_off))
                    h_invAt (StmtFrame.congr hF h_run0 h_val0) h_envD h_step
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
                  h_invAt (StmtFrame.congr hF h_run0 h_val0) h_envD h_step
              · exact storereg_localfresh_simulation compProg
                  (ValuePkg.of_readPkgProjOffset compProg (F.shape _)
                    h_chain.not_proj h_off
                    (h_chain.placeToRegChecked_placeRegMap _)
                    (F.pkgProjOffset _ _ h_chain.loweringSimAny
                      h_chain.not_proj h_off))
                  h_invAt (StmtFrame.congr hF h_run0 h_val0) h_envD h_step
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
                  h_invAt (StmtFrame.congr hF (h_cong rfl _).1 (h_cong rfl _).2)
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
                h_invAt (StmtFrame.congr hF (h_cong rfl _).1 (h_cong rfl _).2)
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
          h_invAt (StmtFrame.congr hF (h_cong rfl _).1 (h_cong rfl _).2)
          h_step
      · by_cases h_o : pathOffset spath = 0
        · rw [F.stepFlat] at h_step
          refine storereg_projdst_recursion (base := dbase) (path := dpath) compProg
            (ValuePkg.of_readPkgLowered compProg (F.shape _) ?_ ?_)
            h_invAt (StmtFrame.congr hF (h_cong rfl _).1 (h_cong rfl _).2)
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
            h_invAt (StmtFrame.congr hF (h_cong h_seq _).1 (h_cong h_seq _).2)
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
            (PtrChain_flatten_deref pp) h_invAt (StmtFrame.congr hF
            (fun cs => ((h_cong rfl _).1 cs).trans
              (compileStmt_assign_derefdst_flatten_run _ cs))
            (fun cs so h => by
              obtain ⟨so1, h1⟩ := compileStmt_assign_derefdst_flatten_value _ cs so h
              exact (h_cong rfl _).2 cs so1 h1))
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
              h_invAt (StmtFrame.congr hF
              (fun cs => ((h_cong h_seq _).1 cs).trans
                (compileStmt_assign_derefdst_flatten_run _ cs))
              (fun cs so h => by
                obtain ⟨so1, h1⟩ := compileStmt_assign_derefdst_flatten_value _ cs so h
                exact (h_cong h_seq _).2 cs so1 h1))
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
              h_invAt (StmtFrame.congr hF
              (fun cs => ((h_cong h_seq _).1 cs).trans
                (compileStmt_assign_derefdst_flatten_run _ cs))
              (fun cs so h => by
                obtain ⟨so1, h1⟩ := compileStmt_assign_derefdst_flatten_value _ cs so h
                exact (h_cong h_seq _).2 cs so1 h1))
              h_step
          exact ⟨ρa, _, s_osea', n, AddrRenameIncr.refl ρa, h_incr_t,
            h_run, h_inv'⟩

/-- `copy` is a read-then-store family: its source place carries its own
    layout, and the instruction it emits is the `Load`. -/

theorem CompilerInv_step_readrhs
    {σ τ : LayoutTy}
    {dst : Place Γ τ} {src : Place Γ σ}
    {rhsOf : Place Γ σ → RExpr Γ τ} {mk : Register → Rhs} {post : Register → List Instr}
    (compProg : oseair.Prog)
    (F : ReadRhsFamily compProg rhsOf mk post)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    (h_stmt : prog.get? s_mir.pc = some (.assign dst (rhsOf src)))
    (h_step : mirlite.stepStmt MSB s_mir (.assign dst (rhsOf src)) = .ok s_mir') :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' := by
  obtain ⟨csPrefix, h_csAt, h_invAt⟩ := h_inv.invAt
  exact assignStep_readrhs compProg F h_invAt
    (StmtFrame.ofAssign h_comp h_csAt h_stmt (fun _ => rfl) (fun _ so h => ⟨so, h⟩))
    h_step

theorem copy_readRhsFamily {Γ : Ctx} {τ : LayoutTy} (compProg : oseair.Prog) :
    ReadRhsFamily (Γ := Γ) compProg (fun src => RExpr.copy (τ := τ) src)
      (Rhs.Load (layoutToTyVal τ)) (fun _ => []) where
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
