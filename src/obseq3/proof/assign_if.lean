import obseq3.proof.const_write
import obseq3.proof.copy
import obseq3.proof.ref
import obseq3.proof.casts
import obseq3.proof.ptrarith
import obseq3.proof.protectors
import obseq3.proof.alloc
import obseq3.proof.binop
import obseq3.proof.slice

/-! # `assignIf`: a guarded assign

`assignIf discr val dst rhs` is, on both machines, three things in a
row (2026-09-17):

1. the destination's ROOT LOCAL is allocated if it is still unbound
   (mirlite `ensureRoot`, compiler `ensurePlaceRoot`) — on BOTH paths,
   so the two allocators stay in lockstep whether or not the guard is
   taken;
2. the discriminant is READ, exactly as `copy` reads an integer (`IntL`) place;
3. the loaded word is compared with `val`: equal, and the assign runs
   from the post-read state; unequal, and the statement is over.

The compiled shape is `[root Alloc]; <copy's read>; SkipIf r val n;
<the assign>`, with `n` the assign's length. So the arm's proof is the
root step (below), copy's read package with its register exposed
(`ReadRegPkg`, proof/copy.lean), one `SkipIf` step, and then either the
plain assign leaf at the state the guard falls through to — which is why
the leaves take an `InvAt` at their own start state and a statement
FRAME rather than the prefix bundle — or, on the skip, the invariant
rebuilt directly at the statement's end, where the one fact needed is
that the never-executed body changed no `placeRegMap` entry: exactly the
fact the pre-fix lowering violated. -/

namespace obseq3.proof

variable {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
variable {ρa : AddrRenameMap} {ρt : TagRenameMap}
variable {s_mir s_mir' : mirlite.State MSB Γ}
variable {s_osea : oseair.State MSB}

open obseq3
open obseq3.compile
open obseq3.oseair (Instr Register Rhs Val)

/-! ## Machine steps -/

/-- `SkipIf` on an EQUAL discriminant falls through: `pc + 1`, nothing
    else touched. -/
theorem runN_SkipIf_fallthrough_step (compProg : oseair.Prog) (s : oseair.State MSB)
    {discr : Register} {val : Word} {skip : Nat} {ty : obseq.TyVal}
    (h_instr : compProg s.pc = some (Instr.SkipIf discr val skip))
    (h_reg : oseair.RegMap.lookup s.reg discr = some (ty, [Val.Dat val])) :
    oseair.runN MSB 1 s compProg = oseair.Result.Ok { s with pc := s.pc + 1 } := by
  have h_step : oseair.step MSB s compProg
      = oseair.Result.Ok { s with pc := s.pc + 1 } := by
    simp only [oseair.step, oseair.stepWith, h_instr, h_reg]
    simp
  simp [oseair.runN_succ, oseair.runN_zero, h_step]

/-- `SkipIf` on an UNEQUAL discriminant jumps over the guarded block. -/
theorem runN_SkipIf_jump_step (compProg : oseair.Prog) (s : oseair.State MSB)
    {discr : Register} {val v : Word} {skip : Nat} {ty : obseq.TyVal}
    (h_instr : compProg s.pc = some (Instr.SkipIf discr val skip))
    (h_reg : oseair.RegMap.lookup s.reg discr = some (ty, [Val.Dat v]))
    (h_ne : v ≠ val) :
    oseair.runN MSB 1 s compProg
      = oseair.Result.Ok { s with pc := s.pc + 1 + skip } := by
  have h_step : oseair.step MSB s compProg
      = oseair.Result.Ok { s with pc := s.pc + 1 + skip } := by
    simp only [oseair.step, oseair.stepWith, h_instr, h_reg]
    simp [h_ne]
  simp [oseair.runN_succ, oseair.runN_zero, h_step]

/-- A guarded body whose destination root is ALREADY mapped keeps the
    place map: its own `ensurePlaceRoot` is silent, and nothing else
    writes it. -/
theorem compileAssignChecked_placeRegMap_of_mapped {τ : LayoutTy}
    (dst : Place Γ τ) (rhs : RExpr Γ τ) {cs : CompilerState}
    (h_mapped : PlaceInputsMapped cs dst) :
    (CheckedCompilerM.run (compileAssignChecked dst rhs) cs).placeRegMap
      = cs.placeRegMap := by
  simp only [compileAssignChecked, csMonad]
  rw [ensurePlaceRoot_run_eq_of_mapped h_mapped]
  have h1 := compileRExprPreChecked_placeRegMap_any rhs cs
  split
  · have h2 := placeToRegChecked_placeRegMap_any dst RefKind.Mut
      (CheckedCompilerM.run (compileRExprPreChecked rhs) cs)
    split
    · simp [csMonad, csRun, emit_placeRegMap, h2, h1]
    · rw [h2, h1]
  · exact h1

/-! ## The root step

`ensureRoot` (mirlite) and `ensurePlaceRoot` (compiler) are the same
recursion to the place's root local. A bound root: neither machine
moves. An unbound root: mirlite's `allocateBase` against the target's
`Alloc`, which is the first half of the fresh-local leaf
(`copy_freshroot_prologue`), and the invariant holds again at the
state `ensureLocalRegE` leaves behind. -/
theorem ensureRoot_simulation {τ : LayoutTy} (dst : Place Γ τ) (compProg : oseair.Prog)
    {cs : CompilerState} {s0 : mirlite.State MSB Γ}
    (h_inv : InvAt ρa ρt s_mir s_osea cs)
    (h_code : CodeIncluded compProg (CompilerM.run (ensurePlaceRoot dst) cs))
    (h_root : mirlite.ensureRoot MSB s_mir dst = .ok s0) :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (sA : oseair.State MSB) (n : Nat),
      AddrRenameIncr ρa ρa' ∧ TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok sA ∧
      s0.pc = s_mir.pc ∧
      InvAt ρa' ρt' s0 sA (CompilerM.run (ensurePlaceRoot dst) cs) := by
  induction dst with
  | proj base path ih => exact ih h_code h_root
  | deref pp ih => exact ih h_code h_root
  | «local» loc =>
    rename_i τ'
    obtain ⟨h_pc, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_tbd, h_alloc, h_unmap, h_prb⟩ :=
      h_inv
    cases h_env : mirlite.Env.lookup s_mir.env loc with
    | some b =>
        have h_s0 : s0 = s_mir := by
          simp only [mirlite.ensureRoot, h_env] at h_root
          cases h_root; rfl
        subst h_s0
        obtain ⟨reg, base, tag, h_pi, -⟩ := h_lbs loc b h_env
        have h_run : CompilerM.run (ensurePlaceRoot (Place.local loc)) cs = cs :=
          ensurePlaceRoot_run_eq_of_mapped ⟨reg, τ', h_pi⟩
        rw [h_run]
        exact ⟨ρa, ρt, s_osea, 0, AddrRenameIncr.refl ρa, TagRenameIncr.refl ρt,
          by simp [oseair.runN], rfl,
          ⟨h_pc, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_tbd, h_alloc, h_unmap, h_prb⟩⟩
    | none =>
        have h_prep : mirlite.allocateBase MSB s_mir loc = .ok s0 := by
          simpa only [mirlite.ensureRoot, h_env] using h_root
        have h_pi_none : getPlaceInfo cs loc.idx.1 = none := h_unmap loc h_env
        have h_incr_a :=
          AddrRenameIncr.extendBlock h_id_a s_mir.mem.addrStart (blockSize τ')
        have h_id_a' :=
          IdentityOnDomain.extendBlock h_id_a s_mir.mem.addrStart (blockSize τ')
        have h_ra_dom : ∀ k, k < blockSize τ' →
            (ρa.extendBlock s_mir.mem.addrStart (blockSize τ'))
              (s_mir.mem.addrStart + k) = some (s_mir.mem.addrStart + k) :=
          fun _ hk => AddrRenameMap.extendBlock_mem hk
        obtain ⟨permsOwned, tgtPerms, h_own_tgt', h_perms1, h_pc1, h_env1,
          h_lookup_set, h_memstart1, h_allocs1, h_find1, h_incr_t, h_wf_t', h_tbd',
          h_psim', h_erun, h_prb1, h_lbs1⟩ :=
          copy_freshroot_prologue h_env h_prep h_wf_t h_tbd h_psim h_alloc
            h_lbs h_prb h_pi_none h_incr_a (AddrRenameMap.extendBlock_base _ _ _)
            h_ra_dom
        have h_sz : obseq.typeSize (layoutToTyVal τ') = blockSize τ' :=
          typeSize_layoutToTyVal _
        have h_run : CompilerM.run (ensurePlaceRoot (Place.local loc)) cs
            = freshRootCS cs loc := by
          simp only [ensurePlaceRoot, CompilerM.run_bind]
          rw [h_erun]
          rfl
        rw [h_run] at h_code ⊢
        have h_code0 : compProg s_osea.pc
            = some (Instr.Assgn (Register.R cs.nextReg)
                (Rhs.Alloc (layoutToTyVal τ'))) := by
          rw [h_pc]
          refine h_code _ _ ?_ ?_
          · simp [freshRootCS, emit, setPlaceInfo]
          · simp [freshRootCS, emit, setPlaceInfo]
        have h_run1 := runN_Assgn_Alloc_step compProg s_osea (Register.R cs.nextReg)
          (layoutToTyVal τ') h_code0 h_own_tgt'
        refine ⟨_, _, _, 1, h_incr_a, h_incr_t, h_run1, h_pc1, ?_⟩
        refine ⟨?_, h_lbs1, ?_, ?_, h_id_a', h_wf_t', ?_, ?_, ?_, h_prb1⟩
        · show s_osea.pc + 1 = _
          rw [h_pc]
          simp only [freshRootCS, emit, setPlaceInfo, List.length_cons, List.length_nil]
        · intro a v h_find
          rw [h_find1] at h_find
          exact SourceMemSim.rename_mono h_incr_a h_incr_t h_sms a v h_find
        · rw [h_perms1]; exact h_psim'
        · rw [h_perms1]; exact h_tbd'
        · exact AllocLockstep.of_alloc h_alloc h_incr_a h_sz h_memstart1 h_allocs1
        · intro σ' loc' h_none
          have h_none1 : mirlite.Env.lookup s0.env loc' = none := h_none
          rw [h_env1] at h_none1
          by_cases h_idx : loc'.idx = loc.idx
          · exfalso
            simp only [mirlite.Env.lookup, mirlite.Env.set, h_idx] at h_none1
            exact absurd h_none1 (by simp)
          have h_idxv : loc'.idx.1 ≠ loc.idx.1 := fun h => h_idx (Fin.ext h)
          have h_none0 : mirlite.Env.lookup s_mir.env loc' = none := by
            simpa only [mirlite.Env.lookup, mirlite.Env.set, if_neg h_idx] using h_none1
          show getPlaceInfo (freshRootCS cs loc) _ = _
          simp only [freshRootCS]
          rw [getPlaceInfo_setPlaceInfo_ne _ h_idxv, getPlaceInfo_emit]
          exact h_unmap loc' h_none0

/-! ## The compiled shape of a guard -/

/-- A guard that compiled compiled its body, from the reserved state. -/
theorem emitSkipIfAround_value_inv {α : Type} {discrReg : Register} {val : Word}
    {body : CheckedCompilerM α} {cs : CompilerState}
    (h : CheckedCompilerM.value (emitSkipIfAround discrReg val body) cs = .ok ()) :
    ∃ a, CheckedCompilerM.value body (reserveLabel cs) = .ok a := by
  simp only [emitSkipIfAround, CheckedCompilerM.value, CompilerM.value] at h
  split at h
  · simp at h
  · rename_i a h_a
    exact ⟨a, h_a⟩

/-- After `ensurePlaceRoot`, the place's root is mapped. -/
theorem ensurePlaceRoot_mapped {τ : LayoutTy} (p : Place Γ τ) (cs : CompilerState) :
    PlaceInputsMapped (CompilerM.run (ensurePlaceRoot p) cs) p := by
  induction p with
  | proj base path ih => exact ih
  | deref pp ih => exact ih
  | «local» loc =>
    cases h : getPlaceInfo cs loc.idx.1 with
    | some info =>
        obtain ⟨reg, layout⟩ := info
        rw [ensurePlaceRoot_run_eq_of_mapped (p := Place.local loc) ⟨reg, layout, h⟩]
        exact ⟨reg, layout, h⟩
    | none =>
        obtain ⟨h_run, -⟩ := ensureLocalRegE_fresh (loc := loc) h
        have h_r : CompilerM.run (ensurePlaceRoot (Place.local loc)) cs
            = CompilerM.run (ensureLocalRegE loc) cs := by
          simp only [ensurePlaceRoot, CompilerM.run_bind, CompilerM.run_pure]
        rw [h_r, h_run]
        simp only [PlaceInputsMapped]
        exact ⟨_, _, getPlaceInfo_setPlaceInfo_self _ _ _⟩

/-- The guarded body IS the statement compiler's lowering of the same
    assign — `rfl` for every destination now that the `.assign (.local)`
    fast path is gone (2026-09-18). Kept as the named interface. -/
theorem compileAssignChecked_stmt_run {τ : LayoutTy} (dst : Place Γ τ) (rhs : RExpr Γ τ)
    (cs : CompilerState) :
    CheckedCompilerM.run (compileAssignChecked dst rhs) cs
      = CheckedCompilerM.run (compileStmtChecked (.assign dst rhs)) cs := rfl

theorem compileAssignChecked_stmt_value {τ : LayoutTy} (dst : Place Γ τ) (rhs : RExpr Γ τ)
    (cs : CompilerState) {so : ResultWithEvidence Unit (fun _ => StmtEvidence (.assign dst rhs))}
    (h : CheckedCompilerM.value (compileStmtChecked (.assign dst rhs)) cs = .ok so) :
    ∃ so', CheckedCompilerM.value (compileAssignChecked dst rhs) cs = .ok so' := ⟨so, h⟩

/-- The compiler state after a guard's root step and discriminant read. -/
def guardReadCS (discr : Place Γ (LayoutTy.IntL tN)) {τ : LayoutTy} (dst : Place Γ τ)
    (cs : CompilerState) : CompilerState :=
  CheckedCompilerM.run (guardRead discr) (CompilerM.run (ensurePlaceRoot dst) cs)

/-- A guard that compiled: its read compiled, its body compiled from the
    reserved state after the read, and its run is the body's run with the
    guard's label patched. -/
theorem compileStmt_assignIf_shape {τ : LayoutTy}
    (discr : Place Γ (LayoutTy.IntL tN)) (val : Word) (dst : Place Γ τ) (rhs : RExpr Γ τ)
    (cs : CompilerState)
    (h_ok : ∃ so, CheckedCompilerM.value
      (compileStmtChecked (.assignIf discr val dst rhs)) cs = .ok so) :
    ∃ r, CheckedCompilerM.value (guardRead discr) (CompilerM.run (ensurePlaceRoot dst) cs)
        = .ok r ∧
    (∃ so, CheckedCompilerM.value (compileAssignChecked dst rhs)
      (reserveLabel (guardReadCS discr dst cs)) = .ok so) ∧
    CheckedCompilerM.run (compileStmtChecked (.assignIf discr val dst rhs)) cs
      = patchLabel
          (CheckedCompilerM.run (compileAssignChecked dst rhs)
            (reserveLabel (guardReadCS discr dst cs)))
          (guardReadCS discr dst cs).nextLabel
          (Instr.SkipIf r val
            (skipCount (guardReadCS discr dst cs) (compileAssignChecked dst rhs))) := by
  obtain ⟨so, h_so⟩ := h_ok
  simp only [compileStmtChecked, csMonad] at h_so ⊢
  cases hR : CheckedCompilerM.value (guardRead discr) (CompilerM.run (ensurePlaceRoot dst) cs) with
  | error e =>
      rw [hR] at h_so
      simp at h_so
  | ok r =>
  rw [hR] at h_so
  simp only [] at h_so ⊢
  cases hE : CheckedCompilerM.value
      (emitSkipIfAround r val (compileAssignChecked dst rhs))
      (CheckedCompilerM.run (guardRead discr) (CompilerM.run (ensurePlaceRoot dst) cs)) with
  | error e =>
      rw [hE] at h_so
      simp at h_so
  | ok u =>
  cases u
  obtain ⟨b, h_body⟩ := emitSkipIfAround_value_inv hE
  refine ⟨r, rfl, ⟨b, h_body⟩, ?_⟩
  simp only [guardReadCS]
  rw [emitSkipIfAround_run _ _ _ _ h_body]

/-! ## The arm -/

/-- What an assign leaf provides, abstracted over the rvalue: from the
    invariant at the state its code starts from and a frame conditional
    on it compiling there, the simulation. Every `assignStep_*` is an
    instance; `assignLeaf_all` collects them by rvalue. -/
def AssignLeaf (compProg : oseair.Prog) {τ : LayoutTy} (dst : Place Γ τ) (rhs : RExpr Γ τ) :
    Prop :=
  ∀ {cs0 : CompilerState} {prog : obseq3.Prog Γ} {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_mir' : mirlite.State MSB Γ} {s_osea : oseair.State MSB} {csStart : CompilerState},
    InvAt ρa ρt s_mir s_osea csStart →
    ((∃ so, CheckedCompilerM.value (compileStmtChecked (.assign dst rhs)) csStart
        = Except.ok so) →
      StmtFrame compProg cs0 prog s_mir.pc
        (CheckedCompilerM.run (compileStmtChecked (.assign dst rhs)) csStart)) →
    mirlite.stepStmt MSB s_mir (.assign dst rhs) = .ok s_mir' →
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea'

theorem assignLeaf_all {τ : LayoutTy} (compProg : oseair.Prog)
    (dst : Place Γ τ) (rhs : RExpr Γ τ) :
    AssignLeaf compProg dst rhs := by
  cases rhs with
  | constInit v =>
      intro _ _ _ _ _ _ _ _ h_invAt hF h_step
      exact assignStep_constStore compProg (constInit_valuePkg v compProg) h_invAt hF h_step
  | uninit =>
      intro _ _ _ _ _ _ _ _ h_invAt hF h_step
      exact assignStep_constStore compProg (uninit_valuePkg _ compProg) h_invAt hF h_step
  | copy src =>
      intro _ _ _ _ _ _ _ _ h_invAt hF h_step
      exact assignStep_readrhs compProg (copy_readRhsFamily compProg) h_invAt hF h_step
  | move src =>
      intro _ _ _ _ _ _ _ _ h_invAt hF h_step
      exact assignStep_move compProg h_invAt hF h_step
  | alloc len =>
      intro _ _ _ _ _ _ _ _ h_invAt hF h_step
      exact assignStep_constStore compProg (alloc_valuePkg len compProg) h_invAt hF h_step
  | binOp op a b =>
      intro _ _ _ _ _ _ _ _ h_invAt hF h_step
      exact assignStep_constStore compProg (binOp_valuePkg op a b compProg) h_invAt hF h_step
  | sliceLen src =>
      intro _ _ _ _ _ _ _ _ h_invAt hF h_step
      exact assignStep_constStore compProg (sliceLen_valuePkg src compProg) h_invAt hF h_step
  | subSlice src lo hi =>
      intro _ _ _ _ _ _ _ _ h_invAt hF h_step
      exact assignStep_constStore compProg (subSlice_valuePkg src lo hi compProg)
        h_invAt hF h_step
  | ref kind prot mask src =>
      intro _ _ _ _ _ _ _ _ h_invAt hF h_step
      exact assignStep_ref kind prot mask compProg h_invAt hF h_step
  | ptrCast src =>
      intro _ _ _ _ _ _ _ _ h_invAt hF h_step
      exact assignStep_readrhs compProg (ptrCast_readRhsFamily compProg) h_invAt hF h_step
  | ptrOffset src delta =>
      intro _ _ _ _ _ _ _ _ h_invAt hF h_step
      exact assignStep_readrhs compProg (ptrOffset_readRhsFamily delta compProg) h_invAt hF h_step
  | refSlice kind prot src =>
      intro _ _ _ _ _ _ _ _ h_invAt hF h_step
      exact assignStep_readrhs compProg (refSlice_readRhsFamily kind prot compProg) h_invAt hF h_step
  | exposeAddr src =>
      intro _ _ _ _ _ _ _ _ h_invAt hF h_step
      exact assignStep_readrhs compProg (exposeAddr_readRhsFamily compProg) h_invAt hF h_step
  | fromExposed src =>
      intro _ _ _ _ _ _ _ _ h_invAt hF h_step
      exact assignStep_readrhs compProg (fromExposed_readRhsFamily compProg) h_invAt hF h_step

/-- The `assignIf` step. -/
theorem CompilerInv_step_assignIf {τ : LayoutTy}
    {discr : Place Γ (LayoutTy.IntL tN)} {val : Word} {dst : Place Γ τ} {rhs : RExpr Γ τ}
    (compProg : oseair.Prog)
    (h_leaf : AssignLeaf compProg dst rhs)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    (h_stmt : prog.get? s_mir.pc = some (.assignIf discr val dst rhs))
    (h_step : mirlite.stepStmt MSB s_mir (.assignIf discr val dst rhs) = .ok s_mir') :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' := by
  obtain ⟨csPrefix, h_csAt, h_invAt⟩ := h_inv.invAt
  -- §1 the statement compiled; its shape
  obtain ⟨so, h_so⟩ := stmt_compiles_of_comp h_comp h_csAt h_stmt
  have F : StmtFrame compProg cs0 prog s_mir.pc
      (CheckedCompilerM.run (compileStmtChecked (.assignIf discr val dst rhs)) csPrefix) :=
    StmtFrame.ofStmt h_comp h_csAt h_stmt h_so
  obtain ⟨r, hR, ⟨bo, h_body⟩, h_run⟩ :=
    compileStmt_assignIf_shape discr val dst rhs csPrefix ⟨so, h_so⟩
  rw [h_run] at F
  obtain ⟨discrOut, hD⟩ := guardRead_value_inv hR
  obtain ⟨h_gfr, h_gfv⟩ := guardRead_flat hD
  have h_r : r = Register.R (CheckedCompilerM.run
      (placeToRegChecked RefKind.Shared (flattenPlace discr))
      (CompilerM.run (ensurePlaceRoot dst) csPrefix)).nextReg := by
    rw [hR] at h_gfv
    exact Except.ok.inj h_gfv
  simp only [guardReadCS] at F h_body
  -- the state increments along the statement
  have h_incrRead : StateIncr (CompilerM.run (ensurePlaceRoot dst) csPrefix)
      (CheckedCompilerM.run (guardRead discr) (CompilerM.run (ensurePlaceRoot dst) csPrefix)) :=
    CheckedCompilerM.incr _ _
  have h_incrBody : StateIncr
      (reserveLabel (CheckedCompilerM.run (guardRead discr)
        (CompilerM.run (ensurePlaceRoot dst) csPrefix)))
      (CheckedCompilerM.run (compileAssignChecked dst rhs)
        (reserveLabel (CheckedCompilerM.run (guardRead discr)
          (CompilerM.run (ensurePlaceRoot dst) csPrefix)))) :=
    CheckedCompilerM.incr _ _
  have h_incrStmt : StateIncr (CompilerM.run (ensurePlaceRoot dst) csPrefix)
      (patchLabel
        (CheckedCompilerM.run (compileAssignChecked dst rhs)
          (reserveLabel (CheckedCompilerM.run (guardRead discr)
            (CompilerM.run (ensurePlaceRoot dst) csPrefix))))
        (CheckedCompilerM.run (guardRead discr)
          (CompilerM.run (ensurePlaceRoot dst) csPrefix)).nextLabel
        (Instr.SkipIf r val (skipCount (CheckedCompilerM.run (guardRead discr)
          (CompilerM.run (ensurePlaceRoot dst) csPrefix)) (compileAssignChecked dst rhs)))) :=
    StateIncr.patchLabel
      (h_incrRead.trans ((reserveLabel_state_incr _).trans h_incrBody))
      h_incrRead.nextLabel_le _
  have h_code1 : CodeIncluded compProg (CompilerM.run (ensurePlaceRoot dst) csPrefix) :=
    F.code.mono h_incrStmt
  have h_codeR : CodeIncluded compProg
      (CheckedCompilerM.run (guardRead discr) (CompilerM.run (ensurePlaceRoot dst) csPrefix)) :=
    F.code.mono (StateIncr.patchLabel ((reserveLabel_state_incr _).trans h_incrBody)
      (Nat.le_refl _) _)
  -- the guard's instruction
  have h_skip : compProg (CheckedCompilerM.run (guardRead discr)
      (CompilerM.run (ensurePlaceRoot dst) csPrefix)).nextLabel
      = some (Instr.SkipIf r val (skipCount (CheckedCompilerM.run (guardRead discr)
          (CompilerM.run (ensurePlaceRoot dst) csPrefix)) (compileAssignChecked dst rhs))) := by
    refine F.code _ _ ?_ ?_
    · have := h_incrBody.nextLabel_le
      simp only [reserveLabel_nextLabel] at this
      simp only [patchLabel_nextLabel]
      omega
    · simp [patchLabel]
  -- §2 the source step
  simp only [mirlite.stepStmt] at h_step
  cases h_root : mirlite.ensureRoot MSB s_mir dst with
  | err msg => rw [h_root] at h_step; simp at h_step
  | ok s0 =>
  rw [h_root] at h_step
  simp only [] at h_step
  cases h_eval : mirlite.evalRExpr MSB s0 (.copy discr) with
  | err e => rw [h_eval] at h_step; simp at h_step
  | ok output =>
  rw [h_eval] at h_step
  simp only [] at h_step
  -- §3 the root step
  obtain ⟨ρa1, ρt1, sA, n0, h_incrA1, h_incrT1, h_run0, h_pc0, h_inv1⟩ :=
    ensureRoot_simulation dst compProg h_invAt h_code1 h_root
  -- §4 the read, through copy's package
  have h_eval' : mirlite.evalRExpr MSB s0 (.copy (flattenPlace discr)) = .ok output := by
    rw [evalRExpr_copy_flatten]; exact h_eval
  obtain ⟨pOut, h_pval, h_prmR, h_rest⟩ :=
    copy_readRegPkg_flat compProg discr ρa1 ρt1 s0 sA
      (CompilerM.run (ensurePlaceRoot dst) csPrefix)
      h_inv1.id_a h_inv1.wf_t h_inv1.tbd h_inv1.lbs h_inv1.prb h_inv1.sms h_inv1.alloc
      h_inv1.psim h_inv1.pc output h_eval'
  rw [← h_gfr] at h_prmR h_rest
  obtain ⟨ρt2, nR, sR, perms₂, vals, h_incrT2, h_wfT2, h_ost, h_vlen, h_runR, h_regmono,
    h_lbsR, h_psimR, h_tbdR, h_smem, h_pcR, h_vreg, h_valsRel, h_vbelow, h_frameR⟩ :=
    h_rest h_codeR
  rw [← h_r] at h_vreg
  -- the discriminant is a word
  split at h_step
  · rename_i v h_vals
    rw [h_vals] at h_valsRel
    have h_valsD := ListRel_word_inv h_valsRel
    subst h_valsD
    -- the invariant's per-state half after the read, at the state the
    -- guard falls through to
    have h_prmRes : (reserveLabel (CheckedCompilerM.run (guardRead discr)
        (CompilerM.run (ensurePlaceRoot dst) csPrefix))).placeRegMap
        = (CheckedCompilerM.run (guardRead discr)
          (CompilerM.run (ensurePlaceRoot dst) csPrefix)).placeRegMap := by
      simp
    have h_mappedRes : PlaceInputsMapped (reserveLabel (CheckedCompilerM.run (guardRead discr)
        (CompilerM.run (ensurePlaceRoot dst) csPrefix))) dst :=
      PlaceInputsMapped.placeRegMap_congr (by rw [h_prmRes, h_prmR]) dst
        (ensurePlaceRoot_mapped dst csPrefix)
    have h_prmBody : (CheckedCompilerM.run (compileAssignChecked dst rhs)
        (reserveLabel (CheckedCompilerM.run (guardRead discr)
          (CompilerM.run (ensurePlaceRoot dst) csPrefix)))).placeRegMap
        = (CheckedCompilerM.run (guardRead discr)
          (CompilerM.run (ensurePlaceRoot dst) csPrefix)).placeRegMap := by
      rw [compileAssignChecked_placeRegMap_of_mapped dst rhs h_mappedRes, h_prmRes]
    have h_unmapR : UnboundLocalsUnmapped output.state.env
        (CheckedCompilerM.run (guardRead discr) (CompilerM.run (ensurePlaceRoot dst) csPrefix)) := by
      intro σ' loc' h_none
      rw [getPlaceInfo_congr' h_prmR]
      rw [h_ost] at h_none
      exact h_inv1.unmap loc' h_none
    have h_prbR : PlaceRegMapBound
        (CheckedCompilerM.run (guardRead discr) (CompilerM.run (ensurePlaceRoot dst) csPrefix)) := by
      intro idx reg τ' h_look
      rw [getPlaceInfo_congr' h_prmR] at h_look
      exact RegisterBelow.mono h_regmono (h_inv1.prb idx reg τ' h_look)
    have h_smsR : SourceMemSim ρa1 ρt2 output.state.mem sR.mem := by
      rw [h_ost, h_smem]
      exact SourceMemSim.rename_mono (AddrRenameIncr.refl _) h_incrT2 h_inv1.sms
    have h_allocR : AllocLockstep ρa1 output.state.mem sR.mem := by
      rw [h_ost, h_smem]
      exact h_inv1.alloc
    have h_pcOut : output.state.pc = s_mir.pc := by
      rw [h_ost]; exact h_pc0
    split at h_step
    · -- §5a TAKEN: fall through, then the assign leaf
      rename_i h_veq
      have h_v : v = val := eq_of_beq h_veq
      subst h_v
      have h_run1 := runN_SkipIf_fallthrough_step compProg sR
        (by rw [h_pcR]; exact h_skip) h_vreg
      have h_invF : InvAt ρa1 ρt2 output.state { sR with pc := sR.pc + 1 }
          (reserveLabel (CheckedCompilerM.run (guardRead discr)
            (CompilerM.run (ensurePlaceRoot dst) csPrefix))) :=
        ⟨by show sR.pc + 1 = _; rw [h_pcR]; simp,
         by rw [h_ost]; exact LocalBindingSim.placeRegMap_congr h_prmRes h_lbsR,
         h_smsR,
         by rw [h_ost]; exact h_psimR,
         h_inv1.id_a, h_wfT2,
         by rw [h_ost]; exact h_tbdR,
         h_allocR,
         fun loc' h_none => by rw [getPlaceInfo_congr' h_prmRes]; exact h_unmapR loc' h_none,
         fun idx reg τ' h_look => by
           rw [getPlaceInfo_congr' h_prmRes] at h_look
           show RegisterBelow (CheckedCompilerM.run (guardRead discr)
             (CompilerM.run (ensurePlaceRoot dst) csPrefix)).nextReg reg
           exact h_prbR idx reg τ' h_look⟩
      have hF : (∃ so, CheckedCompilerM.value (compileStmtChecked (.assign dst rhs))
          (reserveLabel (CheckedCompilerM.run (guardRead discr)
            (CompilerM.run (ensurePlaceRoot dst) csPrefix))) = Except.ok so) →
          StmtFrame compProg cs0 prog output.state.pc
            (CheckedCompilerM.run (compileStmtChecked (.assign dst rhs))
              (reserveLabel (CheckedCompilerM.run (guardRead discr)
                (CompilerM.run (ensurePlaceRoot dst) csPrefix)))) := by
        intro _
        rw [← compileAssignChecked_stmt_run, h_pcOut]
        exact StmtFrame.of_patchLabel F (StateIncr.code_reserved h_incrBody)
      obtain ⟨ρa3, ρt3, s_osea', n, h_incrA3, h_incrT3, h_runL, h_inv'⟩ :=
        h_leaf h_invF hF h_step
      refine ⟨ρa3, ρt3, s_osea', n0 + (nR + (1 + n)), h_incrA1.trans h_incrA3,
        (h_incrT1.trans h_incrT2).trans h_incrT3, ?_, h_inv'⟩
      rw [oseair_runN_add _ _ _ _ _ h_run0, oseair_runN_add _ _ _ _ _ h_runR,
        oseair_runN_add _ _ _ _ _ h_run1]
      exact h_runL
    · -- §5b SKIPPED: jump over the body; the invariant at the statement's end
      rename_i h_vne
      have h_ne : v ≠ val := by simpa using h_vne
      cases h_step
      have h_run1 := runN_SkipIf_jump_step compProg sR
        (by rw [h_pcR]; exact h_skip) h_vreg h_ne
      obtain ⟨csNext, h_next, h_nl, h_nr, h_np⟩ := F.next
      have h_prmP : (patchLabel
          (CheckedCompilerM.run (compileAssignChecked dst rhs)
            (reserveLabel (CheckedCompilerM.run (guardRead discr)
              (CompilerM.run (ensurePlaceRoot dst) csPrefix))))
          (CheckedCompilerM.run (guardRead discr)
            (CompilerM.run (ensurePlaceRoot dst) csPrefix)).nextLabel
          (Instr.SkipIf r val (skipCount (CheckedCompilerM.run (guardRead discr)
            (CompilerM.run (ensurePlaceRoot dst) csPrefix)) (compileAssignChecked dst rhs)))).placeRegMap
          = (CheckedCompilerM.run (guardRead discr)
            (CompilerM.run (ensurePlaceRoot dst) csPrefix)).placeRegMap := by
        rw [patchLabel_placeRegMap, h_prmBody]
      have h_bodyLe := h_incrBody.nextLabel_le
      simp only [reserveLabel_nextLabel] at h_bodyLe
      refine ⟨ρa1, ρt2,
        { sR with pc := sR.pc + 1 + skipCount (CheckedCompilerM.run (guardRead discr)
            (CompilerM.run (ensurePlaceRoot dst) csPrefix)) (compileAssignChecked dst rhs) },
        n0 + (nR + 1), h_incrA1, h_incrT1.trans h_incrT2, ?_, ?_⟩
      · rw [oseair_runN_add _ _ _ _ _ h_run0, oseair_runN_add _ _ _ _ _ h_runR]
        exact h_run1
      · refine CompilerInv.ofInvAt h_next (by show output.state.pc + 1 = _; rw [h_pcOut])
          h_nl h_nr h_np ⟨?_, ?_, h_smsR, ?_, h_inv1.id_a, h_wfT2, ?_, h_allocR, ?_, ?_⟩
        · show sR.pc + 1 + skipCount _ _ = _
          rw [h_pcR]
          simp only [patchLabel_nextLabel, skipCount, reserveLabel_nextLabel]
          omega
        · show LocalBindingSim ρa1 ρt2 output.state.env sR _
          rw [h_ost]
          exact LocalBindingSim.placeRegMap_congr h_prmP h_lbsR
        · show PermSim ρt2 output.state.perms sR.perms
          rw [h_ost]; exact h_psimR
        · show TagRenameBounded ρt2 output.state.perms.NextTag sR.perms.NextTag
          rw [h_ost]; exact h_tbdR
        · intro σ' loc' h_none
          rw [getPlaceInfo_congr' h_prmP]
          exact h_unmapR loc' h_none
        · intro idx reg τ' h_look
          rw [getPlaceInfo_congr' h_prmP] at h_look
          have h_le : (CheckedCompilerM.run (guardRead discr)
              (CompilerM.run (ensurePlaceRoot dst) csPrefix)).nextReg
              ≤ (patchLabel
                (CheckedCompilerM.run (compileAssignChecked dst rhs)
                  (reserveLabel (CheckedCompilerM.run (guardRead discr)
                    (CompilerM.run (ensurePlaceRoot dst) csPrefix))))
                (CheckedCompilerM.run (guardRead discr)
                  (CompilerM.run (ensurePlaceRoot dst) csPrefix)).nextLabel
                (Instr.SkipIf r val (skipCount (CheckedCompilerM.run (guardRead discr)
                  (CompilerM.run (ensurePlaceRoot dst) csPrefix)) (compileAssignChecked dst rhs)))).nextReg := by
            simp only [patchLabel_nextReg]
            have := h_incrBody.nextReg_le
            simp only [reserveLabel_nextReg] at this
            exact this
          exact RegisterBelow.mono h_le (h_prbR idx reg τ' h_look)
  · -- not a word: the source is stuck
    simp at h_step

end obseq3.proof
