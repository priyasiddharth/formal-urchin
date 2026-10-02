import obseq3.byteproof.memsim
import obseq3.compile_bytes
import obseq3.oseair_layout

/-!
# The byte-level const_write leaf — A step 2

The first statement of the byte-level compiler proof, end to end: the
byte compiler (`compile_bytes.lean`) lowers `x := const v` with `x` a
BOUND local to one `CStore (L x) [Dat v]` through `x`'s register, and the
layout-typed target (`oseair_layout.lean`) runs it to a state related to
the byte source's (`mirlite_bytes.lean`) by the byte invariant `InvAt`.

The invariant is the cell proof's `InvAt` with the memory half replaced
by the per-byte relation of the spike (`memsim.lean`):
- `ByteMemSim ρt` in place of `SourceMemSim ρa ρt`, and
  `ByteAllocLockstep` in place of `AllocLockstep ρa` — addresses are not
  renamed at all (`ρa` was the identity on its domain), so there is no
  `IdentityOnDomain` and no domain conjunct in the binding relation;
- a bound local's register holds a pointer to the local's whole block at
  its BYTE size `(L loc.idx).size`.
The permission half (`PermSim`, `TagRenameWF`, `TagRenameBounded`) is the
cell proof's, unchanged, and so are the compiler-state halves (now about
`compileB.CompilerState`).

Scope: the bound-local regime (the cell proof's regime A). Fresh roots,
projections and derefs follow the cell leaf structure (`storereg_*`).
-/

namespace obseq3.byteproof

open obseq3 obseq3.bytes obseq3.proof
open obseq3.mirlite (MemValue Binding Env)
open obseq3.oseair (Val Register)
open obseq3.compileB

/-! ## The byte invariant -/

/-- Register `reg` holds a pointer to `[base, base + size)` at offset 0
    with tag `tag` (some extent). -/
def PtrRegEntry (regMap : oseairL.RegMap) (reg : Register) (base size : Nat) (tag : Tag) :
    Prop :=
  ∃ extent, regMap.lookup reg = some [Val.Ptr base 0 extent size tag]

/-- Bound locals: the compiler mapped the local to a register that holds
    a pointer to the local's block (same address, byte size, renamed
    tag); the tag is not the wildcard (`sb_own` minted it). -/
def LocalBindingSimB {Γ : Ctx} (L : mirliteB.LayEnv Γ) (ρt : TagRenameMap)
    (env : Env Γ) (s_osea : oseairL.State MSB) (cs : CompilerState) : Prop :=
  ∀ {τ : LayoutTy} (loc : Local Γ τ) (binding : Binding),
    env.lookup loc = some binding →
    ∃ reg tag,
      getPlaceInfo cs loc.idx.1 = some (reg, τ) ∧
      PtrRegEntry s_osea.reg reg binding.addr (L loc.idx).size tag ∧
      ρt binding.tag = some tag ∧
      (binding.tag == wildcardTag) = false

def UnboundLocalsUnmappedB {Γ : Ctx} (env : Env Γ) (cs : CompilerState) : Prop :=
  ∀ {τ : LayoutTy} (loc : Local Γ τ), env.lookup loc = none → getPlaceInfo cs loc.idx.1 = none

def PlaceRegMapBoundB (cs : CompilerState) : Prop :=
  ∀ idx reg τ, getPlaceInfo cs idx = some (reg, τ) → RegisterBelow cs.nextReg reg

/-- Everything a compiler state emitted is in the program. -/
def CodeIncludedB (compProg : oseairL.Prog) (cs : CompilerState) : Prop :=
  ∀ q instr, q < cs.nextLabel → cs.code q = some instr → compProg q = some instr

/-- The byte invariant at compiler state `cs`. -/
structure InvAtB {Γ : Ctx} (L : mirliteB.LayEnv Γ) (ρt : TagRenameMap)
    (s_mir : mirliteB.State MSB Γ) (s_osea : oseairL.State MSB) (cs : CompilerState) :
    Prop where
  pc : s_osea.pc = cs.nextLabel
  lbs : LocalBindingSimB L ρt s_mir.env s_osea cs
  mem : ByteMemSim ρt s_mir.mem s_osea.mem
  alloc : ByteAllocLockstep s_mir.mem s_osea.mem
  psim : PermSim ρt s_mir.perms s_osea.perms
  wf_t : TagRenameWF ρt
  tbd : TagRenameBounded ρt s_mir.perms.NextTag s_osea.perms.NextTag
  unmap : UnboundLocalsUnmappedB s_mir.env cs
  prb : PlaceRegMapBoundB cs

/-! ## The compiled shape -/

theorem emit_nil (cs : CompilerState) : emit cs [] = cs := by
  cases cs
  simp only [emit, List.length_nil, Nat.add_zero, CompilerState.mk.injEq, true_and]
  refine ⟨?_, trivial⟩
  funext label
  rw [if_neg (by omega)]

theorem ensureLocalRegE_existing {Γ : Ctx} {L : mirliteB.LayEnv Γ} {τ : LayoutTy}
    {loc : Local Γ τ} {cs : CompilerState} {reg : Register} {layout : LayoutTy}
    (h : getPlaceInfo cs loc.idx.1 = some (reg, layout)) :
    CompilerM.run (ensureLocalRegE L loc) cs = cs := by
  unfold CompilerM.run ensureLocalRegE
  split
  · rfl
  · rename_i h'
    rw [h'] at h
    cases h

theorem placeToRegChecked_local_existing {Γ : Ctx} {L : mirliteB.LayEnv Γ} {τ layout : LayoutTy}
    {kind : RefKind} {loc : Local Γ τ} {cs : CompilerState} {reg : Register}
    (h : getPlaceInfo cs loc.idx.1 = some (reg, layout)) :
    CheckedCompilerM.run (placeToRegChecked L kind (.local loc)) cs = cs ∧
    ∃ placeOut,
      CheckedCompilerM.value (placeToRegChecked L kind (.local loc)) cs
        = Except.ok placeOut ∧
      placeOut.result = { reg := reg, cleanup := [] } := by
  simp only [CheckedCompilerM.run, CheckedCompilerM.value, CompilerM.run,
    CompilerM.value, placeToRegChecked]
  refine ⟨?_, ?_⟩
  · split <;> rfl
  · split
    · rename_i reg' layout' h'
      rw [h'] at h
      injection h with h2
      have h_eq : reg' = reg := congrArg Prod.fst h2
      subst h_eq
      exact ⟨_, rfl, rfl⟩
    · rename_i h'
      rw [h'] at h
      cases h

/-- A constant store to a BOUND local compiles to exactly one `CStore` at
    the local's byte layout, through the local's register. -/
theorem compileStmt_constInit_local {Γ : Ctx} {L : mirliteB.LayEnv Γ}
    {loc : Local Γ obseq.LayoutTy.NatL} {cs : CompilerState} {reg : Register} {layout : LayoutTy} (v : Word)
    (h : getPlaceInfo cs loc.idx.1 = some (reg, layout)) :
    CheckedCompilerM.run (compileStmtChecked L (.assign (.local loc) (.constInit v))) cs
      = emit cs [oseairL.Instr.CStore (L loc.idx) [Val.Dat v] reg] ∧
    ∃ so, CheckedCompilerM.value
      (compileStmtChecked L (.assign (.local loc) (.constInit v))) cs = Except.ok so := by
  obtain ⟨h_run, out, h_val, h_res⟩ :=
    placeToRegChecked_local_existing (L := L) (kind := RefKind.Mut) h
  have h_ens := ensureLocalRegE_existing (L := L) h
  simp only [compileStmtChecked, compileAssignChecked, ensurePlaceRoot,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind, CheckedCompilerM.run_lift,
    CheckedCompilerM.value_lift, CompilerM.run_bind, CompilerM.value_bind,
    CompilerM.run_pure, compileRExprPreChecked, CheckedCompilerM.run_pure,
    CheckedCompilerM.value_pure, h_ens, h_run, h_val, h_res]
  refine ⟨?_, ⟨_, rfl⟩⟩
  simp only [CompilerM.run, emitM, cleanupInstrs, List.reverse_nil, List.map_nil, emit_nil]
  rfl

/-! ## The step -/

/-- A layout store only rewrites bytes: the allocation table, watermark
    and freed list are untouched. -/
theorem writeL_eq_write {m m' : bytes.Mem} {a : Nat} {lay : BLayout} {vs : List MemValue}
    (hw : mirliteB.writeL m a lay vs = .ok m') : ∃ buf, m' = m.write a buf := by
  unfold mirliteB.writeL at hw
  by_cases hc : (vs.length != lay.leaves.length) = true
  · rw [if_pos hc] at hw; cases hw
  · rw [if_neg hc] at hw
    simp only [bind, Except.bind, pure, Except.pure] at hw
    split at hw
    · cases hw
    · rename_i buf _
      simp only [Except.ok.injEq] at hw
      exact ⟨buf, hw.symm⟩

theorem ByteAllocLockstep.write {mS mT : bytes.Mem} (h : ByteAllocLockstep mS mT)
    (a a' : Nat) (bs bs' : List AbstractByte) :
    ByteAllocLockstep (mS.write a bs) (mT.write a' bs') := h

/-- REGIME A of the byte const_write leaf: `x := const v` with `x` a bound
    local. If the byte source steps, the compiled `CStore` runs in one
    target step to a state related by the byte invariant at the
    statement's compiled state. -/
theorem constWrite_local_sim {Γ : Ctx} {L : mirliteB.LayEnv Γ} {ρt : TagRenameMap}
    {s_mir s_mir' : mirliteB.State MSB Γ} {s_osea : oseairL.State MSB}
    {loc : Local Γ obseq.LayoutTy.NatL} {b : Binding} {v : Word} {cs : CompilerState}
    (compProg : oseairL.Prog)
    (h_inv : InvAtB L ρt s_mir s_osea cs)
    (h_code : CodeIncludedB compProg
      (CheckedCompilerM.run (compileStmtChecked L (.assign (.local loc) (.constInit v))) cs))
    (h_env : s_mir.env.lookup loc = some b)
    (h_step : mirliteB.stepStmt MSB L s_mir (.assign (.local loc) (.constInit v)) = .ok s_mir') :
    ∃ s_osea', oseairL.runN MSB 1 s_osea compProg = .Ok s_osea' ∧
      InvAtB L ρt s_mir' s_osea'
        (CheckedCompilerM.run (compileStmtChecked L (.assign (.local loc) (.constInit v))) cs) := by
  obtain ⟨reg, tag, h_pi, ⟨ext, h_reg⟩, h_rt, h_nw⟩ := h_inv.lbs loc b h_env
  obtain ⟨h_run, -⟩ := compileStmt_constInit_local (L := L) v h_pi
  rw [h_run] at h_code ⊢
  have h_instr : compProg s_osea.pc
      = some (oseairL.Instr.CStore (L loc.idx) [Val.Dat v] reg) := by
    rw [h_inv.pc]
    apply h_code
    · simp [emit]
    · simp [emit]
  -- the source: a bound root, the constant, the checked typed store
  simp only [mirliteB.stepStmt, mirliteB.doAssign, mirliteB.preparePlaceAssign,
    mirliteB.resolvePlace?, h_env, mirliteB.evalRExpr, mirliteB.resolvePlaceAcc,
    mirliteB.writeResolvedPlace, mirliteB.placeLayout] at h_step
  split at h_step
  · cases h_step
  rename_i h_free
  split at h_step
  · cases h_step
  split at h_step
  · rename_i perms' hu
    split at h_step
    · rename_i mem' hw
      simp only [mirliteB.Result.ok.injEq] at h_step
      subst h_step
      -- the target: the same store, related values
      have hv : ListRel (StoreSim ρt) [MemValue.word v]
          ([Val.Dat v].map oseairB.Val.toMem) :=
        ⟨Or.inr ⟨by simp, rfl⟩, trivial⟩
      obtain ⟨pT', mT', hu', hw', hp', hm'⟩ :=
        store_step_sim h_inv.wf_t h_inv.psim h_inv.mem h_rt hv hu hw
      have h_freeT : s_osea.mem.isFreed b.addr = false := by
        simp only [bytes.Mem.isFreed, h_inv.alloc.2.2] at h_free ⊢
        simpa using h_free
      refine ⟨{ s_osea with perms := pT', mem := mT', pc := s_osea.pc + 1 }, ?_, ?_⟩
      · simp only [oseairL.runN, oseairL.step, h_instr, oseairL.writeThroughPtr, h_reg,
          h_freeT, Nat.add_zero, gt_iff_lt, Nat.lt_irrefl, if_false]
        simp only [PermissionModel.stackedBorrows] at hu'
        simp only [PermissionModel.stackedBorrows, hu', hw', Bool.false_eq_true, if_false]
      · obtain ⟨bufS, rfl⟩ := writeL_eq_write hw
        obtain ⟨bufT, rfl⟩ := writeL_eq_write hw'
        exact {
          pc := by simp [emit, h_inv.pc]
          lbs := fun loc' b' h' => h_inv.lbs loc' b' h'
          mem := hm'
          alloc := h_inv.alloc.write _ _ _ _
          psim := hp'
          wf_t := h_inv.wf_t
          tbd := by
            have h1 := sb_write_NextTag hu
            have h2 := sb_write_NextTag hu'
            simp only [PermissionModel.stackedBorrows] at h1 h2
            show TagRenameBounded ρt perms'.NextTag pT'.NextTag
            rw [h1, h2]
            exact h_inv.tbd
          unmap := fun loc' h' => h_inv.unmap loc' h'
          prb := h_inv.prb
        }
    · cases h_step
  · cases h_step

end obseq3.byteproof
