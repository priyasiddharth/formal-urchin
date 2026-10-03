import obseq3.byteproof.memsim
import obseq3.compile_bytes
import obseq3.oseair_layout

/-!
# The byte-level proof's spine: invariant, value package, destination leaves

The byte analogue of `proof/spine.lean`. The invariant `InvAtB` is the
cell proof's `InvAt` with the memory half replaced by the per-byte
relation of `memsim.lean`:
- `ByteMemSim ρt` in place of `SourceMemSim ρa ρt`, and
  `ByteAllocLockstep` in place of `AllocLockstep ρa` — addresses are not
  renamed at all (`ρa` was the identity on its domain), so there is no
  `IdentityOnDomain` and no domain conjunct in the binding relation;
- a bound local's register holds a pointer to the local's whole block at
  its BYTE size `(L loc.idx).size`.
The permission half (`PermSim`, `TagRenameWF`, `TagRenameBounded`) and
the compiler-state halves are the cell proof's (now about
`compileB.CompilerState`).

As in the cell proof, a leaf is per DESTINATION shape and sees the rvalue
only through its value package (`ValuePkgB`). One difference: the package
relates the values with `StoreSim` (undef ↦ undef), not the weaker read
relation — a byte STORE must encode the target's value, which can fail,
so an undef source value may only be stored as undef (the spike's finding
3). Every rvalue meets it: reads err on undef on both sides, and `uninit`
stores `Undef` on both.
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


/-! ## Running the target -/

theorem runN_trans {M : PermissionModel} {p : oseairL.Prog} :
    ∀ {n1 n2 : Nat} {s s1 s2 : oseairL.State M},
      oseairL.runN M n1 s p = .Ok s1 → oseairL.runN M n2 s1 p = .Ok s2 →
      oseairL.runN M (n1 + n2) s p = .Ok s2
  | 0, _, s, s1, _, h1, h2 => by
      simp only [oseairL.runN, oseairL.Result.Ok.injEq] at h1
      subst h1
      simpa using h2
  | n + 1, n2, s, s1, s2, h1, h2 => by
      rw [Nat.succ_add]
      simp only [oseairL.runN] at h1 ⊢
      split at h1
      · exact runN_trans h1 h2
      · cases h1

/-! ## The store step, abstracted over the instruction -/

theorem writeThroughPtr_msg_irrel {M : PermissionModel} {s s' : oseairL.State M}
    {ptr : Register} {lay : BLayout} {vals : List Val} (m1 m2 : String)
    (h : oseairL.writeThroughPtr M s ptr lay vals m1 = .Ok s') :
    oseairL.writeThroughPtr M s ptr lay vals m2 = .Ok s' := by
  revert h
  unfold oseairL.writeThroughPtr
  split
  · exact id
  · simp

/-- One store instruction, at a state whose registers agree with the
    post-rvalue state's below `bound`, performs the typed write of `vals`
    at layout `lay` (`proof/common.lean`'s `StoreStep`). -/
def StoreStepB (compProg : oseairL.Prog) (sR : oseairL.State MSB) (bound : Nat)
    (mkStore : Register → oseairL.Instr) (lay : BLayout) (vals : List Val) : Prop :=
  ∀ (s s' : oseairL.State MSB) (dreg : Register),
    (∀ r, RegisterBelow bound r → s.reg.lookup r = sR.reg.lookup r) →
    compProg s.pc = some (mkStore dreg) →
    oseairL.writeThroughPtr MSB s dreg lay vals "store" = .Ok s' →
    oseairL.runN MSB 1 s compProg = .Ok s'

/-- A CONSTANT store: the values ride in the instruction. -/
theorem StoreStepB.cstore (compProg : oseairL.Prog) (sR : oseairL.State MSB)
    (bound : Nat) (lay : BLayout) (vals : List Val) :
    StoreStepB compProg sR bound (fun d => oseairL.Instr.CStore lay vals d) lay vals := by
  intro s s' dreg _ h_code h_wtp
  simp only [oseairL.runN, oseairL.step, h_code,
    writeThroughPtr_msg_irrel _ "CStore Invalid Ptr" h_wtp]

/-- A REGISTER store: the operand register still holds the values. -/
theorem StoreStepB.rstore (compProg : oseairL.Prog) (sR : oseairL.State MSB)
    (bound : Nat) (lay : BLayout) (vreg : Register) (vals : List Val)
    (h_vregR : sR.reg.lookup vreg = some vals)
    (h_vbelow : RegisterBelow bound vreg) :
    StoreStepB compProg sR bound (fun d => oseairL.Instr.RStore lay vreg d) lay vals := by
  intro s s' dreg h_frame h_code h_wtp
  have h_v : s.reg.lookup vreg = some vals := by
    rw [h_frame vreg h_vbelow]; exact h_vregR
  simp only [oseairL.runN, oseairL.step, h_code, h_v,
    writeThroughPtr_msg_irrel _ "RStore Invalid Regs" h_wtp]

/-! ## The value package -/

/-- Everything a destination leaf needs of an rvalue (`proof/spine.lean`'s
    `ValuePkg`), at destination layout `dstL`: it lowers to code ending in
    ONE store, and once that code is in the program the target reaches a
    state whose store writes values `StoreSim`-related to the source's. -/
def ValuePkgB {Γ : Ctx} {τ : LayoutTy} (compProg : oseairL.Prog) (L : mirliteB.LayEnv Γ)
    (dstL : BLayout) (rhs : RExpr Γ τ) : Prop :=
  ∀ (ρt : TagRenameMap) (sM : mirliteB.State MSB Γ) (sA : oseairL.State MSB)
    (csA : CompilerState),
    TagRenameWF ρt →
    TagRenameBounded ρt sM.perms.NextTag sA.perms.NextTag →
    LocalBindingSimB L ρt sM.env sA csA →
    PlaceRegMapBoundB csA →
    ByteMemSim ρt sM.mem sA.mem →
    ByteAllocLockstep sM.mem sA.mem →
    PermSim ρt sM.perms sA.perms →
    sA.pc = csA.nextLabel →
    UnboundLocalsUnmappedB sM.env csA →
    ∀ (output : mirliteB.EvalOutput MSB Γ),
      mirliteB.evalRExpr MSB L sM dstL rhs = .ok output →
      ∃ (mkStore : Register → oseairL.Instr) (pOut : RhsPre L τ rhs),
      CheckedCompilerM.value (compileRExprPreChecked L dstL rhs) csA = Except.ok pOut ∧
      (∀ d, pOut.store d = [mkStore d]) ∧
      pOut.postCleanup = [] ∧
      (CheckedCompilerM.run (compileRExprPreChecked L dstL rhs) csA).placeRegMap
        = csA.placeRegMap ∧
      (CodeIncludedB compProg (CheckedCompilerM.run (compileRExprPreChecked L dstL rhs) csA) →
        ∃ (ρt' : TagRenameMap) (nR : Nat) (sR : oseairL.State MSB)
          (memO : bytes.Mem) (perms₂ : MSB.State) (vals : List Val),
          TagRenameIncr ρt ρt' ∧
          TagRenameWF ρt' ∧
          output.state = { sM with mem := memO, perms := perms₂ } ∧
          oseairL.runN MSB nR sA compProg = .Ok sR ∧
          csA.nextReg ≤ (CheckedCompilerM.run (compileRExprPreChecked L dstL rhs) csA).nextReg ∧
          LocalBindingSimB L ρt' sM.env sR
            (CheckedCompilerM.run (compileRExprPreChecked L dstL rhs) csA) ∧
          PermSim ρt' perms₂ sR.perms ∧
          TagRenameBounded ρt' perms₂.NextTag sR.perms.NextTag ∧
          ByteMemSim ρt' memO sR.mem ∧
          ByteAllocLockstep memO sR.mem ∧
          sR.pc = (CheckedCompilerM.run (compileRExprPreChecked L dstL rhs) csA).nextLabel ∧
          StoreStepB compProg sR
            (CheckedCompilerM.run (compileRExprPreChecked L dstL rhs) csA).nextReg
            mkStore dstL vals ∧
          ListRel (StoreSim ρt') output.values (vals.map oseair.Val.toMem))

/-! ## Destination: a bound local -/

/-- `loc := rhs` with `loc` bound, for any rvalue whose pre-phase ends in
    one store: the pre-phase's code, then the store through `loc`'s
    register. -/
theorem compileStmt_storereg_local {Γ : Ctx} {L : mirliteB.LayEnv Γ} {τ : LayoutTy}
    {loc : Local Γ τ} {rhs : RExpr Γ τ} {cs : CompilerState} {dstReg : Register}
    {mkStore : Register → oseairL.Instr} {pOut : RhsPre L τ rhs}
    (h_dst : getPlaceInfo cs loc.idx.1 = some (dstReg, τ))
    (h_pval : CheckedCompilerM.value (compileRExprPreChecked L (L loc.idx) rhs) cs
      = Except.ok pOut)
    (h_prm : (CheckedCompilerM.run (compileRExprPreChecked L (L loc.idx) rhs) cs).placeRegMap
      = cs.placeRegMap)
    (h_store : ∀ d, pOut.store d = [mkStore d])
    (h_post : pOut.postCleanup = []) :
    CheckedCompilerM.run (compileStmtChecked L (Stmt.assign (.local loc) rhs)) cs
      = emit (CheckedCompilerM.run (compileRExprPreChecked L (L loc.idx) rhs) cs)
          [mkStore dstReg] := by
  have h_dst' : getPlaceInfo (CheckedCompilerM.run (compileRExprPreChecked L (L loc.idx) rhs) cs)
      loc.idx.1 = some (dstReg, τ) := by
    show List.lookup _ _ = _
    rw [h_prm]; exact h_dst
  obtain ⟨h_run, out, h_val, h_res⟩ :=
    placeToRegChecked_local_existing (L := L) (kind := RefKind.Mut) h_dst'
  have h_ens := ensureLocalRegE_existing (L := L) h_dst
  simp only [compileStmtChecked, compileAssignChecked, ensurePlaceRoot,
    CheckedCompilerM.run_bind, CheckedCompilerM.run_lift,
    CheckedCompilerM.value_lift, CompilerM.run_bind, CompilerM.value_bind,
    CompilerM.run_pure, CheckedCompilerM.run_pure, h_ens,
    mirliteB.placeLayout, h_pval, h_run, h_val, h_res, h_store, h_post]
  simp only [CompilerM.run, emitM, cleanupInstrs, List.reverse_nil, List.map_nil, emit_nil]

/-- The bound-local destination leaf, for ANY rvalue with a value package
    (`proof/spine.lean`'s `storereg_local_simulation`). -/
theorem storereg_local_simB {Γ : Ctx} {L : mirliteB.LayEnv Γ} {ρt : TagRenameMap}
    {s_mir s_mir' : mirliteB.State MSB Γ} {s_osea : oseairL.State MSB}
    {τ : LayoutTy} {loc : Local Γ τ} {b : Binding} {rhs : RExpr Γ τ} {cs : CompilerState}
    (compProg : oseairL.Prog)
    (h_pkg : ValuePkgB compProg L (L loc.idx) rhs)
    (h_inv : InvAtB L ρt s_mir s_osea cs)
    (h_code : CodeIncludedB compProg
      (CheckedCompilerM.run (compileStmtChecked L (.assign (.local loc) rhs)) cs))
    (h_env : s_mir.env.lookup loc = some b)
    (h_step : mirliteB.stepStmt MSB L s_mir (.assign (.local loc) rhs) = .ok s_mir') :
    ∃ (ρt' : TagRenameMap) (s_osea' : oseairL.State MSB) (n : Nat),
      TagRenameIncr ρt ρt' ∧
      oseairL.runN MSB n s_osea compProg = .Ok s_osea' ∧
      InvAtB L ρt' s_mir' s_osea'
        (CheckedCompilerM.run (compileStmtChecked L (.assign (.local loc) rhs)) cs) := by
  obtain ⟨reg, -, h_pi, -, -, -⟩ := h_inv.lbs loc b h_env
  -- §1 the source: a bound root, the rvalue, the checked typed store
  simp only [mirliteB.stepStmt, mirliteB.doAssign, mirliteB.preparePlaceAssign,
    mirliteB.resolvePlace?, h_env, mirliteB.placeLayout] at h_step
  split at h_step
  · cases h_step
  rename_i output h_eval
  -- §2 the rvalue, behind its package
  obtain ⟨mkStore, pOut, h_pval, h_storeR, h_postR, h_prmR, h_pkg'⟩ :=
    h_pkg ρt s_mir s_osea cs h_inv.wf_t h_inv.tbd h_inv.lbs h_inv.prb h_inv.mem
      h_inv.alloc h_inv.psim h_inv.pc h_inv.unmap output h_eval
  have h_shape := compileStmt_storereg_local h_pi h_pval h_prmR h_storeR h_postR
  rw [h_shape] at h_code ⊢
  have h_codePre : CodeIncludedB compProg
      (CheckedCompilerM.run (compileRExprPreChecked L (L loc.idx) rhs) cs) := by
    intro q instr hq hc
    apply h_code q instr
    · simp only [emit]; omega
    · simp only [emit]; rw [if_neg (by omega)]; exact hc
  obtain ⟨ρt', nR, sR, memO, perms₂, vals, h_incr_t, h_wf_t', h_ost, h_runR, h_regmono,
    h_lbsR, h_psimR, h_tbdR, h_memR, h_allocR, h_pcR, h_exec, h_valsRel⟩ := h_pkg' h_codePre
  rw [h_ost] at h_step
  simp only [mirliteB.resolvePlaceAcc, h_env, mirliteB.writeResolvedPlace] at h_step
  -- the destination register still holds the root after the rvalue
  obtain ⟨reg2, tag2, h_pi2, ⟨ext2, h_reg2⟩, h_rt2, -⟩ := h_lbsR loc b h_env
  have h_reg_eq : reg2 = reg := by
    have : getPlaceInfo cs loc.idx.1 = some (reg2, τ) := by
      show List.lookup _ _ = _
      rw [← h_prmR]; exact h_pi2
    rw [h_pi] at this
    exact (Prod.mk.inj (Option.some.inj this)).1.symm
  subst h_reg_eq
  -- §3 the store, on both sides
  split at h_step
  · cases h_step
  rename_i h_free
  split at h_step
  · cases h_step
  split at h_step
  · rename_i permsW hu
    split at h_step
    · rename_i memW hw
      simp only [mirliteB.Result.ok.injEq] at h_step
      subst h_step
      obtain ⟨pT', mT', hu', hw', hp', hm'⟩ :=
        store_step_sim h_wf_t' h_psimR h_memR h_rt2 h_valsRel hu hw
      have h_freeT : sR.mem.isFreed b.addr = false := by
        simp only [bytes.Mem.isFreed, h_allocR.2.2] at h_free ⊢
        simpa using h_free
      have h_wtp : oseairL.writeThroughPtr MSB sR reg2 (L loc.idx) vals "store"
          = .Ok { sR with perms := pT', mem := mT', pc := sR.pc + 1 } := by
        simp only [PermissionModel.stackedBorrows] at hu'
        simp only [oseairL.writeThroughPtr, h_reg2, h_freeT, Nat.add_zero, gt_iff_lt,
          Nat.lt_irrefl, if_false, PermissionModel.stackedBorrows, hu', hw',
          Bool.false_eq_true]
      have h_instr : compProg sR.pc = some (mkStore reg2) := by
        rw [h_pcR]
        apply h_code
        · simp [emit]
        · simp [emit]
      have h_run1 := h_exec sR _ reg2 (fun _ _ => rfl) h_instr h_wtp
      refine ⟨ρt', _, nR + 1, h_incr_t, runN_trans h_runR h_run1, ?_⟩
      obtain ⟨bufS, rfl⟩ := writeL_eq_write hw
      obtain ⟨bufT, rfl⟩ := writeL_eq_write hw'
      exact {
        pc := by simp [emit, h_pcR]
        lbs := fun loc' b' h' => h_lbsR loc' b' h'
        mem := hm'
        alloc := h_allocR.write _ _ _ _
        psim := hp'
        wf_t := h_wf_t'
        tbd := by
          have h1 := sb_write_NextTag hu
          have h2 := sb_write_NextTag hu'
          simp only [PermissionModel.stackedBorrows] at h1 h2
          show TagRenameBounded ρt' permsW.NextTag pT'.NextTag
          rw [h1, h2]
          exact h_tbdR
        unmap := fun loc' h' => by
          have : getPlaceInfo (CheckedCompilerM.run (compileRExprPreChecked L (L loc.idx) rhs) cs)
              loc'.idx.1 = none := by
            show List.lookup _ _ = _
            rw [h_prmR]; exact h_inv.unmap loc' h'
          exact this
        prb := fun idx r τ' h' => by
          have : getPlaceInfo cs idx = some (r, τ') := by
            show List.lookup _ _ = _
            rw [← h_prmR]; exact h'
          exact RegisterBelow.mono h_regmono (h_inv.prb idx r τ' this)
      }
    · cases h_step
  · cases h_step

end obseq3.byteproof
