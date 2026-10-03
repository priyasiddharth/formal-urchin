import obseq3.byteproof.refslice
import obseq3.proof.protectors
import obseq3.proof.dealloc

/-!
# The non-assignment statements: protectors and `dealloc`

`pushProtectors`/`popProtectors` act on the permission state only, with
the cell proof's `PermSim.pushFrame`/`PermSim.popFrame`. `dealloc` reads
the pointer (`readToReg_simB`), checks offset zero, frees through the
renamed tag (`sb_dealloc_respects_PermSim`), and on both sides writes the
block's bytes uninit and records the base as freed — so the memory and
lockstep relations survive by `ByteMemSim.write` of related (uninit)
bytes.
-/

namespace obseq3.byteproof

open obseq3 obseq3.bytes obseq3.proof
open obseq3.mirlite (MemValue Binding Env PlaceRes)
open obseq3.oseair (Val Register)
open obseq3.compileB

theorem compileStmt_single {Γ : Ctx} {L : mirliteB.LayEnv Γ} (cs : CompilerState) :
    CheckedCompilerM.run (compileStmtChecked L (Γ := Γ) .pushProtectors) cs
      = emit cs [oseairL.Instr.PushProt] ∧
    CheckedCompilerM.run (compileStmtChecked L (Γ := Γ) .popProtectors) cs
      = emit cs [oseairL.Instr.PopProt] := by
  refine ⟨?_, ?_⟩ <;>
  simp only [compileStmtChecked, CheckedCompilerM.run_bind, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_lift, CheckedCompilerM.run_pure] <;> rfl

theorem pushProt_simB {Γ : Ctx} {L : mirliteB.LayEnv Γ} {ρt : TagRenameMap}
    {s_mir s_mir' : mirliteB.State MSB Γ} {s_osea : oseairL.State MSB} {cs : CompilerState}
    (compProg : oseairL.Prog) (h_inv : InvAtB L ρt s_mir s_osea cs)
    (h_code : CodeIncludedB compProg (CheckedCompilerM.run (compileStmtChecked L .pushProtectors) cs))
    (h_step : mirliteB.stepStmt MSB L s_mir .pushProtectors = .ok s_mir') :
    ∃ (ρt' : TagRenameMap) (s_osea' : oseairL.State MSB) (n : Nat),
      TagRenameIncr ρt ρt' ∧ oseairL.runN MSB n s_osea compProg = .Ok s_osea' ∧
      InvAtB L ρt' s_mir' s_osea' (CheckedCompilerM.run (compileStmtChecked L .pushProtectors) cs) := by
  rw [(compileStmt_single cs).1] at h_code ⊢
  simp only [mirliteB.stepStmt, mirliteB.Result.ok.injEq] at h_step
  subst h_step
  have h_instr : compProg s_osea.pc = some oseairL.Instr.PushProt := by
    rw [h_inv.pc]; apply h_code <;> simp [emit]
  refine ⟨ρt, { s_osea with perms := MSB.pushFrame s_osea.perms, pc := s_osea.pc + 1 }, 1,
    TagRenameIncr.refl ρt, by simp only [oseairL.runN, oseairL.step, h_instr], ?_⟩
  exact {
    pc := by simp [emit, h_inv.pc]
    lbs := h_inv.lbs
    mem := h_inv.mem
    alloc := h_inv.alloc
    psim := PermSim.pushFrame h_inv.psim
    wf_t := h_inv.wf_t
    tbd := h_inv.tbd
    unmap := h_inv.unmap
    prb := h_inv.prb
  }

theorem popProt_simB {Γ : Ctx} {L : mirliteB.LayEnv Γ} {ρt : TagRenameMap}
    {s_mir s_mir' : mirliteB.State MSB Γ} {s_osea : oseairL.State MSB} {cs : CompilerState}
    (compProg : oseairL.Prog) (h_inv : InvAtB L ρt s_mir s_osea cs)
    (h_code : CodeIncludedB compProg (CheckedCompilerM.run (compileStmtChecked L .popProtectors) cs))
    (h_step : mirliteB.stepStmt MSB L s_mir .popProtectors = .ok s_mir') :
    ∃ (ρt' : TagRenameMap) (s_osea' : oseairL.State MSB) (n : Nat),
      TagRenameIncr ρt ρt' ∧ oseairL.runN MSB n s_osea compProg = .Ok s_osea' ∧
      InvAtB L ρt' s_mir' s_osea' (CheckedCompilerM.run (compileStmtChecked L .popProtectors) cs) := by
  rw [(compileStmt_single cs).2] at h_code ⊢
  simp only [mirliteB.stepStmt] at h_step
  split at h_step
  case h_2 => cases h_step
  rename_i p' h_pop
  simp only [mirliteB.Result.ok.injEq] at h_step
  subst h_step
  obtain ⟨tp', h_pop_t, h_psim', h_ntS, h_ntT⟩ := PermSim.popFrame h_inv.psim h_pop
  have h_instr : compProg s_osea.pc = some oseairL.Instr.PopProt := by
    rw [h_inv.pc]; apply h_code <;> simp [emit]
  refine ⟨ρt, { s_osea with perms := tp', pc := s_osea.pc + 1 }, 1,
    TagRenameIncr.refl ρt, by simp only [oseairL.runN, oseairL.step, h_instr, h_pop_t], ?_⟩
  exact {
    pc := by simp [emit, h_inv.pc]
    lbs := h_inv.lbs
    mem := h_inv.mem
    alloc := h_inv.alloc
    psim := h_psim'
    wf_t := h_inv.wf_t
    tbd := by show TagRenameBounded ρt p'.NextTag tp'.NextTag; rw [h_ntS, h_ntT]; exact h_inv.tbd
    unmap := h_inv.unmap
    prb := h_inv.prb
  }

/-! ## `dealloc` -/

theorem ByteMemSim.free {ρt : TagRenameMap} {mS mT : bytes.Mem}
    (h : ByteMemSim ρt mS mT) (base size : Nat) :
    ByteMemSim ρt { mS.write base (List.replicate size .uninit) with
                      freed := base :: (mS.write base (List.replicate size .uninit)).freed }
                  { mT.write base (List.replicate size .uninit) with
                      freed := base :: (mT.write base (List.replicate size .uninit)).freed } :=
  h.write base (ListRel.replicate (R := ByteSim ρt) (a := .uninit) (b := .uninit) trivial size)

theorem ByteAllocLockstep.free {mS mT : bytes.Mem} (h : ByteAllocLockstep mS mT) (base size : Nat) :
    ByteAllocLockstep { mS.write base (List.replicate size .uninit) with
                          freed := base :: (mS.write base (List.replicate size .uninit)).freed }
                      { mT.write base (List.replicate size .uninit) with
                          freed := base :: (mT.write base (List.replicate size .uninit)).freed } := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1, h2, by simp only [bytes.Mem.write]; rw [h3]⟩

theorem dealloc_simB {Γ : Ctx} {L : mirliteB.LayEnv Γ} {ρt : TagRenameMap}
    {s_mir s_mir' : mirliteB.State MSB Γ} {s_osea : oseairL.State MSB} {cs : CompilerState}
    {σ : LayoutTy} {dst : Place Γ (obseq.LayoutTy.PtrL σ)}
    (compProg : oseairL.Prog) (hWF : PtrPlacesWF L) (h_chain : PtrChain dst)
    (h_inv : InvAtB L ρt s_mir s_osea cs)
    (h_code : CodeIncludedB compProg (CheckedCompilerM.run (compileStmtChecked L (.dealloc dst)) cs))
    (h_step : mirliteB.stepStmt MSB L s_mir (.dealloc dst) = .ok s_mir') :
    ∃ (ρt' : TagRenameMap) (s_osea' : oseairL.State MSB) (n : Nat),
      TagRenameIncr ρt ρt' ∧ oseairL.runN MSB n s_osea compProg = .Ok s_osea' ∧
      InvAtB L ρt' s_mir' s_osea' (CheckedCompilerM.run (compileStmtChecked L (.dealloc dst)) cs) := by
  -- the source: read the pointer, check its offset, free
  simp only [mirliteB.stepStmt] at h_step
  split at h_step
  · cases h_step
  rename_i out h_e
  split at h_step
  case h_2 => cases h_step
  rename_i base offset e size tag h_v
  split at h_step
  · cases h_step
  rename_i h_off
  split at h_step
  · cases h_step
  rename_i permsD h_dealloc
  simp only [mirliteB.Result.ok.injEq] at h_step
  subst h_step
  have h_st := evalCopy_state h_e
  -- compile-time
  obtain ⟨sOut, h_sval, h_sclean, h_sprm⟩ := readToReg_compiles h_chain h_inv.lbs h_e
  obtain ⟨h_runR, h_valR⟩ := readToReg_shape h_sval h_sclean
  have h_shape : CheckedCompilerM.run (compileStmtChecked L (.dealloc dst)) cs
      = emit (CheckedCompilerM.run (readToReg L dst) cs)
          [oseairL.Instr.Dealloc
            (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared dst) cs).nextReg)] := by
    simp only [compileStmtChecked, CheckedCompilerM.run_bind, h_valR, CheckedCompilerM.run_lift,
      CheckedCompilerM.run_pure]
    rfl
  rw [h_shape] at h_code ⊢
  -- the read
  obtain ⟨n1, s1, vals, h_run1, h_inv1, -, h_r, -, h_rel, -, -⟩ :=
    readToReg_simB hWF h_chain h_inv h_e (h_code.mono (emit_state_incr _ _))
  rw [h_v] at h_rel
  obtain ⟨t', rfl, h_t⟩ := ptr_of_storeSim h_rel
  -- the free
  obtain ⟨p2, h_dealloc', h_psim', h_ntS, h_ntT⟩ :=
    sb_dealloc_respects_PermSim h_inv1.wf_t h_t size base h_inv1.psim h_dealloc
  have h_instr : compProg s1.pc = some (oseairL.Instr.Dealloc
      (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared dst) cs).nextReg)) := by
    rw [h_inv1.pc]; apply h_code <;> simp [emit]
  have h_run2 : oseairL.runN MSB 1 s1 compProg = .Ok
      { s1 with perms := p2,
                mem := { s1.mem.write base (List.replicate size .uninit) with
                          freed := base :: (s1.mem.write base (List.replicate size .uninit)).freed },
                pc := s1.pc + 1 } := by
    simp only [oseairL.runN, oseairL.step, h_instr, h_r, h_off, Bool.false_eq_true, if_false,
      PermissionModel.stackedBorrows, h_dealloc']
  refine ⟨ρt, _, n1 + 1, TagRenameIncr.refl ρt, runN_trans h_run1 h_run2, ?_⟩
  exact {
    pc := by
      show s1.pc + 1 = _
      rw [h_inv1.pc]; rfl
    lbs := h_inv1.lbs
    mem := h_inv1.mem.free base size
    alloc := h_inv1.alloc.free base size
    psim := h_psim'
    wf_t := h_inv1.wf_t
    tbd := by
      show TagRenameBounded ρt permsD.NextTag p2.NextTag
      rw [h_ntS, h_ntT]; exact h_inv1.tbd
    unmap := h_inv1.unmap
    prb := fun idx r τ' h => RegisterBelow.mono (Nat.le_refl _) (h_inv1.prb idx r τ' h)
  }

end obseq3.byteproof
