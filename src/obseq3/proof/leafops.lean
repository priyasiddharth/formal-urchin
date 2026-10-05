import obseq3.proof.move
import obseq3.proof.chainb

/-!
# One-leaf reads: casts, exposure, pointer offsets

`ptrCast`, `exposeAddr`, `fromExposed` and `ptrOffset` all read ONE leaf
through a place (the source's `readCell`; the compiled code's
`Load (leafLayout k)` or `readCellThrough`) and compute a value from it.
`leaf_pkg_core` proves the package once: the place's lowering, the one
target instruction, the store. Each rvalue supplies only `LeafOpB`: its
source evaluation reads through the place, and its target instruction,
run on related states with the place's pointer in a register, produces
related values.
-/

namespace obseq3.proof

open obseq3 obseq3.bytes obseq3.proof
open obseq3.mirlite (MemValue Binding Env PlaceRes)
open obseq3.oseair (Val Register)
open obseq3.compile

/-- What an rvalue that reads one leaf through `src` supplies. -/
structure LeafOpB {Γ : Ctx} (L : mirlite.LayEnv Γ) (dstL : BLayout) {σ τ : LayoutTy}
    (rhs : RExpr Γ τ) (src : Place Γ σ) (mk : Register → oseair.Rhs) : Prop where
  resolves : ∀ (sM : mirlite.State MSB Γ) output,
    mirlite.evalRExpr MSB L sM dstL rhs = .ok output →
    ∃ r, mirlite.resolvePlaceAcc MSB L sM src = .ok r
  step : ∀ (ρt : TagRenameMap) (sM : mirlite.State MSB Γ) (s1 : oseair.State MSB)
    (reg : Register) (resolved : PlaceRes) (permsR : MSB.State) (ext : Nat) (tres : Tag) output,
    mirlite.evalRExpr MSB L sM dstL rhs = .ok output →
    mirlite.resolvePlaceAcc MSB L sM src = .ok (resolved, permsR) →
    TagRenameWF ρt → TagRenameBounded ρt permsR.NextTag s1.perms.NextTag →
    PermSim ρt permsR s1.perms → ByteMemSim ρt sM.mem s1.mem → ByteAllocLockstep sM.mem s1.mem →
    s1.reg.lookup reg = some [Val.Ptr resolved.allocBase (resolved.addr - resolved.allocBase) ext
      resolved.allocSizeB tres] →
    ρt resolved.tag = some tres → resolved.allocBase ≤ resolved.addr →
    ∃ vals p' perms₂, oseair.evalRhs MSB s1 (mk reg) = .Ok vals { s1 with perms := p' } ∧
      output.state = { sM with perms := perms₂ } ∧
      PermSim ρt perms₂ p' ∧ TagRenameBounded ρt perms₂.NextTag p'.NextTag ∧
      ListRel (StoreSim ρt) output.values (vals.map oseair.Val.toMem)

theorem runN_Assgn {compProg : oseair.Prog} {s s' : oseair.State MSB} {r : Register}
    {rhs : oseair.Rhs} {vals : List Val}
    (h_code : compProg s.pc = some (oseair.Instr.Assgn r rhs))
    (h_ev : oseair.evalRhs MSB s rhs = .Ok vals s') :
    oseair.runN MSB 1 s compProg = .Ok { s' with reg := s'.reg.insert r vals, pc := s.pc + 1 } := by
  simp only [oseair.runN, oseair.step, h_code, h_ev]

theorem leaf_pkg_core {Γ : Ctx} {L : mirlite.LayEnv Γ} {compProg : oseair.Prog}
    {dstL : BLayout} {σ τ : LayoutTy} {rhs : RExpr Γ τ} {src : Place Γ σ}
    {mk : Register → oseair.Rhs}
    {ev : (srcRes : PtrResult) → PlaceToRegEvidence L RefKind.Shared src srcRes →
      (dstPtr : Register) → RExprToEvidence L dstPtr rhs}
    (h_low : LowersB L compProg src) (h_comp : CompilesB L src) (h_op : LeafOpB L dstL rhs src mk)
    (h_pre : compileRExprPreChecked L dstL rhs = readRhsPre L dstL rhs src mk (fun _ => []) ev) :
    ValuePkgB compProg L dstL rhs := by
  intro ρt sM sA csA h_wf h_tbd h_lbs h_prb h_mem h_alloc h_psim h_pc _h_unmap output h_ev
  obtain ⟨⟨resolved, permsR⟩, h_res⟩ := h_op.resolves sM output h_ev
  have h_map : ∀ {τ' : LayoutTy} (loc : Local Γ τ') (b : Binding), sM.env.lookup loc = some b →
      ∃ reg layout, getPlaceInfo csA loc.idx.1 = some (reg, layout) := fun loc b h => by
    obtain ⟨r, t, hpi, -⟩ := h_lbs loc b h
    exact ⟨r, _, hpi⟩
  obtain ⟨sOut, h_sval, h_sclean, h_sprm⟩ :=
    h_comp sM csA RefKind.Shared _ h_map h_res
  obtain ⟨h_run, pOut, h_val, h_store, h_post⟩ :=
    readRhsPre_shape (dstL := dstL) (rhs := rhs) (mk := mk) (ev := ev) h_sval h_sclean
  rw [h_pre]
  refine ⟨_, pOut, h_val, h_store, h_post, by rw [h_run]; exact h_sprm, fun h_code => ?_⟩
  rw [h_run] at h_code ⊢
  obtain ⟨sOut', n1, s1, tres, hS⟩ :=
    h_low ρt sM RefKind.Shared csA sA resolved permsR h_wf h_res h_tbd
      h_lbs h_prb h_mem h_alloc h_psim h_pc
      (h_code.mono ((bumpReg_state_incr' _).trans (emit_state_incr _ _)))
  have h_same : sOut' = sOut := by
    have := hS.val
    rw [h_sval] at this
    exact (Except.ok.inj this).symm
  subst h_same
  obtain ⟨ext, h_entry⟩ := hS.entry
  have h_mem1 : ByteMemSim ρt sM.mem s1.mem := by rw [hS.mem]; exact h_mem
  have h_lock1 : ByteAllocLockstep sM.mem s1.mem := by rw [hS.mem]; exact h_alloc
  have h_tbd1 : TagRenameBounded ρt permsR.NextTag s1.perms.NextTag := by
    rw [hS.srcNT]; exact TagRenameBounded.mono h_tbd (Nat.le_refl _) hS.tgtNT
  obtain ⟨vals, p', perms₂, h_evT, h_ost, h_psim2, h_tbd2, h_rel⟩ :=
    h_op.step ρt sM s1 sOut'.result.reg resolved permsR ext tres output h_ev h_res h_wf h_tbd1
      hS.psim h_mem1 h_lock1 h_entry hS.rt hS.le
  have h_instr : compProg s1.pc = some (oseair.Instr.Assgn
      (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared src) csA).nextReg)
      (mk sOut'.result.reg)) := by
    rw [hS.pc]
    apply h_code
    · simp [emit]
    · simp [emit]
  have h_run1 := runN_Assgn h_instr h_evT
  refine ⟨ρt, n1 + 1, _, sM.mem, perms₂, vals, TagRenameIncr.refl ρt, h_wf, h_ost,
    runN_trans hS.run h_run1, ?_, ?_, h_psim2, h_tbd2, h_mem1, h_lock1, ?_, ?_, h_rel⟩
  · show csA.nextReg ≤ _ + 1
    exact Nat.le_trans hS.regmono (Nat.le_succ _)
  · refine LocalBindingSimB.prm_congr (h_lbs.of_frame h_prb fun r hr => ?_) hS.prm
    have hne := RegisterBelow.ne_fresh (RegisterBelow.mono hS.regmono hr)
    show (s1.reg.insert _ _).lookup r = _
    rw [RegMap.lookup_insert_ne _ _ hne]
    exact hS.frame r hr
  · show s1.pc + 1 = _
    rw [hS.pc]; rfl
  · exact StoreStepB.rstore compProg _ _ dstL _ vals (RegMap.lookup_insert_self _ _ _)
      (show _ < _ + 1 by omega)

/-! ## Reading one leaf on both sides -/

theorem readCell_inv {Γ : Ctx} {L : mirlite.LayEnv Γ} {sM : mirlite.State MSB Γ}
    {σ : LayoutTy} {src : Place Γ σ} {what : String} {v : MemValue} {perms' : MSB.State}
    (h : mirlite.readCell MSB L sM src what = .ok (v, perms')) :
    ∃ resolved permsR, mirlite.resolvePlaceAcc MSB L sM src = .ok (resolved, permsR) ∧
      ¬ sM.mem.isFreed resolved.allocBase = true ∧
      ¬ (resolved.addr + (mirlite.leafKind (mirlite.placeLayout L src)).sizeB
          > resolved.allocBase + resolved.allocSizeB) ∧
      sb_read permsR resolved.addr (mirlite.leafKind (mirlite.placeLayout L src)).sizeB
        resolved.tag = .ok perms' ∧
      v = mirlite.decodeV (mirlite.leafKind (mirlite.placeLayout L src))
        (sM.mem.read resolved.addr (mirlite.leafKind (mirlite.placeLayout L src)).sizeB) := by
  simp only [mirlite.readCell] at h
  cases h_r : mirlite.resolvePlaceAcc MSB L sM src with
  | error e => simp [h_r] at h
  | ok rr =>
  obtain ⟨resolved, permsR⟩ := rr
  simp only [h_r] at h
  split at h
  · cases h
  rename_i h_free
  split at h
  · cases h
  rename_i h_bnd
  split at h
  · cases h
  rename_i p hp
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨resolved, permsR, rfl, h_free, h_bnd, hp, rfl⟩

theorem readCellThrough_sim {ρt : TagRenameMap} (hwf : TagRenameWF ρt)
    {s1 : oseair.State MSB} {reg : Register} {resolved : PlaceRes} {extB : Nat} {tres : Tag}
    {mS : bytes.Mem} {permsR perms' : AccessPerms} {k : Scalar}
    (h_reg : s1.reg.lookup reg = some [Val.Ptr resolved.allocBase
      (resolved.addr - resolved.allocBase) extB resolved.allocSizeB tres])
    (h_rt : ρt resolved.tag = some tres) (h_le : resolved.allocBase ≤ resolved.addr)
    (h_psim : PermSim ρt permsR s1.perms) (h_mem : ByteMemSim ρt mS s1.mem)
    (h_lock : ByteAllocLockstep mS s1.mem)
    (h_free : ¬ mS.isFreed resolved.allocBase = true)
    (h_bnd : ¬ (resolved.addr + k.sizeB > resolved.allocBase + resolved.allocSizeB))
    (h_rd : sb_read permsR resolved.addr k.sizeB resolved.tag = .ok perms') :
    ∃ p2, oseair.readCellThrough MSB s1 reg k
        = .ok (oseair.ofMem (mirlite.decodeV k (s1.mem.read resolved.addr k.sizeB)), p2) ∧
      PermSim ρt perms' p2 ∧ p2.NextTag = s1.perms.NextTag ∧
      ValSim ρt (mirlite.decodeV k (mS.read resolved.addr k.sizeB))
        (mirlite.decodeV k (s1.mem.read resolved.addr k.sizeB)) := by
  obtain ⟨p2, h_rd', h_psim'⟩ := sb_read_respects_PermSim h_psim hwf h_rt h_rd
  have hA : resolved.allocBase + (resolved.addr - resolved.allocBase) = resolved.addr :=
    Nat.add_sub_cancel' h_le
  have h_freeT : s1.mem.isFreed resolved.allocBase = false := by
    simp only [bytes.Mem.isFreed, ← h_lock.2.2] at h_free ⊢
    simpa using h_free
  refine ⟨p2, ?_, h_psim', sb_read_NextTag h_rd', decodeV_sim hwf k (h_mem.read _ _)⟩
  simp only [oseair.readCellThrough, h_reg, hA, h_freeT, Bool.false_eq_true, if_false, h_bnd,
    PermissionModel.stackedBorrows, h_rd']

/-! ## Value inversions -/

theorem valSim_ptr {ρt : TagRenameMap} {b oB eB szB : Nat} {t : Tag} {w : MemValue}
    (h : ValSim ρt (.ptrVal b oB eB szB t) w) :
    ∃ t', w = .ptrVal b oB eB szB t' ∧ ρt t = some t' := by
  cases w with
  | undef => simp [ValSim, MemValSim, oseair.ofMem] at h
  | word _ => simp [ValSim, MemValSim, oseair.ofMem] at h
  | ptrVal b' o' e' s' t' =>
      simp only [ValSim, MemValSim, oseair.ofMem, idA, Option.some.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl, ht, -⟩ := h
      exact ⟨t', rfl, ht⟩

theorem valSim_word {ρt : TagRenameMap} {n : Nat} {w : MemValue}
    (h : ValSim ρt (.word n) w) : w = .word n := by
  cases w with
  | undef => simp [ValSim, MemValSim, oseair.ofMem] at h
  | word n' => simp only [ValSim, MemValSim, oseair.ofMem] at h; rw [h]
  | ptrVal _ _ _ _ _ => simp [ValSim, MemValSim, oseair.ofMem] at h

/-- Determinism of the source's access resolution, as the two
    hypotheses arrive. -/
theorem resolve_eq {Γ : Ctx} {L : mirlite.LayEnv Γ} {sM : mirlite.State MSB Γ}
    {σ : LayoutTy} {src : Place Γ σ} {r1 r2 : PlaceRes} {p1 p2 : MSB.State}
    (h1 : mirlite.resolvePlaceAcc MSB L sM src = .ok (r1, p1))
    (h2 : mirlite.resolvePlaceAcc MSB L sM src = .ok (r2, p2)) : r1 = r2 ∧ p1 = p2 := by
  rw [h1] at h2
  simp only [Except.ok.injEq, Prod.mk.injEq] at h2
  exact h2

/-! ## The instances -/

theorem exposeAddr_leafop {Γ : Ctx} {L : mirlite.LayEnv Γ} (dstL : BLayout) {σ : LayoutTy}
    (src : Place Γ (LayoutTy.PtrL σ)) :
    LeafOpB L dstL (RExpr.exposeAddr (t := tE) src) src
      (oseair.Rhs.ExposeAddr (mirlite.leafKind (mirlite.placeLayout L src))) where
  resolves sM output h := by
    simp only [mirlite.evalRExpr] at h
    split at h
    · cases h
    · rename_i h_rc
      obtain ⟨r, p, h_r, -⟩ := readCell_inv h_rc
      exact ⟨_, h_r⟩
    · cases h
  step ρt sM s1 reg resolved permsR ext tres output h h_res hwf h_tbd h_psim h_mem h_lock
      h_reg h_rt h_le := by
    simp only [mirlite.evalRExpr] at h
    split at h
    · cases h
    · rename_i base offset e sz tag perms' h_rc
      split at h
      · cases h
      rename_i perms'' h_exp
      simp only [mirlite.EvalResult.ok.injEq] at h
      subst h
      obtain ⟨r', p', h_r', h_free, h_bnd, h_rd, h_v⟩ := readCell_inv h_rc
      obtain ⟨rfl, rfl⟩ := resolve_eq h_res h_r'
      obtain ⟨p2, h_rct, h_psim2, h_nt2, h_vs⟩ :=
        readCellThrough_sim hwf h_reg h_rt h_le h_psim h_mem h_lock h_free h_bnd h_rd
      rw [← h_v] at h_vs
      obtain ⟨t', h_w, h_t⟩ := valSim_ptr h_vs
      obtain ⟨p3, h_expT, h_psim3⟩ := sb_expose_respects_PermSim h_psim2 hwf h_t h_exp
      refine ⟨[Val.Dat (base + offset)], p3, perms'', ?_, rfl,
        h_psim3, ?_, ⟨Or.inr ⟨by simp, rfl⟩, trivial⟩⟩
      · simp only [oseair.evalRhs]
        rw [h_rct, h_w]
        simp only [PermissionModel.stackedBorrows, oseair.ofMem]
        rw [h_expT]
      · rw [sb_expose_NextTag h_expT, sb_expose_NextTag h_exp, sb_read_NextTag h_rd, h_nt2]
        exact h_tbd
    · cases h

theorem fromExposed_leafop {Γ : Ctx} {L : mirlite.LayEnv Γ} (dstL : BLayout) {τ : LayoutTy}
    (src : Place Γ (LayoutTy.IntL tN)) :
    LeafOpB L dstL (RExpr.fromExposed (τ := τ) src) src
      (oseair.Rhs.FromExposed (mirlite.leafKind (mirlite.placeLayout L src))) where
  resolves sM output h := by
    simp only [mirlite.evalRExpr] at h
    split at h
    · cases h
    · rename_i h_rc
      obtain ⟨r, p, h_r, -⟩ := readCell_inv h_rc
      exact ⟨_, h_r⟩
    · cases h
  step ρt sM s1 reg resolved permsR ext tres output h h_res hwf h_tbd h_psim h_mem h_lock
      h_reg h_rt h_le := by
    simp only [mirlite.evalRExpr] at h
    split at h
    · cases h
    · rename_i n perms' h_rc
      simp only [mirlite.EvalResult.ok.injEq] at h
      subst h
      obtain ⟨r', p', h_r', h_free, h_bnd, h_rd, h_v⟩ := readCell_inv h_rc
      obtain ⟨rfl, rfl⟩ := resolve_eq h_res h_r'
      obtain ⟨p2, h_rct, h_psim2, h_nt2, h_vs⟩ :=
        readCellThrough_sim hwf h_reg h_rt h_le h_psim h_mem h_lock h_free h_bnd h_rd
      rw [← h_v] at h_vs
      have h_w := valSim_word h_vs
      have h_ao : s1.mem.allocOf n = sM.mem.allocOf n := by
        simp only [bytes.Mem.allocOf, h_lock.1]
      refine ⟨[Val.Ptr ((sM.mem.allocOf n).getD (n, 0)).1 (n - ((sM.mem.allocOf n).getD (n, 0)).1)
          (((sM.mem.allocOf n).getD (n, 0)).2 - (n - ((sM.mem.allocOf n).getD (n, 0)).1))
          ((sM.mem.allocOf n).getD (n, 0)).2 wildcardTag], p2, perms', ?_, rfl, h_psim2, ?_, ?_⟩
      · simp only [oseair.evalRhs]
        rw [h_rct, h_w]
        simp only [oseair.ofMem, h_ao]
      · rw [sb_read_NextTag h_rd, h_nt2]; exact h_tbd
      · refine ⟨Or.inr ⟨by simp, ?_⟩, trivial⟩
        simp only [ValSim, oseair.Val.toMem, oseair.ofMem, MemValSim, idA]
        exact ⟨trivial, trivial, trivial, trivial, hwf.2, fun _ _ => ⟨_, rfl⟩⟩
    · cases h

theorem ptrOffset_leafop {Γ : Ctx} {L : mirlite.LayEnv Γ} (dstL : BLayout) {σ τ : LayoutTy}
    (src : Place Γ (LayoutTy.PtrL σ)) (delta : Int) (inb : Bool) :
    LeafOpB L dstL (RExpr.ptrOffset (τ := τ) src delta inb) src
      (fun r => oseair.Rhs.PtrOffset (mirlite.leafKind (mirlite.placeLayout L src)) r
        (delta * ((mirlite.pointeeLayout L src).sizeB : Int)) inb) where
  resolves sM output h := by
    simp only [mirlite.evalRExpr] at h
    split at h
    · cases h
    · rename_i h_rc
      obtain ⟨r, p, h_r, -⟩ := readCell_inv h_rc
      exact ⟨_, h_r⟩
    · cases h
  step ρt sM s1 reg resolved permsR ext tres output h h_res hwf h_tbd h_psim h_mem h_lock
      h_reg h_rt h_le := by
    simp only [mirlite.evalRExpr] at h
    split at h
    · cases h
    · rename_i base offset e sz tag perms' h_rc
      split at h
      · cases h
      rename_i newOff h_off
      simp only [mirlite.EvalResult.ok.injEq] at h
      subst h
      obtain ⟨r', p', h_r', h_free, h_bnd, h_rd, h_v⟩ := readCell_inv h_rc
      obtain ⟨rfl, rfl⟩ := resolve_eq h_res h_r'
      obtain ⟨p2, h_rct, h_psim2, h_nt2, h_vs⟩ :=
        readCellThrough_sim hwf h_reg h_rt h_le h_psim h_mem h_lock h_free h_bnd h_rd
      rw [← h_v] at h_vs
      obtain ⟨t', h_w, h_t⟩ := valSim_ptr h_vs
      refine ⟨[Val.Ptr base newOff e sz t'], p2, perms', ?_, rfl, h_psim2, ?_, ?_⟩
      · simp only [oseair.evalRhs]
        rw [h_rct, h_w]
        simp only [oseair.ofMem, bytes.Mem.offsetPtr_congr h_lock.2.2, h_off]
      · rw [sb_read_NextTag h_rd, h_nt2]; exact h_tbd
      · refine ⟨Or.inr ⟨by simp, ?_⟩, trivial⟩
        simp only [ValSim, oseair.Val.toMem, oseair.ofMem, MemValSim, idA]
        exact ⟨trivial, trivial, trivial, trivial, h_t, fun _ _ => ⟨_, rfl⟩⟩
    · cases h

theorem leafLayout_sizeB (k : Scalar) : (leafLayout k).sizeB = k.sizeB := by
  cases k <;> rfl

theorem readL_leafLayout (m : bytes.Mem) (a : Nat) (k : Scalar) :
    mirlite.readL m a (leafLayout k) = [mirlite.decodeV k (m.read a k.sizeB)] := by
  cases k <;> simp [mirlite.readL, leafLayout, BLayout.leaves]

theorem ptrCast_leafop {Γ : Ctx} {L : mirlite.LayEnv Γ} (dstL : BLayout) {σ τ : LayoutTy}
    (src : Place Γ (LayoutTy.PtrL σ)) :
    LeafOpB L dstL (RExpr.ptrCast (τ := τ) src) src
      (oseair.Rhs.Load (leafLayout (mirlite.leafKind (mirlite.placeLayout L src)))) where
  resolves sM output h := by
    simp only [mirlite.evalRExpr] at h
    split at h
    · cases h
    · rename_i h_rc
      obtain ⟨r, p, h_r, -⟩ := readCell_inv h_rc
      exact ⟨_, h_r⟩
  step ρt sM s1 reg resolved permsR ext tres output h h_res hwf h_tbd h_psim h_mem h_lock
      h_reg h_rt h_le := by
    simp only [mirlite.evalRExpr] at h
    split at h
    · cases h
    · rename_i v perms' h_rc
      split at h
      · cases h
      rename_i h_def
      simp only [mirlite.EvalResult.ok.injEq] at h
      subst h
      obtain ⟨r', p', h_r', h_free, h_bnd, h_rd, h_v⟩ := readCell_inv h_rc
      obtain ⟨rfl, rfl⟩ := resolve_eq h_res h_r'
      obtain ⟨p2, h_rd', h_psim2⟩ := sb_read_respects_PermSim h_psim hwf h_rt h_rd
      have hv : v ≠ .undef := fun h' => h_def (by rw [h']; rfl)
      have h_vs := decodeV_sim hwf (mirlite.leafKind (mirlite.placeLayout L src))
        (h_mem.read resolved.addr (mirlite.leafKind (mirlite.placeLayout L src)).sizeB)
      rw [← h_v] at h_vs
      obtain ⟨h_defT, h_relS⟩ := readL_rel (vs := [v])
        (ws := [mirlite.decodeV (mirlite.leafKind (mirlite.placeLayout L src))
          (s1.mem.read resolved.addr (mirlite.leafKind (mirlite.placeLayout L src)).sizeB)])
        (show ListRel _ [v] [_] from ⟨h_vs, trivial⟩)
        (by simp only [List.any_cons, List.any_nil, Bool.or_false]
            exact Bool.eq_false_iff.mpr h_def)
      have hA : resolved.allocBase + (resolved.addr - resolved.allocBase) = resolved.addr :=
        Nat.add_sub_cancel' h_le
      have h_freeT : s1.mem.isFreed resolved.allocBase = false := by
        simp only [bytes.Mem.isFreed, ← h_lock.2.2] at h_free ⊢
        simpa using h_free
      refine ⟨_, p2, perms', ?_, rfl, h_psim2, ?_, h_relS⟩
      · simp only [oseair.evalRhs, h_reg, hA, h_freeT, Bool.false_eq_true, if_false,
          leafLayout_sizeB, h_bnd, PermissionModel.stackedBorrows, h_rd', readL_leafLayout,
          List.map_cons, List.map_nil]
        have h_defT' : ([oseair.ofMem (mirlite.decodeV (mirlite.leafKind (mirlite.placeLayout L src))
            (s1.mem.read resolved.addr (mirlite.leafKind (mirlite.placeLayout L src)).sizeB))].any
            fun v => v == Val.Undef) = false := h_defT
        rw [h_defT']
        rfl
      · rw [sb_read_NextTag h_rd, sb_read_NextTag h_rd']; exact h_tbd

/-! ## The packages -/

theorem exposeAddr_pkg {Γ : Ctx} {L : mirlite.LayEnv Γ} {compProg : oseair.Prog}
    (hWF : PtrPlacesWF L) (dstL : BLayout) {σ : LayoutTy}
    {src : Place Γ (LayoutTy.PtrL σ)} (h_chain : ChainB src) :
    ValuePkgB compProg L dstL (RExpr.exposeAddr (t := tE) src) :=
  leaf_pkg_core (ev := fun srcRes evd _ => RExprToEvidence.exposeAddr src srcRes evd)
    (chainB_lowers hWF h_chain) (chainB_compilesB h_chain) (exposeAddr_leafop dstL src) rfl

theorem fromExposed_pkg {Γ : Ctx} {L : mirlite.LayEnv Γ} {compProg : oseair.Prog}
    (hWF : PtrPlacesWF L) (dstL : BLayout) {τ : LayoutTy}
    {src : Place Γ (LayoutTy.IntL tN)} (h_chain : ChainB src) :
    ValuePkgB compProg L dstL (RExpr.fromExposed (τ := τ) src) :=
  leaf_pkg_core (ev := fun srcRes evd _ => RExprToEvidence.fromExposed src srcRes evd)
    (chainB_lowers hWF h_chain) (chainB_compilesB h_chain) (fromExposed_leafop dstL src) rfl

theorem ptrOffset_pkg {Γ : Ctx} {L : mirlite.LayEnv Γ} {compProg : oseair.Prog}
    (hWF : PtrPlacesWF L) (dstL : BLayout) {σ τ : LayoutTy}
    {src : Place Γ (LayoutTy.PtrL σ)} (h_chain : ChainB src) (delta : Int) (inb : Bool) :
    ValuePkgB compProg L dstL (RExpr.ptrOffset (τ := τ) src delta inb) :=
  leaf_pkg_core (ev := fun srcRes evd _ => RExprToEvidence.ptrOffset src delta inb srcRes evd)
    (chainB_lowers hWF h_chain) (chainB_compilesB h_chain) (ptrOffset_leafop dstL src delta inb)
    rfl

theorem ptrCast_pkg {Γ : Ctx} {L : mirlite.LayEnv Γ} {compProg : oseair.Prog}
    (hWF : PtrPlacesWF L) (dstL : BLayout) {σ τ : LayoutTy}
    {src : Place Γ (LayoutTy.PtrL σ)} (h_chain : ChainB src) :
    ValuePkgB compProg L dstL (RExpr.ptrCast (τ := τ) src) :=
  leaf_pkg_core (ev := fun srcRes evd _ => RExprToEvidence.ptrCast src srcRes evd)
    (chainB_lowers hWF h_chain) (chainB_compilesB h_chain) (ptrCast_leafop dstL src) rfl

end obseq3.proof
