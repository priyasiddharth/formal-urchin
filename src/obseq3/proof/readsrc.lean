import obseq3.proof.readreg
import obseq3.proof.assoc
import obseq3.proof.chainb

/-!
# Reading from a field

A copy-read of `b.f` (`b` a pointer chain): at byte offset zero the field
lowers as its base (`proj_zero_lowers`, `proj_zero_compiles`); at a
nonzero offset the compiled read is `Borrow(Shared); Load; Die` through
the borrow temporary, which keystone's `sb_ref_read_die_cancels` (at the
field's byte length) shows is the source's one read through the base's
tag (`readToReg_projoff_simB`). `ReadSrcB` — a chain, or a field of one —
is what every register read now accepts (`readToReg_simR`).
-/

namespace obseq3.proof

open obseq3 obseq3.bytes obseq3.proof
open obseq3.mirlite (MemValue Binding Env PlaceRes)
open obseq3.oseair (Val Register)
open obseq3.compile

theorem proj_zero_compiles {Γ : Ctx} {L : mirlite.LayEnv Γ} {ρ τ : LayoutTy} {b : Place Γ ρ}
    (f : PathTo ρ τ)
    (h_np : ∀ (σ' : LayoutTy) (bb : Place Γ σ') (q : PathTo σ' ρ), b = bb.proj q → False)
    (h0 : pathOffset L b f = 0) (hb : CompilesB L b) : CompilesB L (.proj b f) := by
  intro s cs kind r h_map h_res
  simp only [mirlite.resolvePlaceAcc] at h_res
  cases h_rb : mirlite.resolvePlaceAcc MSB L s b with
  | error e => simp [h_rb] at h_res
  | ok rb =>
  obtain ⟨bOut, h_bval, h_bclean, h_bprm⟩ := hb s cs kind rb h_map h_rb
  obtain ⟨h_run, outP, h_valP, h_resP⟩ := (proj_lowering (kind := kind) f h_np h_bval).1 h0
  exact ⟨outP, h_valP, by rw [h_resP]; exact h_bclean, by rw [h_run]; exact h_bprm⟩

/-- `readToReg`'s value and the facts consumers need, for any lowering. -/
theorem readToReg_factsG {Γ : Ctx} {L : mirlite.LayEnv Γ} {σ : LayoutTy} {p : Place Γ σ}
    {cs : CompilerState}
    {sOut : ResultWithEvidence PtrResult (PlaceToRegEvidence L RefKind.Shared p)}
    (h_sval : CheckedCompilerM.value (placeToRegChecked L RefKind.Shared p) cs = .ok sOut) :
    CheckedCompilerM.run (readToReg L p) cs
      = emit (bumpReg (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared p) cs))
          ([oseair.Instr.Assgn
            (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared p) cs).nextReg)
            (oseair.Rhs.Load (mirlite.placeLayout L p) sOut.result.reg)] ++
            cleanupInstrs sOut.result.cleanup) ∧
    CheckedCompilerM.value (readToReg L p) cs
      = .ok (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared p) cs).nextReg) := by
  simp only [readToReg, CheckedCompilerM.run_bind, CheckedCompilerM.value_bind, h_sval,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift, CheckedCompilerM.run_pure,
    CheckedCompilerM.value_pure]
  exact ⟨rfl, rfl⟩

theorem readToReg_projoff_simB {Γ : Ctx} {L : mirlite.LayEnv Γ} {ρt : TagRenameMap}
    {compProg : oseair.Prog}
    {sM : mirlite.State MSB Γ} {sA : oseair.State MSB} {cs : CompilerState}
    {ρ τ : LayoutTy} {b : Place Γ ρ} {f : PathTo ρ τ} {out : mirlite.EvalOutput MSB Γ}
    (h_np : ∀ (σ' : LayoutTy) (bb : Place Γ σ') (q : PathTo σ' ρ), b = bb.proj q → False)
    (h0 : pathOffset L b f ≠ 0) (hb : LowersB L compProg b) (hcb : CompilesB L b)
    (h_inv : InvAtB L ρt sM sA cs)
    (h_ev : mirlite.evalCopy MSB L sM (.proj b f) = .ok out)
    (h_code : CodeIncludedB compProg (CheckedCompilerM.run (readToReg L (.proj b f)) cs)) :
    ∃ n s' vals, oseair.runN MSB n sA compProg = .Ok s' ∧
      InvAtB L ρt out.state s' (CheckedCompilerM.run (readToReg L (.proj b f)) cs) ∧
      out.state = { sM with perms := out.state.perms } ∧
      s'.reg.lookup
        (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared (.proj b f)) cs).nextReg)
        = some vals ∧
      CheckedCompilerM.value (readToReg L (.proj b f)) cs
        = .ok (Register.R
            (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared (.proj b f)) cs).nextReg) ∧
      ListRel (StoreSim ρt) out.values (vals.map oseair.Val.toMem) ∧
      cs.nextReg ≤ (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared (.proj b f)) cs).nextReg ∧
      (∀ r, RegisterBelow cs.nextReg r → s'.reg.lookup r = sA.reg.lookup r) := by
  -- the source read of the field
  simp only [mirlite.evalCopy] at h_ev
  cases h_res : mirlite.resolvePlaceAcc MSB L sM (.proj b f) with
  | error e => simp [h_res] at h_ev
  | ok rr =>
  obtain ⟨resolved, permsR⟩ := rr
  simp only [h_res] at h_ev
  split at h_ev
  · cases h_ev
  rename_i h_free
  split at h_ev
  · cases h_ev
  rename_i h_bnd
  split at h_ev
  · cases h_ev
  rename_i permsR' h_rd
  split at h_ev
  · cases h_ev
  rename_i h_def
  simp only [mirlite.EvalResult.ok.injEq] at h_ev
  subst h_ev
  obtain ⟨⟨bRes, permsB⟩, h_rb, h_addr, h_tag, h_ab, h_as, h_pb⟩ :=
    borrow_proj_res (L := L) f sM _ h_res
  simp only at h_addr h_tag h_ab h_as h_pb
  subst h_pb
  -- compile-time
  obtain ⟨bOut, h_bval, h_bclean, h_bprm⟩ := hcb sM cs RefKind.Shared _ (fun loc bnd h => by
    obtain ⟨r, t, hpi, -⟩ := h_inv.lbs loc bnd h
    exact ⟨r, _, hpi⟩) h_rb
  obtain ⟨h_runP, outP, h_valP, h_resP⟩ :=
    (proj_lowering (kind := RefKind.Shared) f h_np h_bval).2 h0
  obtain ⟨h_runR, h_valR⟩ := readToReg_factsG h_valP
  rw [h_resP, h_bclean, h_runP] at h_runR
  simp only [List.nil_append, cleanupInstrs, List.reverse_cons, List.reverse_nil,
    List.map_cons, List.map_nil] at h_runR
  rw [h_runR] at h_code ⊢
  -- the base's lowering
  obtain ⟨bOut', n1, s1, tres, hB⟩ :=
    hb ρt sM RefKind.Shared cs sA bRes permsR h_inv.wf_t h_rb h_inv.tbd h_inv.lbs h_inv.prb
      h_inv.mem h_inv.alloc h_inv.psim h_inv.pc
      (h_code.mono (((bumpReg_state_incr' _).trans (emit_state_incr _ _)).trans
        ((bumpReg_state_incr' _).trans (emit_state_incr _ _))))
  have h_same : bOut' = bOut := by
    have := hB.val
    rw [h_bval] at this
    exact (Except.ok.inj this).symm
  subst h_same
  obtain ⟨ext, h_bentry⟩ := hB.entry
  have hA : bRes.allocBase + (bRes.addr - bRes.allocBase) = bRes.addr :=
    Nat.add_sub_cancel' hB.le
  have h_mem1 : ByteMemSim ρt sM.mem s1.mem := by rw [hB.mem]; exact h_inv.mem
  have h_lock1 : ByteAllocLockstep sM.mem s1.mem := by rw [hB.mem]; exact h_inv.alloc
  have h_freeT : s1.mem.isFreed bRes.allocBase = false := by
    rw [h_ab] at h_free
    simp only [bytes.Mem.isFreed, ← h_lock1.2.2] at h_free ⊢
    simpa using h_free
  have h_bnd' : bRes.addr + pathOffset L b f + placeSize L (.proj b f)
      ≤ bRes.allocBase + bRes.allocSizeB := by
    rw [← h_ab, ← h_as]
    have := Nat.le_of_not_gt h_bnd
    rw [h_addr] at this
    exact this
  -- the read, transported; the target's Shared retag; the cancellation
  rw [h_addr, h_tag] at h_rd
  obtain ⟨p2, h_rd', h_psim2⟩ := sb_read_respects_PermSim hB.psim h_inv.wf_t hB.rt h_rd
  obtain ⟨q1, h_ref⟩ := sb_ref_Shared_ok_of_sb_read_ok h_rd'
  have h_tbd_mid : TagRenameBounded ρt permsR.NextTag s1.perms.NextTag := by
    rw [hB.srcNT]; exact TagRenameBounded.mono h_inv.tbd (Nat.le_refl _) hB.tgtNT
  have h_unprot := freshTag_not_protected hB.psim h_tbd_mid
  have h0w : wildcardTag < s1.perms.NextTag := (h_tbd_mid _ _ h_inv.wf_t.2).2
  have h_ntw : (s1.perms.NextTag == wildcardTag) = false := by
    simp only [beq_eq_false_iff_ne]; exact (Nat.ne_of_lt h0w).symm
  obtain ⟨q2, q3, sAcc, h_rd1, h_die1, h_rd2, h_sm, h_ex, h_pf, h_ntle, h_wk⟩ :=
    sb_ref_read_die_cancels h_ntw h_unprot h_ref
  have h_acc : sAcc = p2 := Except.ok.inj (h_rd2.symm.trans h_rd')
  subst h_acc
  -- the values
  have hrel := readL_sim h_inv.wf_t h_mem1 (bRes.addr + pathOffset L b f)
    (mirlite.placeLayout L (.proj b f))
  obtain ⟨h_defT, h_relS⟩ := readL_rel hrel (by rw [h_addr] at h_def; simpa using h_def)
  -- the code
  have hct := code_borrow_load_die (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared b) cs)
  have h_at : ∀ k i, k < 3 →
      (emit (bumpReg (emit (bumpReg (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared b) cs))
        [oseair.Instr.Assgn
          (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared b) cs).nextReg)
          (borrowRhs RefKind.Shared (placeSize L (.proj b f)) bOut'.result.reg (pathOffset L b f))]))
        ([oseair.Instr.Assgn
          (Register.R ((CheckedCompilerM.run (placeToRegChecked L RefKind.Shared b) cs).nextReg + 1))
          (oseair.Rhs.Load (mirlite.placeLayout L (.proj b f))
            (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared b) cs).nextReg))] ++
        [oseair.Instr.Die
          (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared b) cs).nextReg)
          (placeSize L (.proj b f))])).code (s1.pc + k) = some i →
      compProg (s1.pc + k) = some i := by
    intro k i hk hc
    refine h_code _ i ?_ hc
    rw [(hct _ _ _).2.2.2, hB.pc]; omega
  let tmp := Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared b) cs).nextReg
  let ld := Register.R ((CheckedCompilerM.run (placeToRegChecked L RefKind.Shared b) cs).nextReg + 1)
  have hn : (mirlite.placeLayout L (.proj b f)).size = placeSize L (.proj b f) := rfl
  -- §1 Borrow
  have h1 := runN_Borrow (s := s1) (h_at 0 _ (by omega) (by rw [hB.pc]; exact (hct _ _ _).1))
    h_bentry h_freeT (by rw [hA]; exact h_bnd') (by rw [hA]; exact h_ref)
  -- §2 Load through the fresh tag
  let vals := (mirlite.readL s1.mem (bRes.addr + pathOffset L b f)
    (mirlite.placeLayout L (.proj b f))).map oseair.ofMem
  let S1 : oseair.State MSB :=
    { s1 with
        perms := q1,
        reg := s1.reg.insert tmp
          [Val.Ptr bRes.allocBase (bRes.addr - bRes.allocBase + pathOffset L b f)
            (placeSize L (.proj b f)) bRes.allocSizeB s1.perms.NextTag],
        pc := s1.pc + 1 }
  have hA' : bRes.allocBase + (bRes.addr - bRes.allocBase + pathOffset L b f)
      = bRes.addr + pathOffset L b f := by rw [← Nat.add_assoc, hA]
  have h2 : oseair.runN MSB 1 S1 compProg = .Ok
      { S1 with perms := q2, reg := S1.reg.insert ld vals, pc := S1.pc + 1 } := by
    have h_nb : ¬ (bRes.allocBase + (bRes.addr - bRes.allocBase + pathOffset L b f)
        + (mirlite.placeLayout L (.proj b f)).size > bRes.allocBase + bRes.allocSizeB) := by
      rw [hA', hn]; exact Nat.not_lt.mpr h_bnd'
    have h_instr := h_at 1 _ (by omega) (by rw [hB.pc]; exact (hct _ _ _).2.1)
    simp only [oseair.runN, oseair.step]
    rw [show S1.pc = s1.pc + 1 from rfl, h_instr]
    simp only [oseair.evalRhs, S1, tmp, RegMap.lookup_insert_self, h_freeT, Bool.false_eq_true,
      if_false, h_nb, PermissionModel.stackedBorrows]
    rw [hA', hn]
    simp only [h_rd1, h_defT, Bool.false_eq_true, if_false]
    rfl
  -- §3 Die
  let S2 : oseair.State MSB :=
    { S1 with perms := q2, reg := S1.reg.insert ld vals, pc := S1.pc + 1 }
  have hne : tmp ≠ ld := by simp [tmp, ld]
  have h3 := runN_Die (s := S2) (h_at 2 _ (by omega) (by rw [hB.pc]; exact (hct _ _ _).2.2.1))
    (by
      show (S1.reg.insert ld vals).lookup tmp = _
      rw [RegMap.lookup_insert_ne _ _ hne]
      exact RegMap.lookup_insert_self _ _ _)
    (by rw [hA']; exact h_die1)
  have h_frame : ∀ r, RegisterBelow cs.nextReg r →
      ((s1.reg.insert tmp [Val.Ptr bRes.allocBase (bRes.addr - bRes.allocBase + pathOffset L b f)
        (placeSize L (.proj b f)) bRes.allocSizeB s1.perms.NextTag]).insert ld vals).lookup r
        = sA.reg.lookup r := fun r hr => by
    have hr' := RegisterBelow.mono hB.regmono hr
    have hne1 : r ≠ tmp := RegisterBelow.ne_fresh hr'
    have hne2 : r ≠ ld := RegisterBelow.ne_fresh (RegisterBelow.mono (Nat.le_succ _) hr')
    rw [RegMap.lookup_insert_ne _ _ hne2, RegMap.lookup_insert_ne _ _ hne1]
    exact hB.frame r hr
  refine ⟨n1 + 1 + 1 + 1, { S2 with perms := q3, pc := S2.pc + 1 }, vals,
    runN_trans (runN_trans (runN_trans hB.run h1) h2) h3, ?_, rfl,
    by rw [h_runP]; exact RegMap.lookup_insert_self _ _ _, by rw [h_valR],
    by rw [h_addr]; exact h_relS,
    by rw [h_runP]; show _ ≤ _ + 1; exact Nat.le_trans hB.regmono (Nat.le_succ _), h_frame⟩
  exact {
    pc := by
      show s1.pc + 1 + 1 + 1 = _
      rw [(hct _ _ _).2.2.2, hB.pc]
    lbs := LocalBindingSimB.prm_congr (LocalBindingSimB.of_frame h_inv.lbs h_inv.prb h_frame) hB.prm
    mem := h_mem1
    alloc := h_lock1
    psim := ⟨by rw [h_sm]; exact h_psim2.1, by rw [h_pf]; exact h_psim2.2.1,
      by rw [h_ex]; exact h_psim2.2.2.1, Nat.le_trans h_psim2.2.2.2.1 h_ntle,
      by rw [h_wk]; exact h_psim2.2.2.2.2⟩
    wf_t := h_inv.wf_t
    tbd := by
      show TagRenameBounded ρt permsR'.NextTag q3.NextTag
      rw [sb_read_NextTag h_rd, hB.srcNT]
      refine TagRenameBounded.mono h_inv.tbd (Nat.le_refl _) (Nat.le_trans hB.tgtNT ?_)
      rw [← sb_read_NextTag h_rd']; exact h_ntle
    unmap := fun loc h => by
      have : getPlaceInfo (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared b) cs)
          loc.idx.1 = none := by
        show List.lookup _ _ = _
        rw [hB.prm]; exact h_inv.unmap loc h
      exact this
    prb := fun idx r τ' h => by
      have : getPlaceInfo cs idx = some (r, τ') := by
        show List.lookup _ _ = _
        rw [← hB.prm]; exact h
      exact RegisterBelow.mono (Nat.le_trans hB.regmono (by show _ ≤ _ + 1 + 1; omega))
        (h_inv.prb idx r τ' this)
  }

/-! ## Read sources: a chain, or a field of one -/

inductive ReadSrc0 {Γ : Ctx} : {τ : LayoutTy} → Place Γ τ → Prop
  | chain {τ : LayoutTy} {p : Place Γ τ} : ChainB p → ReadSrc0 p
  | field {ρ τ : LayoutTy} {b : Place Γ ρ} (f : PathTo ρ τ) : ChainB b → ReadSrc0 (.proj b f)

/-- Compile-time facts of a register read: its value register, the place
    map untouched, one register past the place's lowering. -/
theorem readToReg_factsR0 {Γ : Ctx} {L : mirlite.LayEnv Γ} {ρt : TagRenameMap}
    {sM : mirlite.State MSB Γ} {sA : oseair.State MSB} {cs : CompilerState}
    {σ : LayoutTy} {p : Place Γ σ} {out : mirlite.EvalOutput MSB Γ}
    (h : ReadSrc0 p) (h_lbs : LocalBindingSimB L ρt sM.env sA cs)
    (h_ev : mirlite.evalCopy MSB L sM p = .ok out) :
    CheckedCompilerM.value (readToReg L p) cs
      = .ok (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared p) cs).nextReg) ∧
    (CheckedCompilerM.run (readToReg L p) cs).placeRegMap = cs.placeRegMap ∧
    (CheckedCompilerM.run (readToReg L p) cs).nextReg
      = (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared p) cs).nextReg + 1 := by
  have h_map : ∀ {τ' : LayoutTy} (loc : Local Γ τ') (b : Binding), sM.env.lookup loc = some b →
      ∃ reg layout, getPlaceInfo cs loc.idx.1 = some (reg, layout) := fun loc b h => by
    obtain ⟨r, t, hpi, -⟩ := h_lbs loc b h
    exact ⟨r, _, hpi⟩
  obtain ⟨r, h_r⟩ := evalCopy_resolves h_ev
  -- the place's lowering compiles, with the place map untouched
  have h_low : ∃ sOut, CheckedCompilerM.value (placeToRegChecked L RefKind.Shared p) cs = .ok sOut ∧
      (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared p) cs).placeRegMap
        = cs.placeRegMap := by
    cases h with
    | chain hc =>
        obtain ⟨o, h1, -, h3⟩ := chainB_compiles h_map hc RefKind.Shared r h_r
        exact ⟨o, h1, h3⟩
    | field f hb =>
        rename_i ρ b
        have h_np := ChainB.not_proj hb
        simp only [mirlite.resolvePlaceAcc] at h_r
        cases h_rb : mirlite.resolvePlaceAcc MSB L sM b with
        | error e => simp [h_rb] at h_r
        | ok rb =>
        obtain ⟨bOut, h_bval, -, h_bprm⟩ := chainB_compiles h_map hb RefKind.Shared rb h_rb
        obtain ⟨hz, hnz⟩ := proj_lowering (kind := RefKind.Shared) f h_np h_bval
        by_cases h0 : pathOffset L b f = 0
        · obtain ⟨h_run, o, h_v, -⟩ := hz h0
          exact ⟨o, h_v, by rw [h_run]; exact h_bprm⟩
        · obtain ⟨h_run, o, h_v, -⟩ := hnz h0
          exact ⟨o, h_v, by rw [h_run]; exact h_bprm⟩
  obtain ⟨sOut, h_sval, h_sprm⟩ := h_low
  obtain ⟨h_run, h_val⟩ := readToReg_factsG h_sval
  refine ⟨h_val, ?_, ?_⟩
  · rw [h_run]; exact h_sprm
  · rw [h_run]; rfl

theorem readToReg_simR0 {Γ : Ctx} {L : mirlite.LayEnv Γ} {ρt : TagRenameMap}
    {compProg : oseair.Prog} (hWF : PtrPlacesWF L)
    {sM : mirlite.State MSB Γ} {sA : oseair.State MSB} {cs : CompilerState}
    {σ : LayoutTy} {p : Place Γ σ} {out : mirlite.EvalOutput MSB Γ}
    (h : ReadSrc0 p) (h_inv : InvAtB L ρt sM sA cs)
    (h_ev : mirlite.evalCopy MSB L sM p = .ok out)
    (h_code : CodeIncludedB compProg (CheckedCompilerM.run (readToReg L p) cs)) :
    ∃ n s' vals, oseair.runN MSB n sA compProg = .Ok s' ∧
      InvAtB L ρt out.state s' (CheckedCompilerM.run (readToReg L p) cs) ∧
      out.state = { sM with perms := out.state.perms } ∧
      s'.reg.lookup
        (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared p) cs).nextReg)
        = some vals ∧
      CheckedCompilerM.value (readToReg L p) cs
        = .ok (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared p) cs).nextReg) ∧
      ListRel (StoreSim ρt) out.values (vals.map oseair.Val.toMem) ∧
      cs.nextReg ≤ (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared p) cs).nextReg ∧
      (∀ r, RegisterBelow cs.nextReg r → s'.reg.lookup r = sA.reg.lookup r) := by
  cases h with
  | chain hc => exact readToReg_simG (chainB_lowers hWF hc) (chainB_compilesB hc) h_inv h_ev h_code
  | field f hb =>
      rename_i ρ b
      have h_np := ChainB.not_proj hb
      by_cases h0 : pathOffset L b f = 0
      · exact readToReg_simG (proj_zero_lowers f h_np h0 (chainB_lowers hWF hb))
          (proj_zero_compiles f h_np h0 (chainB_compilesB hb)) h_inv h_ev h_code
      · exact readToReg_projoff_simB h_np h0 (chainB_lowers hWF hb) (chainB_compilesB hb)
          h_inv h_ev h_code

/-! ## Nested fields -/

/-- Read sources: a chain, a field of one, and nestings of fields
    (`x.f.g` reads as `x.(f ++ g)`). -/
inductive ReadSrcB {Γ : Ctx} : {τ : LayoutTy} → Place Γ τ → Prop
  | base {τ : LayoutTy} {p : Place Γ τ} : ReadSrc0 p → ReadSrcB p
  | nested {ρ σ τ : LayoutTy} {b : Place Γ ρ} {q : PathTo ρ σ} {p : PathTo σ τ} :
      ReadSrcB (.proj b (q.append p)) → ReadSrcB (.proj (.proj b q) p)

theorem evalCopy_assoc {Γ : Ctx} {L : mirlite.LayEnv Γ} (s : mirlite.State MSB Γ)
    {ρ σ τ : LayoutTy} (b : Place Γ ρ) (q : PathTo ρ σ) (p : PathTo σ τ) :
    mirlite.evalCopy MSB L s (.proj (.proj b q) p) = mirlite.evalCopy MSB L s (.proj b (q.append p)) := by
  simp only [mirlite.evalCopy, placeLayout_assoc, resolvePlaceAcc_assoc]

theorem readToReg_assoc {Γ : Ctx} {L : mirlite.LayEnv Γ} {ρ σ τ : LayoutTy}
    (b : Place Γ ρ) (q : PathTo ρ σ) (p : PathTo σ τ) (cs : CompilerState) :
    CheckedCompilerM.run (readToReg L (.proj (.proj b q) p)) cs
      = CheckedCompilerM.run (readToReg L (.proj b (q.append p))) cs ∧
    CheckedCompilerM.value (readToReg L (.proj (.proj b q) p)) cs
      = CheckedCompilerM.value (readToReg L (.proj b (q.append p))) cs := by
  obtain ⟨h_run, h_val⟩ := placeToReg_assoc (L := L) RefKind.Shared b q p cs
  cases h1 : CheckedCompilerM.value (placeToRegChecked L RefKind.Shared (.proj (.proj b q) p)) cs with
  | ok o1 =>
      cases h2 : CheckedCompilerM.value (placeToRegChecked L RefKind.Shared (.proj b (q.append p))) cs with
      | ok o2 =>
          rw [h1, h2] at h_val
          simp only [Except.map, Except.ok.injEq] at h_val
          obtain ⟨hr1, hv1⟩ := readToReg_factsG h1
          obtain ⟨hr2, hv2⟩ := readToReg_factsG h2
          rw [hr1, hr2, hv1, hv2, h_run, h_val, placeLayout_assoc]
          exact ⟨by first | rfl | trivial, by first | rfl | trivial⟩
      | error e => rw [h1, h2] at h_val; simp [Except.map] at h_val
  | error e =>
      cases h2 : CheckedCompilerM.value (placeToRegChecked L RefKind.Shared (.proj b (q.append p))) cs with
      | ok o2 => rw [h1, h2] at h_val; simp [Except.map] at h_val
      | error e' =>
          rw [h1, h2] at h_val
          simp only [Except.map, Except.error.injEq] at h_val
          subst h_val
          simp only [readToReg, CheckedCompilerM.run_bind, CheckedCompilerM.value_bind, h1, h2, h_run]
          exact ⟨by first | rfl | trivial, by first | rfl | trivial⟩

theorem readToReg_factsR {Γ : Ctx} {L : mirlite.LayEnv Γ} {ρt : TagRenameMap}
    {sM : mirlite.State MSB Γ} {sA : oseair.State MSB} {cs : CompilerState}
    {σ : LayoutTy} {p : Place Γ σ} {out : mirlite.EvalOutput MSB Γ}
    (h : ReadSrcB p) (h_lbs : LocalBindingSimB L ρt sM.env sA cs)
    (h_ev : mirlite.evalCopy MSB L sM p = .ok out) :
    CheckedCompilerM.value (readToReg L p) cs
      = .ok (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared p) cs).nextReg) ∧
    (CheckedCompilerM.run (readToReg L p) cs).placeRegMap = cs.placeRegMap ∧
    (CheckedCompilerM.run (readToReg L p) cs).nextReg
      = (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared p) cs).nextReg + 1 := by
  induction h with
  | base h0 => exact readToReg_factsR0 h0 h_lbs h_ev
  | nested _ ih =>
      rename_i b q p' _
      rw [(readToReg_assoc b q p' cs).1, (readToReg_assoc b q p' cs).2,
        (placeToReg_assoc (L := L) RefKind.Shared b q p' cs).1]
      exact ih (by rw [← evalCopy_assoc]; exact h_ev)

theorem readToReg_simR {Γ : Ctx} {L : mirlite.LayEnv Γ} {ρt : TagRenameMap}
    {compProg : oseair.Prog} (hWF : PtrPlacesWF L)
    {sM : mirlite.State MSB Γ} {sA : oseair.State MSB} {cs : CompilerState}
    {σ : LayoutTy} {p : Place Γ σ} {out : mirlite.EvalOutput MSB Γ}
    (h : ReadSrcB p) (h_inv : InvAtB L ρt sM sA cs)
    (h_ev : mirlite.evalCopy MSB L sM p = .ok out)
    (h_code : CodeIncludedB compProg (CheckedCompilerM.run (readToReg L p) cs)) :
    ∃ n s' vals, oseair.runN MSB n sA compProg = .Ok s' ∧
      InvAtB L ρt out.state s' (CheckedCompilerM.run (readToReg L p) cs) ∧
      out.state = { sM with perms := out.state.perms } ∧
      s'.reg.lookup
        (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared p) cs).nextReg)
        = some vals ∧
      CheckedCompilerM.value (readToReg L p) cs
        = .ok (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared p) cs).nextReg) ∧
      ListRel (StoreSim ρt) out.values (vals.map oseair.Val.toMem) ∧
      cs.nextReg ≤ (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared p) cs).nextReg ∧
      (∀ r, RegisterBelow cs.nextReg r → s'.reg.lookup r = sA.reg.lookup r) := by
  induction h with
  | base h0 => exact readToReg_simR0 hWF h0 h_inv h_ev h_code
  | nested _ ih =>
      rename_i b q p' _
      rw [(readToReg_assoc b q p' cs).1] at h_code ⊢
      rw [(readToReg_assoc b q p' cs).2, (placeToReg_assoc (L := L) RefKind.Shared b q p' cs).1]
      exact ih (by rw [← evalCopy_assoc]; exact h_ev) h_code

/-! ## Copy from any read source -/

/-- `copy`'s pre-phase is `readToReg`'s code exactly; its store writes
    the read register. -/
theorem copy_pre_eq {Γ : Ctx} {L : mirlite.LayEnv Γ} {dstL : BLayout} {σ : LayoutTy}
    {src : Place Γ σ} {cs : CompilerState} :
    CheckedCompilerM.run (compileRExprPreChecked L dstL (RExpr.copy src)) cs
      = CheckedCompilerM.run (readToReg L src) cs ∧
    ∀ r, CheckedCompilerM.value (readToReg L src) cs = .ok r →
      ∃ pOut, CheckedCompilerM.value (compileRExprPreChecked L dstL (RExpr.copy src)) cs = .ok pOut ∧
        (∀ d, pOut.store d = [oseair.Instr.RStore dstL r d]) ∧ pOut.postCleanup = [] := by
  have h_pre : compileRExprPreChecked L dstL (RExpr.copy src)
      = readRhsPre L dstL (RExpr.copy src) src (oseair.Rhs.Load (mirlite.placeLayout L src))
          (fun _ => []) (fun srcRes evd _ => RExprToEvidence.copy src srcRes evd) := rfl
  rw [h_pre]
  refine ⟨?_, fun r hr => ?_⟩
  · simp only [readRhsPre, readToReg, CheckedCompilerM.run_bind]
    split
    · simp only [CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
        CheckedCompilerM.run_pure, List.append_nil]
    · rfl
  · simp only [readToReg, CheckedCompilerM.value_bind] at hr
    simp only [readRhsPre, CheckedCompilerM.value_bind]
    split at hr
    · rename_i sOut h_s
      simp only [CheckedCompilerM.value_lift, CheckedCompilerM.run_lift,
        CheckedCompilerM.value_pure] at hr ⊢
      cases hr
      exact ⟨_, rfl, fun _ => rfl, rfl⟩
    · cases hr

theorem copy_pkgR {Γ : Ctx} {L : mirlite.LayEnv Γ} {compProg : oseair.Prog}
    (hWF : PtrPlacesWF L) (dstL : BLayout) {σ : LayoutTy} {src : Place Γ σ}
    (h : ReadSrcB src) :
    ValuePkgB compProg L dstL (RExpr.copy src) := by
  intro ρt sM sA csA h_wf h_tbd h_lbs h_prb h_mem h_alloc h_psim h_pc h_unmap output h_ev
  have h_inv0 : InvAtB L ρt sM sA csA := ⟨h_pc, h_lbs, h_mem, h_alloc, h_psim, h_wf, h_tbd,
    h_unmap, h_prb⟩
  have h_e : mirlite.evalCopy MSB L sM src = .ok output := by
    simpa [mirlite.evalRExpr] using h_ev
  obtain ⟨h_val, h_prm, h_nr⟩ := readToReg_factsR h h_lbs h_e
  obtain ⟨h_run, h_preV⟩ := copy_pre_eq (dstL := dstL) (src := src) (cs := csA) (L := L)
  obtain ⟨pOut, h_pval, h_store, h_post⟩ := h_preV _ h_val
  refine ⟨_, pOut, h_pval, h_store, h_post, by rw [h_run]; exact h_prm, fun h_code => ?_⟩
  rw [h_run] at h_code ⊢
  obtain ⟨n, s', vals, h_r, h_inv', h_st, h_l, -, h_rel, -, -⟩ := readToReg_simR hWF h h_inv0 h_e h_code
  rw [h_st] at h_inv'
  refine ⟨ρt, n, s', sM.mem, output.state.perms, vals, TagRenameIncr.refl ρt, h_wf, h_st, h_r,
    by rw [h_nr]; exact Nat.le_trans ((CheckedCompilerM.incr _ _).nextReg_le) (Nat.le_succ _),
    h_inv'.lbs, h_inv'.psim, h_inv'.tbd, h_inv'.mem, h_inv'.alloc, h_inv'.pc,
    StoreStepB.rstore compProg _ _ dstL _ vals h_l (by show _ < _; rw [h_nr]; omega), h_rel⟩

end obseq3.proof
