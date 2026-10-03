import obseq3.proof.copy_chain
import obseq3.proof.ref
import obseq3.proof.assoc

/-!
# Pointer chains modulo reassociation

`ChainB` is `proof.PtrChain` closed under the compiler's reassociation of
nested projections under a deref: `*((b.q).p)` lowers and resolves as
`*(b.(q ++ p))`. The place-lowering simulation and its compile-time half
are re-proved for it (the chain cases as in `places.lean` /
`copy_chain.lean`; the new case by congruence).
-/

namespace obseq3.proof

open obseq3 obseq3.bytes obseq3.proof
open obseq3.mirlite (MemValue Binding Env PlaceRes)
open obseq3.oseair (Val Register)
open obseq3.compile

inductive ChainB {Γ : Ctx} : {τ : LayoutTy} → Place Γ τ → Prop
  | base {τ : LayoutTy} (loc : Local Γ τ) : ChainB (.local loc)
  | deref {τ : LayoutTy} {p : Place Γ (LayoutTy.PtrL τ)} : ChainB p → ChainB (.deref p)
  | derefProj {σ τ : LayoutTy} {b : Place Γ σ} (f : PathTo σ (LayoutTy.PtrL τ)) :
      ChainB b → ChainB (.deref (.proj b f))
  | derefNested {ρ σ τ : LayoutTy} {b : Place Γ ρ} {q : PathTo ρ σ}
      {p : PathTo σ (LayoutTy.PtrL τ)} :
      ChainB (.deref (.proj b (q.append p))) → ChainB (.deref (.proj (.proj b q) p))

theorem ChainB.not_proj {Γ : Ctx} {σ : LayoutTy} {b : Place Γ σ} (h : ChainB b) :
    ∀ (σ' : LayoutTy) (bb : Place Γ σ') (q : PathTo σ' σ), b = bb.proj q → False := by
  intro σ' bb q h_eq
  cases h <;> simp_all

theorem PtrChain.toB {Γ : Ctx} {τ : LayoutTy} {p : Place Γ τ} (h : PtrChain p) : ChainB p := by
  induction h with
  | base loc => exact .base loc
  | deref _ ih => exact .deref ih
  | derefProj f _ ih => exact .derefProj f ih

theorem resolveAcc_deref_assoc {Γ : Ctx} {L : mirlite.LayEnv Γ} {M : PermissionModel}
    {s : mirlite.State M Γ} {ρ σ τ : LayoutTy} {b : Place Γ ρ} {q : PathTo ρ σ}
    {p : PathTo σ (LayoutTy.PtrL τ)} :
    mirlite.resolvePlaceAcc M L s (.deref (.proj (.proj b q) p))
      = mirlite.resolvePlaceAcc M L s (.deref (.proj b (q.append p))) := by
  have h := resolvePlaceAcc_assoc (L := L) s b q p
  simp only [mirlite.resolvePlaceAcc] at h ⊢
  rw [h]

theorem deref_assoc {Γ : Ctx} {L : mirlite.LayEnv Γ} {ρ σ τ : LayoutTy} (kind : RefKind)
    (b : Place Γ ρ) (q : PathTo ρ σ) (p : PathTo σ (LayoutTy.PtrL τ)) (cs : CompilerState) :
    CheckedCompilerM.run (placeToRegChecked L kind (.deref (.proj (.proj b q) p))) cs
      = CheckedCompilerM.run (placeToRegChecked L kind (.deref (.proj b (q.append p)))) cs ∧
    (CheckedCompilerM.value (placeToRegChecked L kind (.deref (.proj (.proj b q) p))) cs).map (·.result)
      = (CheckedCompilerM.value (placeToRegChecked L kind (.deref (.proj b (q.append p)))) cs).map
          (·.result) := by
  obtain ⟨h_run, h_val⟩ := placeToReg_assoc (L := L) RefKind.Shared b q p cs
  have hd : derefLoad L (.proj (.proj b q) p) = derefLoad L (.proj b (q.append p)) := by
    simp only [derefLoad, mirlite.placeLayout, PathTo.indices_append, fieldLayout_append]
  cases h1 : CheckedCompilerM.value (placeToRegChecked L RefKind.Shared (.proj (.proj b q) p)) cs with
  | ok o1 =>
      cases h2 : CheckedCompilerM.value (placeToRegChecked L RefKind.Shared (.proj b (q.append p))) cs with
      | ok o2 =>
          rw [h1, h2] at h_val
          simp only [Except.map, Except.ok.injEq] at h_val
          obtain ⟨r1, o1', v1, e1⟩ := deref_lowering (kind := kind) h1
          obtain ⟨r2, o2', v2, e2⟩ := deref_lowering (kind := kind) h2
          rw [r1, r2, v1, v2, h_run, h_val, hd]
          exact ⟨rfl, by simp only [Except.map, e1, e2, h_run]⟩
      | error e => rw [h1, h2] at h_val; simp [Except.map] at h_val
  | error e =>
      cases h2 : CheckedCompilerM.value (placeToRegChecked L RefKind.Shared (.proj b (q.append p))) cs with
      | ok o2 => rw [h1, h2] at h_val; simp [Except.map] at h_val
      | error e' =>
          rw [h1, h2] at h_val
          simp only [Except.map, Except.error.injEq] at h_val
          subst h_val
          have hb1 : placeToRegChecked L kind (.deref (.proj (.proj b q) p))
              = (do
                  let ptrOut ← placeToRegChecked L RefKind.Shared (.proj (.proj b q) p)
                  let ptrRes := ptrOut.result
                  let loadedReg ← CheckedCompilerM.lift freshRegM
                  let _ ← CheckedCompilerM.lift (emitM [oseair.Instr.Assgn loadedReg
                    (oseair.Rhs.Load (derefLoad L (.proj (.proj b q) p)) ptrRes.reg)])
                  let _ ← CheckedCompilerM.lift (emitM (cleanupInstrs ptrRes.cleanup))
                  pure { result := { reg := loadedReg, cleanup := [] },
                         evidence := PlaceToRegEvidence.deref _ ptrRes loadedReg ptrOut.evidence }) := by
            simp only [placeToRegChecked]
          have hb2 : placeToRegChecked L kind (.deref (.proj b (q.append p)))
              = (do
                  let ptrOut ← placeToRegChecked L RefKind.Shared (.proj b (q.append p))
                  let ptrRes := ptrOut.result
                  let loadedReg ← CheckedCompilerM.lift freshRegM
                  let _ ← CheckedCompilerM.lift (emitM [oseair.Instr.Assgn loadedReg
                    (oseair.Rhs.Load (derefLoad L (.proj b (q.append p))) ptrRes.reg)])
                  let _ ← CheckedCompilerM.lift (emitM (cleanupInstrs ptrRes.cleanup))
                  pure { result := { reg := loadedReg, cleanup := [] },
                         evidence := PlaceToRegEvidence.deref _ ptrRes loadedReg ptrOut.evidence }) := by
            simp only [placeToRegChecked]
          rw [hb1, hb2]
          simp only [CheckedCompilerM.run_bind, CheckedCompilerM.value_bind, h1, h2, h_run]
          exact ⟨by first | rfl | trivial, by first | rfl | trivial⟩

/-- `LoweredB` transfers to a place with the same run and result. -/
theorem LoweredB.congr {Γ : Ctx} {L : mirlite.LayEnv Γ} {ρt : TagRenameMap}
    {compProg : oseair.Prog} {kind : RefKind} {τ : LayoutTy} {p1 p2 : Place Γ τ}
    {cs : CompilerState} {sM : mirlite.State MSB Γ} {sA : oseair.State MSB}
    {resolved : PlaceRes} {permsD : MSB.State}
    {o1 : ResultWithEvidence PtrResult (PlaceToRegEvidence L kind p1)}
    {o2 : ResultWithEvidence PtrResult (PlaceToRegEvidence L kind p2)}
    {n : Nat} {s' : oseair.State MSB} {t : Tag}
    (h : LoweredB L ρt compProg kind p2 cs sM sA resolved permsD o2 n s' t)
    (h_v1 : CheckedCompilerM.value (placeToRegChecked L kind p1) cs = .ok o1)
    (h_res : o1.result = o2.result)
    (h_run : CheckedCompilerM.run (placeToRegChecked L kind p1) cs
      = CheckedCompilerM.run (placeToRegChecked L kind p2) cs) :
    LoweredB L ρt compProg kind p1 cs sM sA resolved permsD o1 n s' t := {
  val := h_v1
  clean := by rw [h_res]; exact h.clean
  run := h.run
  pc := by rw [h_run]; exact h.pc
  mem := h.mem
  psim := h.psim
  srcNT := h.srcNT
  tgtNT := h.tgtNT
  entry := by rw [h_res]; exact h.entry
  rt := h.rt
  le := h.le
  below := by rw [h_run, h_res]; exact h.below
  prm := by rw [h_run]; exact h.prm
  regmono := by rw [h_run]; exact h.regmono
  labmono := by rw [h_run]; exact h.labmono
  frame := h.frame }

theorem chainB_compiles {Γ : Ctx} {L : mirlite.LayEnv Γ} {M : PermissionModel}
    {s : mirlite.State M Γ} {cs : CompilerState}
    (h_map : ∀ {τ : LayoutTy} (loc : Local Γ τ) (b : Binding), s.env.lookup loc = some b →
      ∃ reg layout, getPlaceInfo cs loc.idx.1 = some (reg, layout))
    {τ : LayoutTy} {p : Place Γ τ} (h_chain : ChainB p) :
    ∀ (kind : RefKind) (r : PlaceRes × M.State), mirlite.resolvePlaceAcc M L s p = .ok r →
      ∃ out, CheckedCompilerM.value (placeToRegChecked L kind p) cs = .ok out ∧
        out.result.cleanup = [] ∧
        (CheckedCompilerM.run (placeToRegChecked L kind p) cs).placeRegMap = cs.placeRegMap := by
  induction h_chain with
  | base loc =>
      intro kind r h
      cases h_env : s.env.lookup loc with
      | none => simp [mirlite.resolvePlaceAcc, h_env] at h
      | some b =>
          obtain ⟨reg, layout, h_pi⟩ := h_map loc b h_env
          obtain ⟨h_run, out, h_val, h_res⟩ :=
            placeToRegChecked_local_existing (L := L) (kind := kind) h_pi
          exact ⟨out, h_val, by rw [h_res], by rw [h_run]⟩
  | deref h_q ih =>
      intro kind r h
      simp only [mirlite.resolvePlaceAcc] at h
      split at h
      · cases h
      rename_i rq h_rq
      obtain ⟨qOut, h_qval, h_qclean, h_qprm⟩ := ih RefKind.Shared _ h_rq
      obtain ⟨h_run, out, h_val, h_res⟩ := deref_lowering (kind := kind) h_qval
      refine ⟨out, h_val, by rw [h_res], ?_⟩
      rw [h_run, h_qclean]
      exact h_qprm
  | derefProj f h_b ih =>
      intro kind r h
      rename_i σb τ' b
      cases h_rb : mirlite.resolvePlaceAcc M L s b with
      | error e => simp [mirlite.resolvePlaceAcc, h_rb] at h
      | ok rb =>
      obtain ⟨bOut, h_bval, h_bclean, h_bprm⟩ := ih RefKind.Shared _ h_rb
      obtain ⟨hz, hnz⟩ := proj_lowering (kind := RefKind.Shared) f (ChainB.not_proj h_b) h_bval
      by_cases h0 : pathOffset L b f = 0
      · obtain ⟨h_runP, outP, h_valP, h_resP⟩ := hz h0
        obtain ⟨h_run, out, h_val, h_res⟩ := deref_lowering (kind := kind) h_valP
        refine ⟨out, h_val, by rw [h_res], ?_⟩
        rw [h_run, h_resP, h_bclean, h_runP]
        exact h_bprm
      · obtain ⟨h_runP, outP, h_valP, h_resP⟩ := hnz h0
        obtain ⟨h_run, out, h_val, h_res⟩ := deref_lowering (kind := kind) h_valP
        refine ⟨out, h_val, by rw [h_res], ?_⟩
        rw [h_run, h_runP]
        exact h_bprm
  | derefNested _ ih =>
      rename_i b q p _
      intro kind r h
      obtain ⟨h_run, h_val⟩ := deref_assoc (L := L) kind b q p cs
      rw [resolveAcc_deref_assoc] at h
      obtain ⟨o2, h_v2, h_c2, h_p2⟩ := ih kind r h
      rw [h_v2] at h_val
      cases h_v1 : CheckedCompilerM.value (placeToRegChecked L kind (.deref (.proj (.proj b q) p))) cs with
      | error e => rw [h_v1] at h_val; cases h_val
      | ok o1 =>
          rw [h_v1] at h_val
          simp only [Except.map, Except.ok.injEq] at h_val
          exact ⟨o1, rfl, by rw [h_val]; exact h_c2, by rw [h_run]; exact h_p2⟩

theorem chainB_lowering_simB {Γ : Ctx} {L : mirlite.LayEnv Γ} {ρt : TagRenameMap}
    {sM : mirlite.State MSB Γ} {compProg : oseair.Prog}
    (hWF : PtrPlacesWF L) (hwf : TagRenameWF ρt)
    {τ : LayoutTy} {p : Place Γ τ} (h_chain : ChainB p) :
    ∀ (kind : RefKind) (cs : CompilerState) (sA : oseair.State MSB)
      (resolved : PlaceRes) (permsD : MSB.State),
      mirlite.resolvePlaceAcc MSB L sM p = .ok (resolved, permsD) →
      TagRenameBounded ρt sM.perms.NextTag sA.perms.NextTag →
      LocalBindingSimB L ρt sM.env sA cs →
      PlaceRegMapBoundB cs →
      ByteMemSim ρt sM.mem sA.mem →
      ByteAllocLockstep sM.mem sA.mem →
      PermSim ρt sM.perms sA.perms →
      sA.pc = cs.nextLabel →
      CodeIncludedB compProg (CheckedCompilerM.run (placeToRegChecked L kind p) cs) →
      ∃ placeOut n s' tres, LoweredB L ρt compProg kind p cs sM sA resolved permsD
        placeOut n s' tres := by
  induction h_chain with
  | base loc =>
      intro kind cs sA resolved permsD h_res h_tbd h_lbs h_prb h_mem h_lock h_psim h_pc h_inc
      cases h_env : sM.env.lookup loc with
      | none => simp [mirlite.resolvePlaceAcc, h_env] at h_res
      | some bnd =>
      simp only [mirlite.resolvePlaceAcc, h_env, Except.ok.injEq, Prod.mk.injEq] at h_res
      obtain ⟨rfl, rfl⟩ := h_res
      obtain ⟨reg, tag, h_pi, ⟨ext, h_reg⟩, h_rt, -⟩ := h_lbs loc bnd h_env
      obtain ⟨h_prun, placeOut, h_pval, h_pres⟩ :=
        placeToRegChecked_local_existing (L := L) (kind := kind) h_pi
      refine ⟨placeOut, 0, sA, tag, {
        val := h_pval
        clean := by rw [h_pres]
        run := by simp [oseair.runN]
        pc := by rw [h_prun]; exact h_pc
        mem := rfl
        psim := h_psim
        srcNT := rfl
        tgtNT := Nat.le_refl _
        entry := ⟨ext, by rw [h_pres, Nat.sub_self]; exact h_reg⟩
        rt := h_rt
        le := Nat.le_refl _
        below := by rw [h_prun, h_pres]; exact h_prb _ _ _ h_pi
        prm := by rw [h_prun]
        regmono := by rw [h_prun]; exact Nat.le_refl _
        labmono := by rw [h_prun]; exact Nat.le_refl _
        frame := fun _ _ => rfl }⟩
  | deref h_chainQ ih =>
      rename_i σ q
      intro kind cs sA resolved permsD h_res h_tbd h_lbs h_prb h_mem h_lock h_psim h_pc h_inc
      simp only [mirlite.resolvePlaceAcc] at h_res
      cases h_qres : mirlite.resolvePlaceAcc MSB L sM q with
      | error e => simp [h_qres] at h_res
      | ok pr =>
      obtain ⟨qRes, permsQ⟩ := pr
      simp only [h_qres] at h_res
      split at h_res
      · cases h_res
      rename_i h_free
      split at h_res
      · cases h_res
      rename_i h_qb
      split at h_res
      · cases h_res
      rename_i permsQ' h_qread
      split at h_res
      · rename_i vb vo ve vsz vt h_dec
        simp only [Except.ok.injEq, Prod.mk.injEq] at h_res
        obtain ⟨rfl, rfl⟩ := h_res
        -- the pointer place's own lowering
        obtain ⟨qOut, n1, s_mid, qtag, hQ⟩ :=
          ih RefKind.Shared cs sA qRes permsQ h_qres h_tbd h_lbs h_prb h_mem h_lock h_psim h_pc
            (h_inc.mono (deref_incr q cs))
        exact deref_level hwf hQ h_mem h_lock h_inc h_free h_qb h_qread h_dec
      · cases h_res
  | derefProj f h_chainB ih =>
      rename_i σb τ' b
      intro kind cs sA resolved permsD h_res h_tbd h_lbs h_prb h_mem h_lock h_psim h_pc h_inc
      have h_np := ChainB.not_proj h_chainB
      simp only [mirlite.resolvePlaceAcc] at h_res
      cases h_bres : mirlite.resolvePlaceAcc MSB L sM b with
      | error e => simp [h_bres] at h_res
      | ok pr =>
      obtain ⟨bRes, permsB⟩ := pr
      simp only [h_bres] at h_res
      split at h_res
      · cases h_res
      rename_i h_free
      split at h_res
      · cases h_res
      rename_i h_qb
      split at h_res
      · cases h_res
      rename_i permsQ' h_qread
      split at h_res
      case h_2 => cases h_res
      rename_i vb vo ve vsz vt h_dec
      simp only [Except.ok.injEq, Prod.mk.injEq] at h_res
      obtain ⟨rfl, rfl⟩ := h_res
      obtain ⟨bOut, n1, s_mid, btag, hB⟩ :=
        ih RefKind.Shared cs sA bRes permsB h_bres h_tbd h_lbs h_prb h_mem h_lock h_psim h_pc
          (h_inc.mono ((proj_incr (kind := RefKind.Shared) f cs h_np).trans
            (deref_incr (.proj b f) cs)))
      obtain ⟨hz, hnz⟩ := proj_lowering (kind := RefKind.Shared) f h_np hB.val
      by_cases h0 : pathOffset L b f = 0
      · -- offset ZERO: the field IS the base; one deref level
        obtain ⟨h_runP, outP, h_valP, h_resP⟩ := hz h0
        have h0' : mirlite.fieldOffset (mirlite.placeLayout L b) f.indices = 0 := h0
        have hP : LoweredB L ρt compProg RefKind.Shared (.proj b f) cs sM sA
            { bRes with addr := bRes.addr + mirlite.fieldOffset (mirlite.placeLayout L b) f.indices }
            permsB outP n1 s_mid btag := {
          val := h_valP
          clean := by rw [h_resP]; exact hB.clean
          run := hB.run
          pc := by rw [h_runP]; exact hB.pc
          mem := hB.mem
          psim := hB.psim
          srcNT := hB.srcNT
          tgtNT := hB.tgtNT
          entry := by
            obtain ⟨e, he⟩ := hB.entry
            exact ⟨e, by rw [h_resP]; simpa [h0'] using he⟩
          rt := hB.rt
          le := by simpa [h0'] using hB.le
          below := by rw [h_runP, h_resP]; exact hB.below
          prm := by rw [h_runP]; exact hB.prm
          regmono := by rw [h_runP]; exact hB.regmono
          labmono := by rw [h_runP]; exact hB.labmono
          frame := hB.frame }
        exact deref_level hwf hP h_mem h_lock h_inc h_free h_qb h_qread h_dec
      · -- offset NONZERO: `Borrow(Shared); Load; Die`, which is the source's
        -- one read of the pointer field (keystone's `sb_ref_read_die_cancels`)
        obtain ⟨h_runP, outP, h_valP, h_resP⟩ := hnz h0
        obtain ⟨h_runD, out, h_valD, h_outres⟩ := deref_lowering (kind := kind) h_valP
        rw [h_resP, hB.clean, h_runP] at h_runD
        simp only [List.nil_append, cleanupInstrs, List.reverse_cons, List.reverse_nil,
          List.map_cons, List.map_nil] at h_runD
        rw [h_runP] at h_outres
        simp only [emit] at h_outres
        obtain ⟨ext, h_bentry⟩ := hB.entry
        have hn : placeSize L (.proj b f) = ptrSize := hWF (.proj b f)
        have hA : bRes.allocBase + (bRes.addr - bRes.allocBase) = bRes.addr :=
          Nat.add_sub_cancel' hB.le
        have h_qb' : bRes.addr + pathOffset L b f + ptrSize ≤ bRes.allocBase + bRes.allocSize :=
          Nat.le_of_not_gt fun h => h_qb (Or.inr h)
        -- the source read, transported; the target's Shared retag succeeds
        obtain ⟨p2, h_read', h_psim2⟩ :=
          sb_read_respects_PermSim hB.psim hwf hB.rt h_qread
        obtain ⟨q1, h_ref⟩ := sb_ref_Shared_ok_of_sb_read_ok h_read'
        have h_tbd_mid : TagRenameBounded ρt permsB.NextTag s_mid.perms.NextTag := by
          rw [hB.srcNT]; exact TagRenameBounded.mono h_tbd (Nat.le_refl _) hB.tgtNT
        have h_unprot := freshTag_not_protected hB.psim h_tbd_mid
        have h0w : wildcardTag < s_mid.perms.NextTag := (h_tbd_mid _ _ hwf.2).2
        have h_ntw : (s_mid.perms.NextTag == wildcardTag) = false := by
          simp only [beq_eq_false_iff_ne]; exact (Nat.ne_of_lt h0w).symm
        obtain ⟨q2, q3, sAcc, h_rd1, h_die1, h_rd2, h_sm, h_ex, h_pf, h_ntle, h_wk⟩ :=
          sb_ref_read_die_cancels h_ntw h_unprot h_ref
        have h_acc : sAcc = p2 := by
          have := h_rd2.symm.trans h_read'
          exact Except.ok.inj this
        subst h_acc
        -- the source pointer, decoded on the target
        have h_decS : mirlite.decodeV .ptr
            (sM.mem.read (bRes.addr + pathOffset L b f) ptrSize) = .ptrVal vb vo ve vsz vt := h_dec
        obtain ⟨t', h_decT, h_t⟩ := decode_ptr_sim hwf h_mem h_decS
        have h_freeT : s_mid.mem.isFreed bRes.allocBase = false := by
          rw [hB.mem]
          simp only [bytes.Mem.isFreed, ← h_lock.2.2] at h_free ⊢
          simpa using h_free
        -- the code
        have hct := fun i1 i2 i3 => code_three
          (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared b) cs) i1 i2 i3
        have hc1 : (CheckedCompilerM.run (placeToRegChecked L kind (.deref (.proj b f))) cs).code
            ((CheckedCompilerM.run (placeToRegChecked L RefKind.Shared b) cs).nextLabel + 0)
            = some (oseair.Instr.Assgn
              (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared b) cs).nextReg)
              (borrowRhs RefKind.Shared (placeSize L (.proj b f)) bOut.result.reg
                (pathOffset L b f))) := by
          rw [h_runD]; exact (hct _ _ _).1
        have hc2 : (CheckedCompilerM.run (placeToRegChecked L kind (.deref (.proj b f))) cs).code
            ((CheckedCompilerM.run (placeToRegChecked L RefKind.Shared b) cs).nextLabel + 1)
            = some (oseair.Instr.Assgn
              (Register.R ((CheckedCompilerM.run (placeToRegChecked L RefKind.Shared b) cs).nextReg + 1))
              (oseair.Rhs.Load (derefLoad L (.proj b f))
                (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared b) cs).nextReg))) := by
          rw [h_runD]; exact (hct _ _ _).2.1
        have hc3 : (CheckedCompilerM.run (placeToRegChecked L kind (.deref (.proj b f))) cs).code
            ((CheckedCompilerM.run (placeToRegChecked L RefKind.Shared b) cs).nextLabel + 2)
            = some (oseair.Instr.Die
              (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared b) cs).nextReg)
              (placeSize L (.proj b f))) := by
          rw [h_runD]; exact (hct _ _ _).2.2.1
        have hnl : (CheckedCompilerM.run (placeToRegChecked L kind (.deref (.proj b f))) cs).nextLabel
            = (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared b) cs).nextLabel + 3 := by
          rw [h_runD]; exact (hct _ _ _).2.2.2
        have h_at : ∀ k instr, k < 3 →
            (CheckedCompilerM.run (placeToRegChecked L kind (.deref (.proj b f))) cs).code
              ((CheckedCompilerM.run (placeToRegChecked L RefKind.Shared b) cs).nextLabel + k)
              = some instr →
            compProg (s_mid.pc + k) = some instr := by
          intro k instr hk hc
          rw [hB.pc]
          exact h_inc _ instr (by rw [hnl]; omega) hc
        -- §1 the Borrow
        have h1 := runN_Borrow (s := s_mid) (h_at 0 _ (by omega) hc1) h_bentry h_freeT
          (by rw [hA, hn]; exact h_qb') (by rw [hA, hn]; exact h_ref)
        -- §2 the Load through the fresh tag
        let S1 : oseair.State MSB :=
          { s_mid with
              perms := q1,
              reg := s_mid.reg.insert
                (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared b) cs).nextReg)
                [Val.Ptr bRes.allocBase (bRes.addr - bRes.allocBase + pathOffset L b f)
                  (placeSize L (.proj b f)) bRes.allocSize s_mid.perms.NextTag],
              pc := s_mid.pc + 1 }
        have h2 := runN_Load_ptr (s := S1) (q := mirlite.placeLayout L (.deref (.proj b f)))
          (h_at 1 _ (by omega) hc2) (RegMap.lookup_insert_self _ _ _)
          (by simpa [S1] using h_freeT)
          (by rw [← Nat.add_assoc, hA]; exact h_qb')
          (by rw [← Nat.add_assoc, hA]; exact h_rd1)
          (by rw [← Nat.add_assoc, hA]; simpa [S1, hB.mem] using h_decT)
        -- §3 the Die
        have hne : Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared b) cs).nextReg
            ≠ Register.R ((CheckedCompilerM.run (placeToRegChecked L RefKind.Shared b) cs).nextReg + 1) := by
          simp
        let S2 : oseair.State MSB :=
          { S1 with
              perms := q2,
              reg := S1.reg.insert
                (Register.R ((CheckedCompilerM.run (placeToRegChecked L RefKind.Shared b) cs).nextReg + 1))
                [Val.Ptr vb vo ve vsz t'],
              pc := S1.pc + 1 }
        have h3 := runN_Die (s := S2) (h_at 2 _ (by omega) hc3)
          (by rw [RegMap.lookup_insert_ne _ _ hne]; exact RegMap.lookup_insert_self _ _ _)
          (by rw [← Nat.add_assoc, hA, hn]; exact h_die1)
        refine ⟨out, n1 + 1 + 1 + 1, _, t', {
          val := h_valD
          clean := by rw [h_outres]
          run := runN_trans (runN_trans (runN_trans hB.run h1) h2) h3
          pc := by
            show s_mid.pc + 1 + 1 + 1 = _
            rw [hnl, hB.pc]
          mem := hB.mem
          psim := ⟨by rw [h_sm]; exact h_psim2.1, by rw [h_pf]; exact h_psim2.2.1,
            by rw [h_ex]; exact h_psim2.2.2.1, Nat.le_trans h_psim2.2.2.2.1 h_ntle,
            by rw [h_wk]; exact h_psim2.2.2.2.2⟩
          srcNT := by rw [sb_read_NextTag h_qread]; exact hB.srcNT
          tgtNT := by
            show sA.perms.NextTag ≤ q3.NextTag
            exact Nat.le_trans hB.tgtNT (by rw [← sb_read_NextTag h_read']; exact h_ntle)
          entry := ⟨ve, by
            rw [h_outres]
            simp only [Nat.add_sub_cancel_left]
            exact RegMap.lookup_insert_self _ _ _⟩
          rt := h_t
          le := Nat.le_add_right _ _
          below := by
            rw [h_outres, h_runD]
            show _ < _ + 1 + 1
            omega
          prm := by rw [h_runD]; exact hB.prm
          regmono := by
            have := hB.regmono
            rw [h_runD]; show _ ≤ _ + 1 + 1; omega
          labmono := by
            have := hB.labmono
            rw [hnl]; omega
          frame := fun r hr => by
            have hr' := RegisterBelow.mono hB.regmono hr
            have hne1 := RegisterBelow.ne_fresh hr'
            have hne2 : r ≠ Register.R
                ((CheckedCompilerM.run (placeToRegChecked L RefKind.Shared b) cs).nextReg + 1) :=
              RegisterBelow.ne_fresh (RegisterBelow.mono (Nat.le_succ _) hr')
            show ((s_mid.reg.insert _ _).insert _ _).lookup r = _
            rw [RegMap.lookup_insert_ne _ _ hne2, RegMap.lookup_insert_ne _ _ hne1]
            exact hB.frame r hr }⟩
  | derefNested _ ih =>
      rename_i b q p _
      intro kind cs sA resolved permsD h_res h_tbd h_lbs h_prb h_mem h_lock h_psim h_pc h_inc
      obtain ⟨h_run, h_val⟩ := deref_assoc (L := L) kind b q p cs
      rw [h_run] at h_inc
      rw [resolveAcc_deref_assoc] at h_res
      obtain ⟨out2, n, s', t, h2⟩ :=
        ih kind cs sA resolved permsD h_res h_tbd h_lbs h_prb h_mem h_lock h_psim h_pc h_inc
      have h_v2 := h2.val
      rw [h_v2] at h_val
      cases h_v1 : CheckedCompilerM.value (placeToRegChecked L kind (.deref (.proj (.proj b q) p))) cs with
      | error e => rw [h_v1] at h_val; cases h_val
      | ok out1 =>
          rw [h_v1] at h_val
          simp only [Except.map, Except.ok.injEq] at h_val
          exact ⟨out1, n, s', t, h2.congr h_v1 h_val h_run⟩


theorem chainB_lowers {Γ : Ctx} {L : mirlite.LayEnv Γ} {compProg : oseair.Prog}
    (hWF : PtrPlacesWF L) {τ : LayoutTy} {p : Place Γ τ} (h_chain : ChainB p) :
    LowersB L compProg p :=
  fun _ _ kind cs sA resolved permsD hwf h_res =>
    chainB_lowering_simB hWF hwf h_chain kind cs sA resolved permsD h_res

theorem chainB_compilesB {Γ : Ctx} {L : mirlite.LayEnv Γ} {τ : LayoutTy} {p : Place Γ τ}
    (h : ChainB p) : CompilesB L p :=
  fun _ _ kind r h_map h_res => chainB_compiles h_map h kind r h_res

end obseq3.proof
