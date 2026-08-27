import obseq3.proof.permsim_transport

/-!
Load-spine place-lowering simulation — the "mother lemma" of the deref
regimes. A *load spine* is a pointer place built from a local by
dereferences only (no projections): its lowering emits one `Load` per
deref level and nothing else — no `Borrow`s, no cleanup. For such places
this file proves, by induction on the spine, that executing the compiled
lowering from a `CompilerInv`-shaped configuration yields a register
holding the ρ-renamed resolved pointer, with the threaded permission
state `PermSim`-related and everything else framed.

Consumers: the const-write deref regime (all depths at once — this
subsumes the hand-rolled depth-1 proof), and later the deref regimes of
copy, ref and dealloc.
-/

namespace obseq3.proof

open obseq3
open obseq3.compile
open obseq3.oseair (Instr Register Rhs Val)

/-- Pointer places whose lowering is a pure `Load` spine: a local, or a
    dereference of a spine. Projections are excluded — they emit
    `Borrow`s, whose simulation needs the `sb_ref` transport. -/
inductive LoadSpine {Γ : Ctx} : {τ : LayoutTy} → Place Γ (obseq.LayoutTy.PtrL τ) → Prop
  | base {τ : LayoutTy} (loc : Local Γ (obseq.LayoutTy.PtrL τ)) : LoadSpine (.local loc)
  | step {τ : LayoutTy} {p : Place Γ (obseq.LayoutTy.PtrL (obseq.LayoutTy.PtrL τ))} :
      LoadSpine p → LoadSpine (.deref p)

/-- A successful access-resolution implies the place's root local is bound,
    hence (under `LocalBindingSim`) compiler-mapped. -/
theorem placeInputsMapped_of_resolveAcc
    {Γ : Ctx} {τ : LayoutTy}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {cs : CompilerState}
    {p : Place Γ τ}
    {resolved : mirlite.PlaceRes} {permsD : MSB.State}
    (h_lbs : LocalBindingSim ρa ρt s_mir.env s_osea cs)
    (h_res : mirlite.resolvePlaceAcc MSB s_mir p = .ok (resolved, permsD)) :
    PlaceInputsMapped cs p := by
  induction p generalizing resolved permsD with
  | «local» loc =>
      cases h_env : mirlite.Env.lookup s_mir.env loc with
      | none => simp [mirlite.resolvePlaceAcc, h_env] at h_res
      | some binding =>
          rcases h_lbs loc binding h_env with ⟨reg, _, _, h_pi, _, _, _, _⟩
          exact ⟨reg, _, h_pi⟩
  | proj base path ih =>
      simp only [mirlite.resolvePlaceAcc] at h_res
      split at h_res
      · exact absurd h_res (by simp)
      · rename_i res perms' h_base
        exact ih h_base
  | deref ptrPlace ih =>
      simp only [mirlite.resolvePlaceAcc] at h_res
      split at h_res
      · exact absurd h_res (by simp)
      · rename_i ptrRes perms' h_ptr
        exact ih h_ptr

/-- Load-spine lowering simulation. Given a `CompilerInv`-shaped
    configuration and a successful source access-resolution of a spine
    pointer place, the compiled lowering (`Load` per deref level) executes
    on the target, ending with the result register holding the ρ-renamed
    resolved pointer. The conclusion carries everything the consumer's
    next event (a `Load` through the result, or the final store) needs:
    the register entry, the resolved tag's rename and non-wildcardness,
    the resolved range's ρa-domain membership, `PermSim` of the threaded
    permission state, and framing (memory untouched, `LocalBindingSim`
    intact, `placeRegMap` unchanged, counters monotone). The spine only
    READS, so it also reports that neither machine's `NextTag` moved —
    which is what lets a consumer carry `TagRenameBounded` across it. -/
theorem loadSpine_lowering_sim
    {Γ : Ctx}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir : mirlite.State MSB Γ}
    {compProg : oseair.Prog}
    (h_id_a : IdentityOnDomain ρa) (h_wf_t : TagRenameWF ρt)
    {τ : LayoutTy} {p : Place Γ (obseq.LayoutTy.PtrL τ)}
    (h_spine : LoadSpine p) :
    ∀ (kind : RefKind) (cs : CompilerState) (s_osea : oseair.State MSB)
      (resolved : mirlite.PlaceRes) (permsD : MSB.State),
      mirlite.resolvePlaceAcc MSB s_mir p = .ok (resolved, permsD) →
      LocalBindingSim ρa ρt s_mir.env s_osea cs →
      PlaceRegMapBound cs →
      SourceMemSim ρa ρt s_mir.mem s_osea.mem →
      PermSim ρt s_mir.perms s_osea.perms →
      s_osea.pc = cs.nextLabel →
      (∀ q instr, q < (CheckedCompilerM.run (placeToRegChecked kind p) cs).nextLabel →
        (CheckedCompilerM.run (placeToRegChecked kind p) cs).code q = some instr →
        compProg q = some instr) →
      ∃ (placeOut : ResultWithEvidence PtrResult (PlaceToRegEvidence kind p))
        (n : Nat) (s_osea' : oseair.State MSB) (tres : Tag),
        CheckedCompilerM.value (placeToRegChecked kind p) cs = Except.ok placeOut ∧
        placeOut.result.cleanup = [] ∧
        oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
        s_osea'.pc = (CheckedCompilerM.run (placeToRegChecked kind p) cs).nextLabel ∧
        s_osea'.mem = s_osea.mem ∧
        PermSim ρt permsD s_osea'.perms ∧
        permsD.NextTag = s_mir.perms.NextTag ∧
        s_osea'.perms.NextTag = s_osea.perms.NextTag ∧
        LocalBindingSim ρa ρt s_mir.env s_osea' cs ∧
        PtrRegisterEntry s_osea'.reg placeOut.result.reg resolved.allocBase
          (resolved.addr - resolved.allocBase) resolved.allocSize tres ∧
        ρt resolved.tag = some tres ∧
        (resolved.tag == wildcardTag) = false ∧
        resolved.allocBase ≤ resolved.addr ∧
        (∀ k, k < resolved.allocSize → ∃ a', ρa (resolved.allocBase + k) = some a') ∧
        RegisterBelow (CheckedCompilerM.run (placeToRegChecked kind p) cs).nextReg
          placeOut.result.reg ∧
        (CheckedCompilerM.run (placeToRegChecked kind p) cs).placeRegMap = cs.placeRegMap ∧
        cs.nextReg ≤ (CheckedCompilerM.run (placeToRegChecked kind p) cs).nextReg ∧
        cs.nextLabel ≤ (CheckedCompilerM.run (placeToRegChecked kind p) cs).nextLabel := by
  induction h_spine with
  | base loc =>
      intro kind cs s_osea resolved permsD h_res h_lbs h_prb h_sms h_psim h_pc h_inst
      cases h_env : mirlite.Env.lookup s_mir.env loc with
      | none => simp [mirlite.resolvePlaceAcc, h_env] at h_res
      | some bind =>
      simp only [mirlite.resolvePlaceAcc, h_env, Except.ok.injEq, Prod.mk.injEq] at h_res
      obtain ⟨h_r, h_p⟩ := h_res
      subst h_r
      subst h_p
      obtain ⟨reg, base, tag, h_pi, h_entry, h_ra, h_rt, h_nw, h_dom⟩ := h_lbs loc bind h_env
      have h_base : base = bind.addr := (h_id_a _ _ h_ra).symm
      subst h_base
      obtain ⟨h_prun, placeOut, h_pval, h_pres⟩ :=
        placeToRegChecked_local_existing (kind := kind) h_pi
      refine ⟨placeOut, 0, s_osea, tag, h_pval, by rw [h_pres],
        by simp [oseair.runN], ?_, rfl, h_psim, rfl, rfl, h_lbs, ?_, h_rt, h_nw,
        Nat.le_refl _, ?_, ?_, ?_, ?_, ?_⟩
      · rw [h_prun]; exact h_pc
      · rw [h_pres, Nat.sub_self]
        exact h_entry
      · intro k hk
        have hk0 : k = 0 := Nat.lt_one_iff.mp hk
        subst hk0
        exact ⟨bind.addr, h_ra⟩
      · rw [h_prun, h_pres]
        exact h_prb _ _ _ h_pi
      · rw [h_prun]
      · rw [h_prun]
        exact Nat.le_refl _
      · rw [h_prun]
        exact Nat.le_refl _
  | step h_spineQ ih =>
      rename_i τ' q
      intro kind cs s_osea resolved permsD h_res h_lbs h_prb h_sms h_psim h_pc h_inst
      -- one resolveAcc level: q's resolution, bounds check, read, content
      simp only [mirlite.resolvePlaceAcc] at h_res
      cases h_qres : mirlite.resolvePlaceAcc MSB s_mir q with
      | error e => simp [h_qres] at h_res
      | ok pr =>
        obtain ⟨qRes, permsQ⟩ := pr
        simp only [h_qres] at h_res
        by_cases h_qb : qRes.addr < qRes.allocBase ∨
            qRes.addr ≥ qRes.allocBase + qRes.allocSize
        · rw [if_pos h_qb] at h_res
          exact absurd h_res (by simp)
        · rw [if_neg h_qb] at h_res
          cases h_qread : MSB.read permsQ qRes.addr 1 qRes.tag with
          | error e => simp [h_qread] at h_res
          | ok permsQ' =>
            simp only [h_qread] at h_res
            cases h_qfind : mirlite.Mem.find? s_mir.mem qRes.addr with
            | none => simp [h_qfind] at h_res
            | some mv =>
              cases mv with
              | undef => simp [h_qfind] at h_res
              | word w => simp [h_qfind] at h_res
              | ptrVal b o sz t =>
              simp only [h_qfind, Except.ok.injEq, Prod.mk.injEq] at h_res
              obtain ⟨h_r1, h_r2⟩ := h_res
              subst h_r1
              subst h_r2
              -- bounds of the pointer place, from the new dereferenceable check
              have h_ge : qRes.allocBase ≤ qRes.addr :=
                Nat.le_of_not_lt (fun h => h_qb (Or.inl h))
              have h_lt_ab : qRes.addr < qRes.allocBase + qRes.allocSize :=
                Nat.lt_of_not_le (fun h => h_qb (Or.inr h))
              have h_cancel : qRes.allocBase + (qRes.addr - qRes.allocBase) = qRes.addr :=
                Nat.add_sub_cancel' h_ge
              have h_off : qRes.addr - qRes.allocBase < qRes.allocSize := by
                rw [← h_cancel] at h_lt_ab
                exact Nat.lt_of_add_lt_add_left h_lt_ab
              -- this level's do-block, definitionally
              have h_bind : placeToRegChecked (Γ := Γ) kind (.deref q)
                  = (do
                      let ptrOut ← placeToRegChecked RefKind.Shared q
                      let ptrRes := ptrOut.result
                      let loadedReg ← CheckedCompilerM.lift freshRegM
                      let _ ← CheckedCompilerM.lift
                        (emitM [Instr.Assgn loadedReg (Rhs.Load obseq.TyVal.PTy ptrRes.reg)])
                      let _ ← CheckedCompilerM.lift (emitM (cleanupInstrs ptrRes.cleanup))
                      pure {
                        result := { reg := loadedReg, cleanup := [] },
                        evidence := PlaceToRegEvidence.deref q ptrRes loadedReg ptrOut.evidence
                      }) := by simp only [placeToRegChecked]
              -- this level's run only grows q's run, so q's fragment is installed
              have h_incrQ : StateIncr
                  (CheckedCompilerM.run (placeToRegChecked RefKind.Shared q) cs)
                  (CheckedCompilerM.run (placeToRegChecked kind (.deref q)) cs) := by
                rw [h_bind, CheckedCompilerM.run_bind]
                cases h : CheckedCompilerM.value (placeToRegChecked RefKind.Shared q) cs with
                | ok a => exact CheckedCompilerM.incr _ _
                | error e => exact StateIncr.refl _
              have h_instQ : ∀ q' instr,
                  q' < (CheckedCompilerM.run (placeToRegChecked RefKind.Shared q) cs).nextLabel →
                  (CheckedCompilerM.run (placeToRegChecked RefKind.Shared q) cs).code q'
                    = some instr →
                  compProg q' = some instr := by
                intro q' instr h_lt h_code
                refine h_inst q' instr (Nat.lt_of_lt_of_le h_lt h_incrQ.nextLabel_le) ?_
                rw [h_incrQ.code_eq q' h_lt]
                exact h_code
              obtain ⟨qOut, n1, s_mid, qtag, h_qval, h_qclean, h_qrun, h_qpc, h_qmem,
                h_qpsim, h_qnt1, h_qnt2, h_qlbs, h_qentry, h_qrt, h_qnw, h_qle,
                h_qrange, h_qbelow, h_qprm, h_qregmono, h_qlabmono⟩ :=
                ih RefKind.Shared cs s_osea qRes permsQ h_qres h_lbs h_prb h_sms h_psim
                  h_pc h_instQ
              -- concrete run/value of this level
              have h_runD : CheckedCompilerM.run (placeToRegChecked kind (.deref q)) cs
                  = emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared q) cs) with
                        nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared q) cs).nextReg + 1 }
                      [Instr.Assgn
                        (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared q) cs).nextReg)
                        (Rhs.Load obseq.TyVal.PTy qOut.result.reg)] := by
                rw [h_bind]
                simp only [CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
                  CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
                  CheckedCompilerM.run_pure, CheckedCompilerM.value_pure, h_qval]
                simp [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM,
                  cleanupInstrs, h_qclean, emit_nil]
              have h_valD : CheckedCompilerM.value (placeToRegChecked kind (.deref q)) cs
                  = Except.ok {
                      result := {
                        reg := Register.R
                          (CheckedCompilerM.run (placeToRegChecked RefKind.Shared q) cs).nextReg,
                        cleanup := [] },
                      evidence := PlaceToRegEvidence.deref q qOut.result
                        (Register.R
                          (CheckedCompilerM.run (placeToRegChecked RefKind.Shared q) cs).nextReg)
                        qOut.evidence } := by
                rw [h_bind]
                simp only [CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
                  CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
                  CheckedCompilerM.run_pure, CheckedCompilerM.value_pure, h_qval]
                simp [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM,
                  cleanupInstrs, h_qclean, emit_nil]
              -- the Load's target read succeeds, PermSim-transported
              obtain ⟨p2, h_read_tgt, h_psim2⟩ :=
                sb_read_respects_PermSim h_qpsim h_wf_t h_qrt h_qnw h_qread
              have h_read_tgt' : MSB.read s_mid.perms
                  (qRes.allocBase + (qRes.addr - qRes.allocBase)) 1 qtag = .ok p2 := by
                rw [h_cancel]
                exact h_read_tgt
              -- the loaded cell holds the ρ-renamed stored pointer
              obtain ⟨addr', value', h_ra', h_find_tgt, h_mvs⟩ := h_sms _ _ h_qfind
              have h_addr' : addr' = qRes.addr := (h_id_a _ _ h_ra').symm
              subst h_addr'
              cases value' with
              | Undef => exact h_mvs.elim
              | Dat _ => exact h_mvs.elim
              | Ptr b2 o2 s2 t2 =>
              obtain ⟨h_b, h_o, h_s, h_t, h_tnw, h_range⟩ := h_mvs
              have h_b2 : b2 = b := (h_id_a _ _ h_b).symm
              subst h_b2
              subst h_o
              subst h_s
              -- code position of this level's Load
              have h_code1 : compProg s_mid.pc = some (Instr.Assgn
                  (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared q) cs).nextReg)
                  (Rhs.Load obseq.TyVal.PTy qOut.result.reg)) := by
                rw [h_qpc]
                refine h_inst _ _ ?_ ?_
                · rw [h_runD]
                  show _ < _ + 1
                  exact Nat.lt_succ_self _
                · rw [h_runD]
                  have h := emit_code_at_new
                    { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared q) cs) with
                        nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared q) cs).nextReg + 1 }
                    [Instr.Assgn
                      (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared q) cs).nextReg)
                      (Rhs.Load obseq.TyVal.PTy qOut.result.reg)]
                    (k := 0) (by simp)
                  simpa using h
              -- execute the Load
              have h_run1 := runN_Assgn_Load_ptr_step compProg s_mid
                (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared q) cs).nextReg)
                qOut.result.reg obseq.TyVal.PTy h_code1 h_qentry h_off h_read_tgt'
              have h_rws : oseair.readWordSeq s_mid.mem
                  (qRes.allocBase + (qRes.addr - qRes.allocBase))
                  (obseq.typeSize obseq.TyVal.PTy) = [Val.Ptr b2 o2 s2 t2] := by
                rw [h_cancel]
                show oseair.readWordSeq s_mid.mem qRes.addr 1 = _
                rw [h_qmem]
                simp [oseair.readWordSeq, h_find_tgt]
              refine ⟨_, n1 + 1, _,  t2, h_valD, rfl,
                (oseair_runN_add n1 1 s_osea compProg s_mid h_qrun).trans h_run1,
                ?_, ?_, h_psim2, ?_, ?_, ?_, ?_, h_t, h_tnw, Nat.le_add_right b2 o2, ?_,
                ?_, ?_, ?_, ?_⟩
              · -- pc
                show s_mid.pc + 1 = _
                rw [h_qpc, h_runD]
                simp [emit]
              · -- mem
                show s_mid.mem = s_osea.mem
                exact h_qmem
              · -- source counter: this level only READS through the pointer
                rw [sb_read_NextTag h_qread]
                exact h_qnt1
              · -- target counter: the `Load`'s read mints nothing either
                show p2.NextTag = s_osea.perms.NextTag
                rw [sb_read_NextTag h_read_tgt]
                exact h_qnt2
              · -- LocalBindingSim: fresh register insert
                exact LocalBindingSim.insert_fresh_reg h_qlbs h_prb h_qregmono rfl
              · -- entry for the loaded register
                show oseair.RegMap.lookup _ _ = _
                rw [RegMap.lookup_insert_self, h_rws, Nat.add_sub_cancel_left]
              · -- range domain from MemValSim
                intro k hk
                exact h_range k hk
              · -- RegisterBelow
                rw [h_runD]
                show _ < _ + 1
                exact Nat.lt_succ_self _
              · -- placeRegMap unchanged
                rw [h_runD]
                exact h_qprm
              · -- nextReg monotone
                rw [h_runD]
                exact Nat.le_trans h_qregmono (Nat.le_succ _)
              · -- nextLabel monotone
                rw [h_runD]
                show cs.nextLabel ≤ _ + 1
                exact Nat.le_trans h_qlabmono (Nat.le_succ _)

end obseq3.proof
