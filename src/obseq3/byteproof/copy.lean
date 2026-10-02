import obseq3.byteproof.spine

/-!
# The byte-level copy package — bound-local source

`dst := copy src` with `src` a bound local lowers (`compileB.readRhsPre`)
to one `Load` at the SOURCE's byte layout into a fresh register, then an
`RStore` of that register at the DESTINATION's layout. Its value package:
the source's typed read (liveness, bounds, SB read, decoded leaves, no
undef leaf) is matched by the `Load` — the spike's `load_step_sim` — and
the loaded values are `StoreSim`-related because none is undef.

Projected and dereferenced sources need the byte place-lowering
simulation (the cell proof's `ptrChain_lowering_sim`) and come next.
-/

namespace obseq3.byteproof

open obseq3 obseq3.bytes obseq3.proof
open obseq3.mirlite (MemValue Binding Env)
open obseq3.oseair (Val Register)
open obseq3.compileB

/-! ## Registers -/

theorem RegMap.lookup_insert_self (r : oseairL.RegMap) (reg : Register) (vs : List Val) :
    (r.insert reg vs).lookup reg = some vs := by
  simp [oseairL.RegMap.insert, oseairL.RegMap.lookup]

theorem RegMap.lookup_insert_ne (r : oseairL.RegMap) {reg reg' : Register} (vs : List Val)
    (h : reg' ≠ reg) : (r.insert reg vs).lookup reg' = r.lookup reg' := by
  simp only [oseairL.RegMap.insert, oseairL.RegMap.lookup, List.lookup]
  have hb : (reg' == reg) = false := by simp [h]
  rw [hb]
  exact lookup_filter_ne h r

theorem RegisterBelow.ne_fresh {n : Nat} {r : Register} (h : RegisterBelow n r) :
    r ≠ Register.R n := by
  cases r with
  | R i => intro h'; cases h'; exact Nat.lt_irrefl _ h

/-! ## Values -/

theorem ofMem_toMem (w : Val) : oseairB.ofMem (oseairB.Val.toMem w) = w := by
  cases w <;> rfl

theorem toMem_ofMem (v : MemValue) : oseairB.Val.toMem (oseairB.ofMem v) = v := by
  cases v <;> rfl

/-- A defined source leaf read as `ValSim`-related to a target leaf: the
    target leaf is defined, and the pair is `StoreSim`-related. -/
theorem storeSim_of_read {ρt : TagRenameMap} {v w : MemValue}
    (h : ValSim ρt v w) (hv : v ≠ .undef) :
    oseairB.ofMem w ≠ Val.Undef ∧
    StoreSim ρt v (oseairB.Val.toMem (oseairB.ofMem w)) := by
  refine ⟨?_, Or.inr ⟨hv, ?_⟩⟩
  · intro hw
    simp only [ValSim, hw] at h
    cases v <;> simp_all [MemValSim]
  · simpa [ValSim, toMem_ofMem] using h

theorem readL_rel {ρt : TagRenameMap} :
    ∀ {vs ws : List MemValue}, ListRel (ValSim ρt) vs ws →
      (vs.any (fun v => v == .undef)) = false →
      ((ws.map oseairB.ofMem).any (fun v => v == Val.Undef)) = false ∧
      ListRel (StoreSim ρt) vs ((ws.map oseairB.ofMem).map oseairB.Val.toMem)
  | [], [], _, _ => ⟨rfl, trivial⟩
  | v :: vs, w :: ws, ⟨h, hs⟩, hany => by
      simp only [List.any_cons, Bool.or_eq_false_iff] at hany
      have hv : v ≠ .undef := by
        intro h'; subst h'; exact absurd hany.1 (by decide)
      obtain ⟨hw, hst⟩ := storeSim_of_read h hv
      obtain ⟨hws, hrest⟩ := readL_rel hs (by simpa using hany.2)
      refine ⟨?_, hst, hrest⟩
      simp only [List.map_cons, List.any_cons, hws, Bool.or_false]
      cases hc : oseairB.ofMem w with
      | Undef => exact absurd hc hw
      | Dat _ => rfl
      | Ptr _ _ _ _ _ => rfl
  | [], _ :: _, h, _ => h.elim
  | _ :: _, [], h, _ => h.elim

/-! ## The compiled shape of a read-then-store rvalue off a bound local -/

theorem readRhsPre_local {Γ : Ctx} {L : mirliteB.LayEnv Γ} {dstL : BLayout}
    {σ τ : LayoutTy} {rhs : RExpr Γ τ} {l : Local Γ σ} {mk : Register → oseairL.Rhs}
    {post : Register → List oseairL.Instr}
    {ev : (srcRes : PtrResult) → PlaceToRegEvidence L RefKind.Shared (.local l) srcRes →
      (dstPtr : Register) → RExprToEvidence L dstPtr rhs}
    {cs : CompilerState} {reg : Register} {layout : LayoutTy}
    (h : getPlaceInfo cs l.idx.1 = some (reg, layout)) :
    CheckedCompilerM.run (readRhsPre L dstL rhs (.local l) mk post ev) cs
      = emit { cs with nextReg := cs.nextReg + 1 }
          ([oseairL.Instr.Assgn (Register.R cs.nextReg) (mk reg)] ++ post (Register.R cs.nextReg)) ∧
    ∃ pOut, CheckedCompilerM.value (readRhsPre L dstL rhs (.local l) mk post ev) cs
        = Except.ok pOut ∧
      (∀ d, pOut.store d = [oseairL.Instr.RStore dstL (Register.R cs.nextReg) d]) ∧
      pOut.postCleanup = [] := by
  obtain ⟨h_run, out, h_val, h_res⟩ :=
    placeToRegChecked_local_existing (L := L) (kind := RefKind.Shared) h
  simp only [readRhsPre, CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift, CheckedCompilerM.run_pure,
    CheckedCompilerM.value_pure, h_run, h_val, h_res]
  refine ⟨?_, _, rfl, fun _ => rfl, rfl⟩
  simp only [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM, cleanupInstrs,
    List.reverse_nil, List.map_nil, List.append_nil]

/-! ## The package -/

theorem copy_local_pkg {Γ : Ctx} {σ : LayoutTy} {compProg : oseairL.Prog}
    {L : mirliteB.LayEnv Γ} (dstL : BLayout) (l : Local Γ σ) :
    ValuePkgB compProg L dstL (RExpr.copy (.local l)) := by
  intro ρt sM sA csA h_wf h_tbd h_lbs h_prb h_mem h_alloc h_psim h_pc output h_ev
  -- the source: a bound local, read whole
  cases h_env : sM.env.lookup l with
  | none =>
      simp [mirliteB.evalRExpr, mirliteB.evalCopy, mirliteB.resolvePlaceAcc, h_env] at h_ev
  | some b =>
  simp only [mirliteB.evalRExpr, mirliteB.evalCopy, mirliteB.resolvePlaceAcc,
    mirliteB.placeLayout, h_env] at h_ev
  obtain ⟨reg, tag, h_pi, ⟨ext, h_reg⟩, h_rt, -⟩ := h_lbs l b h_env
  split at h_ev
  · cases h_ev
  rename_i h_free
  split at h_ev
  · cases h_ev
  rename_i h_bnd
  split at h_ev
  · cases h_ev
  rename_i permsR hu
  split at h_ev
  · cases h_ev
  rename_i h_def
  simp only [mirliteB.EvalResult.ok.injEq] at h_ev
  subst h_ev
  -- the compiled shape
  obtain ⟨h_run, pOut, h_val, h_store, h_post⟩ :=
    readRhsPre_local (L := L) (dstL := dstL) (rhs := RExpr.copy (.local l))
      (mk := oseairL.Rhs.Load (L l.idx)) (post := fun _ => [])
      (ev := fun srcRes evd _ => RExprToEvidence.copy (.local l) srcRes evd) h_pi
  have h_pre : compileRExprPreChecked L dstL (RExpr.copy (.local l))
      = readRhsPre L dstL (RExpr.copy (.local l)) (.local l) (oseairL.Rhs.Load (L l.idx))
          (fun _ => []) (fun srcRes evd _ => RExprToEvidence.copy (.local l) srcRes evd) := rfl
  rw [h_pre]
  refine ⟨_, pOut, h_val, h_store, h_post, by rw [h_run]; rfl, fun h_code => ?_⟩
  rw [h_run] at h_code ⊢
  -- the target: the `Load`
  have h_instr : compProg sA.pc = some (oseairL.Instr.Assgn (Register.R csA.nextReg)
      (oseairL.Rhs.Load (L l.idx) reg)) := by
    rw [h_pc]
    apply h_code
    · simp [emit]
    · simp [emit]
  obtain ⟨pT', hu', hp', hrel⟩ := load_step_sim h_wf h_psim h_mem h_rt (a := b.addr)
    (lay := L l.idx) hu
  have h_freeT : sA.mem.isFreed b.addr = false := by
    simp only [bytes.Mem.isFreed, h_alloc.2.2] at h_free ⊢
    simpa using h_free
  obtain ⟨h_defT, h_relS⟩ := readL_rel hrel (by simpa using h_def)
  let vals := (mirliteB.readL sA.mem b.addr (L l.idx)).map oseairB.ofMem
  let sR : oseairL.State MSB :=
    { sA with perms := pT', reg := sA.reg.insert (Register.R csA.nextReg) vals,
              pc := sA.pc + 1 }
  refine ⟨ρt, 1, sR, sM.mem, permsR, vals, TagRenameIncr.refl ρt, h_wf, rfl, ?_, by simp [emit], ?_, hp', ?_,
    h_mem, h_alloc, by show sA.pc + 1 = _; simp [emit, h_pc], ?_, h_relS⟩
  · -- one target step
    simp only [PermissionModel.stackedBorrows] at hu'
    simp only [oseairL.runN, oseairL.step, h_instr, oseairL.evalRhs, h_reg, h_freeT,
      Nat.add_zero, gt_iff_lt, Nat.lt_irrefl, if_false, PermissionModel.stackedBorrows, hu',
      Bool.false_eq_true]
    simp only [h_defT, Bool.false_eq_true, if_false]
    rfl
  · -- bound locals keep their registers: theirs are below the fresh one
    intro τ' loc' b' h'
    obtain ⟨r, t, hpi, ⟨e, hr⟩, hrt, hnw⟩ := h_lbs loc' b' h'
    refine ⟨r, t, hpi, ⟨e, ?_⟩, hrt, hnw⟩
    rw [RegMap.lookup_insert_ne _ _ (RegisterBelow.ne_fresh (h_prb _ _ _ hpi))]
    exact hr
  · have h1 := sb_read_NextTag hu
    have h2 := sb_read_NextTag hu'
    simp only [PermissionModel.stackedBorrows] at h1 h2
    show TagRenameBounded ρt permsR.NextTag pT'.NextTag
    rw [h1, h2]
    exact h_tbd
  · -- the store writes the loaded register
    exact StoreStepB.rstore compProg _ _ dstL (Register.R csA.nextReg) vals
      (RegMap.lookup_insert_self _ _ _) (show csA.nextReg < csA.nextReg + 1 by omega)

/-- `x := copy y`, both bound locals, at any layouts (a layout mismatch
    fails the source's store, so it is outside the hypothesis). -/
theorem copy_local_local_sim {Γ : Ctx} {L : mirliteB.LayEnv Γ} {ρt : TagRenameMap}
    {s_mir s_mir' : mirliteB.State MSB Γ} {s_osea : oseairL.State MSB}
    {τ : LayoutTy} {loc l : Local Γ τ} {b : Binding} {cs : CompilerState}
    (compProg : oseairL.Prog)
    (h_inv : InvAtB L ρt s_mir s_osea cs)
    (h_code : CodeIncludedB compProg
      (CheckedCompilerM.run (compileStmtChecked L (.assign (.local loc) (.copy (.local l)))) cs))
    (h_env : s_mir.env.lookup loc = some b)
    (h_step : mirliteB.stepStmt MSB L s_mir (.assign (.local loc) (.copy (.local l)))
      = .ok s_mir') :
    ∃ (ρt' : TagRenameMap) (s_osea' : oseairL.State MSB) (n : Nat),
      TagRenameIncr ρt ρt' ∧
      oseairL.runN MSB n s_osea compProg = .Ok s_osea' ∧
      InvAtB L ρt' s_mir' s_osea'
        (CheckedCompilerM.run (compileStmtChecked L (.assign (.local loc) (.copy (.local l)))) cs) :=
  storereg_local_simB compProg (copy_local_pkg _ l) h_inv h_code h_env h_step

end obseq3.byteproof
