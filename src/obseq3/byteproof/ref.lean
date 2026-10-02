import obseq3.byteproof.projdst

/-!
# The reference package

`dst := &kind src` (shared, mutable, raw; with or without a protector;
with the UnsafeCell mask expanded to bytes). Every borrow lowering is an
ANCHOR place's lowering followed by one `Borrow` at a byte offset:
- `&x`: the local itself, offset 0;
- `&*q`: the deref `*q` (its pointer loaded), offset 0;
- `&b.f`: the base `b`, at the field's byte offset.
`ref_pkg_core` proves the package once from three facts about the
anchor: the compiled shape (`BorrowAnchorShape`), the source's resolution
(`BorrowAnchorRes`), and that the anchor lowers (`LowersB`/`CompilesB`).
The retag is `sb_ref_respects_PermSim`, unchanged, which grows the tag
renaming by the minted pair.
-/

namespace obseq3.byteproof

open obseq3 obseq3.bytes obseq3.proof
open obseq3.mirlite (MemValue Binding Env PlaceRes)
open obseq3.oseair (Val Register)
open obseq3.compileB

/-! ## The anchor contract -/

/-- The compile-time half of lowering: a place whose root the source has
    bound compiles, with no cleanup and the place map unchanged. -/
def CompilesB {Γ : Ctx} (L : mirliteB.LayEnv Γ) {τ : LayoutTy} (p : Place Γ τ) : Prop :=
  ∀ (s : mirliteB.State MSB Γ) (cs : CompilerState) (kind : RefKind) (r : PlaceRes × MSB.State),
    (∀ {τ' : LayoutTy} (loc : Local Γ τ') (b : Binding), s.env.lookup loc = some b →
      ∃ reg layout, getPlaceInfo cs loc.idx.1 = some (reg, layout)) →
    mirliteB.resolvePlaceAcc MSB L s p = .ok r →
    ∃ out, CheckedCompilerM.value (placeToRegChecked L kind p) cs = .ok out ∧
      out.result.cleanup = [] ∧
      (CheckedCompilerM.run (placeToRegChecked L kind p) cs).placeRegMap = cs.placeRegMap

theorem ptrChain_compilesB {Γ : Ctx} {L : mirliteB.LayEnv Γ} {τ : LayoutTy} {p : Place Γ τ}
    (h : PtrChain p) : CompilesB L p :=
  fun _ _ kind r h_map h_res => ptrChain_compiles h_map h kind r h_res

/-- Borrowing `src` is lowering the anchor `a`, then one `Borrow` of
    `src`'s bytes at offset `o` from the anchor's pointer. -/
def BorrowAnchorShape {Γ : Ctx} (L : mirliteB.LayEnv Γ) {σ τ : LayoutTy} (src : Place Γ τ)
    (a : Place Γ σ) (o : Nat) : Prop :=
  ∀ (kind : RefKind) (prot : Bool) (mask : List Bool) (cs : CompilerState)
    (aOut : ResultWithEvidence PtrResult (PlaceToRegEvidence L kind a)),
    CheckedCompilerM.value (placeToRegChecked L kind a) cs = .ok aOut →
    aOut.result.cleanup = [] →
    CheckedCompilerM.run (placeToBorrowRegChecked L kind prot mask src) cs
      = emit (bumpReg (CheckedCompilerM.run (placeToRegChecked L kind a) cs))
          [oseairL.Instr.Assgn
            (Register.R (CheckedCompilerM.run (placeToRegChecked L kind a) cs).nextReg)
            (oseairL.Rhs.Borrow kind prot mask (some (placeSize L src)) aOut.result.reg o)] ∧
    ∃ out, CheckedCompilerM.value (placeToBorrowRegChecked L kind prot mask src) cs = .ok out ∧
      out.result.reg = Register.R (CheckedCompilerM.run (placeToRegChecked L kind a) cs).nextReg ∧
      out.result.cleanup =
        [(Register.R (CheckedCompilerM.run (placeToRegChecked L kind a) cs).nextReg,
          placeSize L src)]

/-- The source resolves `src` as the anchor, shifted by `o`. -/
def BorrowAnchorRes {Γ : Ctx} (L : mirliteB.LayEnv Γ) {σ τ : LayoutTy} (src : Place Γ τ)
    (a : Place Γ σ) (o : Nat) : Prop :=
  ∀ (s : mirliteB.State MSB Γ) (r : PlaceRes × MSB.State),
    mirliteB.resolvePlaceAcc MSB L s src = .ok r →
    ∃ ra : PlaceRes × MSB.State, mirliteB.resolvePlaceAcc MSB L s a = .ok ra ∧
      r.1.addr = ra.1.addr + o ∧ r.1.tag = ra.1.tag ∧ r.1.allocBase = ra.1.allocBase ∧
      r.1.allocSize = ra.1.allocSize ∧ r.2 = ra.2

/-! ## The three anchors -/

theorem borrow_local_shape {Γ : Ctx} {L : mirliteB.LayEnv Γ} {τ : LayoutTy} (loc : Local Γ τ) :
    BorrowAnchorShape L (.local loc) (.local loc) 0 := by
  intro kind prot mask cs aOut h_val h_clean
  simp only [placeToBorrowRegChecked, CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    h_val, CheckedCompilerM.run_lift, CheckedCompilerM.value_lift, CheckedCompilerM.run_pure,
    CheckedCompilerM.value_pure]
  exact ⟨rfl, _, rfl, rfl, rfl⟩

theorem borrow_local_res {Γ : Ctx} {L : mirliteB.LayEnv Γ} {τ : LayoutTy} (loc : Local Γ τ) :
    BorrowAnchorRes L (.local loc) (.local loc) 0 :=
  fun _ r h => ⟨r, h, rfl, rfl, rfl, rfl, rfl⟩

theorem borrow_deref_shape {Γ : Ctx} {L : mirliteB.LayEnv Γ} {σ : LayoutTy}
    (q : Place Γ (obseq.LayoutTy.PtrL σ)) :
    BorrowAnchorShape L (.deref q) (.deref q) 0 := by
  intro kind prot mask cs aOut h_val h_clean
  cases h_q : CheckedCompilerM.value (placeToRegChecked L RefKind.Shared q) cs with
  | error e =>
      exfalso
      have h_bind : placeToRegChecked L kind (.deref q)
          = (do
              let ptrOut ← placeToRegChecked L RefKind.Shared q
              let ptrRes := ptrOut.result
              let loadedReg ← CheckedCompilerM.lift freshRegM
              let _ ← CheckedCompilerM.lift
                (emitM [oseairL.Instr.Assgn loadedReg (oseairL.Rhs.Load (derefLoad L q) ptrRes.reg)])
              let _ ← CheckedCompilerM.lift (emitM (cleanupInstrs ptrRes.cleanup))
              pure {
                result := { reg := loadedReg, cleanup := [] },
                evidence := PlaceToRegEvidence.deref q ptrRes loadedReg ptrOut.evidence
              }) := by simp only [placeToRegChecked]
      rw [h_bind, CheckedCompilerM.value_bind, h_q] at h_val
      cases h_val
  | ok qOut =>
      obtain ⟨h_run, out, h_val', h_res⟩ := deref_lowering (kind := kind) h_q
      rw [h_val'] at h_val
      cases h_val
      rw [h_run]
      simp only [placeToBorrowRegChecked, CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
        h_q, CheckedCompilerM.run_lift, CheckedCompilerM.value_lift, CheckedCompilerM.run_pure,
        CheckedCompilerM.value_pure, h_res]
      exact ⟨rfl, _, rfl, rfl, rfl⟩

theorem borrow_deref_res {Γ : Ctx} {L : mirliteB.LayEnv Γ} {σ : LayoutTy}
    (q : Place Γ (obseq.LayoutTy.PtrL σ)) :
    BorrowAnchorRes L (.deref q) (.deref q) 0 :=
  fun _ r h => ⟨r, h, rfl, rfl, rfl, rfl, rfl⟩

theorem borrow_proj_shape {Γ : Ctx} {L : mirliteB.LayEnv Γ} {ρ τ : LayoutTy}
    {b : Place Γ ρ} (f : PathTo ρ τ)
    (h_np : ∀ (σ' : LayoutTy) (bb : Place Γ σ') (q : PathTo σ' ρ), b = bb.proj q → False) :
    BorrowAnchorShape L (.proj b f) b (pathOffset L b f) := by
  intro kind prot mask cs aOut h_val h_clean
  have h_bind : placeToBorrowRegChecked L kind prot mask (.proj b f)
      = (do
          let baseOut ← placeToRegChecked L kind b
          let baseRes := baseOut.result
          let offset := pathOffset L b f
          let tmpReg ← CheckedCompilerM.lift freshRegM
          let _ ← CheckedCompilerM.lift
            (emitM [oseairL.Instr.Assgn tmpReg
              (oseairL.Rhs.Borrow kind prot mask (some (placeSize L (.proj b f))) baseRes.reg offset)])
          pure {
            result := { reg := tmpReg,
                        cleanup := baseRes.cleanup ++ [(tmpReg, placeSize L (.proj b f))] },
            evidence := PlaceToBorrowRegEvidence.proj b f baseRes tmpReg baseOut.evidence
          }) := by
    cases b with
    | «local» loc => simp only [placeToBorrowRegChecked]
    | proj bb q => exact absurd rfl (h_np _ bb q)
    | deref pp => simp only [placeToBorrowRegChecked]
  rw [h_bind]
  simp only [CheckedCompilerM.run_bind, CheckedCompilerM.value_bind, h_val,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift, CheckedCompilerM.run_pure,
    CheckedCompilerM.value_pure]
  refine ⟨rfl, _, rfl, rfl, ?_⟩
  show aOut.result.cleanup ++ _ = _
  rw [h_clean]; rfl

theorem borrow_proj_res {Γ : Ctx} {L : mirliteB.LayEnv Γ} {ρ τ : LayoutTy}
    {b : Place Γ ρ} (f : PathTo ρ τ) :
    BorrowAnchorRes L (.proj b f) b (pathOffset L b f) := by
  intro s r h
  simp only [mirliteB.resolvePlaceAcc] at h
  cases h_b : mirliteB.resolvePlaceAcc MSB L s b with
  | error e => simp [h_b] at h
  | ok ra =>
      simp only [h_b, Except.ok.injEq] at h
      subst h
      exact ⟨ra, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The package -/

theorem LocalBindingSimB.rename_mono {Γ : Ctx} {L : mirliteB.LayEnv Γ} {ρt ρt' : TagRenameMap}
    {env : Env Γ} {s : oseairL.State MSB} {cs : CompilerState}
    (hi : TagRenameIncr ρt ρt') (h : LocalBindingSimB L ρt env s cs) :
    LocalBindingSimB L ρt' env s cs := by
  intro τ loc b h_env
  obtain ⟨r, t, hpi, he, hrt, hnw⟩ := h loc b h_env
  exact ⟨r, t, hpi, he, hi _ _ hrt, hnw⟩

theorem ref_pkg_core {Γ : Ctx} {L : mirliteB.LayEnv Γ} {compProg : oseairL.Prog}
    {σ τ : LayoutTy} {src : Place Γ τ} {a : Place Γ σ} {o : Nat}
    (h_shape : BorrowAnchorShape L src a o) (h_res : BorrowAnchorRes L src a o)
    (h_low : LowersB L compProg a) (h_comp : CompilesB L a)
    (dstL : BLayout) (kind : RefKind) (prot : Bool) (mask : List Bool) :
    ValuePkgB compProg L dstL (RExpr.ref kind prot mask src) := by
  intro ρt sM sA csA h_wf h_tbd h_lbs h_prb h_mem h_alloc h_psim h_pc _h_unmap output h_ev
  -- the source: resolve, check, retag
  simp only [mirliteB.evalRExpr] at h_ev
  cases h_r : mirliteB.resolvePlaceAcc MSB L sM src with
  | error e => simp [h_r] at h_ev
  | ok rr =>
  obtain ⟨resolved, permsR⟩ := rr
  simp only [h_r] at h_ev
  split at h_ev
  · cases h_ev
  rename_i h_free
  split at h_ev
  · cases h_ev
  rename_i h_bnd
  split at h_ev
  case h_2 => cases h_ev
  rename_i perms' freshTag h_ref
  simp only [mirliteB.EvalResult.ok.injEq] at h_ev
  subst h_ev
  obtain ⟨⟨aRes, permsA⟩, h_ra, h_addr, h_tag, h_ab, h_as, h_pa⟩ := h_res sM _ h_r
  simp only at h_addr h_tag h_ab h_as h_pa
  subst h_pa
  -- compile-time facts
  have h_map : ∀ {τ' : LayoutTy} (loc : Local Γ τ') (b : Binding), sM.env.lookup loc = some b →
      ∃ reg layout, getPlaceInfo csA loc.idx.1 = some (reg, layout) := fun loc b h => by
    obtain ⟨r, t, hpi, -⟩ := h_lbs loc b h
    exact ⟨r, _, hpi⟩
  obtain ⟨aOut, h_aval, h_aclean, h_aprm⟩ := h_comp sM csA kind _ h_map h_ra
  obtain ⟨h_brun, bOut, h_bval, h_breg, -⟩ :=
    h_shape kind prot (mirliteB.maskBytes (mirliteB.placeLayout L src) mask) csA aOut h_aval h_aclean
  have h_pre : CheckedCompilerM.run (compileRExprPreChecked L dstL (RExpr.ref kind prot mask src)) csA
      = CheckedCompilerM.run (placeToBorrowRegChecked L kind prot
          (mirliteB.maskBytes (mirliteB.placeLayout L src) mask) src) csA := by
    simp only [compileRExprPreChecked, CheckedCompilerM.run_bind, h_bval,
      CheckedCompilerM.run_pure]
  have h_preV : ∃ pOut, CheckedCompilerM.value
      (compileRExprPreChecked L dstL (RExpr.ref kind prot mask src)) csA = .ok pOut ∧
      (∀ d, pOut.store d = [oseairL.Instr.RStore dstL bOut.result.reg d]) ∧
      pOut.postCleanup = [] := by
    simp only [compileRExprPreChecked, CheckedCompilerM.value_bind, h_bval,
      CheckedCompilerM.value_pure]
    exact ⟨_, rfl, fun _ => rfl, rfl⟩
  obtain ⟨pOut, h_pval, h_store, h_post⟩ := h_preV
  refine ⟨_, pOut, h_pval, h_store, h_post, ?_, fun h_code => ?_⟩
  · rw [h_pre, h_brun]; exact h_aprm
  rw [h_pre, h_brun] at h_code ⊢
  -- the anchor's lowering
  obtain ⟨aOut', n1, s1, tres, hA⟩ :=
    h_low ρt sM kind csA sA aRes permsR h_wf h_ra h_tbd h_lbs h_prb h_mem h_alloc h_psim h_pc
      (h_code.mono ((bumpReg_state_incr' _).trans (emit_state_incr _ _)))
  have h_same : aOut' = aOut := by
    have := hA.val
    rw [h_aval] at this
    exact (Except.ok.inj this).symm
  subst h_same
  obtain ⟨ext, h_aentry⟩ := hA.entry
  have hB : aRes.allocBase + (aRes.addr - aRes.allocBase) = aRes.addr :=
    Nat.add_sub_cancel' hA.le
  -- the retag, transported
  have h_tbd1 : TagRenameBounded ρt permsR.NextTag s1.perms.NextTag := by
    rw [hA.srcNT]; exact TagRenameBounded.mono h_tbd (Nat.le_refl _) hA.tgtNT
  rw [h_addr, h_tag] at h_ref
  obtain ⟨tgt', h_ref', h_fresh, h_incr, h_wf', h_tbd', h_psim'⟩ :=
    sb_ref_respects_PermSim hA.psim h_wf h_tbd1 hA.rt h_ref
  subst h_fresh
  have h_freeT : s1.mem.isFreed aRes.allocBase = false := by
    have h_lock1 : ByteAllocLockstep sM.mem s1.mem := by rw [hA.mem]; exact h_alloc
    rw [h_ab] at h_free
    simp only [bytes.Mem.isFreed, ← h_lock1.2.2] at h_free ⊢
    simpa using h_free
  have h_bnd' : aRes.allocBase + (aRes.addr - aRes.allocBase) + o + placeSize L src
      ≤ aRes.allocBase + aRes.allocSize := by
    rw [hB, ← h_addr, ← h_ab, ← h_as]; exact Nat.le_of_not_gt h_bnd
  have h_instr : compProg s1.pc = some (oseairL.Instr.Assgn
      (Register.R (CheckedCompilerM.run (placeToRegChecked L kind a) csA).nextReg)
      (oseairL.Rhs.Borrow kind prot (mirliteB.maskBytes (mirliteB.placeLayout L src) mask)
        (some (placeSize L src)) aOut'.result.reg o)) := by
    rw [hA.pc]
    apply h_code
    · simp [emit]
    · simp [emit]
  have h_run1 := runN_Borrow (s := s1) h_instr h_aentry h_freeT h_bnd'
    (by rw [hB]; exact h_ref')
  refine ⟨ρt.extend permsR.NextTag s1.perms.NextTag, n1 + 1, _, sM.mem, perms',
    [Val.Ptr aRes.allocBase (aRes.addr - aRes.allocBase + o) (placeSize L src) aRes.allocSize
      s1.perms.NextTag], h_incr, h_wf', rfl, runN_trans hA.run h_run1, ?_, ?_, h_psim', h_tbd',
    ?_, ?_, ?_, ?_, ?_⟩
  · show csA.nextReg ≤ _ + 1
    exact Nat.le_trans hA.regmono (Nat.le_succ _)
  · refine LocalBindingSimB.prm_congr (LocalBindingSimB.of_frame
      (LocalBindingSimB.rename_mono h_incr h_lbs) h_prb fun r hr => ?_) hA.prm
    have hne := RegisterBelow.ne_fresh (RegisterBelow.mono hA.regmono hr)
    show (s1.reg.insert _ _).lookup r = _
    rw [RegMap.lookup_insert_ne _ _ hne]
    exact hA.frame r hr
  · show ByteMemSim _ sM.mem s1.mem
    rw [hA.mem]; exact ByteMemSim.rename_mono h_incr h_mem
  · show ByteAllocLockstep sM.mem s1.mem
    rw [hA.mem]; exact h_alloc
  · show s1.pc + 1 = _
    rw [hA.pc]; rfl
  · rw [← h_breg]
    exact StoreStepB.rstore compProg _ _ dstL _ _ (by rw [h_breg]; exact RegMap.lookup_insert_self _ _ _)
      (by rw [h_breg]; show _ < _ + 1; omega)
  · refine ⟨Or.inr ⟨by simp, ?_⟩, trivial⟩
    simp only [ValSim, oseairB.Val.toMem, oseairB.ofMem, MemValSim, idA, h_ab, h_as]
    exact ⟨trivial, by rw [h_addr, Nat.sub_add_comm hA.le], trivial, trivial,
      TagRenameMap.extend_self _ _ _, fun _ _ => ⟨_, rfl⟩⟩

/-! ## Instances -/

/-- `&x`. -/
theorem ref_local_pkg {Γ : Ctx} {L : mirliteB.LayEnv Γ} {compProg : oseairL.Prog}
    (hWF : PtrPlacesWF L) {τ : LayoutTy} (loc : Local Γ τ)
    (dstL : BLayout) (kind : RefKind) (prot : Bool) (mask : List Bool) :
    ValuePkgB compProg L dstL (RExpr.ref kind prot mask (.local loc)) :=
  ref_pkg_core (borrow_local_shape loc) (borrow_local_res loc)
    (ptrChain_lowers hWF (PtrChain.base loc)) (ptrChain_compilesB (PtrChain.base loc))
    dstL kind prot mask

/-- `&*q`, `&*(*p).f`, …: a deref chain. -/
theorem ref_deref_pkg {Γ : Ctx} {L : mirliteB.LayEnv Γ} {compProg : oseairL.Prog}
    (hWF : PtrPlacesWF L) {σ : LayoutTy} {q : Place Γ (obseq.LayoutTy.PtrL σ)}
    (h_chain : PtrChain (.deref q))
    (dstL : BLayout) (kind : RefKind) (prot : Bool) (mask : List Bool) :
    ValuePkgB compProg L dstL (RExpr.ref kind prot mask (.deref q)) :=
  ref_pkg_core (borrow_deref_shape q) (borrow_deref_res q)
    (ptrChain_lowers hWF h_chain) (ptrChain_compilesB h_chain) dstL kind prot mask

/-- `&b.f` with `b` a chain (a local or a deref chain). -/
theorem ref_proj_pkg {Γ : Ctx} {L : mirliteB.LayEnv Γ} {compProg : oseairL.Prog}
    (hWF : PtrPlacesWF L) {ρ τ : LayoutTy} {b : Place Γ ρ} (f : PathTo ρ τ)
    (h_chain : PtrChain b)
    (dstL : BLayout) (kind : RefKind) (prot : Bool) (mask : List Bool) :
    ValuePkgB compProg L dstL (RExpr.ref kind prot mask (.proj b f)) :=
  ref_pkg_core (borrow_proj_shape f (PtrChain.not_proj h_chain)) (borrow_proj_res f)
    (ptrChain_lowers hWF h_chain) (ptrChain_compilesB h_chain) dstL kind prot mask

end obseq3.byteproof
