import obseq3.proof.common
import obseq3.proof.permsim_transport
import obseq3.proof.spine

namespace obseq3.proof

/-! ### Ambient binders

    The data every simulation leaf and fragment-transfer lemma
    quantifies over. These are IMPLICIT and every leaf's conclusion
    mentions them, so Lean includes them automatically — no `include` is
    needed, and because they were already the leading binders the
    explicit argument order is unchanged.

    A theorem that binds its own `{Γ : Ctx}` shadows these cleanly and
    picks up none of them. -/
variable {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
variable {ρa : AddrRenameMap} {ρt : TagRenameMap}
variable {s_mir s_mir' : mirlite.State MSB Γ}
variable {s_osea : oseair.State MSB}


open obseq3
open obseq3.compile
open obseq3.oseair (Instr Register Rhs Val)



/-- A path never grows its target: every step descends into a tuple
    field, so the destination layout is a subterm of the source. -/
theorem PathTo.sizeOf_le {σ ρ : LayoutTy} (p : PathTo σ ρ) :
    sizeOf ρ ≤ sizeOf σ := by
  induction p with
  | nil => exact Nat.le_refl _
  | @field ρ' tys idx rest ih =>
      have h_lt : sizeOf (tys.get idx) < sizeOf tys :=
        List.sizeOf_lt_of_mem (List.get_mem tys idx)
      grind [obseq.LayoutTy.TupL.sizeOf_spec]





/-! ## The compiled fragment of a `local := &local` retag -/

/-- The fragment of `dst := &src` when the DESTINATION is unmapped: the
    root `Alloc` that `ensureLocalRegE` emits, then the `Borrow` into a
    fresh temp, then the `RStore`. Three instructions, and the only ref
    shape whose compiler state grows a `placeRegMap` entry. -/
theorem compileStmt_ref_fresh_local_lowers
    {Γ : Ctx} {τ : LayoutTy}
    {dstLoc : Local Γ (obseq.LayoutTy.PtrL τ)} {srcLoc : Local Γ τ}
    {cs : CompilerState} {srcReg : Register}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = none)
    (h_src : getPlaceInfo cs srcLoc.idx.1 = some (srcReg, τ)) :
    LowersTo
        (compileStmtChecked
          (Stmt.assign (.local dstLoc) (.ref kind prot mask (.local srcLoc)))) cs
      (emit (emit
          { (setPlaceInfo
              (emit { cs with nextReg := cs.nextReg + 1 }
                [Instr.Assgn (Register.R cs.nextReg)
                  (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))])
              dstLoc.idx.1 (Register.R cs.nextReg, obseq.LayoutTy.PtrL τ)) with
              nextReg := cs.nextReg + 1 + 1 }
          [Instr.Assgn (Register.R (cs.nextReg + 1))
            (Rhs.Borrow kind prot mask (some (blockSize τ)) srcReg 0)])
          [Instr.RStore obseq.TyVal.PTy (Register.R (cs.nextReg + 1))
            (Register.R cs.nextReg)]) := by
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_fresh (loc := dstLoc) h_dst
  have h_run' : (ensureLocalRegE dstLoc cs).snd.val
      = setPlaceInfo
          (emit { cs with nextReg := cs.nextReg + 1 }
            [Instr.Assgn (Register.R cs.nextReg)
              (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))])
          dstLoc.idx.1 (Register.R cs.nextReg, obseq.LayoutTy.PtrL τ) := h_run
  have h_srcPost : getPlaceInfo
      (setPlaceInfo
        (emit { cs with nextReg := cs.nextReg + 1 }
          [Instr.Assgn (Register.R cs.nextReg)
            (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))])
        dstLoc.idx.1 (Register.R cs.nextReg, obseq.LayoutTy.PtrL τ))
      srcLoc.idx.1 = some (srcReg, τ) := by
    by_cases h_eq : srcLoc.idx.1 = dstLoc.idx.1
    · exfalso
      grind
    · rw [getPlaceInfo_setPlaceInfo_ne _ h_eq, getPlaceInfo_emit]
      exact h_src
  refine ⟨?_, ?_⟩
  · obtain ⟨h_prun, placeOut, h_pval, h_pres⟩ :=
      placeToRegChecked_local_existing (kind := kind) h_srcPost
    rw [compileStmt_local_run]
    simp [compileRExprToChecked, compileRExprPreChecked, placeToBorrowRegChecked, h_run, h_val,
      h_prun, h_pval, h_pres]
    simp [csRun, cleanupInstrs, emit_nil, setPlaceInfo, emit]
    funext label
    rw [if_neg (fun h => by grind)]
  · obtain ⟨h_prun, placeOut, h_pval, h_pres⟩ :=
      placeToRegChecked_local_existing (kind := kind) h_srcPost
    refine (compileStmt_local_value_iff _ _ cs).mpr ?_
    simp only [csMonad, compileRExprToChecked, compileRExprPreChecked, placeToBorrowRegChecked,
      h_run, h_pval]
    exact ⟨_, rfl⟩
/-! ## Regime L→L: `dstLocal := &srcLocal`, both bound -/

/-! ## `ref` as a value package

A retag is a read-then-store rvalue too. Its pre-phase is the borrow
lowering, and the register it stores is the one that lowering ALREADY
allocated for the `Borrow`'s result — so unlike copy, whose arm allocates
a further register for the `Load` to land in, the ref arm allocates none
of its own and emits no instruction of its own. Either way exactly one
register holds the value and exactly one `RStore` writes it, which is
what lets ref's leaves BE copy's leaves.

The borrow temp is deliberately NOT retired: `placeToBorrowRegChecked`
returns it with a `cleanup` entry and the ref arm drops it, because the
reference is being written INTO memory and its tag has to stay live past
the statement. Copy's source cleanup, by contrast, is emitted right after
the `Load`.

Every ref source is the projection `f` of a POINTER CHAIN `B` — a bare
local at the nil path, a projected local, a deref, a projected deref.
`RefSrcShape` is what those four have in common: mirlite resolves the
source as the chain's resolution shifted by `f`, and the compiled
pre-phase is the chain's lowering at `kindL` followed by exactly one
`Borrow` at `f`'s offset. The lowering kind is a parameter because a
bare deref lowers its chain `Shared` while a projection lowers it at the
retag's own kind. -/

/-- The code `move` adds after its source chain: `Borrow(Mut)` into a fresh
    temporary at the projection's offset (the clear), `Load` through it into
    a second temporary (the value), `Die` the first. -/
def moveTail (csD : CompilerState) (reg : Register) (off sz : Nat) (ty : obseq.TyVal) :
    CompilerState :=
  emit { (emit { csD with nextReg := csD.nextReg + 1 }
      [Instr.Assgn (Register.R csD.nextReg)
        (Rhs.Borrow RefKind.Mut false [] (some sz) reg off)])
      with nextReg := csD.nextReg + 1 + 1 }
    [Instr.Assgn (Register.R (csD.nextReg + 1)) (Rhs.Load ty (Register.R csD.nextReg)),
     Instr.Die (Register.R csD.nextReg) sz]

/-- A chain's lowering retires nothing: a local is a lookup, a deref's
    loaded register is not a borrow. -/
theorem PtrChain.placeToRegChecked_cleanup_nil {Γ : Ctx} {τ : LayoutTy} {B : Place Γ τ}
    (h : PtrChain B) (kind : RefKind) (cs : CompilerState)
    {dOut : ResultWithEvidence PtrResult (PlaceToRegEvidence kind B)}
    (h_dval : CheckedCompilerM.value (placeToRegChecked kind B) cs = Except.ok dOut) :
    dOut.result.cleanup = [] := by
  cases h with
  | base loc =>
      simp only [placeToRegChecked, CheckedCompilerM.value, CompilerM.value] at h_dval
      split at h_dval
      · cases h_dval; rfl
      · cases h_dval
  | deref hp =>
      rename_i P
      have h_bindD : placeToRegChecked (Γ := Γ) kind (.deref P)
          = (do
              let ptrOut ← placeToRegChecked RefKind.Shared P
              let ptrRes := ptrOut.result
              let loadedReg ← CheckedCompilerM.lift freshRegM
              let _ ← CheckedCompilerM.lift
                (emitM [Instr.Assgn loadedReg (Rhs.Load obseq.TyVal.PTy ptrRes.reg)])
              let _ ← CheckedCompilerM.lift (emitM (cleanupInstrs ptrRes.cleanup))
              pure {
                result := { reg := loadedReg, cleanup := [] },
                evidence := PlaceToRegEvidence.deref P ptrRes loadedReg ptrOut.evidence
              }) := by simp only [placeToRegChecked]
      rw [h_bindD] at h_dval
      simp only [csMonad] at h_dval
      split at h_dval
      · cases h_dval; rfl
      · cases h_dval
  | derefProj f hb =>
      rename_i b
      have h_bindD : placeToRegChecked (Γ := Γ) kind (.deref (.proj b f))
          = (do
              let ptrOut ← placeToRegChecked RefKind.Shared (.proj b f)
              let ptrRes := ptrOut.result
              let loadedReg ← CheckedCompilerM.lift freshRegM
              let _ ← CheckedCompilerM.lift
                (emitM [Instr.Assgn loadedReg (Rhs.Load obseq.TyVal.PTy ptrRes.reg)])
              let _ ← CheckedCompilerM.lift (emitM (cleanupInstrs ptrRes.cleanup))
              pure {
                result := { reg := loadedReg, cleanup := [] },
                evidence := PlaceToRegEvidence.deref (.proj b f) ptrRes loadedReg
                  ptrOut.evidence
              }) := by simp only [placeToRegChecked]
      rw [h_bindD] at h_dval
      simp only [csMonad] at h_dval
      split at h_dval
      · cases h_dval; rfl
      · cases h_dval

/-- The source-shape bundle: three facts, one mirlite and two compiled. -/
structure RefSrcShape {Γ : Ctx} {σb τ : LayoutTy}
    (kindL kind : RefKind) (prot : Bool) (mask : List Bool)
    (B : Place Γ σb) (f : PathTo σb τ) (src : Place Γ τ) : Prop where
  /-- the base is a pointer chain, so the mother lemma applies -/
  chain : PtrChain B
  /-- mirlite resolves the source as the chain shifted by `f` -/
  resolve : ∀ (s : mirlite.State MSB Γ) (r : mirlite.PlaceRes) (p : MSB.State),
    mirlite.resolvePlaceAcc MSB s B = .ok (r, p) →
    mirlite.resolvePlaceAcc MSB s src
      = .ok ({ r with addr := r.addr + PathTo.offset f }, p)
  /-- and it fails exactly when the chain fails -/
  resolveErr : ∀ (s : mirlite.State MSB Γ) (e : String),
    mirlite.resolvePlaceAcc MSB s B = .error e →
    mirlite.resolvePlaceAcc MSB s src = .error e
  /-- the rvalue's code: the chain's lowering, then one `Borrow` -/
  preRun : ∀ (cs : CompilerState)
      (dOut : ResultWithEvidence PtrResult (PlaceToRegEvidence kindL B)),
    CheckedCompilerM.value (placeToRegChecked kindL B) cs = Except.ok dOut →
    CheckedCompilerM.run
        (compileRExprPreChecked (RExpr.ref kind prot mask src)) cs
      = emit { (CheckedCompilerM.run (placeToRegChecked kindL B) cs) with
            nextReg :=
              (CheckedCompilerM.run (placeToRegChecked kindL B) cs).nextReg + 1 }
          [Instr.Assgn
            (Register.R
              (CheckedCompilerM.run (placeToRegChecked kindL B) cs).nextReg)
            (Rhs.Borrow kind prot mask (some (blockSize τ)) dOut.result.reg
              (pathOffset f))]
  /-- and it stores the `Borrow`'s register, with nothing to clean up -/
  preValue : ∀ (cs : CompilerState)
      (dOut : ResultWithEvidence PtrResult (PlaceToRegEvidence kindL B)),
    CheckedCompilerM.value (placeToRegChecked kindL B) cs = Except.ok dOut →
    ∃ pOut : RhsPre Γ (obseq.LayoutTy.PtrL τ) (RExpr.ref kind prot mask src),
      CheckedCompilerM.value
          (compileRExprPreChecked (RExpr.ref kind prot mask src)) cs
        = Except.ok pOut ∧
      (∀ d, pOut.store d = [Instr.RStore obseq.TyVal.PTy
        (Register.R
          (CheckedCompilerM.run (placeToRegChecked kindL B) cs).nextReg) d]) ∧
      pOut.postCleanup = []
  /-- `move`'s code at the same source (2026-09-20): the chain's lowering,
      one `Borrow(Mut)` — the clear — the `Load` through it, its `Die`. -/
  movePreRun : ∀ (cs : CompilerState)
      (dOut : ResultWithEvidence PtrResult (PlaceToRegEvidence kindL B)),
    CheckedCompilerM.value (placeToRegChecked kindL B) cs = Except.ok dOut →
    dOut.result.cleanup = [] →
    kind = RefKind.Mut →
    CheckedCompilerM.run (compileRExprPreChecked (RExpr.move src)) cs
      = moveTail (CheckedCompilerM.run (placeToRegChecked kindL B) cs)
          dOut.result.reg (pathOffset f) (blockSize τ) (layoutToTyVal τ)
  /-- and it stores the `Load`'s register, with nothing to clean up -/
  movePreValue : ∀ (cs : CompilerState)
      (dOut : ResultWithEvidence PtrResult (PlaceToRegEvidence kindL B)),
    CheckedCompilerM.value (placeToRegChecked kindL B) cs = Except.ok dOut →
    kind = RefKind.Mut →
    ∃ pOut : RhsPre Γ τ (RExpr.move src),
      CheckedCompilerM.value (compileRExprPreChecked (RExpr.move src)) cs
        = Except.ok pOut ∧
      (∀ d, pOut.store d = [Instr.RStore (layoutToTyVal τ)
        (Register.R
          ((CheckedCompilerM.run (placeToRegChecked kindL B) cs).nextReg + 1)) d]) ∧
      pOut.postCleanup = []

/-- Every ref source is a value package. The proof is the source half of
    what used to be four separate leaves: the mother lemma through
    `ref_chainsrc_borrow`, and the code-position bookkeeping that used to
    reach into the STATEMENT's fragment now reaching only into the
    rvalue's own. -/
theorem ref_valuePkg_chain
    {σb τ : LayoutTy} {B : Place Γ σb} {f : PathTo σb τ}
    {src : Place Γ τ} {kindL kind : RefKind} {prot : Bool} {mask : List Bool}
    (compProg : oseair.Prog)
    (h_shape : RefSrcShape kindL kind prot mask B f src) :
    ValuePkg compProg (RExpr.ref kind prot mask src) := by
  intro ρa ρt sM sA csA h_id_a h_wf_t h_tbd h_lbs h_prb h_sms h_alloc h_psim h_pc
    output h_eval
  -- §1 invert the retag: the chain resolves, the range fits, the mint
  -- succeeds
  simp only [mirlite.evalRExpr] at h_eval
  cases h_dres : mirlite.resolvePlaceAcc MSB sM B with
  | error e =>
      rw [h_shape.resolveErr _ _ h_dres] at h_eval; simp at h_eval
  | ok pr =>
  obtain ⟨resolved, permsR⟩ := pr
  rw [h_shape.resolve _ _ _ h_dres] at h_eval
  simp only at h_eval
  by_cases h_fit : resolved.addr + PathTo.offset f + blockSize τ
      > resolved.allocBase + resolved.allocSize
  · rw [if_pos h_fit] at h_eval; simp at h_eval
  · rw [if_neg h_fit] at h_eval
    cases h_ref_src : MSB.ref permsR (resolved.addr + PathTo.offset f)
        (blockSize τ) resolved.tag kind prot mask with
    | error e => rw [h_ref_src] at h_eval; simp at h_eval
    | ok pr2 =>
    obtain ⟨perms', freshTag⟩ := pr2
    rw [h_ref_src] at h_eval
    injection h_eval with h_out
    subst h_out
    -- §2 the chain's lowering is well-formed, so the rvalue's code shape
    -- is known
    have h_mapped : PlaceInputsMapped csA B :=
      placeInputsMapped_of_localBindingSim_resolvePlace h_lbs
        (resolvePlace?_of_resolveAcc h_dres)
    obtain ⟨dOut, h_dval⟩ := placeToRegChecked_ok_of_placeInputsMapped
      (cs := csA) (kind := kindL) h_mapped
    have h_pre := h_shape.preRun csA dOut h_dval
    obtain ⟨pOut, h_pval, h_store, h_clean⟩ := h_shape.preValue csA dOut h_dval
    refine ⟨fun d => Instr.RStore obseq.TyVal.PTy (Register.R
        (CheckedCompilerM.run (placeToRegChecked kindL B) csA).nextReg) d,
      pOut, h_pval, h_store, h_clean,
      by rw [h_pre]; simp only [emit]
         exact h_shape.chain.placeToRegChecked_placeRegMap kindL csA, ?_⟩
    intro h_code
    -- §3 the chain's own instructions, and the `Borrow` after them
    have h_instS : ∀ q' instr,
        q' < (CheckedCompilerM.run (placeToRegChecked kindL B) csA).nextLabel →
        (CheckedCompilerM.run (placeToRegChecked kindL B) csA).code q'
          = some instr →
        compProg q' = some instr := by
      refine h_code.mono ?_
      rw [h_pre]
      exact StateIncr.trans (freshReg_state_incr _) (emit_state_incr _ _)
    have hFrag := h_code.fragmentOf
      (base := (CheckedCompilerM.run (placeToRegChecked kindL B) csA).nextLabel)
      h_pre rfl
    -- §4 the source package
    obtain ⟨nB, s_mid, sB, tgtPerms, hsB, rfl, h_incr_t, h_wf_t', h_tbd', h_psim',
      h_runB, h_lbsB, h_pcB, h_dprm, h_dregmono, h_memB, -, h_rt_new,
      h_relB, -⟩ :=
      ref_chainsrc_borrow h_shape.chain f kindL kind prot mask compProg
        sM sA csA h_id_a h_wf_t h_tbd h_lbs h_prb h_sms h_psim h_pc h_dres h_fit
        h_ref_src h_dval _ rfl h_instS (hFrag.instrAt 0 rfl rfl)
    refine ⟨_, nB, sB, perms', _, h_incr_t, h_wf_t', rfl,
      by simp [blockSize, obseq.layoutSize], h_runB,
      by grind [emit],
      by rw [h_pre]; grind [emit],
      by rw [h_pre]; exact h_lbsB,
      by rw [hsB]; exact h_psim', by rw [hsB]; exact h_tbd', h_memB,
      by rw [h_pre]; exact h_pcB,
      StoreStep.rstore compProg sB _ obseq.TyVal.PTy _ _
        (by rw [hsB]; exact RegMap.lookup_insert_self _ _ _)
        (by rw [h_pre]; grind [emit]),
      h_relB⟩

/-- A BARE LOCAL source: the chain lowering emits nothing, so the whole
    rvalue is one `Borrow` at offset zero. -/
theorem refSrcShape_local {τ : LayoutTy} (srcLoc : Local Γ τ)
    (kind : RefKind) (prot : Bool) (mask : List Bool) :
    RefSrcShape kind kind prot mask (Place.local srcLoc) PathTo.nil
      (Place.local srcLoc) where
  chain := PtrChain.base srcLoc
  resolve := by intro s r p h; simpa using h
  resolveErr := by intro s e h; exact h
  preRun := by
    intro cs dOut h_dval
    simp only [compileRExprPreChecked, placeToBorrowRegChecked, csMonad, csRun,
      h_dval]
    rfl
  preValue := by
    intro cs dOut h_dval
    simp only [compileRExprPreChecked, placeToBorrowRegChecked, csMonad, csRun,
      h_dval]
    exact ⟨_, rfl, fun _ => rfl, rfl⟩
  movePreRun := by
    intro cs dOut h_dval h_dclean h_kind
    subst h_kind
    simp only [compileRExprPreChecked, placeToBorrowRegChecked, csMonad, csRun,
      h_dval, moveTail, cleanupInstrs]
    rfl
  movePreValue := by
    intro cs dOut h_dval h_kind
    subst h_kind
    simp only [compileRExprPreChecked, placeToBorrowRegChecked, csMonad, csRun,
      h_dval]
    exact ⟨_, rfl, fun _ => rfl, rfl⟩

/-- A BARE DEREF source: the chain is lowered `Shared` (the reborrow's own
    kind applies only to the mint), then one `Borrow` at offset zero.
    The two `do`-block equations are what makes this the only shape
    needing more than a `simp only`: `placeToBorrowRegChecked`'s deref
    arm and `placeToRegChecked`'s share their first three steps, and
    only spelling both out lets the two sides meet. -/
theorem refSrcShape_deref {τ : LayoutTy} (P : Place Γ (obseq.LayoutTy.PtrL τ))
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (h_chain : PtrChain (Place.deref P)) :
    RefSrcShape RefKind.Shared kind prot mask (Place.deref P) PathTo.nil
      (Place.deref P) where
  chain := h_chain
  resolve := by intro s r p h; simpa using h
  resolveErr := by intro s e h; exact h
  preRun := by
    intro cs dOut h_dval
    have h_bindB : placeToBorrowRegChecked (Γ := Γ) kind prot mask (.deref P)
        = (do
            let ptrOut ← placeToRegChecked RefKind.Shared P
            let ptrRes := ptrOut.result
            let loadedReg ← CheckedCompilerM.lift freshRegM
            let _ ← CheckedCompilerM.lift
              (emitM [Instr.Assgn loadedReg (Rhs.Load obseq.TyVal.PTy ptrRes.reg)])
            let _ ← CheckedCompilerM.lift (emitM (cleanupInstrs ptrRes.cleanup))
            let tmpReg ← CheckedCompilerM.lift freshRegM
            let _ ← CheckedCompilerM.lift
              (emitM [Instr.Assgn tmpReg (Rhs.Borrow kind prot mask (some (blockSize τ)) loadedReg 0)])
            pure {
              result := { reg := tmpReg, cleanup := [(tmpReg, blockSize τ)] },
              evidence := PlaceToBorrowRegEvidence.deref P ptrRes loadedReg tmpReg
                ptrOut.evidence
            }) := by simp only [placeToBorrowRegChecked]
    have h_bindD : placeToRegChecked (Γ := Γ) RefKind.Shared (.deref P)
        = (do
            let ptrOut ← placeToRegChecked RefKind.Shared P
            let ptrRes := ptrOut.result
            let loadedReg ← CheckedCompilerM.lift freshRegM
            let _ ← CheckedCompilerM.lift
              (emitM [Instr.Assgn loadedReg (Rhs.Load obseq.TyVal.PTy ptrRes.reg)])
            let _ ← CheckedCompilerM.lift (emitM (cleanupInstrs ptrRes.cleanup))
            pure {
              result := { reg := loadedReg, cleanup := [] },
              evidence := PlaceToRegEvidence.deref P ptrRes loadedReg ptrOut.evidence
            }) := by simp only [placeToRegChecked]
    cases h_x : CheckedCompilerM.value (placeToRegChecked RefKind.Shared P) cs with
    | error e =>
        exfalso
        rw [h_bindD] at h_dval
        simp only [csMonad, h_x] at h_dval
        simp at h_dval
    | ok pOut =>
        rw [h_bindD] at h_dval
        simp only [csMonad, h_x] at h_dval
        simp only [csRun] at h_dval
        cases h_dval
        simp [compileRExprPreChecked, csMonad, csRun, h_bindB, h_bindD, h_x]
        simp [csRun, cleanupInstrs, emit_nil]
        rfl
  preValue := by
    intro cs dOut h_dval
    have h_bindB : placeToBorrowRegChecked (Γ := Γ) kind prot mask (.deref P)
        = (do
            let ptrOut ← placeToRegChecked RefKind.Shared P
            let ptrRes := ptrOut.result
            let loadedReg ← CheckedCompilerM.lift freshRegM
            let _ ← CheckedCompilerM.lift
              (emitM [Instr.Assgn loadedReg (Rhs.Load obseq.TyVal.PTy ptrRes.reg)])
            let _ ← CheckedCompilerM.lift (emitM (cleanupInstrs ptrRes.cleanup))
            let tmpReg ← CheckedCompilerM.lift freshRegM
            let _ ← CheckedCompilerM.lift
              (emitM [Instr.Assgn tmpReg (Rhs.Borrow kind prot mask (some (blockSize τ)) loadedReg 0)])
            pure {
              result := { reg := tmpReg, cleanup := [(tmpReg, blockSize τ)] },
              evidence := PlaceToBorrowRegEvidence.deref P ptrRes loadedReg tmpReg
                ptrOut.evidence
            }) := by simp only [placeToBorrowRegChecked]
    have h_bindD : placeToRegChecked (Γ := Γ) RefKind.Shared (.deref P)
        = (do
            let ptrOut ← placeToRegChecked RefKind.Shared P
            let ptrRes := ptrOut.result
            let loadedReg ← CheckedCompilerM.lift freshRegM
            let _ ← CheckedCompilerM.lift
              (emitM [Instr.Assgn loadedReg (Rhs.Load obseq.TyVal.PTy ptrRes.reg)])
            let _ ← CheckedCompilerM.lift (emitM (cleanupInstrs ptrRes.cleanup))
            pure {
              result := { reg := loadedReg, cleanup := [] },
              evidence := PlaceToRegEvidence.deref P ptrRes loadedReg ptrOut.evidence
            }) := by simp only [placeToRegChecked]
    cases h_x : CheckedCompilerM.value (placeToRegChecked RefKind.Shared P) cs with
    | error e =>
        exfalso
        rw [h_bindD] at h_dval
        simp only [csMonad, h_x] at h_dval
        simp at h_dval
    | ok pOut =>
        simp only [compileRExprPreChecked, csMonad, csRun, h_bindB, h_bindD, h_x]
        exact ⟨_, rfl, fun _ => rfl, rfl⟩
  movePreRun := by
    intro cs dOut h_dval h_dclean h_kind
    subst h_kind
    have h_bindB : placeToBorrowRegChecked (Γ := Γ) RefKind.Mut false [] (.deref P)
        = (do
            let ptrOut ← placeToRegChecked RefKind.Shared P
            let ptrRes := ptrOut.result
            let loadedReg ← CheckedCompilerM.lift freshRegM
            let _ ← CheckedCompilerM.lift
              (emitM [Instr.Assgn loadedReg (Rhs.Load obseq.TyVal.PTy ptrRes.reg)])
            let _ ← CheckedCompilerM.lift (emitM (cleanupInstrs ptrRes.cleanup))
            let tmpReg ← CheckedCompilerM.lift freshRegM
            let _ ← CheckedCompilerM.lift
              (emitM [Instr.Assgn tmpReg (Rhs.Borrow RefKind.Mut false [] (some (blockSize τ)) loadedReg 0)])
            pure {
              result := { reg := tmpReg, cleanup := [(tmpReg, blockSize τ)] },
              evidence := PlaceToBorrowRegEvidence.deref P ptrRes loadedReg tmpReg
                ptrOut.evidence
            }) := by simp only [placeToBorrowRegChecked]
    have h_bindD : placeToRegChecked (Γ := Γ) RefKind.Shared (.deref P)
        = (do
            let ptrOut ← placeToRegChecked RefKind.Shared P
            let ptrRes := ptrOut.result
            let loadedReg ← CheckedCompilerM.lift freshRegM
            let _ ← CheckedCompilerM.lift
              (emitM [Instr.Assgn loadedReg (Rhs.Load obseq.TyVal.PTy ptrRes.reg)])
            let _ ← CheckedCompilerM.lift (emitM (cleanupInstrs ptrRes.cleanup))
            pure {
              result := { reg := loadedReg, cleanup := [] },
              evidence := PlaceToRegEvidence.deref P ptrRes loadedReg ptrOut.evidence
            }) := by simp only [placeToRegChecked]
    cases h_x : CheckedCompilerM.value (placeToRegChecked RefKind.Shared P) cs with
    | error e =>
        exfalso
        rw [h_bindD] at h_dval
        simp only [csMonad, h_x] at h_dval
        simp at h_dval
    | ok pOut =>
        rw [h_bindD] at h_dval
        simp only [csMonad, h_x] at h_dval
        simp only [csRun] at h_dval
        cases h_dval
        simp [compileRExprPreChecked, csMonad, csRun, h_bindB, h_bindD, h_x]
        simp [csRun, cleanupInstrs, emit_nil, moveTail]
        rfl
  movePreValue := by
    intro cs dOut h_dval h_kind
    subst h_kind
    have h_bindB : placeToBorrowRegChecked (Γ := Γ) RefKind.Mut false [] (.deref P)
        = (do
            let ptrOut ← placeToRegChecked RefKind.Shared P
            let ptrRes := ptrOut.result
            let loadedReg ← CheckedCompilerM.lift freshRegM
            let _ ← CheckedCompilerM.lift
              (emitM [Instr.Assgn loadedReg (Rhs.Load obseq.TyVal.PTy ptrRes.reg)])
            let _ ← CheckedCompilerM.lift (emitM (cleanupInstrs ptrRes.cleanup))
            let tmpReg ← CheckedCompilerM.lift freshRegM
            let _ ← CheckedCompilerM.lift
              (emitM [Instr.Assgn tmpReg (Rhs.Borrow RefKind.Mut false [] (some (blockSize τ)) loadedReg 0)])
            pure {
              result := { reg := tmpReg, cleanup := [(tmpReg, blockSize τ)] },
              evidence := PlaceToBorrowRegEvidence.deref P ptrRes loadedReg tmpReg
                ptrOut.evidence
            }) := by simp only [placeToBorrowRegChecked]
    have h_bindD : placeToRegChecked (Γ := Γ) RefKind.Shared (.deref P)
        = (do
            let ptrOut ← placeToRegChecked RefKind.Shared P
            let ptrRes := ptrOut.result
            let loadedReg ← CheckedCompilerM.lift freshRegM
            let _ ← CheckedCompilerM.lift
              (emitM [Instr.Assgn loadedReg (Rhs.Load obseq.TyVal.PTy ptrRes.reg)])
            let _ ← CheckedCompilerM.lift (emitM (cleanupInstrs ptrRes.cleanup))
            pure {
              result := { reg := loadedReg, cleanup := [] },
              evidence := PlaceToRegEvidence.deref P ptrRes loadedReg ptrOut.evidence
            }) := by simp only [placeToRegChecked]
    cases h_x : CheckedCompilerM.value (placeToRegChecked RefKind.Shared P) cs with
    | error e =>
        exfalso
        rw [h_bindD] at h_dval
        simp only [csMonad, h_x] at h_dval
        simp at h_dval
    | ok pOut =>
        simp only [compileRExprPreChecked, csMonad, csRun, h_bindB, h_bindD, h_x]
        exact ⟨_, rfl, fun _ => rfl, rfl⟩

/-- A PROJECTED source over any chain: the chain is lowered at the
    retag's own kind, then one `Borrow` at the path's offset. The chain
    is never proj-topped, which is what rules out
    `placeToBorrowRegChecked`'s reassociation arm — hence the case
    split, which is the only reason this is three lines rather than one. -/
theorem refSrcShape_proj {σb τ : LayoutTy} {B : Place Γ σb} (f : PathTo σb τ)
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (h_chain : PtrChain B) :
    RefSrcShape kind kind prot mask B f (Place.proj B f) where
  chain := h_chain
  resolve := fun _ _ _ h => resolvePlaceAcc_proj_base_ok h
  resolveErr := fun _ _ h => resolvePlaceAcc_proj_base_err h
  preRun := by
    intro cs dOut h_dval
    cases h_chain with
    | base loc =>
        simp only [compileRExprPreChecked, placeToBorrowRegChecked, csMonad,
          csRun, h_dval]
    | deref hp =>
        simp only [compileRExprPreChecked, placeToBorrowRegChecked, csMonad,
          csRun, h_dval]
    | derefProj g hb =>
        simp only [compileRExprPreChecked, placeToBorrowRegChecked, csMonad,
          csRun, h_dval]
  preValue := by
    intro cs dOut h_dval
    cases h_chain with
    | base loc =>
        simp only [compileRExprPreChecked, placeToBorrowRegChecked, csMonad,
          csRun, h_dval]
        exact ⟨_, rfl, fun _ => rfl, rfl⟩
    | deref hp =>
        simp only [compileRExprPreChecked, placeToBorrowRegChecked, csMonad,
          csRun, h_dval]
        exact ⟨_, rfl, fun _ => rfl, rfl⟩
    | derefProj g hb =>
        simp only [compileRExprPreChecked, placeToBorrowRegChecked, csMonad,
          csRun, h_dval]
        exact ⟨_, rfl, fun _ => rfl, rfl⟩
  movePreRun := by
    intro cs dOut h_dval h_dclean h_kind
    subst h_kind
    cases h_chain with
    | base loc =>
        simp only [compileRExprPreChecked, placeToBorrowRegChecked, csMonad,
          csRun, h_dval, h_dclean, moveTail, cleanupInstrs]
        rfl
    | deref hp =>
        simp only [compileRExprPreChecked, placeToBorrowRegChecked, csMonad,
          csRun, h_dval, h_dclean, moveTail, cleanupInstrs]
        rfl
    | derefProj g hb =>
        simp only [compileRExprPreChecked, placeToBorrowRegChecked, csMonad,
          csRun, h_dval, h_dclean, moveTail, cleanupInstrs]
        rfl
  movePreValue := by
    intro cs dOut h_dval h_kind
    subst h_kind
    cases h_chain with
    | base loc =>
        simp only [compileRExprPreChecked, placeToBorrowRegChecked, csMonad,
          csRun, h_dval]
        exact ⟨_, rfl, fun _ => rfl, rfl⟩
    | deref hp =>
        simp only [compileRExprPreChecked, placeToBorrowRegChecked, csMonad,
          csRun, h_dval]
        exact ⟨_, rfl, fun _ => rfl, rfl⟩
    | derefProj g hb =>
        simp only [compileRExprPreChecked, placeToBorrowRegChecked, csMonad,
          csRun, h_dval]
        exact ⟨_, rfl, fun _ => rfl, rfl⟩


/-- Every FLATTENED ref source is a value package. A flattened source is
    either a pointer chain or one projection over a chain
    (`flatten_chainish`); a chain lowers `Shared` when it is a deref and
    at the retag's kind when it is a bare local, which is the only thing
    the three cases here decide. -/
theorem ref_valuePkg_of_chain {τ : LayoutTy} {B : Place Γ τ}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (compProg : oseair.Prog) (h_chain : PtrChain B) :
    ValuePkg compProg (RExpr.ref kind prot mask B) := by
  cases h_chain with
  | base loc =>
      exact ref_valuePkg_chain compProg (refSrcShape_local loc kind prot mask)
  | deref h =>
      exact ref_valuePkg_chain compProg
        (refSrcShape_deref _ kind prot mask (PtrChain.deref h))
  | derefProj f h =>
      exact ref_valuePkg_chain compProg
        (refSrcShape_deref _ kind prot mask (PtrChain.derefProj f h))

/-- …and one projection over a chain is the projected shape. -/
theorem ref_valuePkg_of_projchain {σb τ : LayoutTy} {B : Place Γ σb}
    (f : PathTo σb τ) (kind : RefKind) (prot : Bool) (mask : List Bool)
    (compProg : oseair.Prog) (h_chain : PtrChain B) :
    ValuePkg compProg (RExpr.ref kind prot mask (Place.proj B f)) :=
  ref_valuePkg_chain compProg (refSrcShape_proj f kind prot mask h_chain)

/-! ## Flatten transfer for the ref deref-src shape (through the
    borrow-deref arm: both sides share their prefix, aligned by the
    INNER agree at `Shared P`). -/









/-! ## Projected destination with a PROJ-TOPPED source over a bound
    local. As everywhere in ref, the source projection costs only the
    `Borrow`'s offset operand, so these are the local-source fragments
    with `pathOffset f` in place of `0`. -/

/-! ## A CHAIN source under a PROJECTED destination over a bound local.
    The destination has no spine — at zero offset its lowering is the
    root register itself — so only the SOURCE needs the mother lemma.
    The plain deref source `&kind *p` is the `pathOffset f = 0` case of
    the same fragment. -/

/-! ## A CHAIN source under a PROJECTED destination at NONZERO offset:
    the spine, the source `Borrow`, then the projection's own interior
    `Borrow(Mut)` and its cleanup `Die` — BRIDGE 1 on the destination. -/

/-! ## The deref-dst fragments (MIR order: Borrow first, then the dst)

`*P := &src` lowers, under the d34 MIR order, to the rhs `Borrow`
FIRST, then the WHOLE dst lowering (owned opaquely by
`ptrChain_lowering_sim`), then the `RStore` of the borrow through the
loaded register. The borrow temp `R cs.nextReg` crosses the dst
lowering via the mother lemma's register-frame conjunct. -/




/-! ## Flatten transfer for the ref deref-dst shape -/

/-! ## The DESTINATION-flattening transfer for a projection over a
    deref base, the shape the last residual leaf consumes. -/




/-! ## A PROJ-TOPPED source over a DEREF base, into a bound local:
    `dst := &kind (*p).f`. `placeToRegChecked`'s deref arm ignores its
    `kind` (it lowers the pointer place at `Shared` and `Load`s), so the
    base lowering is the same chain code the plain deref source emits —
    only the `Borrow`'s offset operand differs, which is why the mother
    lemma can be invoked at `kind` and consumed unchanged. -/

/-! ## A PROJ-TOPPED source over a DEREF base, into a FRESH local. -/

/-! ## Source flattening for ref

    `placeToBorrowRegChecked` carries its own reassociating arm for
    nested projection borrows, so the compiled statement cannot tell a
    ref source from its flattening apart
    (`placeToBorrowRegChecked_flatten_agree`), and neither can mirlite
    (`stepStmt_assign_refsrc_anyflatten`). That turns a proj-of-proj
    source into a single projection over the flattened base — which,
    when that base is a local, is exactly the shape the closed leaves
    take.

    The statement-level transfers all factor through one CONGRUENCE:
    two sources whose borrow lowerings agree (run, and value's result
    component) compile the enclosing statement identically. Stating it
    that way avoids rewriting a `Place` underneath `compileStmtChecked`,
    whose result TYPE mentions the statement — such a rewrite is not
    type-correct. -/

/-! ## Deref destination with a PROJ-TOPPED source over a bound local.
    `placeToBorrowRegChecked`'s proj arm differs from its local arm only
    in the borrow's OFFSET, so the fragment is the deref-dst pair with
    `pathOffset f` in place of `0`. -/



/-! ## A PROJECTED destination over a DEREF base: `(*p).g := &kind _`.

    The destination root is a chain, so BOTH places need
    `ptrChain_lowering_sim` — the destination-spine mirror of the
    two-mother leaf. The source is left GENERIC: any base that is a
    `PtrChain` and is not itself a projection works, which after
    flattening covers every source shape. `h_unfold` is the
    `placeToBorrowRegChecked` equation for that base, supplied by
    `simp only [placeToBorrowRegChecked]` at each call site. -/

/-! ## The same at NONZERO destination offset: the projection mints its
    own interior `Borrow(Mut)` over the destination chain's register and
    dies after the store, so BRIDGE 1 must collapse the triple. -/



/-! ## TWO MOTHERS: a proj-topped DEREF source under a DEREF
    destination, `*D := &kind (*P).f`. The source chain lowers first
    (mother at `kind`, whose deref arm ignores it), then one `Borrow` at
    the projection's offset, then the destination chain (mother at
    `Mut`) whose register-frame conjunct carries the borrow temp across,
    then one `RStore`. Both lowerings leave an empty cleanup, so no
    `Die` is emitted and BRIDGE 1 is not needed. -/






/-! ## Fresh projected destination with a PROJ-TOPPED source. -/

/-! ## The destination root as its own source: `t.g := &kind t.f`
    with `t` FRESH. The source register is the root register the
    `Alloc` just produced, so the source's placeInfo is
    `getPlaceInfo_setPlaceInfo_self` rather than a survival argument. -/

/-! ## A CHAIN source under a FRESH projected destination, offset zero. -/

/-! ## A CHAIN source under a FRESH projected destination at NONZERO
    offset: the σ-sized root `Alloc`, the spine, the source `Borrow`,
    then BRIDGE 1's `Borrow(Mut)`/`RStore`/`Die` on the destination. -/




/-- The ref pre-phase sees its source only through the borrow lowering,
    which agrees under flattening. -/
theorem compileRExprPreChecked_ref_flatten {τ : LayoutTy}
    (kind : RefKind) (prot : Bool) (mask : List Bool) (src : Place Γ τ)
    (cs : CompilerState) :
    CheckedCompilerM.run (compileRExprPreChecked (RExpr.ref kind prot mask (flattenPlace src))) cs
      = CheckedCompilerM.run (compileRExprPreChecked (RExpr.ref kind prot mask src)) cs ∧
    (CheckedCompilerM.value (compileRExprPreChecked (RExpr.ref kind prot mask (flattenPlace src))) cs).map
        (fun p => (p.store, p.postCleanup))
      = (CheckedCompilerM.value (compileRExprPreChecked (RExpr.ref kind prot mask src)) cs).map
        (fun p => (p.store, p.postCleanup)) := by
  obtain ⟨h_agr, h_agv⟩ := placeToBorrowRegChecked_flatten_agree kind prot mask src cs
  simp only [compileRExprPreChecked, csMonad]
  rcases exceptMap_agree h_agv with ⟨e1, e2, h1, h2⟩ | ⟨o1, o2, h1, h2, h_res⟩
  · have h_e : e1 = e2 := by
      rw [h1, h2] at h_agv
      simpa [Except.map] using h_agv
    subst h_e
    simp only [h1, h2]
    exact ⟨h_agr, rfl⟩
  · constructor
    · simp only [h1, h2, h_res, h_agr]
    · simp only [h1, h2, h_res, Except.map]

/-- The per-statement simulation for `dst := &kind src`. Since
    2026-09-13 the source contributes ONLY a value package: flatten it
    once, read off which of the two package constructors applies, and
    hand it to the destination leaf. So this dispatcher is a case split
    on the DESTINATION alone, and every arm is three lines. -/
theorem assignStep_ref
    {τ : LayoutTy}
    {dst : Place Γ (obseq.LayoutTy.PtrL τ)}
    {src : Place Γ τ}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (compProg : oseair.Prog)
    {csStart : CompilerState}
    (h_invAt : InvAt ρa ρt s_mir s_osea csStart)
    (hF : (∃ so, CheckedCompilerM.value
        (compileStmtChecked (.assign dst (.ref kind prot mask src))) csStart = Except.ok so) →
      StmtFrame compProg cs0 prog s_mir.pc
        (CheckedCompilerM.run (compileStmtChecked (.assign dst (.ref kind prot mask src))) csStart))
    (h_step : mirlite.stepStmt MSB s_mir (.assign dst (.ref kind prot mask src)) = .ok s_mir') :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' := by
  -- the source, normalised once and for all
  rw [stepStmt_assign_refsrc_anyflatten] at h_step
  have h_pkg : ValuePkg compProg (RExpr.ref kind prot mask (flattenPlace src)) := by
    rcases flatten_chainish src with h_ch | ⟨σ', sb, sp, h_eq, h_sb⟩
    · exact ref_valuePkg_of_chain kind prot mask compProg h_ch
    · rw [h_eq]
      exact ref_valuePkg_of_projchain sp kind prot mask compProg h_sb
  obtain ⟨h_crun, h_cval⟩ := compileAssignChecked_congr_pre dst
    (.ref kind prot mask src) (.ref kind prot mask (flattenPlace src))
    (fun cs => (compileRExprPreChecked_ref_flatten kind prot mask src cs).1.symm)
    (fun cs => (compileRExprPreChecked_ref_flatten kind prot mask src cs).2.symm)
  cases dst with
  | «local» dstLoc =>
      cases h_envD : mirlite.Env.lookup s_mir.env dstLoc with
      | some bD =>
          obtain ⟨ρt', s_osea', n, h_incr, h_run, h_inv'⟩ :=
            storereg_local_simulation compProg h_pkg h_invAt
              (StmtFrame.congr hF h_crun h_cval) h_envD h_step
          exact ⟨ρa, ρt', s_osea', n, AddrRenameIncr.refl ρa, h_incr, h_run, h_inv'⟩
      | none =>
          exact storereg_localfresh_simulation compProg h_pkg h_invAt
            (StmtFrame.congr hF h_crun h_cval) h_envD h_step
  | proj dbase g =>
      exact storereg_projdst_recursion compProg h_pkg h_invAt
        (StmtFrame.congr hF h_crun h_cval) h_step
  | deref P =>
      rw [stepStmt_assign_dstderef_flatten] at h_step
      obtain ⟨ρt', s_osea', n, h_incr, h_run, h_inv'⟩ :=
        storereg_chaindst_simulation (P := flattenPlace P) compProg h_pkg
          (PtrChain_flatten_deref P) h_invAt (StmtFrame.congr hF
          (fun cs => (h_crun cs).trans (compileStmt_assign_derefdst_flatten_run _ cs))
          (fun cs so h => by
            obtain ⟨so1, h1⟩ := compileStmt_assign_derefdst_flatten_value _ cs so h
            exact h_cval cs so1 h1))
          h_step
      exact ⟨ρa, ρt', s_osea', n, AddrRenameIncr.refl ρa, h_incr, h_run, h_inv'⟩

theorem CompilerInv_step_ref
    {τ : LayoutTy}
    {dst : Place Γ (obseq.LayoutTy.PtrL τ)}
    {src : Place Γ τ}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (compProg : oseair.Prog)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    (h_stmt : prog.get? s_mir.pc = some (.assign dst (.ref kind prot mask src)))
    (h_step : mirlite.stepStmt MSB s_mir (.assign dst (.ref kind prot mask src)) = .ok s_mir') :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' := by
  obtain ⟨csPrefix, h_csAt, h_invAt⟩ := h_inv.invAt
  exact assignStep_ref kind prot mask compProg h_invAt
    (StmtFrame.ofAssign h_comp h_csAt h_stmt (fun _ => rfl) (fun _ so h => ⟨so, h⟩))
    h_step


/-! ## `move` as a value package (2026-09-20)

`dst := move src` is copy's value with the source's borrow stacks
CLEARED and its bytes left alone: mirlite mints a temporary unique
reborrow of the source (the retag pops every item above the source's
own), reads through it, and retires it; the compiled code is the same
three events, `Borrow(Mut); Load; Die`, after the source chain's
lowering. So the package is the ref mother lemma (`ref_chainsrc_borrow`)
for the mint, the read transport for the `Load`, and the die transport
for the `Die` — no memory event on either side, which is what keeps it
inside the value-package contract every destination leaf already
takes. -/

theorem move_valuePkg_chain
    {σb τ : LayoutTy} {B : Place Γ σb} {f : PathTo σb τ}
    {src : Place Γ τ} {kindL : RefKind}
    (compProg : oseair.Prog)
    (h_shape : RefSrcShape kindL RefKind.Mut false [] B f src) :
    ValuePkg compProg (RExpr.move src) := by
  intro ρa ρt sM sA csA h_id_a h_wf_t h_tbd h_lbs h_prb h_sms h_alloc h_psim h_pc
    output h_eval
  -- §1 invert the move: resolve, fit, mint, read, retire
  simp only [mirlite.evalRExpr] at h_eval
  cases h_dres : mirlite.resolvePlaceAcc MSB sM B with
  | error e =>
      rw [h_shape.resolveErr _ _ h_dres] at h_eval; simp at h_eval
  | ok pr =>
  obtain ⟨resolved, permsR⟩ := pr
  rw [h_shape.resolve _ _ _ h_dres] at h_eval
  simp only at h_eval
  by_cases h_fit : resolved.addr + PathTo.offset f + blockSize τ
      > resolved.allocBase + resolved.allocSize
  · rw [if_pos h_fit] at h_eval; simp at h_eval
  · rw [if_neg h_fit] at h_eval
    cases h_ref_src : MSB.ref permsR (resolved.addr + PathTo.offset f)
        (blockSize τ) resolved.tag RefKind.Mut false [] with
    | error e => rw [h_ref_src] at h_eval; simp at h_eval
    | ok pr2 =>
    obtain ⟨permsM, tmpTag⟩ := pr2
    rw [h_ref_src] at h_eval
    simp only at h_eval
    cases h_read_src : MSB.read permsM (resolved.addr + PathTo.offset f)
        (blockSize τ) tmpTag with
    | error e => rw [h_read_src] at h_eval; simp at h_eval
    | ok permsRd =>
    rw [h_read_src] at h_eval
    simp only at h_eval
    cases h_die_src : MSB.die permsRd (resolved.addr + PathTo.offset f)
        (blockSize τ) tmpTag with
    | error e => rw [h_die_src] at h_eval; simp at h_eval
    | ok perms' =>
    rw [h_die_src] at h_eval
    simp only at h_eval
    split at h_eval
    · simp at h_eval
    rename_i h_init0
    have h_init : (mirlite.readWordSeq sM.mem (resolved.addr + PathTo.offset f) (blockSize τ)).any
        (fun v => v == mirlite.MemValue.undef) = false := by simpa using h_init0
    injection h_eval with h_out
    subst h_out
    -- §2 the compiled shape
    have h_mapped : PlaceInputsMapped csA B :=
      placeInputsMapped_of_localBindingSim_resolvePlace h_lbs
        (resolvePlace?_of_resolveAcc h_dres)
    obtain ⟨dOut, h_dval⟩ := placeToRegChecked_ok_of_placeInputsMapped
      (cs := csA) (kind := kindL) h_mapped
    have h_dclean := h_shape.chain.placeToRegChecked_cleanup_nil kindL csA h_dval
    have h_pre := h_shape.movePreRun csA dOut h_dval h_dclean rfl
    obtain ⟨pOut, h_pval, h_store, h_clean⟩ := h_shape.movePreValue csA dOut h_dval rfl
    have h_sz : obseq.typeSize (layoutToTyVal τ) = blockSize τ :=
      obseq.typeSize_layoutToTyVal _
    have h_prmTail : (moveTail (CheckedCompilerM.run (placeToRegChecked kindL B) csA)
        dOut.result.reg (pathOffset f) (blockSize τ) (layoutToTyVal τ)).placeRegMap
        = csA.placeRegMap := by
      simp only [moveTail, emit]
      exact h_shape.chain.placeToRegChecked_placeRegMap kindL csA
    refine ⟨fun d => Instr.RStore (layoutToTyVal τ) (Register.R
        ((CheckedCompilerM.run (placeToRegChecked kindL B) csA).nextReg + 1)) d,
      pOut, h_pval, h_store, h_clean,
      (congrArg CompilerState.placeRegMap h_pre).trans h_prmTail, ?_⟩
    intro h_code
    rw [h_pre] at h_code
    -- §3 code positions: the chain, then the three instructions
    have h_incrTail : StateIncr (CheckedCompilerM.run (placeToRegChecked kindL B) csA)
        (moveTail (CheckedCompilerM.run (placeToRegChecked kindL B) csA)
          dOut.result.reg (pathOffset f) (blockSize τ) (layoutToTyVal τ)) := by
      simp only [moveTail]
      exact ((freshReg_state_incr _).trans (emit_state_incr _ _)).trans
        ((freshReg_state_incr _).trans (emit_state_incr _ _))
    have h_instS : ∀ q' instr,
        q' < (CheckedCompilerM.run (placeToRegChecked kindL B) csA).nextLabel →
        (CheckedCompilerM.run (placeToRegChecked kindL B) csA).code q'
          = some instr →
        compProg q' = some instr := h_code.mono h_incrTail
    have hFrag := h_code.fragmentOf
      (base := (CheckedCompilerM.run (placeToRegChecked kindL B) csA).nextLabel)
      (show moveTail (CheckedCompilerM.run (placeToRegChecked kindL B) csA)
          dOut.result.reg (pathOffset f) (blockSize τ) (layoutToTyVal τ)
        = emit { (emit { (CheckedCompilerM.run (placeToRegChecked kindL B) csA) with
              nextReg := (CheckedCompilerM.run (placeToRegChecked kindL B) csA).nextReg + 1 }
            [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked kindL B) csA).nextReg)
              (Rhs.Borrow RefKind.Mut false [] (some (blockSize τ)) dOut.result.reg (pathOffset f))])
            with nextReg := (CheckedCompilerM.run (placeToRegChecked kindL B) csA).nextReg + 1 + 1 }
          [Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked kindL B) csA).nextReg + 1))
            (Rhs.Load (layoutToTyVal τ) (Register.R (CheckedCompilerM.run (placeToRegChecked kindL B) csA).nextReg)),
           Instr.Die (Register.R (CheckedCompilerM.run (placeToRegChecked kindL B) csA).nextReg) (blockSize τ)]
        from rfl) rfl
    -- §4 the mint, through the ref mother lemma
    obtain ⟨nB, s_mid, sB, tgtPerms, hsB, h_fresh, h_incr_t, h_wf_t', h_tbd', h_psim',
      h_runB, h_lbsB, h_pcB, h_dprm, h_dregmono, h_memB, -, h_rt_new, -, h_dle⟩ :=
      ref_chainsrc_borrow h_shape.chain f kindL RefKind.Mut false [] compProg
        sM sA csA h_id_a h_wf_t h_tbd h_lbs h_prb h_sms h_psim h_pc h_dres h_fit
        h_ref_src h_dval _ rfl h_instS (hFrag.instrAt 0 rfl rfl)
    subst h_fresh
    have h_addr : resolved.allocBase + (resolved.addr - resolved.allocBase + pathOffset f)
        = resolved.addr + PathTo.offset f := by
      rw [← Nat.add_assoc, resolvedAddr_cancel h_dle]
    have h_pcB' : sB.pc = (CheckedCompilerM.run (placeToRegChecked kindL B) csA).nextLabel + 1 := by
      rw [h_pcB]; simp [emit]
    -- §5 the read through the temporary
    obtain ⟨p2, h_read_tgt, h_psimRd⟩ :=
      sb_read_respects_PermSim h_psim' h_wf_t' h_rt_new h_read_src
    have h_entryB : PtrRegisterEntry sB.reg
        (Register.R (CheckedCompilerM.run (placeToRegChecked kindL B) csA).nextReg)
        resolved.allocBase (resolved.addr - resolved.allocBase + pathOffset f)
        resolved.allocSize s_mid.perms.NextTag := by
      rw [hsB]; exact RegMap.lookup_insert_self _ _ _
    have h_lt : resolved.addr - resolved.allocBase + pathOffset f
        + obseq.typeSize (layoutToTyVal τ) ≤ resolved.allocSize := by
      rw [h_sz]
      have h1 : resolved.addr + PathTo.offset f + blockSize τ
          ≤ resolved.allocBase + resolved.allocSize := Nat.not_lt.mp h_fit
      have h_eq : resolved.allocBase
          + (resolved.addr - resolved.allocBase + pathOffset f + blockSize τ)
          = resolved.addr + PathTo.offset f + blockSize τ := by
        rw [← Nat.add_assoc, ← Nat.add_assoc, resolvedAddr_cancel h_dle]
      exact Nat.le_of_add_le_add_left (by rw [h_eq]; exact h1)
    have h_read' : MSB.read sB.perms
        (resolved.allocBase + (resolved.addr - resolved.allocBase + pathOffset f))
        (obseq.typeSize (layoutToTyVal τ)) s_mid.perms.NextTag = .ok p2 := by
      rw [h_addr, h_sz, hsB]; exact h_read_tgt
    have h_runL := runN_Assgn_Load_ptr_step compProg sB
      (Register.R ((CheckedCompilerM.run (placeToRegChecked kindL B) csA).nextReg + 1))
      (Register.R (CheckedCompilerM.run (placeToRegChecked kindL B) csA).nextReg)
      (layoutToTyVal τ) (by rw [h_pcB']; exact hFrag.instrAt 1 rfl rfl) h_entryB h_lt h_read'
      (by rw [h_addr, h_sz, h_memB]
          exact noUndef_transport (readWordSeq_sim h_id_a h_sms _ _) h_init)
    -- §6 the retirement
    obtain ⟨p3, h_die_tgt, h_psimD, h_ntS, h_ntT⟩ :=
      sb_die_respects_PermSim h_psimRd h_wf_t' h_rt_new h_die_src
    have h_ne : Register.R (CheckedCompilerM.run (placeToRegChecked kindL B) csA).nextReg
        ≠ Register.R ((CheckedCompilerM.run (placeToRegChecked kindL B) csA).nextReg + 1) := by
      simp
    have h_entryL : PtrRegisterEntry
        (oseair.RegMap.insert sB.reg
          (Register.R ((CheckedCompilerM.run (placeToRegChecked kindL B) csA).nextReg + 1))
          (layoutToTyVal τ, oseair.readWordSeq sB.mem
            (resolved.allocBase + (resolved.addr - resolved.allocBase + pathOffset f))
            (obseq.typeSize (layoutToTyVal τ))))
        (Register.R (CheckedCompilerM.run (placeToRegChecked kindL B) csA).nextReg)
        resolved.allocBase (resolved.addr - resolved.allocBase + pathOffset f)
        resolved.allocSize s_mid.perms.NextTag := by
      show oseair.RegMap.lookup (oseair.RegMap.insert _ _ _) _ = _
      rw [RegMap.lookup_insert_ne _ h_ne]
      exact h_entryB
    have h_die' : MSB.die p2
        (resolved.allocBase + (resolved.addr - resolved.allocBase + pathOffset f))
        (blockSize τ) s_mid.perms.NextTag = .ok p3 := by
      rw [h_addr]; exact h_die_tgt
    have h_runD := runN_Die_step compProg
      { sB with perms := p2,
                reg := oseair.RegMap.insert sB.reg
                  (Register.R ((CheckedCompilerM.run (placeToRegChecked kindL B) csA).nextReg + 1))
                  (layoutToTyVal τ, oseair.readWordSeq sB.mem
                    (resolved.allocBase + (resolved.addr - resolved.allocBase + pathOffset f))
                    (obseq.typeSize (layoutToTyVal τ))),
                pc := sB.pc + 1 }
      (Register.R (CheckedCompilerM.run (placeToRegChecked kindL B) csA).nextReg) (blockSize τ)
      (by show compProg (sB.pc + 1) = _; rw [h_pcB']; exact hFrag.instrAt 2 rfl rfl)
      h_entryL h_die'
    -- §7 the package
    have h_prb1 : PlaceRegMapBound
        (emit { (CheckedCompilerM.run (placeToRegChecked kindL B) csA) with
            nextReg := (CheckedCompilerM.run (placeToRegChecked kindL B) csA).nextReg + 1 }
          [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked kindL B) csA).nextReg)
            (Rhs.Borrow RefKind.Mut false [] (some (blockSize τ)) dOut.result.reg (pathOffset f))]) := by
      intro idx reg τ' h_look
      have h_look' : getPlaceInfo csA idx = some (reg, τ') := by
        rw [getPlaceInfo_emit] at h_look
        show csA.placeRegMap.lookup _ = _
        rw [← h_dprm]; exact h_look
      exact RegisterBelow.mono (by simp only [emit]; omega) (h_prb idx reg τ' h_look')
    have h_lbsL : LocalBindingSim ρa (ρt.extend permsR.NextTag s_mid.perms.NextTag) sM.env
        { sB with perms := p2,
                  reg := oseair.RegMap.insert sB.reg
                    (Register.R ((CheckedCompilerM.run (placeToRegChecked kindL B) csA).nextReg + 1))
                    (layoutToTyVal τ, oseair.readWordSeq sB.mem
                      (resolved.allocBase + (resolved.addr - resolved.allocBase + pathOffset f))
                      (obseq.typeSize (layoutToTyVal τ))),
                  pc := sB.pc + 1 }
        (emit { (CheckedCompilerM.run (placeToRegChecked kindL B) csA) with
            nextReg := (CheckedCompilerM.run (placeToRegChecked kindL B) csA).nextReg + 1 }
          [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked kindL B) csA).nextReg)
            (Rhs.Borrow RefKind.Mut false [] (some (blockSize τ)) dOut.result.reg (pathOffset f))]) :=
      LocalBindingSim.insert_fresh_reg h_lbsB h_prb1 (by simp only [emit]; exact Nat.le_refl _) rfl
    refine ⟨_, nB + 1 + 1, _, perms',
      oseair.readWordSeq sB.mem
        (resolved.allocBase + (resolved.addr - resolved.allocBase + pathOffset f))
        (obseq.typeSize (layoutToTyVal τ)),
      h_incr_t, h_wf_t', rfl,
      by rw [oseair_readWordSeq_length, h_sz],
      oseair_runN_trans (oseair_runN_trans h_runB h_runL) h_runD,
      by rw [h_pre]; exact h_prmTail,
      by rw [h_pre]; simp only [moveTail, emit]; omega,
      ?_, h_psimD, ?_, h_memB, ?_, ?_, ?_⟩
    · rw [h_pre]
      exact LocalBindingSim.placeRegMap_congr (by simp only [moveTail, emit]) h_lbsL
    · show TagRenameBounded _ perms'.NextTag p3.NextTag
      rw [h_ntS, h_ntT, sb_read_NextTag h_read_src, sb_read_NextTag h_read_tgt]
      exact h_tbd'
    · show sB.pc + 1 + 1 = _
      rw [h_pre, h_pcB']
      simp only [moveTail, emit, List.length_cons, List.length_nil]
      try omega
    · rw [h_pre]
      refine StoreStep.rstore compProg _ _ (layoutToTyVal τ) _ _ ?_ ?_
      · show oseair.RegMap.lookup (oseair.RegMap.insert _ _ _) _ = _
        exact RegMap.lookup_insert_self _ _ _
      · show _ < (moveTail _ _ _ _ _).nextReg
        simp only [moveTail, emit]
        omega
    · show ListRel (MemValSim ρa _)
        (mirlite.readWordSeq sM.mem (resolved.addr + PathTo.offset f) (blockSize τ)) _
      rw [h_addr, h_sz, h_memB]
      exact readWordSeq_sim h_id_a
        (SourceMemSim.rename_mono (AddrRenameIncr.refl ρa) h_incr_t h_sms) _ _

/-- Every FLATTENED move source is a value package (the ref shapes, at
    `Mut`, unprotected, unmasked). -/
theorem move_valuePkg_of_chain {τ : LayoutTy} {B : Place Γ τ}
    (compProg : oseair.Prog) (h_chain : PtrChain B) :
    ValuePkg compProg (RExpr.move B) := by
  cases h_chain with
  | base loc =>
      exact move_valuePkg_chain compProg (refSrcShape_local loc RefKind.Mut false [])
  | deref h =>
      exact move_valuePkg_chain compProg
        (refSrcShape_deref _ RefKind.Mut false [] (PtrChain.deref h))
  | derefProj f h =>
      exact move_valuePkg_chain compProg
        (refSrcShape_deref _ RefKind.Mut false [] (PtrChain.derefProj f h))

theorem move_valuePkg_of_projchain {σb τ : LayoutTy} {B : Place Γ σb}
    (f : PathTo σb τ) (compProg : oseair.Prog) (h_chain : PtrChain B) :
    ValuePkg compProg (RExpr.move (Place.proj B f)) :=
  move_valuePkg_chain compProg (refSrcShape_proj f RefKind.Mut false [] h_chain)

/-! ## Flatten transfer, and the assign step -/

/-- Flattening the source does not change the move step. -/
theorem stepStmt_assign_movesrc_anyflatten
    {Γ : Ctx} {τ : LayoutTy} {M : PermissionModel}
    (s : mirlite.State M Γ) (dst : Place Γ τ) (src : Place Γ τ) :
    mirlite.stepStmt M s (.assign dst (.move src))
      = mirlite.stepStmt M s (.assign dst (.move (flattenPlace src))) := by
  have h1 : ∀ st : mirlite.State M Γ,
      mirlite.resolvePlaceAcc M st (flattenPlace src)
        = mirlite.resolvePlaceAcc M st src :=
    fun st => resolvePlaceAcc_flatten src
  show mirlite.doAssign M s dst _ = mirlite.doAssign M s dst _
  simp only [mirlite.doAssign, mirlite.evalRExpr, h1]

/-- The move pre-phase sees its source only through the borrow lowering,
    which agrees under flattening. -/
theorem compileRExprPreChecked_move_flatten {τ : LayoutTy} (src : Place Γ τ)
    (cs : CompilerState) :
    CheckedCompilerM.run (compileRExprPreChecked (RExpr.move (flattenPlace src))) cs
      = CheckedCompilerM.run (compileRExprPreChecked (RExpr.move src)) cs ∧
    (CheckedCompilerM.value (compileRExprPreChecked (RExpr.move (flattenPlace src))) cs).map
        (fun p => (p.store, p.postCleanup))
      = (CheckedCompilerM.value (compileRExprPreChecked (RExpr.move src)) cs).map
        (fun p => (p.store, p.postCleanup)) := by
  obtain ⟨h_agr, h_agv⟩ := placeToBorrowRegChecked_flatten_agree RefKind.Mut false [] src cs
  simp only [compileRExprPreChecked, csMonad]
  rcases exceptMap_agree h_agv with ⟨e1, e2, h1, h2⟩ | ⟨o1, o2, h1, h2, h_res⟩
  · have h_e : e1 = e2 := by
      rw [h1, h2] at h_agv
      simpa [Except.map] using h_agv
    subst h_e
    simp only [h1, h2]
    exact ⟨h_agr, rfl⟩
  · constructor
    · simp only [h1, h2, h_res, h_agr]
    · simp only [h1, h2, h_res, h_agr, csRun, Except.map]

theorem assignStep_move
    {τ : LayoutTy} {dst : Place Γ τ} {src : Place Γ τ}
    (compProg : oseair.Prog)
    {csStart : CompilerState}
    (h_invAt : InvAt ρa ρt s_mir s_osea csStart)
    (hF : (∃ so, CheckedCompilerM.value
        (compileStmtChecked (.assign dst (.move src))) csStart = Except.ok so) →
      StmtFrame compProg cs0 prog s_mir.pc
        (CheckedCompilerM.run (compileStmtChecked (.assign dst (.move src))) csStart))
    (h_step : mirlite.stepStmt MSB s_mir (.assign dst (.move src)) = .ok s_mir') :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' := by
  rw [stepStmt_assign_movesrc_anyflatten] at h_step
  have h_pkg : ValuePkg compProg (RExpr.move (flattenPlace src)) := by
    rcases flatten_chainish src with h_ch | ⟨σ', sb, sp, h_eq, h_sb⟩
    · exact move_valuePkg_of_chain compProg h_ch
    · rw [h_eq]
      exact move_valuePkg_of_projchain sp compProg h_sb
  obtain ⟨h_crun, h_cval⟩ := compileAssignChecked_congr_pre dst (.move src)
    (.move (flattenPlace src))
    (fun cs => (compileRExprPreChecked_move_flatten src cs).1.symm)
    (fun cs => (compileRExprPreChecked_move_flatten src cs).2.symm)
  cases dst with
  | «local» dstLoc =>
      cases h_envD : mirlite.Env.lookup s_mir.env dstLoc with
      | some bD =>
          obtain ⟨ρt', s_osea', n, h_incr, h_run, h_inv'⟩ :=
            storereg_local_simulation compProg h_pkg h_invAt
              (StmtFrame.congr hF h_crun h_cval) h_envD h_step
          exact ⟨ρa, ρt', s_osea', n, AddrRenameIncr.refl ρa, h_incr, h_run, h_inv'⟩
      | none =>
          exact storereg_localfresh_simulation compProg h_pkg h_invAt
            (StmtFrame.congr hF h_crun h_cval) h_envD h_step
  | proj dbase g =>
      exact storereg_projdst_recursion compProg h_pkg h_invAt
        (StmtFrame.congr hF h_crun h_cval) h_step
  | deref P =>
      rw [stepStmt_assign_dstderef_flatten] at h_step
      obtain ⟨ρt', s_osea', n, h_incr, h_run, h_inv'⟩ :=
        storereg_chaindst_simulation (P := flattenPlace P) compProg h_pkg
          (PtrChain_flatten_deref P) h_invAt (StmtFrame.congr hF
          (fun cs => (h_crun cs).trans (compileStmt_assign_derefdst_flatten_run _ cs))
          (fun cs so h => by
            obtain ⟨so1, h1⟩ := compileStmt_assign_derefdst_flatten_value _ cs so h
            exact h_cval cs so1 h1))
          h_step
      exact ⟨ρa, ρt', s_osea', n, AddrRenameIncr.refl ρa, h_incr, h_run, h_inv'⟩

theorem CompilerInv_step_move
    {τ : LayoutTy} {dst : Place Γ τ} {src : Place Γ τ}
    (compProg : oseair.Prog)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    (h_stmt : prog.get? s_mir.pc = some (.assign dst (.move src)))
    (h_step : mirlite.stepStmt MSB s_mir (.assign dst (.move src)) = .ok s_mir') :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' := by
  obtain ⟨csPrefix, h_csAt, h_invAt⟩ := h_inv.invAt
  exact assignStep_move compProg h_invAt
    (StmtFrame.ofAssign h_comp h_csAt h_stmt (fun _ => rfl) (fun _ so h => ⟨so, h⟩))
    h_step

end obseq3.proof
