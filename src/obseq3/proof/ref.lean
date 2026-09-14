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
      simp only [obseq.LayoutTy.TupL.sizeOf_spec]
      omega





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
            (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)])
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
    simp [csCompile, compileRExprToChecked, placeToBorrowRegChecked, h_run, h_val, h_prun,
      h_pval, h_pres]
    simp [csRun, cleanupInstrs, emit_nil, setPlaceInfo, emit]
    funext label
    rw [if_neg (fun h => by rcases h with ⟨h1, h2⟩; omega)]
  · obtain ⟨h_prun, placeOut, h_pval, h_pres⟩ :=
      placeToRegChecked_local_existing (kind := kind) h_srcPost
    simp only [csCompile, csMonad, compileRExprToChecked, placeToBorrowRegChecked, h_run, h_pval]
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
            (Rhs.Borrow kind prot mask (blockSize τ) dOut.result.reg
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
      h_relB⟩ :=
      ref_chainsrc_borrow h_shape.chain f kindL kind prot mask compProg
        sM sA csA h_id_a h_wf_t h_tbd h_lbs h_prb h_sms h_psim h_pc h_dres h_fit
        h_ref_src h_dval _ rfl h_instS (hFrag.instrAt 0 rfl rfl)
    refine ⟨_, nB, sB, perms', _, h_incr_t, h_wf_t', rfl,
      by simp [blockSize, obseq.layoutSize], h_runB,
      by rw [h_pre]; simp only [emit]; exact h_dprm,
      by rw [h_pre]; simp only [emit]; omega,
      by rw [h_pre]; exact h_lbsB,
      by rw [hsB]; exact h_psim', by rw [hsB]; exact h_tbd', h_memB,
      by rw [h_pre]; exact h_pcB,
      StoreStep.rstore compProg sB _ obseq.TyVal.PTy _ _
        (by rw [hsB]; exact RegMap.lookup_insert_self _ _ _)
        (by rw [h_pre]; show _ < _; simp only [emit]; omega),
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
              (emitM [Instr.Assgn tmpReg (Rhs.Borrow kind prot mask (blockSize τ) loadedReg 0)])
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
              (emitM [Instr.Assgn tmpReg (Rhs.Borrow kind prot mask (blockSize τ) loadedReg 0)])
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

theorem compileStmt_assign_derefdst_flatten_run
    {Γ : Ctx} {τ : LayoutTy}
    {P : Place Γ (obseq.LayoutTy.PtrL (obseq.LayoutTy.PtrL τ))}
    (rhs : RExpr Γ (obseq.LayoutTy.PtrL τ)) (cs : CompilerState) :
    CheckedCompilerM.run
        (compileStmtChecked
          (Stmt.assign (.deref P) rhs)) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.deref (flattenPlace P))
              rhs)) cs := by
  have h_er : ensurePlaceRoot (Place.deref (flattenPlace P))
      = ensurePlaceRoot (Place.deref P) := ensurePlaceRoot_flatten (Place.deref P)
  simp only [csMonad, compileStmtChecked, h_er]
  cases hP : CheckedCompilerM.value
      (compileRExprPreChecked rhs) (CompilerM.run (ensurePlaceRoot (Place.deref P)) cs) with
  | error eP => simp only [hP]
  | ok oP =>
      simp only [hP]
      obtain ⟨h_agr, h_agv⟩ := placeToRegChecked_flatten_agree (Place.deref P)
        RefKind.Mut (CheckedCompilerM.run (compileRExprPreChecked rhs) (CompilerM.run (ensurePlaceRoot (Place.deref P)) cs))
      rw [show flattenPlace (Place.deref P) = Place.deref (flattenPlace P) from rfl]
        at h_agr h_agv
      cases hF : CheckedCompilerM.value
          (placeToRegChecked RefKind.Mut (Place.deref (flattenPlace P)))
          (CheckedCompilerM.run (compileRExprPreChecked rhs) (CompilerM.run (ensurePlaceRoot (Place.deref P)) cs)) with
      | error eF =>
          cases hO : CheckedCompilerM.value
              (placeToRegChecked RefKind.Mut (Place.deref P))
              (CheckedCompilerM.run (compileRExprPreChecked rhs) (CompilerM.run (ensurePlaceRoot (Place.deref P)) cs)) with
          | error eO =>
              simp only [hF, hO]
              exact h_agr.symm
          | ok oO =>
              exfalso
              rw [hF, hO] at h_agv
              simp [Except.map] at h_agv
      | ok oF =>
          cases hO : CheckedCompilerM.value
              (placeToRegChecked RefKind.Mut (Place.deref P))
              (CheckedCompilerM.run (compileRExprPreChecked rhs) (CompilerM.run (ensurePlaceRoot (Place.deref P)) cs)) with
          | error eO =>
              exfalso
              rw [hF, hO] at h_agv
              simp [Except.map] at h_agv
          | ok oO =>
              have h_res : oF.result = oO.result := by
                rw [hF, hO] at h_agv
                simpa [Except.map] using h_agv
              simp only [hF, hO, h_res]
              rw [h_agr]

theorem compileStmt_assign_derefdst_flatten_value
    {Γ : Ctx} {τ : LayoutTy}
    {P : Place Γ (obseq.LayoutTy.PtrL (obseq.LayoutTy.PtrL τ))}
    (rhs : RExpr Γ (obseq.LayoutTy.PtrL τ)) (cs : CompilerState) :
    ∀ so, CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.deref (flattenPlace P))
            rhs)) cs
      = Except.ok so →
    ∃ so', CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.deref P) rhs)) cs
      = Except.ok so' := by
  intro so h_so
  have h_er : ensurePlaceRoot (Place.deref (flattenPlace P))
      = ensurePlaceRoot (Place.deref P) := ensurePlaceRoot_flatten (Place.deref P)
  simp only [csMonad, compileStmtChecked, h_er] at h_so ⊢
  cases hP : CheckedCompilerM.value
      (compileRExprPreChecked rhs) (CompilerM.run (ensurePlaceRoot (Place.deref P)) cs) with
  | error eP =>
      exfalso
      rw [hP] at h_so
      simp at h_so
  | ok oP =>
      rw [hP] at h_so
      simp only [hP]
      obtain ⟨h_agr, h_agv⟩ := placeToRegChecked_flatten_agree (Place.deref P)
        RefKind.Mut (CheckedCompilerM.run (compileRExprPreChecked rhs) (CompilerM.run (ensurePlaceRoot (Place.deref P)) cs))
      rw [show flattenPlace (Place.deref P) = Place.deref (flattenPlace P) from rfl]
        at h_agr h_agv
      cases hO : CheckedCompilerM.value
          (placeToRegChecked RefKind.Mut (Place.deref P))
          (CheckedCompilerM.run (compileRExprPreChecked rhs) (CompilerM.run (ensurePlaceRoot (Place.deref P)) cs)) with
      | error eO =>
          exfalso
          cases hF : CheckedCompilerM.value
              (placeToRegChecked RefKind.Mut (Place.deref (flattenPlace P)))
              (CheckedCompilerM.run (compileRExprPreChecked rhs) (CompilerM.run (ensurePlaceRoot (Place.deref P)) cs)) with
          | error eF =>
              rw [hF] at h_so
              simp at h_so
          | ok oF =>
              rw [hF, hO] at h_agv
              simp [Except.map] at h_agv
      | ok oO =>
          simp only [hO]
          exact ⟨_, rfl⟩


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

theorem compileStmt_ref_src_congr_local_run
    {Γ : Ctx} {τ : LayoutTy}
    {dstLoc : Local Γ (obseq.LayoutTy.PtrL τ)}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (src1 src2 : Place Γ τ) (cs : CompilerState)
    (h_agr : CheckedCompilerM.run (placeToBorrowRegChecked kind prot mask src1)
        ((ensureLocalRegE dstLoc).run cs)
      = CheckedCompilerM.run (placeToBorrowRegChecked kind prot mask src2)
        ((ensureLocalRegE dstLoc).run cs))
    (h_agv : (CheckedCompilerM.value (placeToBorrowRegChecked kind prot mask src1)
        ((ensureLocalRegE dstLoc).run cs)).map (fun o => o.result)
      = (CheckedCompilerM.value (placeToBorrowRegChecked kind prot mask src2)
        ((ensureLocalRegE dstLoc).run cs)).map (fun o => o.result)) :
    CheckedCompilerM.run
        (compileStmtChecked (Stmt.assign (.local dstLoc) (.ref kind prot mask src1))) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.local dstLoc) (.ref kind prot mask src2))) cs := by
  simp only [csCompile, csMonad, compileRExprToChecked]
  rcases exceptMap_agree h_agv with ⟨e1, e2, h1, h2⟩ | ⟨o1, o2, h1, h2, h_res⟩
  · simp only [h1, h2]; exact h_agr
  · simp only [h1, h2, h_res, h_agr]

theorem compileStmt_ref_src_congr_local_value
    {Γ : Ctx} {τ : LayoutTy}
    {dstLoc : Local Γ (obseq.LayoutTy.PtrL τ)}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (src1 src2 : Place Γ τ) (cs : CompilerState)
    (h_agv : (CheckedCompilerM.value (placeToBorrowRegChecked kind prot mask src1)
        ((ensureLocalRegE dstLoc).run cs)).map (fun o => o.result)
      = (CheckedCompilerM.value (placeToBorrowRegChecked kind prot mask src2)
        ((ensureLocalRegE dstLoc).run cs)).map (fun o => o.result)) :
    ∀ so, CheckedCompilerM.value
        (compileStmtChecked (Stmt.assign (.local dstLoc) (.ref kind prot mask src2))) cs
      = Except.ok so →
    ∃ so', CheckedCompilerM.value
        (compileStmtChecked (Stmt.assign (.local dstLoc) (.ref kind prot mask src1))) cs
      = Except.ok so' := by
  intro so h_so
  simp only [csCompile, csMonad, compileRExprToChecked] at h_so ⊢
  rcases exceptMap_agree h_agv with ⟨e1, e2, h1, h2⟩ | ⟨o1, o2, h1, h2, h_res⟩
  · exfalso; rw [h2] at h_so; simp at h_so
  · simp only [h1]; exact ⟨_, rfl⟩






/-- The general source-flattening transfer for a local destination,
    the other instantiation of the congruence. -/
theorem compileStmt_ref_srcflatten_local_run
    {Γ : Ctx} {τ : LayoutTy}
    {dstLoc : Local Γ (obseq.LayoutTy.PtrL τ)}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (src : Place Γ τ) (cs : CompilerState) :
    CheckedCompilerM.run
        (compileStmtChecked (Stmt.assign (.local dstLoc) (.ref kind prot mask src))) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.local dstLoc)
              (.ref kind prot mask (flattenPlace src)))) cs :=
  compileStmt_ref_src_congr_local_run (dstLoc := dstLoc) kind prot mask _ _ cs
    (placeToBorrowRegChecked_flatten_agree kind prot mask src _).1.symm
    (placeToBorrowRegChecked_flatten_agree kind prot mask src _).2.symm

theorem compileStmt_ref_srcflatten_local_value
    {Γ : Ctx} {τ : LayoutTy}
    {dstLoc : Local Γ (obseq.LayoutTy.PtrL τ)}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (src : Place Γ τ) (cs : CompilerState) :
    ∀ so, CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.local dstLoc)
            (.ref kind prot mask (flattenPlace src)))) cs
      = Except.ok so →
    ∃ so', CheckedCompilerM.value
        (compileStmtChecked (Stmt.assign (.local dstLoc) (.ref kind prot mask src))) cs
      = Except.ok so' :=
  compileStmt_ref_src_congr_local_value (dstLoc := dstLoc) kind prot mask _ _ cs
    (placeToBorrowRegChecked_flatten_agree kind prot mask src _).2.symm

/-- The same congruence for a DEREF destination. The destination
    lowering runs at the POST-rhs state, so run-agreement of the two
    borrow lowerings is what makes it see the same state; the store
    mentions the source only through `result.reg`, which agrees too. -/
theorem compileStmt_ref_src_congr_deref_run
    {Γ : Ctx} {τ : LayoutTy}
    {P : Place Γ (obseq.LayoutTy.PtrL (obseq.LayoutTy.PtrL τ))}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (src1 src2 : Place Γ τ) (cs : CompilerState)
    (h_agr : CheckedCompilerM.run (placeToBorrowRegChecked kind prot mask src1)
        (CompilerM.run (ensurePlaceRoot (Place.deref P)) cs)
      = CheckedCompilerM.run (placeToBorrowRegChecked kind prot mask src2)
        (CompilerM.run (ensurePlaceRoot (Place.deref P)) cs))
    (h_agv : (CheckedCompilerM.value (placeToBorrowRegChecked kind prot mask src1)
        (CompilerM.run (ensurePlaceRoot (Place.deref P)) cs)).map (fun o => o.result)
      = (CheckedCompilerM.value (placeToBorrowRegChecked kind prot mask src2)
        (CompilerM.run (ensurePlaceRoot (Place.deref P)) cs)).map (fun o => o.result)) :
    CheckedCompilerM.run
        (compileStmtChecked (Stmt.assign (.deref P) (.ref kind prot mask src1))) cs
      = CheckedCompilerM.run
          (compileStmtChecked (Stmt.assign (.deref P) (.ref kind prot mask src2))) cs := by
  simp only [csCompile, csMonad]
  rcases exceptMap_agree h_agv with ⟨e1, e2, h1, h2⟩ | ⟨o1, o2, h1, h2, h_res⟩
  · simp only [h1, h2]; exact h_agr
  · simp only [h1, h2, h_res, h_agr]

theorem compileStmt_ref_src_congr_deref_value
    {Γ : Ctx} {τ : LayoutTy}
    {P : Place Γ (obseq.LayoutTy.PtrL (obseq.LayoutTy.PtrL τ))}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (src1 src2 : Place Γ τ) (cs : CompilerState)
    (h_agr : CheckedCompilerM.run (placeToBorrowRegChecked kind prot mask src1)
        (CompilerM.run (ensurePlaceRoot (Place.deref P)) cs)
      = CheckedCompilerM.run (placeToBorrowRegChecked kind prot mask src2)
        (CompilerM.run (ensurePlaceRoot (Place.deref P)) cs))
    (h_agv : (CheckedCompilerM.value (placeToBorrowRegChecked kind prot mask src1)
        (CompilerM.run (ensurePlaceRoot (Place.deref P)) cs)).map (fun o => o.result)
      = (CheckedCompilerM.value (placeToBorrowRegChecked kind prot mask src2)
        (CompilerM.run (ensurePlaceRoot (Place.deref P)) cs)).map (fun o => o.result)) :
    ∀ so, CheckedCompilerM.value
        (compileStmtChecked (Stmt.assign (.deref P) (.ref kind prot mask src2))) cs
      = Except.ok so →
    ∃ so', CheckedCompilerM.value
        (compileStmtChecked (Stmt.assign (.deref P) (.ref kind prot mask src1))) cs
      = Except.ok so' := by
  intro so h_so
  simp only [csCompile, csMonad] at h_so ⊢
  rcases exceptMap_agree h_agv with ⟨e1, e2, h1, h2⟩ | ⟨o1, o2, h1, h2, h_res⟩
  · exfalso; rw [h2] at h_so; simp at h_so
  · simp only [h2] at h_so
    simp only [h1, h_res, h_agr]
    cases hD : CheckedCompilerM.value (placeToRegChecked RefKind.Mut (Place.deref P))
        (CheckedCompilerM.run (placeToBorrowRegChecked kind prot mask src2)
          (CompilerM.run (ensurePlaceRoot (Place.deref P)) cs)) with
    | error eD => exfalso; simp only [hD] at h_so; simp at h_so
    | ok oD => simp only [hD]; exact ⟨_, rfl⟩



/-- The source-flattening transfer for a DEREF destination, the third
    instantiation of the deref-destination congruence. -/
theorem compileStmt_ref_srcflatten_deref_run
    {Γ : Ctx} {τ : LayoutTy}
    {P : Place Γ (obseq.LayoutTy.PtrL (obseq.LayoutTy.PtrL τ))}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (src : Place Γ τ) (cs : CompilerState) :
    CheckedCompilerM.run
        (compileStmtChecked (Stmt.assign (.deref P) (.ref kind prot mask src))) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.deref P) (.ref kind prot mask (flattenPlace src)))) cs :=
  compileStmt_ref_src_congr_deref_run (P := P) kind prot mask _ _ cs
    (placeToBorrowRegChecked_flatten_agree kind prot mask src _).1.symm
    (placeToBorrowRegChecked_flatten_agree kind prot mask src _).2.symm

theorem compileStmt_ref_srcflatten_deref_value
    {Γ : Ctx} {τ : LayoutTy}
    {P : Place Γ (obseq.LayoutTy.PtrL (obseq.LayoutTy.PtrL τ))}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (src : Place Γ τ) (cs : CompilerState) :
    ∀ so, CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.deref P) (.ref kind prot mask (flattenPlace src)))) cs
      = Except.ok so →
    ∃ so', CheckedCompilerM.value
        (compileStmtChecked (Stmt.assign (.deref P) (.ref kind prot mask src))) cs
      = Except.ok so' :=
  compileStmt_ref_src_congr_deref_value (P := P) kind prot mask _ _ cs
    (placeToBorrowRegChecked_flatten_agree kind prot mask src _).1.symm
    (placeToBorrowRegChecked_flatten_agree kind prot mask src _).2.symm



/-- The same congruence for a PROJECTED destination, general in the
    base so both the local-base and deref-base spellings are covered. -/
theorem compileStmt_ref_src_congr_proj_run
    {Γ : Ctx} {τ : LayoutTy}
    {σ : LayoutTy} {dbase : Place Γ σ} {g : PathTo σ (obseq.LayoutTy.PtrL τ)}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (src1 src2 : Place Γ τ) (cs : CompilerState)
    (h_agr : CheckedCompilerM.run (placeToBorrowRegChecked kind prot mask src1)
        (CompilerM.run (ensurePlaceRoot (Place.proj dbase g)) cs)
      = CheckedCompilerM.run (placeToBorrowRegChecked kind prot mask src2)
        (CompilerM.run (ensurePlaceRoot (Place.proj dbase g)) cs))
    (h_agv : (CheckedCompilerM.value (placeToBorrowRegChecked kind prot mask src1)
        (CompilerM.run (ensurePlaceRoot (Place.proj dbase g)) cs)).map (fun o => o.result)
      = (CheckedCompilerM.value (placeToBorrowRegChecked kind prot mask src2)
        (CompilerM.run (ensurePlaceRoot (Place.proj dbase g)) cs)).map (fun o => o.result)) :
    CheckedCompilerM.run
        (compileStmtChecked (Stmt.assign (.proj dbase g) (.ref kind prot mask src1))) cs
      = CheckedCompilerM.run
          (compileStmtChecked (Stmt.assign (.proj dbase g) (.ref kind prot mask src2))) cs := by
  simp only [csCompile, csMonad]
  rcases exceptMap_agree h_agv with ⟨e1, e2, h1, h2⟩ | ⟨o1, o2, h1, h2, h_res⟩
  · simp only [h1, h2]; exact h_agr
  · simp only [h1, h2, h_res, h_agr]

theorem compileStmt_ref_src_congr_proj_value
    {Γ : Ctx} {τ : LayoutTy}
    {σ : LayoutTy} {dbase : Place Γ σ} {g : PathTo σ (obseq.LayoutTy.PtrL τ)}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (src1 src2 : Place Γ τ) (cs : CompilerState)
    (h_agr : CheckedCompilerM.run (placeToBorrowRegChecked kind prot mask src1)
        (CompilerM.run (ensurePlaceRoot (Place.proj dbase g)) cs)
      = CheckedCompilerM.run (placeToBorrowRegChecked kind prot mask src2)
        (CompilerM.run (ensurePlaceRoot (Place.proj dbase g)) cs))
    (h_agv : (CheckedCompilerM.value (placeToBorrowRegChecked kind prot mask src1)
        (CompilerM.run (ensurePlaceRoot (Place.proj dbase g)) cs)).map (fun o => o.result)
      = (CheckedCompilerM.value (placeToBorrowRegChecked kind prot mask src2)
        (CompilerM.run (ensurePlaceRoot (Place.proj dbase g)) cs)).map (fun o => o.result)) :
    ∀ so, CheckedCompilerM.value
        (compileStmtChecked (Stmt.assign (.proj dbase g) (.ref kind prot mask src2))) cs
      = Except.ok so →
    ∃ so', CheckedCompilerM.value
        (compileStmtChecked (Stmt.assign (.proj dbase g) (.ref kind prot mask src1))) cs
      = Except.ok so' := by
  intro so h_so
  simp only [csCompile, csMonad] at h_so ⊢
  rcases exceptMap_agree h_agv with ⟨e1, e2, h1, h2⟩ | ⟨o1, o2, h1, h2, h_res⟩
  · exfalso; rw [h2] at h_so; simp at h_so
  · simp only [h2] at h_so
    simp only [h1, h_res, h_agr]
    cases hD : CheckedCompilerM.value (placeToRegChecked RefKind.Mut (Place.proj dbase g))
        (CheckedCompilerM.run (placeToBorrowRegChecked kind prot mask src2)
          (CompilerM.run (ensurePlaceRoot (Place.proj dbase g)) cs)) with
    | error eD => exfalso; simp only [hD] at h_so; simp at h_so
    | ok oD => simp only [hD]; exact ⟨_, rfl⟩

/-- The source-flattening transfer for a PROJECTED destination, the
    other instantiation of the projected-destination congruence. -/
theorem compileStmt_ref_srcflatten_proj_run
    {Γ : Ctx} {τ σ : LayoutTy}
    {dbase : Place Γ σ} {g : PathTo σ (obseq.LayoutTy.PtrL τ)}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (src : Place Γ τ) (cs : CompilerState) :
    CheckedCompilerM.run
        (compileStmtChecked (Stmt.assign (.proj dbase g) (.ref kind prot mask src))) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.proj dbase g)
              (.ref kind prot mask (flattenPlace src)))) cs :=
  compileStmt_ref_src_congr_proj_run (dbase := dbase) (g := g) kind prot mask _ _ cs
    (placeToBorrowRegChecked_flatten_agree kind prot mask src _).1.symm
    (placeToBorrowRegChecked_flatten_agree kind prot mask src _).2.symm

theorem compileStmt_ref_srcflatten_proj_value
    {Γ : Ctx} {τ σ : LayoutTy}
    {dbase : Place Γ σ} {g : PathTo σ (obseq.LayoutTy.PtrL τ)}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (src : Place Γ τ) (cs : CompilerState) :
    ∀ so, CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.proj dbase g) (.ref kind prot mask (flattenPlace src)))) cs
      = Except.ok so →
    ∃ so', CheckedCompilerM.value
        (compileStmtChecked (Stmt.assign (.proj dbase g) (.ref kind prot mask src))) cs
      = Except.ok so' :=
  compileStmt_ref_src_congr_proj_value (dbase := dbase) (g := g) kind prot mask _ _ cs
    (placeToBorrowRegChecked_flatten_agree kind prot mask src _).1.symm
    (placeToBorrowRegChecked_flatten_agree kind prot mask src _).2.symm







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




/-- The per-statement simulation for `dst := &kind src`. Since
    2026-09-13 the source contributes ONLY a value package: flatten it
    once, read off which of the two package constructors applies, and
    hand it to the destination leaf. So this dispatcher is a case split
    on the DESTINATION alone, and every arm is three lines. -/
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
  -- the source, normalised once and for all
  rw [stepStmt_assign_refsrc_anyflatten] at h_step
  have h_pkg : ValuePkg compProg (RExpr.ref kind prot mask (flattenPlace src)) := by
    rcases flatten_chainish src with h_ch | ⟨σ', sb, sp, h_eq, h_sb⟩
    · exact ref_valuePkg_of_chain kind prot mask compProg h_ch
    · rw [h_eq]
      exact ref_valuePkg_of_projchain sp kind prot mask compProg h_sb
  cases dst with
  | «local» dstLoc =>
      cases h_envD : mirlite.Env.lookup s_mir.env dstLoc with
      | some bD =>
          obtain ⟨ρt', s_osea', n, h_incr, h_run, h_inv'⟩ :=
            storereg_local_simulation compProg h_pkg h_comp h_inv h_stmt
              (fun cs => compileStmt_ref_srcflatten_local_run kind prot mask src cs)
              (fun cs so h =>
                compileStmt_ref_srcflatten_local_value kind prot mask src cs so h)
              h_envD h_step
          exact ⟨ρa, ρt', s_osea', n, AddrRenameIncr.refl ρa, h_incr, h_run, h_inv'⟩
      | none =>
          exact storereg_localfresh_simulation compProg h_pkg h_comp h_inv h_stmt
            (fun cs => compileStmt_ref_srcflatten_local_run kind prot mask src cs)
            (fun cs so h =>
              compileStmt_ref_srcflatten_local_value kind prot mask src cs so h)
            h_envD h_step
  | proj dbase g =>
      exact storereg_projdst_recursion compProg h_pkg h_comp h_inv h_stmt
        (fun cs => compileStmt_ref_srcflatten_proj_run kind prot mask src cs)
        (fun cs so h =>
          compileStmt_ref_srcflatten_proj_value kind prot mask src cs so h)
        h_step
  | deref P =>
      rw [stepStmt_assign_dstderef_flatten] at h_step
      obtain ⟨ρt', s_osea', n, h_incr, h_run, h_inv'⟩ :=
        storereg_chaindst_simulation (P := flattenPlace P) compProg h_pkg
          (PtrChain_flatten_deref P) h_comp h_inv h_stmt
          (fun cs => (compileStmt_ref_srcflatten_deref_run kind prot mask src cs).trans
            (compileStmt_assign_derefdst_flatten_run _ cs))
          (fun cs so h => by
            obtain ⟨so1, h1⟩ := compileStmt_assign_derefdst_flatten_value _ cs so h
            exact compileStmt_ref_srcflatten_deref_value kind prot mask src cs so1 h1)
          h_step
      exact ⟨ρa, ρt', s_osea', n, AddrRenameIncr.refl ρa, h_incr, h_run, h_inv'⟩

end obseq3.proof
