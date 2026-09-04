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

/-- A layout is never its own pointee: `τ ≠ PtrL τ`. Since `Local` carries
    `Γ.get idx = τ`, this is what makes a `PtrL τ`-typed destination and a
    `τ`-typed source necessarily DISTINCT locals — which the fresh-
    destination regime needs, because mirlite binds the destination before
    resolving the source. -/
theorem layout_ne_ptrL (τ : LayoutTy) : τ ≠ obseq.LayoutTy.PtrL τ := by
  intro h
  have := congrArg sizeOf h
  simp at this

/-- Hence the two locals have different indices. -/
theorem ref_dst_src_idx_ne {Γ : Ctx} {τ : LayoutTy}
    (dstLoc : Local Γ (obseq.LayoutTy.PtrL τ)) (srcLoc : Local Γ τ) :
    srcLoc.idx ≠ dstLoc.idx := by
  intro h
  have hs := srcLoc.hTy
  rw [h, dstLoc.hTy] at hs
  exact layout_ne_ptrL τ hs.symm

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

/-- Index disjointness for a PROJECTED DESTINATION over a plain source:
    sharing an index would force `σ = τ` and hence a path from `τ` to
    `PtrL τ`, but `PtrL τ` is strictly bigger than `τ`. -/
theorem ref_dst_src_idx_ne_of_proj {Γ : Ctx} {τ σ : LayoutTy}
    (dstLoc : Local Γ σ) (srcLoc : Local Γ τ)
    (g : PathTo σ (obseq.LayoutTy.PtrL τ)) :
    srcLoc.idx ≠ dstLoc.idx := by
  intro h
  have hs := srcLoc.hTy
  rw [h, dstLoc.hTy] at hs
  subst hs
  have h_le := PathTo.sizeOf_le g
  simp only [obseq.LayoutTy.PtrL.sizeOf_spec] at h_le
  omega

/-- `prepare_lookup_ne` for a PROJECTED destination whose root is
    unbound: `allocateRoot` sets exactly the root local, so every other
    local's binding survives. -/
theorem prepare_lookup_ne_proj {Γ : Ctx} {τ σ ρ : LayoutTy}
    {s s' : mirlite.State MSB Γ}
    {dst : Local Γ σ} {g : PathTo σ ρ} {other : Local Γ τ}
    (h_ne : other.idx ≠ dst.idx)
    (h_env : mirlite.Env.lookup s.env dst = none)
    (h : mirlite.preparePlaceAssign MSB s (.proj (.local dst) g) = .ok s') :
    mirlite.Env.lookup s'.env other = mirlite.Env.lookup s.env other := by
  simp only [mirAlloc, mirPrep, mirlite.resolvePlaceAcc, h_env] at h
  split at h
  · exact absurd h (by simp)
  · injection h with h'
    rw [← h']
    show (mirlite.Env.set s.env dst _) other.idx = _
    simp only [mirlite.Env.set, if_neg h_ne]
    rfl

/-- The same for a PROJECTED source: if the two locals shared an index
    the source's layout would be `PtrL τ`, and there is no path from a
    pointer layout to `τ` — `.nil` would force `τ = PtrL τ` and `.field`
    needs a tuple. `cases f` discharges both by unification. -/
theorem ref_proj_dst_src_idx_ne {Γ : Ctx} {τ σb : LayoutTy}
    (dstLoc : Local Γ (obseq.LayoutTy.PtrL τ)) (srcLoc : Local Γ σb)
    (f : PathTo σb τ) :
    srcLoc.idx ≠ dstLoc.idx := by
  intro h
  have hs := srcLoc.hTy
  rw [h, dstLoc.hTy] at hs
  subst hs
  cases f

/-- Preparing one local's assignment leaves every OTHER local's binding
    alone: either the destination was already bound (the state is
    unchanged) or it was allocated, and `Env.set` only touches its own
    index. Needed twice by the fresh-destination regime, because
    `doAssign` resolves the SOURCE against the post-allocation state. -/
theorem prepare_lookup_ne {Γ : Ctx} {τ σ : LayoutTy}
    {s s' : mirlite.State MSB Γ}
    {dst : Local Γ σ} {other : Local Γ τ}
    (h_ne : other.idx ≠ dst.idx)
    (h : mirlite.preparePlaceAssign MSB s (.local dst) = .ok s') :
    mirlite.Env.lookup s'.env other = mirlite.Env.lookup s.env other := by
  simp only [mirPrep] at h
  cases h_env : mirlite.Env.lookup s.env dst with
  | some b =>
      rw [h_env] at h
      simp only at h
      injection h with h'
      rw [← h']
  | none =>
      rw [h_env] at h
      simp only [mirlite.allocateRoot, mirlite.allocateBase] at h
      split at h
      · exact absurd h (by simp)
      · injection h with h'
        rw [← h']
        show (mirlite.Env.set s.env dst _) other.idx = _
        simp only [mirlite.Env.set, if_neg h_ne]
        rfl

/-! ## The compiled fragment of a `local := &local` retag -/

/-- The fragment of `dst := &src` when BOTH places are mapped locals: one
    `Borrow` into a fresh temp, then the `RStore` of that pointer into the
    destination. Note there is no `Die`: the borrow's cleanup lives in the
    rhs result, and the `.assign (.local _)` arm never emits it — the
    stored reference must stay alive, which is exactly why this leaf does
    NOT need BRIDGE 1. -/
theorem compileStmt_ref_local_local_lowers
    {Γ : Ctx} {τ : LayoutTy}
    {dstLoc : Local Γ (obseq.LayoutTy.PtrL τ)} {srcLoc : Local Γ τ}
    {cs : CompilerState} {dstReg srcReg : Register}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = some (dstReg, obseq.LayoutTy.PtrL τ))
    (h_src : getPlaceInfo cs srcLoc.idx.1 = some (srcReg, τ)) :
    LowersTo
        (compileStmtChecked
          (Stmt.assign (.local dstLoc) (.ref kind prot mask (.local srcLoc)))) cs
      (emit (emit { cs with nextReg := cs.nextReg + 1 }
          [Instr.Assgn (Register.R cs.nextReg)
            (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)])
          [Instr.RStore obseq.TyVal.PTy (Register.R cs.nextReg) dstReg]) := by
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_existing h_dst
  refine ⟨?_, ?_⟩
  · obtain ⟨h_prun, placeOut, h_pval, h_pres⟩ :=
      placeToRegChecked_local_existing (kind := kind) h_src
    simp [csCompile, compileRExprToChecked, placeToBorrowRegChecked, h_run, h_val, h_prun,
      h_pval, h_pres]
    simp [csRun, cleanupInstrs, emit_nil]
  · obtain ⟨h_prun, placeOut, h_pval, h_pres⟩ :=
      placeToRegChecked_local_existing (kind := kind) h_src
    simp only [csCompile, csMonad, compileRExprToChecked, placeToBorrowRegChecked, h_run, h_pval]
    exact ⟨_, rfl⟩
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
/-- The fragment of `dst := &kind s.f` when `dst` is an UNMAPPED local
    and the borrowed place is a PROJECTED field of a mapped local:
    `Alloc` for the fresh destination root, then the `Borrow` at the
    field's offset, then the `RStore`. Same THREE instructions as the
    fresh L→L fragment — as everywhere in `ref`, the projection only
    moves the borrow's offset operand. -/
theorem compileStmt_ref_fresh_projsrc_lowers
    {Γ : Ctx} {τ σb : LayoutTy}
    {dstLoc : Local Γ (obseq.LayoutTy.PtrL τ)} {srcLoc : Local Γ σb}
    {f : PathTo σb τ}
    {cs : CompilerState} {srcReg : Register}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = none)
    (h_src : getPlaceInfo cs srcLoc.idx.1 = some (srcReg, σb)) :
    LowersTo
        (compileStmtChecked
          (Stmt.assign (.local dstLoc)
            (.ref kind prot mask (.proj (.local srcLoc) f)))) cs
      (emit (emit
          { (setPlaceInfo
              (emit { cs with nextReg := cs.nextReg + 1 }
                [Instr.Assgn (Register.R cs.nextReg)
                  (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))])
              dstLoc.idx.1 (Register.R cs.nextReg, obseq.LayoutTy.PtrL τ)) with
              nextReg := cs.nextReg + 1 + 1 }
          [Instr.Assgn (Register.R (cs.nextReg + 1))
            (Rhs.Borrow kind prot mask (blockSize τ) srcReg (pathOffset f))])
          [Instr.RStore obseq.TyVal.PTy (Register.R (cs.nextReg + 1))
            (Register.R cs.nextReg)]) := by
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_fresh (loc := dstLoc) h_dst
  refine ⟨?_, ?_⟩
  · have h_run' : (ensureLocalRegE dstLoc cs).snd.val
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
        srcLoc.idx.1 = some (srcReg, σb) := by
      by_cases h_eq : srcLoc.idx.1 = dstLoc.idx.1
      · exfalso
        grind
      · rw [getPlaceInfo_setPlaceInfo_ne _ h_eq, getPlaceInfo_emit]
        exact h_src
    obtain ⟨h_prun, placeOut, h_pval, h_pres⟩ :=
      placeToRegChecked_local_existing (kind := kind) h_srcPost
    have h_borrow_eq : placeToBorrowRegChecked (Γ := Γ) kind prot mask
        (.proj (.local srcLoc) f)
        = (do
            let baseOut ← placeToRegChecked kind (.local srcLoc)
            let baseRes := baseOut.result
            let offset := pathOffset f
            let tmpReg ← CheckedCompilerM.lift freshRegM
            let _ ← CheckedCompilerM.lift
              (emitM [Instr.Assgn tmpReg (Rhs.Borrow kind prot mask (blockSize τ) baseRes.reg offset)])
            pure {
              result := { reg := tmpReg,
                          cleanup := baseRes.cleanup ++ [(tmpReg, blockSize τ)] },
              evidence := PlaceToBorrowRegEvidence.proj (.local srcLoc) f baseRes tmpReg
                baseOut.evidence
            }) := by simp only [placeToBorrowRegChecked]
    simp [csCompile, compileRExprToChecked, h_borrow_eq, h_run, h_val, h_prun, h_pval, h_pres]
    simp [csRun, cleanupInstrs, emit_nil, setPlaceInfo, emit]
    funext label
    rw [if_neg (fun h => by rcases h with ⟨h1, h2⟩; omega)]
  · have h_srcPost : getPlaceInfo
        (setPlaceInfo
          (emit { cs with nextReg := cs.nextReg + 1 }
            [Instr.Assgn (Register.R cs.nextReg)
              (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))])
          dstLoc.idx.1 (Register.R cs.nextReg, obseq.LayoutTy.PtrL τ))
        srcLoc.idx.1 = some (srcReg, σb) := by
      by_cases h_eq : srcLoc.idx.1 = dstLoc.idx.1
      · exfalso
        grind
      · rw [getPlaceInfo_setPlaceInfo_ne _ h_eq, getPlaceInfo_emit]
        exact h_src
    obtain ⟨h_prun, placeOut, h_pval, h_pres⟩ :=
      placeToRegChecked_local_existing (kind := kind) h_srcPost
    simp only [csCompile, csMonad, compileRExprToChecked, placeToBorrowRegChecked, h_run, h_pval]
    exact ⟨_, rfl⟩
/-- The fragment of `dst := &src.f` when `dst` is a mapped local and the
    borrowed place is a PROJECTED field of a mapped local: one `Borrow` at
    the field's offset over the field's length, then the `RStore`. Same
    two instructions as the L→L fragment — projection only moves the
    offset, thanks to the reassociating lowering. -/
theorem compileStmt_ref_proj_local_lowers
    {Γ : Ctx} {τ σb : LayoutTy}
    {dstLoc : Local Γ (obseq.LayoutTy.PtrL τ)} {srcLoc : Local Γ σb}
    {f : PathTo σb τ}
    {cs : CompilerState} {dstReg srcReg : Register}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = some (dstReg, obseq.LayoutTy.PtrL τ))
    (h_src : getPlaceInfo cs srcLoc.idx.1 = some (srcReg, σb)) :
    LowersTo
        (compileStmtChecked
          (Stmt.assign (.local dstLoc)
            (.ref kind prot mask (.proj (.local srcLoc) f)))) cs
      (emit (emit { cs with nextReg := cs.nextReg + 1 }
          [Instr.Assgn (Register.R cs.nextReg)
            (Rhs.Borrow kind prot mask (blockSize τ) srcReg (pathOffset f))])
          [Instr.RStore obseq.TyVal.PTy (Register.R cs.nextReg) dstReg]) := by
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_existing h_dst
  have h_run' : (ensureLocalRegE dstLoc cs).snd.val = cs := h_run
  obtain ⟨h_prun, placeOut, h_pval, h_pres⟩ :=
    placeToRegChecked_local_existing (kind := kind) h_src
  refine ⟨?_, ?_⟩
  · have h_borrow_eq : placeToBorrowRegChecked (Γ := Γ) kind prot mask
        (.proj (.local srcLoc) f)
        = (do
            let baseOut ← placeToRegChecked kind (.local srcLoc)
            let baseRes := baseOut.result
            let offset := pathOffset f
            let tmpReg ← CheckedCompilerM.lift freshRegM
            let _ ← CheckedCompilerM.lift
              (emitM [Instr.Assgn tmpReg (Rhs.Borrow kind prot mask (blockSize τ) baseRes.reg offset)])
            pure {
              result := { reg := tmpReg,
                          cleanup := baseRes.cleanup ++ [(tmpReg, blockSize τ)] },
              evidence := PlaceToBorrowRegEvidence.proj (.local srcLoc) f baseRes tmpReg
                baseOut.evidence
            }) := by simp only [placeToBorrowRegChecked]
    simp [csCompile, compileRExprToChecked, h_borrow_eq, h_run, h_run', h_val, h_prun, h_pval,
      h_pres]
    simp [csRun, cleanupInstrs, emit_nil]
  · have h_borrow_eq : placeToBorrowRegChecked (Γ := Γ) kind prot mask
        (.proj (.local srcLoc) f)
        = (do
            let baseOut ← placeToRegChecked kind (.local srcLoc)
            let baseRes := baseOut.result
            let offset := pathOffset f
            let tmpReg ← CheckedCompilerM.lift freshRegM
            let _ ← CheckedCompilerM.lift
              (emitM [Instr.Assgn tmpReg (Rhs.Borrow kind prot mask (blockSize τ) baseRes.reg offset)])
            pure {
              result := { reg := tmpReg,
                          cleanup := baseRes.cleanup ++ [(tmpReg, blockSize τ)] },
              evidence := PlaceToBorrowRegEvidence.proj (.local srcLoc) f baseRes tmpReg
                baseOut.evidence
            }) := by simp only [placeToBorrowRegChecked]
    simp only [csCompile, csMonad, compileRExprToChecked, h_borrow_eq, h_run, h_pval]
    exact ⟨_, rfl⟩
/-- The fragment of `dst := &kind *P`, stated over the OPAQUE run of the
    WHOLE source place's lowering: the src code (owned by the mother
    lemma, ending in its `Load`), then the `Borrow` off the loaded
    register, then the `RStore` into the mapped dst. The borrow-deref
    arm shares its prefix with the place-lowering deref arm, so the
    equality is proved by one case split on the INNER value. -/
theorem compileStmt_ref_deref_lowers
    {Γ : Ctx} {τ : LayoutTy}
    {dstLoc : Local Γ (obseq.LayoutTy.PtrL τ)}
    {P : Place Γ (obseq.LayoutTy.PtrL τ)}
    {cs : CompilerState} {dstReg : Register}
    {dOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared (.deref P))}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = some (dstReg, obseq.LayoutTy.PtrL τ))
    (h_dval : CheckedCompilerM.value (placeToRegChecked RefKind.Shared (.deref P)) cs
      = Except.ok dOut) :
    LowersTo
        (compileStmtChecked
          (Stmt.assign (.local dstLoc) (.ref kind prot mask (.deref P)))) cs
      (emit (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (Place.deref P)) cs) with
            nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (Place.deref P)) cs).nextReg + 1 }
          [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (Place.deref P)) cs).nextReg)
            (Rhs.Borrow kind prot mask (blockSize τ) dOut.result.reg 0)])
          [Instr.RStore obseq.TyVal.PTy (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (Place.deref P)) cs).nextReg) dstReg]) := by
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_existing h_dst
  refine ⟨?_, ?_⟩
  · have h_run' : (ensureLocalRegE dstLoc cs).snd.val = cs := h_run
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
        simp [csCompile, compileRExprToChecked, h_bindB, h_bindD, h_run, h_run', h_val, h_x]
        simp [csRun, cleanupInstrs, emit_nil]
  · have h_bindB : placeToBorrowRegChecked (Γ := Γ) kind prot mask (.deref P)
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
        simp only [csCompile, csMonad, compileRExprToChecked, h_bindB, h_run, h_x]
        exact ⟨_, rfl⟩
/-- The fragment of `dst := &kind *chain` when `dst` is an UNMAPPED
    local: the σ-sized `Alloc` for the fresh root comes FIRST, so the
    source spine lowers from the post-`Alloc` compiler state and the
    `RStore` goes through the root register. -/
theorem compileStmt_ref_fresh_derefsrc_lowers
    {Γ : Ctx} {τ : LayoutTy}
    {dstLoc : Local Γ (obseq.LayoutTy.PtrL τ)}
    {P : Place Γ (obseq.LayoutTy.PtrL τ)}
    {cs : CompilerState}
    {dOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared (.deref P))}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = none)
    (h_dval : CheckedCompilerM.value (placeToRegChecked RefKind.Shared (.deref P))
        (setPlaceInfo
        (emit { cs with nextReg := cs.nextReg + 1 }
          [Instr.Assgn (Register.R cs.nextReg)
            (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))])
        dstLoc.idx.1 (Register.R cs.nextReg, obseq.LayoutTy.PtrL τ))
      = Except.ok dOut) :
    LowersTo
        (compileStmtChecked
          (Stmt.assign (.local dstLoc) (.ref kind prot mask (.deref P)))) cs
      (emit (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (Place.deref P))
          (setPlaceInfo
                (emit { cs with nextReg := cs.nextReg + 1 }
                  [Instr.Assgn (Register.R cs.nextReg)
                    (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))])
                dstLoc.idx.1 (Register.R cs.nextReg, obseq.LayoutTy.PtrL τ))) with
            nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (Place.deref P))
          (setPlaceInfo
                (emit { cs with nextReg := cs.nextReg + 1 }
                  [Instr.Assgn (Register.R cs.nextReg)
                    (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))])
                dstLoc.idx.1 (Register.R cs.nextReg, obseq.LayoutTy.PtrL τ))).nextReg + 1 }
          [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (Place.deref P))
          (setPlaceInfo
                (emit { cs with nextReg := cs.nextReg + 1 }
                  [Instr.Assgn (Register.R cs.nextReg)
                    (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))])
                dstLoc.idx.1 (Register.R cs.nextReg, obseq.LayoutTy.PtrL τ))).nextReg)
            (Rhs.Borrow kind prot mask (blockSize τ) dOut.result.reg 0)])
          [Instr.RStore obseq.TyVal.PTy
            (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (Place.deref P))
          (setPlaceInfo
                (emit { cs with nextReg := cs.nextReg + 1 }
                  [Instr.Assgn (Register.R cs.nextReg)
                    (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))])
                dstLoc.idx.1 (Register.R cs.nextReg, obseq.LayoutTy.PtrL τ))).nextReg) (Register.R cs.nextReg)]) := by
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_fresh (loc := dstLoc) h_dst
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
  refine ⟨?_, ?_⟩
  · have h_bindD : placeToRegChecked (Γ := Γ) RefKind.Shared (.deref P)
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
    cases h_x : CheckedCompilerM.value (placeToRegChecked RefKind.Shared P)
        (setPlaceInfo
          (emit { cs with nextReg := cs.nextReg + 1 }
            [Instr.Assgn (Register.R cs.nextReg)
              (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))])
          dstLoc.idx.1 (Register.R cs.nextReg, obseq.LayoutTy.PtrL τ)) with
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
        simp [csCompile, compileRExprToChecked, h_bindB, h_bindD, h_run, h_val, h_x]
        simp [csRun, cleanupInstrs, emit_nil, setPlaceInfo]
  · have h_bindD : placeToRegChecked (Γ := Γ) RefKind.Shared (.deref P)
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
    cases h_x : CheckedCompilerM.value (placeToRegChecked RefKind.Shared P)
        (setPlaceInfo
          (emit { cs with nextReg := cs.nextReg + 1 }
            [Instr.Assgn (Register.R cs.nextReg)
              (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))])
          dstLoc.idx.1 (Register.R cs.nextReg, obseq.LayoutTy.PtrL τ)) with
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
        simp only [csCompile, csMonad, compileRExprToChecked, h_bindB, h_bindD, h_run, h_x]
        simp only [csRun]
        exact ⟨_, rfl⟩
/-! ## Regime L→L: `dstLocal := &srcLocal`, both bound -/

/-- REGIME L→L, CLOSED: a reference to a BOUND local stored into a BOUND
    pointer-typed local. The fragment is `Borrow; RStore` — no `Die`, so
    no BRIDGE 1: the borrow stays alive because it is the stored value.
    This is the first leaf that grows ρt at a USER-visible tag: the
    source's fresh reference tag and the target's are paired by
    `sb_ref_respects_PermSim`, and the stored pointer's `MemValSim` holds
    under that extension with its referent range supplied by the source
    local's `LocalBindingSim` block-domain conjunct. ρa does not grow.

    No size side condition: zero-sized referents are fine. (Until
    2026-08-22 the target's `Rhs.Borrow` bounds check was
    `addr ≥ base + size`, which rejected them while mirlite's `M.ref`
    accepted them — Rust sides with mirlite, `&()` is legal — and this
    regime carried `0 < blockSize τ`. The check is now the range form
    `addr + len > base + size`, the same as `writeThroughPtr`'s, and the
    residual is gone.) -/
theorem ref_local_local_simulation
    {τ : LayoutTy}
    {dstLoc : Local Γ (obseq.LayoutTy.PtrL τ)} {srcLoc : Local Γ τ}
    {bD bS : mirlite.Binding}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (compProg : oseair.Prog)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    (h_stmt : prog.get? s_mir.pc
      = some (.assign (.local dstLoc) (.ref kind prot mask (.local srcLoc))))
    (h_envD : mirlite.Env.lookup s_mir.env dstLoc = some bD)
    (h_envS : mirlite.Env.lookup s_mir.env srcLoc = some bS)
    (h_step : mirlite.stepStmt MSB s_mir
      (.assign (.local dstLoc) (.ref kind prot mask (.local srcLoc))) = .ok s_mir') :
    ∃ (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa ρt' s_mir' s_osea' := by
  obtain ⟨csPrefix, ⟨h_csAt, h_pc⟩, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_tbd,
    h_alloc, h_unmap, h_prb⟩ := h_inv
  obtain ⟨dstReg, baseD, tagD, h_piD, h_entryD, h_raD, h_rtD, h_nwD, h_domD⟩ :=
    h_lbs dstLoc bD h_envD
  obtain ⟨srcReg, baseS, tagS, h_piS, h_entryS, h_raS, h_rtS, h_nwS, h_domS⟩ :=
    h_lbs srcLoc bS h_envS
  have h_baseD : baseD = bD.addr := (h_id_a _ _ h_raD).symm
  have h_baseS : baseS = bS.addr := (h_id_a _ _ h_raS).symm
  subst h_baseD
  subst h_baseS
  -- §1 invert the source step: prepare is a no-op, both locals resolve,
  -- the retag succeeds, the pointer is written
  simp only [mirPrep, mirlite.stepStmt, mirlite.doAssign, mirlite.doAssignCont, h_envD,
    mirlite.resolvePlaceAcc, h_envS, mirlite.evalRExpr] at h_step
  rw [if_neg (Nat.lt_irrefl (bS.addr + blockSize τ))] at h_step
  cases h_ref_src : MSB.ref s_mir.perms bS.addr (blockSize τ) bS.tag kind prot mask with
  | error e => rw [h_ref_src] at h_step; simp at h_step
  | ok pr =>
      obtain ⟨perms', freshTag⟩ := pr
      rw [h_ref_src] at h_step
      simp only at h_step
      have h0 : wildcardTag < s_mir.perms.NextTag := (h_tbd _ _ h_wf_t.2).1
      have h_nw_new : (s_mir.perms.NextTag == wildcardTag) = false := by grind
      -- §3 the fragment and its two instructions
      have h_stmtRun := (compileStmt_ref_local_local_lowers (cs := csPrefix) kind prot mask
        h_piD h_piS).run
      obtain ⟨stmtOut, h_stmtOut⟩ :=
        (compileStmt_ref_local_local_lowers (cs := csPrefix) kind prot mask h_piD h_piS).value
      have hFrag :=
        (CodeIncluded.of_stmt h_comp h_csAt h_stmt h_stmtOut).fragmentOf
          h_stmtRun h_pc
      have h_code1 : compProg s_osea.pc
          = some (Instr.Assgn (Register.R csPrefix.nextReg)
              (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)) :=
        hFrag.instrAt 0 rfl rfl
      have h_code2 : compProg (s_osea.pc + 1)
          = some (Instr.RStore obseq.TyVal.PTy (Register.R csPrefix.nextReg) dstReg) :=
        hFrag.instrAt 1 rfl rfl
      -- §4 the SOURCE package: the retag transported, the `Borrow` executed
      obtain ⟨tgtPerms, rfl, h_incr_t, h_wf_t', h_tbd', h_psim', h_run1, h_lbsB,
        h_pcB, h_relB⟩ :=
        ref_local_borrow τ τ kind prot mask 0 compProg s_mir s_osea csPrefix
          h_id_a h_wf_t h_tbd h_lbs h_prb h_psim h_pc h_entryS h_raS h_rtS h_nwS
          h_domS (by simp) (by simpa using h_ref_src) h_code1
      have h_rt_new : (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag)
          s_mir.perms.NextTag = some s_osea.perms.NextTag :=
        TagRenameMap.extend_self _ _ _
      have h_rtD' : (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag) bD.tag
          = some tagD := h_incr_t _ _ h_rtD
      -- §5-§6 the BOUND-root PLAIN write seam: the store goes through the
      -- destination local's own register
      simp only [h_envD] at h_step
      have h_regne : dstReg ≠ Register.R csPrefix.nextReg := by
        cases dstReg with
        | R n =>
            have h_lt := h_prb _ _ _ h_piD
            grind
      obtain ⟨s_osea', n, h_run, h_inv'⟩ :=
        copy_boundplain_write_after_read (τ := obseq.LayoutTy.PtrL τ)
          (dbase := bD.addr) (dtag := bD.tag)
          (dsize := blockSize (obseq.LayoutTy.PtrL τ))
          (csR := (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
            [Instr.Assgn (Register.R csPrefix.nextReg)
              (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)]))
          (sR := { s_osea with
            perms := tgtPerms,
            reg := oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
              (obseq.TyVal.PTy, [Val.Ptr bS.addr (0 + 0) (blockSize τ) s_osea.perms.NextTag]),
            pc := s_osea.pc + 1 })
          (vreg := Register.R csPrefix.nextReg)
          (vals := [Val.Ptr bS.addr (0 + 0) (blockSize τ) s_osea.perms.NextTag])
          (mvals := [mirlite.MemValue.ptrVal bS.addr (bS.addr - bS.addr) (blockSize τ)
            s_mir.perms.NextTag])
          compProg h_comp h_stmt h_csAt h_stmtOut h_id_a h_wf_t' h_unmap h_prb
          0 h_raD h_rtD' h_nwD h_domD h_run1
          (by
            show oseair.RegMap.lookup _ _ = _
            rw [RegMap.lookup_insert_ne _ h_regne]
            exact h_entryD)
          (SourceMemSim.rename_mono (AddrRenameIncr.refl ρa) h_incr_t h_sms)
          h_alloc rfl (by simp only [emit]; exact Nat.le_succ _) h_lbsB h_psim'
          h_tbd' h_pcB (RegMap.lookup_insert_self _ _ _)
          (by simp [blockSize, obseq.layoutSize])
          (by simp [blockSize, obseq.layoutSize])
          h_code2
          (by rw [h_pc, h_stmtRun]; simp [emit])
          (by rw [h_stmtRun]; simp only [emit])
          (by rw [h_stmtRun]; simp only [emit]; omega)
          (by simp [blockSize, obseq.layoutSize]) (by simp) rfl rfl rfl h_relB h_step
      exact ⟨_, s_osea', n, h_incr_t, h_run, h_inv'⟩
/-- REGIME F→L, CLOSED: `&src` stored into an UNBOUND local. mirlite's
    prepare allocates the destination, so the fragment gains a leading
    root `Alloc` and BOTH renames grow — ρa by the identity pair
    (`AllocLockstep` makes the two allocators agree), and ρt TWICE in one
    statement: `sb_own` mints the destination's root tag, then `sb_ref`
    mints the reference tag. The second extension is well-formed because
    the first member hands back the `TagRenameBounded` at the intermediate
    counters, which is exactly the hypothesis the second one takes. -/
theorem ref_fresh_dst_simulation
    {τ : LayoutTy}
    {dstLoc : Local Γ (obseq.LayoutTy.PtrL τ)} {srcLoc : Local Γ τ}
    {bS : mirlite.Binding}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (compProg : oseair.Prog)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    (h_stmt : prog.get? s_mir.pc
      = some (.assign (.local dstLoc) (.ref kind prot mask (.local srcLoc))))
    (h_envD : mirlite.Env.lookup s_mir.env dstLoc = none)
    (h_envS : mirlite.Env.lookup s_mir.env srcLoc = some bS)
    (h_step : mirlite.stepStmt MSB s_mir
      (.assign (.local dstLoc) (.ref kind prot mask (.local srcLoc))) = .ok s_mir') :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' := by
  obtain ⟨csPrefix, ⟨h_csAt, h_pc⟩, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_tbd,
    h_alloc, h_unmap, h_prb⟩ := h_inv
  have h_piD : getPlaceInfo csPrefix dstLoc.idx.1 = none := h_unmap dstLoc h_envD
  obtain ⟨srcReg, baseS, tagS, h_piS, h_entryS, h_raS, h_rtS, h_nwS, h_domS⟩ :=
    h_lbs srcLoc bS h_envS
  have h_baseS : baseS = bS.addr := (h_id_a _ _ h_raS).symm
  subst h_baseS
  have h_idx_ne := ref_dst_src_idx_ne dstLoc srcLoc
  -- §1 the destination allocation, via the shared fresh-root prologue
  simp only [mirlite.stepStmt, mirlite.doAssign] at h_step
  cases h_prep : mirlite.preparePlaceAssign MSB s_mir (Place.local dstLoc) with
  | err m => rw [h_prep] at h_step; simp at h_step
  | ok s1 =>
      rw [h_prep] at h_step
      rw [show mirlite.preparePlaceAssign MSB s_mir (Place.local dstLoc)
          = mirlite.allocateBase MSB s_mir dstLoc from by
        simp only [mirPrep, mirAlloc, h_envD]] at h_prep
      -- §2 the ρa extension is at the single root address (a pointer is one
      -- word), which is why the prologue takes its four facts as inputs
      have h_incr_a : AddrRenameIncr ρa
          (ρa.extend s_mir.mem.addrStart s_mir.mem.addrStart) :=
        AddrRenameIncr.extend_id h_id_a _
      have h_id_a' : IdentityOnDomain
          (ρa.extend s_mir.mem.addrStart s_mir.mem.addrStart) :=
        IdentityOnDomain.extend_id h_id_a _
      have h_ra_new : (ρa.extend s_mir.mem.addrStart s_mir.mem.addrStart)
          s_mir.mem.addrStart = some s_mir.mem.addrStart :=
        AddrRenameMap.extend_self _ _ _
      obtain ⟨permsOwned, tgtP1, h_own_tgt', h_perms1, h_pc1, h_env1,
        hD1, h_memstart1, h_find1, h_incr1, h_wf1, h_tbd1, h_psim1,
        h_erun, h_prb1, h_lbs1⟩ :=
        copy_freshroot_prologue h_envD h_prep h_id_a h_wf_t h_tbd h_psim h_alloc
          h_lbs h_prb h_piD h_incr_a h_id_a' h_ra_new
          (fun k hk => by
            have hk0 : k = 0 := by
              simp only [blockSize, obseq.layoutSize] at hk
              omega
            subst hk0
            simpa using h_ra_new)
      have h_addr_eq : s_osea.mem.addrStart = s_mir.mem.addrStart := h_alloc
      have h_szD : obseq.typeSize (layoutToTyVal (obseq.LayoutTy.PtrL τ))
          = blockSize (obseq.LayoutTy.PtrL τ) := obseq.typeSize_layoutToTyVal _
      -- §3 resolve the source (untouched by the allocation) and retag it
      have hS1 : mirlite.Env.lookup s1.env srcLoc = some bS := by
        rw [h_env1]
        simp only [mirlite.Env.lookup, mirlite.Env.set, if_neg h_idx_ne]
        exact h_envS
      simp only [mirlite.doAssignCont, mirlite.resolvePlaceAcc, hD1,
        mirlite.evalRExpr, hS1] at h_step
      rw [if_neg (Nat.lt_irrefl (bS.addr + blockSize τ))] at h_step
      cases h_ref_src : MSB.ref s1.perms bS.addr (blockSize τ) bS.tag kind prot mask with
      | error e => rw [h_ref_src] at h_step; simp at h_step
      | ok pr2 =>
          obtain ⟨perms', tagR⟩ := pr2
          rw [h_ref_src] at h_step
          simp only at h_step
          -- §4 the source binding's facts move to the extended ρt
          have h_rtS1 := h_incr1 _ _ h_rtS
          have h_raS' := h_incr_a _ _ h_raS
          -- §7 the fragment: Alloc; Borrow; RStore
          have h_stmtRun := (compileStmt_ref_fresh_local_lowers (cs := csPrefix)
            kind prot mask h_piD h_piS).run
          obtain ⟨stmtOut, h_stmtOut⟩ :=
            (compileStmt_ref_fresh_local_lowers (cs := csPrefix) kind prot mask h_piD h_piS).value
          have h_frag :=
            (CodeIncluded.of_stmt h_comp h_csAt h_stmt h_stmtOut).fragmentOf
              h_stmtRun h_pc
          have h_code1 : compProg s_osea.pc
              = some (Instr.Assgn (Register.R csPrefix.nextReg)
                  (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))) :=
            h_frag.instrAt 0 rfl rfl
          have h_code2 : compProg (s_osea.pc + 1)
              = some (Instr.Assgn (Register.R (csPrefix.nextReg + 1))
                  (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)) :=
            h_frag.instrAt 1 rfl rfl
          have h_code3 : compProg (s_osea.pc + 1 + 1)
              = some (Instr.RStore obseq.TyVal.PTy (Register.R (csPrefix.nextReg + 1))
                  (Register.R csPrefix.nextReg)) :=
            h_frag.instrAt 2 rfl rfl
          -- §8 execute Alloc, then Borrow
          have h_run1 := runN_Assgn_Alloc_step compProg s_osea
            (Register.R csPrefix.nextReg) (layoutToTyVal (obseq.LayoutTy.PtrL τ))
            h_code1 h_own_tgt'
          have h_regne : srcReg ≠ Register.R csPrefix.nextReg := by
            cases srcReg with
            | R n => have h_lt := h_prb _ _ _ h_piS; grind
          have h_entryS1 : PtrRegisterEntry
              (oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
                (obseq.TyVal.PTy, [Val.Ptr s_osea.mem.addrStart 0
                  (obseq.typeSize (layoutToTyVal (obseq.LayoutTy.PtrL τ)))
                  s_osea.perms.NextTag]))
              srcReg bS.addr 0 (blockSize τ) tagS := by
            show oseair.RegMap.lookup _ _ = _
            rw [RegMap.lookup_insert_ne _ h_regne]
            exact h_entryS
          -- §8 the SOURCE half as the local-borrow package, from the post-Alloc
          -- states: the retag transport and the Borrow
          obtain ⟨tgtP2, rfl, h_incr2, h_wf2, h_tbd2, h_psim2, h_run2, h_lbsB, h_pcB,
            h_relB⟩ :=
            ref_local_borrow (ρa := ρa.extend s_mir.mem.addrStart s_mir.mem.addrStart)
              (ρt := ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag)
              τ τ kind prot mask 0 compProg s1
              { s_osea with mem := (oseair.allocate s_osea.mem (obseq.typeSize (layoutToTyVal (obseq.LayoutTy.PtrL τ)))).2, perms := tgtP1, reg := oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg) (obseq.TyVal.PTy, [Val.Ptr s_osea.mem.addrStart 0 (obseq.typeSize (layoutToTyVal (obseq.LayoutTy.PtrL τ))) s_osea.perms.NextTag]), pc := s_osea.pc + 1 }
              (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))]) dstLoc.idx.1 (Register.R csPrefix.nextReg, obseq.LayoutTy.PtrL τ))
              h_id_a' h_wf1 (by rw [h_perms1]; exact h_tbd1) h_lbs1 h_prb1
              (by rw [h_perms1]; exact h_psim1)
              (by
                show s_osea.pc + 1 = _
                rw [h_pc]
                simp only [emit_nextLabel, setPlaceInfo_nextLabel, List.length_cons,
                  List.length_nil])
              h_entryS1 h_raS' h_rtS1 h_nwS
              (fun k hk => ⟨(h_domS k hk).choose,
                h_incr_a _ _ (h_domS k hk).choose_spec⟩)
              (by simp) (by simpa using h_ref_src) h_code2
          have h_incr12 := TagRenameIncr.trans h_incr1 h_incr2
          -- §9-§10 the fresh-root WRITE seam, shared with copy: the
          -- `RStore` through the root, the memory extension, the rebuild
          simp only [hD1] at h_step
          exact copy_freshroot_write_after_read
            (τ := obseq.LayoutTy.PtrL τ)
            (csR := (emit
              { (setPlaceInfo
                (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                  [Instr.Assgn (Register.R csPrefix.nextReg)
                    (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))])
                dstLoc.idx.1 (Register.R csPrefix.nextReg, obseq.LayoutTy.PtrL τ)) with
                nextReg := csPrefix.nextReg + 1 + 1 }
              [Instr.Assgn (Register.R (csPrefix.nextReg + 1))
                (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)]))
            (sR := { s_osea with
                mem := (oseair.allocate s_osea.mem
                  (obseq.typeSize (layoutToTyVal (obseq.LayoutTy.PtrL τ)))).2,
                perms := tgtP2,
                reg := oseair.RegMap.insert
                  (oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
                    (obseq.TyVal.PTy, [Val.Ptr s_osea.mem.addrStart 0
                      (obseq.typeSize (layoutToTyVal (obseq.LayoutTy.PtrL τ)))
                      s_osea.perms.NextTag]))
                  (Register.R (csPrefix.nextReg + 1))
                  (obseq.TyVal.PTy, [Val.Ptr bS.addr (0 + 0) (blockSize τ)
                    tgtP1.NextTag]),
                pc := s_osea.pc + 1 + 1 })
            (vreg := Register.R (csPrefix.nextReg + 1))
            (vals := [Val.Ptr bS.addr (0 + 0) (blockSize τ) tgtP1.NextTag])
            (mvals := [mirlite.MemValue.ptrVal bS.addr (bS.addr - bS.addr)
              (blockSize τ) s1.perms.NextTag])
            compProg h_comp h_stmt h_csAt
            h_stmtOut h_sms h_unmap h_prb hD1 h_env1 h_pc1 h_memstart1 h_find1
            h_addr_eq h_szD h_run1 h_incr_a h_incr12 h_id_a' h_wf2
            (fun k hk => by
              have hk0 : k = 0 := by
                simp only [blockSize, obseq.layoutSize] at hk
                omega
              subst hk0
              simpa using h_ra_new)
            h_prb1 h_run2
            (by simp only [emit, setPlaceInfo])
            (by simp only [emit, setPlaceInfo]; omega)
            h_lbsB
            h_psim2 h_tbd2 rfl
            h_pcB
            (RegMap.lookup_insert_self _ _ _)
            (by simp [blockSize, obseq.layoutSize])
            h_stmtRun (by simp [blockSize, obseq.layoutSize]) (Nat.le_refl _) rfl rfl
            h_relB
            h_step
/-- REGIME P→L, CLOSED: a reference to a PROJECTED FIELD of a bound local,
    stored into a bound local — `q := &mut s.f` (any kind, any offset,
    projections composed by the reassociating lowering). The same two
    instructions as L→L with the offset moved; the target `Borrow`'s
    bounds check is discharged by pure TYPING
    (`PathTo.offset_add_size_le`: a field's range fits its layout), since
    the source's `sb_ref` has no bounds check to transport. The stored
    pointer covers the WHOLE base allocation (mirlite stores
    `allocBase`/`allocSize`), which is exactly why `LocalBindingSim`
    carries the block-domain conjunct over the full block. -/
theorem ref_proj_local_simulation
    {τ σb : LayoutTy}
    {dstLoc : Local Γ (obseq.LayoutTy.PtrL τ)} {srcLoc : Local Γ σb}
    {f : PathTo σb τ}
    {bD bS : mirlite.Binding}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (compProg : oseair.Prog)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    {stmt0 : Stmt Γ}
    (h_stmt : prog.get? s_mir.pc = some stmt0)
    (h_run0 : ∀ cs, CheckedCompilerM.run (compileStmtChecked stmt0) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.local dstLoc) (.ref kind prot mask (.proj (.local srcLoc) f)))) cs)
    (h_val0 : ∀ cs so, CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.local dstLoc) (.ref kind prot mask (.proj (.local srcLoc) f)))) cs
        = Except.ok so →
      ∃ so', CheckedCompilerM.value (compileStmtChecked stmt0) cs
        = Except.ok so')
    (h_envD : mirlite.Env.lookup s_mir.env dstLoc = some bD)
    (h_envS : mirlite.Env.lookup s_mir.env srcLoc = some bS)
    (h_step : mirlite.stepStmt MSB s_mir
      (.assign (.local dstLoc)
        (.ref kind prot mask (.proj (.local srcLoc) f))) = .ok s_mir') :
    ∃ (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa ρt' s_mir' s_osea' := by
  obtain ⟨csPrefix, ⟨h_csAt, h_pc⟩, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_tbd,
    h_alloc, h_unmap, h_prb⟩ := h_inv
  obtain ⟨dstReg, baseD, tagD, h_piD, h_entryD, h_raD, h_rtD, h_nwD, h_domD⟩ :=
    h_lbs dstLoc bD h_envD
  obtain ⟨srcReg, baseS, tagS, h_piS, h_entryS, h_raS, h_rtS, h_nwS, h_domS⟩ :=
    h_lbs srcLoc bS h_envS
  have h_baseD : baseD = bD.addr := (h_id_a _ _ h_raD).symm
  have h_baseS : baseS = bS.addr := (h_id_a _ _ h_raS).symm
  subst h_baseD
  subst h_baseS
  -- §1 invert the source step: both locals resolve, retag at the FIELD
  simp only [mirPrep, mirlite.stepStmt, mirlite.doAssign, mirlite.doAssignCont, h_envD,
    mirlite.resolvePlaceAcc, h_envS, mirlite.evalRExpr] at h_step
  rw [if_neg (Nat.not_lt.mpr (show bS.addr + pathOffset f + blockSize τ
      ≤ bS.addr + blockSize σb by
    have h_fit := PathTo.offset_add_size_le f
    simp only [Nat.add_assoc]
    exact Nat.add_le_add_left h_fit _))] at h_step
  cases h_ref_src : MSB.ref s_mir.perms (bS.addr + pathOffset f) (blockSize τ)
      bS.tag kind prot mask with
  | error e => rw [h_ref_src] at h_step; simp at h_step
  | ok pr =>
      obtain ⟨perms', freshTag⟩ := pr
      rw [h_ref_src] at h_step
      simp only at h_step
      -- §3 the fragment
      have h_stmtRun := (h_run0 csPrefix).trans
        ((compileStmt_ref_proj_local_lowers (cs := csPrefix) (f := f)
          kind prot mask h_piD h_piS).run)
      obtain ⟨stmtOutC, h_stmtOutC⟩ :=
        (compileStmt_ref_proj_local_lowers (cs := csPrefix) (f := f) kind prot mask h_piD h_piS).value
      obtain ⟨stmtOut, h_stmtOut⟩ := h_val0 csPrefix stmtOutC h_stmtOutC
      have hFrag2 :=
        (CodeIncluded.of_stmt h_comp h_csAt h_stmt h_stmtOut).fragmentOf
          h_stmtRun h_pc
      have h_code1 : compProg s_osea.pc
          = some (Instr.Assgn (Register.R csPrefix.nextReg)
              (Rhs.Borrow kind prot mask (blockSize τ) srcReg (pathOffset f))) :=
        hFrag2.instrAt 0 rfl rfl
      have h_code2 : compProg (s_osea.pc + 1)
          = some (Instr.RStore obseq.TyVal.PTy (Register.R csPrefix.nextReg) dstReg) :=
        hFrag2.instrAt 1 rfl rfl
      -- §4 the SOURCE half as the local-borrow package: the retag transport
      -- and the Borrow, at the field offset (bounds by TYPING)
      obtain ⟨tgtPerms, rfl, h_incr_t, h_wf_t', h_tbd', h_psim', h_run1, h_lbsB, h_pcB,
        h_relB⟩ :=
        ref_local_borrow τ σb kind prot mask (pathOffset f) compProg s_mir s_osea csPrefix
          h_id_a h_wf_t h_tbd h_lbs h_prb h_psim h_pc h_entryS h_raS h_rtS h_nwS
          h_domS (PathTo.offset_add_size_le f) h_ref_src h_code1
      -- §5-§6 the BOUND-root PLAIN write seam
      simp only [h_envD] at h_step
      have h_regne : dstReg ≠ Register.R csPrefix.nextReg := by
        cases dstReg with
        | R n =>
            have h_lt := h_prb _ _ _ h_piD
            grind
      obtain ⟨s_osea', n, h_run, h_inv'⟩ :=
        copy_boundplain_write_after_read (τ := obseq.LayoutTy.PtrL τ)
          (dbase := bD.addr) (dtag := bD.tag)
          (dsize := blockSize (obseq.LayoutTy.PtrL τ))
          (csR := (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
            [Instr.Assgn (Register.R csPrefix.nextReg)
              (Rhs.Borrow kind prot mask (blockSize τ) srcReg (pathOffset f))]))
          (sR := { s_osea with
            perms := tgtPerms,
            reg := oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
              (obseq.TyVal.PTy, [Val.Ptr bS.addr (0 + pathOffset f) (blockSize σb) s_osea.perms.NextTag]),
            pc := s_osea.pc + 1 })
          (vreg := Register.R csPrefix.nextReg)
          (vals := [Val.Ptr bS.addr (0 + pathOffset f) (blockSize σb) s_osea.perms.NextTag])
          (mvals := [mirlite.MemValue.ptrVal bS.addr
            (bS.addr + pathOffset f - bS.addr) (blockSize σb) s_mir.perms.NextTag])
          compProg h_comp h_stmt h_csAt h_stmtOut h_id_a h_wf_t' h_unmap h_prb
          0 h_raD (h_incr_t _ _ h_rtD) h_nwD h_domD h_run1
          (by
            show oseair.RegMap.lookup _ _ = _
            rw [RegMap.lookup_insert_ne _ h_regne]
            exact h_entryD)
          (SourceMemSim.rename_mono (AddrRenameIncr.refl ρa) h_incr_t h_sms)
          h_alloc rfl (by simp only [emit]; exact Nat.le_succ _)
          h_lbsB
          h_psim' h_tbd'
          h_pcB
          (RegMap.lookup_insert_self _ _ _)
          (by simp [blockSize, obseq.layoutSize])
          (by simp [blockSize, obseq.layoutSize])
          h_code2
          (by rw [h_pc, h_stmtRun]; simp [emit])
          (by rw [h_stmtRun]; simp only [emit])
          (by rw [h_stmtRun]; simp only [emit]; omega)
          (by simp [blockSize, obseq.layoutSize]) (by simp) rfl rfl rfl
          h_relB
          h_step
      exact ⟨_, s_osea', n, h_incr_t, h_run, h_inv'⟩
/-! ## Flatten transfer for the ref deref-src shape (through the
    borrow-deref arm: both sides share their prefix, aligned by the
    INNER agree at `Shared P`). -/

theorem compileRExprToChecked_refsrc_flatten_run
    {Γ : Ctx} {τ : LayoutTy} {P : Place Γ (obseq.LayoutTy.PtrL τ)}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (r : Register) (cs : CompilerState) :
    CheckedCompilerM.run
        (compileRExprToChecked r (RExpr.ref (Γ := Γ) kind prot mask (.deref P))) cs
      = CheckedCompilerM.run
          (compileRExprToChecked r
            (RExpr.ref kind prot mask (.deref (flattenPlace P)))) cs := by
  obtain ⟨h_agr, h_agv⟩ := placeToRegChecked_flatten_agree P RefKind.Shared cs
  have h_bF : placeToBorrowRegChecked (Γ := Γ) kind prot mask (.deref (flattenPlace P))
      = (do
          let ptrOut ← placeToRegChecked RefKind.Shared (flattenPlace P)
          let ptrRes := ptrOut.result
          let loadedReg ← CheckedCompilerM.lift freshRegM
          let _ ← CheckedCompilerM.lift
            (emitM [Instr.Assgn loadedReg (Rhs.Load obseq.TyVal.PTy ptrRes.reg)])
          let _ ← CheckedCompilerM.lift (emitM (cleanupInstrs ptrRes.cleanup))
          let tmpReg ← CheckedCompilerM.lift freshRegM
          let _ ← CheckedCompilerM.lift
            (emitM [Instr.Assgn tmpReg
              (Rhs.Borrow kind prot mask (blockSize τ) loadedReg 0)])
          pure {
            result := { reg := tmpReg, cleanup := [(tmpReg, blockSize τ)] },
            evidence := PlaceToBorrowRegEvidence.deref (flattenPlace P) ptrRes
              loadedReg tmpReg ptrOut.evidence
          }) := by simp only [placeToBorrowRegChecked]
  have h_bO : placeToBorrowRegChecked (Γ := Γ) kind prot mask (.deref P)
      = (do
          let ptrOut ← placeToRegChecked RefKind.Shared P
          let ptrRes := ptrOut.result
          let loadedReg ← CheckedCompilerM.lift freshRegM
          let _ ← CheckedCompilerM.lift
            (emitM [Instr.Assgn loadedReg (Rhs.Load obseq.TyVal.PTy ptrRes.reg)])
          let _ ← CheckedCompilerM.lift (emitM (cleanupInstrs ptrRes.cleanup))
          let tmpReg ← CheckedCompilerM.lift freshRegM
          let _ ← CheckedCompilerM.lift
            (emitM [Instr.Assgn tmpReg
              (Rhs.Borrow kind prot mask (blockSize τ) loadedReg 0)])
          pure {
            result := { reg := tmpReg, cleanup := [(tmpReg, blockSize τ)] },
            evidence := PlaceToBorrowRegEvidence.deref P ptrRes loadedReg tmpReg
              ptrOut.evidence
          }) := by simp only [placeToBorrowRegChecked]
  simp only [csMonad, compileRExprToChecked, compileRExprPreChecked, h_bF, h_bO]
  cases hF : CheckedCompilerM.value
      (placeToRegChecked RefKind.Shared (flattenPlace P)) cs with
  | error eF =>
      cases hO : CheckedCompilerM.value
          (placeToRegChecked RefKind.Shared P) cs with
      | error eO =>
          simp only [hF, hO]
          exact h_agr.symm
      | ok oO =>
          exfalso
          rw [hF, hO] at h_agv
          simp [Except.map] at h_agv
  | ok oF =>
      cases hO : CheckedCompilerM.value
          (placeToRegChecked RefKind.Shared P) cs with
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

theorem compileRExprToChecked_refsrc_flatten_valunit
    {Γ : Ctx} {τ : LayoutTy} {P : Place Γ (obseq.LayoutTy.PtrL τ)}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (r : Register) (cs : CompilerState) :
    (CheckedCompilerM.value
        (compileRExprToChecked r (RExpr.ref (Γ := Γ) kind prot mask (.deref P))) cs).map
      (fun _ => ())
      = (CheckedCompilerM.value
          (compileRExprToChecked r
            (RExpr.ref kind prot mask (.deref (flattenPlace P)))) cs).map
        (fun _ => ()) := by
  obtain ⟨h_agr, h_agv⟩ := placeToRegChecked_flatten_agree P RefKind.Shared cs
  have h_bF : placeToBorrowRegChecked (Γ := Γ) kind prot mask (.deref (flattenPlace P))
      = (do
          let ptrOut ← placeToRegChecked RefKind.Shared (flattenPlace P)
          let ptrRes := ptrOut.result
          let loadedReg ← CheckedCompilerM.lift freshRegM
          let _ ← CheckedCompilerM.lift
            (emitM [Instr.Assgn loadedReg (Rhs.Load obseq.TyVal.PTy ptrRes.reg)])
          let _ ← CheckedCompilerM.lift (emitM (cleanupInstrs ptrRes.cleanup))
          let tmpReg ← CheckedCompilerM.lift freshRegM
          let _ ← CheckedCompilerM.lift
            (emitM [Instr.Assgn tmpReg
              (Rhs.Borrow kind prot mask (blockSize τ) loadedReg 0)])
          pure {
            result := { reg := tmpReg, cleanup := [(tmpReg, blockSize τ)] },
            evidence := PlaceToBorrowRegEvidence.deref (flattenPlace P) ptrRes
              loadedReg tmpReg ptrOut.evidence
          }) := by simp only [placeToBorrowRegChecked]
  have h_bO : placeToBorrowRegChecked (Γ := Γ) kind prot mask (.deref P)
      = (do
          let ptrOut ← placeToRegChecked RefKind.Shared P
          let ptrRes := ptrOut.result
          let loadedReg ← CheckedCompilerM.lift freshRegM
          let _ ← CheckedCompilerM.lift
            (emitM [Instr.Assgn loadedReg (Rhs.Load obseq.TyVal.PTy ptrRes.reg)])
          let _ ← CheckedCompilerM.lift (emitM (cleanupInstrs ptrRes.cleanup))
          let tmpReg ← CheckedCompilerM.lift freshRegM
          let _ ← CheckedCompilerM.lift
            (emitM [Instr.Assgn tmpReg
              (Rhs.Borrow kind prot mask (blockSize τ) loadedReg 0)])
          pure {
            result := { reg := tmpReg, cleanup := [(tmpReg, blockSize τ)] },
            evidence := PlaceToBorrowRegEvidence.deref P ptrRes loadedReg tmpReg
              ptrOut.evidence
          }) := by simp only [placeToBorrowRegChecked]
  simp only [csMonad, compileRExprToChecked, compileRExprPreChecked, h_bF, h_bO]
  cases hF : CheckedCompilerM.value
      (placeToRegChecked RefKind.Shared (flattenPlace P)) cs with
  | error eF =>
      cases hO : CheckedCompilerM.value
          (placeToRegChecked RefKind.Shared P) cs with
      | error eO =>
          have h_e : eF = eO := by
            rw [hF, hO] at h_agv
            simpa [Except.map] using h_agv
          subst h_e
          simp [hF, hO, Except.map]
      | ok oO =>
          exfalso
          rw [hF, hO] at h_agv
          simp [Except.map] at h_agv
  | ok oF =>
      cases hO : CheckedCompilerM.value
          (placeToRegChecked RefKind.Shared P) cs with
      | error eO =>
          exfalso
          rw [hF, hO] at h_agv
          simp [Except.map] at h_agv
      | ok oO =>
          simp [hF, hO, Except.map]

theorem compileStmt_ref_derefsrc_flatten_run
    {Γ : Ctx} {τ : LayoutTy}
    {dstLoc : Local Γ (obseq.LayoutTy.PtrL τ)} {P : Place Γ (obseq.LayoutTy.PtrL τ)}
    (kind : RefKind) (prot : Bool) (mask : List Bool) (cs : CompilerState) :
    CheckedCompilerM.run
        (compileStmtChecked
          (Stmt.assign (.local dstLoc) (.ref kind prot mask (.deref P)))) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.local dstLoc)
              (.ref kind prot mask (.deref (flattenPlace P))))) cs := by
  simp only [csMonad, compileStmtChecked]
  have h_run := compileRExprToChecked_refsrc_flatten_run (Γ := Γ) (P := P)
    kind prot mask ((ensureLocalRegE dstLoc).value cs).result.reg
    (CompilerM.run (ensureLocalRegE dstLoc) cs)
  have h_val := compileRExprToChecked_refsrc_flatten_valunit (Γ := Γ) (P := P)
    kind prot mask ((ensureLocalRegE dstLoc).value cs).result.reg
    (CompilerM.run (ensureLocalRegE dstLoc) cs)
  cases hO : CheckedCompilerM.value
      (compileRExprToChecked ((ensureLocalRegE dstLoc).value cs).result.reg
        (RExpr.ref (Γ := Γ) kind prot mask (.deref P)))
      (CompilerM.run (ensureLocalRegE dstLoc) cs) with
  | error eO =>
      cases hF : CheckedCompilerM.value
          (compileRExprToChecked ((ensureLocalRegE dstLoc).value cs).result.reg
            (RExpr.ref kind prot mask (.deref (flattenPlace P))))
          (CompilerM.run (ensureLocalRegE dstLoc) cs) with
      | error eF =>
          simp only [hO, hF]
          exact h_run
      | ok oF =>
          exfalso
          rw [hO, hF] at h_val
          simp [Except.map] at h_val
  | ok oO =>
      cases hF : CheckedCompilerM.value
          (compileRExprToChecked ((ensureLocalRegE dstLoc).value cs).result.reg
            (RExpr.ref kind prot mask (.deref (flattenPlace P))))
          (CompilerM.run (ensureLocalRegE dstLoc) cs) with
      | error eF =>
          exfalso
          rw [hO, hF] at h_val
          simp [Except.map] at h_val
      | ok oF =>
          simp only [hO, hF]
          exact h_run

theorem compileStmt_ref_derefsrc_flatten_value
    {Γ : Ctx} {τ : LayoutTy}
    {dstLoc : Local Γ (obseq.LayoutTy.PtrL τ)} {P : Place Γ (obseq.LayoutTy.PtrL τ)}
    (kind : RefKind) (prot : Bool) (mask : List Bool) (cs : CompilerState) :
    ∀ so, CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.local dstLoc)
            (.ref kind prot mask (.deref (flattenPlace P))))) cs
      = Except.ok so →
    ∃ so', CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.local dstLoc) (.ref kind prot mask (.deref P)))) cs
      = Except.ok so' := by
  intro so h_so
  have h_val := compileRExprToChecked_refsrc_flatten_valunit (Γ := Γ) (P := P)
    kind prot mask ((ensureLocalRegE dstLoc).value cs).result.reg
    (CompilerM.run (ensureLocalRegE dstLoc) cs)
  simp only [csMonad, compileStmtChecked] at h_so ⊢
  cases hO : CheckedCompilerM.value
      (compileRExprToChecked ((ensureLocalRegE dstLoc).value cs).result.reg
        (RExpr.ref (Γ := Γ) kind prot mask (.deref P)))
      (CompilerM.run (ensureLocalRegE dstLoc) cs) with
  | error eO =>
      exfalso
      cases hF : CheckedCompilerM.value
          (compileRExprToChecked ((ensureLocalRegE dstLoc).value cs).result.reg
            (RExpr.ref kind prot mask (.deref (flattenPlace P))))
          (CompilerM.run (ensureLocalRegE dstLoc) cs) with
      | error eF =>
          rw [hF] at h_so
          simp at h_so
      | ok oF =>
          rw [hO, hF] at h_val
          simp [Except.map] at h_val
  | ok oO =>
      simp only [hO]
      exact ⟨_, rfl⟩

/-- REGIME D→L (src side) over full chains, COLLAPSED 2026-08-29
    (originally closed 2026-08-28 for load spines): `dst := &kind *P`
    for every src with `PtrChain (.deref P)` — spines, proj-topped
    pointer places (`x := &*(s.f)`), interior projections at any
    depth; dst a bound local. The mother lemma at `Shared` on the
    WHOLE source place performs the lowering including the final
    `Load`; the leaf adds the `Borrow` off the loaded register (bound
    paid by the retag-dereferenceability check) and the `RStore` into
    the dst. One tag minted on each side. -/
theorem ref_deref_local_simulation
    {τ : LayoutTy}
    {dstLoc : Local Γ (obseq.LayoutTy.PtrL τ)}
    {P : Place Γ (obseq.LayoutTy.PtrL τ)}
    {bD : mirlite.Binding}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (compProg : oseair.Prog)
    (h_spine : PtrChain (Place.deref P))
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    {stmt0 : Stmt Γ}
    (h_stmt : prog.get? s_mir.pc = some stmt0)
    (h_run0 : ∀ cs, CheckedCompilerM.run (compileStmtChecked stmt0) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.local dstLoc) (.ref kind prot mask (.deref P)))) cs)
    (h_val0 : ∀ cs so, CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.local dstLoc) (.ref kind prot mask (.deref P)))) cs
        = Except.ok so →
      ∃ so', CheckedCompilerM.value (compileStmtChecked stmt0) cs
        = Except.ok so')
    (h_envD : mirlite.Env.lookup s_mir.env dstLoc = some bD)
    (h_step : mirlite.stepStmt MSB s_mir
      (.assign (.local dstLoc) (.ref kind prot mask (.deref P))) = .ok s_mir') :
    ∃ (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa ρt' s_mir' s_osea' := by
  obtain ⟨csPrefix, ⟨h_csAt, h_pc⟩, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_tbd,
    h_alloc, h_unmap, h_prb⟩ := h_inv
  obtain ⟨dstReg, baseD, tagD, h_piD, h_entryD, h_raD, h_rtD, h_nwD, -⟩ :=
    h_lbs dstLoc bD h_envD
  have h_baseD : baseD = bD.addr := (h_id_a _ _ h_raD).symm
  subst h_baseD
  -- §1 invert: prepare is a no-op (bound dst); the rhs resolves the
  -- WHOLE src place ACC-style (kept opaque), checks the retag range,
  -- and mints
  simp only [mirlite.stepStmt, mirlite.doAssign] at h_step
  cases h_prep : mirlite.preparePlaceAssign MSB s_mir (Place.local dstLoc) with
  | err msg => rw [h_prep] at h_step; simp at h_step
  | ok s1 =>
  rw [h_prep] at h_step
  have h_s1 : s1 = s_mir := by
    simp only [mirPrep, h_envD] at h_prep
    grind
  rw [h_s1] at h_step
  simp only [mirlite.evalRExpr] at h_step
  cases h_dres : mirlite.resolvePlaceAcc MSB s_mir (Place.deref P) with
  | error e => rw [h_dres] at h_step; simp at h_step
  | ok pr =>
  obtain ⟨resolved, permsR⟩ := pr
  rw [h_dres] at h_step
  simp only at h_step
  by_cases h_fit : resolved.addr + blockSize τ
      > resolved.allocBase + resolved.allocSize
  · rw [if_pos h_fit] at h_step
    simp at h_step
  · rw [if_neg h_fit] at h_step
    cases h_ref_src : MSB.ref permsR resolved.addr (blockSize τ) resolved.tag
        kind prot mask with
    | error e => rw [h_ref_src] at h_step; simp at h_step
    | ok pr2 =>
    obtain ⟨perms', freshTag⟩ := pr2
    rw [h_ref_src] at h_step
    simp only [mirlite.resolvePlaceAcc, h_envD] at h_step
    -- §2 compiler scaffolding: the statement's run is known BEFORE the
    -- mother lemma (the run lemma needs only the value's ok-ness)
    have h_mapped : PlaceInputsMapped csPrefix (Place.deref P) :=
      placeInputsMapped_of_localBindingSim_resolvePlace h_lbs
        (resolvePlace?_of_resolveAcc h_dres)
    obtain ⟨dOut, h_dval⟩ := placeToRegChecked_ok_of_placeInputsMapped
      (cs := csPrefix) (kind := RefKind.Shared) h_mapped
    obtain ⟨stmtOutC, h_stmtOutC⟩ :=
      (compileStmt_ref_deref_lowers kind prot mask h_piD h_dval).value
    obtain ⟨stmtOut, h_stmtOut⟩ := h_val0 csPrefix stmtOutC h_stmtOutC
    have h_stmtRun := (h_run0 csPrefix).trans
      ((compileStmt_ref_deref_lowers kind prot mask h_piD h_dval).run)
    have h_instS : ∀ q' instr,
        q' < (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (Place.deref P)) csPrefix).nextLabel →
        (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (Place.deref P)) csPrefix).code q' = some instr →
        compProg q' = some instr := by
      intro q' instr h_lt h_code
      refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
      · rw [h_stmtRun]
        simp only [emit, List.length_cons, List.length_nil]
        omega
      · rw [h_stmtRun]
        rw [emit_code_lt_nextLabel _ _ (by
          simp only [emit, List.length_cons, List.length_nil]; omega)]
        rw [emit_code_lt_nextLabel _ _ (by
          simp only [emit, List.length_cons, List.length_nil]; omega)]
        exact h_code
    -- §3-§5 the SOURCE half as one package, at the nil projection: the
    -- chain is lowered Shared and the Borrow minted at `kind`
    have hFrag := (CodeIncluded.of_stmt h_comp h_csAt h_stmt h_stmtOut).fragmentOf
      (base := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (Place.deref P)) csPrefix).nextLabel)
      h_stmtRun rfl
    obtain ⟨nB, s_mid, sB, tgtPerms, hsB, rfl, h_incr_t, h_wf_t', h_tbd', h_psim',
      h_runB, h_lbsB, h_pcB, h_dprm, h_dregmono, h_memB, -, h_rt_new, h_nw_new,
      h_relB⟩ :=
      ref_chainsrc_borrow h_spine PathTo.nil RefKind.Shared kind prot mask compProg
        s_mir s_osea csPrefix h_id_a h_wf_t h_tbd h_lbs h_prb h_sms h_psim h_pc h_dres
        (by simpa using h_fit) (by simpa using h_ref_src)
        h_dval _ rfl h_instS (hFrag.instrAt 0 rfl rfl)
    -- §6 the destination binding at the post-Borrow state
    obtain ⟨dstReg2, baseD2, tagD2, h_piD2, h_entryD2, h_raD2, h_rtD2, h_nwD2,
      h_domD⟩ := (LocalBindingSim.placeRegMap_congr (cs' := csPrefix)
        (by simp only [emit]; exact h_dprm.symm) h_lbsB) dstLoc bD h_envD
    have h_dr2 : dstReg2 = dstReg := by grind
    have h_baseD2 : baseD2 = bD.addr := (h_id_a _ _ h_raD2).symm
    rw [h_dr2, h_baseD2] at h_entryD2
    rw [h_baseD2] at h_raD2
    have h_code2 : compProg sB.pc
        = some (Instr.RStore obseq.TyVal.PTy
            (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (Place.deref P)) csPrefix).nextReg) dstReg) := by
      rw [h_pcB]
      simp only [emit, List.length_cons, List.length_nil]
      exact hFrag.instrAt 1 rfl rfl
    -- §7 the BOUND-root PLAIN write seam
    obtain ⟨s_osea', n, h_run, h_inv'⟩ :=
      copy_boundplain_write_after_read (τ := obseq.LayoutTy.PtrL τ)
        (dbase := bD.addr) (dtag := bD.tag)
        (dsize := blockSize (obseq.LayoutTy.PtrL τ))
        (sR := sB)
        (vreg := Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (Place.deref P)) csPrefix).nextReg)
        (vals := [Val.Ptr resolved.allocBase
          (resolved.addr - resolved.allocBase + pathOffset PathTo.nil) resolved.allocSize
          s_mid.perms.NextTag])
        (mvals := [mirlite.MemValue.ptrVal resolved.allocBase
          (resolved.addr + pathOffset PathTo.nil - resolved.allocBase) resolved.allocSize
          permsR.NextTag])
        compProg h_comp h_stmt h_csAt h_stmtOut h_id_a h_wf_t' h_unmap h_prb
        0 h_raD2 h_rtD2 h_nwD2 h_domD h_runB h_entryD2
        (by rw [h_memB]
            exact SourceMemSim.rename_mono (AddrRenameIncr.refl ρa) h_incr_t h_sms)
        (by rw [h_memB]; exact h_alloc)
        (by simp only [emit]; exact h_dprm)
        (by simp only [emit]; exact Nat.le_trans h_dregmono (Nat.le_succ _))
        h_lbsB (by rw [hsB]; exact h_psim') (by rw [hsB]; exact h_tbd') h_pcB
        (by subst hsB; exact RegMap.lookup_insert_self _ _ _)
        (by simp [blockSize, obseq.layoutSize])
        (by simp [blockSize, obseq.layoutSize])
        h_code2
        (by rw [h_pcB, h_stmtRun]; simp [emit])
        (by rw [h_stmtRun]; simp only [emit]; try exact h_dprm)
        (by rw [h_stmtRun]; simp only [emit]; omega)
        (by simp [blockSize, obseq.layoutSize]) (by simp) rfl rfl rfl h_relB h_step
    exact ⟨_, s_osea', n, h_incr_t, h_run, h_inv'⟩
/-- `local`: one fragment lemma for both offsets, the destination tail
    stated through `projDstTail`. -/
theorem compileStmt_ref_projdst_local_lowers
    {Γ : Ctx} {τ σ : LayoutTy}
    {dstLoc : Local Γ σ} {g : PathTo σ (obseq.LayoutTy.PtrL τ)}
    {srcLoc : Local Γ τ}
    {cs : CompilerState} {dstReg srcReg : Register}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = some (dstReg, σ))
    (h_src : getPlaceInfo cs srcLoc.idx.1 = some (srcReg, τ)) :
    LowersTo
        (compileStmtChecked
          (Stmt.assign (.proj (.local dstLoc) g)
            (.ref kind prot mask (.local srcLoc)))) cs
      (projDstTail (emit { cs with nextReg := cs.nextReg + 1 }
          [Instr.Assgn (Register.R cs.nextReg)
            (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)])
        (pathOffset g) (blockSize (obseq.LayoutTy.PtrL τ)) obseq.TyVal.PTy
        (Register.R cs.nextReg) dstReg) := by
  obtain ⟨h_prun, placeOut, h_pval, h_pres⟩ :=
    placeToRegChecked_local_existing (kind := kind) h_src
  have h_dst' : getPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 }
      [Instr.Assgn (Register.R cs.nextReg)
        (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)]) dstLoc.idx.1
      = some (dstReg, σ) := by
    rw [getPlaceInfo_emit, getPlaceInfo_setNextReg]
    exact h_dst
  obtain ⟨h_brun, baseOut, h_bval, h_bres⟩ :=
    placeToRegChecked_local_existing (kind := RefKind.Mut) h_dst'
  have h_proj_eq := placeToRegChecked_proj_root_eq (Γ := Γ) (kind := RefKind.Mut)
    (base := .local dstLoc) g (fun _ _ _ h => by cases h)
  by_cases h_off : pathOffset g = 0
  · rw [h_off, projDstTail_zero]
    refine ⟨?_, ?_⟩
    · have h_root : CompilerM.run (ensurePlaceRoot (Place.proj (Place.local dstLoc) g)) cs
          = cs := by
        exact ensurePlaceRoot_run_eq_of_mapped ⟨dstReg, σ, h_dst⟩
      simp only [csCompile, csMonad, compileRExprToChecked, placeToBorrowRegChecked, h_proj_eq,
        h_root, h_prun, h_pval, h_off, dif_pos]
      simp [csRun, cleanupInstrs, h_pres, emit_nil]
      simp only [h_bval, h_brun, h_bres]
      simp [cleanupInstrs, emit_nil]
    · have h_root : CompilerM.run (ensurePlaceRoot (Place.proj (Place.local dstLoc) g)) cs
          = cs :=
        ensurePlaceRoot_run_eq_of_mapped ⟨dstReg, σ, h_dst⟩
      simp only [csCompile, csMonad, compileRExprToChecked, placeToBorrowRegChecked, h_proj_eq,
        h_root, h_prun, h_pval, h_off, dif_pos]
      simp only [csRun]
      simp only [h_pres]
      simp only [h_bval]
      exact ⟨_, rfl⟩
  · rw [projDstTail_pos _ h_off]
    refine ⟨?_, ?_⟩
    · have h_root : CompilerM.run (ensurePlaceRoot (Place.proj (Place.local dstLoc) g)) cs
          = cs := by
        exact ensurePlaceRoot_run_eq_of_mapped ⟨dstReg, σ, h_dst⟩
      simp only [csCompile, csMonad, compileRExprToChecked, placeToBorrowRegChecked, h_proj_eq,
        h_root, h_prun, h_pval, h_off, dif_neg]
      simp [csRun, cleanupInstrs, h_pres, emit_nil]
      simp only [h_pres, h_bval, h_brun, h_bres]
      simp [csRun, cleanupInstrs, emit_nil, borrowRhs]
      try rfl
    · have h_root : CompilerM.run (ensurePlaceRoot (Place.proj (Place.local dstLoc) g)) cs
          = cs :=
        ensurePlaceRoot_run_eq_of_mapped ⟨dstReg, σ, h_dst⟩
      simp only [csCompile, csMonad, compileRExprToChecked, placeToBorrowRegChecked, h_proj_eq,
        h_root, h_prun, h_pval, h_off, dif_neg]
      simp only [csRun]
      simp only [h_pres]
      simp only [h_bval]
      exact ⟨_, rfl⟩

/-- `derefsrc`: one fragment lemma for both offsets, the destination tail
    stated through `projDstTail`. -/
theorem compileStmt_ref_projdst_derefsrc_lowers
    {Γ : Ctx} {τ σ σb : LayoutTy}
    {dstLoc : Local Γ σ} {g : PathTo σ (obseq.LayoutTy.PtrL τ)}
    {P : Place Γ (obseq.LayoutTy.PtrL σb)} {f : PathTo σb τ}
    {cs : CompilerState} {dstReg : Register}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    {dOut : ResultWithEvidence PtrResult (PlaceToRegEvidence kind (.deref P))}
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = some (dstReg, σ))
    (h_dval : CheckedCompilerM.value (placeToRegChecked kind (.deref P)) cs
      = Except.ok dOut)
    (h_dclean : dOut.result.cleanup = [])
    (h_prm : (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) cs).placeRegMap = cs.placeRegMap) :
    LowersTo
        (compileStmtChecked
          (Stmt.assign (.proj (.local dstLoc) g)
            (.ref kind prot mask (.proj (.deref P) f)))) cs
      (projDstTail (emit { (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) cs) with nextReg := (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) cs).nextReg + 1 }
          [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) cs).nextReg)
            (Rhs.Borrow kind prot mask (blockSize τ) dOut.result.reg (pathOffset f))])
        (pathOffset g) (blockSize (obseq.LayoutTy.PtrL τ)) obseq.TyVal.PTy
        (Register.R (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) cs).nextReg) dstReg) := by
  have h_borrow_eq : placeToBorrowRegChecked (Γ := Γ) kind prot mask
      (.proj (.deref P) f)
      = (do
          let baseOut ← placeToRegChecked kind (.deref P)
          let baseRes := baseOut.result
          let offset := pathOffset f
          let tmpReg ← CheckedCompilerM.lift freshRegM
          let _ ← CheckedCompilerM.lift
            (emitM [Instr.Assgn tmpReg (Rhs.Borrow kind prot mask (blockSize τ) baseRes.reg offset)])
          pure {
            result := { reg := tmpReg,
                        cleanup := baseRes.cleanup ++ [(tmpReg, blockSize τ)] },
            evidence := PlaceToBorrowRegEvidence.proj (.deref P) f baseRes tmpReg
              baseOut.evidence
          }) := by simp only [placeToBorrowRegChecked]
  have h_dst' : getPlaceInfo
      (emit { (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) cs) with nextReg := (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) cs).nextReg + 1 }
        [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) cs).nextReg)
          (Rhs.Borrow kind prot mask (blockSize τ) dOut.result.reg (pathOffset f))])
      dstLoc.idx.1 = some (dstReg, σ) := by
    rw [getPlaceInfo_emit, getPlaceInfo_setNextReg]
    show (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) cs).placeRegMap.lookup dstLoc.idx.1 = _
    rw [h_prm]
    exact h_dst
  obtain ⟨h_brun, baseOut, h_bval, h_bres⟩ :=
    placeToRegChecked_local_existing (kind := RefKind.Mut) h_dst'
  have h_proj_eq := placeToRegChecked_proj_root_eq (Γ := Γ) (kind := RefKind.Mut)
    (base := .local dstLoc) g (fun _ _ _ h => by cases h)
  by_cases h_off : pathOffset g = 0
  · rw [h_off, projDstTail_zero]
    refine ⟨?_, ?_⟩
    · have h_root : CompilerM.run (ensurePlaceRoot (Place.proj (Place.local dstLoc) g)) cs
          = cs := ensurePlaceRoot_run_eq_of_mapped ⟨dstReg, σ, h_dst⟩
      simp only [csCompile, csMonad, compileRExprToChecked, h_borrow_eq, h_proj_eq, h_root, h_dval,
        h_off, dif_pos]
      simp [csRun, cleanupInstrs, h_dclean, emit_nil]
      simp only [h_bval, h_brun, h_bres]
      simp [cleanupInstrs, emit_nil]
    · have h_root : CompilerM.run (ensurePlaceRoot (Place.proj (Place.local dstLoc) g)) cs
          = cs := ensurePlaceRoot_run_eq_of_mapped ⟨dstReg, σ, h_dst⟩
      simp only [csCompile, csMonad, compileRExprToChecked, h_borrow_eq, h_proj_eq, h_root, h_dval,
        h_off, dif_pos]
      simp only [csRun]
      simp only [h_bval]
      exact ⟨_, rfl⟩
  · rw [projDstTail_pos _ h_off]
    refine ⟨?_, ?_⟩
    · have h_root : CompilerM.run (ensurePlaceRoot (Place.proj (Place.local dstLoc) g)) cs
          = cs := ensurePlaceRoot_run_eq_of_mapped ⟨dstReg, σ, h_dst⟩
      simp only [csCompile, csMonad, compileRExprToChecked, h_borrow_eq, h_proj_eq, h_root, h_dval,
        h_off, dif_neg]
      simp [csRun, cleanupInstrs, h_dclean, emit_nil]
      simp only [h_bval, h_brun, h_bres]
      simp [csRun, cleanupInstrs, emit_nil, borrowRhs]
      try rfl
    · have h_root : CompilerM.run (ensurePlaceRoot (Place.proj (Place.local dstLoc) g)) cs
          = cs := ensurePlaceRoot_run_eq_of_mapped ⟨dstReg, σ, h_dst⟩
      simp only [csCompile, csMonad, compileRExprToChecked, h_borrow_eq, h_proj_eq, h_root, h_dval,
        h_off, dif_neg]
      simp only [csRun]
      simp only [h_bval]
      exact ⟨_, rfl⟩

/-- `projsrc`: one fragment lemma for both offsets, the destination tail
    stated through `projDstTail`. -/
theorem compileStmt_ref_projdst_projsrc_lowers
    {Γ : Ctx} {τ σ σb : LayoutTy}
    {dstLoc : Local Γ σ} {g : PathTo σ (obseq.LayoutTy.PtrL τ)}
    {srcLoc : Local Γ σb} {f : PathTo σb τ}
    {cs : CompilerState} {dstReg srcReg : Register}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = some (dstReg, σ))
    (h_src : getPlaceInfo cs srcLoc.idx.1 = some (srcReg, σb)) :
    LowersTo
        (compileStmtChecked
          (Stmt.assign (.proj (.local dstLoc) g)
            (.ref kind prot mask (.proj (.local srcLoc) f)))) cs
      (projDstTail (emit { cs with nextReg := cs.nextReg + 1 }
          [Instr.Assgn (Register.R cs.nextReg)
            (Rhs.Borrow kind prot mask (blockSize τ) srcReg (pathOffset f))])
        (pathOffset g) (blockSize (obseq.LayoutTy.PtrL τ)) obseq.TyVal.PTy
        (Register.R cs.nextReg) dstReg) := by
  obtain ⟨h_prun, placeOut, h_pval, h_pres⟩ :=
    placeToRegChecked_local_existing (kind := kind) h_src
  have h_borrow_eq : placeToBorrowRegChecked (Γ := Γ) kind prot mask
      (.proj (.local srcLoc) f)
      = (do
          let baseOut ← placeToRegChecked kind (.local srcLoc)
          let baseRes := baseOut.result
          let offset := pathOffset f
          let tmpReg ← CheckedCompilerM.lift freshRegM
          let _ ← CheckedCompilerM.lift
            (emitM [Instr.Assgn tmpReg (Rhs.Borrow kind prot mask (blockSize τ) baseRes.reg offset)])
          pure {
            result := { reg := tmpReg,
                        cleanup := baseRes.cleanup ++ [(tmpReg, blockSize τ)] },
            evidence := PlaceToBorrowRegEvidence.proj (.local srcLoc) f baseRes tmpReg
              baseOut.evidence
          }) := by simp only [placeToBorrowRegChecked]
  have h_dst' : getPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 }
      [Instr.Assgn (Register.R cs.nextReg)
        (Rhs.Borrow kind prot mask (blockSize τ) srcReg (pathOffset f))]) dstLoc.idx.1
      = some (dstReg, σ) := by
    rw [getPlaceInfo_emit, getPlaceInfo_setNextReg]
    exact h_dst
  obtain ⟨h_brun, baseOut, h_bval, h_bres⟩ :=
    placeToRegChecked_local_existing (kind := RefKind.Mut) h_dst'
  have h_proj_eq := placeToRegChecked_proj_root_eq (Γ := Γ) (kind := RefKind.Mut)
    (base := .local dstLoc) g (fun _ _ _ h => by cases h)
  by_cases h_off : pathOffset g = 0
  · rw [h_off, projDstTail_zero]
    refine ⟨?_, ?_⟩
    · have h_root : CompilerM.run (ensurePlaceRoot (Place.proj (Place.local dstLoc) g)) cs
          = cs := by
        exact ensurePlaceRoot_run_eq_of_mapped ⟨dstReg, σ, h_dst⟩
      simp only [csCompile, csMonad, compileRExprToChecked, h_borrow_eq, h_proj_eq, h_root, h_prun,
        h_pval, h_off, dif_pos]
      simp [csRun, cleanupInstrs, h_pres, emit_nil]
      simp only [h_bval, h_brun, h_bres]
      simp [cleanupInstrs, emit_nil]
    · have h_root : CompilerM.run (ensurePlaceRoot (Place.proj (Place.local dstLoc) g)) cs
          = cs :=
        ensurePlaceRoot_run_eq_of_mapped ⟨dstReg, σ, h_dst⟩
      simp only [csCompile, csMonad, compileRExprToChecked, h_borrow_eq, h_proj_eq, h_root, h_prun,
        h_pval, h_off, dif_pos]
      simp only [csRun]
      simp only [h_pres]
      simp only [h_bval]
      exact ⟨_, rfl⟩
  · rw [projDstTail_pos _ h_off]
    refine ⟨?_, ?_⟩
    · have h_root : CompilerM.run (ensurePlaceRoot (Place.proj (Place.local dstLoc) g)) cs
          = cs := by
        exact ensurePlaceRoot_run_eq_of_mapped ⟨dstReg, σ, h_dst⟩
      simp only [csCompile, csMonad, compileRExprToChecked, h_borrow_eq, h_proj_eq, h_root, h_prun,
        h_pval, h_off, dif_neg]
      simp [csRun, cleanupInstrs, h_pres, emit_nil]
      simp only [h_pres, h_bval, h_brun, h_bres]
      simp [csRun, cleanupInstrs, emit_nil, borrowRhs]
      try rfl
    · have h_root : CompilerM.run (ensurePlaceRoot (Place.proj (Place.local dstLoc) g)) cs
          = cs :=
        ensurePlaceRoot_run_eq_of_mapped ⟨dstReg, σ, h_dst⟩
      simp only [csCompile, csMonad, compileRExprToChecked, h_borrow_eq, h_proj_eq, h_root, h_prun,
        h_pval, h_off, dif_neg]
      simp only [csRun]
      simp only [h_pres]
      simp only [h_bval]
      exact ⟨_, rfl⟩

/-- Fresh projected destination, local source: `Alloc; Borrow;` then the
    destination tail at the projection's offset — one lemma for both
    offsets, the tail stated through `projDstTail`. -/
theorem compileStmt_ref_proj_fresh_lowers
    {Γ : Ctx} {τ σ : LayoutTy}
    {dstLoc : Local Γ σ} {g : PathTo σ (obseq.LayoutTy.PtrL τ)}
    {srcLoc : Local Γ τ}
    {cs : CompilerState} {srcReg : Register}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = none)
    (h_src : getPlaceInfo cs srcLoc.idx.1 = some (srcReg, τ)) :
    LowersTo
        (compileStmtChecked
          (Stmt.assign (.proj (.local dstLoc) g)
            (.ref kind prot mask (.local srcLoc)))) cs
      (projDstTail (emit
          { (setPlaceInfo
              (emit { cs with nextReg := cs.nextReg + 1 }
                [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
              dstLoc.idx.1 (Register.R cs.nextReg, σ)) with
              nextReg := cs.nextReg + 1 + 1 }
          [Instr.Assgn (Register.R (cs.nextReg + 1))
            (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)])
        (pathOffset g) (blockSize (obseq.LayoutTy.PtrL τ)) obseq.TyVal.PTy
        (Register.R (cs.nextReg + 1)) (Register.R cs.nextReg)) := by
  obtain ⟨h_run, -⟩ := ensureLocalRegE_fresh (loc := dstLoc) h_dst
  have h_proj_eq := placeToRegChecked_proj_root_eq (Γ := Γ) (kind := RefKind.Mut)
    (base := .local dstLoc) g (fun _ _ _ h => by cases h)
  have h_root : CompilerM.run
      (ensurePlaceRoot (Place.proj (Place.local dstLoc) g)) cs = (setPlaceInfo
          (emit { cs with nextReg := cs.nextReg + 1 }
            [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
          dstLoc.idx.1 (Register.R cs.nextReg, σ)) := by
    show CompilerM.run (do let _ ← ensureLocalRegE dstLoc; pure ()) cs = _
    simp [CompilerM.run_bind, CompilerM.run_pure, h_run]
  have h_srcPost : getPlaceInfo
      (setPlaceInfo
        (emit { cs with nextReg := cs.nextReg + 1 }
          [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
        dstLoc.idx.1 (Register.R cs.nextReg, σ))
      srcLoc.idx.1 = some (srcReg, τ) := by
    by_cases h_eq : srcLoc.idx.1 = dstLoc.idx.1
    · exfalso
      grind
    · rw [getPlaceInfo_setPlaceInfo_ne _ h_eq, getPlaceInfo_emit]
      exact h_src
  obtain ⟨h_prun, placeOut, h_pval, h_pres⟩ :=
    placeToRegChecked_local_existing (kind := kind) h_srcPost
  have h_dstPost : getPlaceInfo
      (emit
        { (setPlaceInfo
            (emit { cs with nextReg := cs.nextReg + 1 }
              [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
            dstLoc.idx.1 (Register.R cs.nextReg, σ)) with
            nextReg := cs.nextReg + 1 + 1 }
        [Instr.Assgn (Register.R (cs.nextReg + 1))
          (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)])
      dstLoc.idx.1 = some (Register.R cs.nextReg, σ) := by
    rw [getPlaceInfo_emit, getPlaceInfo_setNextReg]
    exact getPlaceInfo_setPlaceInfo_self _ _ _
  obtain ⟨h_brun, baseOut, h_bval, h_bres⟩ :=
    placeToRegChecked_local_existing (kind := RefKind.Mut) h_dstPost
  by_cases h_off : pathOffset g = 0
  · rw [h_off, projDstTail_zero]
    refine ⟨?_, ?_⟩
    · simp only [csCompile, csMonad, placeToBorrowRegChecked, h_proj_eq, h_root, h_prun, h_pval,
        h_off, dif_pos]
      simp [csRun, cleanupInstrs, h_pres, emit_nil]
      csnorm at h_bval h_brun h_bres ⊢
      simp only [h_bval, h_brun, h_bres]
      simp [emit_nil]
    · simp only [csCompile, csMonad, placeToBorrowRegChecked, h_proj_eq, h_root, h_prun, h_pval,
        h_off, dif_pos]
      simp only [csRun]
      simp only [h_pres]
      csnorm at h_bval ⊢
      simp only [h_bval]
      exact ⟨_, rfl⟩
  · rw [projDstTail_pos _ h_off]
    refine ⟨?_, ?_⟩
    · simp only [csCompile, csMonad, placeToBorrowRegChecked, h_proj_eq, h_root, h_prun, h_pval,
        h_off, dif_neg]
      simp [csRun, cleanupInstrs, h_pres, emit_nil]
      csnorm at h_bval h_brun h_bres ⊢
      simp only [h_pres, h_bval, h_brun, h_bres]
      simp [csRun, cleanupInstrs, emit_nil, borrowRhs]
      rfl
    · simp only [csCompile, csMonad, placeToBorrowRegChecked, h_proj_eq, h_root, h_prun, h_pval,
        h_off, dif_neg]
      simp only [csRun]
      simp only [h_pres]
      csnorm at h_bval ⊢
      simp only [h_bval]
      exact ⟨_, rfl⟩

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

/-- REGIME L→P0 (field destination, ZERO offset), CLOSED 2026-08-29:
    `dst.g := &src` with both roots bound locals and `g` at offset 0 —
    regime L→L with a WIDER destination allocation (the resolved dst
    covers the base's whole block), exactly as C0 widened regime A. The
    fragment is L→L's: `[Borrow; RStore]` through the dst BASE
    register. -/
theorem ref_projdst_local_simulation
    {τ σ : LayoutTy}
    {dstLoc : Local Γ σ} {g : PathTo σ (obseq.LayoutTy.PtrL τ)}
    {srcLoc : Local Γ τ}
    {bD bS : mirlite.Binding}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (compProg : oseair.Prog)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    {stmt0 : Stmt Γ}
    (h_stmt : prog.get? s_mir.pc = some stmt0)
    (h_run0 : ∀ cs, CheckedCompilerM.run (compileStmtChecked stmt0) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.proj (.local dstLoc) g)
              (.ref kind prot mask (.local srcLoc)))) cs)
    (h_val0 : ∀ cs so, CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.proj (.local dstLoc) g)
            (.ref kind prot mask (.local srcLoc)))) cs
        = Except.ok so →
      ∃ so', CheckedCompilerM.value (compileStmtChecked stmt0) cs
        = Except.ok so')
    (h_envD : mirlite.Env.lookup s_mir.env dstLoc = some bD)
    (h_envS : mirlite.Env.lookup s_mir.env srcLoc = some bS)
    (h_step : mirlite.stepStmt MSB s_mir
      (.assign (.proj (.local dstLoc) g)
        (.ref kind prot mask (.local srcLoc))) = .ok s_mir') :
    ∃ (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa ρt' s_mir' s_osea' := by
  obtain ⟨csPrefix, ⟨h_csAt, h_pc⟩, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_tbd,
    h_alloc, h_unmap, h_prb⟩ := h_inv
  obtain ⟨dstReg, baseD, tagD, h_piD, h_entryD, h_raD, h_rtD, h_nwD, h_domD⟩ :=
    h_lbs dstLoc bD h_envD
  obtain ⟨srcReg, baseS, tagS, h_piS, h_entryS, h_raS, h_rtS, h_nwS, h_domS⟩ :=
    h_lbs srcLoc bS h_envS
  have h_baseD : baseD = bD.addr := (h_id_a _ _ h_raD).symm
  have h_baseS : baseS = bS.addr := (h_id_a _ _ h_raS).symm
  subst h_baseD
  subst h_baseS
  -- §1 invert the source: prepare no-op, dst resolves at the FIELD (offset
  -- 0), the retag succeeds, the pointer is written into the base block
  simp only [mirPrep, mirlite.stepStmt, mirlite.doAssign, mirlite.doAssignCont, h_envD,
    mirlite.resolvePlaceAcc, h_envS, mirlite.evalRExpr] at h_step
  rw [if_neg (Nat.lt_irrefl (bS.addr + blockSize τ))] at h_step
  cases h_ref_src : MSB.ref s_mir.perms bS.addr (blockSize τ) bS.tag kind prot mask with
  | error e => rw [h_ref_src] at h_step; simp at h_step
  | ok pr =>
      obtain ⟨perms', freshTag⟩ := pr
      rw [h_ref_src] at h_step
      simp only at h_step
      -- §2 the retag on the target, with ρt extended at the fresh pair
      -- §3 the fragment and its two instructions
      have h_stmtRunC := (compileStmt_ref_projdst_local_lowers (cs := csPrefix) (g := g)
        kind prot mask h_piD h_piS).run
      have h_stmtRun := (h_run0 csPrefix).trans h_stmtRunC
      obtain ⟨stmtOutC, h_stmtOutC⟩ :=
        (compileStmt_ref_projdst_local_lowers (cs := csPrefix) (g := g) kind prot mask
          h_piD h_piS).value
      obtain ⟨stmtOut, h_stmtOut⟩ := h_val0 csPrefix stmtOutC h_stmtOutC
      have hFrag4 := ((CodeIncluded.of_stmt h_comp h_csAt h_stmt h_stmtOut).mono
        (by rw [h_stmtRun]; exact projDstTail_state_incr _ _ _ _ _ _)).fragmentOf
        rfl h_pc
      have h_code1 : compProg s_osea.pc
          = some (Instr.Assgn (Register.R csPrefix.nextReg)
              (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)) :=
        hFrag4.instrAt 0 rfl rfl
      -- §4 execute the Borrow
      -- §4 the SOURCE package: the retag transported, the `Borrow` executed
      obtain ⟨tgtPerms, rfl, h_incr_t, h_wf_t', h_tbd', h_psim', h_run1, h_lbsB,
        h_pcB, h_relB⟩ :=
        ref_local_borrow τ τ kind prot mask 0 compProg s_mir s_osea csPrefix
          h_id_a h_wf_t h_tbd h_lbs h_prb h_psim h_pc h_entryS h_raS h_rtS h_nwS
          h_domS (by simp) (by simpa using h_ref_src) h_code1
      have h_rtD' : (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag) bD.tag
          = some tagD := h_incr_t _ _ h_rtD
      -- §5-§6 the BOUND-root PLAIN write seam: at zero offset the store goes
      -- straight through the destination's own register
      simp only [h_envD] at h_step
      have h_regne : dstReg ≠ Register.R csPrefix.nextReg := by
        cases dstReg with
        | R n =>
            have h_lt := h_prb _ _ _ h_piD
            grind
      obtain ⟨s_osea', n, h_run, h_inv'⟩ :=
        copy_bound_write_after_read (τ := obseq.LayoutTy.PtrL τ)
          (dbase := bD.addr) (dtag := bD.tag) (dsize := blockSize σ)
          (csR := (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
            [Instr.Assgn (Register.R csPrefix.nextReg)
              (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)]))
          (sR := { s_osea with
            perms := tgtPerms,
            reg := oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
              (obseq.TyVal.PTy, [Val.Ptr bS.addr (0 + 0) (blockSize τ)
                s_osea.perms.NextTag]),
            pc := s_osea.pc + 1 })
          (vreg := Register.R csPrefix.nextReg)
          (vals := [Val.Ptr bS.addr (0 + 0) (blockSize τ) s_osea.perms.NextTag])
          (mvals := [mirlite.MemValue.ptrVal bS.addr (bS.addr - bS.addr) (blockSize τ)
            s_mir.perms.NextTag])
          compProg h_comp h_stmt h_csAt h_stmtOut h_id_a h_wf_t' h_unmap h_prb
          0 h_raD h_rtD' h_nwD h_domD (pathOffset g)
          (by simpa using PathTo.offset_add_size_le g) h_run1
          (by
            show oseair.RegMap.lookup _ _ = _
            rw [RegMap.lookup_insert_ne _ h_regne]
            exact h_entryD)
          (SourceMemSim.rename_mono (AddrRenameIncr.refl ρa) h_incr_t h_sms)
          h_alloc rfl (by simp only [emit]; exact Nat.le_succ _) h_lbsB h_psim'
          h_tbd' h_pcB (RegMap.lookup_insert_self _ _ _)
          (by show _ < _; simp only [emit]; exact Nat.lt_succ_self _)
          (by simp [blockSize, obseq.layoutSize])
          h_stmtRun
          (by simp [blockSize, obseq.layoutSize]) (by simp) rfl rfl rfl h_relB h_step
      exact ⟨_, s_osea', n, h_incr_t, h_run, h_inv'⟩
/-! ## The deref-dst fragments (MIR order: Borrow first, then the dst)

`*P := &src` lowers, under the d34 MIR order, to the rhs `Borrow`
FIRST, then the WHOLE dst lowering (owned opaquely by
`ptrChain_lowering_sim`), then the `RStore` of the borrow through the
loaded register. The borrow temp `R cs.nextReg` crosses the dst
lowering via the mother lemma's register-frame conjunct. -/

/-- Reduce a local's access-resolution without unfolding
    `resolvePlaceAcc` elsewhere in the term (keeps sibling `.deref`
    applications OPAQUE for the mother lemma). -/
theorem resolvePlaceAcc_local
    {Γ : Ctx} {τ : LayoutTy} {M : PermissionModel}
    {s : mirlite.State M Γ} {loc : Local Γ τ} {b : mirlite.Binding}
    (h : mirlite.Env.lookup s.env loc = some b) :
    mirlite.resolvePlaceAcc M s (.local loc)
      = .ok ({ addr := b.addr, tag := b.tag,
               allocBase := b.addr, allocSize := blockSize τ }, s.perms) := by
  simp [mirlite.resolvePlaceAcc, h]

theorem compileStmt_ref_derefdst_run
    {Γ : Ctx} {τ : LayoutTy}
    {P : Place Γ (obseq.LayoutTy.PtrL (obseq.LayoutTy.PtrL τ))} {srcLoc : Local Γ τ}
    {cs cs1 : CompilerState} {srcReg : Register}
    {dOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Mut (.deref P))}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (h_root : CompilerM.run (ensurePlaceRoot (Place.deref P)) cs = cs)
    (h_src : getPlaceInfo cs srcLoc.idx.1 = some (srcReg, τ))
    (h_cs1 : cs1 = emit { cs with nextReg := cs.nextReg + 1 }
      [Instr.Assgn (Register.R cs.nextReg)
        (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)])
    (h_dval : CheckedCompilerM.value (placeToRegChecked RefKind.Mut (.deref P)) cs1
      = Except.ok dOut)
    (h_dclean : dOut.result.cleanup = []) :
    CheckedCompilerM.run
        (compileStmtChecked
          (Stmt.assign (.deref P) (.ref kind prot mask (.local srcLoc)))) cs
      = emit (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (.deref P)) cs1)
          [Instr.RStore obseq.TyVal.PTy (Register.R cs.nextReg) dOut.result.reg] := by
  obtain ⟨h_prun, placeOut, h_pval0, h_pres⟩ :=
    placeToRegChecked_local_existing (kind := kind) h_src
  subst h_cs1
  simp [csCompile, placeToBorrowRegChecked, h_root, h_prun, h_pval0, h_pres, h_dval]
  simp [csRun, cleanupInstrs, h_dval, h_dclean, emit_nil]

/-- The deref-dst statement lowers. -/
theorem compileStmt_ref_derefdst_value
    {Γ : Ctx} {τ : LayoutTy}
    {P : Place Γ (obseq.LayoutTy.PtrL (obseq.LayoutTy.PtrL τ))} {srcLoc : Local Γ τ}
    {cs cs1 : CompilerState} {srcReg : Register}
    {dOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Mut (.deref P))}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (h_root : CompilerM.run (ensurePlaceRoot (Place.deref P)) cs = cs)
    (h_src : getPlaceInfo cs srcLoc.idx.1 = some (srcReg, τ))
    (h_cs1 : cs1 = emit { cs with nextReg := cs.nextReg + 1 }
      [Instr.Assgn (Register.R cs.nextReg)
        (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)])
    (h_dval : CheckedCompilerM.value (placeToRegChecked RefKind.Mut (.deref P)) cs1
      = Except.ok dOut) :
    ∃ so, CheckedCompilerM.value
      (compileStmtChecked
        (Stmt.assign (.deref P) (.ref kind prot mask (.local srcLoc)))) cs
      = Except.ok so := by
  obtain ⟨h_prun, placeOut, h_pval0, h_pres⟩ :=
    placeToRegChecked_local_existing (kind := kind) h_src
  subst h_cs1
  simp only [csCompile, csMonad, placeToBorrowRegChecked, h_root, h_prun, h_pval0, h_pres]
  simp only [csRun]
  simp only [csMonad, h_dval]
  exact ⟨_, rfl⟩

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

theorem compileStmt_assign_projderefdst_flatten_run
    {Γ : Ctx} {τ σ : LayoutTy}
    {pp : Place Γ (obseq.LayoutTy.PtrL σ)}
    {g : PathTo σ (obseq.LayoutTy.PtrL τ)}
    (rhs : RExpr Γ (obseq.LayoutTy.PtrL τ)) (cs : CompilerState) :
    CheckedCompilerM.run
        (compileStmtChecked
          (Stmt.assign (.proj (Place.deref pp) g) rhs)) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.proj (Place.deref (flattenPlace pp)) g)
              rhs)) cs := by
  have h_er : ensurePlaceRoot (Place.proj (Place.deref (flattenPlace pp)) g)
      = ensurePlaceRoot (Place.proj (Place.deref pp) g) :=
    ensurePlaceRoot_flatten (Place.proj (Place.deref pp) g)
  simp only [csMonad, compileStmtChecked, h_er]
  cases hP : CheckedCompilerM.value
      (compileRExprPreChecked rhs) (CompilerM.run (ensurePlaceRoot (Place.proj (Place.deref pp) g)) cs) with
  | error eP => simp only [hP]
  | ok oP =>
      simp only [hP]
      obtain ⟨h_agr, h_agv⟩ := placeToRegChecked_flatten_agree (Place.proj (Place.deref pp) g)
        RefKind.Mut (CheckedCompilerM.run (compileRExprPreChecked rhs) (CompilerM.run (ensurePlaceRoot (Place.proj (Place.deref pp) g)) cs))
      rw [show flattenPlace (Place.proj (Place.deref pp) g)
        = Place.proj (Place.deref (flattenPlace pp)) g from rfl] at h_agr h_agv
      cases hF : CheckedCompilerM.value
          (placeToRegChecked RefKind.Mut (Place.proj (Place.deref (flattenPlace pp)) g))
          (CheckedCompilerM.run (compileRExprPreChecked rhs) (CompilerM.run (ensurePlaceRoot (Place.proj (Place.deref pp) g)) cs)) with
      | error eF =>
          cases hO : CheckedCompilerM.value
              (placeToRegChecked RefKind.Mut (Place.proj (Place.deref pp) g))
              (CheckedCompilerM.run (compileRExprPreChecked rhs) (CompilerM.run (ensurePlaceRoot (Place.proj (Place.deref pp) g)) cs)) with
          | error eO =>
              simp only [hF, hO]
              exact h_agr.symm
          | ok oO =>
              exfalso
              rw [hF, hO] at h_agv
              simp [Except.map] at h_agv
      | ok oF =>
          cases hO : CheckedCompilerM.value
              (placeToRegChecked RefKind.Mut (Place.proj (Place.deref pp) g))
              (CheckedCompilerM.run (compileRExprPreChecked rhs) (CompilerM.run (ensurePlaceRoot (Place.proj (Place.deref pp) g)) cs)) with
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

theorem compileStmt_assign_projderefdst_flatten_value
    {Γ : Ctx} {τ σ : LayoutTy}
    {pp : Place Γ (obseq.LayoutTy.PtrL σ)}
    {g : PathTo σ (obseq.LayoutTy.PtrL τ)}
    (rhs : RExpr Γ (obseq.LayoutTy.PtrL τ)) (cs : CompilerState) :
    ∀ so, CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.proj (Place.deref (flattenPlace pp)) g)
            rhs)) cs
      = Except.ok so →
    ∃ so', CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.proj (Place.deref pp) g) rhs)) cs
      = Except.ok so' := by
  intro so h_so
  have h_er : ensurePlaceRoot (Place.proj (Place.deref (flattenPlace pp)) g)
      = ensurePlaceRoot (Place.proj (Place.deref pp) g) :=
    ensurePlaceRoot_flatten (Place.proj (Place.deref pp) g)
  simp only [csMonad, compileStmtChecked, h_er] at h_so ⊢
  cases hP : CheckedCompilerM.value
      (compileRExprPreChecked rhs) (CompilerM.run (ensurePlaceRoot (Place.proj (Place.deref pp) g)) cs) with
  | error eP =>
      exfalso
      rw [hP] at h_so
      simp at h_so
  | ok oP =>
      rw [hP] at h_so
      simp only [hP]
      obtain ⟨h_agr, h_agv⟩ := placeToRegChecked_flatten_agree (Place.proj (Place.deref pp) g)
        RefKind.Mut (CheckedCompilerM.run (compileRExprPreChecked rhs) (CompilerM.run (ensurePlaceRoot (Place.proj (Place.deref pp) g)) cs))
      rw [show flattenPlace (Place.proj (Place.deref pp) g)
        = Place.proj (Place.deref (flattenPlace pp)) g from rfl] at h_agr h_agv
      cases hO : CheckedCompilerM.value
          (placeToRegChecked RefKind.Mut (Place.proj (Place.deref pp) g))
          (CheckedCompilerM.run (compileRExprPreChecked rhs) (CompilerM.run (ensurePlaceRoot (Place.proj (Place.deref pp) g)) cs)) with
      | error eO =>
          exfalso
          cases hF : CheckedCompilerM.value
              (placeToRegChecked RefKind.Mut (Place.proj (Place.deref (flattenPlace pp)) g))
              (CheckedCompilerM.run (compileRExprPreChecked rhs) (CompilerM.run (ensurePlaceRoot (Place.proj (Place.deref pp) g)) cs)) with
          | error eF =>
              rw [hF] at h_so
              simp at h_so
          | ok oF =>
              rw [hF, hO] at h_agv
              simp [Except.map] at h_agv
      | ok oO =>
          simp only [hO]
          exact ⟨_, rfl⟩


/-! ## A PROJ-TOPPED source over a DEREF base, into a bound local:
    `dst := &kind (*p).f`. `placeToRegChecked`'s deref arm ignores its
    `kind` (it lowers the pointer place at `Shared` and `Load`s), so the
    base lowering is the same chain code the plain deref source emits —
    only the `Borrow`'s offset operand differs, which is why the mother
    lemma can be invoked at `kind` and consumed unchanged. -/

theorem compileStmt_ref_derefprojsrc_lowers
    {Γ : Ctx} {τ σb : LayoutTy}
    {dstLoc : Local Γ (obseq.LayoutTy.PtrL τ)}
    {P : Place Γ (obseq.LayoutTy.PtrL σb)} {f : PathTo σb τ}
    {cs : CompilerState} {dstReg : Register}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    {dOut : ResultWithEvidence PtrResult (PlaceToRegEvidence kind (.deref P))}
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = some (dstReg, obseq.LayoutTy.PtrL τ))
    (h_dval : CheckedCompilerM.value (placeToRegChecked kind (.deref P)) cs
      = Except.ok dOut) :
    LowersTo
        (compileStmtChecked
          (Stmt.assign (.local dstLoc) (.ref kind prot mask (.proj (.deref P) f)))) cs
      (emit (emit
          { (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) cs) with
              nextReg :=
                (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) cs).nextReg + 1 }
          [Instr.Assgn
            (Register.R
              (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) cs).nextReg)
            (Rhs.Borrow kind prot mask (blockSize τ) dOut.result.reg (pathOffset f))])
          [Instr.RStore obseq.TyVal.PTy
            (Register.R
              (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) cs).nextReg)
            dstReg]) := by
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_existing h_dst
  refine ⟨?_, ?_⟩
  · have h_bindB : placeToBorrowRegChecked (Γ := Γ) kind prot mask (.proj (.deref P) f)
        = (do
            let baseOut ← placeToRegChecked kind (.deref P)
            let baseRes := baseOut.result
            let offset := pathOffset f
            let tmpReg ← CheckedCompilerM.lift freshRegM
            let _ ← CheckedCompilerM.lift
              (emitM [Instr.Assgn tmpReg (Rhs.Borrow kind prot mask (blockSize τ) baseRes.reg offset)])
            pure {
              result := { reg := tmpReg,
                          cleanup := baseRes.cleanup ++ [(tmpReg, blockSize τ)] },
              evidence := PlaceToBorrowRegEvidence.proj (.deref P) f baseRes tmpReg
                baseOut.evidence
            }) := by simp only [placeToBorrowRegChecked]
    simp [csCompile, compileRExprToChecked, h_bindB, h_run, h_val, h_dval]
    simp [csRun, cleanupInstrs, emit_nil]
  · have h_bindB : placeToBorrowRegChecked (Γ := Γ) kind prot mask (.proj (.deref P) f)
        = (do
            let baseOut ← placeToRegChecked kind (.deref P)
            let baseRes := baseOut.result
            let offset := pathOffset f
            let tmpReg ← CheckedCompilerM.lift freshRegM
            let _ ← CheckedCompilerM.lift
              (emitM [Instr.Assgn tmpReg (Rhs.Borrow kind prot mask (blockSize τ) baseRes.reg offset)])
            pure {
              result := { reg := tmpReg,
                          cleanup := baseRes.cleanup ++ [(tmpReg, blockSize τ)] },
              evidence := PlaceToBorrowRegEvidence.proj (.deref P) f baseRes tmpReg
                baseOut.evidence
            }) := by simp only [placeToBorrowRegChecked]
    simp only [csCompile, csMonad, compileRExprToChecked, h_bindB, h_run, h_dval]
    exact ⟨_, rfl⟩
/-! ## A PROJ-TOPPED source over a DEREF base, into a FRESH local. -/

theorem compileStmt_ref_fresh_derefprojsrc_lowers
    {Γ : Ctx} {τ σb : LayoutTy}
    {dstLoc : Local Γ (obseq.LayoutTy.PtrL τ)}
    {P : Place Γ (obseq.LayoutTy.PtrL σb)} {f : PathTo σb τ}
    {cs : CompilerState}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    {dOut : ResultWithEvidence PtrResult (PlaceToRegEvidence kind (.deref P))}
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = none)
    (h_dval : CheckedCompilerM.value (placeToRegChecked kind (.deref P))
        (setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 } [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))]) dstLoc.idx.1 (Register.R cs.nextReg, obseq.LayoutTy.PtrL τ))
      = Except.ok dOut) :
    LowersTo
        (compileStmtChecked
          (Stmt.assign (.local dstLoc) (.ref kind prot mask (.proj (.deref P) f)))) cs
      (emit (emit { (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) (setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 } [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))]) dstLoc.idx.1 (Register.R cs.nextReg, obseq.LayoutTy.PtrL τ))) with nextReg := (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) (setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 } [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))]) dstLoc.idx.1 (Register.R cs.nextReg, obseq.LayoutTy.PtrL τ))).nextReg + 1 }
          [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) (setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 } [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))]) dstLoc.idx.1 (Register.R cs.nextReg, obseq.LayoutTy.PtrL τ))).nextReg)
            (Rhs.Borrow kind prot mask (blockSize τ) dOut.result.reg (pathOffset f))])
          [Instr.RStore obseq.TyVal.PTy
            (Register.R (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) (setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 } [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))]) dstLoc.idx.1 (Register.R cs.nextReg, obseq.LayoutTy.PtrL τ))).nextReg) (Register.R cs.nextReg)]) := by
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_fresh (loc := dstLoc) h_dst
  refine ⟨?_, ?_⟩
  · have h_bindB : placeToBorrowRegChecked (Γ := Γ) kind prot mask (.proj (.deref P) f)
        = (do
            let baseOut ← placeToRegChecked kind (.deref P)
            let baseRes := baseOut.result
            let offset := pathOffset f
            let tmpReg ← CheckedCompilerM.lift freshRegM
            let _ ← CheckedCompilerM.lift
              (emitM [Instr.Assgn tmpReg (Rhs.Borrow kind prot mask (blockSize τ) baseRes.reg offset)])
            pure {
              result := { reg := tmpReg,
                          cleanup := baseRes.cleanup ++ [(tmpReg, blockSize τ)] },
              evidence := PlaceToBorrowRegEvidence.proj (.deref P) f baseRes tmpReg
                baseOut.evidence
            }) := by simp only [placeToBorrowRegChecked]
    simp [csCompile, compileRExprToChecked, h_bindB, h_run, h_val, h_dval]
    simp [csRun, cleanupInstrs, emit_nil, setPlaceInfo]
  · have h_bindB : placeToBorrowRegChecked (Γ := Γ) kind prot mask (.proj (.deref P) f)
        = (do
            let baseOut ← placeToRegChecked kind (.deref P)
            let baseRes := baseOut.result
            let offset := pathOffset f
            let tmpReg ← CheckedCompilerM.lift freshRegM
            let _ ← CheckedCompilerM.lift
              (emitM [Instr.Assgn tmpReg (Rhs.Borrow kind prot mask (blockSize τ) baseRes.reg offset)])
            pure {
              result := { reg := tmpReg,
                          cleanup := baseRes.cleanup ++ [(tmpReg, blockSize τ)] },
              evidence := PlaceToBorrowRegEvidence.proj (.deref P) f baseRes tmpReg
                baseOut.evidence
            }) := by simp only [placeToBorrowRegChecked]
    simp only [csCompile, csMonad, compileRExprToChecked, h_bindB, h_run, h_dval]
    exact ⟨_, rfl⟩
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

/-- Flattening does not distinguish the two spellings of a nested
    projection source: both sides fuse to the same path. -/
theorem flattenPlace_srcproj_assoc {Γ : Ctx} {σ1 σ2 τ : LayoutTy}
    (b : Place Γ σ1) (q : PathTo σ1 σ2) (f : PathTo σ2 τ) :
    flattenPlace (Place.proj (Place.proj b q) f)
      = flattenPlace (Place.proj b (q.append f)) := by
  show projInto (projInto (flattenPlace b) q) f
    = projInto (flattenPlace b) (q.append f)
  exact projInto_projInto _ q f

/-- The compiler's own reassociating arm, as an agreement statement. -/
theorem placeToBorrowRegChecked_projassoc_agree {Γ : Ctx} {σ1 σ2 τ : LayoutTy}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (b : Place Γ σ1) (q : PathTo σ1 σ2) (f : PathTo σ2 τ) (cs : CompilerState) :
    CheckedCompilerM.run
        (placeToBorrowRegChecked kind prot mask (Place.proj (Place.proj b q) f)) cs
      = CheckedCompilerM.run
          (placeToBorrowRegChecked kind prot mask (Place.proj b (q.append f))) cs ∧
    (CheckedCompilerM.value
        (placeToBorrowRegChecked kind prot mask (Place.proj (Place.proj b q) f)) cs).map
        (fun o => o.result)
      = (CheckedCompilerM.value
          (placeToBorrowRegChecked kind prot mask (Place.proj b (q.append f))) cs).map
        (fun o => o.result) := by
  constructor
  · show CheckedCompilerM.run
      (placeToBorrowRegChecked kind prot mask (Place.proj (Place.proj b q) f)) cs = _
    simp only [placeToBorrowRegChecked, CheckedCompilerM.run_bind,
      CheckedCompilerM.value_bind, CheckedCompilerM.run_pure,
      CheckedCompilerM.value_pure]
    split <;> rfl
  · show (CheckedCompilerM.value
      (placeToBorrowRegChecked kind prot mask (Place.proj (Place.proj b q) f)) cs).map _ = _
    simp only [placeToBorrowRegChecked, CheckedCompilerM.run_bind,
      CheckedCompilerM.value_bind, CheckedCompilerM.run_pure,
      CheckedCompilerM.value_pure]
    cases h : CheckedCompilerM.value
        (placeToBorrowRegChecked kind prot mask (Place.proj b (q.append f))) cs <;>
      simp [Except.map]

/-- The mirlite step reassociates a nested projection SOURCE, the
    source-side mirror of `stepStmt_assign_proj_assoc`. -/
theorem stepStmt_assign_refsrc_projassoc
    {Γ : Ctx} {σ1 σ2 τ : LayoutTy} {M : PermissionModel}
    (s : mirlite.State M Γ) (dst : Place Γ (obseq.LayoutTy.PtrL τ))
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (b : Place Γ σ1) (q : PathTo σ1 σ2) (f : PathTo σ2 τ) :
    mirlite.stepStmt M s (.assign dst (.ref kind prot mask (.proj (.proj b q) f)))
      = mirlite.stepStmt M s
          (.assign dst (.ref kind prot mask (.proj b (q.append f)))) := by
  rw [stepStmt_assign_refsrc_anyflatten s dst kind prot mask
        (Place.proj (Place.proj b q) f),
      stepStmt_assign_refsrc_anyflatten s dst kind prot mask
        (Place.proj b (q.append f)),
      flattenPlace_srcproj_assoc]

theorem compileStmt_ref_srcproj_assoc_local_run
    {Γ : Ctx} {σ1 σ2 τ : LayoutTy}
    {dstLoc : Local Γ (obseq.LayoutTy.PtrL τ)}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (b : Place Γ σ1) (q : PathTo σ1 σ2) (f : PathTo σ2 τ) (cs : CompilerState) :
    CheckedCompilerM.run
        (compileStmtChecked
          (Stmt.assign (.local dstLoc)
            (.ref kind prot mask (.proj (.proj b q) f)))) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.local dstLoc)
              (.ref kind prot mask (.proj b (q.append f))))) cs :=
  compileStmt_ref_src_congr_local_run (dstLoc := dstLoc) kind prot mask _ _ cs
    (placeToBorrowRegChecked_projassoc_agree kind prot mask b q f _).1
    (placeToBorrowRegChecked_projassoc_agree kind prot mask b q f _).2

theorem compileStmt_ref_srcproj_assoc_local_value
    {Γ : Ctx} {σ1 σ2 τ : LayoutTy}
    {dstLoc : Local Γ (obseq.LayoutTy.PtrL τ)}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (b : Place Γ σ1) (q : PathTo σ1 σ2) (f : PathTo σ2 τ) (cs : CompilerState) :
    ∀ so, CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.local dstLoc)
            (.ref kind prot mask (.proj b (q.append f))))) cs
      = Except.ok so →
    ∃ so', CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.local dstLoc)
            (.ref kind prot mask (.proj (.proj b q) f)))) cs
      = Except.ok so' :=
  compileStmt_ref_src_congr_local_value (dstLoc := dstLoc) kind prot mask _ _ cs
    (placeToBorrowRegChecked_projassoc_agree kind prot mask b q f _).2

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

theorem compileStmt_ref_srcproj_assoc_deref_run
    {Γ : Ctx} {σ1 σ2 τ : LayoutTy}
    {P : Place Γ (obseq.LayoutTy.PtrL (obseq.LayoutTy.PtrL τ))}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (b : Place Γ σ1) (q : PathTo σ1 σ2) (f : PathTo σ2 τ) (cs : CompilerState) :
    CheckedCompilerM.run
        (compileStmtChecked
          (Stmt.assign (.deref P) (.ref kind prot mask (.proj (.proj b q) f)))) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.deref P)
              (.ref kind prot mask (.proj b (q.append f))))) cs :=
  compileStmt_ref_src_congr_deref_run (P := P) kind prot mask _ _ cs
    (placeToBorrowRegChecked_projassoc_agree kind prot mask b q f _).1
    (placeToBorrowRegChecked_projassoc_agree kind prot mask b q f _).2

theorem compileStmt_ref_srcproj_assoc_deref_value
    {Γ : Ctx} {σ1 σ2 τ : LayoutTy}
    {P : Place Γ (obseq.LayoutTy.PtrL (obseq.LayoutTy.PtrL τ))}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (b : Place Γ σ1) (q : PathTo σ1 σ2) (f : PathTo σ2 τ) (cs : CompilerState) :
    ∀ so, CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.deref P)
            (.ref kind prot mask (.proj b (q.append f))))) cs
      = Except.ok so →
    ∃ so', CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.deref P) (.ref kind prot mask (.proj (.proj b q) f)))) cs
      = Except.ok so' :=
  compileStmt_ref_src_congr_deref_value (P := P) kind prot mask _ _ cs
    (placeToBorrowRegChecked_projassoc_agree kind prot mask b q f _).1
    (placeToBorrowRegChecked_projassoc_agree kind prot mask b q f _).2

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

/-- The NIL-projection eta for a DEREF destination. -/
theorem compileStmt_ref_srcnil_deref_run
    {Γ : Ctx} {τ : LayoutTy}
    {D : Place Γ (obseq.LayoutTy.PtrL (obseq.LayoutTy.PtrL τ))}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (P : Place Γ (obseq.LayoutTy.PtrL τ)) (cs : CompilerState) :
    CheckedCompilerM.run
        (compileStmtChecked
          (Stmt.assign (.deref D) (.ref kind prot mask (.deref P)))) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.deref D)
              (.ref kind prot mask (.proj (.deref P) PathTo.nil)))) cs :=
  compileStmt_ref_src_congr_deref_run (P := D) kind prot mask _ _ cs
    (placeToBorrowRegChecked_nil_agree kind prot mask P _).1.symm
    (placeToBorrowRegChecked_nil_agree kind prot mask P _).2.symm

theorem compileStmt_ref_srcnil_deref_value
    {Γ : Ctx} {τ : LayoutTy}
    {D : Place Γ (obseq.LayoutTy.PtrL (obseq.LayoutTy.PtrL τ))}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (P : Place Γ (obseq.LayoutTy.PtrL τ)) (cs : CompilerState) :
    ∀ so, CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.deref D)
            (.ref kind prot mask (.proj (.deref P) PathTo.nil)))) cs
      = Except.ok so →
    ∃ so', CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.deref D) (.ref kind prot mask (.deref P)))) cs
      = Except.ok so' :=
  compileStmt_ref_src_congr_deref_value (P := D) kind prot mask _ _ cs
    (placeToBorrowRegChecked_nil_agree kind prot mask P _).1.symm
    (placeToBorrowRegChecked_nil_agree kind prot mask P _).2.symm

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

/-- The NIL-projection eta for a PROJECTED destination: `&kind *P` and
    `&kind (*P).nil` compile to the same code, so a plain deref source
    can be handed to the `.proj (.deref _) _` leaves. -/
theorem compileStmt_ref_srcnil_proj_run
    {Γ : Ctx} {τ σ : LayoutTy}
    {dbase : Place Γ σ} {g : PathTo σ (obseq.LayoutTy.PtrL τ)}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (P : Place Γ (obseq.LayoutTy.PtrL τ)) (cs : CompilerState) :
    CheckedCompilerM.run
        (compileStmtChecked
          (Stmt.assign (.proj dbase g) (.ref kind prot mask (.deref P)))) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.proj dbase g)
              (.ref kind prot mask (.proj (.deref P) PathTo.nil)))) cs :=
  compileStmt_ref_src_congr_proj_run (dbase := dbase) (g := g) kind prot mask _ _ cs
    (placeToBorrowRegChecked_nil_agree kind prot mask P _).1.symm
    (placeToBorrowRegChecked_nil_agree kind prot mask P _).2.symm

theorem compileStmt_ref_srcnil_proj_value
    {Γ : Ctx} {τ σ : LayoutTy}
    {dbase : Place Γ σ} {g : PathTo σ (obseq.LayoutTy.PtrL τ)}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (P : Place Γ (obseq.LayoutTy.PtrL τ)) (cs : CompilerState) :
    ∀ so, CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.proj dbase g)
            (.ref kind prot mask (.proj (.deref P) PathTo.nil)))) cs
      = Except.ok so →
    ∃ so', CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.proj dbase g) (.ref kind prot mask (.deref P)))) cs
      = Except.ok so' :=
  compileStmt_ref_src_congr_proj_value (dbase := dbase) (g := g) kind prot mask _ _ cs
    (placeToBorrowRegChecked_nil_agree kind prot mask P _).1.symm
    (placeToBorrowRegChecked_nil_agree kind prot mask P _).2.symm

/-- The NIL-projection eta for a PROJECTED destination and ANY chain
    source base, the general form the last residual site needs. -/
theorem compileStmt_ref_srcnilchain_proj_run
    {Γ : Ctx} {τ σ : LayoutTy}
    {dbase : Place Γ σ} {g : PathTo σ (obseq.LayoutTy.PtrL τ)}
    {b : Place Γ τ}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (h_chain : PtrChain b) (cs : CompilerState) :
    CheckedCompilerM.run
        (compileStmtChecked (Stmt.assign (.proj dbase g) (.ref kind prot mask b))) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.proj dbase g)
              (.ref kind prot mask (.proj b PathTo.nil)))) cs :=
  compileStmt_ref_src_congr_proj_run (dbase := dbase) (g := g) kind prot mask _ _ cs
    (placeToBorrowRegChecked_nil_agree_chain h_chain kind prot mask _).1.symm
    (placeToBorrowRegChecked_nil_agree_chain h_chain kind prot mask _).2.symm

theorem compileStmt_ref_srcnilchain_proj_value
    {Γ : Ctx} {τ σ : LayoutTy}
    {dbase : Place Γ σ} {g : PathTo σ (obseq.LayoutTy.PtrL τ)}
    {b : Place Γ τ}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (h_chain : PtrChain b) (cs : CompilerState) :
    ∀ so, CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.proj dbase g)
            (.ref kind prot mask (.proj b PathTo.nil)))) cs
      = Except.ok so →
    ∃ so', CheckedCompilerM.value
        (compileStmtChecked (Stmt.assign (.proj dbase g) (.ref kind prot mask b))) cs
      = Except.ok so' :=
  compileStmt_ref_src_congr_proj_value (dbase := dbase) (g := g) kind prot mask _ _ cs
    (placeToBorrowRegChecked_nil_agree_chain h_chain kind prot mask _).1.symm
    (placeToBorrowRegChecked_nil_agree_chain h_chain kind prot mask _).2.symm

theorem compileStmt_ref_srcproj_assoc_proj_run
    {Γ : Ctx} {σ1 σ2 τ : LayoutTy}
    {σ : LayoutTy} {dbase : Place Γ σ} {g : PathTo σ (obseq.LayoutTy.PtrL τ)}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (b : Place Γ σ1) (q : PathTo σ1 σ2) (f : PathTo σ2 τ) (cs : CompilerState) :
    CheckedCompilerM.run
        (compileStmtChecked
          (Stmt.assign (.proj dbase g) (.ref kind prot mask (.proj (.proj b q) f)))) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.proj dbase g)
              (.ref kind prot mask (.proj b (q.append f))))) cs :=
  compileStmt_ref_src_congr_proj_run (dbase := dbase) (g := g) kind prot mask _ _ cs
    (placeToBorrowRegChecked_projassoc_agree kind prot mask b q f _).1
    (placeToBorrowRegChecked_projassoc_agree kind prot mask b q f _).2

theorem compileStmt_ref_srcproj_assoc_proj_value
    {Γ : Ctx} {σ1 σ2 τ : LayoutTy}
    {σ : LayoutTy} {dbase : Place Γ σ} {g : PathTo σ (obseq.LayoutTy.PtrL τ)}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (b : Place Γ σ1) (q : PathTo σ1 σ2) (f : PathTo σ2 τ) (cs : CompilerState) :
    ∀ so, CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.proj dbase g)
            (.ref kind prot mask (.proj b (q.append f))))) cs
      = Except.ok so →
    ∃ so', CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.proj dbase g) (.ref kind prot mask (.proj (.proj b q) f)))) cs
      = Except.ok so' :=
  compileStmt_ref_src_congr_proj_value (dbase := dbase) (g := g) kind prot mask _ _ cs
    (placeToBorrowRegChecked_projassoc_agree kind prot mask b q f _).1
    (placeToBorrowRegChecked_projassoc_agree kind prot mask b q f _).2

/-! ## Deref destination with a PROJ-TOPPED source over a bound local.
    `placeToBorrowRegChecked`'s proj arm differs from its local arm only
    in the borrow's OFFSET, so the fragment is the deref-dst pair with
    `pathOffset f` in place of `0`. -/

theorem compileStmt_ref_derefdst_projsrc_run
    {Γ : Ctx} {τ σs : LayoutTy}
    {P : Place Γ (obseq.LayoutTy.PtrL (obseq.LayoutTy.PtrL τ))}
    {srcLoc : Local Γ σs} {f : PathTo σs τ}
    {cs cs1 : CompilerState} {srcReg : Register}
    {dOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Mut (.deref P))}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (h_root : CompilerM.run (ensurePlaceRoot (Place.deref P)) cs = cs)
    (h_src : getPlaceInfo cs srcLoc.idx.1 = some (srcReg, σs))
    (h_cs1 : cs1 = emit { cs with nextReg := cs.nextReg + 1 }
      [Instr.Assgn (Register.R cs.nextReg)
        (Rhs.Borrow kind prot mask (blockSize τ) srcReg (pathOffset f))])
    (h_dval : CheckedCompilerM.value (placeToRegChecked RefKind.Mut (.deref P)) cs1
      = Except.ok dOut)
    (h_dclean : dOut.result.cleanup = []) :
    CheckedCompilerM.run
        (compileStmtChecked
          (Stmt.assign (.deref P)
            (.ref kind prot mask (.proj (.local srcLoc) f)))) cs
      = emit (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (.deref P)) cs1)
          [Instr.RStore obseq.TyVal.PTy (Register.R cs.nextReg) dOut.result.reg] := by
  obtain ⟨h_prun, placeOut, h_pval0, h_pres⟩ :=
    placeToRegChecked_local_existing (kind := kind) h_src
  subst h_cs1
  simp [csCompile, placeToBorrowRegChecked, h_root, h_prun, h_pval0, h_pres, h_dval]
  simp [csRun, cleanupInstrs, h_dval, h_dclean, emit_nil]

theorem compileStmt_ref_derefdst_projsrc_value
    {Γ : Ctx} {τ σs : LayoutTy}
    {P : Place Γ (obseq.LayoutTy.PtrL (obseq.LayoutTy.PtrL τ))}
    {srcLoc : Local Γ σs} {f : PathTo σs τ}
    {cs cs1 : CompilerState} {srcReg : Register}
    {dOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Mut (.deref P))}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (h_root : CompilerM.run (ensurePlaceRoot (Place.deref P)) cs = cs)
    (h_src : getPlaceInfo cs srcLoc.idx.1 = some (srcReg, σs))
    (h_cs1 : cs1 = emit { cs with nextReg := cs.nextReg + 1 }
      [Instr.Assgn (Register.R cs.nextReg)
        (Rhs.Borrow kind prot mask (blockSize τ) srcReg (pathOffset f))])
    (h_dval : CheckedCompilerM.value (placeToRegChecked RefKind.Mut (.deref P)) cs1
      = Except.ok dOut) :
    ∃ so, CheckedCompilerM.value
      (compileStmtChecked
        (Stmt.assign (.deref P)
          (.ref kind prot mask (.proj (.local srcLoc) f)))) cs
      = Except.ok so := by
  obtain ⟨h_prun, placeOut, h_pval0, h_pres⟩ :=
    placeToRegChecked_local_existing (kind := kind) h_src
  subst h_cs1
  simp only [csCompile, csMonad, placeToBorrowRegChecked, h_root, h_prun, h_pval0, h_pres]
  simp only [csRun]
  simp only [csMonad, h_dval]
  exact ⟨_, rfl⟩

/-! ## A PROJECTED destination over a DEREF base: `(*p).g := &kind _`.

    The destination root is a chain, so BOTH places need
    `ptrChain_lowering_sim` — the destination-spine mirror of the
    two-mother leaf. The source is left GENERIC: any base that is a
    `PtrChain` and is not itself a projection works, which after
    flattening covers every source shape. `h_unfold` is the
    `placeToBorrowRegChecked` equation for that base, supplied by
    `simp only [placeToBorrowRegChecked]` at each call site. -/

/-- At ZERO offset a projection over a deref returns the deref's own
    result, whose cleanup is empty. -/
theorem placeToRegChecked_projzero_deref_cleanup
    {Γ : Ctx} {σ τ : LayoutTy} {kind : RefKind}
    {pp : Place Γ (obseq.LayoutTy.PtrL σ)} {g : PathTo σ τ} {cs : CompilerState}
    {out : ResultWithEvidence PtrResult
      (PlaceToRegEvidence kind (.proj (.deref pp) g))}
    (h_o : pathOffset g = 0)
    (h : CheckedCompilerM.value (placeToRegChecked kind (.proj (.deref pp) g)) cs
      = Except.ok out) :
    out.result.cleanup = [] := by
  have h_np : ∀ (σ' : LayoutTy) (b : Place Γ σ') (q : PathTo σ' σ),
      Place.deref pp = b.proj q → False := by
    intro _ _ _ h_eq; cases h_eq
  cases h_b : CheckedCompilerM.value (placeToRegChecked kind (Place.deref pp)) cs with
  | error e =>
      rw [placeToRegChecked_proj_root_eq g h_np, CheckedCompilerM.value_bind, h_b] at h
      simp at h
  | ok o =>
      rw [placeToRegChecked_proj_zero_value g h_np h_o h_b] at h
      cases h
      exact placeToRegChecked_deref_cleanup h_b

/-! ## The same at NONZERO destination offset: the projection mints its
    own interior `Borrow(Mut)` over the destination chain's register and
    dies after the store, so BRIDGE 1 must collapse the triple. -/

/-- A chain source under a projected DEREF destination: one fragment lemma for
    both offsets, the tail through `projDstTail` over the destination chain's
    own register. -/
theorem compileStmt_ref_projderefdst_chainsrc_run
    {Γ : Ctx} {τ σd σs : LayoutTy}
    {pp : Place Γ (obseq.LayoutTy.PtrL σd)}
    {g : PathTo σd (obseq.LayoutTy.PtrL τ)}
    {sbase : Place Γ σs} {f : PathTo σs τ}
    {cs cs1 : CompilerState}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    {sOut : ResultWithEvidence PtrResult (PlaceToRegEvidence kind sbase)}
    {bOut : ResultWithEvidence PtrResult
      (PlaceToRegEvidence RefKind.Mut (.deref pp))}
    (h_unfold : placeToBorrowRegChecked (Γ := Γ) kind prot mask (Place.proj sbase f)
      = (do
          let baseOut ← placeToRegChecked kind sbase
          let baseRes := baseOut.result
          let offset := pathOffset f
          let tmpReg ← CheckedCompilerM.lift freshRegM
          let _ ← CheckedCompilerM.lift
            (emitM [Instr.Assgn tmpReg
              (Rhs.Borrow kind prot mask (blockSize τ) baseRes.reg offset)])
          pure {
            result := { reg := tmpReg,
                        cleanup := baseRes.cleanup ++ [(tmpReg, blockSize τ)] },
            evidence := PlaceToBorrowRegEvidence.proj sbase f baseRes tmpReg
              baseOut.evidence
          }))
    (h_root : CompilerM.run
      (ensurePlaceRoot (Place.proj (Place.deref pp) g)) cs = cs)
    (h_sval : CheckedCompilerM.value (placeToRegChecked kind sbase) cs
      = Except.ok sOut)
    (h_cs1 : cs1 = (emit { (CheckedCompilerM.run (placeToRegChecked kind sbase) cs) with nextReg := (CheckedCompilerM.run (placeToRegChecked kind sbase) cs).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked kind sbase) cs).nextReg) (Rhs.Borrow kind prot mask (blockSize τ) sOut.result.reg (pathOffset f))]))
    (h_bval : CheckedCompilerM.value (placeToRegChecked RefKind.Mut (.deref pp))
      cs1 = Except.ok bOut)
    (h_bclean : bOut.result.cleanup = []) :
    CheckedCompilerM.run
        (compileStmtChecked
          (Stmt.assign (Place.proj (Place.deref pp) g)
            (.ref kind prot mask (.proj sbase f)))) cs
      = projDstTail (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (Place.deref pp)) cs1)
          (pathOffset g) (blockSize (obseq.LayoutTy.PtrL τ)) obseq.TyVal.PTy
          (Register.R (CheckedCompilerM.run (placeToRegChecked kind sbase) cs).nextReg) bOut.result.reg := by
  subst h_cs1
  have h_proj_eq := placeToRegChecked_proj_root_eq (Γ := Γ) (kind := RefKind.Mut)
    (base := Place.deref pp) g (fun _ _ _ h => by cases h)
  by_cases h_go : pathOffset g = 0
  · rw [h_go, projDstTail_zero]
    simp only [csCompile, csMonad, h_unfold, h_proj_eq, h_root, h_sval]
    simp only [csRun]
    simp only [csMonad, h_bval, h_go, dif_pos]
    simp [csRun, cleanupInstrs, h_bclean, emit_nil]
  · rw [projDstTail_pos _ h_go]
    simp only [csCompile, csMonad, h_unfold, h_proj_eq, h_root, h_sval]
    simp only [csRun]
    simp only [csMonad, h_bval, h_go, dif_neg]
    simp [csRun, cleanupInstrs, h_bclean, emit_nil, borrowRhs]
    try rfl

theorem compileStmt_ref_projderefdst_chainsrc_value
    {Γ : Ctx} {τ σd σs : LayoutTy}
    {pp : Place Γ (obseq.LayoutTy.PtrL σd)}
    {g : PathTo σd (obseq.LayoutTy.PtrL τ)}
    {sbase : Place Γ σs} {f : PathTo σs τ}
    {cs cs1 : CompilerState}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    {sOut : ResultWithEvidence PtrResult (PlaceToRegEvidence kind sbase)}
    {bOut : ResultWithEvidence PtrResult
      (PlaceToRegEvidence RefKind.Mut (.deref pp))}
    (h_unfold : placeToBorrowRegChecked (Γ := Γ) kind prot mask (Place.proj sbase f)
      = (do
          let baseOut ← placeToRegChecked kind sbase
          let baseRes := baseOut.result
          let offset := pathOffset f
          let tmpReg ← CheckedCompilerM.lift freshRegM
          let _ ← CheckedCompilerM.lift
            (emitM [Instr.Assgn tmpReg
              (Rhs.Borrow kind prot mask (blockSize τ) baseRes.reg offset)])
          pure {
            result := { reg := tmpReg,
                        cleanup := baseRes.cleanup ++ [(tmpReg, blockSize τ)] },
            evidence := PlaceToBorrowRegEvidence.proj sbase f baseRes tmpReg
              baseOut.evidence
          }))
    (h_root : CompilerM.run
      (ensurePlaceRoot (Place.proj (Place.deref pp) g)) cs = cs)
    (h_sval : CheckedCompilerM.value (placeToRegChecked kind sbase) cs
      = Except.ok sOut)
    (h_cs1 : cs1 = (emit { (CheckedCompilerM.run (placeToRegChecked kind sbase) cs) with nextReg := (CheckedCompilerM.run (placeToRegChecked kind sbase) cs).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked kind sbase) cs).nextReg) (Rhs.Borrow kind prot mask (blockSize τ) sOut.result.reg (pathOffset f))]))
    (h_bval : CheckedCompilerM.value (placeToRegChecked RefKind.Mut (.deref pp))
      cs1 = Except.ok bOut) :
    ∃ so, CheckedCompilerM.value
      (compileStmtChecked
        (Stmt.assign (Place.proj (Place.deref pp) g)
          (.ref kind prot mask (.proj sbase f)))) cs
      = Except.ok so := by
  subst h_cs1
  have h_proj_eq := placeToRegChecked_proj_root_eq (Γ := Γ) (kind := RefKind.Mut)
    (base := Place.deref pp) g (fun _ _ _ h => by cases h)
  by_cases h_go : pathOffset g = 0
  · simp only [csCompile, csMonad, h_unfold, h_proj_eq, h_root, h_sval]
    simp only [csRun]
    simp only [csMonad, h_bval, h_go, dif_pos]
    exact ⟨_, rfl⟩
  · simp only [csCompile, csMonad, h_unfold, h_proj_eq, h_root, h_sval]
    simp only [csRun]
    simp only [csMonad, h_bval, h_go, dif_neg]
    exact ⟨_, rfl⟩

/-! ## TWO MOTHERS: a proj-topped DEREF source under a DEREF
    destination, `*D := &kind (*P).f`. The source chain lowers first
    (mother at `kind`, whose deref arm ignores it), then one `Borrow` at
    the projection's offset, then the destination chain (mother at
    `Mut`) whose register-frame conjunct carries the borrow temp across,
    then one `RStore`. Both lowerings leave an empty cleanup, so no
    `Die` is emitted and BRIDGE 1 is not needed. -/

theorem compileStmt_ref_derefdst_derefprojsrc_run
    {Γ : Ctx} {τ σb : LayoutTy}
    {D : Place Γ (obseq.LayoutTy.PtrL (obseq.LayoutTy.PtrL τ))}
    {P : Place Γ (obseq.LayoutTy.PtrL σb)} {f : PathTo σb τ}
    {cs cs1 : CompilerState}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    {sOut : ResultWithEvidence PtrResult (PlaceToRegEvidence kind (.deref P))}
    {dOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Mut (.deref D))}
    (h_root : CompilerM.run (ensurePlaceRoot (Place.deref D)) cs = cs)
    (h_sval : CheckedCompilerM.value (placeToRegChecked kind (.deref P)) cs
      = Except.ok sOut)
    (h_cs1 : cs1 = emit
      { (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) cs) with
          nextReg :=
            (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) cs).nextReg + 1 }
      [Instr.Assgn
        (Register.R
          (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) cs).nextReg)
        (Rhs.Borrow kind prot mask (blockSize τ) sOut.result.reg (pathOffset f))])
    (h_dval : CheckedCompilerM.value (placeToRegChecked RefKind.Mut (.deref D)) cs1
      = Except.ok dOut)
    (h_dclean : dOut.result.cleanup = []) :
    CheckedCompilerM.run
        (compileStmtChecked
          (Stmt.assign (.deref D) (.ref kind prot mask (.proj (.deref P) f)))) cs
      = emit (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (.deref D)) cs1)
          [Instr.RStore obseq.TyVal.PTy
            (Register.R
              (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) cs).nextReg)
            dOut.result.reg] := by
  have h_bindB : placeToBorrowRegChecked (Γ := Γ) kind prot mask (.proj (.deref P) f)
      = (do
          let baseOut ← placeToRegChecked kind (.deref P)
          let baseRes := baseOut.result
          let offset := pathOffset f
          let tmpReg ← CheckedCompilerM.lift freshRegM
          let _ ← CheckedCompilerM.lift
            (emitM [Instr.Assgn tmpReg
              (Rhs.Borrow kind prot mask (blockSize τ) baseRes.reg offset)])
          pure {
            result := { reg := tmpReg,
                        cleanup := baseRes.cleanup ++ [(tmpReg, blockSize τ)] },
            evidence := PlaceToBorrowRegEvidence.proj (.deref P) f baseRes tmpReg
              baseOut.evidence
          }) := by simp only [placeToBorrowRegChecked]
  subst h_cs1
  simp [csCompile, h_bindB, h_root, h_sval, h_dval]
  simp [csRun, cleanupInstrs, h_dval, h_dclean, emit_nil]

theorem compileStmt_ref_derefdst_derefprojsrc_value
    {Γ : Ctx} {τ σb : LayoutTy}
    {D : Place Γ (obseq.LayoutTy.PtrL (obseq.LayoutTy.PtrL τ))}
    {P : Place Γ (obseq.LayoutTy.PtrL σb)} {f : PathTo σb τ}
    {cs cs1 : CompilerState}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    {sOut : ResultWithEvidence PtrResult (PlaceToRegEvidence kind (.deref P))}
    {dOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Mut (.deref D))}
    (h_root : CompilerM.run (ensurePlaceRoot (Place.deref D)) cs = cs)
    (h_sval : CheckedCompilerM.value (placeToRegChecked kind (.deref P)) cs
      = Except.ok sOut)
    (h_cs1 : cs1 = emit
      { (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) cs) with
          nextReg :=
            (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) cs).nextReg + 1 }
      [Instr.Assgn
        (Register.R
          (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) cs).nextReg)
        (Rhs.Borrow kind prot mask (blockSize τ) sOut.result.reg (pathOffset f))])
    (h_dval : CheckedCompilerM.value (placeToRegChecked RefKind.Mut (.deref D)) cs1
      = Except.ok dOut) :
    ∃ so, CheckedCompilerM.value
      (compileStmtChecked
        (Stmt.assign (.deref D) (.ref kind prot mask (.proj (.deref P) f)))) cs
      = Except.ok so := by
  have h_bindB : placeToBorrowRegChecked (Γ := Γ) kind prot mask (.proj (.deref P) f)
      = (do
          let baseOut ← placeToRegChecked kind (.deref P)
          let baseRes := baseOut.result
          let offset := pathOffset f
          let tmpReg ← CheckedCompilerM.lift freshRegM
          let _ ← CheckedCompilerM.lift
            (emitM [Instr.Assgn tmpReg
              (Rhs.Borrow kind prot mask (blockSize τ) baseRes.reg offset)])
          pure {
            result := { reg := tmpReg,
                        cleanup := baseRes.cleanup ++ [(tmpReg, blockSize τ)] },
            evidence := PlaceToBorrowRegEvidence.proj (.deref P) f baseRes tmpReg
              baseOut.evidence
          }) := by simp only [placeToBorrowRegChecked]
  subst h_cs1
  simp only [csCompile, csMonad, h_bindB, h_root, h_sval]
  simp only [csRun]
  simp only [csMonad, h_dval]
  exact ⟨_, rfl⟩

/-- REGIME D-dst over full chains, COLLAPSED 2026-08-29 (originally
    closed 2026-08-29 for load spines): `*P := &kind src` for every dst
    with `PtrChain (.deref P)` — spines, proj-topped pointer places
    (`*(s.f) := &x`), interior projections at any depth; src a bound
    local. MIR order runs the retag FIRST; the mother lemma at `Mut` on
    the WHOLE dst (from the post-Borrow state, under the extended
    rename) performs the lowering including the final `Load`, its
    register-frame conjunct carrying the borrow temp across; the leaf
    adds one `RStore` (BRIDGE 2 through the loaded tag). One tag is
    minted on each side. -/
theorem ref_derefdst_local_simulation
    {τ : LayoutTy}
    {P : Place Γ (obseq.LayoutTy.PtrL (obseq.LayoutTy.PtrL τ))}
    {srcLoc : Local Γ τ}
    {bS : mirlite.Binding}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (compProg : oseair.Prog)
    (h_spine : PtrChain (Place.deref P))
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    {stmt0 : Stmt Γ}
    (h_stmt : prog.get? s_mir.pc = some stmt0)
    (h_run0 : ∀ cs, CheckedCompilerM.run (compileStmtChecked stmt0) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.deref P) (.ref kind prot mask (.local srcLoc)))) cs)
    (h_val0 : ∀ cs so, CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.deref P) (.ref kind prot mask (.local srcLoc)))) cs
        = Except.ok so →
      ∃ so', CheckedCompilerM.value (compileStmtChecked stmt0) cs
        = Except.ok so')
    (h_envS : mirlite.Env.lookup s_mir.env srcLoc = some bS)
    (h_step : mirlite.stepStmt MSB s_mir
      (.assign (.deref P) (.ref kind prot mask (.local srcLoc))) = .ok s_mir') :
    ∃ (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa ρt' s_mir' s_osea' := by
  obtain ⟨csPrefix, ⟨h_csAt, h_pc⟩, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_tbd,
    h_alloc, h_unmap, h_prb⟩ := h_inv
  obtain ⟨srcReg, baseS, tagS, h_piS, h_entryS, h_raS, h_rtS, h_nwS, h_domS⟩ :=
    h_lbs srcLoc bS h_envS
  have h_baseS : baseS = bS.addr := (h_id_a _ _ h_raS).symm
  subst h_baseS
  -- §1 invert: prepare is the identity on a resolvable deref root
  simp only [mirlite.stepStmt, mirlite.doAssign] at h_step
  cases h_prep : mirlite.preparePlaceAssign MSB s_mir (Place.deref P) with
  | err msg => simp [h_prep] at h_step
  | ok s1 =>
  simp only [h_prep] at h_step
  have h_pre : s1 = s_mir ∧
      ∃ r0, mirlite.resolvePlace? s_mir (Place.deref P) = some r0 := by
    simp only [mirlite.preparePlaceAssign] at h_prep
    split at h_prep
    · rename_i r0 h_r0
      cases h_prep
      exact ⟨rfl, r0, h_r0⟩
    · simp [mirlite.allocateRoot] at h_prep
  obtain ⟨h_s1, r0, h_resolved⟩ := h_pre
  rw [h_s1] at h_step
  -- §2 the rhs retag mints on the source FIRST (Rust order); the src's
  -- local resolution reduces WITHOUT unfolding the dst's resolveAcc
  simp only [mirlite.evalRExpr, resolvePlaceAcc_local h_envS] at h_step
  rw [if_neg (Nat.lt_irrefl (bS.addr + blockSize τ))] at h_step
  cases h_ref_src : MSB.ref s_mir.perms bS.addr (blockSize τ) bS.tag kind prot mask with
  | error e => rw [h_ref_src] at h_step; simp at h_step
  | ok pr =>
  obtain ⟨perms1, mintS⟩ := pr
  rw [h_ref_src] at h_step
  simp only at h_step
  -- §3 the WHOLE dst resolves on the POST-retag state (kept opaque)
  cases h_dres : mirlite.resolvePlaceAcc MSB
      { s_mir with perms := perms1 } (Place.deref P) with
  | error e => rw [h_dres] at h_step; simp at h_step
  | ok pr2 =>
  obtain ⟨resolved, permsD⟩ := pr2
  rw [h_dres] at h_step
  simp only at h_step
  -- §5 compiler-side scaffolding: the post-Borrow LocalBindingSim feeds
  -- both the mapped-ness of the dst at cs1 and the mother lemma
  have h_mapped : PlaceInputsMapped csPrefix (Place.deref P) :=
    placeInputsMapped_of_localBindingSim_resolvePlace h_lbs h_resolved
  have h_root := ensurePlaceRoot_run_eq_of_mapped h_mapped
  obtain ⟨dOut0, h_dval0⟩ := placeToRegChecked_ok_of_placeInputsMapped
    (cs := emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
      [Instr.Assgn (Register.R csPrefix.nextReg)
        (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)])
    (kind := RefKind.Mut)
    (PlaceInputsMapped.placeRegMap_congr (by simp only [emit]) _ h_mapped)
  obtain ⟨stmtOutC, h_stmtOutC⟩ :=
    compileStmt_ref_derefdst_value kind prot mask h_root h_piS rfl h_dval0
  obtain ⟨stmtOut, h_stmtOut⟩ := h_val0 csPrefix stmtOutC h_stmtOutC
  obtain ⟨h_lprun, placeOutL, h_lpval, h_lpres⟩ :=
    placeToRegChecked_local_existing (kind := kind) h_piS
  have h_incr2 : StateIncr
      (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (Place.deref P))
      (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
        [Instr.Assgn (Register.R csPrefix.nextReg)
          (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)]))
      (CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix) := by
    rw [h_run0]
    simp only [csCompile, csMonad, placeToBorrowRegChecked, h_root, h_lprun, h_lpval, h_lpres]
    simp only [csRun]
    simp only [csMonad, h_dval0]
    exact StateIncr.trans (emit_state_incr _ _)
      (StateIncr.trans (emit_state_incr _ _) (emit_state_incr _ _))
  have h_instD :=
    (CodeIncluded.of_stmt h_comp h_csAt h_stmt h_stmtOut).mono h_incr2
  -- §6 execute the Borrow (the rhs, FIRST)
  have h_incr_cs1 : StateIncr
      (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
        [Instr.Assgn (Register.R csPrefix.nextReg)
          (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)])
      (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (Place.deref P))
      (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
        [Instr.Assgn (Register.R csPrefix.nextReg)
          (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)])) :=
    CheckedCompilerM.incr _ _
  have h_lt_cs1 : csPrefix.nextLabel
      < (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
          [Instr.Assgn (Register.R csPrefix.nextReg)
            (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)]).nextLabel := by
    simp only [emit, List.length_cons, List.length_nil]
    omega
  have h_code1 : compProg s_osea.pc
      = some (Instr.Assgn (Register.R csPrefix.nextReg)
          (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)) := by
    rw [h_pc]
    refine h_instD _ _ (Nat.lt_of_lt_of_le h_lt_cs1 h_incr_cs1.nextLabel_le) ?_
    rw [h_incr_cs1.code_eq _ h_lt_cs1]
    have h := emit_code_at_new { csPrefix with nextReg := csPrefix.nextReg + 1 }
      [Instr.Assgn (Register.R csPrefix.nextReg)
        (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)] (k := 0) (by simp)
    simpa using h
  -- the SOURCE package: the retag transported, the `Borrow` executed, and
  -- the post-`Borrow` binding simulation the destination mother wants
  obtain ⟨tgtP1, rfl, h_incr_t, h_wf_t', h_tbd', h_psim', h_run1, h_lbs1,
    h_pc1, h_relB⟩ :=
    ref_local_borrow τ τ kind prot mask 0 compProg s_mir s_osea csPrefix
      h_id_a h_wf_t h_tbd h_lbs h_prb h_psim h_pc h_entryS h_raS h_rtS h_nwS
      h_domS (by simp) (by simpa using h_ref_src) h_code1
  -- §7 the WHOLE dst lowering via the mother lemma, from the
  -- post-Borrow state under the extended rename
  have h_prb1 : PlaceRegMapBound
      (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
        [Instr.Assgn (Register.R csPrefix.nextReg)
          (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)]) := by
    intro idx reg'' τ'' h_look
    refine RegisterBelow.mono ?_ (h_prb _ _ _ h_look)
    simp only [emit]
    exact Nat.le_succ _
  have h_sms1 : SourceMemSim ρa
      (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag)
      s_mir.mem s_osea.mem :=
    SourceMemSim.rename_mono (AddrRenameIncr.refl ρa) h_incr_t h_sms
  -- §7-§9: the shared chain-write seam (spine.lean) does the destination
  -- mother, the store, the memory argument and the rebuild
  obtain ⟨s_osea', n, h_run, h_inv'⟩ :=
    copy_chainwrite_after_read (τ := obseq.LayoutTy.PtrL τ)
      (csR := emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
        [Instr.Assgn (Register.R csPrefix.nextReg)
          (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)])
      (sR := { s_osea with
          perms := tgtP1,
          reg := oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
            (obseq.TyVal.PTy,
              [Val.Ptr bS.addr (0 + 0) (blockSize τ) s_osea.perms.NextTag]),
          pc := s_osea.pc + 1 })
      (vreg := Register.R csPrefix.nextReg)
      (vals := [Val.Ptr bS.addr (0 + 0) (blockSize τ) s_osea.perms.NextTag])
      (mvals := [mirlite.MemValue.ptrVal bS.addr (bS.addr - bS.addr) (blockSize τ)
        s_mir.perms.NextTag])
      compProg h_spine h_comp h_stmt h_csAt
      h_stmtOut h_id_a h_wf_t' h_sms1 h_alloc h_unmap h_prb
      h_dres rfl h_step
      h_run1
      rfl
      (by simp only [emit]; exact Nat.le_succ _)
      h_lbs1 h_psim' h_tbd'
      rfl
      h_pc1
      (RegMap.lookup_insert_self _ _ _)
      (by show _ < _; simp only [emit]; exact Nat.lt_succ_self _)
      rfl
      h_relB
      h_instD
      (fun dOut h_dval h_dclean => (h_run0 csPrefix).trans
        (compileStmt_ref_derefdst_run kind prot mask h_root h_piS rfl
          h_dval h_dclean))
  exact ⟨_, s_osea', n, h_incr_t, h_run, h_inv'⟩

/-- `fresh_projsrc`: one fragment lemma for both offsets, the destination tail
    stated through `projDstTail`. -/
theorem compileStmt_ref_proj_fresh_projsrc_lowers
    {Γ : Ctx} {τ σ σb : LayoutTy}
    {dstLoc : Local Γ σ} {g : PathTo σ (obseq.LayoutTy.PtrL τ)}
    {srcLoc : Local Γ σb} {f : PathTo σb τ}
    {cs : CompilerState} {srcReg : Register}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = none)
    (h_src : getPlaceInfo cs srcLoc.idx.1 = some (srcReg, σb)) :
    LowersTo
        (compileStmtChecked
          (Stmt.assign (.proj (.local dstLoc) g)
            (.ref kind prot mask (.proj (.local srcLoc) f)))) cs
      (projDstTail (emit
          { (setPlaceInfo
              (emit { cs with nextReg := cs.nextReg + 1 }
                [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
              dstLoc.idx.1 (Register.R cs.nextReg, σ)) with
              nextReg := cs.nextReg + 1 + 1 }
          [Instr.Assgn (Register.R (cs.nextReg + 1))
            (Rhs.Borrow kind prot mask (blockSize τ) srcReg (pathOffset f))])
        (pathOffset g) (blockSize (obseq.LayoutTy.PtrL τ)) obseq.TyVal.PTy
        (Register.R (cs.nextReg + 1)) (Register.R cs.nextReg)) := by
  obtain ⟨h_run, -⟩ := ensureLocalRegE_fresh (loc := dstLoc) h_dst
  have h_proj_eq := placeToRegChecked_proj_root_eq (Γ := Γ) (kind := RefKind.Mut)
    (base := .local dstLoc) g (fun _ _ _ h => by cases h)
  have h_root : CompilerM.run
      (ensurePlaceRoot (Place.proj (Place.local dstLoc) g)) cs = (setPlaceInfo
          (emit { cs with nextReg := cs.nextReg + 1 }
            [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
          dstLoc.idx.1 (Register.R cs.nextReg, σ)) := by
    show CompilerM.run (do let _ ← ensureLocalRegE dstLoc; pure ()) cs = _
    simp [CompilerM.run_bind, CompilerM.run_pure, h_run]
  have h_srcPost : getPlaceInfo
      (setPlaceInfo
        (emit { cs with nextReg := cs.nextReg + 1 }
          [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
        dstLoc.idx.1 (Register.R cs.nextReg, σ))
      srcLoc.idx.1 = some (srcReg, σb) := by
    by_cases h_eq : srcLoc.idx.1 = dstLoc.idx.1
    · exfalso
      grind
    · rw [getPlaceInfo_setPlaceInfo_ne _ h_eq, getPlaceInfo_emit]
      exact h_src
  obtain ⟨h_prun, placeOut, h_pval, h_pres⟩ :=
    placeToRegChecked_local_existing (kind := kind) h_srcPost
  have h_borrow_eq : placeToBorrowRegChecked (Γ := Γ) kind prot mask
      (.proj (.local srcLoc) f)
      = (do
          let baseOut ← placeToRegChecked kind (.local srcLoc)
          let baseRes := baseOut.result
          let offset := pathOffset f
          let tmpReg ← CheckedCompilerM.lift freshRegM
          let _ ← CheckedCompilerM.lift
            (emitM [Instr.Assgn tmpReg (Rhs.Borrow kind prot mask (blockSize τ) baseRes.reg offset)])
          pure {
            result := { reg := tmpReg,
                        cleanup := baseRes.cleanup ++ [(tmpReg, blockSize τ)] },
            evidence := PlaceToBorrowRegEvidence.proj (.local srcLoc) f baseRes tmpReg
              baseOut.evidence
          }) := by simp only [placeToBorrowRegChecked]
  have h_dstPost : getPlaceInfo
      (emit
        { (setPlaceInfo
            (emit { cs with nextReg := cs.nextReg + 1 }
              [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
            dstLoc.idx.1 (Register.R cs.nextReg, σ)) with
            nextReg := cs.nextReg + 1 + 1 }
        [Instr.Assgn (Register.R (cs.nextReg + 1))
          (Rhs.Borrow kind prot mask (blockSize τ) srcReg (pathOffset f))])
      dstLoc.idx.1 = some (Register.R cs.nextReg, σ) := by
    rw [getPlaceInfo_emit, getPlaceInfo_setNextReg]
    exact getPlaceInfo_setPlaceInfo_self _ _ _
  by_cases h_off : pathOffset g = 0
  · rw [h_off, projDstTail_zero]
    refine ⟨?_, ?_⟩
    · obtain ⟨h_brun, baseOut, h_bval, h_bres⟩ :=
        placeToRegChecked_local_existing (kind := RefKind.Mut) h_dstPost
      simp only [csCompile, csMonad, h_borrow_eq, h_proj_eq, h_root, h_prun, h_pval, h_off, dif_pos]
      simp [csRun, cleanupInstrs, h_pres, emit_nil]
      csnorm at h_bval h_brun h_bres ⊢
      simp only [h_bval, h_brun, h_bres]
      simp [emit_nil]
    · obtain ⟨h_brun, baseOut, h_bval, h_bres⟩ :=
        placeToRegChecked_local_existing (kind := RefKind.Mut) h_dstPost
      simp only [csCompile, csMonad, h_borrow_eq, h_proj_eq, h_root, h_prun, h_pval, h_off, dif_pos]
      simp only [csRun]
      simp only [h_pres]
      csnorm at h_bval ⊢
      simp only [h_bval]
      exact ⟨_, rfl⟩
  · rw [projDstTail_pos _ h_off]
    refine ⟨?_, ?_⟩
    · obtain ⟨h_brun, baseOut, h_bval, h_bres⟩ :=
        placeToRegChecked_local_existing (kind := RefKind.Mut) h_dstPost
      simp only [csCompile, csMonad, h_borrow_eq, h_proj_eq, h_root, h_prun, h_pval, h_off, dif_neg]
      simp [csRun, cleanupInstrs, h_pres, emit_nil]
      csnorm at h_bval h_brun h_bres ⊢
      simp only [h_pres, h_bval, h_brun, h_bres]
      simp [csRun, cleanupInstrs, emit_nil, borrowRhs]
      rfl
    · obtain ⟨h_brun, baseOut, h_bval, h_bres⟩ :=
        placeToRegChecked_local_existing (kind := RefKind.Mut) h_dstPost
      simp only [csCompile, csMonad, h_borrow_eq, h_proj_eq, h_root, h_prun, h_pval, h_off, dif_neg]
      simp only [csRun]
      simp only [h_pres]
      csnorm at h_bval ⊢
      simp only [h_bval]
      exact ⟨_, rfl⟩

/-- `fresh_selfsrc`: one fragment lemma for both offsets, the destination tail
    stated through `projDstTail`. -/
theorem compileStmt_ref_proj_fresh_selfsrc_lowers
    {Γ : Ctx} {τ σ : LayoutTy}
    {dstLoc : Local Γ σ} {g : PathTo σ (obseq.LayoutTy.PtrL τ)}
    {f : PathTo σ τ}
    {cs : CompilerState}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = none)
    :
    LowersTo
        (compileStmtChecked
          (Stmt.assign (.proj (.local dstLoc) g)
            (.ref kind prot mask (.proj (.local dstLoc) f)))) cs
      (projDstTail (emit
          { (setPlaceInfo
              (emit { cs with nextReg := cs.nextReg + 1 }
                [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
              dstLoc.idx.1 (Register.R cs.nextReg, σ)) with
              nextReg := cs.nextReg + 1 + 1 }
          [Instr.Assgn (Register.R (cs.nextReg + 1))
            (Rhs.Borrow kind prot mask (blockSize τ) (Register.R cs.nextReg) (pathOffset f))])
        (pathOffset g) (blockSize (obseq.LayoutTy.PtrL τ)) obseq.TyVal.PTy
        (Register.R (cs.nextReg + 1)) (Register.R cs.nextReg)) := by
  obtain ⟨h_run, -⟩ := ensureLocalRegE_fresh (loc := dstLoc) h_dst
  have h_proj_eq := placeToRegChecked_proj_root_eq (Γ := Γ) (kind := RefKind.Mut)
    (base := .local dstLoc) g (fun _ _ _ h => by cases h)
  have h_root : CompilerM.run
      (ensurePlaceRoot (Place.proj (Place.local dstLoc) g)) cs = (setPlaceInfo
          (emit { cs with nextReg := cs.nextReg + 1 }
            [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
          dstLoc.idx.1 (Register.R cs.nextReg, σ)) := by
    show CompilerM.run (do let _ ← ensureLocalRegE dstLoc; pure ()) cs = _
    simp [CompilerM.run_bind, CompilerM.run_pure, h_run]
  have h_srcPost : getPlaceInfo
      (setPlaceInfo
        (emit { cs with nextReg := cs.nextReg + 1 }
          [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
        dstLoc.idx.1 (Register.R cs.nextReg, σ))
      dstLoc.idx.1 = some (Register.R cs.nextReg, σ) :=
    getPlaceInfo_setPlaceInfo_self _ _ _
  obtain ⟨h_prun, placeOut, h_pval, h_pres⟩ :=
    placeToRegChecked_local_existing (kind := kind) h_srcPost
  have h_borrow_eq : placeToBorrowRegChecked (Γ := Γ) kind prot mask
      (.proj (.local dstLoc) f)
      = (do
          let baseOut ← placeToRegChecked kind (.local dstLoc)
          let baseRes := baseOut.result
          let offset := pathOffset f
          let tmpReg ← CheckedCompilerM.lift freshRegM
          let _ ← CheckedCompilerM.lift
            (emitM [Instr.Assgn tmpReg (Rhs.Borrow kind prot mask (blockSize τ) baseRes.reg offset)])
          pure {
            result := { reg := tmpReg,
                        cleanup := baseRes.cleanup ++ [(tmpReg, blockSize τ)] },
            evidence := PlaceToBorrowRegEvidence.proj (.local dstLoc) f baseRes tmpReg
              baseOut.evidence
          }) := by simp only [placeToBorrowRegChecked]
  have h_dstPost : getPlaceInfo
      (emit
        { (setPlaceInfo
            (emit { cs with nextReg := cs.nextReg + 1 }
              [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
            dstLoc.idx.1 (Register.R cs.nextReg, σ)) with
            nextReg := cs.nextReg + 1 + 1 }
        [Instr.Assgn (Register.R (cs.nextReg + 1))
          (Rhs.Borrow kind prot mask (blockSize τ) (Register.R cs.nextReg) (pathOffset f))])
      dstLoc.idx.1 = some (Register.R cs.nextReg, σ) := by
    rw [getPlaceInfo_emit, getPlaceInfo_setNextReg]
    exact getPlaceInfo_setPlaceInfo_self _ _ _
  by_cases h_off : pathOffset g = 0
  · rw [h_off, projDstTail_zero]
    refine ⟨?_, ?_⟩
    · obtain ⟨h_brun, baseOut, h_bval, h_bres⟩ :=
        placeToRegChecked_local_existing (kind := RefKind.Mut) h_dstPost
      simp only [csCompile, csMonad, h_borrow_eq, h_proj_eq, h_root, h_prun, h_pval, h_off, dif_pos]
      simp [csRun, cleanupInstrs, h_pres, emit_nil]
      csnorm at h_bval h_brun h_bres ⊢
      simp only [h_bval, h_brun, h_bres]
      simp [emit_nil]
    · obtain ⟨h_brun, baseOut, h_bval, h_bres⟩ :=
        placeToRegChecked_local_existing (kind := RefKind.Mut) h_dstPost
      simp only [csCompile, csMonad, h_borrow_eq, h_proj_eq, h_root, h_prun, h_pval, h_off, dif_pos]
      simp only [csRun]
      simp only [h_pres]
      csnorm at h_bval ⊢
      simp only [h_bval]
      exact ⟨_, rfl⟩
  · rw [projDstTail_pos _ h_off]
    refine ⟨?_, ?_⟩
    · obtain ⟨h_brun, baseOut, h_bval, h_bres⟩ :=
        placeToRegChecked_local_existing (kind := RefKind.Mut) h_dstPost
      simp only [csCompile, csMonad, h_borrow_eq, h_proj_eq, h_root, h_prun, h_pval, h_off, dif_neg]
      simp [csRun, cleanupInstrs, h_pres, emit_nil]
      csnorm at h_bval h_brun h_bres ⊢
      simp only [h_pres, h_bval, h_brun, h_bres]
      simp [csRun, cleanupInstrs, emit_nil, borrowRhs]
      rfl
    · obtain ⟨h_brun, baseOut, h_bval, h_bres⟩ :=
        placeToRegChecked_local_existing (kind := RefKind.Mut) h_dstPost
      simp only [csCompile, csMonad, h_borrow_eq, h_proj_eq, h_root, h_prun, h_pval, h_off, dif_neg]
      simp only [csRun]
      simp only [h_pres]
      csnorm at h_bval ⊢
      simp only [h_bval]
      exact ⟨_, rfl⟩

/-- `fresh_derefsrc`: one fragment lemma for both offsets, the destination tail
    stated through `projDstTail`. -/
theorem compileStmt_ref_proj_fresh_derefsrc_lowers
    {Γ : Ctx} {τ σ σb : LayoutTy}
    {dstLoc : Local Γ σ} {g : PathTo σ (obseq.LayoutTy.PtrL τ)}
    {P : Place Γ (obseq.LayoutTy.PtrL σb)} {f : PathTo σb τ}
    {cs : CompilerState}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    {dOut : ResultWithEvidence PtrResult (PlaceToRegEvidence kind (.deref P))}
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = none)
    (h_dval : CheckedCompilerM.value (placeToRegChecked kind (.deref P))
        (setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 } [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) dstLoc.idx.1 (Register.R cs.nextReg, σ))
      = Except.ok dOut)
    (h_dclean : dOut.result.cleanup = [])
    (h_prm : (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) (setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 } [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) dstLoc.idx.1 (Register.R cs.nextReg, σ))).placeRegMap = ((setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 } [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) dstLoc.idx.1 (Register.R cs.nextReg, σ))).placeRegMap) :
    LowersTo
        (compileStmtChecked
          (Stmt.assign (.proj (.local dstLoc) g)
            (.ref kind prot mask (.proj (.deref P) f)))) cs
      (projDstTail (emit { (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) (setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 } [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) dstLoc.idx.1 (Register.R cs.nextReg, σ))) with nextReg := (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) (setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 } [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) dstLoc.idx.1 (Register.R cs.nextReg, σ))).nextReg + 1 }
          [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) (setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 } [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) dstLoc.idx.1 (Register.R cs.nextReg, σ))).nextReg)
            (Rhs.Borrow kind prot mask (blockSize τ) dOut.result.reg (pathOffset f))])
        (pathOffset g) (blockSize (obseq.LayoutTy.PtrL τ)) obseq.TyVal.PTy
        (Register.R (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) (setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 } [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) dstLoc.idx.1 (Register.R cs.nextReg, σ))).nextReg) (Register.R cs.nextReg)) := by
  obtain ⟨h_run, -⟩ := ensureLocalRegE_fresh (loc := dstLoc) h_dst
  have h_proj_eq := placeToRegChecked_proj_root_eq (Γ := Γ) (kind := RefKind.Mut)
    (base := .local dstLoc) g (fun _ _ _ h => by cases h)
  have h_root : CompilerM.run
      (ensurePlaceRoot (Place.proj (Place.local dstLoc) g)) cs = (setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 } [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) dstLoc.idx.1 (Register.R cs.nextReg, σ)) := by
    show CompilerM.run (do let _ ← ensureLocalRegE dstLoc; pure ()) cs = _
    simp [CompilerM.run_bind, CompilerM.run_pure, h_run]
  have h_bindB : placeToBorrowRegChecked (Γ := Γ) kind prot mask (.proj (.deref P) f)
      = (do
          let baseOut ← placeToRegChecked kind (.deref P)
          let baseRes := baseOut.result
          let offset := pathOffset f
          let tmpReg ← CheckedCompilerM.lift freshRegM
          let _ ← CheckedCompilerM.lift
            (emitM [Instr.Assgn tmpReg (Rhs.Borrow kind prot mask (blockSize τ) baseRes.reg offset)])
          pure {
            result := { reg := tmpReg,
                        cleanup := baseRes.cleanup ++ [(tmpReg, blockSize τ)] },
            evidence := PlaceToBorrowRegEvidence.proj (.deref P) f baseRes tmpReg
              baseOut.evidence
          }) := by simp only [placeToBorrowRegChecked]
  have h_dstPost : getPlaceInfo
      (emit { (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) (setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 } [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) dstLoc.idx.1 (Register.R cs.nextReg, σ))) with nextReg := (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) (setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 } [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) dstLoc.idx.1 (Register.R cs.nextReg, σ))).nextReg + 1 }
        [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) (setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 } [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) dstLoc.idx.1 (Register.R cs.nextReg, σ))).nextReg)
          (Rhs.Borrow kind prot mask (blockSize τ) dOut.result.reg (pathOffset f))])
      dstLoc.idx.1 = some (Register.R cs.nextReg, σ) := by
    rw [getPlaceInfo_emit, getPlaceInfo_setNextReg]
    show (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) (setPlaceInfo (emit { cs with nextReg := cs.nextReg + 1 } [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) dstLoc.idx.1 (Register.R cs.nextReg, σ))).placeRegMap.lookup dstLoc.idx.1 = _
    rw [h_prm]
    exact getPlaceInfo_setPlaceInfo_self _ _ _
  by_cases h_off : pathOffset g = 0
  · rw [h_off, projDstTail_zero]
    refine ⟨?_, ?_⟩
    · obtain ⟨h_brun, baseOut, h_bval, h_bres⟩ :=
        placeToRegChecked_local_existing (kind := RefKind.Mut) h_dstPost
      simp only [csCompile, csMonad, compileRExprToChecked, h_bindB, h_proj_eq, h_root, h_dval,
        h_off, dif_pos]
      simp [csRun, cleanupInstrs, h_dclean, emit_nil]
      csnorm at h_bval h_brun h_bres ⊢
      simp only [h_bval, h_brun, h_bres]
      simp [emit_nil]
    · obtain ⟨h_brun, baseOut, h_bval, h_bres⟩ :=
        placeToRegChecked_local_existing (kind := RefKind.Mut) h_dstPost
      simp only [csCompile, csMonad, compileRExprToChecked, h_bindB, h_proj_eq, h_root, h_dval,
        h_off, dif_pos]
      simp only [csRun]
      csnorm at h_bval ⊢
      simp only [h_bval]
      exact ⟨_, rfl⟩
  · rw [projDstTail_pos _ h_off]
    refine ⟨?_, ?_⟩
    · obtain ⟨h_brun, baseOut, h_bval, h_bres⟩ :=
        placeToRegChecked_local_existing (kind := RefKind.Mut) h_dstPost
      simp only [csCompile, csMonad, compileRExprToChecked, h_bindB, h_proj_eq, h_root, h_dval,
        h_off, dif_neg]
      simp [csRun, cleanupInstrs, h_dclean, emit_nil]
      csnorm at h_bval h_brun h_bres ⊢
      simp only [h_bval, h_brun, h_bres]
      simp [csRun, cleanupInstrs, emit_nil, borrowRhs]
      rfl
    · obtain ⟨h_brun, baseOut, h_bval, h_bres⟩ :=
        placeToRegChecked_local_existing (kind := RefKind.Mut) h_dstPost
      simp only [csCompile, csMonad, compileRExprToChecked, h_bindB, h_proj_eq, h_root, h_dval,
        h_off, dif_neg]
      simp only [csRun]
      csnorm at h_bval ⊢
      simp only [h_bval]
      exact ⟨_, rfl⟩

/-- REGIME B-proj of ref: `dst := &kind s.f` with the DESTINATION ROOT
    UNBOUND. `preparePlaceAssign` allocates the destination on the
    mirlite side and `ensureLocalRegE` emits the matching `Alloc`, in
    lockstep; the source is a projected field of a bound local, which —
    as everywhere in `ref` — costs only the `Borrow`'s offset operand.
    Three instructions: `Alloc; Borrow; RStore`. -/
theorem ref_fresh_projsrc_simulation
    {τ σb : LayoutTy}
    {dstLoc : Local Γ (obseq.LayoutTy.PtrL τ)} {srcLoc : Local Γ σb}
    {f : PathTo σb τ}
    {bS : mirlite.Binding}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (compProg : oseair.Prog)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    {stmt0 : Stmt Γ}
    (h_stmt : prog.get? s_mir.pc = some stmt0)
    (h_run0 : ∀ cs, CheckedCompilerM.run (compileStmtChecked stmt0) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.local dstLoc) (.ref kind prot mask (.proj (.local srcLoc) f)))) cs)
    (h_val0 : ∀ cs so, CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.local dstLoc) (.ref kind prot mask (.proj (.local srcLoc) f)))) cs
        = Except.ok so →
      ∃ so', CheckedCompilerM.value (compileStmtChecked stmt0) cs
        = Except.ok so')
    (h_envD : mirlite.Env.lookup s_mir.env dstLoc = none)
    (h_envS : mirlite.Env.lookup s_mir.env srcLoc = some bS)
    (h_step : mirlite.stepStmt MSB s_mir
      (.assign (.local dstLoc) (.ref kind prot mask (.proj (.local srcLoc) f))) = .ok s_mir') :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' := by
  obtain ⟨csPrefix, ⟨h_csAt, h_pc⟩, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_tbd,
    h_alloc, h_unmap, h_prb⟩ := h_inv
  have h_piD : getPlaceInfo csPrefix dstLoc.idx.1 = none := h_unmap dstLoc h_envD
  obtain ⟨srcReg, baseS, tagS, h_piS, h_entryS, h_raS, h_rtS, h_nwS, h_domS⟩ :=
    h_lbs srcLoc bS h_envS
  have h_baseS : baseS = bS.addr := (h_id_a _ _ h_raS).symm
  subst h_baseS
  have h_idx_ne : srcLoc.idx ≠ dstLoc.idx := by
    intro h
    have hcontra : mirlite.Env.lookup s_mir.env dstLoc = some bS := by
      show s_mir.env dstLoc.idx = some bS
      rw [← h]; exact h_envS
    rw [h_envD] at hcontra
    simp at hcontra
  -- §1 the destination allocation, via the shared fresh-root prologue
  simp only [mirlite.stepStmt, mirlite.doAssign] at h_step
  cases h_prep : mirlite.preparePlaceAssign MSB s_mir (Place.local dstLoc) with
  | err m => rw [h_prep] at h_step; simp at h_step
  | ok s1 =>
      rw [h_prep] at h_step
      rw [show mirlite.preparePlaceAssign MSB s_mir (Place.local dstLoc)
          = mirlite.allocateBase MSB s_mir dstLoc from by
        simp only [mirPrep, mirAlloc, h_envD]] at h_prep
      have h_incr_a : AddrRenameIncr ρa
          (ρa.extend s_mir.mem.addrStart s_mir.mem.addrStart) :=
        AddrRenameIncr.extend_id h_id_a _
      have h_id_a' : IdentityOnDomain
          (ρa.extend s_mir.mem.addrStart s_mir.mem.addrStart) :=
        IdentityOnDomain.extend_id h_id_a _
      have h_ra_new : (ρa.extend s_mir.mem.addrStart s_mir.mem.addrStart)
          s_mir.mem.addrStart = some s_mir.mem.addrStart :=
        AddrRenameMap.extend_self _ _ _
      obtain ⟨permsOwned, tgtP1, h_own_tgt', h_perms1, h_pc1, h_env1,
        hD1, h_memstart1, h_find1, h_incr1, h_wf1, h_tbd1, h_psim1,
        h_erun, h_prb1, h_lbs1⟩ :=
        copy_freshroot_prologue h_envD h_prep h_id_a h_wf_t h_tbd h_psim h_alloc
          h_lbs h_prb h_piD h_incr_a h_id_a' h_ra_new
          (fun k hk => by
            have hk0 : k = 0 := by
              simp only [blockSize, obseq.layoutSize] at hk
              omega
            subst hk0
            simpa using h_ra_new)
      have h_addr_eq : s_osea.mem.addrStart = s_mir.mem.addrStart := h_alloc
      have h_szD : obseq.typeSize (layoutToTyVal (obseq.LayoutTy.PtrL τ))
          = blockSize (obseq.LayoutTy.PtrL τ) := obseq.typeSize_layoutToTyVal _
      -- §2 the source is untouched by the allocation; resolve and retag it
      have hS1 : mirlite.Env.lookup s1.env srcLoc = some bS := by
        rw [h_env1]
        simp only [mirlite.Env.lookup, mirlite.Env.set, if_neg h_idx_ne]
        exact h_envS
      simp only [mirlite.resolvePlaceAcc, mirlite.evalRExpr, hS1] at h_step
      rw [if_neg (Nat.not_lt.mpr (show bS.addr + pathOffset f + blockSize τ
          ≤ bS.addr + blockSize σb by
        have h_fit := PathTo.offset_add_size_le f
        simp only [Nat.add_assoc]
        exact Nat.add_le_add_left h_fit _))] at h_step
      cases h_ref_src : MSB.ref s1.perms (bS.addr + pathOffset f) (blockSize τ)
          bS.tag kind prot mask with
      | error e => rw [h_ref_src] at h_step; simp at h_step
      | ok pr2 =>
          obtain ⟨perms', tagR⟩ := pr2
          rw [h_ref_src] at h_step
          simp only at h_step
          -- the source binding's facts move to the extended ρt
          have h_rtS1 := h_incr1 _ _ h_rtS
          have h_raS' := h_incr_a _ _ h_raS
          -- §7 the fragment: Alloc; Borrow; RStore
          have h_stmtRun := (h_run0 csPrefix).trans
            ((compileStmt_ref_fresh_projsrc_lowers (cs := csPrefix) (f := f)
              kind prot mask h_piD h_piS).run)
          obtain ⟨stmtOutC, h_stmtOutC⟩ :=
            (compileStmt_ref_fresh_projsrc_lowers (cs := csPrefix) (f := f)
              kind prot mask h_piD h_piS).value
          obtain ⟨stmtOut, h_stmtOut⟩ := h_val0 csPrefix stmtOutC h_stmtOutC
          have hFrag6 :=
            (CodeIncluded.of_stmt h_comp h_csAt h_stmt h_stmtOut).fragmentOf
              h_stmtRun h_pc
          have h_code1 : compProg s_osea.pc
              = some (Instr.Assgn (Register.R csPrefix.nextReg)
                  (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))) :=
            hFrag6.instrAt 0 rfl rfl
          have h_code2 : compProg (s_osea.pc + 1)
              = some (Instr.Assgn (Register.R (csPrefix.nextReg + 1))
                  (Rhs.Borrow kind prot mask (blockSize τ) srcReg (pathOffset f))) :=
            hFrag6.instrAt 1 rfl rfl
          have h_code3 : compProg (s_osea.pc + 1 + 1)
              = some (Instr.RStore obseq.TyVal.PTy (Register.R (csPrefix.nextReg + 1))
                  (Register.R csPrefix.nextReg)) :=
            hFrag6.instrAt 2 rfl rfl
          -- §8 execute Alloc, then Borrow
          have h_run1 := runN_Assgn_Alloc_step compProg s_osea
            (Register.R csPrefix.nextReg) (layoutToTyVal (obseq.LayoutTy.PtrL τ))
            h_code1 h_own_tgt'
          have h_regne : srcReg ≠ Register.R csPrefix.nextReg := by
            cases srcReg with
            | R n => have h_lt := h_prb _ _ _ h_piS; grind
          have h_entryS1 : PtrRegisterEntry
              (oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
                (obseq.TyVal.PTy, [Val.Ptr s_osea.mem.addrStart 0
                  (obseq.typeSize (layoutToTyVal (obseq.LayoutTy.PtrL τ)))
                  s_osea.perms.NextTag]))
              srcReg bS.addr 0 (blockSize σb) tagS := by
            show oseair.RegMap.lookup _ _ = _
            rw [RegMap.lookup_insert_ne _ h_regne]
            exact h_entryS
          -- §8 the SOURCE half as the local-borrow package, from the post-Alloc
          -- states: the retag transport and the Borrow, at the field offset
          obtain ⟨tgtP2, rfl, h_incr2, h_wf2, h_tbd2, h_psim2, h_run2, h_lbsB, h_pcB,
            h_relB⟩ :=
            ref_local_borrow (ρa := ρa.extend s_mir.mem.addrStart s_mir.mem.addrStart)
              (ρt := ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag)
              τ σb kind prot mask (pathOffset f) compProg s1
              { s_osea with mem := (oseair.allocate s_osea.mem (obseq.typeSize (layoutToTyVal (obseq.LayoutTy.PtrL τ)))).2, perms := tgtP1, reg := oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg) (obseq.TyVal.PTy, [Val.Ptr s_osea.mem.addrStart 0 (obseq.typeSize (layoutToTyVal (obseq.LayoutTy.PtrL τ))) s_osea.perms.NextTag]), pc := s_osea.pc + 1 }
              (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))]) dstLoc.idx.1 (Register.R csPrefix.nextReg, obseq.LayoutTy.PtrL τ))
              h_id_a' h_wf1 (by rw [h_perms1]; exact h_tbd1) h_lbs1 h_prb1
              (by rw [h_perms1]; exact h_psim1)
              (by
                show s_osea.pc + 1 = _
                rw [h_pc]
                simp only [emit_nextLabel, setPlaceInfo_nextLabel, List.length_cons,
                  List.length_nil])
              h_entryS1 h_raS' h_rtS1 h_nwS
              (fun k hk => ⟨(h_domS k hk).choose,
                h_incr_a _ _ (h_domS k hk).choose_spec⟩)
              (PathTo.offset_add_size_le f) h_ref_src h_code2
          have h_incr12 := TagRenameIncr.trans h_incr1 h_incr2
          -- §9-§10 the fresh-root WRITE seam, shared with copy
          simp only [hD1] at h_step
          exact copy_freshroot_write_after_read
            (τ := obseq.LayoutTy.PtrL τ)
            (csR := emit
              { (setPlaceInfo
                (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                  [Instr.Assgn (Register.R csPrefix.nextReg)
                    (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))])
                dstLoc.idx.1 (Register.R csPrefix.nextReg, obseq.LayoutTy.PtrL τ)) with
                nextReg := csPrefix.nextReg + 1 + 1 }
              [Instr.Assgn (Register.R (csPrefix.nextReg + 1))
                (Rhs.Borrow kind prot mask (blockSize τ) srcReg (pathOffset f))])
            (sR := { s_osea with
                mem := (oseair.allocate s_osea.mem
                  (obseq.typeSize (layoutToTyVal (obseq.LayoutTy.PtrL τ)))).2,
                perms := tgtP2,
                reg := oseair.RegMap.insert
                  (oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
                    (obseq.TyVal.PTy, [Val.Ptr s_osea.mem.addrStart 0
                      (obseq.typeSize (layoutToTyVal (obseq.LayoutTy.PtrL τ)))
                      s_osea.perms.NextTag]))
                  (Register.R (csPrefix.nextReg + 1))
                  (obseq.TyVal.PTy, [Val.Ptr bS.addr (0 + pathOffset f) (blockSize σb)
                    tgtP1.NextTag]),
                pc := s_osea.pc + 1 + 1 })
            (vreg := Register.R (csPrefix.nextReg + 1))
            (vals := [Val.Ptr bS.addr (0 + pathOffset f) (blockSize σb) tgtP1.NextTag])
            (mvals := [mirlite.MemValue.ptrVal bS.addr (bS.addr + pathOffset f - bS.addr)
              (blockSize σb) s1.perms.NextTag])
            compProg h_comp h_stmt h_csAt
            h_stmtOut h_sms h_unmap h_prb hD1 h_env1 h_pc1 h_memstart1 h_find1
            h_addr_eq h_szD h_run1 h_incr_a h_incr12 h_id_a' h_wf2
            (fun k hk => by
              have hk0 : k = 0 := by
                simp only [blockSize, obseq.layoutSize] at hk
                omega
              subst hk0
              simpa using h_ra_new)
            h_prb1 h_run2
            (by simp only [emit, setPlaceInfo])
            (by simp only [emit, setPlaceInfo]; omega)
            h_lbsB
            h_psim2 h_tbd2 rfl
            h_pcB
            (RegMap.lookup_insert_self _ _ _)
            (by simp [blockSize, obseq.layoutSize])
            h_stmtRun (by simp [blockSize, obseq.layoutSize]) (Nat.le_refl _) rfl rfl
            h_relB
            h_step
/-! ## Fresh projected destination with a PROJ-TOPPED source. -/

/-! ## The destination root as its own source: `t.g := &kind t.f`
    with `t` FRESH. The source register is the root register the
    `Alloc` just produced, so the source's placeInfo is
    `getPlaceInfo_setPlaceInfo_self` rather than a survival argument. -/

/-! ## A CHAIN source under a FRESH projected destination, offset zero. -/

/-! ## A CHAIN source under a FRESH projected destination at NONZERO
    offset: the σ-sized root `Alloc`, the spine, the source `Borrow`,
    then BRIDGE 1's `Borrow(Mut)`/`RStore`/`Die` on the destination. -/

/-- REGIME B-proj for the DESTINATION: `dst.g := &kind s` at ZERO
    field offset with `dst`'s root UNBOUND. `preparePlaceAssign` runs
    `allocateRoot` for the whole σ-sized root and `ensurePlaceRoot`
    emits the matching σ-sized `Alloc`; ρa extends by the IDENTITY over
    that whole block (`extendBlock`), not at a single cell as in the
    pointer-local case. At offset zero the store goes through the root
    register, so the fragment is still `Alloc; Borrow; RStore`. -/
theorem ref_proj_fresh_simulation
    {τ σ : LayoutTy}
    {dstLoc : Local Γ σ} {g : PathTo σ (obseq.LayoutTy.PtrL τ)}
    {srcLoc : Local Γ τ}
    {bS : mirlite.Binding}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (compProg : oseair.Prog)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    {stmt0 : Stmt Γ}
    (h_stmt : prog.get? s_mir.pc = some stmt0)
    (h_run0 : ∀ cs, CheckedCompilerM.run (compileStmtChecked stmt0) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.proj (.local dstLoc) g)
              (.ref kind prot mask (.local srcLoc)))) cs)
    (h_val0 : ∀ cs so, CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.proj (.local dstLoc) g)
            (.ref kind prot mask (.local srcLoc)))) cs
        = Except.ok so →
      ∃ so', CheckedCompilerM.value (compileStmtChecked stmt0) cs
        = Except.ok so')
    (h_envD : mirlite.Env.lookup s_mir.env dstLoc = none)
    (h_envS : mirlite.Env.lookup s_mir.env srcLoc = some bS)
    (h_step : mirlite.stepStmt MSB s_mir
      (.assign (.proj (.local dstLoc) g) (.ref kind prot mask (.local srcLoc))) = .ok s_mir') :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' := by
  obtain ⟨csPrefix, ⟨h_csAt, h_pc⟩, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_tbd,
    h_alloc, h_unmap, h_prb⟩ := h_inv
  have h_piD : getPlaceInfo csPrefix dstLoc.idx.1 = none := h_unmap dstLoc h_envD
  obtain ⟨srcReg, baseS, tagS, h_piS, h_entryS, h_raS, h_rtS, h_nwS, h_domS⟩ :=
    h_lbs srcLoc bS h_envS
  have h_baseS : baseS = bS.addr := (h_id_a _ _ h_raS).symm
  subst h_baseS
  have h_idx_ne : srcLoc.idx ≠ dstLoc.idx := by
    intro h
    have hcontra : mirlite.Env.lookup s_mir.env dstLoc = some bS := by
      show s_mir.env dstLoc.idx = some bS
      rw [← h]; exact h_envS
    rw [h_envD] at hcontra
    exact absurd hcontra (by simp)
  -- §1 the destination allocation, via the shared fresh-root prologue: the
  -- projected destination's ROOT is what gets allocated
  simp only [mirlite.stepStmt, mirlite.doAssign] at h_step
  cases h_prep : mirlite.preparePlaceAssign MSB s_mir
      (Place.proj (Place.local dstLoc) g) with
  | err m => rw [h_prep] at h_step; simp at h_step
  | ok s1 =>
      rw [h_prep] at h_step
      rw [show mirlite.preparePlaceAssign MSB s_mir (Place.proj (Place.local dstLoc) g)
          = mirlite.allocateBase MSB s_mir dstLoc from by
        simp only [mirPrep, mirAlloc, h_envD]] at h_prep
      have h_incr_a : AddrRenameIncr ρa
          (ρa.extendBlock s_mir.mem.addrStart (blockSize σ)) :=
        AddrRenameIncr.extendBlock h_id_a _ _
      have h_id_a' : IdentityOnDomain
          (ρa.extendBlock s_mir.mem.addrStart (blockSize σ)) :=
        IdentityOnDomain.extendBlock h_id_a _ _
      have h_ra_base : (ρa.extendBlock s_mir.mem.addrStart (blockSize σ))
          s_mir.mem.addrStart = some s_mir.mem.addrStart :=
        AddrRenameMap.extendBlock_base _ _ _
      have h_ra_dom : ∀ k, k < blockSize σ →
          (ρa.extendBlock s_mir.mem.addrStart (blockSize σ))
            (s_mir.mem.addrStart + k) = some (s_mir.mem.addrStart + k) :=
        fun _ hk => AddrRenameMap.extendBlock_mem hk
      obtain ⟨permsOwned, tgtP1, h_own_tgt', h_perms1, h_pc1, h_env1,
        hD1, h_memstart1, h_find1, h_incr1, h_wf1, h_tbd1, h_psim1,
        h_erun, h_prb1, h_lbs1⟩ :=
        copy_freshroot_prologue h_envD h_prep h_id_a h_wf_t h_tbd h_psim h_alloc
          h_lbs h_prb h_piD h_incr_a h_id_a' h_ra_base h_ra_dom
      have h_addr_eq : s_osea.mem.addrStart = s_mir.mem.addrStart := h_alloc
      have h_szD : obseq.typeSize (layoutToTyVal σ) = blockSize σ :=
        obseq.typeSize_layoutToTyVal _
      -- §2 the source is untouched by the allocation; resolve and retag it
      have hS1 : mirlite.Env.lookup s1.env srcLoc = some bS := by
        rw [h_env1]
        simp only [mirlite.Env.lookup, mirlite.Env.set, if_neg h_idx_ne]
        exact h_envS
      simp only [mirlite.doAssignCont, mirlite.resolvePlaceAcc, hD1,
        mirlite.evalRExpr, hS1] at h_step
      rw [if_neg (Nat.lt_irrefl (bS.addr + blockSize τ))] at h_step
      cases h_ref_src : MSB.ref s1.perms bS.addr (blockSize τ) bS.tag kind prot mask with
      | error e => rw [h_ref_src] at h_step; simp at h_step
      | ok pr2 =>
          obtain ⟨perms', tagR⟩ := pr2
          rw [h_ref_src] at h_step
          simp only at h_step
          have h_rtS1 := h_incr1 _ _ h_rtS
          have h_raS' := h_incr_a _ _ h_raS
          -- §7 the fragment: Alloc; Borrow; then the destination tail at the
          -- projection's offset, whichever it is
          have h_stmtRun := (h_run0 csPrefix).trans
            ((compileStmt_ref_proj_fresh_lowers (cs := csPrefix)
              kind prot mask h_piD h_piS).run)
          obtain ⟨stmtOutC, h_stmtOutC⟩ :=
            (compileStmt_ref_proj_fresh_lowers (cs := csPrefix) kind prot mask
              h_piD h_piS).value
          obtain ⟨stmtOut, h_stmtOut⟩ := h_val0 csPrefix stmtOutC h_stmtOutC
          have hFrag7 := ((CodeIncluded.of_stmt h_comp h_csAt h_stmt h_stmtOut).mono
            (by rw [h_stmtRun]; exact projDstTail_state_incr _ _ _ _ _ _)).fragmentOf
            rfl h_pc
          have h_code1 : compProg s_osea.pc
              = some (Instr.Assgn (Register.R csPrefix.nextReg)
                  (Rhs.Alloc (layoutToTyVal (σ)))) :=
            hFrag7.instrAt 0 rfl rfl
          have h_code2 : compProg (s_osea.pc + 1)
              = some (Instr.Assgn (Register.R (csPrefix.nextReg + 1))
                  (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)) :=
            hFrag7.instrAt 1 rfl rfl
          -- §8 execute Alloc, then Borrow
          have h_run1 := runN_Assgn_Alloc_step compProg s_osea
            (Register.R csPrefix.nextReg) (layoutToTyVal (σ))
            h_code1 h_own_tgt'
          have h_regne : srcReg ≠ Register.R csPrefix.nextReg := by
            cases srcReg with
            | R n => have h_lt := h_prb _ _ _ h_piS; grind
          have h_entryS1 : PtrRegisterEntry
              (oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
                (obseq.TyVal.PTy, [Val.Ptr s_osea.mem.addrStart 0
                  (obseq.typeSize (layoutToTyVal (σ)))
                  s_osea.perms.NextTag]))
              srcReg bS.addr 0 (blockSize τ) tagS := by
            show oseair.RegMap.lookup _ _ = _
            rw [RegMap.lookup_insert_ne _ h_regne]
            exact h_entryS
          -- §8 the SOURCE half as the local-borrow package, from the post-Alloc
          -- states: the retag transport and the Borrow
          obtain ⟨tgtP2, rfl, h_incr2, h_wf2, h_tbd2, h_psim2, h_run2, h_lbsB, h_pcB,
            h_relB⟩ :=
            ref_local_borrow (ρa := ρa.extendBlock s_mir.mem.addrStart (blockSize σ))
              (ρt := ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag)
              τ τ kind prot mask 0 compProg s1
              { s_osea with mem := (oseair.allocate s_osea.mem (obseq.typeSize (layoutToTyVal σ))).2, perms := tgtP1, reg := oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg) (obseq.TyVal.PTy, [Val.Ptr s_osea.mem.addrStart 0 (obseq.typeSize (layoutToTyVal σ)) s_osea.perms.NextTag]), pc := s_osea.pc + 1 }
              (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) dstLoc.idx.1 (Register.R csPrefix.nextReg, σ))
              h_id_a' h_wf1 (by rw [h_perms1]; exact h_tbd1) h_lbs1 h_prb1
              (by rw [h_perms1]; exact h_psim1)
              (by
                show s_osea.pc + 1 = _
                rw [h_pc]
                simp only [emit_nextLabel, setPlaceInfo_nextLabel, List.length_cons,
                  List.length_nil])
              h_entryS1 h_raS' h_rtS1 h_nwS
              (fun k hk => ⟨(h_domS k hk).choose,
                h_incr_a _ _ (h_domS k hk).choose_spec⟩)
              (by simp) (by simpa using h_ref_src) h_code2
          have h_incr12 := TagRenameIncr.trans h_incr1 h_incr2
          -- §9-§10 the fresh WRITE seam, at the projection's offset: the root
          -- is σ-sized, the value stored is the borrow's pointer
          simp only [hD1] at h_step
          exact copy_fresh_write_after_read
            (τ := obseq.LayoutTy.PtrL τ)
            (csR := emit
              { (setPlaceInfo
                (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                  [Instr.Assgn (Register.R csPrefix.nextReg)
                    (Rhs.Alloc (layoutToTyVal σ))])
                dstLoc.idx.1 (Register.R csPrefix.nextReg, σ)) with
                nextReg := csPrefix.nextReg + 1 + 1 }
              [Instr.Assgn (Register.R (csPrefix.nextReg + 1))
                (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)])
            (sR := { s_osea with
                mem := (oseair.allocate s_osea.mem
                  (obseq.typeSize (layoutToTyVal σ))).2,
                perms := tgtP2,
                reg := oseair.RegMap.insert
                  (oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
                    (obseq.TyVal.PTy, [Val.Ptr s_osea.mem.addrStart 0
                      (obseq.typeSize (layoutToTyVal σ)) s_osea.perms.NextTag]))
                  (Register.R (csPrefix.nextReg + 1))
                  (obseq.TyVal.PTy, [Val.Ptr bS.addr (0 + 0) (blockSize τ)
                    tgtP1.NextTag]),
                pc := s_osea.pc + 1 + 1 })
            (vreg := Register.R (csPrefix.nextReg + 1))
            (vals := [Val.Ptr bS.addr (0 + 0) (blockSize τ) tgtP1.NextTag])
            (mvals := [mirlite.MemValue.ptrVal bS.addr (bS.addr - bS.addr)
              (blockSize τ) s1.perms.NextTag])
            compProg h_comp h_stmt h_csAt h_stmtOut h_sms h_unmap h_prb hD1
            h_env1 h_pc1 h_memstart1 h_find1 h_addr_eq h_szD h_run1 h_incr_a
            h_incr12 h_id_a' h_wf2 h_ra_dom h_prb1
            (pathOffset g) (PathTo.offset_add_size_le g) h_run2
            (by simp only [emit, setPlaceInfo])
            (by simp only [emit, setPlaceInfo]; omega)
            h_lbsB h_psim2 h_tbd2 rfl h_pcB
            (RegMap.lookup_insert_self _ _ _)
            (by show _ < _; simp only [emit, setPlaceInfo]; omega)
            (by simp [blockSize, obseq.layoutSize])
            h_stmtRun
            (by simp [blockSize, obseq.layoutSize]) rfl rfl rfl rfl
            h_relB h_step
/-- REGIME B of ref with a DEREF SOURCE: `dst := &kind *chain` and
    `dst`'s root UNBOUND. The root `Alloc` comes FIRST, so the source
    spine lowers from the post-`Alloc` states — which means the mother
    lemma's whole hypothesis bundle (`LocalBindingSim`,
    `PlaceRegMapBound`, `SourceMemSim`, `PermSim`, the pc agreement and
    the instruction transfer) has to be re-established MID-PROOF at the
    extended renames, not just rebuilt at the end. -/
theorem ref_fresh_derefsrc_simulation
    {τ : LayoutTy}
    {dstLoc : Local Γ (obseq.LayoutTy.PtrL τ)}
    {P : Place Γ (obseq.LayoutTy.PtrL τ)}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (compProg : oseair.Prog)
    (h_spine : PtrChain (Place.deref P))
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    {stmt0 : Stmt Γ}
    (h_stmt : prog.get? s_mir.pc = some stmt0)
    (h_run0 : ∀ cs, CheckedCompilerM.run (compileStmtChecked stmt0) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.local dstLoc) (.ref kind prot mask (.deref P)))) cs)
    (h_val0 : ∀ cs so, CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.local dstLoc) (.ref kind prot mask (.deref P)))) cs
        = Except.ok so →
      ∃ so', CheckedCompilerM.value (compileStmtChecked stmt0) cs
        = Except.ok so')
    (h_envD : mirlite.Env.lookup s_mir.env dstLoc = none)
    (h_step : mirlite.stepStmt MSB s_mir
      (.assign (.local dstLoc) (.ref kind prot mask (.deref P))) = .ok s_mir') :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' := by
  obtain ⟨csPrefix, ⟨h_csAt, h_pc⟩, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_tbd,
    h_alloc, h_unmap, h_prb⟩ := h_inv
  have h_piD : getPlaceInfo csPrefix dstLoc.idx.1 = none := h_unmap dstLoc h_envD
  -- §1 the destination root is allocated on both machines, via the shared
  -- fresh-root prologue
  simp only [mirlite.stepStmt, mirlite.doAssign] at h_step
  cases h_prep : mirlite.preparePlaceAssign MSB s_mir (Place.local dstLoc) with
  | err m => rw [h_prep] at h_step; simp at h_step
  | ok s1 =>
  rw [h_prep] at h_step
  rw [show mirlite.preparePlaceAssign MSB s_mir (Place.local dstLoc)
      = mirlite.allocateBase MSB s_mir dstLoc from by
    simp only [mirPrep, mirAlloc, h_envD]] at h_prep
  have h_incr_a : AddrRenameIncr ρa
      (ρa.extendBlock s_mir.mem.addrStart (blockSize (obseq.LayoutTy.PtrL τ))) :=
    AddrRenameIncr.extendBlock h_id_a _ _
  have h_id_a' : IdentityOnDomain
      (ρa.extendBlock s_mir.mem.addrStart (blockSize (obseq.LayoutTy.PtrL τ))) :=
    IdentityOnDomain.extendBlock h_id_a _ _
  have h_ra_base : (ρa.extendBlock s_mir.mem.addrStart (blockSize (obseq.LayoutTy.PtrL τ)))
      s_mir.mem.addrStart = some s_mir.mem.addrStart :=
    AddrRenameMap.extendBlock_base _ _ _
  have h_ra_dom : ∀ k, k < blockSize (obseq.LayoutTy.PtrL τ) →
      (ρa.extendBlock s_mir.mem.addrStart (blockSize (obseq.LayoutTy.PtrL τ)))
        (s_mir.mem.addrStart + k) = some (s_mir.mem.addrStart + k) :=
    fun _ hk => AddrRenameMap.extendBlock_mem hk
  obtain ⟨permsOwned, tgtP1, h_own_tgt', h_perms1, h_pc1, h_env1,
    h_lookup_set, h_memstart1, h_find1, h_incr_t, h_wf1, h_tbd1, h_psim1,
    h_erun, h_prb1, h_lbs1⟩ :=
    copy_freshroot_prologue h_envD h_prep h_id_a h_wf_t h_tbd h_psim h_alloc
      h_lbs h_prb h_piD h_incr_a h_id_a' h_ra_base h_ra_dom
  -- §2 the facts the source mother will want, at the post-`Alloc` states
  have h_addr_eq : s_osea.mem.addrStart = s_mir.mem.addrStart := h_alloc
  have h_sz : obseq.typeSize (layoutToTyVal (obseq.LayoutTy.PtrL τ)) = blockSize (obseq.LayoutTy.PtrL τ) :=
    obseq.typeSize_layoutToTyVal _
  have h_rt_new : (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag)
      s_mir.perms.NextTag = some s_osea.perms.NextTag :=
    TagRenameMap.extend_self _ _ _
  have h0 : wildcardTag < s_mir.perms.NextTag := (h_tbd _ _ h_wf_t.2).1
  have h_nw : (s_mir.perms.NextTag == wildcardTag) = false := by grind
  have h_smsA : SourceMemSim
      (ρa.extendBlock s_mir.mem.addrStart (blockSize (obseq.LayoutTy.PtrL τ)))
      (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag)
      s1.mem (oseair.allocate s_osea.mem
        (obseq.typeSize (layoutToTyVal (obseq.LayoutTy.PtrL τ)))).2 := by
    intro a v h_find
    rw [h_find1] at h_find
    exact SourceMemSim.rename_mono h_incr_a h_incr_t h_sms a v h_find
  have h_pi_new : getPlaceInfo (setPlaceInfo
      (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
        [Instr.Assgn (Register.R csPrefix.nextReg)
          (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))])
      dstLoc.idx.1 (Register.R csPrefix.nextReg, (obseq.LayoutTy.PtrL τ))) dstLoc.idx.1
      = some (Register.R csPrefix.nextReg, (obseq.LayoutTy.PtrL τ)) :=
    getPlaceInfo_setPlaceInfo_self _ _ _
  -- §4 the rhs resolves on the POST-allocation state, kept opaque
  simp only [mirlite.evalRExpr] at h_step
  cases h_dres : mirlite.resolvePlaceAcc MSB s1 (Place.deref P) with
  | error e => rw [h_dres] at h_step; simp at h_step
  | ok pr2 =>
  obtain ⟨resolved, permsR⟩ := pr2
  rw [h_dres] at h_step
  simp only at h_step
  by_cases h_fit : resolved.addr + blockSize τ
      > resolved.allocBase + resolved.allocSize
  · rw [if_pos h_fit] at h_step
    simp at h_step
  · rw [if_neg h_fit] at h_step
    cases h_ref_src : MSB.ref permsR resolved.addr (blockSize τ) resolved.tag
        kind prot mask with
    | error e => rw [h_ref_src] at h_step; simp at h_step
    | ok pr3 =>
    obtain ⟨perms', freshTag⟩ := pr3
    rw [h_ref_src] at h_step
    simp only [mirlite.resolvePlaceAcc, h_lookup_set] at h_step
    -- §5 the compiled statement, known before the mother lemma
    obtain ⟨dOut0, h_dval0⟩ := placeToRegChecked_ok_of_placeInputsMapped
      (cs := (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))]) dstLoc.idx.1 (Register.R csPrefix.nextReg, obseq.LayoutTy.PtrL τ))) (kind := RefKind.Shared)
      (placeInputsMapped_of_localBindingSim_resolvePlace h_lbs1
        (resolvePlace?_of_resolveAcc h_dres))
    obtain ⟨stmtOutC, h_stmtOutC⟩ :=
      (compileStmt_ref_fresh_derefsrc_lowers kind prot mask h_piD h_dval0).value
    obtain ⟨stmtOut, h_stmtOut⟩ := h_val0 csPrefix stmtOutC h_stmtOutC
    have h_stmtRun := (h_run0 csPrefix).trans
      ((compileStmt_ref_fresh_derefsrc_lowers kind prot mask h_piD h_dval0).run)
    have h_instS : ∀ q' instr,
        q' < (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (Place.deref P)) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))]) dstLoc.idx.1 (Register.R csPrefix.nextReg, obseq.LayoutTy.PtrL τ))).nextLabel →
        (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (Place.deref P)) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))]) dstLoc.idx.1 (Register.R csPrefix.nextReg, obseq.LayoutTy.PtrL τ))).code q' = some instr →
        compProg q' = some instr := by
      intro q' instr h_lt h_code
      refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
      · rw [h_stmtRun]
        simp only [emit_nextLabel, List.length_cons, List.length_nil]
        omega
      · rw [h_stmtRun]
        rw [emit_code_lt_nextLabel _ _ (by
          simp only [emit_nextLabel, List.length_cons, List.length_nil]; omega)]
        rw [emit_code_lt_nextLabel _ _ (by
          simp only [emit_nextLabel, List.length_cons, List.length_nil]; omega)]
        exact h_code
    -- §6 execute the root `Alloc`
    have h_code0 : compProg s_osea.pc
        = some (Instr.Assgn (Register.R csPrefix.nextReg)
            (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))) := by
      rw [h_pc]
      refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
      · rw [h_stmtRun]
        have h_le := (CheckedCompilerM.incr
          (placeToRegChecked RefKind.Shared (Place.deref P)) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))]) dstLoc.idx.1 (Register.R csPrefix.nextReg, obseq.LayoutTy.PtrL τ))).nextLabel_le
        simp only [emit_nextLabel, setPlaceInfo_nextLabel, List.length_cons,
            List.length_nil] at h_le ⊢
        omega
      · rw [h_stmtRun]
        rw [emit_code_lt_nextLabel _ _ (by
          have h_le := (CheckedCompilerM.incr
            (placeToRegChecked RefKind.Shared (Place.deref P)) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))]) dstLoc.idx.1 (Register.R csPrefix.nextReg, obseq.LayoutTy.PtrL τ))).nextLabel_le
          simp only [emit_nextLabel, setPlaceInfo_nextLabel, List.length_cons,
            List.length_nil] at h_le ⊢
          omega)]
        rw [emit_code_lt_nextLabel _ _ (by
          have h_le := (CheckedCompilerM.incr
            (placeToRegChecked RefKind.Shared (Place.deref P)) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))]) dstLoc.idx.1 (Register.R csPrefix.nextReg, obseq.LayoutTy.PtrL τ))).nextLabel_le
          simp only [emit_nextLabel, setPlaceInfo_nextLabel, List.length_cons,
            List.length_nil] at h_le ⊢
          omega)]
        rw [(CheckedCompilerM.incr
          (placeToRegChecked RefKind.Shared (Place.deref P)) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))]) dstLoc.idx.1 (Register.R csPrefix.nextReg, obseq.LayoutTy.PtrL τ))).code_eq _ (by
          simp only [emit_nextLabel, setPlaceInfo_nextLabel, List.length_cons,
            List.length_nil]
          omega)]
        show (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } _).code _ = _
        have h := emit_code_at_new { csPrefix with nextReg := csPrefix.nextReg + 1 }
          [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))] (k := 0) (by simp)
        simpa [setPlaceInfo] using h
    have h_runAlloc := runN_Assgn_Alloc_step compProg s_osea
      (Register.R csPrefix.nextReg) (layoutToTyVal (obseq.LayoutTy.PtrL τ)) h_code0 h_own_tgt'
    -- §7-§9 the SOURCE half as one package, from the post-Alloc states, at
    -- the nil projection: the chain is lowered Shared, the Borrow at `kind`
    have hFrag := (CodeIncluded.of_stmt h_comp h_csAt h_stmt h_stmtOut).fragmentOf
      (base := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (Place.deref P)) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))]) dstLoc.idx.1 (Register.R csPrefix.nextReg, obseq.LayoutTy.PtrL τ))).nextLabel)
      h_stmtRun rfl
    obtain ⟨nB, s_mid, sB, tgtPerms, hsB, rfl, h_incr_t2, h_wf_t', h_tbd', h_psim',
      h_runB, h_lbsB, h_pcB, h_dprm, h_dregmono, h_memB, -, h_rt_new2, h_nw_new,
      h_relB⟩ :=
      ref_chainsrc_borrow
        (ρa := ρa.extendBlock s_mir.mem.addrStart (blockSize (obseq.LayoutTy.PtrL τ)))
        (ρt := ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag)
        h_spine PathTo.nil RefKind.Shared kind prot mask compProg s1
        { s_osea with mem := (oseair.allocate s_osea.mem (obseq.typeSize (layoutToTyVal (obseq.LayoutTy.PtrL τ)))).2, perms := tgtP1, reg := oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg) (obseq.TyVal.PTy, [Val.Ptr s_osea.mem.addrStart 0 (obseq.typeSize (layoutToTyVal (obseq.LayoutTy.PtrL τ))) s_osea.perms.NextTag]), pc := s_osea.pc + 1 }
        (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))]) dstLoc.idx.1 (Register.R csPrefix.nextReg, obseq.LayoutTy.PtrL τ))
        h_id_a' h_wf1 (by rw [h_perms1]; exact h_tbd1) h_lbs1 h_prb1 h_smsA
        (by rw [h_perms1]; exact h_psim1)
        (by
          show s_osea.pc + 1 = _
          rw [h_pc]
          simp only [emit_nextLabel, setPlaceInfo_nextLabel, List.length_cons,
            List.length_nil])
        h_dres (by simpa using h_fit) (by simpa using h_ref_src)
        h_dval0 _ rfl h_instS (hFrag.instrAt 0 rfl rfl)
    have h_code2 : compProg sB.pc
        = some (Instr.RStore obseq.TyVal.PTy
            (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (Place.deref P)) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))]) dstLoc.idx.1 (Register.R csPrefix.nextReg, obseq.LayoutTy.PtrL τ))).nextReg) (Register.R csPrefix.nextReg)) := by
      rw [h_pcB]
      simp only [emit, List.length_cons, List.length_nil]
      exact hFrag.instrAt 1 rfl rfl
    -- §10-§11 the fresh-root WRITE seam, shared with copy
    exact copy_freshroot_write_after_read
      (τ := obseq.LayoutTy.PtrL τ)
      (sR := sB)
      (vreg := Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (Place.deref P)) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))]) dstLoc.idx.1 (Register.R csPrefix.nextReg, obseq.LayoutTy.PtrL τ))).nextReg)
      (vals := [Val.Ptr resolved.allocBase (resolved.addr - resolved.allocBase + pathOffset PathTo.nil) resolved.allocSize s_mid.perms.NextTag])
      (mvals := [mirlite.MemValue.ptrVal resolved.allocBase
        (resolved.addr + pathOffset PathTo.nil - resolved.allocBase) resolved.allocSize
        permsR.NextTag])
      compProg h_comp h_stmt h_csAt h_stmtOut h_sms h_unmap h_prb h_lookup_set
      h_env1 h_pc1 h_memstart1 h_find1 h_addr_eq h_sz h_runAlloc h_incr_a
      (TagRenameIncr.trans h_incr_t h_incr_t2) h_id_a' h_wf_t' h_ra_dom h_prb1
      h_runB
      (by simp only [emit]; exact h_dprm)
      (by simp only [emit]; exact Nat.le_trans h_dregmono (Nat.le_succ _))
      h_lbsB (by rw [hsB]; exact h_psim') (by rw [hsB]; exact h_tbd') h_memB h_pcB
      (by subst hsB; exact RegMap.lookup_insert_self _ _ _)
      (by simp [blockSize, obseq.layoutSize])
      h_stmtRun (by simp [blockSize, obseq.layoutSize]) (Nat.le_refl _) rfl rfl
      h_relB h_step
/-- REGIME L→P0 with a PROJ-TOPPED SOURCE: `dst.g := &kind s.f` at
    ZERO destination offset, both roots bound locals. The source
    projection costs only the `Borrow`'s offset operand, so this is
    `ref_projdst_local_simulation` with `pathOffset f` for `0` and the
    stored pointer covering the source base's WHOLE block. -/
theorem ref_projdst_projsrc_simulation
    {τ σ σb : LayoutTy}
    {dstLoc : Local Γ σ} {g : PathTo σ (obseq.LayoutTy.PtrL τ)}
    {srcLoc : Local Γ σb} {f : PathTo σb τ}
    {bD bS : mirlite.Binding}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (compProg : oseair.Prog)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    {stmt0 : Stmt Γ}
    (h_stmt : prog.get? s_mir.pc = some stmt0)
    (h_run0 : ∀ cs, CheckedCompilerM.run (compileStmtChecked stmt0) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.proj (.local dstLoc) g)
              (.ref kind prot mask (.proj (.local srcLoc) f)))) cs)
    (h_val0 : ∀ cs so, CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.proj (.local dstLoc) g)
            (.ref kind prot mask (.proj (.local srcLoc) f)))) cs
        = Except.ok so →
      ∃ so', CheckedCompilerM.value (compileStmtChecked stmt0) cs
        = Except.ok so')
    (h_envD : mirlite.Env.lookup s_mir.env dstLoc = some bD)
    (h_envS : mirlite.Env.lookup s_mir.env srcLoc = some bS)
    (h_step : mirlite.stepStmt MSB s_mir
      (.assign (.proj (.local dstLoc) g)
        (.ref kind prot mask (.proj (.local srcLoc) f))) = .ok s_mir') :
    ∃ (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa ρt' s_mir' s_osea' := by
  obtain ⟨csPrefix, ⟨h_csAt, h_pc⟩, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_tbd,
    h_alloc, h_unmap, h_prb⟩ := h_inv
  obtain ⟨dstReg, baseD, tagD, h_piD, h_entryD, h_raD, h_rtD, h_nwD, h_domD⟩ :=
    h_lbs dstLoc bD h_envD
  obtain ⟨srcReg, baseS, tagS, h_piS, h_entryS, h_raS, h_rtS, h_nwS, h_domS⟩ :=
    h_lbs srcLoc bS h_envS
  have h_baseD : baseD = bD.addr := (h_id_a _ _ h_raD).symm
  have h_baseS : baseS = bS.addr := (h_id_a _ _ h_raS).symm
  subst h_baseD
  subst h_baseS
  -- §1 invert the source: prepare no-op, dst resolves at the FIELD (offset
  -- 0), the retag succeeds, the pointer is written into the base block
  simp only [mirPrep, mirlite.stepStmt, mirlite.doAssign, mirlite.doAssignCont, h_envD,
    mirlite.resolvePlaceAcc, h_envS, mirlite.evalRExpr] at h_step
  rw [if_neg (Nat.not_lt.mpr (show bS.addr + pathOffset f + blockSize τ
      ≤ bS.addr + blockSize σb by
    have h_fit := PathTo.offset_add_size_le f
    simp only [Nat.add_assoc]
    exact Nat.add_le_add_left h_fit _))] at h_step
  cases h_ref_src : MSB.ref s_mir.perms (bS.addr + pathOffset f) (blockSize τ)
      bS.tag kind prot mask with
  | error e => rw [h_ref_src] at h_step; simp at h_step
  | ok pr =>
      obtain ⟨perms', freshTag⟩ := pr
      rw [h_ref_src] at h_step
      simp only at h_step
      -- §2 the retag on the target, with ρt extended at the fresh pair
      -- §3 the fragment and its two instructions
      have h_stmtRunC := (compileStmt_ref_projdst_projsrc_lowers (cs := csPrefix) (g := g) (f := f)
        kind prot mask h_piD h_piS).run
      have h_stmtRun := (h_run0 csPrefix).trans h_stmtRunC
      obtain ⟨stmtOutC, h_stmtOutC⟩ :=
        (compileStmt_ref_projdst_projsrc_lowers (cs := csPrefix) (g := g) (f := f) kind prot mask
          h_piD h_piS).value
      obtain ⟨stmtOut, h_stmtOut⟩ := h_val0 csPrefix stmtOutC h_stmtOutC
      have hFrag10 := ((CodeIncluded.of_stmt h_comp h_csAt h_stmt h_stmtOut).mono
        (by rw [h_stmtRun]; exact projDstTail_state_incr _ _ _ _ _ _)).fragmentOf
        rfl h_pc
      have h_code1 : compProg s_osea.pc
          = some (Instr.Assgn (Register.R csPrefix.nextReg)
              (Rhs.Borrow kind prot mask (blockSize τ) srcReg (pathOffset f))) :=
        hFrag10.instrAt 0 rfl rfl
      -- §4 the SOURCE package: the projected retag transported, the `Borrow`
      obtain ⟨tgtPerms, rfl, h_incr_t, h_wf_t', h_tbd', h_psim', h_run1, h_lbsB,
        h_pcB, h_relB⟩ :=
        ref_local_borrow τ σb kind prot mask (pathOffset f) compProg s_mir s_osea
          csPrefix h_id_a h_wf_t h_tbd h_lbs h_prb h_psim h_pc h_entryS h_raS
          h_rtS h_nwS h_domS (PathTo.offset_add_size_le f)
          (by simpa using h_ref_src) h_code1
      have h_rtD' : (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag) bD.tag
          = some tagD := h_incr_t _ _ h_rtD
      -- §5-§6 the BOUND-root PLAIN write seam
      simp only [h_envD] at h_step
      have h_regne : dstReg ≠ Register.R csPrefix.nextReg := by
        cases dstReg with
        | R n =>
            have h_lt := h_prb _ _ _ h_piD
            grind
      obtain ⟨s_osea', n, h_run, h_inv'⟩ :=
        copy_bound_write_after_read (τ := obseq.LayoutTy.PtrL τ)
          (dbase := bD.addr) (dtag := bD.tag) (dsize := blockSize σ)
          (csR := (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
            [Instr.Assgn (Register.R csPrefix.nextReg)
              (Rhs.Borrow kind prot mask (blockSize τ) srcReg (pathOffset f))]))
          (sR := { s_osea with
            perms := tgtPerms,
            reg := oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
              (obseq.TyVal.PTy, [Val.Ptr bS.addr (0 + pathOffset f) (blockSize σb) s_osea.perms.NextTag]),
            pc := s_osea.pc + 1 })
          (vreg := Register.R csPrefix.nextReg)
          (vals := [Val.Ptr bS.addr (0 + pathOffset f) (blockSize σb) s_osea.perms.NextTag])
          (mvals := [mirlite.MemValue.ptrVal bS.addr
            (bS.addr + pathOffset f - bS.addr) (blockSize σb) s_mir.perms.NextTag])
          compProg h_comp h_stmt h_csAt h_stmtOut h_id_a h_wf_t' h_unmap h_prb
          0 h_raD h_rtD' h_nwD h_domD (pathOffset g)
          (by simpa using PathTo.offset_add_size_le g) h_run1
          (by
            show oseair.RegMap.lookup _ _ = _
            rw [RegMap.lookup_insert_ne _ h_regne]
            exact h_entryD)
          (SourceMemSim.rename_mono (AddrRenameIncr.refl ρa) h_incr_t h_sms)
          h_alloc rfl (by simp only [emit]; exact Nat.le_succ _) h_lbsB h_psim'
          h_tbd' h_pcB (RegMap.lookup_insert_self _ _ _)
          (by show _ < _; simp only [emit]; exact Nat.lt_succ_self _)
          (by simp [blockSize, obseq.layoutSize])
          h_stmtRun
          (by simp [blockSize, obseq.layoutSize]) (by simp) rfl rfl rfl h_relB h_step
      exact ⟨_, s_osea', n, h_incr_t, h_run, h_inv'⟩
/-- REGIME B-proj for the DESTINATION with a PROJ-TOPPED SOURCE:
    `dst.g := &kind s.f` at ZERO destination offset, `dst`'s root
    UNBOUND. -/
theorem ref_proj_fresh_projsrc_simulation
    {τ σ σb : LayoutTy}
    {dstLoc : Local Γ σ} {g : PathTo σ (obseq.LayoutTy.PtrL τ)}
    {srcLoc : Local Γ σb} {f : PathTo σb τ}
    {bS : mirlite.Binding}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (compProg : oseair.Prog)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    {stmt0 : Stmt Γ}
    (h_stmt : prog.get? s_mir.pc = some stmt0)
    (h_run0 : ∀ cs, CheckedCompilerM.run (compileStmtChecked stmt0) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.proj (.local dstLoc) g)
              (.ref kind prot mask (.proj (.local srcLoc) f)))) cs)
    (h_val0 : ∀ cs so, CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.proj (.local dstLoc) g)
            (.ref kind prot mask (.proj (.local srcLoc) f)))) cs
        = Except.ok so →
      ∃ so', CheckedCompilerM.value (compileStmtChecked stmt0) cs
        = Except.ok so')
    (h_envD : mirlite.Env.lookup s_mir.env dstLoc = none)
    (h_envS : mirlite.Env.lookup s_mir.env srcLoc = some bS)
    (h_step : mirlite.stepStmt MSB s_mir
      (.assign (.proj (.local dstLoc) g) (.ref kind prot mask (.proj (.local srcLoc) f))) = .ok s_mir') :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' := by
  obtain ⟨csPrefix, ⟨h_csAt, h_pc⟩, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_tbd,
    h_alloc, h_unmap, h_prb⟩ := h_inv
  have h_piD : getPlaceInfo csPrefix dstLoc.idx.1 = none := h_unmap dstLoc h_envD
  obtain ⟨srcReg, baseS, tagS, h_piS, h_entryS, h_raS, h_rtS, h_nwS, h_domS⟩ :=
    h_lbs srcLoc bS h_envS
  have h_baseS : baseS = bS.addr := (h_id_a _ _ h_raS).symm
  subst h_baseS
  have h_idx_ne : srcLoc.idx ≠ dstLoc.idx := by
    intro h
    have hcontra : mirlite.Env.lookup s_mir.env dstLoc = some bS := by
      show s_mir.env dstLoc.idx = some bS
      rw [← h]; exact h_envS
    rw [h_envD] at hcontra
    exact absurd hcontra (by simp)
  -- §1 the destination allocation, via the shared fresh-root prologue: the
  -- projected destination's ROOT is what gets allocated
  simp only [mirlite.stepStmt, mirlite.doAssign] at h_step
  cases h_prep : mirlite.preparePlaceAssign MSB s_mir
      (Place.proj (Place.local dstLoc) g) with
  | err m => rw [h_prep] at h_step; simp at h_step
  | ok s1 =>
      rw [h_prep] at h_step
      rw [show mirlite.preparePlaceAssign MSB s_mir (Place.proj (Place.local dstLoc) g)
          = mirlite.allocateBase MSB s_mir dstLoc from by
        simp only [mirPrep, mirAlloc, h_envD]] at h_prep
      have h_incr_a : AddrRenameIncr ρa
          (ρa.extendBlock s_mir.mem.addrStart (blockSize σ)) :=
        AddrRenameIncr.extendBlock h_id_a _ _
      have h_id_a' : IdentityOnDomain
          (ρa.extendBlock s_mir.mem.addrStart (blockSize σ)) :=
        IdentityOnDomain.extendBlock h_id_a _ _
      have h_ra_base : (ρa.extendBlock s_mir.mem.addrStart (blockSize σ))
          s_mir.mem.addrStart = some s_mir.mem.addrStart :=
        AddrRenameMap.extendBlock_base _ _ _
      have h_ra_dom : ∀ k, k < blockSize σ →
          (ρa.extendBlock s_mir.mem.addrStart (blockSize σ))
            (s_mir.mem.addrStart + k) = some (s_mir.mem.addrStart + k) :=
        fun _ hk => AddrRenameMap.extendBlock_mem hk
      obtain ⟨permsOwned, tgtP1, h_own_tgt', h_perms1, h_pc1, h_env1,
        hD1, h_memstart1, h_find1, h_incr1, h_wf1, h_tbd1, h_psim1,
        h_erun, h_prb1, h_lbs1⟩ :=
        copy_freshroot_prologue h_envD h_prep h_id_a h_wf_t h_tbd h_psim h_alloc
          h_lbs h_prb h_piD h_incr_a h_id_a' h_ra_base h_ra_dom
      have h_addr_eq : s_osea.mem.addrStart = s_mir.mem.addrStart := h_alloc
      have h_szD : obseq.typeSize (layoutToTyVal σ) = blockSize σ :=
        obseq.typeSize_layoutToTyVal _
      -- §2 the source is untouched by the allocation; resolve and retag it
      have hS1 : mirlite.Env.lookup s1.env srcLoc = some bS := by
        rw [h_env1]
        simp only [mirlite.Env.lookup, mirlite.Env.set, if_neg h_idx_ne]
        exact h_envS
      simp only [mirlite.doAssignCont, mirlite.resolvePlaceAcc, hD1,
        mirlite.evalRExpr, hS1] at h_step
      rw [if_neg (Nat.not_lt.mpr (show bS.addr + pathOffset f + blockSize τ
          ≤ bS.addr + blockSize σb by
        have h_fit := PathTo.offset_add_size_le f
        simp only [Nat.add_assoc]
        exact Nat.add_le_add_left h_fit _))] at h_step
      cases h_ref_src : MSB.ref s1.perms (bS.addr + pathOffset f) (blockSize τ)
          bS.tag kind prot mask with
      | error e => rw [h_ref_src] at h_step; simp at h_step
      | ok pr2 =>
          obtain ⟨perms', tagR⟩ := pr2
          rw [h_ref_src] at h_step
          simp only at h_step
          have h_rtS1 := h_incr1 _ _ h_rtS
          have h_raS' := h_incr_a _ _ h_raS
          -- §7 the fragment: Alloc; Borrow; RStore
          have h_stmtRun := (h_run0 csPrefix).trans
            ((compileStmt_ref_proj_fresh_projsrc_lowers (cs := csPrefix)
              kind prot mask h_piD h_piS).run)
          obtain ⟨stmtOutC, h_stmtOutC⟩ :=
            (compileStmt_ref_proj_fresh_projsrc_lowers (cs := csPrefix) kind prot mask
              h_piD h_piS).value
          obtain ⟨stmtOut, h_stmtOut⟩ := h_val0 csPrefix stmtOutC h_stmtOutC
          have hFrag12 := ((CodeIncluded.of_stmt h_comp h_csAt h_stmt h_stmtOut).mono
            (by rw [h_stmtRun]; exact projDstTail_state_incr _ _ _ _ _ _)).fragmentOf
            rfl h_pc
          have h_code1 : compProg s_osea.pc
              = some (Instr.Assgn (Register.R csPrefix.nextReg)
                  (Rhs.Alloc (layoutToTyVal (σ)))) :=
            hFrag12.instrAt 0 rfl rfl
          have h_code2 : compProg (s_osea.pc + 1)
              = some (Instr.Assgn (Register.R (csPrefix.nextReg + 1))
                  (Rhs.Borrow kind prot mask (blockSize τ) srcReg (pathOffset f))) :=
            hFrag12.instrAt 1 rfl rfl
          -- §8 execute Alloc, then Borrow
          have h_run1 := runN_Assgn_Alloc_step compProg s_osea
            (Register.R csPrefix.nextReg) (layoutToTyVal (σ))
            h_code1 h_own_tgt'
          have h_regne : srcReg ≠ Register.R csPrefix.nextReg := by
            cases srcReg with
            | R n => have h_lt := h_prb _ _ _ h_piS; grind
          have h_entryS1 : PtrRegisterEntry
              (oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
                (obseq.TyVal.PTy, [Val.Ptr s_osea.mem.addrStart 0
                  (obseq.typeSize (layoutToTyVal (σ)))
                  s_osea.perms.NextTag]))
              srcReg bS.addr 0 (blockSize σb) tagS := by
            show oseair.RegMap.lookup _ _ = _
            rw [RegMap.lookup_insert_ne _ h_regne]
            exact h_entryS
          -- §8 the SOURCE half as the local-borrow package, from the post-Alloc
          -- states: the retag transport and the Borrow, at the field offset
          obtain ⟨tgtP2, rfl, h_incr2, h_wf2, h_tbd2, h_psim2, h_run2, h_lbsB, h_pcB,
            h_relB⟩ :=
            ref_local_borrow (ρa := ρa.extendBlock s_mir.mem.addrStart (blockSize σ))
              (ρt := ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag)
              τ σb kind prot mask (pathOffset f) compProg s1
              { s_osea with mem := (oseair.allocate s_osea.mem (obseq.typeSize (layoutToTyVal σ))).2, perms := tgtP1, reg := oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg) (obseq.TyVal.PTy, [Val.Ptr s_osea.mem.addrStart 0 (obseq.typeSize (layoutToTyVal σ)) s_osea.perms.NextTag]), pc := s_osea.pc + 1 }
              (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) dstLoc.idx.1 (Register.R csPrefix.nextReg, σ))
              h_id_a' h_wf1 (by rw [h_perms1]; exact h_tbd1) h_lbs1 h_prb1
              (by rw [h_perms1]; exact h_psim1)
              (by
                show s_osea.pc + 1 = _
                rw [h_pc]
                simp only [emit_nextLabel, setPlaceInfo_nextLabel, List.length_cons,
                  List.length_nil])
              h_entryS1 h_raS' h_rtS1 h_nwS
              (fun k hk => ⟨(h_domS k hk).choose,
                h_incr_a _ _ (h_domS k hk).choose_spec⟩)
              (PathTo.offset_add_size_le f) h_ref_src h_code2
          have h_incr12 := TagRenameIncr.trans h_incr1 h_incr2
          -- §9-§10 the fresh-root WRITE seam, shared with copy
          simp only [hD1] at h_step
          exact copy_fresh_write_after_read
            (τ := obseq.LayoutTy.PtrL τ)
            (csR := emit
              { (setPlaceInfo
                (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                  [Instr.Assgn (Register.R csPrefix.nextReg)
                    (Rhs.Alloc (layoutToTyVal σ))])
                dstLoc.idx.1 (Register.R csPrefix.nextReg, σ)) with
                nextReg := csPrefix.nextReg + 1 + 1 }
              [Instr.Assgn (Register.R (csPrefix.nextReg + 1))
                (Rhs.Borrow kind prot mask (blockSize τ) srcReg (pathOffset f))])
            (sR := { s_osea with
                mem := (oseair.allocate s_osea.mem
                  (obseq.typeSize (layoutToTyVal σ))).2,
                perms := tgtP2,
                reg := oseair.RegMap.insert
                  (oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
                    (obseq.TyVal.PTy, [Val.Ptr s_osea.mem.addrStart 0
                      (obseq.typeSize (layoutToTyVal σ)) s_osea.perms.NextTag]))
                  (Register.R (csPrefix.nextReg + 1))
                  (obseq.TyVal.PTy, [Val.Ptr bS.addr (0 + pathOffset f) (blockSize σb) tgtP1.NextTag]),
                pc := s_osea.pc + 1 + 1 })
            (vreg := Register.R (csPrefix.nextReg + 1))
            (vals := [Val.Ptr bS.addr (0 + pathOffset f) (blockSize σb) tgtP1.NextTag])
            (mvals := [mirlite.MemValue.ptrVal bS.addr
              (bS.addr + pathOffset f - bS.addr) (blockSize σb) s1.perms.NextTag])
            compProg h_comp h_stmt h_csAt
            h_stmtOut h_sms h_unmap h_prb hD1 h_env1 h_pc1 h_memstart1 h_find1
            h_addr_eq h_szD h_run1 h_incr_a h_incr12 h_id_a' h_wf2 h_ra_dom
            h_prb1 (pathOffset g) (PathTo.offset_add_size_le g) h_run2
            (by simp only [emit, setPlaceInfo])
            (by simp only [emit, setPlaceInfo]; omega)
            h_lbsB
            h_psim2 h_tbd2 rfl
            h_pcB
            (RegMap.lookup_insert_self _ _ _)
            (by show _ < _; simp only [emit, setPlaceInfo]; omega)
            (by simp [blockSize, obseq.layoutSize])
            h_stmtRun
            (by simp [blockSize, obseq.layoutSize]) rfl rfl rfl rfl
            h_relB
            h_step
/-- `t.g := &kind t.f` with `t` FRESH, at ZERO destination offset: the
    destination root is its OWN source root. The source binding is the
    one `allocateRoot` just made, so its register is the root register
    and every source fact comes from the extended renames rather than
    from `h_lbs` on the pre-state. -/
theorem ref_proj_fresh_selfsrc_simulation
    {τ σ : LayoutTy}
    {dstLoc : Local Γ σ} {g : PathTo σ (obseq.LayoutTy.PtrL τ)}
    {f : PathTo σ τ}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (compProg : oseair.Prog)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    {stmt0 : Stmt Γ}
    (h_stmt : prog.get? s_mir.pc = some stmt0)
    (h_run0 : ∀ cs, CheckedCompilerM.run (compileStmtChecked stmt0) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.proj (.local dstLoc) g)
              (.ref kind prot mask (.proj (.local dstLoc) f)))) cs)
    (h_val0 : ∀ cs so, CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.proj (.local dstLoc) g)
            (.ref kind prot mask (.proj (.local dstLoc) f)))) cs
        = Except.ok so →
      ∃ so', CheckedCompilerM.value (compileStmtChecked stmt0) cs
        = Except.ok so')
    (h_envD : mirlite.Env.lookup s_mir.env dstLoc = none)
    (h_step : mirlite.stepStmt MSB s_mir
      (.assign (.proj (.local dstLoc) g) (.ref kind prot mask (.proj (.local dstLoc) f))) = .ok s_mir') :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' := by
  obtain ⟨csPrefix, ⟨h_csAt, h_pc⟩, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_tbd,
    h_alloc, h_unmap, h_prb⟩ := h_inv
  have h_piD : getPlaceInfo csPrefix dstLoc.idx.1 = none := h_unmap dstLoc h_envD
  -- §1 the destination allocation, via the shared fresh-root prologue: the
  -- source borrows out of the very root the statement allocates
  simp only [mirlite.stepStmt, mirlite.doAssign] at h_step
  cases h_prep : mirlite.preparePlaceAssign MSB s_mir
      (Place.proj (Place.local dstLoc) g) with
  | err m => rw [h_prep] at h_step; simp at h_step
  | ok s1 =>
      rw [h_prep] at h_step
      rw [show mirlite.preparePlaceAssign MSB s_mir (Place.proj (Place.local dstLoc) g)
          = mirlite.allocateBase MSB s_mir dstLoc from by
        simp only [mirPrep, mirAlloc, h_envD]] at h_prep
      have h_incr_a : AddrRenameIncr ρa
          (ρa.extendBlock s_mir.mem.addrStart (blockSize σ)) :=
        AddrRenameIncr.extendBlock h_id_a _ _
      have h_id_a' : IdentityOnDomain
          (ρa.extendBlock s_mir.mem.addrStart (blockSize σ)) :=
        IdentityOnDomain.extendBlock h_id_a _ _
      have h_ra_base : (ρa.extendBlock s_mir.mem.addrStart (blockSize σ))
          s_mir.mem.addrStart = some s_mir.mem.addrStart :=
        AddrRenameMap.extendBlock_base _ _ _
      have h_ra_dom : ∀ k, k < blockSize σ →
          (ρa.extendBlock s_mir.mem.addrStart (blockSize σ))
            (s_mir.mem.addrStart + k) = some (s_mir.mem.addrStart + k) :=
        fun _ hk => AddrRenameMap.extendBlock_mem hk
      obtain ⟨permsOwned, tgtP1, h_own_tgt', h_perms1, h_pc1, h_env1,
        hD1, h_memstart1, h_find1, h_incr1, h_wf1, h_tbd1, h_psim1,
        h_erun, h_prb1, h_lbs1⟩ :=
        copy_freshroot_prologue h_envD h_prep h_id_a h_wf_t h_tbd h_psim h_alloc
          h_lbs h_prb h_piD h_incr_a h_id_a' h_ra_base h_ra_dom
      have h_addr_eq : s_osea.mem.addrStart = s_mir.mem.addrStart := h_alloc
      have h_szD : obseq.typeSize (layoutToTyVal σ) = blockSize σ :=
        obseq.typeSize_layoutToTyVal _
      -- §2 the source place is the root itself, at its own path offset
      simp only [mirlite.doAssignCont, mirlite.resolvePlaceAcc, hD1,
        mirlite.evalRExpr] at h_step
      rw [if_neg (Nat.not_lt.mpr (show s_mir.mem.addrStart + pathOffset f + blockSize τ
          ≤ s_mir.mem.addrStart + blockSize σ by
        have h_fit := PathTo.offset_add_size_le f
        simp only [Nat.add_assoc]
        exact Nat.add_le_add_left h_fit _))] at h_step
      cases h_ref_src : MSB.ref s1.perms (s_mir.mem.addrStart + pathOffset f)
          (blockSize τ) s_mir.perms.NextTag kind prot mask with
      | error e => rw [h_ref_src] at h_step; simp at h_step
      | ok pr2 =>
          obtain ⟨perms', tagR⟩ := pr2
          rw [h_ref_src] at h_step
          simp only at h_step
          -- the source binding IS the freshly allocated root
          have h_rtS1 : (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag)
              s_mir.perms.NextTag = some s_osea.perms.NextTag :=
            TagRenameMap.extend_self _ _ _
          have h0 : wildcardTag < s_mir.perms.NextTag := (h_tbd _ _ h_wf_t.2).1
          have h_nwD : (s_mir.perms.NextTag == wildcardTag) = false := by grind
          -- §7 the fragment: Alloc; Borrow; RStore
          have h_stmtRun := (h_run0 csPrefix).trans
            ((compileStmt_ref_proj_fresh_selfsrc_lowers (cs := csPrefix)
              kind prot mask h_piD).run)
          obtain ⟨stmtOutC, h_stmtOutC⟩ :=
            (compileStmt_ref_proj_fresh_selfsrc_lowers (cs := csPrefix) kind prot mask
              h_piD).value
          obtain ⟨stmtOut, h_stmtOut⟩ := h_val0 csPrefix stmtOutC h_stmtOutC
          have hFrag14 := ((CodeIncluded.of_stmt h_comp h_csAt h_stmt h_stmtOut).mono
            (by rw [h_stmtRun]; exact projDstTail_state_incr _ _ _ _ _ _)).fragmentOf
            rfl h_pc
          have h_code1 : compProg s_osea.pc
              = some (Instr.Assgn (Register.R csPrefix.nextReg)
                  (Rhs.Alloc (layoutToTyVal (σ)))) :=
            hFrag14.instrAt 0 rfl rfl
          have h_code2 : compProg (s_osea.pc + 1)
              = some (Instr.Assgn (Register.R (csPrefix.nextReg + 1))
                  (Rhs.Borrow kind prot mask (blockSize τ) (Register.R csPrefix.nextReg) (pathOffset f))) :=
            hFrag14.instrAt 1 rfl rfl
          -- §8 execute Alloc, then Borrow
          have h_run1 := runN_Assgn_Alloc_step compProg s_osea
            (Register.R csPrefix.nextReg) (layoutToTyVal (σ))
            h_code1 h_own_tgt'
          have h_entryS1 : PtrRegisterEntry
              (oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
                (obseq.TyVal.PTy, [Val.Ptr s_osea.mem.addrStart 0
                  (obseq.typeSize (layoutToTyVal (σ)))
                  s_osea.perms.NextTag]))
              (Register.R csPrefix.nextReg) s_mir.mem.addrStart 0 (blockSize σ)
              s_osea.perms.NextTag := by
            rw [← h_addr_eq, ← h_szD]
            show oseair.RegMap.lookup _ _ = _
            exact RegMap.lookup_insert_self _ _ _
          -- §8 the SOURCE half as the local-borrow package, from the post-Alloc
          -- states: the source binding IS the freshly allocated root
          obtain ⟨tgtP2, rfl, h_incr2, h_wf2, h_tbd2, h_psim2, h_run2, h_lbsB, h_pcB,
            h_relB⟩ :=
            ref_local_borrow (ρa := ρa.extendBlock s_mir.mem.addrStart (blockSize σ))
              (ρt := ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag)
              (bS := { addr := s_mir.mem.addrStart, tag := s_mir.perms.NextTag })
              τ σ kind prot mask (pathOffset f) compProg s1
              { s_osea with mem := (oseair.allocate s_osea.mem (obseq.typeSize (layoutToTyVal σ))).2, perms := tgtP1, reg := oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg) (obseq.TyVal.PTy, [Val.Ptr s_osea.mem.addrStart 0 (obseq.typeSize (layoutToTyVal σ)) s_osea.perms.NextTag]), pc := s_osea.pc + 1 }
              (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))]) dstLoc.idx.1 (Register.R csPrefix.nextReg, σ))
              h_id_a' h_wf1 (by rw [h_perms1]; exact h_tbd1) h_lbs1 h_prb1
              (by rw [h_perms1]; exact h_psim1)
              (by
                show s_osea.pc + 1 = _
                rw [h_pc]
                simp only [emit_nextLabel, setPlaceInfo_nextLabel, List.length_cons,
                  List.length_nil])
              h_entryS1 h_ra_base h_rtS1 h_nwD
              (fun k hk => ⟨s_mir.mem.addrStart + k, h_ra_dom k hk⟩)
              (PathTo.offset_add_size_le f) h_ref_src h_code2
          have h_incr12 := TagRenameIncr.trans h_incr1 h_incr2
          -- §9-§10 the fresh-root WRITE seam, shared with copy
          simp only [hD1] at h_step
          exact copy_fresh_write_after_read
            (τ := obseq.LayoutTy.PtrL τ)
            (csR := emit
              { (setPlaceInfo
                (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                  [Instr.Assgn (Register.R csPrefix.nextReg)
                    (Rhs.Alloc (layoutToTyVal σ))])
                dstLoc.idx.1 (Register.R csPrefix.nextReg, σ)) with
                nextReg := csPrefix.nextReg + 1 + 1 }
              [Instr.Assgn (Register.R (csPrefix.nextReg + 1))
                (Rhs.Borrow kind prot mask (blockSize τ)
                  (Register.R csPrefix.nextReg) (pathOffset f))])
            (sR := { s_osea with
                mem := (oseair.allocate s_osea.mem
                  (obseq.typeSize (layoutToTyVal σ))).2,
                perms := tgtP2,
                reg := oseair.RegMap.insert
                  (oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
                    (obseq.TyVal.PTy, [Val.Ptr s_osea.mem.addrStart 0
                      (obseq.typeSize (layoutToTyVal σ)) s_osea.perms.NextTag]))
                  (Register.R (csPrefix.nextReg + 1))
                  (obseq.TyVal.PTy, [Val.Ptr s_mir.mem.addrStart (0 + pathOffset f) (blockSize σ) tgtP1.NextTag]),
                pc := s_osea.pc + 1 + 1 })
            (vreg := Register.R (csPrefix.nextReg + 1))
            (vals := [Val.Ptr s_mir.mem.addrStart (0 + pathOffset f) (blockSize σ) tgtP1.NextTag])
            (mvals := [mirlite.MemValue.ptrVal s_mir.mem.addrStart
              (s_mir.mem.addrStart + pathOffset f - s_mir.mem.addrStart)
              (blockSize σ) s1.perms.NextTag])
            compProg h_comp h_stmt h_csAt
            h_stmtOut h_sms h_unmap h_prb hD1 h_env1 h_pc1 h_memstart1 h_find1
            h_addr_eq h_szD h_run1 h_incr_a h_incr12 h_id_a' h_wf2 h_ra_dom
            h_prb1 (pathOffset g) (PathTo.offset_add_size_le g) h_run2
            (by simp only [emit, setPlaceInfo])
            (by simp only [emit, setPlaceInfo]; omega)
            h_lbsB
            h_psim2 h_tbd2 rfl
            h_pcB
            (RegMap.lookup_insert_self _ _ _)
            (by show _ < _; simp only [emit, setPlaceInfo]; omega)
            (by simp [blockSize, obseq.layoutSize])
            h_stmtRun
            (by simp [blockSize, obseq.layoutSize]) rfl rfl rfl rfl
            h_relB
            h_step
/-- `dst := &kind (*p).f` with `dst` a BOUND local: a proj-topped
    source over a DEREF base. The chain lowers by the mother lemma
    exactly as for a plain deref source — `placeToRegChecked`'s deref
    arm ignores its `kind` — and the projection costs only the
    `Borrow`'s offset operand. -/
theorem ref_derefprojsrc_local_simulation
    {τ σb : LayoutTy}
    {dstLoc : Local Γ (obseq.LayoutTy.PtrL τ)}
    {P : Place Γ (obseq.LayoutTy.PtrL σb)} {f : PathTo σb τ}
    {bD : mirlite.Binding}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (compProg : oseair.Prog)
    (h_spine : PtrChain (Place.deref P))
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    {stmt0 : Stmt Γ}
    (h_stmt : prog.get? s_mir.pc = some stmt0)
    (h_run0 : ∀ cs, CheckedCompilerM.run (compileStmtChecked stmt0) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.local dstLoc) (.ref kind prot mask (.proj (.deref P) f)))) cs)
    (h_val0 : ∀ cs so, CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.local dstLoc) (.ref kind prot mask (.proj (.deref P) f)))) cs
        = Except.ok so →
      ∃ so', CheckedCompilerM.value (compileStmtChecked stmt0) cs
        = Except.ok so')
    (h_envD : mirlite.Env.lookup s_mir.env dstLoc = some bD)
    (h_step : mirlite.stepStmt MSB s_mir
      (.assign (.local dstLoc) (.ref kind prot mask (.proj (.deref P) f))) = .ok s_mir') :
    ∃ (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa ρt' s_mir' s_osea' := by
  obtain ⟨csPrefix, ⟨h_csAt, h_pc⟩, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_tbd,
    h_alloc, h_unmap, h_prb⟩ := h_inv
  obtain ⟨dstReg, baseD, tagD, h_piD, h_entryD, h_raD, h_rtD, h_nwD, -⟩ :=
    h_lbs dstLoc bD h_envD
  have h_baseD : baseD = bD.addr := (h_id_a _ _ h_raD).symm
  subst h_baseD
  -- §1 invert: prepare is a no-op (bound dst); the rhs resolves the
  -- WHOLE src place ACC-style (kept opaque), checks the retag range,
  -- and mints
  simp only [mirlite.stepStmt, mirlite.doAssign] at h_step
  cases h_prep : mirlite.preparePlaceAssign MSB s_mir (Place.local dstLoc) with
  | err msg => rw [h_prep] at h_step; simp at h_step
  | ok s1 =>
  rw [h_prep] at h_step
  have h_s1 : s1 = s_mir := by
    simp only [mirPrep, h_envD] at h_prep
    grind
  rw [h_s1] at h_step
  simp only [mirlite.evalRExpr] at h_step
  cases h_dres : mirlite.resolvePlaceAcc MSB s_mir (Place.deref P) with
  | error e =>
      rw [resolvePlaceAcc_proj_base_err (path := f) h_dres] at h_step
      simp at h_step
  | ok pr =>
  obtain ⟨resolved, permsR⟩ := pr
  rw [resolvePlaceAcc_proj_base_ok (path := f) h_dres] at h_step
  simp only at h_step
  by_cases h_fit : resolved.addr + PathTo.offset f + blockSize τ
      > resolved.allocBase + resolved.allocSize
  · rw [if_pos h_fit] at h_step
    simp at h_step
  · rw [if_neg h_fit] at h_step
    cases h_ref_src : MSB.ref permsR (resolved.addr + PathTo.offset f) (blockSize τ)
        resolved.tag kind prot mask with
    | error e => rw [h_ref_src] at h_step; simp at h_step
    | ok pr2 =>
    obtain ⟨perms', freshTag⟩ := pr2
    rw [h_ref_src] at h_step
    simp only [mirlite.resolvePlaceAcc, h_envD] at h_step
    -- §2 compiler scaffolding: the statement's run is known BEFORE the
    -- mother lemma (the run lemma needs only the value's ok-ness)
    have h_mapped : PlaceInputsMapped csPrefix (Place.deref P) :=
      placeInputsMapped_of_localBindingSim_resolvePlace h_lbs
        (resolvePlace?_of_resolveAcc h_dres)
    obtain ⟨dOut, h_dval⟩ := placeToRegChecked_ok_of_placeInputsMapped
      (cs := csPrefix) (kind := kind) h_mapped
    obtain ⟨stmtOutC, h_stmtOutC⟩ :=
      (compileStmt_ref_derefprojsrc_lowers kind prot mask h_piD h_dval).value
    obtain ⟨stmtOut, h_stmtOut⟩ := h_val0 csPrefix stmtOutC h_stmtOutC
    have h_stmtRun := (h_run0 csPrefix).trans
      ((compileStmt_ref_derefprojsrc_lowers kind prot mask h_piD h_dval).run)
    have h_instS : ∀ q' instr,
        q' < (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) csPrefix).nextLabel →
        (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) csPrefix).code q' = some instr →
        compProg q' = some instr := by
      intro q' instr h_lt h_code
      refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
      · rw [h_stmtRun]
        simp only [emit, List.length_cons, List.length_nil]
        omega
      · rw [h_stmtRun]
        rw [emit_code_lt_nextLabel _ _ (by
          simp only [emit, List.length_cons, List.length_nil]; omega)]
        rw [emit_code_lt_nextLabel _ _ (by
          simp only [emit, List.length_cons, List.length_nil]; omega)]
        exact h_code
    -- §3-§5 the SOURCE half as one package: the chain lowering, the retag
    -- transport and the Borrow
    have hFrag := (CodeIncluded.of_stmt h_comp h_csAt h_stmt h_stmtOut).fragmentOf
      (base := (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) csPrefix).nextLabel)
      h_stmtRun rfl
    obtain ⟨nB, s_mid, sB, tgtPerms, hsB, rfl, h_incr_t, h_wf_t', h_tbd', h_psim',
      h_runB, h_lbsB, h_pcB, h_dprm, h_dregmono, h_memB, -, h_rt_new, h_nw_new,
      h_relB⟩ :=
      ref_chainsrc_borrow h_spine f kind kind prot mask compProg s_mir s_osea csPrefix
        h_id_a h_wf_t h_tbd h_lbs h_prb h_sms h_psim h_pc h_dres h_fit h_ref_src
        h_dval _ rfl h_instS (hFrag.instrAt 0 rfl rfl)
    -- §6 the destination binding at the post-Borrow state
    obtain ⟨dstReg2, baseD2, tagD2, h_piD2, h_entryD2, h_raD2, h_rtD2, h_nwD2,
      h_domD⟩ := (LocalBindingSim.placeRegMap_congr (cs' := csPrefix)
        (by simp only [emit]; exact h_dprm.symm) h_lbsB) dstLoc bD h_envD
    have h_dr2 : dstReg2 = dstReg := by grind
    have h_baseD2 : baseD2 = bD.addr := (h_id_a _ _ h_raD2).symm
    rw [h_dr2, h_baseD2] at h_entryD2
    rw [h_baseD2] at h_raD2
    have h_code2 : compProg sB.pc
        = some (Instr.RStore obseq.TyVal.PTy
            (Register.R (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) csPrefix).nextReg) dstReg) := by
      rw [h_pcB]
      simp only [emit, List.length_cons, List.length_nil]
      exact hFrag.instrAt 1 rfl rfl
    -- §7 the BOUND-root PLAIN write seam
    obtain ⟨s_osea', n, h_run, h_inv'⟩ :=
      copy_boundplain_write_after_read (τ := obseq.LayoutTy.PtrL τ)
        (dbase := bD.addr) (dtag := bD.tag)
        (dsize := blockSize (obseq.LayoutTy.PtrL τ))
        (sR := sB)
        (vreg := Register.R (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) csPrefix).nextReg)
        (vals := [Val.Ptr resolved.allocBase
          (resolved.addr - resolved.allocBase + pathOffset f) resolved.allocSize
          s_mid.perms.NextTag])
        (mvals := [mirlite.MemValue.ptrVal resolved.allocBase
          (resolved.addr + pathOffset f - resolved.allocBase) resolved.allocSize
          permsR.NextTag])
        compProg h_comp h_stmt h_csAt h_stmtOut h_id_a h_wf_t' h_unmap h_prb
        0 h_raD2 h_rtD2 h_nwD2 h_domD h_runB h_entryD2
        (by rw [h_memB]
            exact SourceMemSim.rename_mono (AddrRenameIncr.refl ρa) h_incr_t h_sms)
        (by rw [h_memB]; exact h_alloc)
        (by simp only [emit]; exact h_dprm)
        (by simp only [emit]; exact Nat.le_trans h_dregmono (Nat.le_succ _))
        h_lbsB (by rw [hsB]; exact h_psim') (by rw [hsB]; exact h_tbd') h_pcB
        (by subst hsB; exact RegMap.lookup_insert_self _ _ _)
        (by simp [blockSize, obseq.layoutSize])
        (by simp [blockSize, obseq.layoutSize])
        h_code2
        (by rw [h_pcB, h_stmtRun]; simp [emit])
        (by rw [h_stmtRun]; simp only [emit]; try exact h_dprm)
        (by rw [h_stmtRun]; simp only [emit]; omega)
        (by simp [blockSize, obseq.layoutSize]) (by simp) rfl rfl rfl h_relB h_step
    exact ⟨_, s_osea', n, h_incr_t, h_run, h_inv'⟩
/-- `dst := &kind (*p).f` with `dst`'s root UNBOUND: the fresh-root
    chain-source leaf with the projection folded into the `Borrow`'s
    offset operand. -/
theorem ref_fresh_derefprojsrc_simulation
    {τ σb : LayoutTy}
    {dstLoc : Local Γ (obseq.LayoutTy.PtrL τ)}
    {P : Place Γ (obseq.LayoutTy.PtrL σb)} {f : PathTo σb τ}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (compProg : oseair.Prog)
    (h_spine : PtrChain (Place.deref P))
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    {stmt0 : Stmt Γ}
    (h_stmt : prog.get? s_mir.pc = some stmt0)
    (h_run0 : ∀ cs, CheckedCompilerM.run (compileStmtChecked stmt0) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.local dstLoc) (.ref kind prot mask (.proj (.deref P) f)))) cs)
    (h_val0 : ∀ cs so, CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.local dstLoc) (.ref kind prot mask (.proj (.deref P) f)))) cs
        = Except.ok so →
      ∃ so', CheckedCompilerM.value (compileStmtChecked stmt0) cs
        = Except.ok so')
    (h_envD : mirlite.Env.lookup s_mir.env dstLoc = none)
    (h_step : mirlite.stepStmt MSB s_mir
      (.assign (.local dstLoc) (.ref kind prot mask (.proj (.deref P) f))) = .ok s_mir') :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' := by
  obtain ⟨csPrefix, ⟨h_csAt, h_pc⟩, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_tbd,
    h_alloc, h_unmap, h_prb⟩ := h_inv
  have h_piD : getPlaceInfo csPrefix dstLoc.idx.1 = none := h_unmap dstLoc h_envD
  -- §1 the destination root is allocated on both machines, via the shared
  -- fresh-root prologue
  simp only [mirlite.stepStmt, mirlite.doAssign] at h_step
  cases h_prep : mirlite.preparePlaceAssign MSB s_mir (Place.local dstLoc) with
  | err m => rw [h_prep] at h_step; simp at h_step
  | ok s1 =>
  rw [h_prep] at h_step
  rw [show mirlite.preparePlaceAssign MSB s_mir (Place.local dstLoc)
      = mirlite.allocateBase MSB s_mir dstLoc from by
    simp only [mirPrep, mirAlloc, h_envD]] at h_prep
  have h_incr_a : AddrRenameIncr ρa
      (ρa.extendBlock s_mir.mem.addrStart (blockSize (obseq.LayoutTy.PtrL τ))) :=
    AddrRenameIncr.extendBlock h_id_a _ _
  have h_id_a' : IdentityOnDomain
      (ρa.extendBlock s_mir.mem.addrStart (blockSize (obseq.LayoutTy.PtrL τ))) :=
    IdentityOnDomain.extendBlock h_id_a _ _
  have h_ra_base : (ρa.extendBlock s_mir.mem.addrStart (blockSize (obseq.LayoutTy.PtrL τ)))
      s_mir.mem.addrStart = some s_mir.mem.addrStart :=
    AddrRenameMap.extendBlock_base _ _ _
  have h_ra_dom : ∀ k, k < blockSize (obseq.LayoutTy.PtrL τ) →
      (ρa.extendBlock s_mir.mem.addrStart (blockSize (obseq.LayoutTy.PtrL τ)))
        (s_mir.mem.addrStart + k) = some (s_mir.mem.addrStart + k) :=
    fun _ hk => AddrRenameMap.extendBlock_mem hk
  obtain ⟨permsOwned, tgtP1, h_own_tgt', h_perms1, h_pc1, h_env1,
    h_lookup_set, h_memstart1, h_find1, h_incr_t, h_wf1, h_tbd1, h_psim1,
    h_erun, h_prb1, h_lbs1⟩ :=
    copy_freshroot_prologue h_envD h_prep h_id_a h_wf_t h_tbd h_psim h_alloc
      h_lbs h_prb h_piD h_incr_a h_id_a' h_ra_base h_ra_dom
  -- §2 the facts the source mother will want, at the post-`Alloc` states
  have h_addr_eq : s_osea.mem.addrStart = s_mir.mem.addrStart := h_alloc
  have h_sz : obseq.typeSize (layoutToTyVal (obseq.LayoutTy.PtrL τ)) = blockSize (obseq.LayoutTy.PtrL τ) :=
    obseq.typeSize_layoutToTyVal _
  have h_rt_new : (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag)
      s_mir.perms.NextTag = some s_osea.perms.NextTag :=
    TagRenameMap.extend_self _ _ _
  have h0 : wildcardTag < s_mir.perms.NextTag := (h_tbd _ _ h_wf_t.2).1
  have h_nw : (s_mir.perms.NextTag == wildcardTag) = false := by grind
  have h_smsA : SourceMemSim
      (ρa.extendBlock s_mir.mem.addrStart (blockSize (obseq.LayoutTy.PtrL τ)))
      (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag)
      s1.mem (oseair.allocate s_osea.mem
        (obseq.typeSize (layoutToTyVal (obseq.LayoutTy.PtrL τ)))).2 := by
    intro a v h_find
    rw [h_find1] at h_find
    exact SourceMemSim.rename_mono h_incr_a h_incr_t h_sms a v h_find
  have h_pi_new : getPlaceInfo (setPlaceInfo
      (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
        [Instr.Assgn (Register.R csPrefix.nextReg)
          (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))])
      dstLoc.idx.1 (Register.R csPrefix.nextReg, (obseq.LayoutTy.PtrL τ))) dstLoc.idx.1
      = some (Register.R csPrefix.nextReg, (obseq.LayoutTy.PtrL τ)) :=
    getPlaceInfo_setPlaceInfo_self _ _ _
  -- §4 the rhs resolves on the POST-allocation state, kept opaque
  simp only [mirlite.evalRExpr] at h_step
  cases h_dres : mirlite.resolvePlaceAcc MSB s1 (Place.deref P) with
  | error e =>
      rw [resolvePlaceAcc_proj_base_err (path := f) h_dres] at h_step
      simp at h_step
  | ok pr2 =>
  obtain ⟨resolved, permsR⟩ := pr2
  rw [resolvePlaceAcc_proj_base_ok (path := f) h_dres] at h_step
  simp only at h_step
  by_cases h_fit : resolved.addr + PathTo.offset f + blockSize τ
      > resolved.allocBase + resolved.allocSize
  · rw [if_pos h_fit] at h_step
    simp at h_step
  · rw [if_neg h_fit] at h_step
    cases h_ref_src : MSB.ref permsR (resolved.addr + PathTo.offset f) (blockSize τ)
        resolved.tag kind prot mask with
    | error e => rw [h_ref_src] at h_step; simp at h_step
    | ok pr3 =>
    obtain ⟨perms', freshTag⟩ := pr3
    rw [h_ref_src] at h_step
    simp only [mirlite.resolvePlaceAcc, h_lookup_set] at h_step
    -- §5 the compiled statement, known before the mother lemma
    obtain ⟨dOut0, h_dval0⟩ := placeToRegChecked_ok_of_placeInputsMapped
      (cs := (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))]) dstLoc.idx.1 (Register.R csPrefix.nextReg, obseq.LayoutTy.PtrL τ))) (kind := kind)
      (placeInputsMapped_of_localBindingSim_resolvePlace h_lbs1
        (resolvePlace?_of_resolveAcc h_dres))
    obtain ⟨stmtOutC, h_stmtOutC⟩ :=
      (compileStmt_ref_fresh_derefprojsrc_lowers kind prot mask h_piD h_dval0).value
    obtain ⟨stmtOut, h_stmtOut⟩ := h_val0 csPrefix stmtOutC h_stmtOutC
    have h_stmtRun := (h_run0 csPrefix).trans
      ((compileStmt_ref_fresh_derefprojsrc_lowers kind prot mask h_piD h_dval0).run)
    have h_instS : ∀ q' instr,
        q' < (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))]) dstLoc.idx.1 (Register.R csPrefix.nextReg, obseq.LayoutTy.PtrL τ))).nextLabel →
        (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))]) dstLoc.idx.1 (Register.R csPrefix.nextReg, obseq.LayoutTy.PtrL τ))).code q' = some instr →
        compProg q' = some instr := by
      intro q' instr h_lt h_code
      refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
      · rw [h_stmtRun]
        simp only [emit_nextLabel, List.length_cons, List.length_nil]
        omega
      · rw [h_stmtRun]
        rw [emit_code_lt_nextLabel _ _ (by
          simp only [emit_nextLabel, List.length_cons, List.length_nil]; omega)]
        rw [emit_code_lt_nextLabel _ _ (by
          simp only [emit_nextLabel, List.length_cons, List.length_nil]; omega)]
        exact h_code
    -- §6 execute the root `Alloc`
    have h_code0 : compProg s_osea.pc
        = some (Instr.Assgn (Register.R csPrefix.nextReg)
            (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))) := by
      rw [h_pc]
      refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
      · rw [h_stmtRun]
        have h_le := (CheckedCompilerM.incr
          (placeToRegChecked kind (Place.deref P)) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))]) dstLoc.idx.1 (Register.R csPrefix.nextReg, obseq.LayoutTy.PtrL τ))).nextLabel_le
        simp only [emit_nextLabel, setPlaceInfo_nextLabel, List.length_cons,
            List.length_nil] at h_le ⊢
        omega
      · rw [h_stmtRun]
        rw [emit_code_lt_nextLabel _ _ (by
          have h_le := (CheckedCompilerM.incr
            (placeToRegChecked kind (Place.deref P)) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))]) dstLoc.idx.1 (Register.R csPrefix.nextReg, obseq.LayoutTy.PtrL τ))).nextLabel_le
          simp only [emit_nextLabel, setPlaceInfo_nextLabel, List.length_cons,
            List.length_nil] at h_le ⊢
          omega)]
        rw [emit_code_lt_nextLabel _ _ (by
          have h_le := (CheckedCompilerM.incr
            (placeToRegChecked kind (Place.deref P)) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))]) dstLoc.idx.1 (Register.R csPrefix.nextReg, obseq.LayoutTy.PtrL τ))).nextLabel_le
          simp only [emit_nextLabel, setPlaceInfo_nextLabel, List.length_cons,
            List.length_nil] at h_le ⊢
          omega)]
        rw [(CheckedCompilerM.incr
          (placeToRegChecked kind (Place.deref P)) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))]) dstLoc.idx.1 (Register.R csPrefix.nextReg, obseq.LayoutTy.PtrL τ))).code_eq _ (by
          simp only [emit_nextLabel, setPlaceInfo_nextLabel, List.length_cons,
            List.length_nil]
          omega)]
        show (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } _).code _ = _
        have h := emit_code_at_new { csPrefix with nextReg := csPrefix.nextReg + 1 }
          [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))] (k := 0) (by simp)
        simpa [setPlaceInfo] using h
    have h_runAlloc := runN_Assgn_Alloc_step compProg s_osea
      (Register.R csPrefix.nextReg) (layoutToTyVal (obseq.LayoutTy.PtrL τ)) h_code0 h_own_tgt'
    -- §7-§9 the SOURCE half as one package, from the post-Alloc states
    have hFrag := (CodeIncluded.of_stmt h_comp h_csAt h_stmt h_stmtOut).fragmentOf
      (base := (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))]) dstLoc.idx.1 (Register.R csPrefix.nextReg, obseq.LayoutTy.PtrL τ))).nextLabel)
      h_stmtRun rfl
    obtain ⟨nB, s_mid, sB, tgtPerms, hsB, rfl, h_incr_t2, h_wf_t', h_tbd', h_psim',
      h_runB, h_lbsB, h_pcB, h_dprm, h_dregmono, h_memB, -, h_rt_new2, h_nw_new,
      h_relB⟩ :=
      ref_chainsrc_borrow
        (ρa := ρa.extendBlock s_mir.mem.addrStart (blockSize (obseq.LayoutTy.PtrL τ)))
        (ρt := ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag)
        h_spine f kind kind prot mask compProg s1
        { s_osea with mem := (oseair.allocate s_osea.mem (obseq.typeSize (layoutToTyVal (obseq.LayoutTy.PtrL τ)))).2, perms := tgtP1, reg := oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg) (obseq.TyVal.PTy, [Val.Ptr s_osea.mem.addrStart 0 (obseq.typeSize (layoutToTyVal (obseq.LayoutTy.PtrL τ))) s_osea.perms.NextTag]), pc := s_osea.pc + 1 }
        (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))]) dstLoc.idx.1 (Register.R csPrefix.nextReg, obseq.LayoutTy.PtrL τ))
        h_id_a' h_wf1 (by rw [h_perms1]; exact h_tbd1) h_lbs1 h_prb1 h_smsA
        (by rw [h_perms1]; exact h_psim1)
        (by
          show s_osea.pc + 1 = _
          rw [h_pc]
          simp only [emit_nextLabel, setPlaceInfo_nextLabel, List.length_cons,
            List.length_nil])
        h_dres h_fit h_ref_src h_dval0 _ rfl h_instS (hFrag.instrAt 0 rfl rfl)
    have h_code2 : compProg sB.pc
        = some (Instr.RStore obseq.TyVal.PTy
            (Register.R (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))]) dstLoc.idx.1 (Register.R csPrefix.nextReg, obseq.LayoutTy.PtrL τ))).nextReg) (Register.R csPrefix.nextReg)) := by
      rw [h_pcB]
      simp only [emit, List.length_cons, List.length_nil]
      exact hFrag.instrAt 1 rfl rfl
    -- §10-§11 the fresh-root WRITE seam, shared with copy
    exact copy_freshroot_write_after_read
      (τ := obseq.LayoutTy.PtrL τ)
      (sR := sB)
      (vreg := Register.R (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))]) dstLoc.idx.1 (Register.R csPrefix.nextReg, obseq.LayoutTy.PtrL τ))).nextReg)
      (vals := [Val.Ptr resolved.allocBase (resolved.addr - resolved.allocBase + pathOffset f) resolved.allocSize s_mid.perms.NextTag])
      (mvals := [mirlite.MemValue.ptrVal resolved.allocBase
        (resolved.addr + pathOffset f - resolved.allocBase) resolved.allocSize
        permsR.NextTag])
      compProg h_comp h_stmt h_csAt h_stmtOut h_sms h_unmap h_prb h_lookup_set
      h_env1 h_pc1 h_memstart1 h_find1 h_addr_eq h_sz h_runAlloc h_incr_a
      (TagRenameIncr.trans h_incr_t h_incr_t2) h_id_a' h_wf_t' h_ra_dom h_prb1
      h_runB
      (by simp only [emit]; exact h_dprm)
      (by simp only [emit]; exact Nat.le_trans h_dregmono (Nat.le_succ _))
      h_lbsB (by rw [hsB]; exact h_psim') (by rw [hsB]; exact h_tbd') h_memB h_pcB
      (by subst hsB; exact RegMap.lookup_insert_self _ _ _)
      (by simp [blockSize, obseq.layoutSize])
      h_stmtRun (by simp [blockSize, obseq.layoutSize]) (Nat.le_refl _) rfl rfl
      h_relB h_step
/-- A CHAIN source under a PROJECTED destination at ZERO offset, both
    roots bound locals: `dst.g := &kind (*p).f`. The destination has no
    spine — at zero offset its lowering IS the root register — so only
    the source needs the mother lemma, and the plain `&kind *p` is the
    `pathOffset f = 0` instance. -/
theorem ref_projdst_derefsrc_simulation
    {τ σ σb : LayoutTy}
    {dstLoc : Local Γ σ} {g : PathTo σ (obseq.LayoutTy.PtrL τ)}
    {P : Place Γ (obseq.LayoutTy.PtrL σb)} {f : PathTo σb τ}
    {bD : mirlite.Binding}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (compProg : oseair.Prog)
    (h_spine : PtrChain (Place.deref P))
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    {stmt0 : Stmt Γ}
    (h_stmt : prog.get? s_mir.pc = some stmt0)
    (h_run0 : ∀ cs, CheckedCompilerM.run (compileStmtChecked stmt0) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.proj (.local dstLoc) g) (.ref kind prot mask (.proj (.deref P) f)))) cs)
    (h_val0 : ∀ cs so, CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.proj (.local dstLoc) g) (.ref kind prot mask (.proj (.deref P) f)))) cs
        = Except.ok so →
      ∃ so', CheckedCompilerM.value (compileStmtChecked stmt0) cs
        = Except.ok so')
    (h_envD : mirlite.Env.lookup s_mir.env dstLoc = some bD)
    (h_step : mirlite.stepStmt MSB s_mir
      (.assign (.proj (.local dstLoc) g) (.ref kind prot mask (.proj (.deref P) f))) = .ok s_mir') :
    ∃ (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa ρt' s_mir' s_osea' := by
  obtain ⟨csPrefix, ⟨h_csAt, h_pc⟩, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_tbd,
    h_alloc, h_unmap, h_prb⟩ := h_inv
  obtain ⟨dstReg, baseD, tagD, h_piD, h_entryD, h_raD, h_rtD, h_nwD, -⟩ :=
    h_lbs dstLoc bD h_envD
  have h_baseD : baseD = bD.addr := (h_id_a _ _ h_raD).symm
  subst h_baseD
  -- §1 invert: prepare is a no-op (bound dst); the rhs resolves the
  -- WHOLE src place ACC-style (kept opaque), checks the retag range,
  -- and mints
  simp only [mirlite.stepStmt, mirlite.doAssign] at h_step
  cases h_prep : mirlite.preparePlaceAssign MSB s_mir (Place.proj (Place.local dstLoc) g) with
  | err msg => rw [h_prep] at h_step; simp at h_step
  | ok s1 =>
  rw [h_prep] at h_step
  have h_s1 : s1 = s_mir := by
    simp only [mirPrep, h_envD] at h_prep
    grind
  rw [h_s1] at h_step
  simp only [mirlite.evalRExpr] at h_step
  cases h_dres : mirlite.resolvePlaceAcc MSB s_mir (Place.deref P) with
  | error e =>
      rw [resolvePlaceAcc_proj_base_err (path := f) h_dres] at h_step
      simp at h_step
  | ok pr =>
  obtain ⟨resolved, permsR⟩ := pr
  rw [resolvePlaceAcc_proj_base_ok (path := f) h_dres] at h_step
  simp only at h_step
  by_cases h_fit : resolved.addr + PathTo.offset f + blockSize τ
      > resolved.allocBase + resolved.allocSize
  · rw [if_pos h_fit] at h_step
    simp at h_step
  · rw [if_neg h_fit] at h_step
    cases h_ref_src : MSB.ref permsR (resolved.addr + PathTo.offset f) (blockSize τ)
        resolved.tag kind prot mask with
    | error e => rw [h_ref_src] at h_step; simp at h_step
    | ok pr2 =>
    obtain ⟨perms', freshTag⟩ := pr2
    rw [h_ref_src] at h_step
    simp only [mirlite.resolvePlaceAcc, h_envD] at h_step
    -- §2 compiler scaffolding: the statement's run is known BEFORE the
    -- mother lemma (the run lemma needs only the value's ok-ness)
    have h_mapped : PlaceInputsMapped csPrefix (Place.deref P) :=
      placeInputsMapped_of_localBindingSim_resolvePlace h_lbs
        (resolvePlace?_of_resolveAcc h_dres)
    obtain ⟨dOut, h_dval⟩ := placeToRegChecked_ok_of_placeInputsMapped
      (cs := csPrefix) (kind := kind) h_mapped
    have h_dclean0 := placeToRegChecked_deref_cleanup h_dval
    have h_prm0 := (PtrChain.placeToRegChecked_placeRegMap h_spine) kind csPrefix
    obtain ⟨stmtOutC, h_stmtOutC⟩ :=
      (compileStmt_ref_projdst_derefsrc_lowers kind prot mask h_piD h_dval
        h_dclean0 h_prm0).value
    obtain ⟨stmtOut, h_stmtOut⟩ := h_val0 csPrefix stmtOutC h_stmtOutC
    have h_stmtRun := (h_run0 csPrefix).trans
      ((compileStmt_ref_projdst_derefsrc_lowers kind prot mask h_piD h_dval
        h_dclean0 h_prm0).run)
    -- the statement's code seen from the post-chain and post-source-Borrow
    -- prefixes of its tower
    have hInc := CodeIncluded.of_stmt h_comp h_csAt h_stmt h_stmtOut
    have h_incrB : StateIncr
        (emit { (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) csPrefix) with nextReg := (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) csPrefix).nextReg + 1 }
          [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) csPrefix).nextReg)
            (Rhs.Borrow kind prot mask (blockSize τ) dOut.result.reg (pathOffset f))])
        (CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix) := by
      rw [h_stmtRun]; exact projDstTail_state_incr _ _ _ _ _ _
    have h_instS := hInc.mono
      (StateIncr.trans (StateIncr.trans (freshReg_state_incr _) (emit_state_incr _ _)) h_incrB)
    -- §3-§5 the SOURCE half as one package: the chain lowering, the retag
    -- transport and the Borrow; the fragment is stated at the post-chain
    -- label, so the package never has to expose the mother's state
    have hFrag := (hInc.mono h_incrB).fragmentOf (base := (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) csPrefix).nextLabel) rfl rfl
    obtain ⟨nB, s_mid, sB, tgtPerms, hsB, rfl, h_incr_t, h_wf_t', h_tbd', h_psim',
      h_runB, h_lbsB, h_pcB, h_dprm, h_dregmono, h_memB, -, h_rt_new, h_nw_new,
      h_relB⟩ :=
      ref_chainsrc_borrow h_spine f kind kind prot mask compProg s_mir s_osea csPrefix
        h_id_a h_wf_t h_tbd h_lbs h_prb h_sms h_psim h_pc h_dres h_fit h_ref_src
        h_dval _ rfl h_instS (hFrag.instrAt 0 rfl rfl)
    -- §6 the destination binding at the post-Borrow state, read off the
    -- package's LocalBindingSim transported back to the prefix
    obtain ⟨dstReg2, baseD2, tagD2, h_piD2, h_entryD2, h_raD2, h_rtD2, h_nwD2,
      h_domD⟩ := (LocalBindingSim.placeRegMap_congr (cs' := csPrefix)
        (by simp only [emit]; exact h_dprm.symm) h_lbsB) dstLoc bD h_envD
    have h_dr2 : dstReg2 = dstReg := by grind
    have h_baseD2 : baseD2 = bD.addr := (h_id_a _ _ h_raD2).symm
    rw [h_dr2, h_baseD2] at h_entryD2
    rw [h_baseD2] at h_raD2
    -- §7 the BOUND-root write seam, at the projection's offset
    obtain ⟨s_osea', n, h_run, h_inv'⟩ :=
      copy_bound_write_after_read (τ := obseq.LayoutTy.PtrL τ)
        (dbase := bD.addr) (dtag := bD.tag) (dsize := blockSize σ)
        (sR := sB)
        (vreg := Register.R (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) csPrefix).nextReg)
        (vals := [Val.Ptr resolved.allocBase
          (resolved.addr - resolved.allocBase + pathOffset f) resolved.allocSize
          s_mid.perms.NextTag])
        (mvals := [mirlite.MemValue.ptrVal resolved.allocBase
          (resolved.addr + pathOffset f - resolved.allocBase) resolved.allocSize
          permsR.NextTag])
        compProg h_comp h_stmt h_csAt h_stmtOut h_id_a h_wf_t' h_unmap h_prb
        0 h_raD2 h_rtD2 h_nwD2 h_domD (pathOffset g)
        (by simpa using PathTo.offset_add_size_le g)
        h_runB h_entryD2
        (by rw [h_memB]
            exact SourceMemSim.rename_mono (AddrRenameIncr.refl ρa) h_incr_t h_sms)
        (by rw [h_memB]; exact h_alloc)
        (by simp only [emit]; exact h_dprm)
        (by simp only [emit]; exact Nat.le_trans h_dregmono (Nat.le_succ _))
        h_lbsB (by rw [hsB]; exact h_psim') (by rw [hsB]; exact h_tbd') h_pcB
        (by subst hsB; exact RegMap.lookup_insert_self _ _ _)
        (by show _ < _; simp only [emit]; exact Nat.lt_succ_self _)
        (by simp [blockSize, obseq.layoutSize])
        h_stmtRun
        (by simp [blockSize, obseq.layoutSize]) (by simp) rfl rfl rfl h_relB h_step
    exact ⟨_, s_osea', n, h_incr_t, h_run, h_inv'⟩
/-- A CHAIN source under a FRESH projected destination at ZERO offset:
    `dst.g := &kind (*p).f` with `dst`'s root unbound. The σ-sized root
    `Alloc` of regime B-proj, and the source spine after it. -/
theorem ref_proj_fresh_derefsrc_simulation
    {τ σ σb : LayoutTy}
    {dstLoc : Local Γ σ} {g : PathTo σ (obseq.LayoutTy.PtrL τ)}
    {P : Place Γ (obseq.LayoutTy.PtrL σb)} {f : PathTo σb τ}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (compProg : oseair.Prog)
    (h_spine : PtrChain (Place.deref P))
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    {stmt0 : Stmt Γ}
    (h_stmt : prog.get? s_mir.pc = some stmt0)
    (h_run0 : ∀ cs, CheckedCompilerM.run (compileStmtChecked stmt0) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.proj (.local dstLoc) g) (.ref kind prot mask (.proj (.deref P) f)))) cs)
    (h_val0 : ∀ cs so, CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.proj (.local dstLoc) g) (.ref kind prot mask (.proj (.deref P) f)))) cs
        = Except.ok so →
      ∃ so', CheckedCompilerM.value (compileStmtChecked stmt0) cs
        = Except.ok so')
    (h_envD : mirlite.Env.lookup s_mir.env dstLoc = none)
    (h_step : mirlite.stepStmt MSB s_mir
      (.assign (.proj (.local dstLoc) g) (.ref kind prot mask (.proj (.deref P) f))) = .ok s_mir') :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' := by
  obtain ⟨csPrefix, ⟨h_csAt, h_pc⟩, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_tbd,
    h_alloc, h_unmap, h_prb⟩ := h_inv
  have h_piD : getPlaceInfo csPrefix dstLoc.idx.1 = none := h_unmap dstLoc h_envD
  -- §1 the destination root is allocated on both machines, via the shared
  -- fresh-root prologue
  simp only [mirlite.stepStmt, mirlite.doAssign] at h_step
  cases h_prep : mirlite.preparePlaceAssign MSB s_mir
      (Place.proj (Place.local dstLoc) g) with
  | err m => rw [h_prep] at h_step; simp at h_step
  | ok s1 =>
  rw [h_prep] at h_step
  rw [show mirlite.preparePlaceAssign MSB s_mir (Place.proj (Place.local dstLoc) g)
      = mirlite.allocateBase MSB s_mir dstLoc from by
    simp only [mirPrep, mirAlloc, h_envD]] at h_prep
  have h_incr_a : AddrRenameIncr ρa
      (ρa.extendBlock s_mir.mem.addrStart (blockSize σ)) :=
    AddrRenameIncr.extendBlock h_id_a _ _
  have h_id_a' : IdentityOnDomain
      (ρa.extendBlock s_mir.mem.addrStart (blockSize σ)) :=
    IdentityOnDomain.extendBlock h_id_a _ _
  have h_ra_base : (ρa.extendBlock s_mir.mem.addrStart (blockSize σ))
      s_mir.mem.addrStart = some s_mir.mem.addrStart :=
    AddrRenameMap.extendBlock_base _ _ _
  have h_ra_dom : ∀ k, k < blockSize σ →
      (ρa.extendBlock s_mir.mem.addrStart (blockSize σ))
        (s_mir.mem.addrStart + k) = some (s_mir.mem.addrStart + k) :=
    fun _ hk => AddrRenameMap.extendBlock_mem hk
  obtain ⟨permsOwned, tgtP1, h_own_tgt', h_perms1, h_pc1, h_env1,
    h_lookup_set, h_memstart1, h_find1, h_incr_t, h_wf1, h_tbd1, h_psim1,
    h_erun, h_prb1, h_lbs1⟩ :=
    copy_freshroot_prologue h_envD h_prep h_id_a h_wf_t h_tbd h_psim h_alloc
      h_lbs h_prb h_piD h_incr_a h_id_a' h_ra_base h_ra_dom
  -- §2 the facts the source mother will want, at the post-`Alloc` states
  have h_addr_eq : s_osea.mem.addrStart = s_mir.mem.addrStart := h_alloc
  have h_sz : obseq.typeSize (layoutToTyVal σ) = blockSize σ :=
    obseq.typeSize_layoutToTyVal _
  have h_rt_new : (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag)
      s_mir.perms.NextTag = some s_osea.perms.NextTag :=
    TagRenameMap.extend_self _ _ _
  have h0 : wildcardTag < s_mir.perms.NextTag := (h_tbd _ _ h_wf_t.2).1
  have h_nw : (s_mir.perms.NextTag == wildcardTag) = false := by grind
  have h_smsA : SourceMemSim
      (ρa.extendBlock s_mir.mem.addrStart (blockSize σ))
      (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag)
      s1.mem (oseair.allocate s_osea.mem
        (obseq.typeSize (layoutToTyVal σ))).2 := by
    intro a v h_find
    rw [h_find1] at h_find
    exact SourceMemSim.rename_mono h_incr_a h_incr_t h_sms a v h_find
  have h_pi_new : getPlaceInfo (setPlaceInfo
      (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
        [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
      dstLoc.idx.1 (Register.R csPrefix.nextReg, σ)) dstLoc.idx.1
      = some (Register.R csPrefix.nextReg, σ) :=
    getPlaceInfo_setPlaceInfo_self _ _ _
  -- §4 the rhs resolves on the POST-allocation state, kept opaque
  simp only [mirlite.evalRExpr] at h_step
  cases h_dres : mirlite.resolvePlaceAcc MSB s1 (Place.deref P) with
  | error e =>
      rw [resolvePlaceAcc_proj_base_err (path := f) h_dres] at h_step
      simp at h_step
  | ok pr2 =>
  obtain ⟨resolved, permsR⟩ := pr2
  rw [resolvePlaceAcc_proj_base_ok (path := f) h_dres] at h_step
  simp only at h_step
  by_cases h_fit : resolved.addr + PathTo.offset f + blockSize τ
      > resolved.allocBase + resolved.allocSize
  · rw [if_pos h_fit] at h_step
    simp at h_step
  · rw [if_neg h_fit] at h_step
    cases h_ref_src : MSB.ref permsR (resolved.addr + PathTo.offset f) (blockSize τ)
        resolved.tag kind prot mask with
    | error e => rw [h_ref_src] at h_step; simp at h_step
    | ok pr3 =>
    obtain ⟨perms', freshTag⟩ := pr3
    rw [h_ref_src] at h_step
    simp only [mirlite.resolvePlaceAcc, h_lookup_set] at h_step
    -- §5 the compiled statement, known before the mother lemma
    obtain ⟨dOut0, h_dval0⟩ := placeToRegChecked_ok_of_placeInputsMapped
      (cs := (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal (σ)))]) dstLoc.idx.1 (Register.R csPrefix.nextReg, σ))) (kind := kind)
      (placeInputsMapped_of_localBindingSim_resolvePlace h_lbs1
        (resolvePlace?_of_resolveAcc h_dres))
    have h_dclean0 := placeToRegChecked_deref_cleanup h_dval0
    have h_prm0 := (PtrChain.placeToRegChecked_placeRegMap h_spine) kind
      (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal (σ)))]) dstLoc.idx.1 (Register.R csPrefix.nextReg, σ))
    obtain ⟨stmtOutC, h_stmtOutC⟩ :=
      (compileStmt_ref_proj_fresh_derefsrc_lowers kind prot mask h_piD h_dval0
        h_dclean0 h_prm0).value
    obtain ⟨stmtOut, h_stmtOut⟩ := h_val0 csPrefix stmtOutC h_stmtOutC
    have h_stmtRun := (h_run0 csPrefix).trans
      ((compileStmt_ref_proj_fresh_derefsrc_lowers kind prot mask h_piD h_dval0
        h_dclean0 h_prm0).run)
    -- the statement's code, seen from three prefixes of its tower: the
    -- post-Alloc state (the Alloc itself), the post-chain state (the
    -- chain's own code, for the mother), and the post-source-Borrow state
    have hInc := CodeIncluded.of_stmt h_comp h_csAt h_stmt h_stmtOut
    have h_incrB : StateIncr
        (emit { (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal (σ)))]) dstLoc.idx.1 (Register.R csPrefix.nextReg, σ))) with nextReg := (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal (σ)))]) dstLoc.idx.1 (Register.R csPrefix.nextReg, σ))).nextReg + 1 }
          [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal (σ)))]) dstLoc.idx.1 (Register.R csPrefix.nextReg, σ))).nextReg)
            (Rhs.Borrow kind prot mask (blockSize τ) dOut0.result.reg (pathOffset f))])
        (CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix) := by
      rw [h_stmtRun]; exact projDstTail_state_incr _ _ _ _ _ _
    have h_incrD : StateIncr (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal (σ)))]) dstLoc.idx.1 (Register.R csPrefix.nextReg, σ)))
        (CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix) :=
      StateIncr.trans (StateIncr.trans (freshReg_state_incr _) (emit_state_incr _ _)) h_incrB
    have h_instS := hInc.mono h_incrD
    -- §6 execute the root `Alloc`
    have hFragA := (hInc.mono (StateIncr.trans (CheckedCompilerM.incr _ _) h_incrD)).fragmentOf
      (base := csPrefix.nextLabel) rfl rfl
    have h_code0 : compProg s_osea.pc
        = some (Instr.Assgn (Register.R csPrefix.nextReg)
            (Rhs.Alloc (layoutToTyVal (σ)))) := by
      rw [h_pc]; exact hFragA.instrAt 0 rfl rfl
    have h_runAlloc := runN_Assgn_Alloc_step compProg s_osea
      (Register.R csPrefix.nextReg) (layoutToTyVal (σ)) h_code0 h_own_tgt'
    -- §7-§9 the SOURCE half as one package, from the post-Alloc states: the
    -- chain lowering, the retag transport and the source Borrow
    have hFrag := (hInc.mono h_incrB).fragmentOf (base := (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal (σ)))]) dstLoc.idx.1 (Register.R csPrefix.nextReg, σ))).nextLabel) rfl rfl
    obtain ⟨nB, s_mid, sB, tgtPerms, hsB, rfl, h_incr_t2, h_wf_t', h_tbd', h_psim',
      h_runB, h_lbsB, h_pcB, h_dprm, h_dregmono, h_memB, -, h_rt_new2, h_nw_new,
      h_relB⟩ :=
      ref_chainsrc_borrow (ρa := ρa.extendBlock s_mir.mem.addrStart (blockSize σ))
        (ρt := ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag)
        h_spine f kind kind prot mask compProg s1
        { s_osea with mem := (oseair.allocate s_osea.mem (obseq.typeSize (layoutToTyVal (σ)))).2, perms := tgtP1, reg := oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg) (obseq.TyVal.PTy, [Val.Ptr s_osea.mem.addrStart 0 (obseq.typeSize (layoutToTyVal (σ))) s_osea.perms.NextTag]), pc := s_osea.pc + 1 }
        (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal (σ)))]) dstLoc.idx.1 (Register.R csPrefix.nextReg, σ))
        h_id_a' h_wf1 (by rw [h_perms1]; exact h_tbd1) h_lbs1 h_prb1 h_smsA
        (by rw [h_perms1]; exact h_psim1)
        (by
          show s_osea.pc + 1 = _
          rw [h_pc]
          simp only [emit_nextLabel, setPlaceInfo_nextLabel, List.length_cons,
            List.length_nil])
        h_dres h_fit h_ref_src h_dval0 _ rfl h_instS (hFrag.instrAt 0 rfl rfl)
    -- §10-§11 the fresh WRITE seam, at the projection's offset
    exact copy_fresh_write_after_read
      (τ := obseq.LayoutTy.PtrL τ)
      (sR := sB)
      (vreg := Register.R (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal (σ)))]) dstLoc.idx.1 (Register.R csPrefix.nextReg, σ))).nextReg)
      (vals := [Val.Ptr resolved.allocBase (resolved.addr - resolved.allocBase + pathOffset f) resolved.allocSize s_mid.perms.NextTag])
      (mvals := [mirlite.MemValue.ptrVal resolved.allocBase
        (resolved.addr + pathOffset f - resolved.allocBase) resolved.allocSize
        permsR.NextTag])
      compProg h_comp h_stmt h_csAt h_stmtOut h_sms h_unmap h_prb h_lookup_set
      h_env1 h_pc1 h_memstart1 h_find1 h_addr_eq h_sz h_runAlloc h_incr_a
      (TagRenameIncr.trans h_incr_t h_incr_t2) h_id_a' h_wf_t' h_ra_dom h_prb1
      (pathOffset g) (PathTo.offset_add_size_le g) h_runB
      (by simp only [emit]; exact h_dprm)
      (by simp only [emit]; exact Nat.le_trans h_dregmono (Nat.le_succ _))
      h_lbsB (by rw [hsB]; exact h_psim') (by rw [hsB]; exact h_tbd') h_memB h_pcB
      (by subst hsB; exact RegMap.lookup_insert_self _ _ _)
      (by show _ < _; simp only [emit]; omega)
      (by simp [blockSize, obseq.layoutSize])
      h_stmtRun
      (by simp [blockSize, obseq.layoutSize]) rfl rfl rfl rfl h_relB h_step
theorem ref_derefdst_projsrc_simulation
    {τ σb : LayoutTy}
    {P : Place Γ (obseq.LayoutTy.PtrL (obseq.LayoutTy.PtrL τ))}
    {srcLoc : Local Γ σb} {f : PathTo σb τ}
    {bS : mirlite.Binding}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (compProg : oseair.Prog)
    (h_spine : PtrChain (Place.deref P))
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    {stmt0 : Stmt Γ}
    (h_stmt : prog.get? s_mir.pc = some stmt0)
    (h_run0 : ∀ cs, CheckedCompilerM.run (compileStmtChecked stmt0) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.deref P) (.ref kind prot mask (.proj (.local srcLoc) f)))) cs)
    (h_val0 : ∀ cs so, CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.deref P) (.ref kind prot mask (.proj (.local srcLoc) f)))) cs
        = Except.ok so →
      ∃ so', CheckedCompilerM.value (compileStmtChecked stmt0) cs
        = Except.ok so')
    (h_envS : mirlite.Env.lookup s_mir.env srcLoc = some bS)
    (h_step : mirlite.stepStmt MSB s_mir
      (.assign (.deref P) (.ref kind prot mask (.proj (.local srcLoc) f))) = .ok s_mir') :
    ∃ (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa ρt' s_mir' s_osea' := by
  obtain ⟨csPrefix, ⟨h_csAt, h_pc⟩, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_tbd,
    h_alloc, h_unmap, h_prb⟩ := h_inv
  obtain ⟨srcReg, baseS, tagS, h_piS, h_entryS, h_raS, h_rtS, h_nwS, h_domS⟩ :=
    h_lbs srcLoc bS h_envS
  have h_baseS : baseS = bS.addr := (h_id_a _ _ h_raS).symm
  subst h_baseS
  -- §1 invert: prepare is the identity on a resolvable deref root
  simp only [mirlite.stepStmt, mirlite.doAssign] at h_step
  cases h_prep : mirlite.preparePlaceAssign MSB s_mir (Place.deref P) with
  | err msg => simp [h_prep] at h_step
  | ok s1 =>
  simp only [h_prep] at h_step
  have h_pre : s1 = s_mir ∧
      ∃ r0, mirlite.resolvePlace? s_mir (Place.deref P) = some r0 := by
    simp only [mirlite.preparePlaceAssign] at h_prep
    split at h_prep
    · rename_i r0 h_r0
      cases h_prep
      exact ⟨rfl, r0, h_r0⟩
    · simp [mirlite.allocateRoot] at h_prep
  obtain ⟨h_s1, r0, h_resolved⟩ := h_pre
  rw [h_s1] at h_step
  -- §2 the rhs retag mints on the source FIRST (Rust order); the src's
  -- local resolution reduces WITHOUT unfolding the dst's resolveAcc
  simp only [mirlite.evalRExpr,
    resolvePlaceAcc_proj_base_ok (path := f) (resolvePlaceAcc_local h_envS)] at h_step
  rw [if_neg (Nat.not_lt.mpr (show bS.addr + PathTo.offset f + blockSize τ
      ≤ bS.addr + blockSize σb by
    have h_fit := PathTo.offset_add_size_le f
    simp only [Nat.add_assoc]
    exact Nat.add_le_add_left h_fit _))] at h_step
  cases h_ref_src : MSB.ref s_mir.perms (bS.addr + PathTo.offset f) (blockSize τ)
      bS.tag kind prot mask with
  | error e => rw [h_ref_src] at h_step; simp at h_step
  | ok pr =>
  obtain ⟨perms1, mintS⟩ := pr
  rw [h_ref_src] at h_step
  simp only at h_step
  -- §3 the WHOLE dst resolves on the POST-retag state (kept opaque)
  cases h_dres : mirlite.resolvePlaceAcc MSB
      { s_mir with perms := perms1 } (Place.deref P) with
  | error e => rw [h_dres] at h_step; simp at h_step
  | ok pr2 =>
  obtain ⟨resolved, permsD⟩ := pr2
  rw [h_dres] at h_step
  simp only at h_step
  -- §5 compiler-side scaffolding: the post-Borrow LocalBindingSim feeds
  -- both the mapped-ness of the dst at cs1 and the mother lemma
  have h_mapped : PlaceInputsMapped csPrefix (Place.deref P) :=
    placeInputsMapped_of_localBindingSim_resolvePlace h_lbs h_resolved
  have h_root := ensurePlaceRoot_run_eq_of_mapped h_mapped
  obtain ⟨dOut0, h_dval0⟩ := placeToRegChecked_ok_of_placeInputsMapped
    (cs := emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
      [Instr.Assgn (Register.R csPrefix.nextReg)
        (Rhs.Borrow kind prot mask (blockSize τ) srcReg (pathOffset f))])
    (kind := RefKind.Mut)
    (PlaceInputsMapped.placeRegMap_congr (by simp only [emit]) _ h_mapped)
  obtain ⟨stmtOutC, h_stmtOutC⟩ :=
    compileStmt_ref_derefdst_projsrc_value kind prot mask h_root h_piS rfl h_dval0
  obtain ⟨stmtOut, h_stmtOut⟩ := h_val0 csPrefix stmtOutC h_stmtOutC
  obtain ⟨h_lprun, placeOutL, h_lpval, h_lpres⟩ :=
    placeToRegChecked_local_existing (kind := kind) h_piS
  have h_incr2 : StateIncr
      (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (Place.deref P))
      (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
        [Instr.Assgn (Register.R csPrefix.nextReg)
          (Rhs.Borrow kind prot mask (blockSize τ) srcReg (pathOffset f))]))
      (CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix) := by
    rw [h_run0]
    simp only [csCompile, csMonad, placeToBorrowRegChecked, h_root, h_lprun, h_lpval, h_lpres]
    simp only [csRun]
    simp only [csMonad, h_dval0]
    exact StateIncr.trans (emit_state_incr _ _)
      (StateIncr.trans (emit_state_incr _ _) (emit_state_incr _ _))
  have h_instD :=
    (CodeIncluded.of_stmt h_comp h_csAt h_stmt h_stmtOut).mono h_incr2
  -- §6 execute the Borrow (the rhs, FIRST)
  have h_incr_cs1 : StateIncr
      (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
        [Instr.Assgn (Register.R csPrefix.nextReg)
          (Rhs.Borrow kind prot mask (blockSize τ) srcReg (pathOffset f))])
      (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (Place.deref P))
      (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
        [Instr.Assgn (Register.R csPrefix.nextReg)
          (Rhs.Borrow kind prot mask (blockSize τ) srcReg (pathOffset f))])) :=
    CheckedCompilerM.incr _ _
  have h_lt_cs1 : csPrefix.nextLabel
      < (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
          [Instr.Assgn (Register.R csPrefix.nextReg)
            (Rhs.Borrow kind prot mask (blockSize τ) srcReg (pathOffset f))]).nextLabel := by
    simp only [emit, List.length_cons, List.length_nil]
    omega
  have h_code1 : compProg s_osea.pc
      = some (Instr.Assgn (Register.R csPrefix.nextReg)
          (Rhs.Borrow kind prot mask (blockSize τ) srcReg (pathOffset f))) := by
    rw [h_pc]
    refine h_instD _ _ (Nat.lt_of_lt_of_le h_lt_cs1 h_incr_cs1.nextLabel_le) ?_
    rw [h_incr_cs1.code_eq _ h_lt_cs1]
    have h := emit_code_at_new { csPrefix with nextReg := csPrefix.nextReg + 1 }
      [Instr.Assgn (Register.R csPrefix.nextReg)
        (Rhs.Borrow kind prot mask (blockSize τ) srcReg (pathOffset f))] (k := 0) (by simp)
    simpa using h
  -- the SOURCE package: the projected retag transported, the `Borrow`
  -- executed, and the post-`Borrow` binding simulation
  obtain ⟨tgtP1, rfl, h_incr_t, h_wf_t', h_tbd', h_psim', h_run1, h_lbs1,
    h_pc1, h_relB⟩ :=
    ref_local_borrow τ σb kind prot mask (pathOffset f) compProg s_mir s_osea
      csPrefix h_id_a h_wf_t h_tbd h_lbs h_prb h_psim h_pc h_entryS h_raS h_rtS
      h_nwS h_domS (PathTo.offset_add_size_le f) (by simpa using h_ref_src)
      h_code1
  -- §7 the WHOLE dst lowering via the mother lemma, from the
  -- post-Borrow state under the extended rename
  have h_prb1 : PlaceRegMapBound
      (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
        [Instr.Assgn (Register.R csPrefix.nextReg)
          (Rhs.Borrow kind prot mask (blockSize τ) srcReg (pathOffset f))]) := by
    intro idx reg'' τ'' h_look
    refine RegisterBelow.mono ?_ (h_prb _ _ _ h_look)
    simp only [emit]
    exact Nat.le_succ _
  have h_sms1 : SourceMemSim ρa
      (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag)
      s_mir.mem s_osea.mem :=
    SourceMemSim.rename_mono (AddrRenameIncr.refl ρa) h_incr_t h_sms
  -- §7-§9: the shared chain-write seam (spine.lean)
  obtain ⟨s_osea', n, h_run, h_inv'⟩ :=
    copy_chainwrite_after_read (τ := obseq.LayoutTy.PtrL τ)
      (csR := emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
        [Instr.Assgn (Register.R csPrefix.nextReg)
          (Rhs.Borrow kind prot mask (blockSize τ) srcReg (pathOffset f))])
      (sR := { s_osea with
          perms := tgtP1,
          reg := oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
            (obseq.TyVal.PTy,
              [Val.Ptr bS.addr (0 + pathOffset f) (blockSize σb) s_osea.perms.NextTag]),
          pc := s_osea.pc + 1 })
      (vreg := Register.R csPrefix.nextReg)
      (vals := [Val.Ptr bS.addr (0 + pathOffset f) (blockSize σb) s_osea.perms.NextTag])
      (mvals := [mirlite.MemValue.ptrVal bS.addr (bS.addr + pathOffset f - bS.addr)
        (blockSize σb) s_mir.perms.NextTag])
      compProg h_spine h_comp h_stmt h_csAt
      h_stmtOut h_id_a h_wf_t' h_sms1 h_alloc h_unmap h_prb
      h_dres rfl h_step
      h_run1
      rfl
      (by simp only [emit]; exact Nat.le_succ _)
      h_lbs1 h_psim' h_tbd'
      rfl
      h_pc1
      (RegMap.lookup_insert_self _ _ _)
      (by show _ < _; simp only [emit]; exact Nat.lt_succ_self _)
      rfl
      h_relB
      h_instD
      (fun dOut h_dval h_dclean => (h_run0 csPrefix).trans
        (compileStmt_ref_derefdst_projsrc_run kind prot mask h_root h_piS rfl
          h_dval h_dclean))
  exact ⟨_, s_osea', n, h_incr_t, h_run, h_inv'⟩

/-- TWO MOTHERS: `*D := &kind (*P).f`, a chain SOURCE under a chain
    DESTINATION — the one shape needing two `ptrChain_lowering_sim`
    applications in a single statement.

    Rust order runs the retag first, and so does the compiler: the
    SOURCE chain lowers at `kind` from the prefix state (its deref arm
    ignores the kind), one `Borrow` at the projection's offset mints the
    reference, and only THEN does the DESTINATION chain lower at `Mut` —
    from the post-`Borrow` state, under the ρt extended by the mint,
    with its register-frame conjunct carrying the borrow temp across.
    One `RStore` (BRIDGE 2) writes the reference through the loaded tag.

    Both lowerings leave an empty cleanup (`placeToRegChecked`'s deref
    arm), so no `Die` is emitted and BRIDGE 1 is not needed. That also
    makes the whole compiled shape available up front
    (`compileStmt_ref_derefdst_derefprojsrc_run` needs only the two
    values and the destination's empty cleanup), which is what keeps the
    three code-inclusion obligations to one `StateIncr` step each
    instead of copy's towers.

    By the nil-projection eta this leaf also closes
    `*D := &kind *P`. -/
theorem ref_derefdst_derefprojsrc_simulation
    {τ σb : LayoutTy}
    {D : Place Γ (obseq.LayoutTy.PtrL (obseq.LayoutTy.PtrL τ))}
    {P : Place Γ (obseq.LayoutTy.PtrL σb)} {f : PathTo σb τ}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (compProg : oseair.Prog)
    (h_dchain : PtrChain (Place.deref D))
    (h_schain : PtrChain (Place.deref P))
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    {stmt0 : Stmt Γ}
    (h_stmt : prog.get? s_mir.pc = some stmt0)
    (h_run0 : ∀ cs, CheckedCompilerM.run (compileStmtChecked stmt0) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.deref D) (.ref kind prot mask (.proj (.deref P) f)))) cs)
    (h_val0 : ∀ cs so, CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.deref D) (.ref kind prot mask (.proj (.deref P) f)))) cs
        = Except.ok so →
      ∃ so', CheckedCompilerM.value (compileStmtChecked stmt0) cs
        = Except.ok so')
    (h_step : mirlite.stepStmt MSB s_mir
      (.assign (.deref D) (.ref kind prot mask (.proj (.deref P) f))) = .ok s_mir') :
    ∃ (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa ρt' s_mir' s_osea' := by
  obtain ⟨csPrefix, ⟨h_csAt, h_pc⟩, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_tbd,
    h_alloc, h_unmap, h_prb⟩ := h_inv
  -- §1 invert: prepare is the identity on a resolvable deref root
  simp only [mirlite.stepStmt, mirlite.doAssign] at h_step
  cases h_prep : mirlite.preparePlaceAssign MSB s_mir (Place.deref D) with
  | err msg => simp [h_prep] at h_step
  | ok s1 =>
  simp only [h_prep] at h_step
  have h_pre : s1 = s_mir ∧
      ∃ r0, mirlite.resolvePlace? s_mir (Place.deref D) = some r0 := by
    simp only [mirlite.preparePlaceAssign] at h_prep
    split at h_prep
    · rename_i r0 h_r0
      cases h_prep
      exact ⟨rfl, r0, h_r0⟩
    · simp [mirlite.allocateRoot] at h_prep
  obtain ⟨h_s1, r0, h_resolvedD⟩ := h_pre
  rw [h_s1] at h_step
  -- §2 the rhs retags the SOURCE first (Rust order); the source chain
  -- resolves ACC-style and is kept OPAQUE
  simp only [mirlite.evalRExpr] at h_step
  cases h_sres : mirlite.resolvePlaceAcc MSB s_mir (Place.deref P) with
  | error e =>
      rw [resolvePlaceAcc_proj_base_err (path := f) h_sres] at h_step
      simp at h_step
  | ok pr =>
  obtain ⟨rs, permsR⟩ := pr
  rw [resolvePlaceAcc_proj_base_ok (path := f) h_sres] at h_step
  simp only at h_step
  by_cases h_fit : rs.addr + PathTo.offset f + blockSize τ
      > rs.allocBase + rs.allocSize
  · rw [if_pos h_fit] at h_step
    simp at h_step
  rw [if_neg h_fit] at h_step
  cases h_ref_src : MSB.ref permsR (rs.addr + PathTo.offset f) (blockSize τ)
      rs.tag kind prot mask with
  | error e => rw [h_ref_src] at h_step; simp at h_step
  | ok pr2 =>
  obtain ⟨perms1, mintS⟩ := pr2
  rw [h_ref_src] at h_step
  simp only at h_step
  -- §3 the WHOLE dst resolves on the POST-retag state (also opaque)
  cases h_dres : mirlite.resolvePlaceAcc MSB
      { s_mir with perms := perms1 } (Place.deref D) with
  | error e => rw [h_dres] at h_step; simp at h_step
  | ok pr3 =>
  obtain ⟨resolved, permsD⟩ := pr3
  rw [h_dres] at h_step
  simp only at h_step
  -- §4 both chains are mapped, so the whole statement compiles and its
  -- emitted shape is known BEFORE either mother lemma
  have h_mappedS : PlaceInputsMapped csPrefix (Place.deref P) :=
    placeInputsMapped_of_localBindingSim_resolvePlace h_lbs
      (resolvePlace?_of_resolveAcc h_sres)
  have h_mappedD : PlaceInputsMapped csPrefix (Place.deref D) :=
    placeInputsMapped_of_localBindingSim_resolvePlace h_lbs h_resolvedD
  have h_root := ensurePlaceRoot_run_eq_of_mapped h_mappedD
  obtain ⟨sOut0, h_sval0⟩ := placeToRegChecked_ok_of_placeInputsMapped
    (cs := csPrefix) (kind := kind) h_mappedS
  have h_prmS : (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) csPrefix).placeRegMap = csPrefix.placeRegMap :=
    h_schain.placeToRegChecked_placeRegMap kind csPrefix
  obtain ⟨dOut0, h_dval0⟩ := placeToRegChecked_ok_of_placeInputsMapped
    (cs := (emit { (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) csPrefix) with nextReg := (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) csPrefix).nextReg + 1 }
      [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) csPrefix).nextReg)
        (Rhs.Borrow kind prot mask (blockSize τ) sOut0.result.reg (pathOffset f))]))
    (kind := RefKind.Mut)
    (PlaceInputsMapped.placeRegMap_congr (by simp only [emit]; exact h_prmS)
      _ h_mappedD)
  have h_dclean0 : dOut0.result.cleanup = [] :=
    placeToRegChecked_deref_cleanup h_dval0
  obtain ⟨stmtOutC, h_stmtOutC⟩ :=
    compileStmt_ref_derefdst_derefprojsrc_value kind prot mask h_root h_sval0 rfl
      h_dval0
  obtain ⟨stmtOut, h_stmtOut⟩ := h_val0 csPrefix stmtOutC h_stmtOutC
  have h_stmtRun := (h_run0 csPrefix).trans
    (compileStmt_ref_derefdst_derefprojsrc_run kind prot mask h_root h_sval0 rfl
      h_dval0 h_dclean0)
  -- §5 the three code-inclusion obligations, one `StateIncr` step each
  have h_incrS : StateIncr (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) csPrefix)
      (CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix) := by
    rw [h_stmtRun]
    exact StateIncr.trans
      (StateIncr.trans (freshReg_state_incr (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) csPrefix)) (emit_state_incr _ _))
      (StateIncr.trans (CheckedCompilerM.incr _ _) (emit_state_incr _ _))
  have h_instS :=
    (CodeIncluded.of_stmt h_comp h_csAt h_stmt h_stmtOut).mono h_incrS
  have h_incrCS1 : StateIncr (emit { (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) csPrefix) with nextReg := (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) csPrefix).nextReg + 1 }
      [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) csPrefix).nextReg)
        (Rhs.Borrow kind prot mask (blockSize τ) sOut0.result.reg (pathOffset f))])
      (CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix) := by
    rw [h_stmtRun]
    exact StateIncr.trans (CheckedCompilerM.incr _ _) (emit_state_incr _ _)
  have h_instCS1 :=
    (CodeIncluded.of_stmt h_comp h_csAt h_stmt h_stmtOut).mono h_incrCS1
  have h_incrD : StateIncr
      (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (Place.deref D)) (emit { (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) csPrefix) with nextReg := (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) csPrefix).nextReg + 1 }
      [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) csPrefix).nextReg)
        (Rhs.Borrow kind prot mask (blockSize τ) sOut0.result.reg (pathOffset f))]))
      (CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix) := by
    rw [h_stmtRun]
    exact emit_state_incr _ _
  have h_instDst :=
    (CodeIncluded.of_stmt h_comp h_csAt h_stmt h_stmtOut).mono h_incrD
  -- §6-§8 the SOURCE half as one package: the source chain lowering, the
  -- retag transport and the Borrow; its code fact comes from the
  -- post-source inclusion, stated at the post-chain label
  have h_code1 : compProg (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) csPrefix).nextLabel
      = some (Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) csPrefix).nextReg)
          (Rhs.Borrow kind prot mask (blockSize τ) sOut0.result.reg (pathOffset f))) := by
    refine h_instCS1 _ _ ?_ ?_
    · simp only [emit, List.length_cons, List.length_nil]
      omega
    · have h := emit_code_at_new
        { (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) csPrefix) with nextReg := (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) csPrefix).nextReg + 1 }
        [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) csPrefix).nextReg)
          (Rhs.Borrow kind prot mask (blockSize τ) sOut0.result.reg (pathOffset f))]
        (k := 0) (by simp)
      simpa using h
  obtain ⟨nB, s_mid, sB, tgtPerms, hsB, rfl, h_incr_t, h_wf_t', h_tbd', h_psim',
    h_runB, h_lbsB, h_pcB, h_sprm, h_sregmono, h_memB, -, h_rt_new, h_nw_new,
    h_relB⟩ :=
    ref_chainsrc_borrow h_schain f kind kind prot mask compProg s_mir s_osea csPrefix
      h_id_a h_wf_t h_tbd h_lbs h_prb h_sms h_psim h_pc h_sres h_fit h_ref_src
      h_sval0 _ rfl h_instS h_code1
  -- §9-§12: the shared chain-write seam (spine.lean)
  obtain ⟨s_osea', n, h_run, h_inv'⟩ :=
    copy_chainwrite_after_read (τ := obseq.LayoutTy.PtrL τ)
      (csR := (emit { (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) csPrefix) with nextReg := (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) csPrefix).nextReg + 1 }
      [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) csPrefix).nextReg)
        (Rhs.Borrow kind prot mask (blockSize τ) sOut0.result.reg (pathOffset f))]))
      (sR := sB)
      (vreg := Register.R (CheckedCompilerM.run (placeToRegChecked kind (Place.deref P)) csPrefix).nextReg)
      (vals := [Val.Ptr rs.allocBase (rs.addr - rs.allocBase + pathOffset f)
        rs.allocSize s_mid.perms.NextTag])
      (mvals := [mirlite.MemValue.ptrVal rs.allocBase
        (rs.addr + pathOffset f - rs.allocBase) rs.allocSize permsR.NextTag])
      compProg h_dchain h_comp h_stmt h_csAt
      h_stmtOut h_id_a h_wf_t'
      (SourceMemSim.rename_mono (AddrRenameIncr.refl ρa) h_incr_t h_sms)
      h_alloc h_unmap h_prb
      h_dres rfl h_step
      h_runB
      (by simp only [emit]; exact h_prmS)
      (by simp only [emit]; exact Nat.le_trans h_sregmono (Nat.le_succ _))
      h_lbsB (by rw [hsB]; exact h_psim') (by rw [hsB]; exact h_tbd')
      h_memB h_pcB
      (by subst hsB; exact RegMap.lookup_insert_self _ _ _)
      (by show _ < _; simp only [emit]; omega)
      rfl h_relB h_instDst
      (fun dOut h_dval h_dclean => (h_run0 csPrefix).trans
        (compileStmt_ref_derefdst_derefprojsrc_run kind prot mask h_root h_sval0 rfl
          h_dval h_dclean))
  exact ⟨_, s_osea', n, h_incr_t, h_run, h_inv'⟩

/-- `(*p).g := &kind (chain).f` at NONZERO destination offset — the LAST
    residual shape. Two mothers AND BRIDGE 1: the source chain lowers
    and its `Borrow` mints, the destination CHAIN lowers at `Mut`, and
    then the projection mints its OWN interior `Borrow(Mut)` at the
    field offset which has no mirlite counterpart. `sb_ref_use_die_cancels`
    collapses that ref/store/die triple to the parent's single use. -/
theorem ref_projderefdst_chainsrc_simulation
    {τ σd σs : LayoutTy}
    {pp : Place Γ (obseq.LayoutTy.PtrL σd)}
    {g : PathTo σd (obseq.LayoutTy.PtrL τ)}
    {sbase : Place Γ σs} {f : PathTo σs τ}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (compProg : oseair.Prog)
    (h_dchain : PtrChain (Place.deref pp))
    (h_schain : PtrChain sbase)
    (h_unfold : placeToBorrowRegChecked (Γ := Γ) kind prot mask (Place.proj sbase f)
      = (do
          let baseOut ← placeToRegChecked kind sbase
          let baseRes := baseOut.result
          let offset := pathOffset f
          let tmpReg ← CheckedCompilerM.lift freshRegM
          let _ ← CheckedCompilerM.lift
            (emitM [Instr.Assgn tmpReg
              (Rhs.Borrow kind prot mask (blockSize τ) baseRes.reg offset)])
          pure {
            result := { reg := tmpReg,
                        cleanup := baseRes.cleanup ++ [(tmpReg, blockSize τ)] },
            evidence := PlaceToBorrowRegEvidence.proj sbase f baseRes tmpReg
              baseOut.evidence
          }))
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    {stmt0 : Stmt Γ}
    (h_stmt : prog.get? s_mir.pc = some stmt0)
    (h_run0 : ∀ cs, CheckedCompilerM.run (compileStmtChecked stmt0) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (Place.proj (Place.deref pp) g) (.ref kind prot mask (.proj sbase f)))) cs)
    (h_val0 : ∀ cs so, CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (Place.proj (Place.deref pp) g) (.ref kind prot mask (.proj sbase f)))) cs
        = Except.ok so →
      ∃ so', CheckedCompilerM.value (compileStmtChecked stmt0) cs
        = Except.ok so')
    (h_step : mirlite.stepStmt MSB s_mir
      (.assign (Place.proj (Place.deref pp) g) (.ref kind prot mask (.proj sbase f))) = .ok s_mir') :
    ∃ (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa ρt' s_mir' s_osea' := by
  obtain ⟨csPrefix, ⟨h_csAt, h_pc⟩, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_tbd,
    h_alloc, h_unmap, h_prb⟩ := h_inv
  -- §1 invert: prepare is the identity on a resolvable deref-rooted place
  simp only [mirlite.stepStmt, mirlite.doAssign] at h_step
  cases h_prep : mirlite.preparePlaceAssign MSB s_mir (Place.proj (Place.deref pp) g) with
  | err msg => simp [h_prep] at h_step
  | ok s1 =>
  simp only [h_prep] at h_step
  have h_pre : s1 = s_mir ∧
      ∃ r0, mirlite.resolvePlace? s_mir (Place.proj (Place.deref pp) g) = some r0 := by
    simp only [mirlite.preparePlaceAssign] at h_prep
    split at h_prep
    · rename_i r0 h_r0
      cases h_prep
      exact ⟨rfl, r0, h_r0⟩
    · simp [mirlite.allocateRoot] at h_prep
  obtain ⟨h_s1, r0, h_resolvedD⟩ := h_pre
  rw [h_s1] at h_step
  -- §2 the rhs retags the SOURCE first (Rust order)
  simp only [mirlite.evalRExpr] at h_step
  cases h_sres : mirlite.resolvePlaceAcc MSB s_mir sbase with
  | error e =>
      rw [resolvePlaceAcc_proj_base_err (path := f) h_sres] at h_step
      simp at h_step
  | ok pr =>
  obtain ⟨rs, permsR⟩ := pr
  rw [resolvePlaceAcc_proj_base_ok (path := f) h_sres] at h_step
  simp only at h_step
  by_cases h_fit : rs.addr + PathTo.offset f + blockSize τ
      > rs.allocBase + rs.allocSize
  · rw [if_pos h_fit] at h_step
    simp at h_step
  rw [if_neg h_fit] at h_step
  cases h_ref_src : MSB.ref permsR (rs.addr + PathTo.offset f) (blockSize τ)
      rs.tag kind prot mask with
  | error e => rw [h_ref_src] at h_step; simp at h_step
  | ok pr2 =>
  obtain ⟨perms1, mintS⟩ := pr2
  rw [h_ref_src] at h_step
  simp only at h_step
  -- §3 the destination's CHAIN BASE resolves on the post-retag state;
  -- the field offset rides on top
  cases h_dbres : mirlite.resolvePlaceAcc MSB
      { s_mir with perms := perms1 } (Place.deref pp) with
  | error e =>
      rw [resolvePlaceAcc_proj_base_err (path := g) h_dbres] at h_step
      simp at h_step
  | ok pr3 =>
  obtain ⟨rd, permsD⟩ := pr3
  rw [resolvePlaceAcc_proj_base_ok (path := g) h_dbres] at h_step
  simp only at h_step
  -- §4 both places are mapped; the emitted shape is known up front
  have h_mappedS : PlaceInputsMapped csPrefix sbase :=
    placeInputsMapped_of_localBindingSim_resolvePlace h_lbs
      (resolvePlace?_of_resolveAcc h_sres)
  have h_mappedD : PlaceInputsMapped csPrefix (Place.proj (Place.deref pp) g) :=
    placeInputsMapped_of_localBindingSim_resolvePlace h_lbs h_resolvedD
  have h_root := ensurePlaceRoot_run_eq_of_mapped h_mappedD
  obtain ⟨sOut0, h_sval0⟩ := placeToRegChecked_ok_of_placeInputsMapped
    (cs := csPrefix) (kind := kind) h_mappedS
  have h_prmS : (CheckedCompilerM.run (placeToRegChecked kind sbase) csPrefix).placeRegMap = csPrefix.placeRegMap :=
    h_schain.placeToRegChecked_placeRegMap kind csPrefix
  obtain ⟨bOut0, h_bval0⟩ := placeToRegChecked_ok_of_placeInputsMapped
    (cs := (emit { (CheckedCompilerM.run (placeToRegChecked kind sbase) csPrefix) with nextReg := (CheckedCompilerM.run (placeToRegChecked kind sbase) csPrefix).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked kind sbase) csPrefix).nextReg) (Rhs.Borrow kind prot mask (blockSize τ) sOut0.result.reg (pathOffset f))]))
    (kind := RefKind.Mut)
    (PlaceInputsMapped.placeRegMap_congr (by simp only [emit]; exact h_prmS)
      (Place.deref pp) h_mappedD)
  have h_bclean0 : bOut0.result.cleanup = [] :=
    placeToRegChecked_deref_cleanup h_bval0
  obtain ⟨stmtOutC, h_stmtOutC⟩ :=
    compileStmt_ref_projderefdst_chainsrc_value kind prot mask h_unfold
      h_root h_sval0 rfl h_bval0
  obtain ⟨stmtOut, h_stmtOut⟩ := h_val0 csPrefix stmtOutC h_stmtOutC
  have h_stmtRun := (h_run0 csPrefix).trans
    (compileStmt_ref_projderefdst_chainsrc_run kind prot mask h_unfold
      h_root h_sval0 rfl h_bval0 h_bclean0)
  -- §5 the code-inclusion obligations, each a StateIncr to the statement's
  -- run: the destination tail only adds, so every prefix is included
  have h_incrB : StateIncr (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (Place.deref pp)) (emit { (CheckedCompilerM.run (placeToRegChecked kind sbase) csPrefix) with nextReg := (CheckedCompilerM.run (placeToRegChecked kind sbase) csPrefix).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked kind sbase) csPrefix).nextReg) (Rhs.Borrow kind prot mask (blockSize τ) sOut0.result.reg (pathOffset f))]))
      (CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix) := by
    rw [h_stmtRun]; exact projDstTail_state_incr _ _ _ _ _ _
  have h_incrCS1 : StateIncr (emit { (CheckedCompilerM.run (placeToRegChecked kind sbase) csPrefix) with nextReg := (CheckedCompilerM.run (placeToRegChecked kind sbase) csPrefix).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked kind sbase) csPrefix).nextReg) (Rhs.Borrow kind prot mask (blockSize τ) sOut0.result.reg (pathOffset f))])
      (CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix) :=
    StateIncr.trans (CheckedCompilerM.incr _ _) h_incrB
  have h_incrS : StateIncr (CheckedCompilerM.run (placeToRegChecked kind sbase) csPrefix)
      (CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix) :=
    StateIncr.trans
      (StateIncr.trans (freshReg_state_incr (CheckedCompilerM.run (placeToRegChecked kind sbase) csPrefix)) (emit_state_incr _ _))
      h_incrCS1
  have h_instS :=
    (CodeIncluded.of_stmt h_comp h_csAt h_stmt h_stmtOut).mono h_incrS
  have h_instCS1 :=
    (CodeIncluded.of_stmt h_comp h_csAt h_stmt h_stmtOut).mono h_incrCS1
  have h_instB :=
    (CodeIncluded.of_stmt h_comp h_csAt h_stmt h_stmtOut).mono h_incrB
  -- §6-§8 the SOURCE half as one package: the source chain lowering, the
  -- retag transport and the Borrow, with the code fact at the post-chain label
  have h_code1 : compProg (CheckedCompilerM.run (placeToRegChecked kind sbase) csPrefix).nextLabel
      = some (Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked kind sbase) csPrefix).nextReg)
          (Rhs.Borrow kind prot mask (blockSize τ) sOut0.result.reg (pathOffset f))) := by
    refine h_instCS1 _ _ ?_ ?_
    · simp only [emit, List.length_cons, List.length_nil]
      omega
    · have h := emit_code_at_new
        { (CheckedCompilerM.run (placeToRegChecked kind sbase) csPrefix) with nextReg := (CheckedCompilerM.run (placeToRegChecked kind sbase) csPrefix).nextReg + 1 }
        [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked kind sbase) csPrefix).nextReg)
          (Rhs.Borrow kind prot mask (blockSize τ) sOut0.result.reg (pathOffset f))]
        (k := 0) (by simp)
      simpa using h
  obtain ⟨nB, s_mid, sB, tgtPerms, hsB, rfl, h_incr_t, h_wf_t', h_tbd', h_psim',
    h_runB, h_lbsB, h_pcB, h_sprm, h_sregmono, h_memB, -, h_rt_new, h_nw_new,
    h_relB⟩ :=
    ref_chainsrc_borrow h_schain f kind kind prot mask compProg s_mir s_osea csPrefix
      h_id_a h_wf_t h_tbd h_lbs h_prb h_sms h_psim h_pc h_sres h_fit h_ref_src
      h_sval0 _ rfl h_instS h_code1
  -- §9 MOTHER 2: the DESTINATION CHAIN BASE, from the post-Borrow state
  have h_prmCS1 : (emit { (CheckedCompilerM.run (placeToRegChecked kind sbase) csPrefix) with nextReg := (CheckedCompilerM.run (placeToRegChecked kind sbase) csPrefix).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked kind sbase) csPrefix).nextReg) (Rhs.Borrow kind prot mask (blockSize τ) sOut0.result.reg (pathOffset f))]).placeRegMap = csPrefix.placeRegMap := by
    simp only [emit]
    exact h_prmS
  have h_prb1 : PlaceRegMapBound (emit { (CheckedCompilerM.run (placeToRegChecked kind sbase) csPrefix) with nextReg := (CheckedCompilerM.run (placeToRegChecked kind sbase) csPrefix).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked kind sbase) csPrefix).nextReg) (Rhs.Borrow kind prot mask (blockSize τ) sOut0.result.reg (pathOffset f))]) := by
    intro idx reg'' τ'' h_look
    have h_cs : getPlaceInfo csPrefix idx = some (reg'', τ'') := by
      show csPrefix.placeRegMap.lookup idx = _
      rw [← h_prmCS1]
      exact h_look
    refine RegisterBelow.mono ?_ (h_prb _ _ _ h_cs)
    simp only [emit]
    exact Nat.le_trans h_sregmono (Nat.le_succ _)
  obtain ⟨bOut, n2, s_mid2, tresD, h_bval, h_bclean, h_brun, h_bpc, h_bmem,
    h_bpsim, h_bnt1, h_bnt2, h_blbs, h_bentry, h_brt, h_bnw, h_ble, h_brange,
    h_bbelow, h_bprm, h_bregmono, h_blabmono, h_bframe, h_bbase⟩ :=
    ptrChain_lowering_sim (s_mir := { s_mir with perms := perms1 })
      h_id_a h_wf_t' h_dchain RefKind.Mut (emit { (CheckedCompilerM.run (placeToRegChecked kind sbase) csPrefix) with nextReg := (CheckedCompilerM.run (placeToRegChecked kind sbase) csPrefix).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked kind sbase) csPrefix).nextReg) (Rhs.Borrow kind prot mask (blockSize τ) sOut0.result.reg (pathOffset f))]) sB
      rd permsD h_dbres (by rw [hsB]; exact h_tbd') h_lbsB h_prb1
      (by
        show SourceMemSim ρa (ρt.extend permsR.NextTag s_mid.perms.NextTag)
          s_mir.mem sB.mem
        rw [h_memB]
        exact SourceMemSim.rename_mono (AddrRenameIncr.refl ρa) h_incr_t h_sms)
      (by rw [hsB]; exact h_psim') h_pcB
      h_instB
  have h_bOut_eq : bOut = bOut0 := by
    rw [h_bval0] at h_bval
    exact (Except.ok.inj h_bval).symm
  subst h_bOut_eq
  have h_cancelD := resolvedAddr_cancel h_ble
  have h_goff_eq := resolvedOffset_shift h_ble (pathOffset g)
  -- §10 the mirlite write and BRIDGE 1
  have h_tbd2 : TagRenameBounded (ρt.extend permsR.NextTag s_mid.perms.NextTag)
      permsD.NextTag s_mid2.perms.NextTag := by
    rw [h_bnt1]
    exact TagRenameBounded.mono h_tbd' (Nat.le_refl _) (by rw [hsB] at h_bnt2; exact h_bnt2)
  have h_regbelowS : RegisterBelow (emit { (CheckedCompilerM.run (placeToRegChecked kind sbase) csPrefix) with nextReg := (CheckedCompilerM.run (placeToRegChecked kind sbase) csPrefix).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked kind sbase) csPrefix).nextReg) (Rhs.Borrow kind prot mask (blockSize τ) sOut0.result.reg (pathOffset f))]).nextReg (Register.R (CheckedCompilerM.run (placeToRegChecked kind sbase) csPrefix).nextReg) := by
    show (CheckedCompilerM.run (placeToRegChecked kind sbase) csPrefix).nextReg < _
    simp only [emit]
    omega
  -- §12-§16 the BOUND-root projected write seam, at the CHAIN-resolved
  -- destination the second mother produced
  have h_fitD : (rd.addr - rd.allocBase) + pathOffset g
      + blockSize (obseq.LayoutTy.PtrL τ) ≤ rd.allocSize := by
    have h1 := Nat.not_lt.mp (writeResolvedPlace_ok_inv h_step).1
    have h3 : rd.allocBase ≤ rd.addr := h_ble
    have h4 : rd.allocBase + (rd.addr - rd.allocBase) = rd.addr := h_cancelD
    grind
  obtain ⟨s_osea', n, h_run, h_inv'⟩ :=
    copy_bound_write_after_read
      (τ := obseq.LayoutTy.PtrL τ) (dbase := rd.allocBase) (dtag := rd.tag)
      (dsize := rd.allocSize)
      (rd := { addr := rd.addr + PathTo.offset g, tag := rd.tag,
               allocBase := rd.allocBase, allocSize := rd.allocSize })
      (csR := CheckedCompilerM.run (placeToRegChecked RefKind.Mut (Place.deref pp))
        (emit { (CheckedCompilerM.run (placeToRegChecked kind sbase) csPrefix) with nextReg := (CheckedCompilerM.run (placeToRegChecked kind sbase) csPrefix).nextReg + 1 } [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked kind sbase) csPrefix).nextReg) (Rhs.Borrow kind prot mask (blockSize τ) sOut0.result.reg (pathOffset f))]))
      (sR := s_mid2)
      (vreg := Register.R (CheckedCompilerM.run (placeToRegChecked kind sbase) csPrefix).nextReg)
      (vals := [Val.Ptr rs.allocBase (rs.addr - rs.allocBase + pathOffset f)
        rs.allocSize s_mid.perms.NextTag])
      (mvals := [mirlite.MemValue.ptrVal rs.allocBase
        (rs.addr + pathOffset f - rs.allocBase) rs.allocSize permsR.NextTag])
      compProg h_comp h_stmt h_csAt h_stmtOut h_id_a h_wf_t' h_unmap h_prb
      (rd.addr - rd.allocBase) h_bbase h_brt h_bnw h_brange (pathOffset g)
      h_fitD
      (oseair_runN_trans h_runB h_brun)
      h_bentry
      (by rw [h_bmem, h_memB]
          exact SourceMemSim.rename_mono (AddrRenameIncr.refl ρa) h_incr_t h_sms)
      (by rw [h_bmem, h_memB]; exact h_alloc)
      (h_bprm.trans (by simp only [emit]; exact h_sprm))
      (Nat.le_trans (by simp only [emit]; omega) h_bregmono)
      (LocalBindingSim.placeRegMap_congr h_bprm h_blbs) h_bpsim h_tbd2 h_bpc
      (by rw [h_bframe _ h_regbelowS, hsB]
          exact RegMap.lookup_insert_self _ _ _)
      (RegisterBelow.mono h_bregmono h_regbelowS)
      rfl h_stmtRun rfl
      (by rw [← Nat.add_assoc, h_cancelD]) rfl rfl rfl
      h_relB
      h_step
  exact ⟨_, s_osea', n, h_incr_t, h_run, h_inv'⟩
/-- The source-flattening recursion for a PROJECTED destination over a
    bound-or-fresh LOCAL base. Base cases dispatch on the destination
    offset and on whether the destination root is bound, into the four
    `*_projsrc_*` leaves.

    ONE sub-case cannot be closed here and routes to the residual: both
    roots unbound AND the same local (`t.g := &kind t.f`, `t` fresh).
    Unlike every other fresh-destination shape, the types give no
    disjointness — `g : PathTo σ (PtrL τ)` and `f : PathTo σ τ` can
    leave the same layout — and the allocation BINDS the source root,
    so the step really can succeed. It needs a leaf that reads the
    source binding off the post-allocation state. -/
theorem ref_proj_src_projdst_simulation
    {τ σ σb : LayoutTy}
    {dstLoc : Local Γ σ} {g : PathTo σ (obseq.LayoutTy.PtrL τ)}
    {sbase : Place Γ σb} {f : PathTo σb τ}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (compProg : oseair.Prog)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    {stmt0 : Stmt Γ}
    (h_stmt : prog.get? s_mir.pc = some stmt0)
    (h_run0 : ∀ cs, CheckedCompilerM.run (compileStmtChecked stmt0) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.proj (.local dstLoc) g)
              (.ref kind prot mask (.proj sbase f)))) cs)
    (h_val0 : ∀ cs so, CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.proj (.local dstLoc) g)
            (.ref kind prot mask (.proj sbase f)))) cs
        = Except.ok so →
      ∃ so', CheckedCompilerM.value (compileStmtChecked stmt0) cs
        = Except.ok so')
    (h_step : mirlite.stepStmt MSB s_mir
      (.assign (.proj (.local dstLoc) g)
        (.ref kind prot mask (.proj sbase f))) = .ok s_mir') :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' := by
  induction sbase with
  | @«local» σ' srcLoc =>
      cases h_envD : mirlite.Env.lookup s_mir.env dstLoc with
      | some bD =>
          cases h_envS : mirlite.Env.lookup s_mir.env srcLoc with
          | some bS =>
              obtain ⟨ρt', s_osea', n, h_incr, h_run, h_inv'⟩ :=
                ref_projdst_projsrc_simulation kind prot mask compProg
                  h_comp h_inv h_stmt h_run0 h_val0 h_envD h_envS h_step
              exact ⟨ρa, ρt', s_osea', n, AddrRenameIncr.refl ρa, h_incr,
                h_run, h_inv'⟩
          | none =>
              exfalso
              simp [mirPrep, mirlite.stepStmt, mirlite.doAssign, mirlite.doAssignCont, h_envD,
                mirlite.resolvePlaceAcc, h_envS, mirlite.evalRExpr] at h_step
      | none =>
          cases h_envS : mirlite.Env.lookup s_mir.env srcLoc with
          | some bS =>
              exact ref_proj_fresh_projsrc_simulation kind prot mask
                compProg h_comp h_inv h_stmt h_run0 h_val0 h_envD h_envS h_step
          | none =>
              by_cases h_same : srcLoc.idx = dstLoc.idx
              · -- the SOURCE root IS the destination root: the allocation
                -- binds it, and the step succeeds
                have hσ : σ' = σ := by
                  have h1 := srcLoc.hTy
                  rw [h_same, dstLoc.hTy] at h1
                  exact h1.symm
                subst hσ
                have h_eq : srcLoc = dstLoc := by
                  cases srcLoc; cases dstLoc; cases h_same; rfl
                subst h_eq
                exact ref_proj_fresh_selfsrc_simulation kind prot mask
                  compProg h_comp h_inv h_stmt h_run0 h_val0 h_envD h_step
              · -- distinct unbound roots: the source stays unbound and errs
                exfalso
                simp only [mirlite.stepStmt, mirlite.doAssign] at h_step
                cases h_prep : mirlite.preparePlaceAssign MSB s_mir
                    (Place.proj (Place.local dstLoc) g) with
                | err m => rw [h_prep] at h_step; simp at h_step
                | ok s1 =>
                    rw [h_prep] at h_step
                    have hS1 : mirlite.Env.lookup s1.env srcLoc = none := by
                      rw [prepare_lookup_ne_proj h_same h_envD h_prep]; exact h_envS
                    simp [mirlite.evalRExpr, mirlite.resolvePlaceAcc, hS1] at h_step
  | proj b q ih =>
      refine ih
        (fun cs => (h_run0 cs).trans
          (compileStmt_ref_srcproj_assoc_proj_run (dbase := Place.local dstLoc) (g := g)
            kind prot mask b q f cs))
        (fun cs so h => by
          obtain ⟨so', h'⟩ :=
            compileStmt_ref_srcproj_assoc_proj_value (dbase := Place.local dstLoc) (g := g)
              kind prot mask b q f cs so h
          exact h_val0 cs so' h')
        ?_
      rw [← stepStmt_assign_refsrc_projassoc s_mir (Place.proj (Place.local dstLoc) g)
        kind prot mask b q f]
      exact h_step
  | deref pp =>
      -- CLOSED: `dst.g := &kind (*p).f` — the source spine by the mother
      -- lemma, the destination by its four quadrants
      rw [stepStmt_assign_refsrc_anyflatten] at h_step
      cases h_envD : mirlite.Env.lookup s_mir.env dstLoc with
      | some bD =>
          obtain ⟨ρt', s_osea', n, h_incr, h_run, h_inv'⟩ :=
            ref_projdst_derefsrc_simulation (P := flattenPlace pp) kind prot mask
              compProg (PtrChain_flatten_deref pp) h_comp h_inv h_stmt
              (fun cs => (h_run0 cs).trans
                (compileStmt_ref_srcflatten_proj_run (dbase := Place.local dstLoc) (g := g)
                  kind prot mask (Place.proj (Place.deref pp) f) cs))
              (fun cs so h => by
                obtain ⟨so', h'⟩ :=
                  compileStmt_ref_srcflatten_proj_value (dbase := Place.local dstLoc) (g := g)
                    kind prot mask (Place.proj (Place.deref pp) f) cs so h
                exact h_val0 cs so' h')
              h_envD h_step
          exact ⟨ρa, ρt', s_osea', n, AddrRenameIncr.refl ρa, h_incr, h_run, h_inv'⟩
      | none =>
          exact ref_proj_fresh_derefsrc_simulation (P := flattenPlace pp) kind prot mask
            compProg (PtrChain_flatten_deref pp) h_comp h_inv h_stmt
              (fun cs => (h_run0 cs).trans
                (compileStmt_ref_srcflatten_proj_run (dbase := Place.local dstLoc) (g := g)
                  kind prot mask (Place.proj (Place.deref pp) f) cs))
              (fun cs so h => by
                obtain ⟨so', h'⟩ :=
                  compileStmt_ref_srcflatten_proj_value (dbase := Place.local dstLoc) (g := g)
                    kind prot mask (Place.proj (Place.deref pp) f) cs so h
                exact h_val0 cs so' h')
              h_envD h_step

/-- The dst-flattening recursion for ref: a PROJECTED destination of any
    nesting depth reassociates on both machines
    (`compileStmt_assign_proj_assoc_run/_value`,
    `stepStmt_assign_proj_assoc`) and recurses into the closed field-dst
    leaves, threading the PROGRAM's own statement (`stmt0`). Deref
    bases, non-local srcs and unbound roots route to the residual. -/
theorem ref_proj_dst_simulation
    {τ : LayoutTy} {σ' : LayoutTy}
    {dbase : Place Γ σ'} {g : PathTo σ' (obseq.LayoutTy.PtrL τ)}
    {src : Place Γ τ}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (compProg : oseair.Prog)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    {stmt0 : Stmt Γ}
    (h_stmt : prog.get? s_mir.pc = some stmt0)
    (h_run0 : ∀ cs, CheckedCompilerM.run (compileStmtChecked stmt0) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.proj dbase g) (.ref kind prot mask src))) cs)
    (h_val0 : ∀ cs so, CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.proj dbase g) (.ref kind prot mask src))) cs
        = Except.ok so →
      ∃ so', CheckedCompilerM.value (compileStmtChecked stmt0) cs
        = Except.ok so')
    (h_step : mirlite.stepStmt MSB s_mir
      (.assign (.proj dbase g) (.ref kind prot mask src)) = .ok s_mir') :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' := by
  induction dbase with
  | «local» dstLoc =>
      cases src with
      | «local» srcLoc =>
          cases h_envD : mirlite.Env.lookup s_mir.env dstLoc with
          | some bD =>
              cases h_envS : mirlite.Env.lookup s_mir.env srcLoc with
              | some bS =>
                  obtain ⟨ρt', s_osea', n, h_incr, h_run, h_inv'⟩ :=
                    ref_projdst_local_simulation kind prot mask compProg
                      h_comp h_inv h_stmt h_run0 h_val0
                      h_envD h_envS h_step
                  exact ⟨ρa, ρt', s_osea', n, AddrRenameIncr.refl ρa, h_incr,
                    h_run, h_inv'⟩
              | none =>
                  exfalso
                  simp [mirPrep, mirlite.stepStmt, mirlite.doAssign, mirlite.doAssignCont,
                    h_envD, mirlite.resolvePlaceAcc, h_envS, mirlite.evalRExpr] at h_step
          | none =>
              cases h_envS : mirlite.Env.lookup s_mir.env srcLoc with
              | some bS =>
                  -- CLOSED: `dst.g := &kind s` at offset 0, `dst` UNBOUND
                  exact ref_proj_fresh_simulation kind prot mask compProg
                    h_comp h_inv h_stmt h_run0 h_val0 h_envD h_envS h_step
              | none =>
                  -- `&src` of an unbound local: the source errs at resolution
                  exfalso
                  have h_ne := ref_dst_src_idx_ne_of_proj dstLoc srcLoc g
                  simp only [mirlite.stepStmt, mirlite.doAssign] at h_step
                  cases h_prep : mirlite.preparePlaceAssign MSB s_mir
                      (Place.proj (Place.local dstLoc) g) with
                  | err m => rw [h_prep] at h_step; simp at h_step
                  | ok s1 =>
                      rw [h_prep] at h_step
                      have hS1 : mirlite.Env.lookup s1.env srcLoc = none := by
                        rw [prepare_lookup_ne_proj h_ne h_envD h_prep]; exact h_envS
                      simp [mirlite.evalRExpr, mirlite.resolvePlaceAcc, hS1] at h_step
      | proj sbase f =>
          -- CLOSED for any source base that flattens to a LOCAL distinct from
          -- the destination root: the source-flattening recursion
          exact ref_proj_src_projdst_simulation kind prot mask compProg h_comp h_inv
            h_stmt h_run0 h_val0 h_step
      | deref pp =>
          -- CLOSED: `dst.g := &kind *P`. The nil-projection eta puts the
          -- plain deref spelling into the `.proj (.deref _) _` grammar
          -- the source-flattening recursion already covers.
          exact ref_proj_src_projdst_simulation (sbase := Place.deref pp) (f := PathTo.nil)
            kind prot mask compProg h_comp h_inv h_stmt
            (fun cs => (h_run0 cs).trans
              (compileStmt_ref_srcnil_proj_run (dbase := Place.local dstLoc) (g := g)
                kind prot mask pp cs))
            (fun cs so h => by
              obtain ⟨so', h'⟩ :=
                compileStmt_ref_srcnil_proj_value (dbase := Place.local dstLoc) (g := g)
                  kind prot mask pp cs so h
              exact h_val0 cs so' h')
            (by rw [← stepStmt_assign_refsrc_nil]; exact h_step)
  | proj b q ih =>
      refine ih
        (fun cs => (h_run0 cs).trans
          (compileStmt_assign_proj_assoc_run b q g (.ref kind prot mask src) cs))
        (fun cs so h => by
          obtain ⟨so', h'⟩ :=
            compileStmt_assign_proj_assoc_value b q g (.ref kind prot mask src) cs h
          exact h_val0 cs so' h')
        ?_
      rw [← stepStmt_assign_proj_assoc b q g (.ref kind prot mask src)]
      exact h_step
  | deref pp =>
      -- CLOSED: `(*p).g := &kind _`, the LAST residual shape. BOTH
      -- places are flattened, then the source is normalized into
      -- `.proj <chain> _` (nil-eta when it is already a chain), and the
      -- destination offset picks the zero-offset leaf or the
      -- BRIDGE 1 one.
      rw [stepStmt_assign_dstflatten] at h_step
      rw [stepStmt_assign_refsrc_anyflatten] at h_step
      have h_runD : ∀ cs, CheckedCompilerM.run (compileStmtChecked stmt0) cs
          = CheckedCompilerM.run (compileStmtChecked
              (Stmt.assign (Place.proj (Place.deref (flattenPlace pp)) g)
                (.ref kind prot mask (flattenPlace src)))) cs := by
        intro cs
        refine ((h_run0 cs).trans
          (compileStmt_assign_projderefdst_flatten_run
            (pp := pp) (g := g) (.ref kind prot mask src) cs)).trans ?_
        exact compileStmt_ref_srcflatten_proj_run
          (dbase := Place.deref (flattenPlace pp)) (g := g) kind prot mask src cs
      have h_valD : ∀ cs so, CheckedCompilerM.value (compileStmtChecked
            (Stmt.assign (Place.proj (Place.deref (flattenPlace pp)) g)
              (.ref kind prot mask (flattenPlace src)))) cs = Except.ok so →
          ∃ so', CheckedCompilerM.value (compileStmtChecked stmt0) cs
            = Except.ok so' := by
        intro cs so h
        obtain ⟨so1, h1⟩ := compileStmt_ref_srcflatten_proj_value
          (dbase := Place.deref (flattenPlace pp)) (g := g) kind prot mask src cs so h
        obtain ⟨so2, h2⟩ := compileStmt_assign_projderefdst_flatten_value
          (pp := pp) (g := g) (.ref kind prot mask src) cs so1 h1
        exact h_val0 cs so2 h2
      rcases flatten_chainish src with h_ch | ⟨σ', sb, path, h_eq, h_sb⟩
      · rw [stepStmt_assign_refsrc_nil] at h_step
        have h_runN : ∀ cs, CheckedCompilerM.run (compileStmtChecked stmt0) cs
            = CheckedCompilerM.run (compileStmtChecked
                (Stmt.assign (Place.proj (Place.deref (flattenPlace pp)) g)
                  (.ref kind prot mask
                    (Place.proj (flattenPlace src) PathTo.nil)))) cs :=
          fun cs => (h_runD cs).trans
            (compileStmt_ref_srcnilchain_proj_run
              (dbase := Place.deref (flattenPlace pp)) (g := g) kind prot mask h_ch cs)
        have h_valN : ∀ cs so, CheckedCompilerM.value (compileStmtChecked
              (Stmt.assign (Place.proj (Place.deref (flattenPlace pp)) g)
                (.ref kind prot mask
                  (Place.proj (flattenPlace src) PathTo.nil)))) cs = Except.ok so →
            ∃ so', CheckedCompilerM.value (compileStmtChecked stmt0) cs
              = Except.ok so' := by
          intro cs so h
          obtain ⟨so1, h1⟩ := compileStmt_ref_srcnilchain_proj_value
            (dbase := Place.deref (flattenPlace pp)) (g := g) kind prot mask h_ch cs so h
          exact h_valD cs so1 h1
        obtain ⟨ρt', s_osea', n, h_incr, h_run, h_inv'⟩ :=
          ref_projderefdst_chainsrc_simulation
            (sbase := flattenPlace src) (f := PathTo.nil)
            kind prot mask compProg (PtrChain_flatten_deref pp) h_ch
            (placeToBorrowRegChecked_proj_root_eq PathTo.nil (PtrChain.not_proj h_ch))
            h_comp h_inv h_stmt h_runN h_valN h_step
        exact ⟨ρa, ρt', s_osea', n, AddrRenameIncr.refl ρa, h_incr, h_run, h_inv'⟩
      · rw [h_eq] at h_step
        rw [h_eq] at h_runD h_valD
        obtain ⟨ρt', s_osea', n, h_incr, h_run, h_inv'⟩ :=
          ref_projderefdst_chainsrc_simulation
            (sbase := sb) (f := path)
            kind prot mask compProg (PtrChain_flatten_deref pp) h_sb
            (placeToBorrowRegChecked_proj_root_eq path (PtrChain.not_proj h_sb))
            h_comp h_inv h_stmt h_runD h_valD h_step
        exact ⟨ρa, ρt', s_osea', n, AddrRenameIncr.refl ρa, h_incr, h_run, h_inv'⟩
/-- The SOURCE-flattening recursion, the mirror of
    `ref_proj_dst_simulation`: a nested projection source over a local
    destination reassociates one layer at a time on BOTH machines
    (`stepStmt_assign_refsrc_projassoc` source-side,
    `compileStmt_ref_srcproj_assoc_local_run/_value` compiled-side) and
    lands in the closed proj-over-local leaves. Only a DEREF-rooted
    source survives to the residual. -/
theorem ref_proj_src_local_simulation
    {τ : LayoutTy} {σ : LayoutTy}
    {dstLoc : Local Γ (obseq.LayoutTy.PtrL τ)}
    {sbase : Place Γ σ} {f : PathTo σ τ}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (compProg : oseair.Prog)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    {stmt0 : Stmt Γ}
    (h_stmt : prog.get? s_mir.pc = some stmt0)
    (h_run0 : ∀ cs, CheckedCompilerM.run (compileStmtChecked stmt0) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.local dstLoc) (.ref kind prot mask (.proj sbase f)))) cs)
    (h_val0 : ∀ cs so, CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.local dstLoc) (.ref kind prot mask (.proj sbase f)))) cs
        = Except.ok so →
      ∃ so', CheckedCompilerM.value (compileStmtChecked stmt0) cs
        = Except.ok so')
    (h_step : mirlite.stepStmt MSB s_mir
      (.assign (.local dstLoc) (.ref kind prot mask (.proj sbase f))) = .ok s_mir') :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' := by
  induction sbase with
  | «local» srcLoc =>
      cases h_envD : mirlite.Env.lookup s_mir.env dstLoc with
      | some bD =>
          cases h_envS : mirlite.Env.lookup s_mir.env srcLoc with
          | some bS =>
              obtain ⟨ρt', s_osea', n, h_incr, h_run, h_inv'⟩ :=
                ref_proj_local_simulation kind prot mask compProg h_comp h_inv
                  h_stmt h_run0 h_val0 h_envD h_envS h_step
              exact ⟨ρa, ρt', s_osea', n, AddrRenameIncr.refl ρa, h_incr,
                h_run, h_inv'⟩
          | none =>
              exfalso
              simp [mirPrep, mirlite.stepStmt, mirlite.doAssign, mirlite.doAssignCont, h_envD,
                mirlite.resolvePlaceAcc, h_envS, mirlite.evalRExpr] at h_step
      | none =>
          cases h_envS : mirlite.Env.lookup s_mir.env srcLoc with
          | some bS =>
              exact ref_fresh_projsrc_simulation kind prot mask compProg
                h_comp h_inv h_stmt h_run0 h_val0 h_envD h_envS h_step
          | none =>
              exfalso
              have h_ne := ref_proj_dst_src_idx_ne dstLoc srcLoc f
              simp only [mirlite.stepStmt, mirlite.doAssign] at h_step
              cases h_prep : mirlite.preparePlaceAssign MSB s_mir
                  (Place.local dstLoc) with
              | err m => rw [h_prep] at h_step; simp at h_step
              | ok s1 =>
                  rw [h_prep] at h_step
                  have hS1 : mirlite.Env.lookup s1.env srcLoc = none := by
                    rw [prepare_lookup_ne h_ne h_prep]; exact h_envS
                  simp [mirlite.evalRExpr, mirlite.resolvePlaceAcc, hS1] at h_step
  | proj b q ih =>
      refine ih
        (fun cs => (h_run0 cs).trans
          (compileStmt_ref_srcproj_assoc_local_run (dstLoc := dstLoc)
            kind prot mask b q f cs))
        (fun cs so h => by
          obtain ⟨so', h'⟩ :=
            compileStmt_ref_srcproj_assoc_local_value (dstLoc := dstLoc)
              kind prot mask b q f cs so h
          exact h_val0 cs so' h')
        ?_
      rw [← stepStmt_assign_refsrc_projassoc s_mir (Place.local dstLoc)
        kind prot mask b q f]
      exact h_step
  | deref pp =>
      -- CLOSED: `dst := &kind (*p).f` — the chain lowers by the mother
      -- lemma and the projection rides in the Borrow's offset operand
      rw [stepStmt_assign_refsrc_anyflatten] at h_step
      cases h_envD : mirlite.Env.lookup s_mir.env dstLoc with
      | some bD =>
          obtain ⟨ρt', s_osea', n, h_incr, h_run, h_inv'⟩ :=
            ref_derefprojsrc_local_simulation (P := flattenPlace pp) kind prot mask
              compProg (PtrChain_flatten_deref pp) h_comp h_inv h_stmt
              (fun cs => (h_run0 cs).trans
                (compileStmt_ref_srcflatten_local_run (dstLoc := dstLoc) kind prot mask
                  (Place.proj (Place.deref pp) f) cs))
              (fun cs so h => by
                obtain ⟨so', h'⟩ :=
                  compileStmt_ref_srcflatten_local_value (dstLoc := dstLoc) kind prot mask
                    (Place.proj (Place.deref pp) f) cs so h
                exact h_val0 cs so' h')
              h_envD h_step
          exact ⟨ρa, ρt', s_osea', n, AddrRenameIncr.refl ρa, h_incr, h_run, h_inv'⟩
      | none =>
          exact ref_fresh_derefprojsrc_simulation (P := flattenPlace pp) kind prot mask
            compProg (PtrChain_flatten_deref pp) h_comp h_inv h_stmt
            (fun cs => (h_run0 cs).trans
              (compileStmt_ref_srcflatten_local_run (dstLoc := dstLoc) kind prot mask
                (Place.proj (Place.deref pp) f) cs))
            (fun cs so h => by
              obtain ⟨so', h'⟩ :=
                compileStmt_ref_srcflatten_local_value (dstLoc := dstLoc) kind prot mask
                  (Place.proj (Place.deref pp) f) cs so h
              exact h_val0 cs so' h')
            h_envD h_step

/-- The source-flattening recursion for a DEREF destination. Same shape
    as `ref_proj_src_local_simulation`; the base case additionally
    flattens the DESTINATION chain, composing both transfers into the
    threaded `stmt0`. -/
theorem ref_proj_src_deref_simulation
    {τ : LayoutTy} {σ : LayoutTy}
    {P : Place Γ (obseq.LayoutTy.PtrL (obseq.LayoutTy.PtrL τ))}
    {sbase : Place Γ σ} {f : PathTo σ τ}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (compProg : oseair.Prog)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    {stmt0 : Stmt Γ}
    (h_stmt : prog.get? s_mir.pc = some stmt0)
    (h_run0 : ∀ cs, CheckedCompilerM.run (compileStmtChecked stmt0) cs
      = CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.deref P) (.ref kind prot mask (.proj sbase f)))) cs)
    (h_val0 : ∀ cs so, CheckedCompilerM.value
        (compileStmtChecked
          (Stmt.assign (.deref P) (.ref kind prot mask (.proj sbase f)))) cs
        = Except.ok so →
      ∃ so', CheckedCompilerM.value (compileStmtChecked stmt0) cs
        = Except.ok so')
    (h_step : mirlite.stepStmt MSB s_mir
      (.assign (.deref P) (.ref kind prot mask (.proj sbase f))) = .ok s_mir') :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' := by
  induction sbase with
  | «local» srcLoc =>
      cases h_envS : mirlite.Env.lookup s_mir.env srcLoc with
      | some bS =>
          rw [stepStmt_assign_dstderef_flatten] at h_step
          obtain ⟨ρt', s_osea', n, h_incr, h_run, h_inv'⟩ :=
            ref_derefdst_projsrc_simulation (P := flattenPlace P) kind prot mask
              compProg (PtrChain_flatten_deref P) h_comp h_inv h_stmt
              (fun cs => (h_run0 cs).trans
                (compileStmt_assign_derefdst_flatten_run _ cs))
              (fun cs so h => by
                obtain ⟨so', h'⟩ :=
                  compileStmt_assign_derefdst_flatten_value _ cs so h
                exact h_val0 cs so' h')
              h_envS h_step
          exact ⟨ρa, ρt', s_osea', n, AddrRenameIncr.refl ρa, h_incr,
            h_run, h_inv'⟩
      | none =>
          exfalso
          simp only [mirlite.stepStmt, mirlite.doAssign] at h_step
          cases h_prep : mirlite.preparePlaceAssign MSB s_mir (Place.deref P) with
          | err m => rw [h_prep] at h_step; simp at h_step
          | ok s1 =>
              have h_pre : s1 = s_mir := by
                simp only [mirlite.preparePlaceAssign] at h_prep
                split at h_prep
                · cases h_prep; rfl
                · simp [mirlite.allocateRoot] at h_prep
              rw [h_prep] at h_step
              rw [h_pre] at h_step
              simp [mirlite.evalRExpr, mirlite.resolvePlaceAcc, h_envS] at h_step
  | proj b q ih =>
      refine ih
        (fun cs => (h_run0 cs).trans
          (compileStmt_ref_srcproj_assoc_deref_run (P := P) kind prot mask b q f cs))
        (fun cs so h => by
          obtain ⟨so', h'⟩ :=
            compileStmt_ref_srcproj_assoc_deref_value (P := P) kind prot mask b q f cs so h
          exact h_val0 cs so' h')
        ?_
      rw [← stepStmt_assign_refsrc_projassoc s_mir (Place.deref P)
        kind prot mask b q f]
      exact h_step
  | deref pp =>
      -- CLOSED: `*chain := &kind (*p).f`, the TWO-MOTHER leaf. Both
      -- chains are flattened first, so both spines come from
      -- `PtrChain_flatten_deref`.
      rw [stepStmt_assign_dstderef_flatten] at h_step
      rw [stepStmt_assign_refsrc_anyflatten] at h_step
      obtain ⟨ρt', s_osea', n, h_incr, h_run, h_inv'⟩ :=
        ref_derefdst_derefprojsrc_simulation (D := flattenPlace P)
          (P := flattenPlace pp) (f := f) kind prot mask compProg
          (PtrChain_flatten_deref P) (PtrChain_flatten_deref pp)
          h_comp h_inv h_stmt
          (fun cs => ((h_run0 cs).trans
            (compileStmt_assign_derefdst_flatten_run _ cs)).trans
            (compileStmt_ref_srcflatten_deref_run (P := flattenPlace P)
              kind prot mask (Place.proj (Place.deref pp) f) cs))
          (fun cs so h => by
            obtain ⟨so', h'⟩ :=
              compileStmt_ref_srcflatten_deref_value (P := flattenPlace P)
                kind prot mask (Place.proj (Place.deref pp) f) cs so h
            obtain ⟨so'', h''⟩ :=
              compileStmt_assign_derefdst_flatten_value _ cs so' h'
            exact h_val0 cs so'' h'')
          h_step
      exact ⟨ρa, ρt', s_osea', n, AddrRenameIncr.refl ρa, h_incr, h_run, h_inv'⟩

/-- LEAF 3 (the dispatcher): per-statement simulation for
    `.assign dst (.ref kind prot mask src)`, decomposed by the shapes of
    the two places. Regime L→L (both bound locals, any referent size) is
    CLOSED by `ref_local_local_simulation`; the residuals are named. -/
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
  cases dst with
  | «local» dstLoc =>
      cases src with
      | «local» srcLoc =>
          cases h_envD : mirlite.Env.lookup s_mir.env dstLoc with
          | some bD =>
              cases h_envS : mirlite.Env.lookup s_mir.env srcLoc with
              | some bS =>
                  obtain ⟨ρt', s_osea', n, h_incr, h_run, h_inv'⟩ :=
                    ref_local_local_simulation kind prot mask compProg h_comp h_inv
                      h_stmt h_envD h_envS h_step
                  exact ⟨ρa, ρt', s_osea', n, AddrRenameIncr.refl ρa, h_incr, h_run, h_inv'⟩
              | none =>
                  -- `&src` of an unbound local: the source errs at resolution
                  exfalso
                  simp [mirPrep, mirlite.stepStmt, mirlite.doAssign, mirlite.doAssignCont,
                    h_envD, mirlite.resolvePlaceAcc, h_envS, mirlite.evalRExpr] at h_step
          | none =>
              cases h_envS : mirlite.Env.lookup s_mir.env srcLoc with
              | some bS =>
                  exact ref_fresh_dst_simulation kind prot mask compProg h_comp h_inv
                    h_stmt h_envD h_envS h_step
              | none =>
                  -- `&src` of an unbound local: the source errs at resolution
                  exfalso
                  have h_ne := ref_dst_src_idx_ne dstLoc srcLoc
                  simp only [mirlite.stepStmt, mirlite.doAssign] at h_step
                  cases h_prep : mirlite.preparePlaceAssign MSB s_mir
                      (Place.local dstLoc) with
                  | err m => rw [h_prep] at h_step; simp at h_step
                  | ok s1 =>
                      rw [h_prep] at h_step
                      have hS1 : mirlite.Env.lookup s1.env srcLoc = none := by
                        rw [prepare_lookup_ne h_ne h_prep]; exact h_envS
                      simp [mirlite.evalRExpr, mirlite.resolvePlaceAcc, hS1] at h_step
      | proj sbase f =>
          -- CLOSED for any source base that flattens to a LOCAL: the
          -- source-flattening recursion reassociates nested projections
          -- and lands in the proj-over-local leaves
          exact ref_proj_src_local_simulation kind prot mask compProg h_comp h_inv
            h_stmt (fun _ => rfl) (fun _ so h => ⟨so, h⟩) h_step
      | deref pp =>
          cases h_envD : mirlite.Env.lookup s_mir.env dstLoc with
          | some bD =>
              -- CLOSED: `dst := &kind *chain` — flatten-normalized, TOTAL
              rw [stepStmt_assign_refsrc_flatten] at h_step
              obtain ⟨ρt', s_osea', n, h_incr, h_run, h_inv'⟩ :=
                ref_deref_local_simulation (P := flattenPlace pp) kind prot mask
                  compProg (PtrChain_flatten_deref pp) h_comp h_inv h_stmt
                  (fun cs => compileStmt_ref_derefsrc_flatten_run kind prot mask cs)
                  (fun cs so h =>
                    compileStmt_ref_derefsrc_flatten_value kind prot mask cs so h)
                  h_envD h_step
              exact ⟨ρa, ρt', s_osea', n, AddrRenameIncr.refl ρa, h_incr,
                h_run, h_inv'⟩
          | none =>
              -- CLOSED: `dst := &kind *chain` with `dst` UNBOUND (regime B)
              rw [stepStmt_assign_refsrc_flatten] at h_step
              exact ref_fresh_derefsrc_simulation (P := flattenPlace pp) kind prot mask
                compProg (PtrChain_flatten_deref pp) h_comp h_inv h_stmt
                (fun cs => compileStmt_ref_derefsrc_flatten_run kind prot mask cs)
                (fun cs so h =>
                  compileStmt_ref_derefsrc_flatten_value kind prot mask cs so h)
                h_envD h_step
  | proj dbase g =>
      exact ref_proj_dst_simulation kind prot mask compProg h_comp h_inv h_stmt
        (fun _ => rfl) (fun _ so h => ⟨so, h⟩) h_step
  | deref P =>
      cases src with
      | «local» srcLoc =>
          cases h_envS : mirlite.Env.lookup s_mir.env srcLoc with
          | some bS =>
              -- CLOSED: `*chain := &kind src` — flatten-normalized, TOTAL
              rw [stepStmt_assign_dstderef_flatten] at h_step
              obtain ⟨ρt', s_osea', n, h_incr, h_run, h_inv'⟩ :=
                ref_derefdst_local_simulation (P := flattenPlace P) kind prot mask
                  compProg (PtrChain_flatten_deref P) h_comp h_inv h_stmt
                  (fun cs => compileStmt_assign_derefdst_flatten_run _ cs)
                  (fun cs so h =>
                    compileStmt_assign_derefdst_flatten_value _ cs so h)
                  h_envS h_step
              exact ⟨ρa, ρt', s_osea', n, AddrRenameIncr.refl ρa, h_incr,
                h_run, h_inv'⟩
          | none =>
                -- `&src` of an unbound local: the source errs at resolution
                exfalso
                simp only [mirlite.stepStmt, mirlite.doAssign] at h_step
                cases h_prep : mirlite.preparePlaceAssign MSB s_mir (Place.deref P) with
                | err m => rw [h_prep] at h_step; simp at h_step
                | ok s1 =>
                    have h_pre : s1 = s_mir := by
                      simp only [mirlite.preparePlaceAssign] at h_prep
                      split at h_prep
                      · cases h_prep; rfl
                      · simp [mirlite.allocateRoot] at h_prep
                    rw [h_prep] at h_step
                    rw [h_pre] at h_step
                    simp [mirlite.evalRExpr, mirlite.resolvePlaceAcc, h_envS] at h_step
      | proj sbase f =>
          -- CLOSED for any source base that flattens to a LOCAL: the
          -- source-flattening recursion, under a deref destination
          exact ref_proj_src_deref_simulation kind prot mask compProg h_comp h_inv
            h_stmt (fun _ => rfl) (fun _ so h => ⟨so, h⟩) h_step
      | deref pp =>
          -- The nil-projection eta MERGES this site with the projected
          -- deref source under a deref destination: `*chain := &kind *P`
          -- compiles exactly as `*chain := &kind (*P).nil`.
          exact ref_proj_src_deref_simulation (sbase := Place.deref pp) (f := PathTo.nil)
            kind prot mask compProg h_comp h_inv h_stmt
            (fun cs => compileStmt_ref_srcnil_deref_run (D := P) kind prot mask pp cs)
            (fun cs so h =>
              compileStmt_ref_srcnil_deref_value (D := P) kind prot mask pp cs so h)
            (by rw [← stepStmt_assign_refsrc_nil]; exact h_step)

end obseq3.proof
