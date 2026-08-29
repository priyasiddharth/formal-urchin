import obseq3.proof.common
import obseq3.proof.permsim_transport
import obseq3.proof.spine

namespace obseq3.proof

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
  simp only [mirlite.preparePlaceAssign, mirlite.resolvePlace?] at h
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
theorem compileStmt_ref_local_local_run
    {Γ : Ctx} {τ : LayoutTy}
    {dstLoc : Local Γ (obseq.LayoutTy.PtrL τ)} {srcLoc : Local Γ τ}
    {cs : CompilerState} {dstReg srcReg : Register}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = some (dstReg, obseq.LayoutTy.PtrL τ))
    (h_src : getPlaceInfo cs srcLoc.idx.1 = some (srcReg, τ)) :
    CheckedCompilerM.run
        (compileStmtChecked
          (Stmt.assign (.local dstLoc) (.ref kind prot mask (.local srcLoc)))) cs
      = emit (emit { cs with nextReg := cs.nextReg + 1 }
          [Instr.Assgn (Register.R cs.nextReg)
            (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)])
          [Instr.RStore obseq.TyVal.PTy (Register.R cs.nextReg) dstReg] := by
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_existing h_dst
  obtain ⟨h_prun, placeOut, h_pval, h_pres⟩ :=
    placeToRegChecked_local_existing (kind := kind) h_src
  simp [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked, placeToBorrowRegChecked,
    h_run, h_val, h_prun, h_pval, h_pres]
  simp [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM,
    cleanupInstrs, emit_nil]

/-- The fragment of `dst := &src` when the DESTINATION is unmapped: the
    root `Alloc` that `ensureLocalRegE` emits, then the `Borrow` into a
    fresh temp, then the `RStore`. Three instructions, and the only ref
    shape whose compiler state grows a `placeRegMap` entry. -/
theorem compileStmt_ref_fresh_local_run
    {Γ : Ctx} {τ : LayoutTy}
    {dstLoc : Local Γ (obseq.LayoutTy.PtrL τ)} {srcLoc : Local Γ τ}
    {cs : CompilerState} {srcReg : Register}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = none)
    (h_src : getPlaceInfo cs srcLoc.idx.1 = some (srcReg, τ)) :
    CheckedCompilerM.run
        (compileStmtChecked
          (Stmt.assign (.local dstLoc) (.ref kind prot mask (.local srcLoc)))) cs
      = emit (emit
          { (setPlaceInfo
              (emit { cs with nextReg := cs.nextReg + 1 }
                [Instr.Assgn (Register.R cs.nextReg)
                  (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))])
              dstLoc.idx.1 (Register.R cs.nextReg, obseq.LayoutTy.PtrL τ)) with
              nextReg := cs.nextReg + 1 + 1 }
          [Instr.Assgn (Register.R (cs.nextReg + 1))
            (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)])
          [Instr.RStore obseq.TyVal.PTy (Register.R (cs.nextReg + 1))
            (Register.R cs.nextReg)] := by
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
  obtain ⟨h_prun, placeOut, h_pval, h_pres⟩ :=
    placeToRegChecked_local_existing (kind := kind) h_srcPost
  simp [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked, placeToBorrowRegChecked,
    h_run, h_val, h_prun, h_pval, h_pres]
  simp [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM,
    cleanupInstrs, emit_nil, setPlaceInfo, emit]
  funext label
  rw [if_neg (fun h => by rcases h with ⟨h1, h2⟩; omega)]

/-- The fresh-destination statement lowers. -/
theorem compileStmt_ref_fresh_local_value
    {Γ : Ctx} {τ : LayoutTy}
    {dstLoc : Local Γ (obseq.LayoutTy.PtrL τ)} {srcLoc : Local Γ τ}
    {cs : CompilerState} {srcReg : Register}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = none)
    (h_src : getPlaceInfo cs srcLoc.idx.1 = some (srcReg, τ)) :
    ∃ so, CheckedCompilerM.value
      (compileStmtChecked
        (Stmt.assign (.local dstLoc) (.ref kind prot mask (.local srcLoc)))) cs
      = Except.ok so := by
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
  obtain ⟨h_prun, placeOut, h_pval, h_pres⟩ :=
    placeToRegChecked_local_existing (kind := kind) h_srcPost
  simp only [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked, placeToBorrowRegChecked,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
    h_run, h_pval]
  exact ⟨_, rfl⟩

/-- The fragment of `dst := &src.f` when `dst` is a mapped local and the
    borrowed place is a PROJECTED field of a mapped local: one `Borrow` at
    the field's offset over the field's length, then the `RStore`. Same
    two instructions as the L→L fragment — projection only moves the
    offset, thanks to the reassociating lowering. -/
theorem compileStmt_ref_proj_local_run
    {Γ : Ctx} {τ σb : LayoutTy}
    {dstLoc : Local Γ (obseq.LayoutTy.PtrL τ)} {srcLoc : Local Γ σb}
    {f : PathTo σb τ}
    {cs : CompilerState} {dstReg srcReg : Register}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = some (dstReg, obseq.LayoutTy.PtrL τ))
    (h_src : getPlaceInfo cs srcLoc.idx.1 = some (srcReg, σb)) :
    CheckedCompilerM.run
        (compileStmtChecked
          (Stmt.assign (.local dstLoc)
            (.ref kind prot mask (.proj (.local srcLoc) f)))) cs
      = emit (emit { cs with nextReg := cs.nextReg + 1 }
          [Instr.Assgn (Register.R cs.nextReg)
            (Rhs.Borrow kind prot mask (blockSize τ) srcReg (pathOffset f))])
          [Instr.RStore obseq.TyVal.PTy (Register.R cs.nextReg) dstReg] := by
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_existing h_dst
  have h_run' : (ensureLocalRegE dstLoc cs).snd.val = cs := h_run
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
  simp [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked, h_borrow_eq,
    h_run, h_run', h_val, h_prun, h_pval, h_pres]
  simp [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM,
    cleanupInstrs, emit_nil]

/-- The proj-src statement lowers. -/
theorem compileStmt_ref_proj_local_value
    {Γ : Ctx} {τ σb : LayoutTy}
    {dstLoc : Local Γ (obseq.LayoutTy.PtrL τ)} {srcLoc : Local Γ σb}
    {f : PathTo σb τ}
    {cs : CompilerState} {dstReg srcReg : Register}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = some (dstReg, obseq.LayoutTy.PtrL τ))
    (h_src : getPlaceInfo cs srcLoc.idx.1 = some (srcReg, σb)) :
    ∃ so, CheckedCompilerM.value
      (compileStmtChecked
        (Stmt.assign (.local dstLoc)
          (.ref kind prot mask (.proj (.local srcLoc) f)))) cs
      = Except.ok so := by
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_existing h_dst
  have h_run' : (ensureLocalRegE dstLoc cs).snd.val = cs := h_run
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
  simp only [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked, h_borrow_eq,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
    h_run, h_pval]
  exact ⟨_, rfl⟩

/-- The fragment of `dst := &kind *P` when `dst` is a mapped local and `P`
    lowers with no cleanup (e.g. a load spine): the pointer is loaded,
    the referent is borrowed through the LOADED tag at offset 0, and the
    reference is stored: `[P-code; Load; Borrow; RStore]`. -/
theorem compileStmt_ref_deref_run
    {Γ : Ctx} {τ : LayoutTy}
    {dstLoc : Local Γ (obseq.LayoutTy.PtrL τ)}
    {P : Place Γ (obseq.LayoutTy.PtrL τ)}
    {cs : CompilerState} {dstReg : Register}
    {pOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared P)}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = some (dstReg, obseq.LayoutTy.PtrL τ))
    (h_pval : CheckedCompilerM.value (placeToRegChecked RefKind.Shared P) cs
      = Except.ok pOut)
    (h_pclean : pOut.result.cleanup = []) :
    CheckedCompilerM.run
        (compileStmtChecked
          (Stmt.assign (.local dstLoc) (.ref kind prot mask (.deref P)))) cs
      = emit (emit
          { (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) cs) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) cs).nextReg + 1 }
              [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) cs).nextReg)
                (Rhs.Load obseq.TyVal.PTy pOut.result.reg)]) with
              nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) cs).nextReg + 1 + 1 }
          [Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) cs).nextReg + 1))
            (Rhs.Borrow kind prot mask (blockSize τ)
              (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) cs).nextReg) 0)])
          [Instr.RStore obseq.TyVal.PTy (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) cs).nextReg + 1)) dstReg] := by
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_existing h_dst
  have h_run' : (ensureLocalRegE dstLoc cs).snd.val = cs := h_run
  have h_borrow_eq : placeToBorrowRegChecked (Γ := Γ) kind prot mask (.deref P)
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
  simp [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked, h_borrow_eq,
    h_run, h_run', h_val, h_pval]
  simp [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM,
    cleanupInstrs, h_pclean, emit_nil]
  rfl

/-- The deref-src statement lowers. -/
theorem compileStmt_ref_deref_value
    {Γ : Ctx} {τ : LayoutTy}
    {dstLoc : Local Γ (obseq.LayoutTy.PtrL τ)}
    {P : Place Γ (obseq.LayoutTy.PtrL τ)}
    {cs : CompilerState} {dstReg : Register}
    {pOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared P)}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = some (dstReg, obseq.LayoutTy.PtrL τ))
    (h_pval : CheckedCompilerM.value (placeToRegChecked RefKind.Shared P) cs
      = Except.ok pOut) :
    ∃ so, CheckedCompilerM.value
      (compileStmtChecked
        (Stmt.assign (.local dstLoc) (.ref kind prot mask (.deref P)))) cs
      = Except.ok so := by
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_existing h_dst
  have h_run' : (ensureLocalRegE dstLoc cs).snd.val = cs := h_run
  have h_borrow_eq : placeToBorrowRegChecked (Γ := Γ) kind prot mask (.deref P)
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
  simp only [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked, h_borrow_eq,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
    h_run, h_pval]
  exact ⟨_, rfl⟩

/-- The statement lowers (its checked value is `ok`) in this regime. -/
theorem compileStmt_ref_local_local_value
    {Γ : Ctx} {τ : LayoutTy}
    {dstLoc : Local Γ (obseq.LayoutTy.PtrL τ)} {srcLoc : Local Γ τ}
    {cs : CompilerState} {dstReg srcReg : Register}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = some (dstReg, obseq.LayoutTy.PtrL τ))
    (h_src : getPlaceInfo cs srcLoc.idx.1 = some (srcReg, τ)) :
    ∃ so, CheckedCompilerM.value
      (compileStmtChecked
        (Stmt.assign (.local dstLoc) (.ref kind prot mask (.local srcLoc)))) cs
      = Except.ok so := by
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_existing h_dst
  obtain ⟨h_prun, placeOut, h_pval, h_pres⟩ :=
    placeToRegChecked_local_existing (kind := kind) h_src
  simp only [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked, placeToBorrowRegChecked,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
    h_run, h_pval]
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
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
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
  obtain ⟨dstReg, baseD, tagD, h_piD, h_entryD, h_raD, h_rtD, h_nwD, -⟩ :=
    h_lbs dstLoc bD h_envD
  obtain ⟨srcReg, baseS, tagS, h_piS, h_entryS, h_raS, h_rtS, h_nwS, h_domS⟩ :=
    h_lbs srcLoc bS h_envS
  have h_baseD : baseD = bD.addr := (h_id_a _ _ h_raD).symm
  have h_baseS : baseS = bS.addr := (h_id_a _ _ h_raS).symm
  subst h_baseD
  subst h_baseS
  -- §1 invert the source step: prepare is a no-op, both locals resolve,
  -- the retag succeeds, the pointer is written
  simp only [mirlite.stepStmt, mirlite.doAssign, mirlite.doAssignCont, mirlite.preparePlaceAssign,
    mirlite.resolvePlace?, h_envD, mirlite.resolvePlaceAcc, h_envS,
    mirlite.evalRExpr] at h_step
  rw [if_neg (Nat.lt_irrefl (bS.addr + blockSize τ))] at h_step
  cases h_ref_src : MSB.ref s_mir.perms bS.addr (blockSize τ) bS.tag kind prot mask with
  | error e => rw [h_ref_src] at h_step; simp at h_step
  | ok pr =>
      obtain ⟨perms', freshTag⟩ := pr
      rw [h_ref_src] at h_step
      simp only at h_step
      -- §2 the retag on the target, with ρt extended at the fresh pair
      obtain ⟨tgtPerms, h_ref_tgt, h_fresh_eq, h_incr_t, h_wf_t', h_tbd', h_psim'⟩ :=
        sb_ref_respects_PermSim h_psim h_wf_t h_tbd h_rtS h_nwS h_ref_src
      subst h_fresh_eq
      have h_rt_new : (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag)
          s_mir.perms.NextTag = some s_osea.perms.NextTag :=
        TagRenameMap.extend_self _ _ _
      have h0 : wildcardTag < s_mir.perms.NextTag := (h_tbd _ _ h_wf_t.2).1
      have h_nw_new : (s_mir.perms.NextTag == wildcardTag) = false := by grind
      have h_rtD' : (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag) bD.tag
          = some tagD := h_incr_t _ _ h_rtD
      -- §3 the fragment and its two instructions
      have h_stmtRun := compileStmt_ref_local_local_run (cs := csPrefix) kind prot mask
        h_piD h_piS
      obtain ⟨stmtOut, h_stmtOut⟩ :=
        compileStmt_ref_local_local_value (cs := csPrefix) kind prot mask h_piD h_piS
      have h_code1 : compProg s_osea.pc
          = some (Instr.Assgn (Register.R csPrefix.nextReg)
              (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)) := by
        rw [h_pc]
        refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
        · rw [h_stmtRun]
          simp only [emit, List.length_cons, List.length_nil]
          omega
        · rw [h_stmtRun]
          rw [emit_code_lt_nextLabel _ _ (by
            simp only [emit, List.length_cons, List.length_nil]; omega)]
          have h := emit_code_at_new { csPrefix with nextReg := csPrefix.nextReg + 1 }
            [Instr.Assgn (Register.R csPrefix.nextReg)
              (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)] (k := 0) (by simp)
          simpa using h
      have h_code2 : compProg (s_osea.pc + 1)
          = some (Instr.RStore obseq.TyVal.PTy (Register.R csPrefix.nextReg) dstReg) := by
        rw [h_pc]
        refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
        · rw [h_stmtRun]
          simp only [emit, List.length_cons, List.length_nil]
          omega
        · rw [h_stmtRun]
          simp [emit]
      -- §4 execute the Borrow
      have h_ref_tgt' : MSB.ref s_osea.perms (bS.addr + 0 + 0) (blockSize τ) tagS kind prot mask
          = .ok (tgtPerms, s_osea.perms.NextTag) := by
        simpa using h_ref_tgt
      have h_run1 := runN_Assgn_Borrow_step compProg s_osea
        (Register.R csPrefix.nextReg) srcReg kind prot mask (blockSize τ) 0
        h_code1 h_entryS (by
          show bS.addr + 0 + 0 + blockSize τ ≤ bS.addr + blockSize τ
          simp only [Nat.add_zero]
          exact Nat.le_refl _) h_ref_tgt'
      -- §5 the pointer write: source side destructured, target via BRIDGE 2
      simp only [h_envD] at h_step
      have h_w := h_step
      simp only [mirlite.writeResolvedPlace] at h_w
      split at h_w
      · simp at h_w
      · rename_i h_nb
        split at h_w
        · rename_i perms'' h_useMut_src
          cases h_w
          obtain ⟨p2, h_useMut_tgt, h_psim2⟩ :=
            sb_write_respects_PermSim h_psim' h_wf_t' h_rtD' h_nwD h_useMut_src
          have h_regne : dstReg ≠ Register.R csPrefix.nextReg := by
            cases dstReg with
            | R n =>
                have h_lt := h_prb _ _ _ h_piD
                grind [RegisterBelow]
          -- the post-Borrow register file
          have h_entryD1 : PtrRegisterEntry
              (oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
                (obseq.TyVal.PTy, [Val.Ptr bS.addr (0 + 0) (blockSize τ) s_osea.perms.NextTag]))
              dstReg bD.addr (bD.addr - bD.addr) (blockSize (obseq.LayoutTy.PtrL τ)) tagD := by
            rw [Nat.sub_self]
            show oseair.RegMap.lookup _ _ = _
            rw [RegMap.lookup_insert_ne _ h_regne]
            exact h_entryD
          obtain ⟨h_wtp, h_sms'⟩ :=
            writeThroughPtr_sim (τ := obseq.LayoutTy.PtrL τ)
              (s_osea :=
                { s_osea with
                    perms := tgtPerms,
                    reg := oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
                      (obseq.TyVal.PTy,
                        [Val.Ptr bS.addr (0 + 0) (blockSize τ) s_osea.perms.NextTag]),
                    pc := s_osea.pc + 1 })
              (resolved := { addr := bD.addr, tag := bD.tag, allocBase := bD.addr,
                             allocSize := blockSize (obseq.LayoutTy.PtrL τ) })
              "RStore Invalid Regs"
              [mirlite.MemValue.ptrVal bS.addr (bS.addr - bS.addr) (blockSize τ) s_mir.perms.NextTag]
              [Val.Ptr bS.addr (0 + 0) (blockSize τ) s_osea.perms.NextTag] rfl
              ⟨⟨h_raS, by simp, rfl, h_rt_new, h_nw_new,
                h_domS⟩, trivial⟩
              h_id_a h_entryD1 h_useMut_tgt
              (by exact SourceMemSim.rename_mono (AddrRenameIncr.refl ρa) h_incr_t h_sms)
              (Nat.le_refl _)
              (fun k hk => by
                simp [blockSize, Nat.lt_one_iff] at hk
                subst hk
                exact h_raD)
              h_step
          have h_run2 := runN_RStore_step compProg _ _ obseq.TyVal.PTy
            (Register.R csPrefix.nextReg) dstReg _ _ h_code2
            (RegMap.lookup_insert_self _ _ _)
            (by rw [RegMap.lookup_insert_ne _ h_regne]; exact h_entryD)
            h_wtp
          have h_run := (oseair_runN_add 1 1 s_osea compProg _ h_run1).trans h_run2
          -- §6 rebuild the invariant under the extended ρt
          refine ⟨_, _, 1 + 1, h_incr_t, h_run, ?_⟩
          refine ⟨CheckedCompilerM.run
            (compileStmtChecked
              (Stmt.assign (.local dstLoc) (.ref kind prot mask (.local srcLoc)))) csPrefix,
            ⟨prefixCompileState_succ h_csAt h_stmt h_stmtOut, ?_⟩, ?_, h_sms', h_psim2,
            h_id_a, h_wf_t', ?_, ?_, ?_, ?_⟩
          · -- label agreement at pc+2
            show s_osea.pc + 1 + 1 = _
            rw [h_pc, h_stmtRun]
            simp [emit]
          · -- LocalBindingSim: env unchanged; fresh temp register; ρt grew
            refine LocalBindingSim.placeRegMap_congr ?_
              (LocalBindingSim.insert_fresh_reg
                (LocalBindingSim.rename_mono (AddrRenameIncr.refl ρa) h_incr_t h_lbs)
                h_prb (Nat.le_refl _) rfl)
            rw [h_stmtRun]
            rfl
          · -- TagRenameBounded: the write mints nothing beyond the retag's tag
            show TagRenameBounded _ perms''.NextTag p2.NextTag
            rw [sb_write_NextTag h_useMut_src, sb_write_NextTag h_useMut_tgt]
            exact h_tbd'
          · -- AllocLockstep: stores only
            simp only [AllocLockstep, mirlite_writeWordSeq_addrStart,
              oseair_writeWordSeq_addrStart]
            exact h_alloc
          · -- UnboundLocalsUnmapped: env and placeRegMap both unchanged
            intro τ' loc' h_none
            rw [h_stmtRun, getPlaceInfo_emit, getPlaceInfo_emit]
            exact h_unmap loc' h_none
          · -- PlaceRegMapBound: placeRegMap unchanged, nextReg grew
            intro idx reg τ'' h_look
            rw [h_stmtRun] at h_look ⊢
            rw [getPlaceInfo_emit, getPlaceInfo_emit] at h_look
            refine RegisterBelow.mono ?_ (h_prb _ _ _ h_look)
            simp only [emit]
            omega
        · simp at h_w

/-- REGIME F→L, CLOSED: `&src` stored into an UNBOUND local. mirlite's
    prepare allocates the destination, so the fragment gains a leading
    root `Alloc` and BOTH renames grow — ρa by the identity pair
    (`AllocLockstep` makes the two allocators agree), and ρt TWICE in one
    statement: `sb_own` mints the destination's root tag, then `sb_ref`
    mints the reference tag. The second extension is well-formed because
    the first member hands back the `TagRenameBounded` at the intermediate
    counters, which is exactly the hypothesis the second one takes. -/
theorem ref_fresh_dst_simulation
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
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
  -- §1 the destination allocation
  simp only [mirlite.stepStmt, mirlite.doAssign] at h_step
  cases h_prep : mirlite.preparePlaceAssign MSB s_mir (Place.local dstLoc) with
  | err m => rw [h_prep] at h_step; simp at h_step
  | ok s1 =>
      rw [h_prep] at h_step
      -- invert prepare: the destination was unbound, so `allocateBase` ran
      have h_prep' := h_prep
      simp only [mirlite.preparePlaceAssign, mirlite.resolvePlace?, h_envD,
        mirlite.allocateRoot, mirlite.allocateBase, mirlite.allocate] at h_prep'
      cases h_own_src : MSB.own s_mir.perms s_mir.mem.addrStart
          (blockSize (obseq.LayoutTy.PtrL τ)) with
      | error e => rw [h_own_src] at h_prep'; simp at h_prep'
      | ok pr =>
          obtain ⟨permsOwned, tagD⟩ := pr
          rw [h_own_src] at h_prep'
          injection h_prep' with h_s1
          subst h_s1
          -- §2 resolve the destination (now bound) and the source (untouched)
          have hD1 : mirlite.Env.lookup
              (mirlite.Env.set s_mir.env dstLoc
                { addr := s_mir.mem.addrStart, tag := tagD }) dstLoc
              = some { addr := s_mir.mem.addrStart, tag := tagD } := by
            simp [mirlite.Env.lookup, mirlite.Env.set]
          have hS1 : mirlite.Env.lookup
              (mirlite.Env.set s_mir.env dstLoc
                { addr := s_mir.mem.addrStart, tag := tagD }) srcLoc
              = some bS := by
            simp only [mirlite.Env.lookup, mirlite.Env.set, if_neg h_idx_ne]
            exact h_envS
          simp only [mirlite.doAssignCont, mirlite.resolvePlaceAcc, hD1,
            mirlite.evalRExpr, hS1] at h_step
          rw [if_neg (Nat.lt_irrefl (bS.addr + blockSize τ))] at h_step
          -- §3 the retag on the source place
          cases h_ref_src : MSB.ref permsOwned bS.addr (blockSize τ) bS.tag kind prot mask with
          | error e => rw [h_ref_src] at h_step; simp at h_step
          | ok pr2 =>
              obtain ⟨perms', tagR⟩ := pr2
              rw [h_ref_src] at h_step
              simp only at h_step
              -- §4 FIRST ρt extension: the destination's root tag (sb_own)
              obtain ⟨tgtP1, h_own_tgt, h_tagD_eq, h_incr1, h_wf1, h_tbd1, h_psim1⟩ :=
                sb_own_respects_PermSim h_psim h_wf_t h_tbd h_own_src
              subst h_tagD_eq
              have h_addr_eq : s_osea.mem.addrStart = s_mir.mem.addrStart := h_alloc
              have h_szD : obseq.typeSize (layoutToTyVal (obseq.LayoutTy.PtrL τ))
                  = blockSize (obseq.LayoutTy.PtrL τ) := obseq.typeSize_layoutToTyVal _
              -- the source binding's facts move to the extended ρt
              have h_rtS1 := h_incr1 _ _ h_rtS
              -- §5 SECOND ρt extension: the reference tag (sb_ref), on top
              obtain ⟨tgtP2, h_ref_tgt, h_tagR_eq, h_incr2, h_wf2, h_tbd2, h_psim2⟩ :=
                sb_ref_respects_PermSim h_psim1 h_wf1 h_tbd1 h_rtS1 h_nwS h_ref_src
              subst h_tagR_eq
              have h_incr12 : TagRenameIncr ρt
                  (((ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag).extend
                    permsOwned.NextTag tgtP1.NextTag)) :=
                TagRenameIncr.trans h_incr1 h_incr2
              have h_rt_new : ((ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag).extend
                  permsOwned.NextTag tgtP1.NextTag) permsOwned.NextTag
                  = some tgtP1.NextTag := TagRenameMap.extend_self _ _ _
              have h_rtD_new : ((ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag).extend
                  permsOwned.NextTag tgtP1.NextTag) s_mir.perms.NextTag
                  = some s_osea.perms.NextTag :=
                h_incr2 _ _ (TagRenameMap.extend_self _ _ _)
              have h0 : wildcardTag < s_mir.perms.NextTag := (h_tbd _ _ h_wf_t.2).1
              have h_nwD : (s_mir.perms.NextTag == wildcardTag) = false := by grind
              have h1 : wildcardTag < permsOwned.NextTag := (h_tbd1 _ _ h_wf1.2).1
              have h_nwR : (permsOwned.NextTag == wildcardTag) = false := by grind
              -- §6 ρa grows too, at the identity pair
              have h_incr_a : AddrRenameIncr ρa
                  (ρa.extend s_mir.mem.addrStart s_mir.mem.addrStart) :=
                AddrRenameIncr.extend_id h_id_a _
              have h_id_a' : IdentityOnDomain
                  (ρa.extend s_mir.mem.addrStart s_mir.mem.addrStart) :=
                IdentityOnDomain.extend_id h_id_a _
              have h_ra_new : (ρa.extend s_mir.mem.addrStart s_mir.mem.addrStart)
                  s_mir.mem.addrStart = some s_mir.mem.addrStart :=
                AddrRenameMap.extend_self _ _ _
              have h_raS' := h_incr_a _ _ h_raS
              -- §7 the fragment: Alloc; Borrow; RStore
              have h_stmtRun := compileStmt_ref_fresh_local_run (cs := csPrefix)
                kind prot mask h_piD h_piS
              obtain ⟨stmtOut, h_stmtOut⟩ :=
                compileStmt_ref_fresh_local_value (cs := csPrefix) kind prot mask h_piD h_piS
              have h_code1 : compProg s_osea.pc
                  = some (Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))) := by
                rw [h_pc]
                refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
                · rw [h_stmtRun]
                  simp only [emit, setPlaceInfo, List.length_cons, List.length_nil]
                  omega
                · rw [h_stmtRun]
                  rw [emit_code_lt_nextLabel _ _ (by
                    simp only [emit, setPlaceInfo, List.length_cons, List.length_nil]; omega)]
                  rw [emit_code_lt_nextLabel _ _ (by
                    simp only [emit, setPlaceInfo, List.length_cons, List.length_nil]; omega)]
                  have h := emit_code_at_new { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))] (k := 0) (by simp)
                  simpa [setPlaceInfo] using h
              have h_code2 : compProg (s_osea.pc + 1)
                  = some (Instr.Assgn (Register.R (csPrefix.nextReg + 1))
                      (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)) := by
                rw [h_pc]
                refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
                · rw [h_stmtRun]
                  simp only [emit, setPlaceInfo, List.length_cons, List.length_nil]
                  omega
                · rw [h_stmtRun]
                  rw [emit_code_lt_nextLabel _ _ (by
                    simp only [emit, setPlaceInfo, List.length_cons, List.length_nil]; omega)]
                  have h := emit_code_at_new
                    { (setPlaceInfo
                        (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                          [Instr.Assgn (Register.R csPrefix.nextReg)
                            (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))])
                        dstLoc.idx.1 (Register.R csPrefix.nextReg, obseq.LayoutTy.PtrL τ)) with
                        nextReg := csPrefix.nextReg + 1 + 1 }
                    [Instr.Assgn (Register.R (csPrefix.nextReg + 1))
                      (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)] (k := 0) (by simp)
                  simpa [emit, setPlaceInfo] using h
              have h_code3 : compProg (s_osea.pc + 1 + 1)
                  = some (Instr.RStore obseq.TyVal.PTy (Register.R (csPrefix.nextReg + 1))
                      (Register.R csPrefix.nextReg)) := by
                rw [h_pc]
                refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
                · rw [h_stmtRun]
                  simp only [emit, setPlaceInfo, List.length_cons, List.length_nil]
                  omega
                · rw [h_stmtRun]
                  have h := emit_code_at_new
                    (emit { (setPlaceInfo
                        (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                          [Instr.Assgn (Register.R csPrefix.nextReg)
                            (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))])
                        dstLoc.idx.1 (Register.R csPrefix.nextReg, obseq.LayoutTy.PtrL τ)) with
                        nextReg := csPrefix.nextReg + 1 + 1 }
                      [Instr.Assgn (Register.R (csPrefix.nextReg + 1))
                        (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)])
                    [Instr.RStore obseq.TyVal.PTy (Register.R (csPrefix.nextReg + 1))
                      (Register.R csPrefix.nextReg)] (k := 0) (by simp)
                  simpa [emit, setPlaceInfo] using h
              -- §8 execute Alloc, then Borrow
              have h_own_tgt' : MSB.own s_osea.perms s_osea.mem.addrStart
                  (obseq.typeSize (layoutToTyVal (obseq.LayoutTy.PtrL τ)))
                  = .ok (tgtP1, s_osea.perms.NextTag) := by
                rw [h_szD, h_addr_eq]; exact h_own_tgt
              have h_run1 := runN_Assgn_Alloc_step compProg s_osea
                (Register.R csPrefix.nextReg) (layoutToTyVal (obseq.LayoutTy.PtrL τ))
                h_code1 h_own_tgt'
              have h_regne : srcReg ≠ Register.R csPrefix.nextReg := by
                cases srcReg with
                | R n => have h_lt := h_prb _ _ _ h_piS; grind [RegisterBelow]
              have h_entryS1 : PtrRegisterEntry
                  (oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
                    (obseq.TyVal.PTy, [Val.Ptr s_osea.mem.addrStart 0
                      (obseq.typeSize (layoutToTyVal (obseq.LayoutTy.PtrL τ)))
                      s_osea.perms.NextTag]))
                  srcReg bS.addr 0 (blockSize τ) tagS := by
                show oseair.RegMap.lookup _ _ = _
                rw [RegMap.lookup_insert_ne _ h_regne]
                exact h_entryS
              have h_ref_tgt' : MSB.ref tgtP1 (bS.addr + 0 + 0) (blockSize τ) tagS
                  kind prot mask = .ok (tgtP2, tgtP1.NextTag) := by simpa using h_ref_tgt
              have h_le2 : bS.addr + 0 + 0 + blockSize τ ≤ bS.addr + blockSize τ :=
                Nat.le_of_eq (by simp)
              have h_run2 := runN_Assgn_Borrow_step compProg
                { s_osea with
                    mem := (oseair.allocate s_osea.mem
                      (obseq.typeSize (layoutToTyVal (obseq.LayoutTy.PtrL τ)))).2,
                    perms := tgtP1,
                    reg := oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
                      (obseq.TyVal.PTy, [Val.Ptr s_osea.mem.addrStart 0
                        (obseq.typeSize (layoutToTyVal (obseq.LayoutTy.PtrL τ)))
                        s_osea.perms.NextTag]),
                    pc := s_osea.pc + 1 }
                (Register.R (csPrefix.nextReg + 1)) srcReg kind prot mask (blockSize τ) 0
                h_code2 h_entryS1 h_le2 h_ref_tgt'
              -- §9 the store: source side destructured, target via BRIDGE 2
              simp only [hD1] at h_step
              have h_w := h_step
              simp only [mirlite.writeResolvedPlace] at h_w
              split at h_w
              · simp at h_w
              · rename_i h_nb
                split at h_w
                · rename_i perms'' h_useMut_src
                  cases h_w
                  obtain ⟨p3, h_useMut_tgt, h_psim3⟩ :=
                    sb_write_respects_PermSim h_psim2 h_wf2 h_rtD_new h_nwD h_useMut_src
                  have h_regne2 : Register.R csPrefix.nextReg
                      ≠ Register.R (csPrefix.nextReg + 1) := by grind
                  have h_entryD2 : PtrRegisterEntry
                      (oseair.RegMap.insert
                        (oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
                          (obseq.TyVal.PTy, [Val.Ptr s_osea.mem.addrStart 0
                            (obseq.typeSize (layoutToTyVal (obseq.LayoutTy.PtrL τ)))
                            s_osea.perms.NextTag]))
                        (Register.R (csPrefix.nextReg + 1))
                        (obseq.TyVal.PTy, [Val.Ptr bS.addr (0 + 0) (blockSize τ)
                          tgtP1.NextTag]))
                      (Register.R csPrefix.nextReg) s_mir.mem.addrStart
                      (s_mir.mem.addrStart - s_mir.mem.addrStart)
                      (blockSize (obseq.LayoutTy.PtrL τ)) s_osea.perms.NextTag := by
                    rw [Nat.sub_self, ← h_addr_eq, ← h_szD]
                    show oseair.RegMap.lookup _ _ = _
                    rw [RegMap.lookup_insert_ne _ h_regne2]
                    exact RegMap.lookup_insert_self _ _ _
                  obtain ⟨h_wtp, h_sms'⟩ :=
                    writeThroughPtr_sim (τ := obseq.LayoutTy.PtrL τ)
                      (s_osea :=
                        { s_osea with
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
                      (resolved := { addr := s_mir.mem.addrStart, tag := s_mir.perms.NextTag,
                                     allocBase := s_mir.mem.addrStart,
                                     allocSize := blockSize (obseq.LayoutTy.PtrL τ) })
                      "RStore Invalid Regs"
                      [mirlite.MemValue.ptrVal bS.addr (bS.addr - bS.addr) (blockSize τ)
                        permsOwned.NextTag]
                      [Val.Ptr bS.addr (0 + 0) (blockSize τ) tgtP1.NextTag] rfl
                      ⟨⟨h_raS', by simp, rfl, h_rt_new, h_nwR,
                        fun k hk => ⟨(h_domS k hk).choose,
                          h_incr_a _ _ (h_domS k hk).choose_spec⟩⟩, trivial⟩
                      h_id_a' h_entryD2 h_useMut_tgt
                      (by exact SourceMemSim.rename_mono h_incr_a h_incr12 h_sms)
                      (Nat.le_refl _)
                      (fun k hk => by
                        simp [blockSize, Nat.lt_one_iff] at hk
                        subst hk
                        exact h_ra_new)
                      h_step
                  have h_run3 := runN_RStore_step compProg _ _ obseq.TyVal.PTy
                    (Register.R (csPrefix.nextReg + 1)) (Register.R csPrefix.nextReg) _ _
                    h_code3 (RegMap.lookup_insert_self _ _ _)
                    (by rw [RegMap.lookup_insert_ne _ h_regne2]
                        exact RegMap.lookup_insert_self _ _ _)
                    h_wtp
                  have h_run :=
                    (oseair_runN_add (1 + 1) 1 s_osea compProg _
                      ((oseair_runN_add 1 1 s_osea compProg _ h_run1).trans h_run2)).trans h_run3
                  -- §10 rebuild the invariant under both extended renames
                  refine ⟨_, _, _, 1 + 1 + 1, h_incr_a, h_incr12, h_run, ?_⟩
                  refine ⟨CheckedCompilerM.run
                    (compileStmtChecked
                      (Stmt.assign (.local dstLoc)
                        (.ref kind prot mask (.local srcLoc)))) csPrefix,
                    ⟨prefixCompileState_succ h_csAt h_stmt h_stmtOut, ?_⟩, ?_, h_sms',
                    h_psim3, h_id_a', h_wf2, ?_, ?_, ?_, ?_⟩
                  · -- label agreement at pc+3
                    show s_osea.pc + 1 + 1 + 1 = _
                    rw [h_pc, h_stmtRun]
                    simp [emit, setPlaceInfo]
                  · -- LocalBindingSim: the destination is now bound and mapped;
                    -- the others survive two fresh registers and the new entry
                    intro τ' loc' binding' h_env'
                    by_cases h_idx : loc'.idx = dstLoc.idx
                    · have h_ty : τ' = obseq.LayoutTy.PtrL τ := by
                        rw [← loc'.hTy, h_idx, dstLoc.hTy]
                      subst h_ty
                      have h_b : binding' = { addr := s_mir.mem.addrStart,
                                              tag := s_mir.perms.NextTag } := by
                        grind [mirlite.Env.lookup, mirlite.Env.set]
                      subst h_b
                      refine ⟨Register.R csPrefix.nextReg, s_mir.mem.addrStart,
                        s_osea.perms.NextTag, ?_, ?_, h_ra_new, h_rtD_new, h_nwD, ?_⟩
                      · rw [h_stmtRun, getPlaceInfo_emit, getPlaceInfo_emit,
                          getPlaceInfo_setNextReg,
                          show loc'.idx.1 = dstLoc.idx.1 from congrArg Fin.val h_idx]
                        exact getPlaceInfo_setPlaceInfo_self _ _ _
                      · show oseair.RegMap.lookup _ _ = _
                        rw [← h_addr_eq, ← h_szD, RegMap.lookup_insert_ne _ h_regne2]
                        exact RegMap.lookup_insert_self _ _ _
                      · intro k hk
                        have hk0 : k = 0 := by
                          simp [blockSize, obseq.layoutSize] at hk
                          omega
                        subst hk0
                        exact ⟨s_mir.mem.addrStart, h_ra_new⟩
                    · have h_env'' : mirlite.Env.lookup s_mir.env loc' = some binding' := by
                        grind [mirlite.Env.lookup, mirlite.Env.set]
                      obtain ⟨reg', base', tag', h_pi', h_entry', h_ra', h_rt', h_nw', h_dom'⟩ :=
                        h_lbs loc' binding' h_env''
                      have h_idxv : loc'.idx.1 ≠ dstLoc.idx.1 := by grind [Fin.ext]
                      have h_rne1 : reg' ≠ Register.R csPrefix.nextReg := by
                        cases reg' with
                        | R n => have h_lt := h_prb _ _ _ h_pi'; grind [RegisterBelow]
                      have h_rne2 : reg' ≠ Register.R (csPrefix.nextReg + 1) := by
                        cases reg' with
                        | R n => have h_lt := h_prb _ _ _ h_pi'; grind [RegisterBelow]
                      refine ⟨reg', base', tag', ?_, ?_, h_incr_a _ _ h_ra',
                        h_incr12 _ _ h_rt', h_nw',
                        fun k hk => ⟨(h_dom' k hk).choose,
                          h_incr_a _ _ (h_dom' k hk).choose_spec⟩⟩
                      · rw [h_stmtRun, getPlaceInfo_emit, getPlaceInfo_emit,
                          getPlaceInfo_setNextReg, getPlaceInfo_setPlaceInfo_ne _ h_idxv,
                          getPlaceInfo_emit]
                        exact h_pi'
                      · show oseair.RegMap.lookup _ _ = _
                        rw [RegMap.lookup_insert_ne _ h_rne2,
                          RegMap.lookup_insert_ne _ h_rne1]
                        exact h_entry'
                  · -- TagRenameBounded across the store
                    show TagRenameBounded _ perms''.NextTag p3.NextTag
                    rw [sb_write_NextTag h_useMut_src, sb_write_NextTag h_useMut_tgt]
                    exact h_tbd2
                  · -- AllocLockstep: both machines bumped by the same size, then stored
                    simp only [AllocLockstep, mirlite_writeWordSeq_addrStart,
                      oseair_writeWordSeq_addrStart, mirlite.allocate, oseair.allocate]
                    rw [h_addr_eq, h_szD]
                  · -- UnboundLocalsUnmapped: only the destination became mapped,
                    -- and it is now bound
                    intro τ' loc' h_none
                    by_cases h_idx : loc'.idx = dstLoc.idx
                    · exfalso
                      grind [mirlite.Env.lookup, mirlite.Env.set]
                    · have h_idxv : loc'.idx.1 ≠ dstLoc.idx.1 := by grind [Fin.ext]
                      have h_none' : mirlite.Env.lookup s_mir.env loc' = none := by
                        grind [mirlite.Env.lookup, mirlite.Env.set]
                      rw [h_stmtRun, getPlaceInfo_emit, getPlaceInfo_emit,
                        getPlaceInfo_setNextReg, getPlaceInfo_setPlaceInfo_ne _ h_idxv,
                        getPlaceInfo_emit]
                      exact h_unmap loc' h_none'
                  · -- PlaceRegMapBound: two fresh registers, both below nextReg+2
                    intro idx reg τ'' h_look
                    rw [h_stmtRun] at h_look ⊢
                    rw [getPlaceInfo_emit, getPlaceInfo_emit, getPlaceInfo_setNextReg] at h_look
                    by_cases h_i : idx = dstLoc.idx.1
                    · subst h_i
                      rw [getPlaceInfo_setPlaceInfo_self] at h_look
                      injection h_look with h_look'
                      have : reg = Register.R csPrefix.nextReg :=
                        (congrArg Prod.fst h_look').symm
                      subst this
                      show csPrefix.nextReg < _
                      simp only [emit, setPlaceInfo]
                      omega
                    · rw [getPlaceInfo_setPlaceInfo_ne _ h_i, getPlaceInfo_emit] at h_look
                      refine RegisterBelow.mono ?_ (h_prb _ _ _ h_look)
                      simp only [emit, setPlaceInfo]
                      omega
                · simp at h_w

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
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {τ σb : LayoutTy}
    {dstLoc : Local Γ (obseq.LayoutTy.PtrL τ)} {srcLoc : Local Γ σb}
    {f : PathTo σb τ}
    {bD bS : mirlite.Binding}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (compProg : oseair.Prog)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    (h_stmt : prog.get? s_mir.pc
      = some (.assign (.local dstLoc)
          (.ref kind prot mask (.proj (.local srcLoc) f))))
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
  obtain ⟨dstReg, baseD, tagD, h_piD, h_entryD, h_raD, h_rtD, h_nwD, -⟩ :=
    h_lbs dstLoc bD h_envD
  obtain ⟨srcReg, baseS, tagS, h_piS, h_entryS, h_raS, h_rtS, h_nwS, h_domS⟩ :=
    h_lbs srcLoc bS h_envS
  have h_baseD : baseD = bD.addr := (h_id_a _ _ h_raD).symm
  have h_baseS : baseS = bS.addr := (h_id_a _ _ h_raS).symm
  subst h_baseD
  subst h_baseS
  -- §1 invert the source step: both locals resolve, retag at the FIELD
  simp only [mirlite.stepStmt, mirlite.doAssign, mirlite.doAssignCont, mirlite.preparePlaceAssign,
    mirlite.resolvePlace?, h_envD, mirlite.resolvePlaceAcc, h_envS,
    mirlite.evalRExpr] at h_step
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
      -- §2 the retag on the target, ρt extended at the fresh pair
      obtain ⟨tgtPerms, h_ref_tgt, h_fresh_eq, h_incr_t, h_wf_t', h_tbd', h_psim'⟩ :=
        sb_ref_respects_PermSim h_psim h_wf_t h_tbd h_rtS h_nwS h_ref_src
      subst h_fresh_eq
      have h_rt_new : (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag)
          s_mir.perms.NextTag = some s_osea.perms.NextTag :=
        TagRenameMap.extend_self _ _ _
      have h0 : wildcardTag < s_mir.perms.NextTag := (h_tbd _ _ h_wf_t.2).1
      have h_nw_new : (s_mir.perms.NextTag == wildcardTag) = false := by grind
      -- §3 the fragment
      have h_stmtRun := compileStmt_ref_proj_local_run (cs := csPrefix) (f := f)
        kind prot mask h_piD h_piS
      obtain ⟨stmtOut, h_stmtOut⟩ :=
        compileStmt_ref_proj_local_value (cs := csPrefix) (f := f) kind prot mask h_piD h_piS
      have h_code1 : compProg s_osea.pc
          = some (Instr.Assgn (Register.R csPrefix.nextReg)
              (Rhs.Borrow kind prot mask (blockSize τ) srcReg (pathOffset f))) := by
        rw [h_pc]
        refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
        · rw [h_stmtRun]
          simp only [emit, List.length_cons, List.length_nil]
          omega
        · rw [h_stmtRun]
          rw [emit_code_lt_nextLabel _ _ (by
            simp only [emit, List.length_cons, List.length_nil]; omega)]
          have h := emit_code_at_new { csPrefix with nextReg := csPrefix.nextReg + 1 }
            [Instr.Assgn (Register.R csPrefix.nextReg)
              (Rhs.Borrow kind prot mask (blockSize τ) srcReg (pathOffset f))]
            (k := 0) (by simp)
          simpa using h
      have h_code2 : compProg (s_osea.pc + 1)
          = some (Instr.RStore obseq.TyVal.PTy (Register.R csPrefix.nextReg) dstReg) := by
        rw [h_pc]
        refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
        · rw [h_stmtRun]
          simp only [emit, List.length_cons, List.length_nil]
          omega
        · rw [h_stmtRun]
          have h := emit_code_at_new
            (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
              [Instr.Assgn (Register.R csPrefix.nextReg)
                (Rhs.Borrow kind prot mask (blockSize τ) srcReg (pathOffset f))])
            [Instr.RStore obseq.TyVal.PTy (Register.R csPrefix.nextReg) dstReg]
            (k := 0) (by simp)
          simpa [emit] using h
      -- §4 execute the Borrow: bounds by TYPING (field fits its layout)
      have h_le2 : bS.addr + 0 + pathOffset f + blockSize τ
          ≤ bS.addr + blockSize σb := by
        have h_fit := PathTo.offset_add_size_le f
        show bS.addr + 0 + pathOffset f + blockSize τ ≤ bS.addr + blockSize σb
        simp only [Nat.add_zero, Nat.add_assoc]
        exact Nat.add_le_add_left h_fit _
      have h_ref_tgt' : MSB.ref s_osea.perms (bS.addr + 0 + pathOffset f)
          (blockSize τ) tagS kind prot mask
          = .ok (tgtPerms, s_osea.perms.NextTag) := by
        simpa using h_ref_tgt
      have h_run1 := runN_Assgn_Borrow_step compProg s_osea
        (Register.R csPrefix.nextReg) srcReg kind prot mask (blockSize τ)
        (pathOffset f) h_code1 h_entryS h_le2 h_ref_tgt'
      -- §5 the pointer store via BRIDGE 2
      simp only [h_envD] at h_step
      have h_w := h_step
      simp only [mirlite.writeResolvedPlace] at h_w
      split at h_w
      · simp at h_w
      · rename_i h_nb
        split at h_w
        · rename_i perms'' h_useMut_src
          cases h_w
          obtain ⟨p2, h_useMut_tgt, h_psim2⟩ :=
            sb_write_respects_PermSim h_psim' h_wf_t'
              (h_incr_t _ _ h_rtD) h_nwD h_useMut_src
          have h_regne : dstReg ≠ Register.R csPrefix.nextReg := by
            cases dstReg with
            | R n =>
                have h_lt := h_prb _ _ _ h_piD
                grind [RegisterBelow]
          have h_entryD1 : PtrRegisterEntry
              (oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
                (obseq.TyVal.PTy, [Val.Ptr bS.addr (0 + pathOffset f) (blockSize σb)
                  s_osea.perms.NextTag]))
              dstReg bD.addr (bD.addr - bD.addr) (blockSize (obseq.LayoutTy.PtrL τ)) tagD := by
            rw [Nat.sub_self]
            show oseair.RegMap.lookup _ _ = _
            rw [RegMap.lookup_insert_ne _ h_regne]
            exact h_entryD
          obtain ⟨h_wtp, h_sms'⟩ :=
            writeThroughPtr_sim (τ := obseq.LayoutTy.PtrL τ)
              (s_osea :=
                { s_osea with
                    perms := tgtPerms,
                    reg := oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
                      (obseq.TyVal.PTy,
                        [Val.Ptr bS.addr (0 + pathOffset f) (blockSize σb)
                          s_osea.perms.NextTag]),
                    pc := s_osea.pc + 1 })
              (resolved := { addr := bD.addr, tag := bD.tag, allocBase := bD.addr,
                             allocSize := blockSize (obseq.LayoutTy.PtrL τ) })
              "RStore Invalid Regs"
              [mirlite.MemValue.ptrVal bS.addr (bS.addr + pathOffset f - bS.addr)
                (blockSize σb) s_mir.perms.NextTag]
              [Val.Ptr bS.addr (0 + pathOffset f) (blockSize σb) s_osea.perms.NextTag] rfl
              ⟨⟨h_raS, by simp [Nat.add_sub_cancel_left], rfl, h_rt_new, h_nw_new,
                fun k hk => ⟨(h_domS k hk).choose,
                  AddrRenameIncr.refl ρa _ _ (h_domS k hk).choose_spec⟩⟩, trivial⟩
              h_id_a h_entryD1 h_useMut_tgt
              (by exact SourceMemSim.rename_mono (AddrRenameIncr.refl ρa) h_incr_t h_sms)
              (Nat.le_refl _)
              (fun k hk => by
                have hk0 : k = 0 := by simpa using hk
                subst hk0
                rw [Nat.add_zero]
                exact h_raD)
              h_step
          have h_run2 := runN_RStore_step compProg _ _ obseq.TyVal.PTy
            (Register.R csPrefix.nextReg) dstReg _ _ h_code2
            (RegMap.lookup_insert_self _ _ _)
            (by rw [RegMap.lookup_insert_ne _ h_regne]; exact h_entryD)
            h_wtp
          have h_run := (oseair_runN_add 1 1 s_osea compProg _ h_run1).trans h_run2
          -- §6 rebuild the invariant under the extended ρt
          refine ⟨_, _, 1 + 1, h_incr_t, h_run, ?_⟩
          refine ⟨CheckedCompilerM.run
            (compileStmtChecked
              (Stmt.assign (.local dstLoc)
                (.ref kind prot mask (.proj (.local srcLoc) f)))) csPrefix,
            ⟨prefixCompileState_succ h_csAt h_stmt h_stmtOut, ?_⟩, ?_, h_sms', h_psim2,
            h_id_a, h_wf_t', ?_, ?_, ?_, ?_⟩
          · show s_osea.pc + 1 + 1 = _
            rw [h_pc, h_stmtRun]
            simp [emit]
          · refine LocalBindingSim.placeRegMap_congr ?_
              (LocalBindingSim.insert_fresh_reg
                (LocalBindingSim.rename_mono (AddrRenameIncr.refl ρa) h_incr_t h_lbs)
                h_prb (Nat.le_refl _) rfl)
            rw [h_stmtRun]
            rfl
          · show TagRenameBounded _ perms''.NextTag p2.NextTag
            rw [sb_write_NextTag h_useMut_src, sb_write_NextTag h_useMut_tgt]
            exact h_tbd'
          · simp only [AllocLockstep, mirlite_writeWordSeq_addrStart,
              oseair_writeWordSeq_addrStart]
            exact h_alloc
          · intro τ' loc' h_none
            rw [h_stmtRun, getPlaceInfo_emit, getPlaceInfo_emit]
            exact h_unmap loc' h_none
          · intro idx reg τ'' h_look
            rw [h_stmtRun] at h_look ⊢
            rw [getPlaceInfo_emit, getPlaceInfo_emit] at h_look
            refine RegisterBelow.mono ?_ (h_prb _ _ _ h_look)
            simp only [emit]
            omega
        · simp at h_w

/-- REGIME D→L, CLOSED 2026-08-28: a reference THROUGH A LOADED POINTER
    stored into a bound local — `dst := &kind *P` with `P` a load spine.
    Fragment: `[P-code; Load; Borrow(kind, offset 0); RStore]`. The target
    `Borrow`'s bounds check is discharged by the SOURCE's retag-
    dereferenceability check (the 2026-08-28 event fix) transported
    through `MemValSim`'s offset/size equalities on the loaded pointer —
    the shape that was UNPROVABLE before the event fix, because no
    invariant on untyped memory could supply the bound. `ρt` extends at
    the fresh pair; the RStore lands via BRIDGE 2 exactly as in P→L. -/
theorem ref_deref_local_simulation
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {τ : LayoutTy}
    {dstLoc : Local Γ (obseq.LayoutTy.PtrL τ)}
    {P : Place Γ (obseq.LayoutTy.PtrL τ)}
    {bD : mirlite.Binding}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (compProg : oseair.Prog)
    (h_spine : PtrChain P)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    (h_stmt : prog.get? s_mir.pc
      = some (.assign (.local dstLoc) (.ref kind prot mask (.deref P))))
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
  -- §1 invert the source step down to the loaded pointer
  simp only [mirlite.stepStmt, mirlite.doAssign, mirlite.doAssignCont, mirlite.preparePlaceAssign,
    mirlite.resolvePlace?, h_envD, mirlite.resolvePlaceAcc,
    mirlite.evalRExpr] at h_step
  cases h_dres : mirlite.resolvePlaceAcc MSB s_mir P with
  | error e => simp [h_dres] at h_step
  | ok pr =>
  obtain ⟨pRes, permsP⟩ := pr
  simp only [h_dres] at h_step
  by_cases h_qb : pRes.addr < pRes.allocBase ∨
      pRes.addr ≥ pRes.allocBase + pRes.allocSize
  · rw [if_pos h_qb] at h_step
    simp at h_step
  · rw [if_neg h_qb] at h_step
    cases h_qread : MSB.read permsP pRes.addr 1 pRes.tag with
    | error e => simp [h_qread] at h_step
    | ok permsP' =>
    simp only [h_qread] at h_step
    cases h_qfind : mirlite.Mem.find? s_mir.mem pRes.addr with
    | none => simp [h_qfind] at h_step
    | some mv =>
    cases mv with
    | undef => simp [h_qfind] at h_step
    | word w => simp [h_qfind] at h_step
    | ptrVal b o sz t =>
    simp only [h_qfind] at h_step
    -- §2 the retag-dereferenceability event check: source success bounds
    -- the referent inside the loaded pointer's extent
    by_cases h_fit : b + o + blockSize τ > b + sz
    · rw [if_pos h_fit] at h_step
      simp at h_step
    · rw [if_neg h_fit] at h_step
      cases h_ref_src : MSB.ref permsP' (b + o) (blockSize τ) t kind prot mask with
      | error e => rw [h_ref_src] at h_step; simp at h_step
      | ok pr2 =>
      obtain ⟨perms', freshTag⟩ := pr2
      rw [h_ref_src] at h_step
      simp only at h_step
      -- §3 compiler-side scaffolding: the statement lowers
      have h_mapped : PlaceInputsMapped csPrefix P :=
        placeInputsMapped_of_resolveAcc h_lbs h_dres
      obtain ⟨pOut0, h_pval0⟩ := placeToRegChecked_ok_of_placeInputsMapped
        (cs := csPrefix) (kind := RefKind.Shared) (p := P) h_mapped
      obtain ⟨stmtOut, h_stmtOut⟩ :=
        compileStmt_ref_deref_value (cs := csPrefix) kind prot mask h_piD h_pval0
      have h_borrow_eq : placeToBorrowRegChecked (Γ := Γ) kind prot mask (.deref P)
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
      have h_incr0 : StateIncr
          (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix)
          (CheckedCompilerM.run
            (placeToBorrowRegChecked kind prot mask (.deref P)) csPrefix) := by
        rw [h_borrow_eq, CheckedCompilerM.run_bind]
        cases h : CheckedCompilerM.value (placeToRegChecked RefKind.Shared P) csPrefix with
        | ok a => exact CheckedCompilerM.incr _ _
        | error e => exact StateIncr.refl _
      have h_pre_bind : compileRExprPreChecked
            (RExpr.ref (Γ := Γ) kind prot mask (.deref P))
          = (do
              let srcOut ← placeToBorrowRegChecked kind prot mask (.deref P)
              let srcRes := srcOut.result
              pure {
                store := fun dstPtr =>
                  [Instr.RStore obseq.TyVal.PTy srcRes.reg dstPtr],
                postCleanup := [],
                ev := fun _ => RExprToEvidence.ref kind prot mask (.deref P)
                  srcRes srcOut.evidence
              }) := rfl
      have h_pre_run : CheckedCompilerM.run
            (compileRExprPreChecked (RExpr.ref (Γ := Γ) kind prot mask (.deref P)))
            csPrefix
          = CheckedCompilerM.run
              (placeToBorrowRegChecked kind prot mask (.deref P)) csPrefix := by
        rw [h_pre_bind, CheckedCompilerM.run_bind]
        cases h : CheckedCompilerM.value
            (placeToBorrowRegChecked kind prot mask (.deref P)) csPrefix with
        | ok a => rfl
        | error e => rfl
      have h_rhs_bind : ∀ r : Register, compileRExprToChecked r
            (RExpr.ref kind prot mask (.deref P))
          = (do
              let pre ← compileRExprPreChecked
                (RExpr.ref kind prot mask (.deref P))
              let _ ← CheckedCompilerM.lift (emitM (pre.store r))
              let _ ← CheckedCompilerM.lift (emitM (cleanupInstrs pre.postCleanup))
              pure { result := (), evidence := pre.ev r }) := fun _ => rfl
      have h_incr1 : ∀ r : Register, StateIncr
          (CheckedCompilerM.run
            (placeToBorrowRegChecked kind prot mask (.deref P)) csPrefix)
          (CheckedCompilerM.run
            (compileRExprToChecked r (.ref kind prot mask (.deref P))) csPrefix) := by
        intro r
        rw [h_rhs_bind r, CheckedCompilerM.run_bind]
        cases h : CheckedCompilerM.value
            (compileRExprPreChecked
              (RExpr.ref (Γ := Γ) kind prot mask (.deref P))) csPrefix with
        | ok a => rw [h_pre_run] at *; exact CheckedCompilerM.incr _ _
        | error e => rw [h_pre_run] at *; exact StateIncr.refl _
      obtain ⟨h_erun, h_eval⟩ := ensureLocalRegE_existing h_piD
      have h_stmt_bind : compileStmtChecked
            (Stmt.assign (.local dstLoc) (.ref kind prot mask (.deref P)))
          = (do
              let dstOut ← CheckedCompilerM.lift (ensureLocalRegE dstLoc)
              let dstRes := dstOut.result
              let rhsOut ← compileRExprToChecked dstRes.reg
                (.ref kind prot mask (.deref P))
              pure {
                result := (),
                evidence := StmtEvidence.assignLocal dstLoc
                  (.ref kind prot mask (.deref P)) dstRes
                  dstOut.evidence rhsOut.evidence
              }) := rfl
      have h_incr2 : StateIncr
          (CheckedCompilerM.run
            (placeToBorrowRegChecked kind prot mask (.deref P)) csPrefix)
          (CheckedCompilerM.run
            (compileStmtChecked
              (Stmt.assign (.local dstLoc) (.ref kind prot mask (.deref P)))) csPrefix) := by
        rw [h_stmt_bind, CheckedCompilerM.run_bind]
        simp only [CheckedCompilerM.value_lift, CheckedCompilerM.run_lift, h_erun]
        rw [CheckedCompilerM.run_bind]
        split
        · simp only [CheckedCompilerM.run_pure]
          exact h_incr1 _
        · exact h_incr1 _
      have h_instP : ∀ q' instr,
          q' < (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextLabel →
          (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).code q'
            = some instr →
          compProg q' = some instr := by
        intro q' instr h_lt h_code
        have h_incrP := StateIncr.trans h_incr0 h_incr2
        refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
        · exact Nat.lt_of_lt_of_le h_lt h_incrP.nextLabel_le
        · rw [h_incrP.code_eq q' h_lt]
          exact h_code
      -- §4 the spine prelude
      obtain ⟨pOut, n1, s_mid, ptag, h_pval, h_pclean, h_prun, h_ppc, h_pmem, h_ppsim,
        h_pnt1, h_pnt2, h_plbs, h_pentry, h_prt, h_pnw, h_ple, h_prange, h_pbelow,
        h_pprm, h_pregmono, h_plabmono, -⟩ :=
        ptrChain_lowering_sim h_id_a h_wf_t h_spine RefKind.Shared csPrefix s_osea
          pRes permsP h_dres h_tbd h_lbs h_prb h_sms h_psim h_pc h_instP
      have h_stmtRun := compileStmt_ref_deref_run (cs := csPrefix) (pOut := pOut)
        kind prot mask h_piD h_pval h_pclean
      have h_len3 : ((emit (emit
          { (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg + 1 }
              [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg)
                (Rhs.Load obseq.TyVal.PTy pOut.result.reg)]) with
              nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg + 1 + 1 }
          [Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg + 1))
            (Rhs.Borrow kind prot mask (blockSize τ)
              (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg) 0)])
          [Instr.RStore obseq.TyVal.PTy
            (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg + 1)) dstReg])).nextLabel
          = (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextLabel + 3 := by
        simp only [emit, List.length_cons, List.length_nil]
      -- §5 the three instructions are in the program
      have h_code1 : compProg s_mid.pc
          = some (Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg)
              (Rhs.Load obseq.TyVal.PTy pOut.result.reg)) := by
        rw [h_ppc]
        refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
        · rw [h_stmtRun, h_len3]; omega
        · rw [h_stmtRun]
          rw [emit_code_lt_nextLabel _ _ (by
            simp only [emit, List.length_cons, List.length_nil]; omega)]
          rw [emit_code_lt_nextLabel _ _ (by
            simp only [emit, List.length_cons, List.length_nil]; omega)]
          have h := emit_code_at_new { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg + 1 }
            [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg)
              (Rhs.Load obseq.TyVal.PTy pOut.result.reg)] (k := 0) (by simp)
          simpa using h
      have h_code2 : compProg (s_mid.pc + 1)
          = some (Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg + 1))
              (Rhs.Borrow kind prot mask (blockSize τ)
                (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg) 0)) := by
        rw [h_ppc]
        refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
        · rw [h_stmtRun, h_len3]; omega
        · rw [h_stmtRun]
          rw [emit_code_lt_nextLabel _ _ (by
            simp only [emit, List.length_cons, List.length_nil]; omega)]
          have h := emit_code_at_new
            { (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg + 1 }
                [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg)
                  (Rhs.Load obseq.TyVal.PTy pOut.result.reg)]) with
                nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg + 1 + 1 }
            [Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg + 1))
              (Rhs.Borrow kind prot mask (blockSize τ)
                (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg) 0)] (k := 0) (by simp)
          simpa [emit] using h
      have h_code3 : compProg (s_mid.pc + 1 + 1)
          = some (Instr.RStore obseq.TyVal.PTy
              (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg + 1)) dstReg) := by
        rw [h_ppc]
        refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
        · rw [h_stmtRun, h_len3]; omega
        · rw [h_stmtRun]
          have h := emit_code_at_new
            (emit { (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg + 1 }
                [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg)
                  (Rhs.Load obseq.TyVal.PTy pOut.result.reg)]) with
                nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg + 1 + 1 }
              [Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg + 1))
                (Rhs.Borrow kind prot mask (blockSize τ)
                  (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg) 0)])
            [Instr.RStore obseq.TyVal.PTy
              (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg + 1)) dstReg]
            (k := 0) (by simp)
          simpa [emit] using h
      -- §6 execute the Load through the transported pointer-cell read
      obtain ⟨p2, h_read_tgt, h_psim2⟩ :=
        sb_read_respects_PermSim h_ppsim h_wf_t h_prt h_pnw h_qread
      have h_cancel : pRes.allocBase + (pRes.addr - pRes.allocBase) = pRes.addr := by
        grind
      have h_offP : pRes.addr - pRes.allocBase < pRes.allocSize := by grind
      have h_read_tgt' : MSB.read s_mid.perms
          (pRes.allocBase + (pRes.addr - pRes.allocBase)) 1 ptag = .ok p2 := by
        rw [h_cancel]; exact h_read_tgt
      have h_run1 := runN_Assgn_Load_ptr_step compProg s_mid
        (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg)
        pOut.result.reg obseq.TyVal.PTy
        h_code1 h_pentry h_offP h_read_tgt'
      obtain ⟨addr', value', h_ra', h_find_tgt, h_mvs⟩ := h_sms _ _ h_qfind
      have h_addr' : addr' = pRes.addr := (h_id_a _ _ h_ra').symm
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
      have h_rws : oseair.readWordSeq s_mid.mem
          (pRes.allocBase + (pRes.addr - pRes.allocBase))
          (obseq.typeSize obseq.TyVal.PTy) = [Val.Ptr b2 o2 s2 t2] := by
        rw [h_cancel]
        show oseair.readWordSeq s_mid.mem pRes.addr 1 = _
        rw [h_pmem]
        simp [oseair.readWordSeq, h_find_tgt]
      -- §7 the retag transported: the fresh pair extends ρt
      have h_tbd2 : TagRenameBounded ρt permsP'.NextTag p2.NextTag := by
        rw [sb_read_NextTag h_qread, h_pnt1, sb_read_NextTag h_read_tgt]
        exact TagRenameBounded.mono h_tbd (Nat.le_refl _) h_pnt2
      obtain ⟨tgtPerms, h_ref_tgt, h_fresh_eq, h_incr_t, h_wf_t', h_tbd', h_psim'⟩ :=
        sb_ref_respects_PermSim h_psim2 h_wf_t h_tbd2 h_t h_tnw h_ref_src
      subst h_fresh_eq
      have h_rt_new : (ρt.extend permsP'.NextTag p2.NextTag) permsP'.NextTag
          = some p2.NextTag := TagRenameMap.extend_self _ _ _
      have h0 : wildcardTag < permsP'.NextTag := (h_tbd2 _ _ h_wf_t.2).1
      have h_nw_new : (permsP'.NextTag == wildcardTag) = false := by grind
      -- §8 execute the Borrow: bound from the SOURCE event check
      have h_le2 : b2 + o2 + 0 + blockSize τ ≤ b2 + s2 := by grind
      have h_entry_loaded : PtrRegisterEntry
          (oseair.RegMap.insert s_mid.reg
            (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg)
            (obseq.TyVal.PTy, oseair.readWordSeq s_mid.mem
              (pRes.allocBase + (pRes.addr - pRes.allocBase))
              (obseq.typeSize obseq.TyVal.PTy)))
          (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg)
          b2 o2 s2 t2 := by
        show oseair.RegMap.lookup _ _ = _
        rw [RegMap.lookup_insert_self, h_rws]
      have h_ref_tgt' : MSB.ref p2 (b2 + o2 + 0) (blockSize τ) t2 kind prot mask
          = .ok (tgtPerms, p2.NextTag) := by
        simpa using h_ref_tgt
      have h_run2 := runN_Assgn_Borrow_step compProg
        { s_mid with
            perms := p2,
            reg := oseair.RegMap.insert s_mid.reg
              (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg)
              (obseq.TyVal.PTy, oseair.readWordSeq s_mid.mem
                (pRes.allocBase + (pRes.addr - pRes.allocBase))
                (obseq.typeSize obseq.TyVal.PTy)),
            pc := s_mid.pc + 1 }
        (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg + 1))
        (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg)
        kind prot mask (blockSize τ) 0
        h_code2 h_entry_loaded h_le2 h_ref_tgt'
      -- §9 the pointer store via BRIDGE 2 into the dst binding
      obtain ⟨dstReg2, baseD2, tagD2, h_piD2, h_entryD2, h_raD2, h_rtD2, h_nwD2, -⟩ :=
        h_plbs dstLoc bD h_envD
      have h_dr2 : dstReg2 = dstReg := by grind
      have h_baseD2 : baseD2 = bD.addr := (h_id_a _ _ h_raD2).symm
      rw [h_dr2, h_baseD2] at h_entryD2
      rw [h_baseD2] at h_raD2
      have h_regne1 : dstReg
          ≠ Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg := by
        cases dstReg with
        | R n =>
            have h_lt := h_prb _ _ _ h_piD
            grind [RegisterBelow]
      have h_regne2 : dstReg
          ≠ Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg + 1) := by
        cases dstReg with
        | R n =>
            have h_lt := h_prb _ _ _ h_piD
            grind [RegisterBelow]
      simp only [h_envD] at h_step
      have h_w := h_step
      simp only [mirlite.writeResolvedPlace] at h_w
      split at h_w
      · simp at h_w
      · rename_i h_nb
        split at h_w
        · rename_i perms'' h_useMut_src
          cases h_w
          obtain ⟨p3, h_useMut_tgt, h_psim3⟩ :=
            sb_write_respects_PermSim h_psim' h_wf_t'
              (h_incr_t _ _ h_rtD2) h_nwD2 h_useMut_src
          have h_entryD1 : PtrRegisterEntry
              (oseair.RegMap.insert
                (oseair.RegMap.insert s_mid.reg
                  (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg)
                  (obseq.TyVal.PTy, oseair.readWordSeq s_mid.mem
                    (pRes.allocBase + (pRes.addr - pRes.allocBase))
                    (obseq.typeSize obseq.TyVal.PTy)))
                (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg + 1))
                (obseq.TyVal.PTy, [Val.Ptr b2 (o2 + 0) s2 p2.NextTag]))
              dstReg bD.addr (bD.addr - bD.addr) (blockSize (obseq.LayoutTy.PtrL τ)) tagD2 := by
            rw [Nat.sub_self]
            show oseair.RegMap.lookup _ _ = _
            rw [RegMap.lookup_insert_ne _ h_regne2,
              RegMap.lookup_insert_ne _ h_regne1]
            exact h_entryD2
          obtain ⟨h_wtp, h_sms'⟩ :=
            writeThroughPtr_sim (τ := obseq.LayoutTy.PtrL τ)
              (s_osea :=
                { s_mid with
                    perms := tgtPerms,
                    reg := oseair.RegMap.insert
                      (oseair.RegMap.insert s_mid.reg
                        (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg)
                        (obseq.TyVal.PTy, oseair.readWordSeq s_mid.mem
                          (pRes.allocBase + (pRes.addr - pRes.allocBase))
                          (obseq.typeSize obseq.TyVal.PTy)))
                      (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg + 1))
                      (obseq.TyVal.PTy, [Val.Ptr b2 (o2 + 0) s2 p2.NextTag]),
                    pc := s_mid.pc + 1 + 1 })
              (resolved := { addr := bD.addr, tag := bD.tag, allocBase := bD.addr,
                             allocSize := blockSize (obseq.LayoutTy.PtrL τ) })
              "RStore Invalid Regs"
              [mirlite.MemValue.ptrVal b2 (b2 + o2 - b2) s2 permsP'.NextTag]
              [Val.Ptr b2 (o2 + 0) s2 p2.NextTag] rfl
              ⟨⟨h_b, by simp [Nat.add_sub_cancel_left], rfl, h_rt_new, h_nw_new,
                fun k hk => ⟨(h_range k hk).choose,
                  AddrRenameIncr.refl ρa _ _ (h_range k hk).choose_spec⟩⟩, trivial⟩
              h_id_a h_entryD1 h_useMut_tgt
              (by
                show SourceMemSim ρa (ρt.extend permsP'.NextTag p2.NextTag)
                  s_mir.mem s_mid.mem
                rw [h_pmem]
                exact SourceMemSim.rename_mono (AddrRenameIncr.refl ρa) h_incr_t h_sms)
              (Nat.le_refl _)
              (fun k hk => by
                have hk0 : k = 0 := by simpa using hk
                subst hk0
                rw [Nat.add_zero]
                exact h_raD2)
              h_step
          have h_run3 := runN_RStore_step compProg _ _ obseq.TyVal.PTy
            (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg + 1))
            dstReg _ _ h_code3
            (RegMap.lookup_insert_self _ _ _)
            (by rw [RegMap.lookup_insert_ne _ h_regne2,
                RegMap.lookup_insert_ne _ h_regne1]; exact h_entryD2)
            h_wtp
          have h_runA := (oseair_runN_add n1 1 s_osea compProg s_mid h_prun).trans h_run1
          have h_runB := (oseair_runN_add (n1 + 1) 1 s_osea compProg _ h_runA).trans h_run2
          have h_runC := (oseair_runN_add (n1 + 1 + 1) 1 s_osea compProg _ h_runB).trans h_run3
          -- §10 rebuild the invariant under the extended ρt
          refine ⟨_, _, n1 + 1 + 1 + 1, h_incr_t, h_runC, ?_⟩
          refine ⟨CheckedCompilerM.run
            (compileStmtChecked
              (Stmt.assign (.local dstLoc)
                (.ref kind prot mask (.deref P)))) csPrefix,
            ⟨prefixCompileState_succ h_csAt h_stmt h_stmtOut, ?_⟩, ?_, h_sms', h_psim3,
            h_id_a, h_wf_t', ?_, ?_, ?_, ?_⟩
          · show s_mid.pc + 1 + 1 + 1 = _
            rw [h_ppc, h_stmtRun, h_len3]
          · have h_plbs' : LocalBindingSim ρa (ρt.extend permsP'.NextTag p2.NextTag)
                s_mir.env s_mid csPrefix :=
              LocalBindingSim.rename_mono (AddrRenameIncr.refl ρa) h_incr_t h_plbs
            have h_lbs1 : LocalBindingSim ρa (ρt.extend permsP'.NextTag p2.NextTag)
                s_mir.env
                { s_mid with
                    perms := p2,
                    reg := oseair.RegMap.insert s_mid.reg
                      (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg)
                      (obseq.TyVal.PTy, oseair.readWordSeq s_mid.mem
                        (pRes.allocBase + (pRes.addr - pRes.allocBase))
                        (obseq.typeSize obseq.TyVal.PTy)),
                    pc := s_mid.pc + 1 } csPrefix :=
              LocalBindingSim.insert_fresh_reg h_plbs' h_prb h_pregmono rfl
            have h_lbs2 : LocalBindingSim ρa (ρt.extend permsP'.NextTag p2.NextTag)
                s_mir.env
                { s_mid with
                    perms := tgtPerms,
                    reg := oseair.RegMap.insert
                      (oseair.RegMap.insert s_mid.reg
                        (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg)
                        (obseq.TyVal.PTy, oseair.readWordSeq s_mid.mem
                          (pRes.allocBase + (pRes.addr - pRes.allocBase))
                          (obseq.typeSize obseq.TyVal.PTy)))
                      (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).nextReg + 1))
                      (obseq.TyVal.PTy, [Val.Ptr b2 (o2 + 0) s2 p2.NextTag]),
                    pc := s_mid.pc + 1 + 1 } csPrefix :=
              LocalBindingSim.insert_fresh_reg h_lbs1 h_prb
                (Nat.le_trans h_pregmono (Nat.le_succ _)) rfl
            intro τ' loc' binding' h_env'
            obtain ⟨reg', base', tag', h_pi', h_entry', h_ra', h_rt', h_nw', h_dom'⟩ :=
              h_lbs2 loc' binding' h_env'
            refine ⟨reg', base', tag', ?_, h_entry', h_ra', h_rt', h_nw', h_dom'⟩
            rw [h_stmtRun, getPlaceInfo_emit, getPlaceInfo_emit,
              getPlaceInfo_setNextReg, getPlaceInfo_emit, getPlaceInfo_setNextReg]
            show (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).placeRegMap.lookup loc'.idx.1 = _
            rw [h_pprm]
            exact h_pi'
          · show TagRenameBounded _ perms''.NextTag p3.NextTag
            rw [sb_write_NextTag h_useMut_src, sb_write_NextTag h_useMut_tgt]
            exact h_tbd'
          · simp only [AllocLockstep, mirlite_writeWordSeq_addrStart,
              oseair_writeWordSeq_addrStart, h_pmem]
            exact h_alloc
          · intro τ' loc' h_none
            rw [h_stmtRun, getPlaceInfo_emit, getPlaceInfo_emit,
              getPlaceInfo_setNextReg, getPlaceInfo_emit, getPlaceInfo_setNextReg]
            show (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) csPrefix).placeRegMap.lookup loc'.idx.1 = none
            rw [h_pprm]
            exact h_unmap loc' h_none
          · intro idx reg'' τ'' h_look
            rw [h_stmtRun] at h_look ⊢
            rw [getPlaceInfo_emit, getPlaceInfo_emit,
              getPlaceInfo_setNextReg, getPlaceInfo_emit, getPlaceInfo_setNextReg] at h_look
            have h_cs : getPlaceInfo csPrefix idx = some (reg'', τ'') := by
              show csPrefix.placeRegMap.lookup idx = _
              rw [← h_pprm]
              exact h_look
            refine RegisterBelow.mono ?_ (h_prb _ _ _ h_cs)
            simp only [emit]
            exact Nat.le_trans h_pregmono
              (Nat.le_trans (Nat.le_succ _) (Nat.le_succ _))
        · simp at h_w

/-- The fragment of `dst.g := &src` at ZERO offset (both roots mapped
    locals): the projection returns the base register, so the fragment
    is L→L's — one `Borrow` into a fresh temp, then the `RStore`
    through the DST BASE register. -/
theorem compileStmt_ref_projzero_local_run
    {Γ : Ctx} {τ σ : LayoutTy}
    {dstLoc : Local Γ σ} {g : PathTo σ (obseq.LayoutTy.PtrL τ)}
    {srcLoc : Local Γ τ}
    {cs : CompilerState} {dstReg srcReg : Register}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (h_g0 : pathOffset g = 0)
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = some (dstReg, σ))
    (h_src : getPlaceInfo cs srcLoc.idx.1 = some (srcReg, τ)) :
    CheckedCompilerM.run
        (compileStmtChecked
          (Stmt.assign (.proj (.local dstLoc) g)
            (.ref kind prot mask (.local srcLoc)))) cs
      = emit (emit { cs with nextReg := cs.nextReg + 1 }
          [Instr.Assgn (Register.R cs.nextReg)
            (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)])
          [Instr.RStore obseq.TyVal.PTy (Register.R cs.nextReg) dstReg] := by
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
  have h_root : CompilerM.run (ensurePlaceRoot (Place.proj (Place.local dstLoc) g)) cs
      = cs := by
    exact ensurePlaceRoot_run_eq_of_mapped ⟨dstReg, σ, h_dst⟩
  simp only [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked,
    placeToBorrowRegChecked, h_proj_eq,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
    h_root, h_prun, h_pval, h_g0, dif_pos]
  simp [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM,
    cleanupInstrs, h_pres, emit_nil]
  simp only [h_bval, h_brun, h_bres]
  simp [cleanupInstrs, emit_nil]

/-- The zero-offset field-dst ref lowers. -/
theorem compileStmt_ref_projzero_local_value
    {Γ : Ctx} {τ σ : LayoutTy}
    {dstLoc : Local Γ σ} {g : PathTo σ (obseq.LayoutTy.PtrL τ)}
    {srcLoc : Local Γ τ}
    {cs : CompilerState} {dstReg srcReg : Register}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (h_g0 : pathOffset g = 0)
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = some (dstReg, σ))
    (h_src : getPlaceInfo cs srcLoc.idx.1 = some (srcReg, τ)) :
    ∃ so, CheckedCompilerM.value
      (compileStmtChecked
        (Stmt.assign (.proj (.local dstLoc) g)
          (.ref kind prot mask (.local srcLoc)))) cs
      = Except.ok so := by
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
  have h_root : CompilerM.run (ensurePlaceRoot (Place.proj (Place.local dstLoc) g)) cs
      = cs :=
    ensurePlaceRoot_run_eq_of_mapped ⟨dstReg, σ, h_dst⟩
  simp only [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked,
    placeToBorrowRegChecked, h_proj_eq,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
    h_root, h_prun, h_pval, h_g0, dif_pos]
  simp only [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM]
  simp only [h_pres]
  simp only [h_bval]
  exact ⟨_, rfl⟩

/-- REGIME L→P0 (field destination, ZERO offset), CLOSED 2026-08-29:
    `dst.g := &src` with both roots bound locals and `g` at offset 0 —
    regime L→L with a WIDER destination allocation (the resolved dst
    covers the base's whole block), exactly as C0 widened regime A. The
    fragment is L→L's: `[Borrow; RStore]` through the dst BASE
    register. -/
theorem ref_local_projzero_simulation
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {τ σ : LayoutTy}
    {dstLoc : Local Γ σ} {g : PathTo σ (obseq.LayoutTy.PtrL τ)}
    {srcLoc : Local Γ τ}
    {bD bS : mirlite.Binding}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (compProg : oseair.Prog)
    (h_g0 : pathOffset g = 0)
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
  simp only [mirlite.stepStmt, mirlite.doAssign, mirlite.doAssignCont,
    mirlite.preparePlaceAssign,
    mirlite.resolvePlace?, h_envD, mirlite.resolvePlaceAcc, h_envS,
    mirlite.evalRExpr] at h_step
  rw [if_neg (Nat.lt_irrefl (bS.addr + blockSize τ))] at h_step
  cases h_ref_src : MSB.ref s_mir.perms bS.addr (blockSize τ) bS.tag kind prot mask with
  | error e => rw [h_ref_src] at h_step; simp at h_step
  | ok pr =>
      obtain ⟨perms', freshTag⟩ := pr
      rw [h_ref_src] at h_step
      simp only at h_step
      rw [show g.offset = 0 from h_g0] at h_step
      -- §2 the retag on the target, with ρt extended at the fresh pair
      obtain ⟨tgtPerms, h_ref_tgt, h_fresh_eq, h_incr_t, h_wf_t', h_tbd', h_psim'⟩ :=
        sb_ref_respects_PermSim h_psim h_wf_t h_tbd h_rtS h_nwS h_ref_src
      subst h_fresh_eq
      have h_rt_new : (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag)
          s_mir.perms.NextTag = some s_osea.perms.NextTag :=
        TagRenameMap.extend_self _ _ _
      have h0 : wildcardTag < s_mir.perms.NextTag := (h_tbd _ _ h_wf_t.2).1
      have h_nw_new : (s_mir.perms.NextTag == wildcardTag) = false := by grind
      have h_rtD' : (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag) bD.tag
          = some tagD := h_incr_t _ _ h_rtD
      -- §3 the fragment and its two instructions
      have h_stmtRunC := compileStmt_ref_projzero_local_run (cs := csPrefix)
        kind prot mask h_g0 h_piD h_piS
      have h_stmtRun := (h_run0 csPrefix).trans h_stmtRunC
      obtain ⟨stmtOutC, h_stmtOutC⟩ :=
        compileStmt_ref_projzero_local_value (cs := csPrefix) kind prot mask
          h_g0 h_piD h_piS
      obtain ⟨stmtOut, h_stmtOut⟩ := h_val0 csPrefix stmtOutC h_stmtOutC
      have h_code1 : compProg s_osea.pc
          = some (Instr.Assgn (Register.R csPrefix.nextReg)
              (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)) := by
        rw [h_pc]
        refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
        · rw [h_stmtRun]
          simp only [emit, List.length_cons, List.length_nil]
          omega
        · rw [h_stmtRun]
          rw [emit_code_lt_nextLabel _ _ (by
            simp only [emit, List.length_cons, List.length_nil]; omega)]
          have h := emit_code_at_new { csPrefix with nextReg := csPrefix.nextReg + 1 }
            [Instr.Assgn (Register.R csPrefix.nextReg)
              (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)] (k := 0) (by simp)
          simpa using h
      have h_code2 : compProg (s_osea.pc + 1)
          = some (Instr.RStore obseq.TyVal.PTy (Register.R csPrefix.nextReg) dstReg) := by
        rw [h_pc]
        refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
        · rw [h_stmtRun]
          simp only [emit, List.length_cons, List.length_nil]
          omega
        · rw [h_stmtRun]
          simp [emit]
      -- §4 execute the Borrow
      have h_ref_tgt' : MSB.ref s_osea.perms (bS.addr + 0 + 0) (blockSize τ) tagS kind prot mask
          = .ok (tgtPerms, s_osea.perms.NextTag) := by
        simpa using h_ref_tgt
      have h_run1 := runN_Assgn_Borrow_step compProg s_osea
        (Register.R csPrefix.nextReg) srcReg kind prot mask (blockSize τ) 0
        h_code1 h_entryS (by
          show bS.addr + 0 + 0 + blockSize τ ≤ bS.addr + blockSize τ
          simp only [Nat.add_zero]
          exact Nat.le_refl _) h_ref_tgt'
      -- §5 the pointer write into the base block via BRIDGE 2
      simp only [h_envD] at h_step
      have h_w := h_step
      simp only [mirlite.writeResolvedPlace] at h_w
      split at h_w
      · simp at h_w
      · rename_i h_nb
        split at h_w
        · rename_i perms'' h_useMut_src
          cases h_w
          obtain ⟨p2, h_useMut_tgt, h_psim2⟩ :=
            sb_write_respects_PermSim h_psim' h_wf_t' h_rtD' h_nwD h_useMut_src
          have h_regne : dstReg ≠ Register.R csPrefix.nextReg := by
            cases dstReg with
            | R n =>
                have h_lt := h_prb _ _ _ h_piD
                grind [RegisterBelow]
          have h_entryD1 : PtrRegisterEntry
              (oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
                (obseq.TyVal.PTy, [Val.Ptr bS.addr (0 + 0) (blockSize τ) s_osea.perms.NextTag]))
              dstReg bD.addr (bD.addr + 0 - bD.addr) (blockSize σ) tagD := by
            rw [show bD.addr + 0 - bD.addr = 0 from Nat.sub_self bD.addr]
            show oseair.RegMap.lookup _ _ = _
            rw [RegMap.lookup_insert_ne _ h_regne]
            exact h_entryD
          have h_bsz : 0 < blockSize σ := by
            have h_fit := PathTo.offset_add_size_le g
            show 0 < layoutSize σ
            have h_fit' : g.offset + layoutSize (obseq.LayoutTy.PtrL τ)
                ≤ layoutSize σ := h_fit
            have h_one : layoutSize (obseq.LayoutTy.PtrL τ) = 1 := rfl
            grind
          obtain ⟨h_wtp, h_sms'⟩ :=
            writeThroughPtr_sim (τ := obseq.LayoutTy.PtrL τ)
              (s_osea :=
                { s_osea with
                    perms := tgtPerms,
                    reg := oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
                      (obseq.TyVal.PTy,
                        [Val.Ptr bS.addr (0 + 0) (blockSize τ) s_osea.perms.NextTag]),
                    pc := s_osea.pc + 1 })
              (resolved := { addr := bD.addr + 0, tag := bD.tag, allocBase := bD.addr,
                             allocSize := blockSize σ })
              "RStore Invalid Regs"
              [mirlite.MemValue.ptrVal bS.addr (bS.addr - bS.addr) (blockSize τ) s_mir.perms.NextTag]
              [Val.Ptr bS.addr (0 + 0) (blockSize τ) s_osea.perms.NextTag] rfl
              ⟨⟨h_raS, by simp, rfl, h_rt_new, h_nw_new,
                h_domS⟩, trivial⟩
              h_id_a h_entryD1 h_useMut_tgt
              (by exact SourceMemSim.rename_mono (AddrRenameIncr.refl ρa) h_incr_t h_sms)
              (Nat.le_add_right _ _)
              (fun k hk => by
                simp [blockSize, Nat.lt_one_iff] at hk
                subst hk
                obtain ⟨a', ha'⟩ := h_domD 0 h_bsz
                grind [IdentityOnDomain])
              h_step
          have h_run2 := runN_RStore_step compProg _ _ obseq.TyVal.PTy
            (Register.R csPrefix.nextReg) dstReg _ _ h_code2
            (RegMap.lookup_insert_self _ _ _)
            (by rw [RegMap.lookup_insert_ne _ h_regne]; exact h_entryD)
            h_wtp
          have h_run := (oseair_runN_add 1 1 s_osea compProg _ h_run1).trans h_run2
          -- §6 rebuild the invariant under the extended ρt
          refine ⟨_, _, 1 + 1, h_incr_t, h_run, ?_⟩
          refine ⟨CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix,
            ⟨prefixCompileState_succ h_csAt h_stmt h_stmtOut, ?_⟩, ?_, h_sms', h_psim2,
            h_id_a, h_wf_t', ?_, ?_, ?_, ?_⟩
          · show s_osea.pc + 1 + 1 = _
            rw [h_pc, h_stmtRun]
            simp [emit]
          · refine LocalBindingSim.placeRegMap_congr ?_
              (LocalBindingSim.insert_fresh_reg
                (LocalBindingSim.rename_mono (AddrRenameIncr.refl ρa) h_incr_t h_lbs)
                h_prb (Nat.le_refl _) rfl)
            rw [h_stmtRun]
            rfl
          · show TagRenameBounded _ perms''.NextTag p2.NextTag
            rw [sb_write_NextTag h_useMut_src, sb_write_NextTag h_useMut_tgt]
            exact h_tbd'
          · simp only [AllocLockstep, mirlite_writeWordSeq_addrStart,
              oseair_writeWordSeq_addrStart]
            exact h_alloc
          · intro τ' loc' h_none
            rw [h_stmtRun, getPlaceInfo_emit, getPlaceInfo_emit]
            exact h_unmap loc' h_none
          · intro idx reg τ'' h_look
            rw [h_stmtRun] at h_look ⊢
            rw [getPlaceInfo_emit, getPlaceInfo_emit] at h_look
            refine RegisterBelow.mono ?_ (h_prb _ _ _ h_look)
            simp only [emit]
            omega
        · simp at h_w

/-- The fragment of `dst.g := &src` at NONZERO offset (both roots
    mapped locals): the rhs borrow, the dst FIELD borrow, the store
    through it, and its cleanup — `[Borrow(kind,src); Borrow(Mut,dst
    field); RStore; Die]`. Two fresh registers, MIR order. -/
theorem compileStmt_ref_projoffset_local_run
    {Γ : Ctx} {τ σ : LayoutTy}
    {dstLoc : Local Γ σ} {g : PathTo σ (obseq.LayoutTy.PtrL τ)}
    {srcLoc : Local Γ τ}
    {cs : CompilerState} {dstReg srcReg : Register}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (h_go : pathOffset g ≠ 0)
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = some (dstReg, σ))
    (h_src : getPlaceInfo cs srcLoc.idx.1 = some (srcReg, τ)) :
    CheckedCompilerM.run
        (compileStmtChecked
          (Stmt.assign (.proj (.local dstLoc) g)
            (.ref kind prot mask (.local srcLoc)))) cs
      = emit (emit (emit
          { (emit { cs with nextReg := cs.nextReg + 1 }
              [Instr.Assgn (Register.R cs.nextReg)
                (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)]) with
              nextReg := cs.nextReg + 1 + 1 }
          [Instr.Assgn (Register.R (cs.nextReg + 1))
            (Rhs.Borrow RefKind.Mut false [] (blockSize (obseq.LayoutTy.PtrL τ))
              dstReg (pathOffset g))])
          [Instr.RStore obseq.TyVal.PTy (Register.R cs.nextReg)
            (Register.R (cs.nextReg + 1))])
          [Instr.Die (Register.R (cs.nextReg + 1))
            (blockSize (obseq.LayoutTy.PtrL τ))] := by
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
  have h_root : CompilerM.run (ensurePlaceRoot (Place.proj (Place.local dstLoc) g)) cs
      = cs :=
    ensurePlaceRoot_run_eq_of_mapped ⟨dstReg, σ, h_dst⟩
  simp only [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked,
    placeToBorrowRegChecked, h_proj_eq,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
    h_root, h_prun, h_pval, h_go, dif_neg]
  simp [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM,
    cleanupInstrs, h_pres, emit_nil]
  simp only [h_pres, h_bval, h_brun, h_bres]
  simp [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM,
    cleanupInstrs, emit_nil, borrowRhs]
  rfl

/-- The nonzero-offset field-dst ref lowers. -/
theorem compileStmt_ref_projoffset_local_value
    {Γ : Ctx} {τ σ : LayoutTy}
    {dstLoc : Local Γ σ} {g : PathTo σ (obseq.LayoutTy.PtrL τ)}
    {srcLoc : Local Γ τ}
    {cs : CompilerState} {dstReg srcReg : Register}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (h_go : pathOffset g ≠ 0)
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = some (dstReg, σ))
    (h_src : getPlaceInfo cs srcLoc.idx.1 = some (srcReg, τ)) :
    ∃ so, CheckedCompilerM.value
      (compileStmtChecked
        (Stmt.assign (.proj (.local dstLoc) g)
          (.ref kind prot mask (.local srcLoc)))) cs
      = Except.ok so := by
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
  have h_root : CompilerM.run (ensurePlaceRoot (Place.proj (Place.local dstLoc) g)) cs
      = cs :=
    ensurePlaceRoot_run_eq_of_mapped ⟨dstReg, σ, h_dst⟩
  simp only [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked,
    placeToBorrowRegChecked, h_proj_eq,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
    h_root, h_prun, h_pval, h_go, dif_neg]
  simp only [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM]
  simp only [h_pres]
  simp only [h_bval]
  exact ⟨_, rfl⟩

/-- REGIME L→P (field destination, NONZERO offset), CLOSED 2026-08-29:
    `dst.g := &src` with both roots bound. The first leaf where the
    TARGET mints TWO tags in one statement — the rhs reference (paired
    with the source's mint; ρt extends there) and the dst field's
    `Borrow(Mut)` (a compiler phantom; BRIDGE 1 cancels its
    `ref; use; die` triple to the parent write the source performs). -/
theorem ref_local_projoffset_simulation
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {τ σ : LayoutTy}
    {dstLoc : Local Γ σ} {g : PathTo σ (obseq.LayoutTy.PtrL τ)}
    {srcLoc : Local Γ τ}
    {bD bS : mirlite.Binding}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (compProg : oseair.Prog)
    (h_go : pathOffset g ≠ 0)
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
  -- §1 invert the source: prepare no-op, dst resolves at the FIELD, the
  -- rhs retag succeeds, the pointer is written at the field
  simp only [mirlite.stepStmt, mirlite.doAssign, mirlite.doAssignCont,
    mirlite.preparePlaceAssign,
    mirlite.resolvePlace?, h_envD, mirlite.resolvePlaceAcc, h_envS,
    mirlite.evalRExpr] at h_step
  rw [if_neg (Nat.lt_irrefl (bS.addr + blockSize τ))] at h_step
  cases h_ref_src : MSB.ref s_mir.perms bS.addr (blockSize τ) bS.tag kind prot mask with
  | error e => rw [h_ref_src] at h_step; simp at h_step
  | ok pr =>
      obtain ⟨perms', freshTag⟩ := pr
      rw [h_ref_src] at h_step
      simp only at h_step
      -- §2 the rhs retag on the target, ρt extended at the fresh pair
      obtain ⟨tgtPerms, h_ref_tgt, h_fresh_eq, h_incr_t, h_wf_t', h_tbd', h_psim'⟩ :=
        sb_ref_respects_PermSim h_psim h_wf_t h_tbd h_rtS h_nwS h_ref_src
      subst h_fresh_eq
      have h_rt_new : (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag)
          s_mir.perms.NextTag = some s_osea.perms.NextTag :=
        TagRenameMap.extend_self _ _ _
      have h0 : wildcardTag < s_mir.perms.NextTag := (h_tbd _ _ h_wf_t.2).1
      have h_nw_new : (s_mir.perms.NextTag == wildcardTag) = false := by grind
      have h_rtD' : (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag) bD.tag
          = some tagD := h_incr_t _ _ h_rtD
      -- §3 the dst write transported under ρt'; its Mut retag succeeds and
      -- BRIDGE 1 cancels the triple to the parent write
      simp only [h_envD] at h_step
      have h_w := h_step
      simp only [mirlite.writeResolvedPlace] at h_w
      split at h_w
      · simp at h_w
      · rename_i h_nb
        split at h_w
        · rename_i perms'' h_useMut_src
          cases h_w
          obtain ⟨qW, h_useMut_tgt, h_psim2⟩ :=
            sb_write_respects_PermSim h_psim' h_wf_t' h_rtD' h_nwD h_useMut_src
          obtain ⟨q1, h_ref_dst⟩ := sb_ref_Mut_ok_of_sb_write_ok h_useMut_tgt
          have h_unprot := freshTag_not_protected h_psim' h_tbd'
          have h0' : wildcardTag < tgtPerms.NextTag := (h_tbd' _ _ h_wf_t'.2).2
          have h_ntw' : (tgtPerms.NextTag == wildcardTag) = false := by grind
          obtain ⟨q2, q3, qAcc', h_wr1, h_die1, h_wr2, h_sm, h_ex, h_pf, h_ntle⟩ :=
            sb_ref_use_die_cancels h_ntw' h_unprot h_ref_dst
          have h_qAcc : qAcc' = qW := by
            grind
          subst h_qAcc
          -- §4 the fragment and its four instructions
          have h_stmtRunC := compileStmt_ref_projoffset_local_run (cs := csPrefix)
            kind prot mask h_go h_piD h_piS
          have h_stmtRun := (h_run0 csPrefix).trans h_stmtRunC
          obtain ⟨stmtOutC, h_stmtOutC⟩ :=
            compileStmt_ref_projoffset_local_value (cs := csPrefix) kind prot mask
              h_go h_piD h_piS
          obtain ⟨stmtOut, h_stmtOut⟩ := h_val0 csPrefix stmtOutC h_stmtOutC
          have h_len4 : ((emit (emit (emit
              { (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                  [Instr.Assgn (Register.R csPrefix.nextReg)
                    (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)]) with
                  nextReg := csPrefix.nextReg + 1 + 1 }
              [Instr.Assgn (Register.R (csPrefix.nextReg + 1))
                (Rhs.Borrow RefKind.Mut false [] (blockSize (obseq.LayoutTy.PtrL τ))
                  dstReg (pathOffset g))])
              [Instr.RStore obseq.TyVal.PTy (Register.R csPrefix.nextReg)
                (Register.R (csPrefix.nextReg + 1))])
              [Instr.Die (Register.R (csPrefix.nextReg + 1))
                (blockSize (obseq.LayoutTy.PtrL τ))])).nextLabel
              = csPrefix.nextLabel + 4 := by
            simp only [emit, List.length_cons, List.length_nil]
          have h_code1 : compProg s_osea.pc
              = some (Instr.Assgn (Register.R csPrefix.nextReg)
                  (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)) := by
            rw [h_pc]
            refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
            · rw [h_stmtRun, h_len4]; omega
            · rw [h_stmtRun]
              rw [emit_code_lt_nextLabel _ _ (by
                simp only [emit, List.length_cons, List.length_nil]; omega)]
              rw [emit_code_lt_nextLabel _ _ (by
                simp only [emit, List.length_cons, List.length_nil]; omega)]
              rw [emit_code_lt_nextLabel _ _ (by
                simp only [emit, List.length_cons, List.length_nil]; omega)]
              have h := emit_code_at_new { csPrefix with nextReg := csPrefix.nextReg + 1 }
                [Instr.Assgn (Register.R csPrefix.nextReg)
                  (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)] (k := 0) (by simp)
              simpa using h
          have h_code2 : compProg (s_osea.pc + 1)
              = some (Instr.Assgn (Register.R (csPrefix.nextReg + 1))
                  (Rhs.Borrow RefKind.Mut false [] (blockSize (obseq.LayoutTy.PtrL τ))
                    dstReg (pathOffset g))) := by
            rw [h_pc]
            refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
            · rw [h_stmtRun, h_len4]; omega
            · rw [h_stmtRun]
              rw [emit_code_lt_nextLabel _ _ (by
                simp only [emit, List.length_cons, List.length_nil]; omega)]
              rw [emit_code_lt_nextLabel _ _ (by
                simp only [emit, List.length_cons, List.length_nil]; omega)]
              have h := emit_code_at_new
                { (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)]) with
                    nextReg := csPrefix.nextReg + 1 + 1 }
                [Instr.Assgn (Register.R (csPrefix.nextReg + 1))
                  (Rhs.Borrow RefKind.Mut false [] (blockSize (obseq.LayoutTy.PtrL τ))
                    dstReg (pathOffset g))] (k := 0) (by simp)
              simpa [emit] using h
          have h_code3 : compProg (s_osea.pc + 1 + 1)
              = some (Instr.RStore obseq.TyVal.PTy (Register.R csPrefix.nextReg)
                  (Register.R (csPrefix.nextReg + 1))) := by
            rw [h_pc]
            refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
            · rw [h_stmtRun, h_len4]; omega
            · rw [h_stmtRun]
              rw [emit_code_lt_nextLabel _ _ (by
                simp only [emit, List.length_cons, List.length_nil]; omega)]
              have h := emit_code_at_new
                (emit { (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)]) with
                    nextReg := csPrefix.nextReg + 1 + 1 }
                  [Instr.Assgn (Register.R (csPrefix.nextReg + 1))
                    (Rhs.Borrow RefKind.Mut false [] (blockSize (obseq.LayoutTy.PtrL τ))
                      dstReg (pathOffset g))])
                [Instr.RStore obseq.TyVal.PTy (Register.R csPrefix.nextReg)
                  (Register.R (csPrefix.nextReg + 1))] (k := 0) (by simp)
              simpa [emit] using h
          have h_code4 : compProg (s_osea.pc + 1 + 1 + 1)
              = some (Instr.Die (Register.R (csPrefix.nextReg + 1))
                  (blockSize (obseq.LayoutTy.PtrL τ))) := by
            rw [h_pc]
            refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
            · rw [h_stmtRun, h_len4]; omega
            · rw [h_stmtRun]
              have h := emit_code_at_new
                (emit (emit { (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                    [Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)]) with
                    nextReg := csPrefix.nextReg + 1 + 1 }
                  [Instr.Assgn (Register.R (csPrefix.nextReg + 1))
                    (Rhs.Borrow RefKind.Mut false [] (blockSize (obseq.LayoutTy.PtrL τ))
                      dstReg (pathOffset g))])
                  [Instr.RStore obseq.TyVal.PTy (Register.R csPrefix.nextReg)
                    (Register.R (csPrefix.nextReg + 1))])
                [Instr.Die (Register.R (csPrefix.nextReg + 1))
                  (blockSize (obseq.LayoutTy.PtrL τ))] (k := 0) (by simp)
              simpa [emit] using h
          -- §5 execute the rhs Borrow
          have h_ref_tgt' : MSB.ref s_osea.perms (bS.addr + 0 + 0) (blockSize τ)
              tagS kind prot mask
              = .ok (tgtPerms, s_osea.perms.NextTag) := by
            simpa using h_ref_tgt
          have h_run1 := runN_Assgn_Borrow_step compProg s_osea
            (Register.R csPrefix.nextReg) srcReg kind prot mask (blockSize τ) 0
            h_code1 h_entryS (by
              show bS.addr + 0 + 0 + blockSize τ ≤ bS.addr + blockSize τ
              simp only [Nat.add_zero]
              exact Nat.le_refl _) h_ref_tgt'
          simp only [Nat.add_zero] at h_run1
          -- §6 execute the dst field Borrow through the base register
          have h_regne : dstReg ≠ Register.R csPrefix.nextReg := by
            cases dstReg with
            | R n =>
                have h_lt := h_prb _ _ _ h_piD
                grind [RegisterBelow]
          have h_dentry : PtrRegisterEntry
              (oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
                (obseq.TyVal.PTy, [Val.Ptr bS.addr 0 (blockSize τ) s_osea.perms.NextTag]))
              dstReg bD.addr 0 (blockSize σ) tagD := by
            show oseair.RegMap.lookup _ _ = _
            rw [RegMap.lookup_insert_ne _ h_regne]
            exact h_entryD
          have h_off_le : bD.addr + 0 + pathOffset g + blockSize (obseq.LayoutTy.PtrL τ)
              ≤ bD.addr + blockSize σ := by
            have h1 : ¬(bD.addr + g.offset + 1 > bD.addr + blockSize σ) := by
              simpa using h_nb
            show bD.addr + 0 + g.offset + 1 ≤ bD.addr + blockSize σ
            simp only [Nat.add_zero]
            grind
          have h_ref_dst' : MSB.ref tgtPerms (bD.addr + 0 + pathOffset g)
              (blockSize (obseq.LayoutTy.PtrL τ)) tagD RefKind.Mut false []
              = .ok (q1, tgtPerms.NextTag) := by
            show MSB.ref tgtPerms (bD.addr + 0 + g.offset) 1 tagD RefKind.Mut false [] = _
            simp only [Nat.add_zero]
            simpa using h_ref_dst
          have h_run2 := runN_Assgn_Borrow_step compProg
            { s_osea with
                perms := tgtPerms,
                reg := oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
                  (obseq.TyVal.PTy, [Val.Ptr bS.addr 0 (blockSize τ) s_osea.perms.NextTag]),
                pc := s_osea.pc + 1 }
            (Register.R (csPrefix.nextReg + 1)) dstReg RefKind.Mut false []
            (blockSize (obseq.LayoutTy.PtrL τ)) (pathOffset g)
            h_code2 h_dentry h_off_le h_ref_dst'
          simp only [Nat.zero_add] at h_run2
          -- §7 the store through the fresh dst tag (BRIDGE 2)
          have h_regne2 : Register.R csPrefix.nextReg
              ≠ Register.R (csPrefix.nextReg + 1) := by grind
          have h_entry_tmpD : PtrRegisterEntry
              (oseair.RegMap.insert
                (oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
                  (obseq.TyVal.PTy, [Val.Ptr bS.addr 0 (blockSize τ) s_osea.perms.NextTag]))
                (Register.R (csPrefix.nextReg + 1))
                (obseq.TyVal.PTy, [Val.Ptr bD.addr (pathOffset g) (blockSize σ)
                  tgtPerms.NextTag]))
              (Register.R (csPrefix.nextReg + 1)) bD.addr
              (bD.addr + g.offset - bD.addr) (blockSize σ) tgtPerms.NextTag := by
            rw [show bD.addr + g.offset - bD.addr = g.offset by grind]
            exact RegMap.lookup_insert_self _ _ _
          have h_wr1' : MSB.useMut q1 (bD.addr + g.offset)
              [Val.Ptr bS.addr 0 (blockSize τ) s_osea.perms.NextTag].length
              tgtPerms.NextTag = .ok q2 := by
            simpa using h_wr1
          obtain ⟨h_wtp, h_sms'⟩ :=
            writeThroughPtr_sim (τ := obseq.LayoutTy.PtrL τ)
              (s_osea :=
                { s_osea with
                    perms := q1,
                    reg := oseair.RegMap.insert
                      (oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
                        (obseq.TyVal.PTy, [Val.Ptr bS.addr 0 (blockSize τ) s_osea.perms.NextTag]))
                      (Register.R (csPrefix.nextReg + 1))
                      (obseq.TyVal.PTy, [Val.Ptr bD.addr (pathOffset g) (blockSize σ)
                        tgtPerms.NextTag]),
                    pc := s_osea.pc + 1 + 1 })
              (resolved := { addr := bD.addr + g.offset, tag := bD.tag,
                             allocBase := bD.addr, allocSize := blockSize σ })
              "RStore Invalid Regs"
              [mirlite.MemValue.ptrVal bS.addr (bS.addr - bS.addr) (blockSize τ)
                s_mir.perms.NextTag]
              [Val.Ptr bS.addr 0 (blockSize τ) s_osea.perms.NextTag] rfl
              ⟨⟨h_raS, by simp, rfl, h_rt_new, h_nw_new, h_domS⟩, trivial⟩
              h_id_a h_entry_tmpD h_wr1'
              (by exact SourceMemSim.rename_mono (AddrRenameIncr.refl ρa) h_incr_t h_sms)
              (Nat.le_add_right _ _)
              (fun k hk => by
                simp [blockSize, Nat.lt_one_iff] at hk
                subst hk
                have h_offlt : g.offset < blockSize σ := by
                  grind
                obtain ⟨a', ha'⟩ := h_domD g.offset h_offlt
                grind [IdentityOnDomain])
              h_step
          have h_run3 := runN_RStore_step compProg _ _ obseq.TyVal.PTy
            (Register.R csPrefix.nextReg) (Register.R (csPrefix.nextReg + 1)) _ _
            h_code3
            (by rw [RegMap.lookup_insert_ne _ h_regne2]
                exact RegMap.lookup_insert_self _ _ _)
            (RegMap.lookup_insert_self _ _ _)
            h_wtp
          -- §8 the dst temp dies (BRIDGE 1's third phase)
          have h_die1' : MSB.die q2 (bD.addr + pathOffset g)
              (blockSize (obseq.LayoutTy.PtrL τ)) tgtPerms.NextTag = .ok q3 := by
            simpa using h_die1
          have h_run4 := runN_Die_step compProg
            { s_osea with
                perms := q2,
                reg := oseair.RegMap.insert
                  (oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
                    (obseq.TyVal.PTy, [Val.Ptr bS.addr 0 (blockSize τ) s_osea.perms.NextTag]))
                  (Register.R (csPrefix.nextReg + 1))
                  (obseq.TyVal.PTy, [Val.Ptr bD.addr (pathOffset g) (blockSize σ)
                    tgtPerms.NextTag]),
                mem := oseair.writeWordSeq s_osea.mem (bD.addr + g.offset)
                  [Val.Ptr bS.addr 0 (blockSize τ) s_osea.perms.NextTag],
                pc := s_osea.pc + 1 + 1 + 1 }
            (Register.R (csPrefix.nextReg + 1)) (blockSize (obseq.LayoutTy.PtrL τ))
            h_code4 (RegMap.lookup_insert_self _ _ _) h_die1'
          have h_runA := (oseair_runN_add 1 1 s_osea compProg _ h_run1).trans h_run2
          have h_runB := (oseair_runN_add (1 + 1) 1 s_osea compProg _ h_runA).trans h_run3
          have h_run := (oseair_runN_add (1 + 1 + 1) 1 s_osea compProg _ h_runB).trans h_run4
          -- §9 the final permission relation (BRIDGE 1 collapses the triple)
          have h_psim4 : PermSim (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag)
              perms'' q3 := by
            obtain ⟨hs, hp, he, hn⟩ := h_psim2
            exact ⟨by rw [h_sm]; exact hs, by rw [h_pf]; exact hp,
                   by rw [h_ex]; exact he, Nat.le_trans hn h_ntle⟩
          -- §10 rebuild the invariant
          refine ⟨_, _, 1 + 1 + 1 + 1, h_incr_t, h_run, ?_⟩
          refine ⟨CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix,
            ⟨prefixCompileState_succ h_csAt h_stmt h_stmtOut, ?_⟩, ?_, h_sms', h_psim4,
            h_id_a, h_wf_t', ?_, ?_, ?_, ?_⟩
          · show s_osea.pc + 1 + 1 + 1 + 1 = _
            rw [h_pc, h_stmtRun, h_len4]
          · have h_lbs' : LocalBindingSim ρa
                (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag)
                s_mir.env s_osea csPrefix :=
              LocalBindingSim.rename_mono (AddrRenameIncr.refl ρa) h_incr_t h_lbs
            have h_lbs1 : LocalBindingSim ρa
                (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag) s_mir.env
                { s_osea with
                    perms := tgtPerms,
                    reg := oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
                      (obseq.TyVal.PTy, [Val.Ptr bS.addr 0 (blockSize τ)
                        s_osea.perms.NextTag]),
                    pc := s_osea.pc + 1 } csPrefix :=
              LocalBindingSim.insert_fresh_reg h_lbs' h_prb (Nat.le_refl _) rfl
            have h_lbs2 : LocalBindingSim ρa
                (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag) s_mir.env
                { s_osea with
                    perms := q3,
                    reg := oseair.RegMap.insert
                      (oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
                        (obseq.TyVal.PTy, [Val.Ptr bS.addr 0 (blockSize τ)
                          s_osea.perms.NextTag]))
                      (Register.R (csPrefix.nextReg + 1))
                      (obseq.TyVal.PTy, [Val.Ptr bD.addr (pathOffset g) (blockSize σ)
                        tgtPerms.NextTag]),
                    mem := oseair.writeWordSeq s_osea.mem (bD.addr + g.offset)
                      [Val.Ptr bS.addr 0 (blockSize τ) s_osea.perms.NextTag],
                    pc := s_osea.pc + 1 + 1 + 1 + 1 } csPrefix :=
              LocalBindingSim.insert_fresh_reg h_lbs1 h_prb (Nat.le_succ _) rfl
            intro τ' loc' binding' h_env'
            obtain ⟨reg', base', tag', h_pi', h_entry', h_ra', h_rt', h_nw', h_dom'⟩ :=
              h_lbs2 loc' binding' h_env'
            refine ⟨reg', base', tag', ?_, h_entry', h_ra', h_rt', h_nw', h_dom'⟩
            rw [h_stmtRun, getPlaceInfo_emit, getPlaceInfo_emit, getPlaceInfo_emit,
              getPlaceInfo_setNextReg, getPlaceInfo_emit, getPlaceInfo_setNextReg]
            exact h_pi'
          · show TagRenameBounded _ perms''.NextTag q3.NextTag
            rw [sb_write_NextTag h_useMut_src]
            refine TagRenameBounded.mono h_tbd' (Nat.le_refl _) ?_
            rw [← sb_write_NextTag h_useMut_tgt]
            exact h_ntle
          · simp only [AllocLockstep, mirlite_writeWordSeq_addrStart,
              oseair_writeWordSeq_addrStart]
            exact h_alloc
          · intro τ' loc' h_none
            rw [h_stmtRun, getPlaceInfo_emit, getPlaceInfo_emit, getPlaceInfo_emit,
              getPlaceInfo_setNextReg, getPlaceInfo_emit, getPlaceInfo_setNextReg]
            exact h_unmap loc' h_none
          · intro idx reg τ'' h_look
            rw [h_stmtRun] at h_look ⊢
            rw [getPlaceInfo_emit, getPlaceInfo_emit, getPlaceInfo_emit,
              getPlaceInfo_setNextReg, getPlaceInfo_emit, getPlaceInfo_setNextReg] at h_look
            refine RegisterBelow.mono ?_ (h_prb _ _ _ h_look)
            simp only [emit]
            omega
        · simp at h_w

/-! ## The deref-dst fragments (MIR order: Borrow first, then the spine)

`*P := &src` lowers, under the d34 MIR order, to the rhs `Borrow` FIRST,
then the dst spine's `Load`s, then the final pointer `Load`, then the
`RStore` of the borrow through it. The borrow temp `R cs.nextReg` must
survive the spine — that is what `ptrChain_lowering_sim`'s register-frame
conjunct exists for. -/

theorem compileStmt_ref_derefdst_run
    {Γ : Ctx} {τ : LayoutTy}
    {P : Place Γ (obseq.LayoutTy.PtrL (obseq.LayoutTy.PtrL τ))} {srcLoc : Local Γ τ}
    {cs cs1 : CompilerState} {srcReg : Register}
    {pOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared P)}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (h_root : CompilerM.run (ensurePlaceRoot (Place.deref P)) cs = cs)
    (h_src : getPlaceInfo cs srcLoc.idx.1 = some (srcReg, τ))
    (h_cs1 : cs1 = emit { cs with nextReg := cs.nextReg + 1 }
      [Instr.Assgn (Register.R cs.nextReg)
        (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)])
    (h_pval : CheckedCompilerM.value (placeToRegChecked RefKind.Shared P) cs1
      = Except.ok pOut)
    (h_pclean : pOut.result.cleanup = []) :
    CheckedCompilerM.run
        (compileStmtChecked
          (Stmt.assign (.deref P) (.ref kind prot mask (.local srcLoc)))) cs
      = emit (emit
          { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) cs1) with
              nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) cs1).nextReg + 1 }
          [Instr.Assgn
            (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) cs1).nextReg)
            (Rhs.Load obseq.TyVal.PTy pOut.result.reg)])
          [Instr.RStore obseq.TyVal.PTy (Register.R cs.nextReg)
            (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P) cs1).nextReg)] := by
  obtain ⟨h_prun, placeOut, h_pval0, h_pres⟩ :=
    placeToRegChecked_local_existing (kind := kind) h_src
  have h_bindD : placeToRegChecked (Γ := Γ) RefKind.Mut (.deref P)
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
  subst h_cs1
  simp [compileStmtChecked, compileRExprPreChecked, placeToBorrowRegChecked, h_bindD,
    h_root, h_prun, h_pval0, h_pres, h_pval]
  simp [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM,
    cleanupInstrs, h_pval, h_pclean, emit_nil]

/-- The deref-dst statement lowers. -/
theorem compileStmt_ref_derefdst_value
    {Γ : Ctx} {τ : LayoutTy}
    {P : Place Γ (obseq.LayoutTy.PtrL (obseq.LayoutTy.PtrL τ))} {srcLoc : Local Γ τ}
    {cs cs1 : CompilerState} {srcReg : Register}
    {pOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared P)}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (h_root : CompilerM.run (ensurePlaceRoot (Place.deref P)) cs = cs)
    (h_src : getPlaceInfo cs srcLoc.idx.1 = some (srcReg, τ))
    (h_cs1 : cs1 = emit { cs with nextReg := cs.nextReg + 1 }
      [Instr.Assgn (Register.R cs.nextReg)
        (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)])
    (h_pval : CheckedCompilerM.value (placeToRegChecked RefKind.Shared P) cs1
      = Except.ok pOut) :
    ∃ so, CheckedCompilerM.value
      (compileStmtChecked
        (Stmt.assign (.deref P) (.ref kind prot mask (.local srcLoc)))) cs
      = Except.ok so := by
  obtain ⟨h_prun, placeOut, h_pval0, h_pres⟩ :=
    placeToRegChecked_local_existing (kind := kind) h_src
  have h_bindD : placeToRegChecked (Γ := Γ) RefKind.Mut (.deref P)
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
  subst h_cs1
  simp only [compileStmtChecked, compileRExprPreChecked, placeToBorrowRegChecked, h_bindD,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
    h_root, h_prun, h_pval0, h_pres]
  simp only [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM]
  simp only [CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure, h_pval]
  exact ⟨_, rfl⟩

/-- REGIME D-dst, CLOSED 2026-08-30: `*P := &src` — a reference stored
    THROUGH a loaded pointer, dst an all-deref load spine, src a bound
    local. Under the d34 MIR order (and the rhs-first source order that
    completed it) both machines run the retag FIRST, then the dst spine:
    fragment `[Borrow(src); spine Loads; Load; RStore]`. The borrow temp
    crosses the spine via `ptrChain_lowering_sim`'s register-frame
    conjunct; the final store is BRIDGE 2 through the loaded tag, its
    bounds supplied by the source `writeResolvedPlace` check through
    `MemValSim`'s `o' = o ∧ s' = s`. One tag is minted on each side. -/
theorem ref_derefdst_local_simulation
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {τ : LayoutTy}
    {P : Place Γ (obseq.LayoutTy.PtrL (obseq.LayoutTy.PtrL τ))}
    {srcLoc : Local Γ τ}
    {bS : mirlite.Binding}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (compProg : oseair.Prog)
    (h_spine : PtrChain P)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    (h_stmt : prog.get? s_mir.pc
      = some (.assign (.deref P) (.ref kind prot mask (.local srcLoc))))
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
  -- §1 invert the source: prepare is the identity on a resolvable deref root
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
  -- §2 the rhs retag mints on the source FIRST (Rust order)
  simp only [mirlite.evalRExpr, mirlite.resolvePlaceAcc, h_envS] at h_step
  rw [if_neg (Nat.lt_irrefl (bS.addr + blockSize τ))] at h_step
  cases h_ref_src : MSB.ref s_mir.perms bS.addr (blockSize τ) bS.tag kind prot mask with
  | error e => rw [h_ref_src] at h_step; simp at h_step
  | ok pr =>
  obtain ⟨perms1, mintS⟩ := pr
  rw [h_ref_src] at h_step
  simp only at h_step
  -- §3 the dst spine resolves on the POST-retag state
  cases h_dres : mirlite.resolvePlaceAcc MSB
      { s_mir with perms := perms1 } P with
  | error e => simp [h_dres] at h_step
  | ok pr2 =>
  obtain ⟨pRes, permsP⟩ := pr2
  simp only [h_dres] at h_step
  by_cases h_qb : pRes.addr < pRes.allocBase ∨
      pRes.addr ≥ pRes.allocBase + pRes.allocSize
  · rw [if_pos h_qb] at h_step
    simp at h_step
  · rw [if_neg h_qb] at h_step
    cases h_qread : MSB.read permsP pRes.addr 1 pRes.tag with
    | error e => simp [h_qread] at h_step
    | ok permsP' =>
    simp only [h_qread] at h_step
    cases h_qfind : mirlite.Mem.find? s_mir.mem pRes.addr with
    | none => simp [h_qfind] at h_step
    | some mv =>
    cases mv with
    | undef => simp [h_qfind] at h_step
    | word w => simp [h_qfind] at h_step
    | ptrVal b o sz t =>
    simp only [h_qfind] at h_step
    -- §4 the retag transported: the fresh pair extends ρt
    obtain ⟨tgtP1, h_ref_tgt, h_mint_eq, h_incr_t, h_wf_t', h_tbd', h_psim'⟩ :=
      sb_ref_respects_PermSim h_psim h_wf_t h_tbd h_rtS h_nwS h_ref_src
    subst h_mint_eq
    have h_rt_new : (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag)
        s_mir.perms.NextTag = some s_osea.perms.NextTag :=
      TagRenameMap.extend_self _ _ _
    have h0 : wildcardTag < s_mir.perms.NextTag := (h_tbd _ _ h_wf_t.2).1
    have h_nw_new : (s_mir.perms.NextTag == wildcardTag) = false := by grind
    -- §5 compiler-side scaffolding: the statement lowers.  The
    -- LocalBindingSim at the post-Borrow state/compiler-state comes first:
    -- it feeds both the mapped-ness of P at cs1 and the spine prelude.
    have h_mapped : PlaceInputsMapped csPrefix (Place.deref P) :=
      placeInputsMapped_of_localBindingSim_resolvePlace h_lbs h_resolved
    have h_root := ensurePlaceRoot_run_eq_of_mapped h_mapped
    have h_lbs0 : LocalBindingSim ρa
        (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag)
        s_mir.env s_osea csPrefix :=
      LocalBindingSim.rename_mono (AddrRenameIncr.refl ρa) h_incr_t h_lbs
    have h_lbs1 : LocalBindingSim ρa
        (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag)
        s_mir.env
        { s_osea with
            perms := tgtP1,
            reg := oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
              (obseq.TyVal.PTy,
                [Val.Ptr bS.addr (0 + 0) (blockSize τ) s_osea.perms.NextTag]),
            pc := s_osea.pc + 1 }
        (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
          [Instr.Assgn (Register.R csPrefix.nextReg)
            (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)]) :=
      LocalBindingSim.insert_fresh_reg h_lbs0 h_prb (Nat.le_refl _) rfl
    have h_mapped1 : PlaceInputsMapped
        (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
          [Instr.Assgn (Register.R csPrefix.nextReg)
            (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)]) P :=
      placeInputsMapped_of_localBindingSim_resolvePlace
        (s_mir := { s_mir with perms := perms1 }) h_lbs1
        (resolvePlace?_of_resolveAcc h_dres)
    obtain ⟨pOut0, h_pval0⟩ := placeToRegChecked_ok_of_placeInputsMapped
      (kind := RefKind.Shared) h_mapped1
    obtain ⟨stmtOut, h_stmtOut⟩ :=
      compileStmt_ref_derefdst_value kind prot mask h_root h_piS rfl h_pval0
    -- state-increment chain: the spine's fragment sits inside the statement's
    obtain ⟨h_lprun, placeOutL, h_lpval, h_lpres⟩ :=
      placeToRegChecked_local_existing (kind := kind) h_piS
    have h_pre_run : CheckedCompilerM.run
        (compileRExprPreChecked (RExpr.ref (Γ := Γ) kind prot mask (.local srcLoc)))
        csPrefix
      = emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
          [Instr.Assgn (Register.R csPrefix.nextReg)
            (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)] := by
      simp [compileRExprPreChecked, placeToBorrowRegChecked,
        h_lprun, h_lpval, h_lpres]
      simp [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM]
    have h_pre_val : ∃ preOut, CheckedCompilerM.value
        (compileRExprPreChecked (RExpr.ref (Γ := Γ) kind prot mask (.local srcLoc)))
        csPrefix = Except.ok preOut := by
      simp only [compileRExprPreChecked, placeToBorrowRegChecked,
        CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
        CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
        CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
        h_lprun, h_lpval]
      exact ⟨_, rfl⟩
    obtain ⟨preOut, h_pre_valOk⟩ := h_pre_val
    have h_bindD : placeToRegChecked (Γ := Γ) RefKind.Mut (.deref P)
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
    have h_incr0 : StateIncr
        (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P)
          (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
            [Instr.Assgn (Register.R csPrefix.nextReg)
              (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)]))
        (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (.deref P))
          (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
            [Instr.Assgn (Register.R csPrefix.nextReg)
              (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)])) := by
      rw [h_bindD, CheckedCompilerM.run_bind]
      cases h : CheckedCompilerM.value (placeToRegChecked RefKind.Shared P)
          (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
            [Instr.Assgn (Register.R csPrefix.nextReg)
              (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)]) with
      | ok a => exact CheckedCompilerM.incr _ _
      | error e => exact StateIncr.refl _
    have h_stmt_bind : compileStmtChecked
          (Stmt.assign (.deref P) (.ref kind prot mask (.local srcLoc)))
        = (do
            let _ ← CheckedCompilerM.lift (ensurePlaceRoot (Place.deref P))
            let pre ← compileRExprPreChecked
              (RExpr.ref kind prot mask (.local srcLoc))
            let dstOut ← placeToRegChecked RefKind.Mut (.deref P)
            let dstRes := dstOut.result
            let _ ← CheckedCompilerM.lift (emitM (pre.store dstRes.reg))
            let _ ← CheckedCompilerM.lift (emitM (cleanupInstrs pre.postCleanup))
            let _ ← CheckedCompilerM.lift (emitM (cleanupInstrs dstRes.cleanup))
            pure {
              result := (),
              evidence := StmtEvidence.assignPlace (.deref P)
                (.ref kind prot mask (.local srcLoc)) dstRes dstOut.evidence
                (pre.ev dstRes.reg)
            }) := rfl
    have h_incr2 : StateIncr
        (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (.deref P))
          (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
            [Instr.Assgn (Register.R csPrefix.nextReg)
              (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)]))
        (CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.deref P) (.ref kind prot mask (.local srcLoc)))) csPrefix) := by
      rw [h_stmt_bind, CheckedCompilerM.run_bind]
      simp only [CheckedCompilerM.value_lift, CheckedCompilerM.run_lift, h_root]
      rw [CheckedCompilerM.run_bind]
      simp only [h_pre_valOk, h_pre_run]
      rw [CheckedCompilerM.run_bind]
      split
      · exact CheckedCompilerM.incr _ _
      · exact StateIncr.refl _
    have h_instP : ∀ q' instr,
        q' < (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P)
          (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
            [Instr.Assgn (Register.R csPrefix.nextReg)
              (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)])).nextLabel →
        (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P)
          (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
            [Instr.Assgn (Register.R csPrefix.nextReg)
              (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)])).code q'
          = some instr →
        compProg q' = some instr := by
      intro q' instr h_lt h_code
      have h_incrP := StateIncr.trans h_incr0 h_incr2
      refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
      · exact Nat.lt_of_lt_of_le h_lt h_incrP.nextLabel_le
      · rw [h_incrP.code_eq q' h_lt]
        exact h_code
    -- §6 execute the Borrow (the rhs, FIRST)
    have h_incr_cs1 : StateIncr
        (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
          [Instr.Assgn (Register.R csPrefix.nextReg)
            (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)])
        (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P)
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
      refine h_instP _ _ (Nat.lt_of_lt_of_le h_lt_cs1 h_incr_cs1.nextLabel_le) ?_
      rw [h_incr_cs1.code_eq _ h_lt_cs1]
      have h := emit_code_at_new { csPrefix with nextReg := csPrefix.nextReg + 1 }
        [Instr.Assgn (Register.R csPrefix.nextReg)
          (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)] (k := 0) (by simp)
      simpa using h
    have h_le1 : bS.addr + 0 + 0 + blockSize τ ≤ bS.addr + blockSize τ := by grind
    have h_ref_tgt' : MSB.ref s_osea.perms (bS.addr + 0 + 0) (blockSize τ) tagS
        kind prot mask = .ok (tgtP1, s_osea.perms.NextTag) := by
      simpa using h_ref_tgt
    have h_run1 := runN_Assgn_Borrow_step compProg s_osea
      (Register.R csPrefix.nextReg) srcReg kind prot mask (blockSize τ) 0
      h_code1 h_entryS h_le1 h_ref_tgt'
    -- §7 the spine prelude, run from the post-Borrow state under the
    -- extended rename
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
    have h_pc1 : s_osea.pc + 1
        = (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
            [Instr.Assgn (Register.R csPrefix.nextReg)
              (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)]).nextLabel := by
      simp only [emit, List.length_cons, List.length_nil]
      omega
    obtain ⟨pOut, n1, s_mid, ptag, h_pval, h_pclean, h_prun, h_ppc, h_pmem, h_ppsim,
      h_pnt1, h_pnt2, h_plbs, h_pentry, h_prt, h_pnw, h_ple, h_prange, h_pbelow,
      h_pprm, h_pregmono, h_plabmono, h_pframe⟩ :=
      ptrChain_lowering_sim h_id_a h_wf_t' h_spine RefKind.Shared
        (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
          [Instr.Assgn (Register.R csPrefix.nextReg)
            (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)])
        { s_osea with
            perms := tgtP1,
            reg := oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
              (obseq.TyVal.PTy,
                [Val.Ptr bS.addr (0 + 0) (blockSize τ) s_osea.perms.NextTag]),
            pc := s_osea.pc + 1 }
        pRes permsP h_dres h_tbd' h_lbs1 h_prb1 h_sms1 h_psim' h_pc1 h_instP
    have h_stmtRun := compileStmt_ref_derefdst_run kind prot mask
      h_root h_piS rfl h_pval h_pclean
    -- §8 execute the Load through the transported pointer-cell read
    obtain ⟨p2, h_read_tgt, h_psim2⟩ :=
      sb_read_respects_PermSim h_ppsim h_wf_t' h_prt h_pnw h_qread
    have h_cancel : pRes.allocBase + (pRes.addr - pRes.allocBase) = pRes.addr := by
      grind
    have h_offP : pRes.addr - pRes.allocBase < pRes.allocSize := by grind
    have h_read_tgt' : MSB.read s_mid.perms
        (pRes.allocBase + (pRes.addr - pRes.allocBase)) 1 ptag = .ok p2 := by
      rw [h_cancel]; exact h_read_tgt
    have h_len2 : ((emit (emit
        { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P)
            (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
              [Instr.Assgn (Register.R csPrefix.nextReg)
                (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)])) with
            nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P)
              (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                [Instr.Assgn (Register.R csPrefix.nextReg)
                  (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)])).nextReg + 1 }
        [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P)
            (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
              [Instr.Assgn (Register.R csPrefix.nextReg)
                (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)])).nextReg)
          (Rhs.Load obseq.TyVal.PTy pOut.result.reg)])
        [Instr.RStore obseq.TyVal.PTy (Register.R csPrefix.nextReg)
          (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P)
            (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
              [Instr.Assgn (Register.R csPrefix.nextReg)
                (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)])).nextReg)])).nextLabel
      = (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P)
          (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
            [Instr.Assgn (Register.R csPrefix.nextReg)
              (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)])).nextLabel + 2 := by
      simp only [emit, List.length_cons, List.length_nil]
    have h_code2 : compProg s_mid.pc
        = some (Instr.Assgn (Register.R (CheckedCompilerM.run
            (placeToRegChecked RefKind.Shared P)
            (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
              [Instr.Assgn (Register.R csPrefix.nextReg)
                (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)])).nextReg)
            (Rhs.Load obseq.TyVal.PTy pOut.result.reg)) := by
      rw [h_ppc]
      refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
      · rw [h_stmtRun, h_len2]; omega
      · rw [h_stmtRun]
        rw [emit_code_lt_nextLabel _ _ (by
          simp only [emit, List.length_cons, List.length_nil]; omega)]
        have h := emit_code_at_new
          { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P)
              (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                [Instr.Assgn (Register.R csPrefix.nextReg)
                  (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)])) with
              nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P)
                (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                  [Instr.Assgn (Register.R csPrefix.nextReg)
                    (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)])).nextReg + 1 }
          [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P)
              (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                [Instr.Assgn (Register.R csPrefix.nextReg)
                  (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)])).nextReg)
            (Rhs.Load obseq.TyVal.PTy pOut.result.reg)] (k := 0) (by simp)
        simpa using h
    have h_run2 := runN_Assgn_Load_ptr_step compProg s_mid
      (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P)
        (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
          [Instr.Assgn (Register.R csPrefix.nextReg)
            (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)])).nextReg)
      pOut.result.reg obseq.TyVal.PTy
      h_code2 h_pentry h_offP h_read_tgt'
    -- the loaded cell holds the ρ-renamed stored pointer
    have h_sms_mid : SourceMemSim ρa
        (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag)
        s_mir.mem s_mid.mem := by
      rw [h_pmem]
      exact h_sms1
    obtain ⟨addr', value', h_ra', h_find_tgt, h_mvs⟩ := h_sms_mid _ _ h_qfind
    have h_addr' : addr' = pRes.addr := (h_id_a _ _ h_ra').symm
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
    have h_rws : oseair.readWordSeq s_mid.mem
        (pRes.allocBase + (pRes.addr - pRes.allocBase))
        (obseq.typeSize obseq.TyVal.PTy) = [Val.Ptr b2 o2 s2 t2] := by
      rw [h_cancel]
      show oseair.readWordSeq s_mid.mem pRes.addr 1 = _
      simp [oseair.readWordSeq, h_find_tgt]
    -- §9 the store through the loaded tag (BRIDGE 2)
    have h_regne1 : Register.R csPrefix.nextReg
        ≠ Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P)
          (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
            [Instr.Assgn (Register.R csPrefix.nextReg)
              (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)])).nextReg := by
      have h_le : csPrefix.nextReg + 1
          ≤ (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P)
            (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
              [Instr.Assgn (Register.R csPrefix.nextReg)
                (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)])).nextReg :=
        h_pregmono
      simp only [ne_eq, Register.R.injEq]
      omega
    have h_below1 : RegisterBelow
        (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
          [Instr.Assgn (Register.R csPrefix.nextReg)
            (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)]).nextReg
        (Register.R csPrefix.nextReg) := by
      simp only [emit]
      show csPrefix.nextReg < csPrefix.nextReg + 1
      exact Nat.lt_succ_self _
    have h_borrow_mid : oseair.RegMap.lookup s_mid.reg (Register.R csPrefix.nextReg)
        = some (obseq.TyVal.PTy,
            [Val.Ptr bS.addr (0 + 0) (blockSize τ) s_osea.perms.NextTag]) := by
      rw [h_pframe _ h_below1]
      exact RegMap.lookup_insert_self _ _ _
    have h_w := h_step
    simp only [mirlite.writeResolvedPlace] at h_w
    split at h_w
    · simp at h_w
    · rename_i h_nb
      split at h_w
      · rename_i perms2 h_useMut_src
        cases h_w
        obtain ⟨p3, h_useMut_tgt, h_psim3⟩ :=
          sb_write_respects_PermSim h_psim2 h_wf_t' h_t h_tnw h_useMut_src
        have h_o_lt : o2 < s2 := by
          grind
        have h_entry_loaded : PtrRegisterEntry
            (oseair.RegMap.insert s_mid.reg
              (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P)
                (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                  [Instr.Assgn (Register.R csPrefix.nextReg)
                    (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)])).nextReg)
              (obseq.TyVal.PTy, oseair.readWordSeq s_mid.mem
                (pRes.allocBase + (pRes.addr - pRes.allocBase))
                (obseq.typeSize obseq.TyVal.PTy)))
            (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P)
              (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                [Instr.Assgn (Register.R csPrefix.nextReg)
                  (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)])).nextReg)
            b2 o2 s2 t2 := by
          show oseair.RegMap.lookup _ _ = _
          rw [RegMap.lookup_insert_self, h_rws]
        obtain ⟨h_wtp, h_sms'⟩ :=
          writeThroughPtr_sim (τ := obseq.LayoutTy.PtrL τ)
            (s_osea :=
              { s_mid with
                  perms := p2,
                  reg := oseair.RegMap.insert s_mid.reg
                    (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P)
                      (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                        [Instr.Assgn (Register.R csPrefix.nextReg)
                          (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)])).nextReg)
                    (obseq.TyVal.PTy, oseair.readWordSeq s_mid.mem
                      (pRes.allocBase + (pRes.addr - pRes.allocBase))
                      (obseq.typeSize obseq.TyVal.PTy)),
                  pc := s_mid.pc + 1 })
            (resolved := { addr := b2 + o2, tag := t, allocBase := b2,
                           allocSize := s2 })
            "RStore Invalid Regs"
            [mirlite.MemValue.ptrVal bS.addr (bS.addr - bS.addr) (blockSize τ)
              s_mir.perms.NextTag]
            [Val.Ptr bS.addr (0 + 0) (blockSize τ) s_osea.perms.NextTag] rfl
            ⟨⟨h_raS, by simp, rfl, h_rt_new, h_nw_new,
              fun k hk => h_domS k hk⟩, trivial⟩
            h_id_a
            (by
              show PtrRegisterEntry _ _ b2 (b2 + o2 - b2) s2 t2
              rw [Nat.add_sub_cancel_left]
              exact h_entry_loaded)
            h_useMut_tgt
            (by
              show SourceMemSim ρa
                (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag)
                s_mir.mem s_mid.mem
              exact h_sms_mid)
            (Nat.le_add_right _ _)
            (fun k hk => by
              have hk0 : k = 0 := by simpa using hk
              subst hk0
              obtain ⟨a', ha'⟩ := h_range o2 h_o_lt
              have h_eq := h_id_a _ _ ha'
              grind)
            h_step
        have h_run3 := runN_RStore_step compProg _ _ obseq.TyVal.PTy
          (Register.R csPrefix.nextReg)
          (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P)
            (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
              [Instr.Assgn (Register.R csPrefix.nextReg)
                (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)])).nextReg)
          _ _
          (by
            show compProg (s_mid.pc + 1) = _
            refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
            · rw [h_stmtRun, h_len2, h_ppc]; omega
            · rw [h_stmtRun]
              have h := emit_code_at_new
                (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P)
                    (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                      [Instr.Assgn (Register.R csPrefix.nextReg)
                        (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)])) with
                    nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P)
                      (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                        [Instr.Assgn (Register.R csPrefix.nextReg)
                          (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)])).nextReg + 1 }
                  [Instr.Assgn (Register.R (CheckedCompilerM.run
                      (placeToRegChecked RefKind.Shared P)
                      (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                        [Instr.Assgn (Register.R csPrefix.nextReg)
                          (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)])).nextReg)
                    (Rhs.Load obseq.TyVal.PTy pOut.result.reg)])
                [Instr.RStore obseq.TyVal.PTy (Register.R csPrefix.nextReg)
                  (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P)
                    (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                      [Instr.Assgn (Register.R csPrefix.nextReg)
                        (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)])).nextReg)]
                (k := 0) (by simp)
              rw [h_ppc]
              simpa [emit] using h)
          (by
            rw [RegMap.lookup_insert_ne _ h_regne1]
            exact h_borrow_mid)
          (RegMap.lookup_insert_self _ _ _)
          h_wtp
        have h_runA := (oseair_runN_add 1 n1 s_osea compProg _ h_run1).trans h_prun
        have h_runB := (oseair_runN_add (1 + n1) 1 s_osea compProg _ h_runA).trans h_run2
        have h_runC := (oseair_runN_add (1 + n1 + 1) 1 s_osea compProg _ h_runB).trans h_run3
        -- §10 rebuild the invariant under the extended ρt
        refine ⟨_, _, 1 + n1 + 1 + 1, h_incr_t, h_runC, ?_⟩
        refine ⟨CheckedCompilerM.run
          (compileStmtChecked
            (Stmt.assign (.deref P)
              (.ref kind prot mask (.local srcLoc)))) csPrefix,
          ⟨prefixCompileState_succ h_csAt h_stmt h_stmtOut, ?_⟩, ?_, h_sms', h_psim3,
          h_id_a, h_wf_t', ?_, ?_, ?_, ?_⟩
        · show s_mid.pc + 1 + 1 = _
          rw [h_ppc, h_stmtRun, h_len2]
        · have h_lbs2 : LocalBindingSim ρa
              (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag)
              s_mir.env
              { s_mid with
                  perms := p2,
                  reg := oseair.RegMap.insert s_mid.reg
                    (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P)
                      (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                        [Instr.Assgn (Register.R csPrefix.nextReg)
                          (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)])).nextReg)
                    (obseq.TyVal.PTy, oseair.readWordSeq s_mid.mem
                      (pRes.allocBase + (pRes.addr - pRes.allocBase))
                      (obseq.typeSize obseq.TyVal.PTy)),
                  pc := s_mid.pc + 1 }
              (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                [Instr.Assgn (Register.R csPrefix.nextReg)
                  (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)]) :=
            LocalBindingSim.insert_fresh_reg h_plbs h_prb1 h_pregmono rfl
          intro τ' loc' binding' h_env'
          obtain ⟨reg', base', tag', h_pi', h_entry', h_ra'', h_rt', h_nw', h_dom'⟩ :=
            h_lbs2 loc' binding' h_env'
          refine ⟨reg', base', tag', ?_, h_entry', h_ra'', h_rt', h_nw', h_dom'⟩
          rw [h_stmtRun, getPlaceInfo_emit, getPlaceInfo_emit, getPlaceInfo_setNextReg]
          show (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P)
            (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
              [Instr.Assgn (Register.R csPrefix.nextReg)
                (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)])).placeRegMap.lookup
              loc'.idx.1 = _
          rw [h_pprm]
          exact h_pi'
        · show TagRenameBounded _ perms2.NextTag p3.NextTag
          rw [sb_write_NextTag h_useMut_src, sb_read_NextTag h_qread, h_pnt1,
            sb_write_NextTag h_useMut_tgt, sb_read_NextTag h_read_tgt]
          exact TagRenameBounded.mono h_tbd' (Nat.le_refl _) h_pnt2
        · simp only [AllocLockstep, mirlite_writeWordSeq_addrStart,
            oseair_writeWordSeq_addrStart, h_pmem]
          exact h_alloc
        · intro τ' loc' h_none
          rw [h_stmtRun, getPlaceInfo_emit, getPlaceInfo_emit, getPlaceInfo_setNextReg]
          show (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P)
            (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
              [Instr.Assgn (Register.R csPrefix.nextReg)
                (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)])).placeRegMap.lookup
              loc'.idx.1 = none
          rw [h_pprm]
          exact h_unmap loc' h_none
        · intro idx reg'' τ'' h_look
          rw [h_stmtRun] at h_look ⊢
          rw [getPlaceInfo_emit, getPlaceInfo_emit, getPlaceInfo_setNextReg] at h_look
          have h_cs : getPlaceInfo csPrefix idx = some (reg'', τ'') := by
            have h_prm2 : (CheckedCompilerM.run (placeToRegChecked RefKind.Shared P)
                (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                  [Instr.Assgn (Register.R csPrefix.nextReg)
                    (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)])).placeRegMap
                = csPrefix.placeRegMap := h_pprm
            show csPrefix.placeRegMap.lookup idx = _
            rw [← h_prm2]
            exact h_look
          refine RegisterBelow.mono ?_ (h_prb _ _ _ h_cs)
          simp only [emit]
          have h_le := h_pregmono
          simp only [emit] at h_le
          omega
      · simp at h_w

/-- RESIDUAL (sorried), NARROWED 2026-08-30: after the dst-flattening
    recursion (`ref_proj_dst_simulation` — nested projection dsts of
    any depth reassociate on both machines and land in the closed
    field-dst leaves, stmt0-threaded). Remaining:
    - projected DEREF dst bases (`(*p).f := &x`) and non-spine deref
      dsts (`*p := &x` with a non-spine `p`);
    - non-local srcs under non-local dsts (proj/deref src places);
    - non-spine deref srcs, proj-of-proj srcs, unbound dst roots. -/
theorem ref_place_residual
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {τ : LayoutTy}
    {dst : Place Γ (obseq.LayoutTy.PtrL τ)} {src : Place Γ τ}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (compProg : oseair.Prog)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    -- the PROGRAM's statement may be a reassociation-equivalent spelling
    -- (the dst-flattening recursion threads it through)
    {stmt0 : Stmt Γ}
    (h_stmt : prog.get? s_mir.pc = some stmt0)
    (h_step : mirlite.stepStmt MSB s_mir (.assign dst (.ref kind prot mask src)) = .ok s_mir') :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' := by
  sorry

/-- The dst-flattening recursion for ref: a PROJECTED destination of any
    nesting depth reassociates on both machines
    (`compileStmt_assign_proj_assoc_run/_value`,
    `stepStmt_assign_proj_assoc`) and recurses into the closed field-dst
    leaves, threading the PROGRAM's own statement (`stmt0`). Deref
    bases, non-local srcs and unbound roots route to the residual. -/
theorem ref_proj_dst_simulation
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
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
          by_cases h_g0 : pathOffset g = 0
          · cases h_envD : mirlite.Env.lookup s_mir.env dstLoc with
            | some bD =>
                cases h_envS : mirlite.Env.lookup s_mir.env srcLoc with
                | some bS =>
                    obtain ⟨ρt', s_osea', n, h_incr, h_run, h_inv'⟩ :=
                      ref_local_projzero_simulation kind prot mask compProg
                        h_g0 h_comp h_inv h_stmt h_run0 h_val0
                        h_envD h_envS h_step
                    exact ⟨ρa, ρt', s_osea', n, AddrRenameIncr.refl ρa, h_incr,
                      h_run, h_inv'⟩
                | none =>
                    exfalso
                    simp [mirlite.stepStmt, mirlite.doAssign, mirlite.doAssignCont,
                      mirlite.preparePlaceAssign, mirlite.resolvePlace?, h_envD,
                      mirlite.resolvePlaceAcc, h_envS,
                      mirlite.evalRExpr] at h_step
            | none =>
                exact ref_place_residual kind prot mask compProg h_comp h_inv
                  h_stmt h_step
          · cases h_envD : mirlite.Env.lookup s_mir.env dstLoc with
            | some bD =>
                cases h_envS : mirlite.Env.lookup s_mir.env srcLoc with
                | some bS =>
                    obtain ⟨ρt', s_osea', n, h_incr, h_run, h_inv'⟩ :=
                      ref_local_projoffset_simulation kind prot mask compProg
                        h_g0 h_comp h_inv h_stmt h_run0 h_val0
                        h_envD h_envS h_step
                    exact ⟨ρa, ρt', s_osea', n, AddrRenameIncr.refl ρa, h_incr,
                      h_run, h_inv'⟩
                | none =>
                    exfalso
                    simp [mirlite.stepStmt, mirlite.doAssign, mirlite.doAssignCont,
                      mirlite.preparePlaceAssign, mirlite.resolvePlace?, h_envD,
                      mirlite.resolvePlaceAcc, h_envS,
                      mirlite.evalRExpr] at h_step
            | none =>
                exact ref_place_residual kind prot mask compProg h_comp h_inv
                  h_stmt h_step
      | proj _ _ =>
          exact ref_place_residual kind prot mask compProg h_comp h_inv h_stmt h_step
      | deref _ =>
          exact ref_place_residual kind prot mask compProg h_comp h_inv h_stmt h_step
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
      exact ref_place_residual kind prot mask compProg h_comp h_inv h_stmt h_step



/-- LEAF 3 (the dispatcher): per-statement simulation for
    `.assign dst (.ref kind prot mask src)`, decomposed by the shapes of
    the two places. Regime L→L (both bound locals, any referent size) is
    CLOSED by `ref_local_local_simulation`; the residuals are named. -/
theorem CompilerInv_step_ref
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
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
                  simp [mirlite.stepStmt, mirlite.doAssign, mirlite.doAssignCont, mirlite.preparePlaceAssign,
                    mirlite.resolvePlace?, h_envD, mirlite.resolvePlaceAcc, h_envS,
                    mirlite.evalRExpr] at h_step
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
          cases sbase with
          | «local» srcLoc =>
              cases h_envD : mirlite.Env.lookup s_mir.env dstLoc with
              | some bD =>
                  cases h_envS : mirlite.Env.lookup s_mir.env srcLoc with
                  | some bS =>
                      -- CLOSED: `dst := &kind s.f`
                      obtain ⟨ρt', s_osea', n, h_incr, h_run, h_inv'⟩ :=
                        ref_proj_local_simulation kind prot mask compProg h_comp h_inv
                          h_stmt h_envD h_envS h_step
                      exact ⟨ρa, ρt', s_osea', n, AddrRenameIncr.refl ρa, h_incr,
                        h_run, h_inv'⟩
                  | none =>
                      exfalso
                      simp [mirlite.stepStmt, mirlite.doAssign, mirlite.doAssignCont,
                        mirlite.preparePlaceAssign, mirlite.resolvePlace?, h_envD,
                        mirlite.resolvePlaceAcc, h_envS, mirlite.evalRExpr] at h_step
              | none =>
                  exact ref_place_residual kind prot mask compProg h_comp h_inv
                    h_stmt h_step
          | proj _ _ =>
              exact ref_place_residual kind prot mask compProg h_comp h_inv h_stmt h_step
          | deref _ =>
              exact ref_place_residual kind prot mask compProg h_comp h_inv h_stmt h_step
      | deref pp =>
          by_cases h_sp : PtrChain pp
          · cases h_envD : mirlite.Env.lookup s_mir.env dstLoc with
            | some bD =>
                -- CLOSED: `dst := &kind *p` through a load spine
                obtain ⟨ρt', s_osea', n, h_incr, h_run, h_inv'⟩ :=
                  ref_deref_local_simulation kind prot mask compProg h_sp h_comp h_inv
                    h_stmt h_envD h_step
                exact ⟨ρa, ρt', s_osea', n, AddrRenameIncr.refl ρa, h_incr,
                  h_run, h_inv'⟩
            | none =>
                exact ref_place_residual kind prot mask compProg h_comp h_inv
                  h_stmt h_step
          · exact ref_place_residual kind prot mask compProg h_comp h_inv h_stmt h_step
  | proj dbase g =>
      exact ref_proj_dst_simulation kind prot mask compProg h_comp h_inv h_stmt
        (fun _ => rfl) (fun _ so h => ⟨so, h⟩) h_step
  | deref P =>
      cases src with
      | «local» srcLoc =>
          by_cases h_sp : PtrChain P
          · cases h_envS : mirlite.Env.lookup s_mir.env srcLoc with
            | some bS =>
                -- CLOSED: `*P := &kind src` through a load spine
                obtain ⟨ρt', s_osea', n, h_incr, h_run, h_inv'⟩ :=
                  ref_derefdst_local_simulation kind prot mask compProg h_sp h_comp
                    h_inv h_stmt h_envS h_step
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
          · exact ref_place_residual kind prot mask compProg h_comp h_inv h_stmt h_step
      | proj _ _ =>
          exact ref_place_residual kind prot mask compProg h_comp h_inv h_stmt h_step
      | deref _ =>
          exact ref_place_residual kind prot mask compProg h_comp h_inv h_stmt h_step

end obseq3.proof
