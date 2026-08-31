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
  simp only [mirlite.preparePlaceAssign, mirlite.resolvePlace?,
    mirlite.resolvePlaceAcc, h_env, mirlite.allocateRoot,
    mirlite.allocateBase, mirlite.allocate] at h
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

/-- The fragment of `dst := &kind s.f` when `dst` is an UNMAPPED local
    and the borrowed place is a PROJECTED field of a mapped local:
    `Alloc` for the fresh destination root, then the `Borrow` at the
    field's offset, then the `RStore`. Same THREE instructions as the
    fresh L→L fragment — as everywhere in `ref`, the projection only
    moves the borrow's offset operand. -/
theorem compileStmt_ref_fresh_projsrc_run
    {Γ : Ctx} {τ σb : LayoutTy}
    {dstLoc : Local Γ (obseq.LayoutTy.PtrL τ)} {srcLoc : Local Γ σb}
    {f : PathTo σb τ}
    {cs : CompilerState} {srcReg : Register}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = none)
    (h_src : getPlaceInfo cs srcLoc.idx.1 = some (srcReg, σb)) :
    CheckedCompilerM.run
        (compileStmtChecked
          (Stmt.assign (.local dstLoc)
            (.ref kind prot mask (.proj (.local srcLoc) f)))) cs
      = emit (emit
          { (setPlaceInfo
              (emit { cs with nextReg := cs.nextReg + 1 }
                [Instr.Assgn (Register.R cs.nextReg)
                  (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))])
              dstLoc.idx.1 (Register.R cs.nextReg, obseq.LayoutTy.PtrL τ)) with
              nextReg := cs.nextReg + 1 + 1 }
          [Instr.Assgn (Register.R (cs.nextReg + 1))
            (Rhs.Borrow kind prot mask (blockSize τ) srcReg (pathOffset f))])
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
  simp [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked, h_borrow_eq,
    h_run, h_val, h_prun, h_pval, h_pres]
  simp [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM,
    cleanupInstrs, emit_nil, setPlaceInfo, emit]
  funext label
  rw [if_neg (fun h => by rcases h with ⟨h1, h2⟩; omega)]

/-- The fresh-destination proj-source statement lowers. -/
theorem compileStmt_ref_fresh_projsrc_value
    {Γ : Ctx} {τ σb : LayoutTy}
    {dstLoc : Local Γ (obseq.LayoutTy.PtrL τ)} {srcLoc : Local Γ σb}
    {f : PathTo σb τ}
    {cs : CompilerState} {srcReg : Register}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = none)
    (h_src : getPlaceInfo cs srcLoc.idx.1 = some (srcReg, σb)) :
    ∃ so, CheckedCompilerM.value
      (compileStmtChecked
        (Stmt.assign (.local dstLoc)
          (.ref kind prot mask (.proj (.local srcLoc) f)))) cs
      = Except.ok so := by
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_fresh (loc := dstLoc) h_dst
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
  simp only [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked,
    placeToBorrowRegChecked,
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

/-- The fragment of `dst := &kind *P`, stated over the OPAQUE run of the
    WHOLE source place's lowering: the src code (owned by the mother
    lemma, ending in its `Load`), then the `Borrow` off the loaded
    register, then the `RStore` into the mapped dst. The borrow-deref
    arm shares its prefix with the place-lowering deref arm, so the
    equality is proved by one case split on the INNER value. -/
theorem compileStmt_ref_deref_run
    {Γ : Ctx} {τ : LayoutTy}
    {dstLoc : Local Γ (obseq.LayoutTy.PtrL τ)}
    {P : Place Γ (obseq.LayoutTy.PtrL τ)}
    {cs : CompilerState} {dstReg : Register}
    {dOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared (.deref P))}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = some (dstReg, obseq.LayoutTy.PtrL τ))
    (h_dval : CheckedCompilerM.value (placeToRegChecked RefKind.Shared (.deref P)) cs
      = Except.ok dOut) :
    CheckedCompilerM.run
        (compileStmtChecked
          (Stmt.assign (.local dstLoc) (.ref kind prot mask (.deref P)))) cs
      = emit (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (Place.deref P)) cs) with
            nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (Place.deref P)) cs).nextReg + 1 }
          [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (Place.deref P)) cs).nextReg)
            (Rhs.Borrow kind prot mask (blockSize τ) dOut.result.reg 0)])
          [Instr.RStore obseq.TyVal.PTy (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (Place.deref P)) cs).nextReg) dstReg] := by
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_existing h_dst
  have h_run' : (ensureLocalRegE dstLoc cs).snd.val = cs := h_run
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
      simp only [CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
        CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
        CheckedCompilerM.run_pure, CheckedCompilerM.value_pure, h_x] at h_dval
      simp at h_dval
  | ok pOut =>
      rw [h_bindD] at h_dval
      simp only [CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
        CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
        CheckedCompilerM.run_pure, CheckedCompilerM.value_pure, h_x] at h_dval
      simp only [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM] at h_dval
      cases h_dval
      simp [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked,
        h_bindB, h_bindD, h_run, h_run', h_val, h_x]
      simp [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM,
        cleanupInstrs, emit_nil]

/-- The fragment of `dst := &kind *chain` when `dst` is an UNMAPPED
    local: the σ-sized `Alloc` for the fresh root comes FIRST, so the
    source spine lowers from the post-`Alloc` compiler state and the
    `RStore` goes through the root register. -/
theorem compileStmt_ref_fresh_derefsrc_run
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
    CheckedCompilerM.run
        (compileStmtChecked
          (Stmt.assign (.local dstLoc) (.ref kind prot mask (.deref P)))) cs
      = emit (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (Place.deref P))
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
                dstLoc.idx.1 (Register.R cs.nextReg, obseq.LayoutTy.PtrL τ))).nextReg) (Register.R cs.nextReg)] := by
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
  cases h_x : CheckedCompilerM.value (placeToRegChecked RefKind.Shared P)
      (setPlaceInfo
        (emit { cs with nextReg := cs.nextReg + 1 }
          [Instr.Assgn (Register.R cs.nextReg)
            (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))])
        dstLoc.idx.1 (Register.R cs.nextReg, obseq.LayoutTy.PtrL τ)) with
  | error e =>
      exfalso
      rw [h_bindD] at h_dval
      simp only [CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
        CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
        CheckedCompilerM.run_pure, CheckedCompilerM.value_pure, h_x] at h_dval
      simp at h_dval
  | ok pOut =>
      rw [h_bindD] at h_dval
      simp only [CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
        CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
        CheckedCompilerM.run_pure, CheckedCompilerM.value_pure, h_x] at h_dval
      simp only [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM] at h_dval
      cases h_dval
      simp [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked,
        h_bindB, h_bindD, h_run, h_val, h_x]
      simp [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM,
        cleanupInstrs, emit_nil, setPlaceInfo]

/-- The fresh-destination deref-src statement lowers. -/
theorem compileStmt_ref_fresh_derefsrc_value
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
    ∃ so, CheckedCompilerM.value
      (compileStmtChecked
        (Stmt.assign (.local dstLoc) (.ref kind prot mask (.deref P)))) cs
      = Except.ok so := by
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
  cases h_x : CheckedCompilerM.value (placeToRegChecked RefKind.Shared P)
      (setPlaceInfo
        (emit { cs with nextReg := cs.nextReg + 1 }
          [Instr.Assgn (Register.R cs.nextReg)
            (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))])
        dstLoc.idx.1 (Register.R cs.nextReg, obseq.LayoutTy.PtrL τ)) with
  | error e =>
      exfalso
      rw [h_bindD] at h_dval
      simp only [CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
        CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
        CheckedCompilerM.run_pure, CheckedCompilerM.value_pure, h_x] at h_dval
      simp at h_dval
  | ok pOut =>
      rw [h_bindD] at h_dval
      simp only [CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
        CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
        CheckedCompilerM.run_pure, CheckedCompilerM.value_pure, h_x] at h_dval
      simp only [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM] at h_dval
      cases h_dval
      simp only [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked,
        h_bindB, h_bindD,
        CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
        CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
        CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
        h_run, h_x]
      simp only [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM]
      exact ⟨_, rfl⟩

/-- The deref-src statement lowers. -/
theorem compileStmt_ref_deref_value
    {Γ : Ctx} {τ : LayoutTy}
    {dstLoc : Local Γ (obseq.LayoutTy.PtrL τ)}
    {P : Place Γ (obseq.LayoutTy.PtrL τ)}
    {cs : CompilerState} {dstReg : Register}
    {dOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared (.deref P))}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = some (dstReg, obseq.LayoutTy.PtrL τ))
    (h_dval : CheckedCompilerM.value (placeToRegChecked RefKind.Shared (.deref P)) cs
      = Except.ok dOut) :
    ∃ so, CheckedCompilerM.value
      (compileStmtChecked
        (Stmt.assign (.local dstLoc) (.ref kind prot mask (.deref P)))) cs
      = Except.ok so := by
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_existing h_dst
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
      simp only [CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
        CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
        CheckedCompilerM.run_pure, CheckedCompilerM.value_pure, h_x] at h_dval
      simp at h_dval
  | ok pOut =>
      simp only [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked,
        h_bindB,
        CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
        CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
        CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
        h_run, h_x]
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
  simp only [compileRExprToChecked, compileRExprPreChecked, h_bF, h_bO,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure]
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
  simp only [compileRExprToChecked, compileRExprPreChecked, h_bF, h_bO,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure]
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
  simp only [compileStmtChecked,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure]
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
  simp only [compileStmtChecked,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure] at h_so ⊢
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
    simp only [mirlite.preparePlaceAssign, mirlite.resolvePlace?, h_envD] at h_prep
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
      compileStmt_ref_deref_value kind prot mask h_piD h_dval
    obtain ⟨stmtOut, h_stmtOut⟩ := h_val0 csPrefix stmtOutC h_stmtOutC
    have h_stmtRun := (h_run0 csPrefix).trans
      (compileStmt_ref_deref_run kind prot mask h_piD h_dval)
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
    -- §3 the WHOLE src lowering via the mother lemma (through the Load)
    obtain ⟨dOut', n1, s_mid, tres, h_dval', h_dclean, h_drun, h_dpc, h_dmem,
      h_dpsim, h_dnt1, h_dnt2, h_dlbs, h_dentry, h_drt, h_dnw, h_dle, h_drange,
      h_dbelow, h_dprm, h_dregmono, h_dlabmono, -, h_dbase⟩ :=
      ptrChain_lowering_sim h_id_a h_wf_t h_spine RefKind.Shared csPrefix s_osea
        resolved permsR h_dres h_tbd h_lbs h_prb h_sms h_psim h_pc h_instS
    have h_deq : dOut = dOut' := by grind
    subst h_deq
    have h_cancel : resolved.allocBase + (resolved.addr - resolved.allocBase)
        = resolved.addr := Nat.add_sub_cancel' h_dle
    -- §4 the retag transported at the post-src state: the fresh pair
    -- extends ρt
    have h_tbd_mid : TagRenameBounded ρt permsR.NextTag s_mid.perms.NextTag := by
      rw [h_dnt1]
      exact TagRenameBounded.mono h_tbd (Nat.le_refl _) h_dnt2
    obtain ⟨tgtPerms, h_ref_tgt, h_fresh_eq, h_incr_t, h_wf_t', h_tbd', h_psim'⟩ :=
      sb_ref_respects_PermSim h_dpsim h_wf_t h_tbd_mid h_drt h_dnw h_ref_src
    subst h_fresh_eq
    have h_rt_new : (ρt.extend permsR.NextTag s_mid.perms.NextTag) permsR.NextTag
        = some s_mid.perms.NextTag := TagRenameMap.extend_self _ _ _
    have h0 : wildcardTag < permsR.NextTag := (h_tbd_mid _ _ h_wf_t.2).1
    have h_nw_new : (permsR.NextTag == wildcardTag) = false := by grind
    -- §5 execute the Borrow: bound from the retag-dereferenceability check
    have h_code1 : compProg s_mid.pc
        = some (Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (Place.deref P)) csPrefix).nextReg)
            (Rhs.Borrow kind prot mask (blockSize τ) dOut.result.reg 0)) := by
      rw [h_dpc]
      refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
      · rw [h_stmtRun]
        simp only [emit, List.length_cons, List.length_nil]
        omega
      · rw [h_stmtRun]
        rw [emit_code_lt_nextLabel _ _ (by
          simp only [emit, List.length_cons, List.length_nil]; omega)]
        have h := emit_code_at_new
          { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (Place.deref P)) csPrefix) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (Place.deref P)) csPrefix).nextReg + 1 }
          [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (Place.deref P)) csPrefix).nextReg)
            (Rhs.Borrow kind prot mask (blockSize τ) dOut.result.reg 0)]
          (k := 0) (by simp)
        simpa using h
    have h_le1 : resolved.allocBase + (resolved.addr - resolved.allocBase) + 0
        + blockSize τ ≤ resolved.allocBase + resolved.allocSize := by
      grind
    have h_ref_tgt' : MSB.ref s_mid.perms
        (resolved.allocBase + (resolved.addr - resolved.allocBase) + 0)
        (blockSize τ) tres kind prot mask
        = .ok (tgtPerms, s_mid.perms.NextTag) := by
      rw [Nat.add_zero, h_cancel]
      exact h_ref_tgt
    have h_run1 := runN_Assgn_Borrow_step compProg s_mid
      (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (Place.deref P)) csPrefix).nextReg)
      dOut.result.reg kind prot mask (blockSize τ) 0
      h_code1 h_dentry h_le1 h_ref_tgt'
    -- §6 the pointer store via BRIDGE 2 into the dst binding
    obtain ⟨dstReg2, baseD2, tagD2, h_piD2, h_entryD2, h_raD2, h_rtD2, h_nwD2, -⟩ :=
      h_dlbs dstLoc bD h_envD
    have h_dr2 : dstReg2 = dstReg := by grind
    have h_baseD2 : baseD2 = bD.addr := (h_id_a _ _ h_raD2).symm
    rw [h_dr2, h_baseD2] at h_entryD2
    rw [h_baseD2] at h_raD2
    have h_regne : dstReg ≠ Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (Place.deref P)) csPrefix).nextReg := by
      cases dstReg with
      | R n =>
          have h_lt := h_prb _ _ _ h_piD
          grind [RegisterBelow]
    have h_code2 : compProg (s_mid.pc + 1)
        = some (Instr.RStore obseq.TyVal.PTy
            (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (Place.deref P)) csPrefix).nextReg) dstReg) := by
      refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
      · rw [h_stmtRun, h_dpc]
        simp only [emit, List.length_cons, List.length_nil]
        omega
      · rw [h_stmtRun, h_dpc]
        have h := emit_code_at_new
          (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (Place.deref P)) csPrefix) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (Place.deref P)) csPrefix).nextReg + 1 }
            [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (Place.deref P)) csPrefix).nextReg)
              (Rhs.Borrow kind prot mask (blockSize τ) dOut.result.reg 0)])
          [Instr.RStore obseq.TyVal.PTy (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (Place.deref P)) csPrefix).nextReg) dstReg]
          (k := 0) (by simp)
        simpa [emit] using h
    have h_w := h_step
    simp only [mirlite.writeResolvedPlace] at h_w
    split at h_w
    · simp at h_w
    · rename_i h_nb
      split at h_w
      · rename_i perms2 h_useMut_src
        cases h_w
        obtain ⟨p3, h_useMut_tgt, h_psim3⟩ :=
          sb_write_respects_PermSim h_psim' h_wf_t'
            (h_incr_t _ _ h_rtD2) h_nwD2 h_useMut_src
        have h_entryD1 : PtrRegisterEntry
            (oseair.RegMap.insert s_mid.reg
              (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (Place.deref P)) csPrefix).nextReg)
              (obseq.TyVal.PTy, [Val.Ptr resolved.allocBase
                (resolved.addr - resolved.allocBase + 0) resolved.allocSize
                s_mid.perms.NextTag]))
            dstReg bD.addr (bD.addr - bD.addr) (blockSize (obseq.LayoutTy.PtrL τ))
            tagD2 := by
          rw [Nat.sub_self]
          show oseair.RegMap.lookup _ _ = _
          rw [RegMap.lookup_insert_ne _ h_regne]
          exact h_entryD2
        obtain ⟨h_wtp, h_sms'⟩ :=
          writeThroughPtr_sim (τ := obseq.LayoutTy.PtrL τ)
            (s_osea :=
              { s_mid with
                  perms := tgtPerms,
                  reg := oseair.RegMap.insert s_mid.reg
                    (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (Place.deref P)) csPrefix).nextReg)
                    (obseq.TyVal.PTy, [Val.Ptr resolved.allocBase
                      (resolved.addr - resolved.allocBase + 0) resolved.allocSize
                      s_mid.perms.NextTag]),
                  pc := s_mid.pc + 1 })
            (resolved := { addr := bD.addr, tag := bD.tag, allocBase := bD.addr,
                           allocSize := blockSize (obseq.LayoutTy.PtrL τ) })
            "RStore Invalid Regs"
            [mirlite.MemValue.ptrVal resolved.allocBase
              (resolved.addr - resolved.allocBase) resolved.allocSize
              permsR.NextTag]
            [Val.Ptr resolved.allocBase (resolved.addr - resolved.allocBase + 0)
              resolved.allocSize s_mid.perms.NextTag] rfl
            ⟨⟨h_dbase, by simp, rfl, h_rt_new, h_nw_new,
              fun k hk => h_drange k hk⟩, trivial⟩
            h_id_a h_entryD1 h_useMut_tgt
            (by
              show SourceMemSim ρa (ρt.extend permsR.NextTag s_mid.perms.NextTag)
                s_mir.mem _
              rw [h_dmem]
              exact SourceMemSim.rename_mono (AddrRenameIncr.refl ρa) h_incr_t h_sms)
            (Nat.le_refl _)
            (fun k hk => by
              have hk0 : k = 0 := by simpa using hk
              subst hk0
              rw [Nat.add_zero]
              exact h_raD2)
            h_step
        have h_run2 := runN_RStore_step compProg _ _ obseq.TyVal.PTy
          (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (Place.deref P)) csPrefix).nextReg)
          dstReg _ _ h_code2
          (RegMap.lookup_insert_self _ _ _)
          (by rw [RegMap.lookup_insert_ne _ h_regne]; exact h_entryD2)
          h_wtp
        have h_runA := (oseair_runN_add n1 1 s_osea compProg s_mid h_drun).trans h_run1
        have h_runB := (oseair_runN_add (n1 + 1) 1 s_osea compProg _ h_runA).trans h_run2
        -- §7 rebuild the invariant under the extended ρt
        refine ⟨_, _, n1 + 1 + 1, h_incr_t, h_runB, ?_⟩
        refine ⟨CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix,
          ⟨prefixCompileState_succ h_csAt h_stmt h_stmtOut, ?_⟩, ?_, h_sms', h_psim3,
          h_id_a, h_wf_t', ?_, ?_, ?_, ?_⟩
        · show s_mid.pc + 1 + 1 = _
          rw [h_dpc, h_stmtRun]
          simp [emit]
        · have h_dlbs' : LocalBindingSim ρa
              (ρt.extend permsR.NextTag s_mid.perms.NextTag)
              s_mir.env s_mid csPrefix :=
            LocalBindingSim.rename_mono (AddrRenameIncr.refl ρa) h_incr_t h_dlbs
          have h_lbs2 : LocalBindingSim ρa
              (ρt.extend permsR.NextTag s_mid.perms.NextTag)
              s_mir.env
              { s_mid with
                  perms := tgtPerms,
                  reg := oseair.RegMap.insert s_mid.reg
                    (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (Place.deref P)) csPrefix).nextReg)
                    (obseq.TyVal.PTy, [Val.Ptr resolved.allocBase
                      (resolved.addr - resolved.allocBase + 0) resolved.allocSize
                      s_mid.perms.NextTag]),
                  pc := s_mid.pc + 1 }
              csPrefix :=
            LocalBindingSim.insert_fresh_reg h_dlbs' h_prb h_dregmono rfl
          intro τ'' loc' binding' h_env'
          obtain ⟨reg', base', tag', h_pi', h_entry', h_ra'', h_rt', h_nw', h_dom'⟩ :=
            h_lbs2 loc' binding' h_env'
          refine ⟨reg', base', tag', ?_, h_entry', h_ra'', h_rt', h_nw', h_dom'⟩
          rw [h_stmtRun, getPlaceInfo_emit, getPlaceInfo_emit, getPlaceInfo_setNextReg]
          show (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (Place.deref P)) csPrefix).placeRegMap.lookup loc'.idx.1 = _
          rw [h_dprm]
          exact h_pi'
        · show TagRenameBounded _ perms2.NextTag p3.NextTag
          rw [sb_write_NextTag h_useMut_src, sb_write_NextTag h_useMut_tgt]
          exact h_tbd'
        · simp only [AllocLockstep, mirlite_writeWordSeq_addrStart,
            oseair_writeWordSeq_addrStart, h_dmem]
          exact h_alloc
        · intro τ'' loc' h_none
          rw [h_stmtRun, getPlaceInfo_emit, getPlaceInfo_emit, getPlaceInfo_setNextReg]
          show (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (Place.deref P)) csPrefix).placeRegMap.lookup loc'.idx.1 = none
          rw [h_dprm]
          exact h_unmap loc' h_none
        · intro idx reg'' τ'' h_look
          rw [h_stmtRun] at h_look ⊢
          rw [getPlaceInfo_emit, getPlaceInfo_emit, getPlaceInfo_setNextReg] at h_look
          have h_prm2 : (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (Place.deref P)) csPrefix).placeRegMap = csPrefix.placeRegMap := h_dprm
          have h_cs : getPlaceInfo csPrefix idx = some (reg'', τ'') := by
            show csPrefix.placeRegMap.lookup idx = _
            rw [← h_prm2]
            exact h_look
          refine RegisterBelow.mono ?_ (h_prb _ _ _ h_cs)
          simp only [emit]
          exact Nat.le_trans h_dregmono (Nat.le_succ _)
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

/-- The fragment of `dst.g := &kind s` at ZERO offset when the
    DESTINATION ROOT IS UNBOUND: `ensurePlaceRoot` allocates the
    σ-sized root, the rhs borrows, and the store goes through the root
    register directly (offset zero needs no interior borrow). Three
    instructions, the fresh L→L shape with a σ-sized `Alloc`. -/
theorem compileStmt_ref_projzero_fresh_run
    {Γ : Ctx} {τ σ : LayoutTy}
    {dstLoc : Local Γ σ} {g : PathTo σ (obseq.LayoutTy.PtrL τ)}
    {srcLoc : Local Γ τ}
    {cs : CompilerState} {srcReg : Register}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (h_g0 : pathOffset g = 0)
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = none)
    (h_src : getPlaceInfo cs srcLoc.idx.1 = some (srcReg, τ)) :
    CheckedCompilerM.run
        (compileStmtChecked
          (Stmt.assign (.proj (.local dstLoc) g)
            (.ref kind prot mask (.local srcLoc)))) cs
      = emit (emit
          { (setPlaceInfo
              (emit { cs with nextReg := cs.nextReg + 1 }
                [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
              dstLoc.idx.1 (Register.R cs.nextReg, σ)) with
              nextReg := cs.nextReg + 1 + 1 }
          [Instr.Assgn (Register.R (cs.nextReg + 1))
            (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)])
          [Instr.RStore obseq.TyVal.PTy (Register.R (cs.nextReg + 1))
            (Register.R cs.nextReg)] := by
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
  simp only [compileStmtChecked, compileRExprPreChecked,
    placeToBorrowRegChecked, h_proj_eq,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
    h_root, h_prun, h_pval, h_g0, dif_pos]
  simp [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM,
    cleanupInstrs, h_pres, emit_nil]
  csnorm at h_bval h_brun h_bres ⊢
  simp only [h_bval, h_brun, h_bres]
  simp [emit_nil]

/-- The zero-offset fresh-root field-dst ref lowers. -/
theorem compileStmt_ref_projzero_fresh_value
    {Γ : Ctx} {τ σ : LayoutTy}
    {dstLoc : Local Γ σ} {g : PathTo σ (obseq.LayoutTy.PtrL τ)}
    {srcLoc : Local Γ τ}
    {cs : CompilerState} {srcReg : Register}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (h_g0 : pathOffset g = 0)
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = none)
    (h_src : getPlaceInfo cs srcLoc.idx.1 = some (srcReg, τ)) :
    ∃ so, CheckedCompilerM.value
      (compileStmtChecked
        (Stmt.assign (.proj (.local dstLoc) g)
          (.ref kind prot mask (.local srcLoc)))) cs
      = Except.ok so := by
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
  simp only [compileStmtChecked, compileRExprPreChecked,
    placeToBorrowRegChecked, h_proj_eq,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
    h_root, h_prun, h_pval, h_g0, dif_pos]
  simp only [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM]
  simp only [h_pres]
  csnorm at h_bval ⊢
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

/-- The fragment of `dst.g := &kind s` at NONZERO offset when the
    DESTINATION ROOT IS UNBOUND: the σ-sized `Alloc`, the rhs `Borrow`,
    then the projection's own interior `Borrow(Mut)` into the fresh
    root register, the `RStore` through it, and its cleanup `Die` —
    five instructions, the fresh shape with BRIDGE 1 on top. -/
theorem compileStmt_ref_projoffset_fresh_run
    {Γ : Ctx} {τ σ : LayoutTy}
    {dstLoc : Local Γ σ} {g : PathTo σ (obseq.LayoutTy.PtrL τ)}
    {srcLoc : Local Γ τ}
    {cs : CompilerState} {srcReg : Register}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (h_go : pathOffset g ≠ 0)
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = none)
    (h_src : getPlaceInfo cs srcLoc.idx.1 = some (srcReg, τ)) :
    CheckedCompilerM.run
        (compileStmtChecked
          (Stmt.assign (.proj (.local dstLoc) g)
            (.ref kind prot mask (.local srcLoc)))) cs
      = emit (emit (emit
          { (emit
              { (setPlaceInfo
                  (emit { cs with nextReg := cs.nextReg + 1 }
                    [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
                  dstLoc.idx.1 (Register.R cs.nextReg, σ)) with
                  nextReg := cs.nextReg + 1 + 1 }
              [Instr.Assgn (Register.R (cs.nextReg + 1))
                (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)]) with
              nextReg := cs.nextReg + 1 + 1 + 1 }
          [Instr.Assgn (Register.R (cs.nextReg + 1 + 1))
            (Rhs.Borrow RefKind.Mut false [] (blockSize (obseq.LayoutTy.PtrL τ))
              (Register.R cs.nextReg) (pathOffset g))])
          [Instr.RStore obseq.TyVal.PTy (Register.R (cs.nextReg + 1))
            (Register.R (cs.nextReg + 1 + 1))])
          [Instr.Die (Register.R (cs.nextReg + 1 + 1))
            (blockSize (obseq.LayoutTy.PtrL τ))] := by
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
  simp only [compileStmtChecked, compileRExprPreChecked,
    placeToBorrowRegChecked, h_proj_eq,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
    h_root, h_prun, h_pval, h_go, dif_neg]
  simp [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM,
    cleanupInstrs, h_pres, emit_nil]
  csnorm at h_bval h_brun h_bres ⊢
  simp only [h_pres, h_bval, h_brun, h_bres]
  simp [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM,
    cleanupInstrs, emit_nil, borrowRhs]
  rfl

/-- The nonzero-offset fresh-root field-dst ref lowers. -/
theorem compileStmt_ref_projoffset_fresh_value
    {Γ : Ctx} {τ σ : LayoutTy}
    {dstLoc : Local Γ σ} {g : PathTo σ (obseq.LayoutTy.PtrL τ)}
    {srcLoc : Local Γ τ}
    {cs : CompilerState} {srcReg : Register}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (h_go : pathOffset g ≠ 0)
    (h_dst : getPlaceInfo cs dstLoc.idx.1 = none)
    (h_src : getPlaceInfo cs srcLoc.idx.1 = some (srcReg, τ)) :
    ∃ so, CheckedCompilerM.value
      (compileStmtChecked
        (Stmt.assign (.proj (.local dstLoc) g)
          (.ref kind prot mask (.local srcLoc)))) cs
      = Except.ok so := by
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
  simp only [compileStmtChecked, compileRExprPreChecked,
    placeToBorrowRegChecked, h_proj_eq,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
    h_root, h_prun, h_pval, h_go, dif_neg]
  simp only [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM]
  simp only [h_pres]
  csnorm at h_bval ⊢
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
  simp [compileStmtChecked, compileRExprPreChecked, placeToBorrowRegChecked,
    h_root, h_prun, h_pval0, h_pres, h_dval]
  simp [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM,
    cleanupInstrs, h_dval, h_dclean, emit_nil]

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
  simp only [compileStmtChecked, compileRExprPreChecked, placeToBorrowRegChecked,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
    h_root, h_prun, h_pval0, h_pres]
  simp only [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM]
  simp only [CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure, h_dval]
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
  simp only [compileStmtChecked,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure, h_er]
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
  simp only [compileStmtChecked,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure, h_er] at h_so ⊢
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
  simp [compileStmtChecked, compileRExprPreChecked, placeToBorrowRegChecked,
    h_root, h_prun, h_pval0, h_pres, h_dval]
  simp [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM,
    cleanupInstrs, h_dval, h_dclean, emit_nil]

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
  simp only [compileStmtChecked, compileRExprPreChecked, placeToBorrowRegChecked,
    CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
    h_root, h_prun, h_pval0, h_pres]
  simp only [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM]
  simp only [CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure, h_dval]
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
  -- §4 the retag transported: the fresh pair extends ρt
  obtain ⟨tgtP1, h_ref_tgt, h_mint_eq, h_incr_t, h_wf_t', h_tbd', h_psim'⟩ :=
    sb_ref_respects_PermSim h_psim h_wf_t h_tbd h_rtS h_nwS h_ref_src
  subst h_mint_eq
  have h_rt_new : (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag)
      s_mir.perms.NextTag = some s_osea.perms.NextTag :=
    TagRenameMap.extend_self _ _ _
  have h0 : wildcardTag < s_mir.perms.NextTag := (h_tbd _ _ h_wf_t.2).1
  have h_nw_new : (s_mir.perms.NextTag == wildcardTag) = false := by grind
  -- §5 compiler-side scaffolding: the post-Borrow LocalBindingSim feeds
  -- both the mapped-ness of the dst at cs1 and the mother lemma
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
  obtain ⟨dOut0, h_dval0⟩ := placeToRegChecked_ok_of_placeInputsMapped
    (cs := emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
      [Instr.Assgn (Register.R csPrefix.nextReg)
        (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)])
    (kind := RefKind.Mut)
    (placeInputsMapped_of_localBindingSim_resolvePlace
      (s_mir := { s_mir with perms := perms1 }) h_lbs1
      (resolvePlace?_of_resolveAcc h_dres))
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
    simp only [compileStmtChecked, compileRExprPreChecked, placeToBorrowRegChecked,
      CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
      CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
      CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
      h_root, h_lprun, h_lpval, h_lpres]
    simp only [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM]
    simp only [CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
      CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
      CheckedCompilerM.run_pure, CheckedCompilerM.value_pure, h_dval0]
    exact StateIncr.trans (emit_state_incr _ _)
      (StateIncr.trans (emit_state_incr _ _) (emit_state_incr _ _))
  have h_instD : ∀ q' instr,
      q' < (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (Place.deref P))
      (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
        [Instr.Assgn (Register.R csPrefix.nextReg)
          (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)])).nextLabel →
      (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (Place.deref P))
      (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
        [Instr.Assgn (Register.R csPrefix.nextReg)
          (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)])).code q' = some instr →
      compProg q' = some instr := by
    intro q' instr h_lt h_code
    refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
    · exact Nat.lt_of_lt_of_le h_lt h_incr2.nextLabel_le
    · rw [h_incr2.code_eq q' h_lt]
      exact h_code
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
  have h_le1 : bS.addr + 0 + 0 + blockSize τ ≤ bS.addr + blockSize τ := by grind
  have h_ref_tgt' : MSB.ref s_osea.perms (bS.addr + 0 + 0) (blockSize τ) tagS
      kind prot mask = .ok (tgtP1, s_osea.perms.NextTag) := by
    simpa using h_ref_tgt
  have h_run1 := runN_Assgn_Borrow_step compProg s_osea
    (Register.R csPrefix.nextReg) srcReg kind prot mask (blockSize τ) 0
    h_code1 h_entryS h_le1 h_ref_tgt'
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
  have h_pc1 : s_osea.pc + 1
      = (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
          [Instr.Assgn (Register.R csPrefix.nextReg)
            (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)]).nextLabel := by
    simp only [emit, List.length_cons, List.length_nil]
    omega
  obtain ⟨dOut, n1, s_mid, tres, h_dval, h_dclean, h_drun, h_dpc, h_dmem, h_dpsim,
    h_dnt1, h_dnt2, h_dlbs, h_dentry, h_drt, h_dnw, h_dle, h_drange, h_dbelow,
    h_dprm, h_dregmono, h_dlabmono, h_dframe, -⟩ :=
    ptrChain_lowering_sim h_id_a h_wf_t' h_spine RefKind.Mut
      (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
        [Instr.Assgn (Register.R csPrefix.nextReg)
          (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)])
      { s_osea with
          perms := tgtP1,
          reg := oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
            (obseq.TyVal.PTy,
              [Val.Ptr bS.addr (0 + 0) (blockSize τ) s_osea.perms.NextTag]),
          pc := s_osea.pc + 1 }
      resolved permsD h_dres h_tbd' h_lbs1 h_prb1 h_sms1 h_psim' h_pc1 h_instD
  have h_stmtRun := (h_run0 csPrefix).trans
    (compileStmt_ref_derefdst_run kind prot mask h_root h_piS rfl h_dval h_dclean)
  -- the borrow temp crosses the dst lowering (register frame)
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
    rw [h_dframe _ h_below1]
    exact RegMap.lookup_insert_self _ _ _
  -- §8 the store through the loaded tag (BRIDGE 2)
  have h_code3 : compProg s_mid.pc
      = some (Instr.RStore obseq.TyVal.PTy (Register.R csPrefix.nextReg)
          dOut.result.reg) := by
    rw [h_dpc]
    refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
    · rw [h_stmtRun]
      show _ < _ + 1
      exact Nat.lt_succ_self _
    · rw [h_stmtRun]
      have h := emit_code_at_new (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (Place.deref P))
      (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
        [Instr.Assgn (Register.R csPrefix.nextReg)
          (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)]))
        [Instr.RStore obseq.TyVal.PTy (Register.R csPrefix.nextReg) dOut.result.reg]
        (k := 0) (by simp)
      simpa using h
  have h_w := h_step
  simp only [mirlite.writeResolvedPlace] at h_w
  split at h_w
  · simp at h_w
  · rename_i h_nb
    split at h_w
    · rename_i perms2 h_useMut_src
      cases h_w
      obtain ⟨p3, h_useMut_tgt, h_psim3⟩ :=
        sb_write_respects_PermSim h_dpsim h_wf_t' h_drt h_dnw h_useMut_src
      obtain ⟨h_wtp, h_sms'⟩ :=
        writeThroughPtr_sim (τ := obseq.LayoutTy.PtrL τ)
          (s_osea := s_mid) (resolved := resolved)
          "RStore Invalid Regs"
          [mirlite.MemValue.ptrVal bS.addr (bS.addr - bS.addr) (blockSize τ)
            s_mir.perms.NextTag]
          [Val.Ptr bS.addr (0 + 0) (blockSize τ) s_osea.perms.NextTag] rfl
          ⟨⟨h_raS, by simp, rfl, h_rt_new, h_nw_new,
            fun k hk => h_domS k hk⟩, trivial⟩
          h_id_a h_dentry h_useMut_tgt
          (by
            show SourceMemSim ρa
              (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag)
              s_mir.mem s_mid.mem
            rw [h_dmem]
            exact h_sms1)
          h_dle
          (fun k hk => by
            have hk0 : k = 0 := by simpa using hk
            subst hk0
            have h_lt : resolved.addr - resolved.allocBase < resolved.allocSize := by
              grind
            obtain ⟨a', ha'⟩ := h_drange _ h_lt
            have h_eq := h_id_a _ _ ha'
            have h_cancel : resolved.allocBase + (resolved.addr - resolved.allocBase)
                = resolved.addr := Nat.add_sub_cancel' h_dle
            grind)
          h_step
      have h_run3 := runN_RStore_step compProg s_mid _
        obseq.TyVal.PTy (Register.R csPrefix.nextReg) dOut.result.reg
        _ _ h_code3 h_borrow_mid h_dentry h_wtp
      have h_runA := (oseair_runN_add 1 n1 s_osea compProg _ h_run1).trans h_drun
      have h_runB := (oseair_runN_add (1 + n1) 1 s_osea compProg _ h_runA).trans h_run3
      -- §9 rebuild the invariant under the extended ρt
      refine ⟨_, _, 1 + n1 + 1, h_incr_t, h_runB, ?_⟩
      refine ⟨CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix,
        ⟨prefixCompileState_succ h_csAt h_stmt h_stmtOut, ?_⟩, ?_, h_sms', h_psim3,
        h_id_a, h_wf_t', ?_, ?_, ?_, ?_⟩
      · show s_mid.pc + 1 = _
        rw [h_dpc, h_stmtRun]
        simp [emit]
      · intro τ'' loc' binding' h_env'
        obtain ⟨reg', base', tag', h_pi', h_entry', h_ra'', h_rt', h_nw', h_dom'⟩ :=
          h_dlbs loc' binding' h_env'
        refine ⟨reg', base', tag', ?_, h_entry', h_ra'', h_rt', h_nw', h_dom'⟩
        rw [h_stmtRun, getPlaceInfo_emit]
        show (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (Place.deref P))
      (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
        [Instr.Assgn (Register.R csPrefix.nextReg)
          (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)])).placeRegMap.lookup loc'.idx.1 = _
        rw [h_dprm]
        exact h_pi'
      · show TagRenameBounded _ perms2.NextTag p3.NextTag
        rw [sb_write_NextTag h_useMut_src, h_dnt1,
          sb_write_NextTag h_useMut_tgt]
        exact TagRenameBounded.mono h_tbd' (Nat.le_refl _) h_dnt2
      · simp only [AllocLockstep, mirlite_writeWordSeq_addrStart,
          oseair_writeWordSeq_addrStart, h_dmem]
        exact h_alloc
      · intro τ'' loc' h_none
        rw [h_stmtRun, getPlaceInfo_emit]
        show (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (Place.deref P))
      (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
        [Instr.Assgn (Register.R csPrefix.nextReg)
          (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)])).placeRegMap.lookup loc'.idx.1 = none
        rw [h_dprm]
        exact h_unmap loc' h_none
      · intro idx reg'' τ'' h_look
        rw [h_stmtRun] at h_look ⊢
        rw [getPlaceInfo_emit] at h_look
        have h_prm2 : (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (Place.deref P))
      (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
        [Instr.Assgn (Register.R csPrefix.nextReg)
          (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)])).placeRegMap = csPrefix.placeRegMap := h_dprm
        have h_cs : getPlaceInfo csPrefix idx = some (reg'', τ'') := by
          show csPrefix.placeRegMap.lookup idx = _
          rw [← h_prm2]
          exact h_look
        refine RegisterBelow.mono ?_ (h_prb _ _ _ h_cs)
        simp only [emit]
        have h_le := h_dregmono
        simp only [emit] at h_le
        omega
    · simp at h_w

/-- REGIME B-proj of ref: `dst := &kind s.f` with the DESTINATION ROOT
    UNBOUND. `preparePlaceAssign` allocates the destination on the
    mirlite side and `ensureLocalRegE` emits the matching `Alloc`, in
    lockstep; the source is a projected field of a bound local, which —
    as everywhere in `ref` — costs only the `Borrow`'s offset operand.
    Three instructions: `Alloc; Borrow; RStore`. -/
theorem ref_fresh_projsrc_simulation
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {τ σb : LayoutTy}
    {dstLoc : Local Γ (obseq.LayoutTy.PtrL τ)} {srcLoc : Local Γ σb}
    {f : PathTo σb τ}
    {bS : mirlite.Binding}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (compProg : oseair.Prog)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    (h_stmt : prog.get? s_mir.pc
      = some (.assign (.local dstLoc) (.ref kind prot mask (.proj (.local srcLoc) f))))
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
          simp only [mirlite.resolvePlaceAcc, mirlite.evalRExpr, hS1] at h_step
          rw [if_neg (Nat.not_lt.mpr (show bS.addr + pathOffset f + blockSize τ
              ≤ bS.addr + blockSize σb by
            have h_fit := PathTo.offset_add_size_le f
            simp only [Nat.add_assoc]
            exact Nat.add_le_add_left h_fit _))] at h_step
          -- §3 the retag on the source place
          cases h_ref_src : MSB.ref permsOwned (bS.addr + pathOffset f) (blockSize τ)
              bS.tag kind prot mask with
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
              have h_stmtRun := compileStmt_ref_fresh_projsrc_run (cs := csPrefix) (f := f)
                kind prot mask h_piD h_piS
              obtain ⟨stmtOut, h_stmtOut⟩ :=
                compileStmt_ref_fresh_projsrc_value (cs := csPrefix) (f := f)
                  kind prot mask h_piD h_piS
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
                      (Rhs.Borrow kind prot mask (blockSize τ) srcReg (pathOffset f))) := by
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
                      (Rhs.Borrow kind prot mask (blockSize τ) srcReg (pathOffset f))] (k := 0) (by simp)
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
                        (Rhs.Borrow kind prot mask (blockSize τ) srcReg (pathOffset f))])
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
                  srcReg bS.addr 0 (blockSize σb) tagS := by
                show oseair.RegMap.lookup _ _ = _
                rw [RegMap.lookup_insert_ne _ h_regne]
                exact h_entryS
              have h_ref_tgt' : MSB.ref tgtP1 (bS.addr + 0 + pathOffset f) (blockSize τ)
                  tagS kind prot mask = .ok (tgtP2, tgtP1.NextTag) := by simpa using h_ref_tgt
              have h_le2 : bS.addr + 0 + pathOffset f + blockSize τ
                  ≤ bS.addr + blockSize σb := by
                have h_fit := PathTo.offset_add_size_le f
                simp only [Nat.add_zero, Nat.add_assoc]
                exact Nat.add_le_add_left h_fit _
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
                (Register.R (csPrefix.nextReg + 1)) srcReg kind prot mask (blockSize τ)
                (pathOffset f) h_code2 h_entryS1 h_le2 h_ref_tgt'
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
                        (obseq.TyVal.PTy, [Val.Ptr bS.addr (0 + pathOffset f) (blockSize σb)
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
                              (obseq.TyVal.PTy, [Val.Ptr bS.addr (0 + pathOffset f) (blockSize σb)
                                tgtP1.NextTag]),
                            pc := s_osea.pc + 1 + 1 })
                      (resolved := { addr := s_mir.mem.addrStart, tag := s_mir.perms.NextTag,
                                     allocBase := s_mir.mem.addrStart,
                                     allocSize := blockSize (obseq.LayoutTy.PtrL τ) })
                      "RStore Invalid Regs"
                      [mirlite.MemValue.ptrVal bS.addr (bS.addr + pathOffset f - bS.addr)
                        (blockSize σb) permsOwned.NextTag]
                      [Val.Ptr bS.addr (0 + pathOffset f) (blockSize σb) tgtP1.NextTag] rfl
                      ⟨⟨h_raS', by simp [Nat.add_sub_cancel_left], rfl, h_rt_new, h_nwR,
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
                        (.ref kind prot mask (.proj (.local srcLoc) f)))) csPrefix,
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


/-- REGIME B-proj for the DESTINATION: `dst.g := &kind s` at ZERO
    field offset with `dst`'s root UNBOUND. `preparePlaceAssign` runs
    `allocateRoot` for the whole σ-sized root and `ensurePlaceRoot`
    emits the matching σ-sized `Alloc`; ρa extends by the IDENTITY over
    that whole block (`extendBlock`), not at a single cell as in the
    pointer-local case. At offset zero the store goes through the root
    register, so the fragment is still `Alloc; Borrow; RStore`. -/
theorem ref_projzero_fresh_simulation
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {τ σ : LayoutTy}
    {dstLoc : Local Γ σ} {g : PathTo σ (obseq.LayoutTy.PtrL τ)}
    {srcLoc : Local Γ τ}
    {bS : mirlite.Binding}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (h_g0 : pathOffset g = 0)
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
  -- §1 the destination allocation
  simp only [mirlite.stepStmt, mirlite.doAssign] at h_step
  cases h_prep : mirlite.preparePlaceAssign MSB s_mir (Place.proj (Place.local dstLoc) g) with
  | err m => rw [h_prep] at h_step; simp at h_step
  | ok s1 =>
      rw [h_prep] at h_step
      -- invert prepare: the destination was unbound, so `allocateBase` ran
      have h_prep' := h_prep
      simp only [mirlite.preparePlaceAssign, mirlite.resolvePlace?, h_envD,
        mirlite.allocateRoot, mirlite.allocateBase, mirlite.allocate] at h_prep'
      cases h_own_src : MSB.own s_mir.perms s_mir.mem.addrStart
          (blockSize (σ)) with
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
            mirlite.evalRExpr, hS1, h_g0, Nat.add_zero] at h_step
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
              have h_szD : obseq.typeSize (layoutToTyVal (σ))
                  = blockSize (σ) := obseq.typeSize_layoutToTyVal _
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
                  (ρa.extendBlock s_mir.mem.addrStart (blockSize σ)) :=
                AddrRenameIncr.extendBlock h_id_a _ _
              have h_id_a' : IdentityOnDomain
                  (ρa.extendBlock s_mir.mem.addrStart (blockSize σ)) :=
                IdentityOnDomain.extendBlock h_id_a _ _
              have h_ra_new : (ρa.extendBlock s_mir.mem.addrStart (blockSize σ))
                  s_mir.mem.addrStart = some s_mir.mem.addrStart :=
                AddrRenameMap.extendBlock_base _ _ _
              have h_ra_dom : ∀ k, k < blockSize σ →
                  (ρa.extendBlock s_mir.mem.addrStart (blockSize σ))
                    (s_mir.mem.addrStart + k) = some (s_mir.mem.addrStart + k) :=
                fun _ hk => AddrRenameMap.extendBlock_mem hk
              have h_raS' := h_incr_a _ _ h_raS
              -- §7 the fragment: Alloc; Borrow; RStore
              have h_stmtRun := (h_run0 csPrefix).trans
                (compileStmt_ref_projzero_fresh_run (cs := csPrefix)
                  kind prot mask h_g0 h_piD h_piS)
              obtain ⟨stmtOutC, h_stmtOutC⟩ :=
                compileStmt_ref_projzero_fresh_value (cs := csPrefix) kind prot mask
                  h_g0 h_piD h_piS
              obtain ⟨stmtOut, h_stmtOut⟩ := h_val0 csPrefix stmtOutC h_stmtOutC
              have h_code1 : compProg s_osea.pc
                  = some (Instr.Assgn (Register.R csPrefix.nextReg)
                      (Rhs.Alloc (layoutToTyVal (σ)))) := by
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
                      (Rhs.Alloc (layoutToTyVal (σ)))] (k := 0) (by simp)
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
                            (Rhs.Alloc (layoutToTyVal (σ)))])
                        dstLoc.idx.1 (Register.R csPrefix.nextReg, σ)) with
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
                            (Rhs.Alloc (layoutToTyVal (σ)))])
                        dstLoc.idx.1 (Register.R csPrefix.nextReg, σ)) with
                        nextReg := csPrefix.nextReg + 1 + 1 }
                      [Instr.Assgn (Register.R (csPrefix.nextReg + 1))
                        (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)])
                    [Instr.RStore obseq.TyVal.PTy (Register.R (csPrefix.nextReg + 1))
                      (Register.R csPrefix.nextReg)] (k := 0) (by simp)
                  simpa [emit, setPlaceInfo] using h
              -- §8 execute Alloc, then Borrow
              have h_own_tgt' : MSB.own s_osea.perms s_osea.mem.addrStart
                  (obseq.typeSize (layoutToTyVal (σ)))
                  = .ok (tgtP1, s_osea.perms.NextTag) := by
                rw [h_szD, h_addr_eq]; exact h_own_tgt
              have h_run1 := runN_Assgn_Alloc_step compProg s_osea
                (Register.R csPrefix.nextReg) (layoutToTyVal (σ))
                h_code1 h_own_tgt'
              have h_regne : srcReg ≠ Register.R csPrefix.nextReg := by
                cases srcReg with
                | R n => have h_lt := h_prb _ _ _ h_piS; grind [RegisterBelow]
              have h_entryS1 : PtrRegisterEntry
                  (oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
                    (obseq.TyVal.PTy, [Val.Ptr s_osea.mem.addrStart 0
                      (obseq.typeSize (layoutToTyVal (σ)))
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
                      (obseq.typeSize (layoutToTyVal (σ)))).2,
                    perms := tgtP1,
                    reg := oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
                      (obseq.TyVal.PTy, [Val.Ptr s_osea.mem.addrStart 0
                        (obseq.typeSize (layoutToTyVal (σ)))
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
                            (obseq.typeSize (layoutToTyVal (σ)))
                            s_osea.perms.NextTag]))
                        (Register.R (csPrefix.nextReg + 1))
                        (obseq.TyVal.PTy, [Val.Ptr bS.addr (0 + 0) (blockSize τ)
                          tgtP1.NextTag]))
                      (Register.R csPrefix.nextReg) s_mir.mem.addrStart
                      (s_mir.mem.addrStart - s_mir.mem.addrStart)
                      (blockSize (σ)) s_osea.perms.NextTag := by
                    rw [Nat.sub_self, ← h_addr_eq, ← h_szD]
                    show oseair.RegMap.lookup _ _ = _
                    rw [RegMap.lookup_insert_ne _ h_regne2]
                    exact RegMap.lookup_insert_self _ _ _
                  obtain ⟨h_wtp, h_sms'⟩ :=
                    writeThroughPtr_sim (τ := obseq.LayoutTy.PtrL τ)
                      (s_osea :=
                        { s_osea with
                            mem := (oseair.allocate s_osea.mem
                              (obseq.typeSize (layoutToTyVal (σ)))).2,
                            perms := tgtP2,
                            reg := oseair.RegMap.insert
                              (oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
                                (obseq.TyVal.PTy, [Val.Ptr s_osea.mem.addrStart 0
                                  (obseq.typeSize (layoutToTyVal (σ)))
                                  s_osea.perms.NextTag]))
                              (Register.R (csPrefix.nextReg + 1))
                              (obseq.TyVal.PTy, [Val.Ptr bS.addr (0 + 0) (blockSize τ)
                                tgtP1.NextTag]),
                            pc := s_osea.pc + 1 + 1 })
                      (resolved := { addr := s_mir.mem.addrStart, tag := s_mir.perms.NextTag,
                                     allocBase := s_mir.mem.addrStart,
                                     allocSize := blockSize (σ) })
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
                  refine ⟨CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix,
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
                    · have h_ty : τ' = σ := by
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
                        exact ⟨s_mir.mem.addrStart + k, h_ra_dom k hk⟩
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


/-- REGIME B-proj for the DESTINATION at NONZERO offset:
    `dst.g := &kind s` with `dst`'s root UNBOUND and the field away from
    the base. The σ-sized root allocation of the zero-offset leaf, plus
    the projection's own interior `Borrow(Mut)` into the fresh root
    register and its cleanup `Die` — BRIDGE 1 collapses that triple to
    mirlite's single parent write. Five instructions. -/
theorem ref_projoffset_fresh_simulation
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {τ σ : LayoutTy}
    {dstLoc : Local Γ σ} {g : PathTo σ (obseq.LayoutTy.PtrL τ)}
    {srcLoc : Local Γ τ}
    {bS : mirlite.Binding}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (h_go : pathOffset g ≠ 0)
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
  -- §1 the destination allocation
  simp only [mirlite.stepStmt, mirlite.doAssign] at h_step
  cases h_prep : mirlite.preparePlaceAssign MSB s_mir (Place.proj (Place.local dstLoc) g) with
  | err m => rw [h_prep] at h_step; simp at h_step
  | ok s1 =>
      rw [h_prep] at h_step
      -- invert prepare: the destination was unbound, so `allocateBase` ran
      have h_prep' := h_prep
      simp only [mirlite.preparePlaceAssign, mirlite.resolvePlace?, h_envD,
        mirlite.allocateRoot, mirlite.allocateBase, mirlite.allocate] at h_prep'
      cases h_own_src : MSB.own s_mir.perms s_mir.mem.addrStart
          (blockSize (σ)) with
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
              have h_szD : obseq.typeSize (layoutToTyVal (σ))
                  = blockSize (σ) := obseq.typeSize_layoutToTyVal _
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
                  (ρa.extendBlock s_mir.mem.addrStart (blockSize σ)) :=
                AddrRenameIncr.extendBlock h_id_a _ _
              have h_id_a' : IdentityOnDomain
                  (ρa.extendBlock s_mir.mem.addrStart (blockSize σ)) :=
                IdentityOnDomain.extendBlock h_id_a _ _
              have h_ra_new : (ρa.extendBlock s_mir.mem.addrStart (blockSize σ))
                  s_mir.mem.addrStart = some s_mir.mem.addrStart :=
                AddrRenameMap.extendBlock_base _ _ _
              have h_ra_dom : ∀ k, k < blockSize σ →
                  (ρa.extendBlock s_mir.mem.addrStart (blockSize σ))
                    (s_mir.mem.addrStart + k) = some (s_mir.mem.addrStart + k) :=
                fun _ hk => AddrRenameMap.extendBlock_mem hk
              have h_raS' := h_incr_a _ _ h_raS
              -- §7 the mirlite write and BRIDGE 1: the interior `Borrow(Mut)`
              -- the compiler mints for the field has no mirlite counterpart,
              -- so ref/use/die must collapse to the parent's use
              simp only [hD1] at h_step
              have h_w := h_step
              simp only [mirlite.writeResolvedPlace] at h_w
              split at h_w
              · simp at h_w
              · rename_i h_nb
                split at h_w
                · rename_i perms'' h_useMut_src
                  cases h_w
                  obtain ⟨qW, h_useMut_tgt, h_psim3⟩ :=
                    sb_write_respects_PermSim h_psim2 h_wf2 h_rtD_new h_nwD h_useMut_src
                  obtain ⟨q1, h_ref_dst⟩ := sb_ref_Mut_ok_of_sb_write_ok h_useMut_tgt
                  have h_unprot := freshTag_not_protected h_psim2 h_tbd2
                  have h2 : wildcardTag < tgtP2.NextTag := (h_tbd2 _ _ h_wf2.2).2
                  have h_ntw' : (tgtP2.NextTag == wildcardTag) = false := by grind
                  obtain ⟨q2, q3, qAcc', h_wr1, h_die1, h_wr2, h_sm, h_ex, h_pf, h_ntle⟩ :=
                    sb_ref_use_die_cancels h_ntw' h_unprot h_ref_dst
                  have h_qAcc : qAcc' = qW := by grind
                  subst h_qAcc
                  -- §8 the fragment: Alloc; Borrow; Borrow(Mut); RStore; Die
                  have h_stmtRun := (h_run0 csPrefix).trans
                    (compileStmt_ref_projoffset_fresh_run (cs := csPrefix)
                      kind prot mask h_go h_piD h_piS)
                  obtain ⟨stmtOutC, h_stmtOutC⟩ :=
                    compileStmt_ref_projoffset_fresh_value (cs := csPrefix) kind prot mask
                      h_go h_piD h_piS
                  obtain ⟨stmtOut, h_stmtOut⟩ := h_val0 csPrefix stmtOutC h_stmtOutC
                  have h_code1 : compProg s_osea.pc
                      = some (Instr.Assgn (Register.R csPrefix.nextReg)
                          (Rhs.Alloc (layoutToTyVal σ))) := by
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
                      rw [emit_code_lt_nextLabel _ _ (by
                        simp only [emit, setPlaceInfo, List.length_cons, List.length_nil]; omega)]
                      rw [emit_code_lt_nextLabel _ _ (by
                        simp only [emit, setPlaceInfo, List.length_cons, List.length_nil]; omega)]
                      have h := emit_code_at_new { csPrefix with nextReg := csPrefix.nextReg + 1 }
                        [Instr.Assgn (Register.R csPrefix.nextReg)
                          (Rhs.Alloc (layoutToTyVal σ))] (k := 0) (by simp)
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
                      rw [emit_code_lt_nextLabel _ _ (by
                        simp only [emit, setPlaceInfo, List.length_cons, List.length_nil]; omega)]
                      rw [emit_code_lt_nextLabel _ _ (by
                        simp only [emit, setPlaceInfo, List.length_cons, List.length_nil]; omega)]
                      have h := emit_code_at_new
                        { (setPlaceInfo
                            (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                              [Instr.Assgn (Register.R csPrefix.nextReg)
                                (Rhs.Alloc (layoutToTyVal σ))])
                            dstLoc.idx.1 (Register.R csPrefix.nextReg, σ)) with
                            nextReg := csPrefix.nextReg + 1 + 1 }
                        [Instr.Assgn (Register.R (csPrefix.nextReg + 1))
                          (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)] (k := 0) (by simp)
                      simpa [emit, setPlaceInfo] using h
                  have h_code3 : compProg (s_osea.pc + 1 + 1)
                      = some (Instr.Assgn (Register.R (csPrefix.nextReg + 1 + 1))
                          (Rhs.Borrow RefKind.Mut false [] (blockSize (obseq.LayoutTy.PtrL τ))
                            (Register.R csPrefix.nextReg) (pathOffset g))) := by
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
                      have h := emit_code_at_new
                        { (emit
                            { (setPlaceInfo
                                (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                                  [Instr.Assgn (Register.R csPrefix.nextReg)
                                    (Rhs.Alloc (layoutToTyVal σ))])
                                dstLoc.idx.1 (Register.R csPrefix.nextReg, σ)) with
                                nextReg := csPrefix.nextReg + 1 + 1 }
                            [Instr.Assgn (Register.R (csPrefix.nextReg + 1))
                              (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)]) with
                            nextReg := csPrefix.nextReg + 1 + 1 + 1 }
                        [Instr.Assgn (Register.R (csPrefix.nextReg + 1 + 1))
                          (Rhs.Borrow RefKind.Mut false [] (blockSize (obseq.LayoutTy.PtrL τ))
                            (Register.R csPrefix.nextReg) (pathOffset g))] (k := 0) (by simp)
                      simpa [emit, setPlaceInfo] using h
                  have h_code4 : compProg (s_osea.pc + 1 + 1 + 1)
                      = some (Instr.RStore obseq.TyVal.PTy (Register.R (csPrefix.nextReg + 1))
                          (Register.R (csPrefix.nextReg + 1 + 1))) := by
                    rw [h_pc]
                    refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
                    · rw [h_stmtRun]
                      simp only [emit, setPlaceInfo, List.length_cons, List.length_nil]
                      omega
                    · rw [h_stmtRun]
                      rw [emit_code_lt_nextLabel _ _ (by
                        simp only [emit, setPlaceInfo, List.length_cons, List.length_nil]; omega)]
                      have h := emit_code_at_new
                        (emit
                          { (emit
                              { (setPlaceInfo
                                  (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
                                    [Instr.Assgn (Register.R csPrefix.nextReg)
                                      (Rhs.Alloc (layoutToTyVal σ))])
                                  dstLoc.idx.1 (Register.R csPrefix.nextReg, σ)) with
                                  nextReg := csPrefix.nextReg + 1 + 1 }
                              [Instr.Assgn (Register.R (csPrefix.nextReg + 1))
                                (Rhs.Borrow kind prot mask (blockSize τ) srcReg 0)]) with
                              nextReg := csPrefix.nextReg + 1 + 1 + 1 }
                          [Instr.Assgn (Register.R (csPrefix.nextReg + 1 + 1))
                            (Rhs.Borrow RefKind.Mut false [] (blockSize (obseq.LayoutTy.PtrL τ))
                              (Register.R csPrefix.nextReg) (pathOffset g))])
                        [Instr.RStore obseq.TyVal.PTy (Register.R (csPrefix.nextReg + 1))
                          (Register.R (csPrefix.nextReg + 1 + 1))] (k := 0) (by simp)
                      simpa [emit, setPlaceInfo] using h
                  have h_code5 : compProg (s_osea.pc + 1 + 1 + 1 + 1)
                      = some (Instr.Die (Register.R (csPrefix.nextReg + 1 + 1))
                          (blockSize (obseq.LayoutTy.PtrL τ))) := by
                    rw [h_pc]
                    refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
                    · rw [h_stmtRun]
                      simp only [emit, setPlaceInfo, List.length_cons, List.length_nil]
                      omega
                    · rw [h_stmtRun]
                      simp [emit, setPlaceInfo]
                  -- §9 execute: Alloc, the rhs Borrow, the field Borrow, RStore, Die
                  have h_own_tgt' : MSB.own s_osea.perms s_osea.mem.addrStart
                      (obseq.typeSize (layoutToTyVal σ))
                      = .ok (tgtP1, s_osea.perms.NextTag) := by
                    rw [h_szD, h_addr_eq]; exact h_own_tgt
                  have h_run1 := runN_Assgn_Alloc_step compProg s_osea
                    (Register.R csPrefix.nextReg) (layoutToTyVal σ)
                    h_code1 h_own_tgt'
                  have h_regne : srcReg ≠ Register.R csPrefix.nextReg := by
                    cases srcReg with
                    | R n => have h_lt := h_prb _ _ _ h_piS; grind [RegisterBelow]
                  have h_entryS1 : PtrRegisterEntry
                      (oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
                        (obseq.TyVal.PTy, [Val.Ptr s_osea.mem.addrStart 0
                          (obseq.typeSize (layoutToTyVal σ))
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
                          (obseq.typeSize (layoutToTyVal σ))).2,
                        perms := tgtP1,
                        reg := oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
                          (obseq.TyVal.PTy, [Val.Ptr s_osea.mem.addrStart 0
                            (obseq.typeSize (layoutToTyVal σ))
                            s_osea.perms.NextTag]),
                        pc := s_osea.pc + 1 }
                    (Register.R (csPrefix.nextReg + 1)) srcReg kind prot mask (blockSize τ) 0
                    h_code2 h_entryS1 h_le2 h_ref_tgt'
                  have h_regne2 : Register.R csPrefix.nextReg
                      ≠ Register.R (csPrefix.nextReg + 1) := by grind
                  have h_entryRoot : PtrRegisterEntry
                      (oseair.RegMap.insert
                        (oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
                          (obseq.TyVal.PTy, [Val.Ptr s_osea.mem.addrStart 0
                            (obseq.typeSize (layoutToTyVal σ))
                            s_osea.perms.NextTag]))
                        (Register.R (csPrefix.nextReg + 1))
                        (obseq.TyVal.PTy, [Val.Ptr bS.addr (0 + 0) (blockSize τ)
                          tgtP1.NextTag]))
                      (Register.R csPrefix.nextReg) s_mir.mem.addrStart 0
                      (blockSize σ) s_osea.perms.NextTag := by
                    rw [← h_addr_eq, ← h_szD]
                    show oseair.RegMap.lookup _ _ = _
                    rw [RegMap.lookup_insert_ne _ h_regne2]
                    exact RegMap.lookup_insert_self _ _ _
                  have h_off_le : s_mir.mem.addrStart + 0 + pathOffset g
                      + blockSize (obseq.LayoutTy.PtrL τ)
                      ≤ s_mir.mem.addrStart + blockSize σ := by
                    have h1 : ¬(s_mir.mem.addrStart + g.offset + 1
                        > s_mir.mem.addrStart + blockSize σ) := by simpa using h_nb
                    show s_mir.mem.addrStart + 0 + g.offset + 1
                      ≤ s_mir.mem.addrStart + blockSize σ
                    simp only [Nat.add_zero]
                    grind
                  have h_ref_dst' : MSB.ref tgtP2 (s_mir.mem.addrStart + 0 + pathOffset g)
                      (blockSize (obseq.LayoutTy.PtrL τ)) s_osea.perms.NextTag
                      RefKind.Mut false []
                      = .ok (q1, tgtP2.NextTag) := by
                    show MSB.ref tgtP2 (s_mir.mem.addrStart + 0 + g.offset) 1
                      s_osea.perms.NextTag RefKind.Mut false [] = _
                    simp only [Nat.add_zero]
                    simpa using h_ref_dst
                  have h_run3 := runN_Assgn_Borrow_step compProg
                    { s_osea with
                        mem := (oseair.allocate s_osea.mem
                          (obseq.typeSize (layoutToTyVal σ))).2,
                        perms := tgtP2,
                        reg := oseair.RegMap.insert
                          (oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
                            (obseq.TyVal.PTy, [Val.Ptr s_osea.mem.addrStart 0
                              (obseq.typeSize (layoutToTyVal σ))
                              s_osea.perms.NextTag]))
                          (Register.R (csPrefix.nextReg + 1))
                          (obseq.TyVal.PTy, [Val.Ptr bS.addr (0 + 0) (blockSize τ)
                            tgtP1.NextTag]),
                        pc := s_osea.pc + 1 + 1 }
                    (Register.R (csPrefix.nextReg + 1 + 1)) (Register.R csPrefix.nextReg)
                    RefKind.Mut false [] (blockSize (obseq.LayoutTy.PtrL τ)) (pathOffset g)
                    h_code3 h_entryRoot h_off_le h_ref_dst'
                  simp only [Nat.zero_add] at h_run3
                  -- §10 the store through the field temp (BRIDGE 2), then its Die
                  have h_regne3 : Register.R (csPrefix.nextReg + 1)
                      ≠ Register.R (csPrefix.nextReg + 1 + 1) := by grind
                  have h_entry_tmpD : PtrRegisterEntry
                      (oseair.RegMap.insert
                        (oseair.RegMap.insert
                          (oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
                            (obseq.TyVal.PTy, [Val.Ptr s_osea.mem.addrStart 0
                              (obseq.typeSize (layoutToTyVal σ))
                              s_osea.perms.NextTag]))
                          (Register.R (csPrefix.nextReg + 1))
                          (obseq.TyVal.PTy, [Val.Ptr bS.addr (0 + 0) (blockSize τ)
                            tgtP1.NextTag]))
                        (Register.R (csPrefix.nextReg + 1 + 1))
                        (obseq.TyVal.PTy, [Val.Ptr s_mir.mem.addrStart (pathOffset g)
                          (blockSize σ) tgtP2.NextTag]))
                      (Register.R (csPrefix.nextReg + 1 + 1)) s_mir.mem.addrStart
                      (s_mir.mem.addrStart + g.offset - s_mir.mem.addrStart)
                      (blockSize σ) tgtP2.NextTag := by
                    rw [show s_mir.mem.addrStart + g.offset - s_mir.mem.addrStart
                        = g.offset by grind]
                    exact RegMap.lookup_insert_self _ _ _
                  have h_wr1' : MSB.useMut q1 (s_mir.mem.addrStart + g.offset)
                      [Val.Ptr bS.addr (0 + 0) (blockSize τ) tgtP1.NextTag].length
                      tgtP2.NextTag = .ok q2 := by
                    simpa using h_wr1
                  obtain ⟨h_wtp, h_sms'⟩ :=
                    writeThroughPtr_sim (τ := obseq.LayoutTy.PtrL τ)
                      (s_osea :=
                        { s_osea with
                            mem := (oseair.allocate s_osea.mem
                              (obseq.typeSize (layoutToTyVal σ))).2,
                            perms := q1,
                            reg := oseair.RegMap.insert
                              (oseair.RegMap.insert
                                (oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
                                  (obseq.TyVal.PTy, [Val.Ptr s_osea.mem.addrStart 0
                                    (obseq.typeSize (layoutToTyVal σ))
                                    s_osea.perms.NextTag]))
                                (Register.R (csPrefix.nextReg + 1))
                                (obseq.TyVal.PTy, [Val.Ptr bS.addr (0 + 0) (blockSize τ)
                                  tgtP1.NextTag]))
                              (Register.R (csPrefix.nextReg + 1 + 1))
                              (obseq.TyVal.PTy, [Val.Ptr s_mir.mem.addrStart (pathOffset g)
                                (blockSize σ) tgtP2.NextTag]),
                            pc := s_osea.pc + 1 + 1 + 1 })
                      (resolved := { addr := s_mir.mem.addrStart + g.offset,
                                     tag := s_mir.perms.NextTag,
                                     allocBase := s_mir.mem.addrStart,
                                     allocSize := blockSize σ })
                      "RStore Invalid Regs"
                      [mirlite.MemValue.ptrVal bS.addr (bS.addr - bS.addr) (blockSize τ)
                        permsOwned.NextTag]
                      [Val.Ptr bS.addr (0 + 0) (blockSize τ) tgtP1.NextTag] rfl
                      ⟨⟨h_raS', by simp, rfl, h_rt_new, h_nwR,
                        fun k hk => ⟨(h_domS k hk).choose,
                          h_incr_a _ _ (h_domS k hk).choose_spec⟩⟩, trivial⟩
                      h_id_a' h_entry_tmpD h_wr1'
                      (by exact SourceMemSim.rename_mono h_incr_a h_incr12 h_sms)
                      (Nat.le_add_right _ _)
                      (fun k hk => by
                        simp [blockSize, Nat.lt_one_iff] at hk
                        subst hk
                        have h_offlt : g.offset < blockSize σ := by grind
                        simpa using h_ra_dom g.offset h_offlt)
                      h_step
                  have h_run4 := runN_RStore_step compProg _ _ obseq.TyVal.PTy
                    (Register.R (csPrefix.nextReg + 1)) (Register.R (csPrefix.nextReg + 1 + 1))
                    _ _ h_code4
                    (by rw [RegMap.lookup_insert_ne _ h_regne3]
                        exact RegMap.lookup_insert_self _ _ _)
                    (RegMap.lookup_insert_self _ _ _)
                    h_wtp
                  have h_die1' : MSB.die q2 (s_mir.mem.addrStart + pathOffset g)
                      (blockSize (obseq.LayoutTy.PtrL τ)) tgtP2.NextTag = .ok q3 := by
                    simpa using h_die1
                  have h_run5 := runN_Die_step compProg
                    { s_osea with
                        mem := oseair.writeWordSeq
                          (oseair.allocate s_osea.mem
                            (obseq.typeSize (layoutToTyVal σ))).2
                          (s_mir.mem.addrStart + g.offset)
                          [Val.Ptr bS.addr (0 + 0) (blockSize τ) tgtP1.NextTag],
                        perms := q2,
                        reg := oseair.RegMap.insert
                          (oseair.RegMap.insert
                            (oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
                              (obseq.TyVal.PTy, [Val.Ptr s_osea.mem.addrStart 0
                                (obseq.typeSize (layoutToTyVal σ))
                                s_osea.perms.NextTag]))
                            (Register.R (csPrefix.nextReg + 1))
                            (obseq.TyVal.PTy, [Val.Ptr bS.addr (0 + 0) (blockSize τ)
                              tgtP1.NextTag]))
                          (Register.R (csPrefix.nextReg + 1 + 1))
                          (obseq.TyVal.PTy, [Val.Ptr s_mir.mem.addrStart (pathOffset g)
                            (blockSize σ) tgtP2.NextTag]),
                        pc := s_osea.pc + 1 + 1 + 1 + 1 }
                    (Register.R (csPrefix.nextReg + 1 + 1))
                    (blockSize (obseq.LayoutTy.PtrL τ))
                    h_code5 (RegMap.lookup_insert_self _ _ _) h_die1'
                  have h_runA := (oseair_runN_add 1 1 s_osea compProg _ h_run1).trans h_run2
                  have h_runB :=
                    (oseair_runN_add (1 + 1) 1 s_osea compProg _ h_runA).trans h_run3
                  have h_runC :=
                    (oseair_runN_add (1 + 1 + 1) 1 s_osea compProg _ h_runB).trans h_run4
                  have h_run :=
                    (oseair_runN_add (1 + 1 + 1 + 1) 1 s_osea compProg _ h_runC).trans h_run5
                  -- §11 BRIDGE 1 collapses the triple to the parent write
                  have h_psim4 : PermSim
                      ((ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag).extend
                        permsOwned.NextTag tgtP1.NextTag) perms'' q3 := by
                    obtain ⟨hs, hp, he, hn⟩ := h_psim3
                    exact ⟨by rw [h_sm]; exact hs, by rw [h_pf]; exact hp,
                           by rw [h_ex]; exact he, Nat.le_trans hn h_ntle⟩
                  -- §12 rebuild the invariant under both extended renames
                  refine ⟨_, _, _, 1 + 1 + 1 + 1 + 1, h_incr_a, h_incr12, h_run, ?_⟩
                  refine ⟨CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix,
                    ⟨prefixCompileState_succ h_csAt h_stmt h_stmtOut, ?_⟩, ?_, h_sms',
                    h_psim4, h_id_a', h_wf2, ?_, ?_, ?_, ?_⟩
                  · -- label agreement at pc+5
                    show s_osea.pc + 1 + 1 + 1 + 1 + 1 = _
                    rw [h_pc, h_stmtRun]
                    simp [emit, setPlaceInfo]
                  · -- LocalBindingSim: the destination is now bound and mapped;
                    -- the others survive three fresh registers and the new entry
                    intro τ' loc' binding' h_env'
                    by_cases h_idx : loc'.idx = dstLoc.idx
                    · have h_ty : τ' = σ := by
                        rw [← loc'.hTy, h_idx, dstLoc.hTy]
                      subst h_ty
                      have h_b : binding' = { addr := s_mir.mem.addrStart,
                                              tag := s_mir.perms.NextTag } := by
                        grind [mirlite.Env.lookup, mirlite.Env.set]
                      subst h_b
                      refine ⟨Register.R csPrefix.nextReg, s_mir.mem.addrStart,
                        s_osea.perms.NextTag, ?_, ?_, h_ra_new, h_rtD_new, h_nwD, ?_⟩
                      · rw [h_stmtRun, getPlaceInfo_emit, getPlaceInfo_emit,
                          getPlaceInfo_emit, getPlaceInfo_setNextReg, getPlaceInfo_emit,
                          getPlaceInfo_setNextReg,
                          show loc'.idx.1 = dstLoc.idx.1 from congrArg Fin.val h_idx]
                        exact getPlaceInfo_setPlaceInfo_self _ _ _
                      · show oseair.RegMap.lookup _ _ = _
                        rw [← h_addr_eq, ← h_szD,
                          RegMap.lookup_insert_ne _ (show Register.R csPrefix.nextReg
                            ≠ Register.R (csPrefix.nextReg + 1 + 1) by grind),
                          RegMap.lookup_insert_ne _ h_regne2]
                        exact RegMap.lookup_insert_self _ _ _
                      · intro k hk
                        exact ⟨s_mir.mem.addrStart + k, h_ra_dom k hk⟩
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
                      have h_rne3 : reg' ≠ Register.R (csPrefix.nextReg + 1 + 1) := by
                        cases reg' with
                        | R n => have h_lt := h_prb _ _ _ h_pi'; grind [RegisterBelow]
                      refine ⟨reg', base', tag', ?_, ?_, h_incr_a _ _ h_ra',
                        h_incr12 _ _ h_rt', h_nw',
                        fun k hk => ⟨(h_dom' k hk).choose,
                          h_incr_a _ _ (h_dom' k hk).choose_spec⟩⟩
                      · rw [h_stmtRun, getPlaceInfo_emit, getPlaceInfo_emit,
                          getPlaceInfo_emit, getPlaceInfo_setNextReg, getPlaceInfo_emit,
                          getPlaceInfo_setNextReg, getPlaceInfo_setPlaceInfo_ne _ h_idxv,
                          getPlaceInfo_emit]
                        exact h_pi'
                      · show oseair.RegMap.lookup _ _ = _
                        rw [RegMap.lookup_insert_ne _ h_rne3,
                          RegMap.lookup_insert_ne _ h_rne2,
                          RegMap.lookup_insert_ne _ h_rne1]
                        exact h_entry'
                  · -- TagRenameBounded across the store
                    show TagRenameBounded _ perms''.NextTag q3.NextTag
                    rw [sb_write_NextTag h_useMut_src]
                    exact TagRenameBounded.mono h_tbd2 (Nat.le_refl _)
                      (by rw [← sb_write_NextTag h_useMut_tgt]; exact h_ntle)
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
                        getPlaceInfo_emit, getPlaceInfo_setNextReg, getPlaceInfo_emit,
                        getPlaceInfo_setNextReg, getPlaceInfo_setPlaceInfo_ne _ h_idxv,
                        getPlaceInfo_emit]
                      exact h_unmap loc' h_none'
                  · -- PlaceRegMapBound: three fresh registers, all below nextReg+3
                    intro idx reg τ'' h_look
                    rw [h_stmtRun] at h_look ⊢
                    rw [getPlaceInfo_emit, getPlaceInfo_emit, getPlaceInfo_emit,
                      getPlaceInfo_setNextReg, getPlaceInfo_emit,
                      getPlaceInfo_setNextReg] at h_look
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


/-- REGIME B of ref with a DEREF SOURCE: `dst := &kind *chain` and
    `dst`'s root UNBOUND. The root `Alloc` comes FIRST, so the source
    spine lowers from the post-`Alloc` states — which means the mother
    lemma's whole hypothesis bundle (`LocalBindingSim`,
    `PlaceRegMapBound`, `SourceMemSim`, `PermSim`, the pc agreement and
    the instruction transfer) has to be re-established MID-PROOF at the
    extended renames, not just rebuilt at the end. -/
theorem ref_fresh_derefsrc_simulation
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
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
  -- §1 the destination root is allocated on both machines
  simp only [mirlite.stepStmt, mirlite.doAssign] at h_step
  cases h_prep : mirlite.preparePlaceAssign MSB s_mir (Place.local dstLoc) with
  | err m => rw [h_prep] at h_step; simp at h_step
  | ok s1 =>
  rw [h_prep] at h_step
  simp only [mirlite.preparePlaceAssign, mirlite.resolvePlace?, h_envD,
    mirlite.allocateRoot, mirlite.allocateBase, mirlite.allocate] at h_prep
  cases h_own_src : MSB.own s_mir.perms s_mir.mem.addrStart (blockSize (obseq.LayoutTy.PtrL τ)) with
  | error e => rw [h_own_src] at h_prep; simp at h_prep
  | ok pr =>
  obtain ⟨permsOwned, tagD⟩ := pr
  rw [h_own_src] at h_prep
  injection h_prep with h_s1
  -- §2 both renames grow: ρt at the root's tag, ρa over the root block
  obtain ⟨tgtP1, h_own_tgt, h_tagD_eq, h_incr_t, h_wf1, h_tbd1, h_psim1⟩ :=
    sb_own_respects_PermSim h_psim h_wf_t h_tbd h_own_src
  subst h_tagD_eq
  have h_addr_eq : s_osea.mem.addrStart = s_mir.mem.addrStart := h_alloc
  have h_sz : obseq.typeSize (layoutToTyVal (obseq.LayoutTy.PtrL τ)) = blockSize (obseq.LayoutTy.PtrL τ) :=
    obseq.typeSize_layoutToTyVal _
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
  have h_rt_new : (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag)
      s_mir.perms.NextTag = some s_osea.perms.NextTag :=
    TagRenameMap.extend_self _ _ _
  have h0 : wildcardTag < s_mir.perms.NextTag := (h_tbd _ _ h_wf_t.2).1
  have h_nw : (s_mir.perms.NextTag == wildcardTag) = false := by grind
  -- the post-allocation source state, by its projections
  have h_lookup_set : mirlite.Env.lookup s1.env dstLoc
      = some { addr := s_mir.mem.addrStart, tag := s_mir.perms.NextTag } := by
    rw [← h_s1]
    simp [mirlite.Env.lookup, mirlite.Env.set]
  have h_perms1 : s1.perms = permsOwned := by rw [← h_s1]
  have h_pc1 : s1.pc = s_mir.pc := by rw [← h_s1]
  have h_find1 : ∀ a, mirlite.Mem.find? s1.mem a = mirlite.Mem.find? s_mir.mem a := by
    intro a; rw [← h_s1]; rfl
  have h_own_tgt' : MSB.own s_osea.perms s_osea.mem.addrStart
      (obseq.typeSize (layoutToTyVal (obseq.LayoutTy.PtrL τ)))
      = .ok (tgtP1, s_osea.perms.NextTag) := by
    rw [h_sz, h_addr_eq]; exact h_own_tgt
  have h_env1 : s1.env = mirlite.Env.set s_mir.env dstLoc
      { addr := s_mir.mem.addrStart, tag := s_mir.perms.NextTag } := by rw [← h_s1]
  have h_smsA : SourceMemSim
      (ρa.extendBlock s_mir.mem.addrStart (blockSize (obseq.LayoutTy.PtrL τ)))
      (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag)
      s1.mem (oseair.allocate s_osea.mem
        (obseq.typeSize (layoutToTyVal (obseq.LayoutTy.PtrL τ)))).2 := by
    intro a v h_find
    rw [h_find1] at h_find
    exact SourceMemSim.rename_mono h_incr_a h_incr_t h_sms a v h_find
  have h_pi_new : getPlaceInfo (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))]) dstLoc.idx.1 (Register.R csPrefix.nextReg, obseq.LayoutTy.PtrL τ)) dstLoc.idx.1
      = some (Register.R csPrefix.nextReg, obseq.LayoutTy.PtrL τ) :=
    getPlaceInfo_setPlaceInfo_self _ _ _
  -- §3 the mother lemma's hypotheses, re-established at the post-Alloc states
  have h_prb1 : PlaceRegMapBound (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))]) dstLoc.idx.1 (Register.R csPrefix.nextReg, obseq.LayoutTy.PtrL τ)) := by
    intro idx reg τ'' h_look
    by_cases h_i : idx = dstLoc.idx.1
    · subst h_i
      rw [getPlaceInfo_setPlaceInfo_self] at h_look
      injection h_look with h_look'
      have : reg = Register.R csPrefix.nextReg := (congrArg Prod.fst h_look').symm
      subst this
      show csPrefix.nextReg < _
      simp only [emit, setPlaceInfo]
      grind
    · rw [getPlaceInfo_setPlaceInfo_ne _ h_i] at h_look
      refine RegisterBelow.mono ?_ (h_prb _ _ _ h_look)
      simp only [emit, setPlaceInfo]
      grind
  have h_lbs1 : LocalBindingSim
      (ρa.extendBlock s_mir.mem.addrStart (blockSize (obseq.LayoutTy.PtrL τ)))
      (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag)
      s1.env { s_osea with mem := (oseair.allocate s_osea.mem (obseq.typeSize (layoutToTyVal (obseq.LayoutTy.PtrL τ)))).2, perms := tgtP1, reg := oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg) (obseq.TyVal.PTy, [Val.Ptr s_osea.mem.addrStart 0 (obseq.typeSize (layoutToTyVal (obseq.LayoutTy.PtrL τ))) s_osea.perms.NextTag]), pc := s_osea.pc + 1 } (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))]) dstLoc.idx.1 (Register.R csPrefix.nextReg, obseq.LayoutTy.PtrL τ)) := by
    rw [← h_s1]
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
        s_osea.perms.NextTag, ?_, ?_, h_ra_base, h_rt_new, h_nw, ?_⟩
      · rw [show loc'.idx.1 = dstLoc.idx.1 from congrArg Fin.val h_idx]
        exact h_pi_new
      · show oseair.RegMap.lookup _ _ = _
        rw [← h_addr_eq, ← h_sz]
        exact RegMap.lookup_insert_self _ _ _
      · intro k hk
        exact ⟨s_mir.mem.addrStart + k, h_ra_dom k hk⟩
    · have h_env'' : mirlite.Env.lookup s_mir.env loc' = some binding' := by
        simpa only [mirlite.Env.lookup, mirlite.Env.set, if_neg h_idx] using h_env'
      obtain ⟨reg', base', tag', h_pi', h_entry', h_ra', h_rt', h_nw', h_dom'⟩ :=
        h_lbs loc' binding' h_env''
      have h_idxv : loc'.idx.1 ≠ dstLoc.idx.1 := by grind [Fin.ext]
      have h_regne : reg' ≠ Register.R csPrefix.nextReg := by
        cases reg' with
        | R n => have h_lt := h_prb _ _ _ h_pi'; grind [RegisterBelow]
      refine ⟨reg', base', tag', ?_, ?_, h_incr_a _ _ h_ra',
        h_incr_t _ _ h_rt', h_nw',
        fun k hk => ⟨(h_dom' k hk).choose,
          h_incr_a _ _ (h_dom' k hk).choose_spec⟩⟩
      · rw [getPlaceInfo_setPlaceInfo_ne _ h_idxv]
        exact h_pi'
      · show oseair.RegMap.lookup _ _ = _
        rw [RegMap.lookup_insert_ne _ h_regne]
        exact h_entry'
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
      compileStmt_ref_fresh_derefsrc_value kind prot mask h_piD h_dval0
    obtain ⟨stmtOut, h_stmtOut⟩ := h_val0 csPrefix stmtOutC h_stmtOutC
    have h_stmtRun := (h_run0 csPrefix).trans
      (compileStmt_ref_fresh_derefsrc_run kind prot mask h_piD h_dval0)
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
    -- §7 the WHOLE src lowering via the mother lemma, from the post-Alloc states
    obtain ⟨dOut, n1, s_mid, tres, h_dval, h_dclean, h_drun, h_dpc, h_dmem,
      h_dpsim, h_dnt1, h_dnt2, h_dlbs, h_dentry, h_drt, h_dnw, h_dle, h_drange,
      h_dbelow, h_dprm, h_dregmono, h_dlabmono, -, h_dbase⟩ :=
      ptrChain_lowering_sim (s_mir := s1) h_id_a' h_wf1 h_spine RefKind.Shared
        (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))]) dstLoc.idx.1 (Register.R csPrefix.nextReg, obseq.LayoutTy.PtrL τ)) { s_osea with mem := (oseair.allocate s_osea.mem (obseq.typeSize (layoutToTyVal (obseq.LayoutTy.PtrL τ)))).2, perms := tgtP1, reg := oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg) (obseq.TyVal.PTy, [Val.Ptr s_osea.mem.addrStart 0 (obseq.typeSize (layoutToTyVal (obseq.LayoutTy.PtrL τ))) s_osea.perms.NextTag]), pc := s_osea.pc + 1 }
        resolved permsR h_dres (by rw [h_perms1]; exact h_tbd1) h_lbs1 h_prb1
        h_smsA
        (by rw [h_perms1]; exact h_psim1)
        (by
          show s_osea.pc + 1 = _
          rw [h_pc]
          simp only [emit_nextLabel, setPlaceInfo_nextLabel, List.length_cons,
            List.length_nil])
        h_instS
    have h_deq : dOut = dOut0 := by
      rw [h_dval0] at h_dval; exact (Except.ok.inj h_dval).symm
    subst h_deq
    have h_cancel : resolved.allocBase + (resolved.addr - resolved.allocBase)
        = resolved.addr := Nat.add_sub_cancel' h_dle
    have h_csAt1 : csAt cs0 prog s1.pc csPrefix := by rw [h_pc1]; exact h_csAt
    have h_stmt1 : prog.get? s1.pc = some stmt0 := by rw [h_pc1]; exact h_stmt
    -- §8 the rhs retag transported at the post-spine state
    have h_tbd_mid : TagRenameBounded
        (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag)
        permsR.NextTag s_mid.perms.NextTag := by
      rw [h_dnt1, h_perms1]
      exact TagRenameBounded.mono h_tbd1 (Nat.le_refl _) h_dnt2
    obtain ⟨tgtPerms, h_ref_tgt, h_fresh_eq, h_incr_t2, h_wf_t', h_tbd', h_psim'⟩ :=
      sb_ref_respects_PermSim h_dpsim h_wf1 h_tbd_mid h_drt h_dnw h_ref_src
    subst h_fresh_eq
    have h_rt_new2 : ((ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag).extend
        permsR.NextTag s_mid.perms.NextTag) permsR.NextTag
        = some s_mid.perms.NextTag := TagRenameMap.extend_self _ _ _
    have h1 : wildcardTag < permsR.NextTag := (h_tbd_mid _ _ h_wf1.2).1
    have h_nw_new : (permsR.NextTag == wildcardTag) = false := by grind
    -- §9 the Borrow and the RStore
    have h_code1 : compProg s_mid.pc
        = some (Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (Place.deref P)) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))]) dstLoc.idx.1 (Register.R csPrefix.nextReg, obseq.LayoutTy.PtrL τ))).nextReg)
            (Rhs.Borrow kind prot mask (blockSize τ) dOut.result.reg 0)) := by
      rw [h_dpc]
      refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
      · rw [h_stmtRun]
        simp only [emit_nextLabel, List.length_cons, List.length_nil]
        omega
      · rw [h_stmtRun]
        rw [emit_code_lt_nextLabel _ _ (by
          simp only [emit_nextLabel, List.length_cons, List.length_nil]; omega)]
        have h := emit_code_at_new
          { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (Place.deref P)) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))]) dstLoc.idx.1 (Register.R csPrefix.nextReg, obseq.LayoutTy.PtrL τ))) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (Place.deref P)) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))]) dstLoc.idx.1 (Register.R csPrefix.nextReg, obseq.LayoutTy.PtrL τ))).nextReg + 1 }
          [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (Place.deref P)) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))]) dstLoc.idx.1 (Register.R csPrefix.nextReg, obseq.LayoutTy.PtrL τ))).nextReg)
            (Rhs.Borrow kind prot mask (blockSize τ) dOut.result.reg 0)]
          (k := 0) (by simp)
        simpa using h
    have h_le1 : resolved.allocBase + (resolved.addr - resolved.allocBase) + 0
        + blockSize τ ≤ resolved.allocBase + resolved.allocSize := by grind
    have h_ref_tgt' : MSB.ref s_mid.perms
        (resolved.allocBase + (resolved.addr - resolved.allocBase) + 0)
        (blockSize τ) tres kind prot mask
        = .ok (tgtPerms, s_mid.perms.NextTag) := by
      rw [Nat.add_zero, h_cancel]
      exact h_ref_tgt
    have h_run1 := runN_Assgn_Borrow_step compProg s_mid
      (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (Place.deref P)) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))]) dstLoc.idx.1 (Register.R csPrefix.nextReg, obseq.LayoutTy.PtrL τ))).nextReg) dOut.result.reg kind prot mask (blockSize τ) 0
      h_code1 h_dentry h_le1 h_ref_tgt'
    obtain ⟨dstReg2, baseD2, tagD2, h_piD2, h_entryD2, h_raD2, h_rtD2, h_nwD2, -⟩ :=
      h_dlbs dstLoc _ h_lookup_set
    have h_dr2 : dstReg2 = Register.R csPrefix.nextReg := by grind
    have h_bd2 : baseD2 = s_mir.mem.addrStart := (h_id_a' _ _ h_raD2).symm
    have h_td2 : tagD2 = s_osea.perms.NextTag := by grind
    subst h_dr2
    subst h_bd2
    subst h_td2
    have h_regne : Register.R csPrefix.nextReg ≠ Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (Place.deref P)) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))]) dstLoc.idx.1 (Register.R csPrefix.nextReg, obseq.LayoutTy.PtrL τ))).nextReg := by
      have h_le := h_dregmono
      csnorm at h_le
      grind
    have h_code2 : compProg (s_mid.pc + 1)
        = some (Instr.RStore obseq.TyVal.PTy
            (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (Place.deref P)) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))]) dstLoc.idx.1 (Register.R csPrefix.nextReg, obseq.LayoutTy.PtrL τ))).nextReg) (Register.R csPrefix.nextReg)) := by
      refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
      · rw [h_stmtRun, h_dpc]
        simp only [emit_nextLabel, List.length_cons, List.length_nil]
        omega
      · rw [h_stmtRun, h_dpc]
        have h := emit_code_at_new
          (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (Place.deref P)) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))]) dstLoc.idx.1 (Register.R csPrefix.nextReg, obseq.LayoutTy.PtrL τ))) with nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (Place.deref P)) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))]) dstLoc.idx.1 (Register.R csPrefix.nextReg, obseq.LayoutTy.PtrL τ))).nextReg + 1 }
            [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (Place.deref P)) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))]) dstLoc.idx.1 (Register.R csPrefix.nextReg, obseq.LayoutTy.PtrL τ))).nextReg)
              (Rhs.Borrow kind prot mask (blockSize τ) dOut.result.reg 0)])
          [Instr.RStore obseq.TyVal.PTy
            (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (Place.deref P)) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))]) dstLoc.idx.1 (Register.R csPrefix.nextReg, obseq.LayoutTy.PtrL τ))).nextReg) (Register.R csPrefix.nextReg)]
          (k := 0) (by simp)
        simpa [emit] using h
    -- §10 the store into the freshly allocated root, via BRIDGE 2
    have h_w := h_step
    simp only [mirlite.writeResolvedPlace] at h_w
    split at h_w
    · simp at h_w
    · rename_i h_nb
      split at h_w
      · rename_i perms2 h_useMut_src
        cases h_w
        obtain ⟨p3, h_useMut_tgt, h_psim3⟩ :=
          sb_write_respects_PermSim h_psim' h_wf_t'
            (h_incr_t2 _ _ h_rtD2) h_nwD2 h_useMut_src
        have h_entryD1 : PtrRegisterEntry
            (oseair.RegMap.insert s_mid.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (Place.deref P)) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))]) dstLoc.idx.1 (Register.R csPrefix.nextReg, obseq.LayoutTy.PtrL τ))).nextReg) (obseq.TyVal.PTy, [Val.Ptr resolved.allocBase (resolved.addr - resolved.allocBase + 0) resolved.allocSize s_mid.perms.NextTag]))
            (Register.R csPrefix.nextReg) s_mir.mem.addrStart
            (s_mir.mem.addrStart - s_mir.mem.addrStart) (blockSize (obseq.LayoutTy.PtrL τ))
            s_osea.perms.NextTag := by
          rw [Nat.sub_self]
          show oseair.RegMap.lookup _ _ = _
          rw [RegMap.lookup_insert_ne _ h_regne]
          exact h_entryD2
        obtain ⟨h_wtp, h_sms'⟩ :=
          writeThroughPtr_sim (τ := obseq.LayoutTy.PtrL τ)
            (s_osea := { s_mid with perms := tgtPerms, reg := oseair.RegMap.insert s_mid.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (Place.deref P)) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))]) dstLoc.idx.1 (Register.R csPrefix.nextReg, obseq.LayoutTy.PtrL τ))).nextReg) (obseq.TyVal.PTy, [Val.Ptr resolved.allocBase (resolved.addr - resolved.allocBase + 0) resolved.allocSize s_mid.perms.NextTag]), pc := s_mid.pc + 1 })
            (resolved := { addr := s_mir.mem.addrStart, tag := s_mir.perms.NextTag,
                           allocBase := s_mir.mem.addrStart,
                           allocSize := blockSize (obseq.LayoutTy.PtrL τ) })
            "RStore Invalid Regs"
            [mirlite.MemValue.ptrVal resolved.allocBase
              (resolved.addr - resolved.allocBase) resolved.allocSize permsR.NextTag]
            [Val.Ptr resolved.allocBase (resolved.addr - resolved.allocBase + 0) resolved.allocSize s_mid.perms.NextTag] rfl
            ⟨⟨h_dbase, by simp, rfl, h_rt_new2, h_nw_new,
              fun k hk => h_drange k hk⟩, trivial⟩
            h_id_a' h_entryD1 h_useMut_tgt
            (by
              rw [h_dmem]
              exact SourceMemSim.rename_mono (AddrRenameIncr.refl _) h_incr_t2 h_smsA)
            (Nat.le_refl _)
            (fun k hk => by
              have hk0 : k = 0 := by simpa using hk
              subst hk0
              rw [Nat.add_zero]
              exact h_ra_base)
            h_step
        have h_run2 := runN_RStore_step compProg _ _ obseq.TyVal.PTy
          (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (Place.deref P)) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))]) dstLoc.idx.1 (Register.R csPrefix.nextReg, obseq.LayoutTy.PtrL τ))).nextReg) (Register.R csPrefix.nextReg) _ _ h_code2
          (RegMap.lookup_insert_self _ _ _)
          (by rw [RegMap.lookup_insert_ne _ h_regne]; exact h_entryD2)
          h_wtp
        have h_runA := (oseair_runN_add 1 n1 s_osea compProg _ h_runAlloc).trans h_drun
        have h_runB := (oseair_runN_add (1 + n1) 1 s_osea compProg _ h_runA).trans h_run1
        have h_runC :=
          (oseair_runN_add (1 + n1 + 1) 1 s_osea compProg _ h_runB).trans h_run2
        -- §11 rebuild the invariant under both extended renames
        refine ⟨_, _, _, 1 + n1 + 1 + 1, h_incr_a,
          TagRenameIncr.trans h_incr_t h_incr_t2, h_runC, ?_⟩
        refine ⟨CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix,
          ⟨prefixCompileState_succ h_csAt1 h_stmt1 h_stmtOut, ?_⟩, ?_, h_sms', h_psim3,
          h_id_a', h_wf_t', ?_, ?_, ?_, ?_⟩
        · show s_mid.pc + 1 + 1 = _
          rw [h_dpc, h_stmtRun]
          simp [emit]
        · have h_dlbs' : LocalBindingSim
              (ρa.extendBlock s_mir.mem.addrStart (blockSize (obseq.LayoutTy.PtrL τ)))
              ((ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag).extend
                permsR.NextTag s_mid.perms.NextTag)
              s1.env s_mid (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))]) dstLoc.idx.1 (Register.R csPrefix.nextReg, obseq.LayoutTy.PtrL τ)) :=
            LocalBindingSim.rename_mono (AddrRenameIncr.refl _) h_incr_t2 h_dlbs
          have h_lbs2 : LocalBindingSim
              (ρa.extendBlock s_mir.mem.addrStart (blockSize (obseq.LayoutTy.PtrL τ)))
              ((ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag).extend
                permsR.NextTag s_mid.perms.NextTag)
              s1.env { s_mid with perms := tgtPerms, reg := oseair.RegMap.insert s_mid.reg (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (Place.deref P)) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))]) dstLoc.idx.1 (Register.R csPrefix.nextReg, obseq.LayoutTy.PtrL τ))).nextReg) (obseq.TyVal.PTy, [Val.Ptr resolved.allocBase (resolved.addr - resolved.allocBase + 0) resolved.allocSize s_mid.perms.NextTag]), pc := s_mid.pc + 1 } (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))]) dstLoc.idx.1 (Register.R csPrefix.nextReg, obseq.LayoutTy.PtrL τ)) :=
            LocalBindingSim.insert_fresh_reg h_dlbs' h_prb1 h_dregmono rfl
          intro τ'' loc' binding' h_env'
          obtain ⟨reg', base', tag', h_pi', h_entry', h_ra'', h_rt', h_nw', h_dom'⟩ :=
            h_lbs2 loc' binding' h_env'
          refine ⟨reg', base', tag', ?_, h_entry', h_ra'', h_rt', h_nw', h_dom'⟩
          rw [h_stmtRun, getPlaceInfo_emit, getPlaceInfo_emit, getPlaceInfo_setNextReg]
          show (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (Place.deref P)) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))]) dstLoc.idx.1 (Register.R csPrefix.nextReg, obseq.LayoutTy.PtrL τ))).placeRegMap.lookup loc'.idx.1 = _
          rw [h_dprm]
          exact h_pi'
        · show TagRenameBounded _ perms2.NextTag p3.NextTag
          rw [sb_write_NextTag h_useMut_src, sb_write_NextTag h_useMut_tgt]
          exact h_tbd'
        · simp only [AllocLockstep, mirlite_writeWordSeq_addrStart,
            oseair_writeWordSeq_addrStart, h_dmem]
          rw [← h_s1]
          simp only [mirlite.allocate, oseair.allocate]
          rw [h_addr_eq, h_sz]
        · intro τ'' loc' h_none
          by_cases h_idx : loc'.idx = dstLoc.idx
          · exfalso
            rw [h_env1] at h_none
            simp [mirlite.Env.lookup, mirlite.Env.set, h_idx] at h_none
          · have h_idxv : loc'.idx.1 ≠ dstLoc.idx.1 := by grind [Fin.ext]
            have h_none' : mirlite.Env.lookup s_mir.env loc' = none := by
              simpa only [h_env1, mirlite.Env.lookup, mirlite.Env.set, if_neg h_idx]
                using h_none
            rw [h_stmtRun, getPlaceInfo_emit, getPlaceInfo_emit, getPlaceInfo_setNextReg]
            show (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (Place.deref P)) (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))]) dstLoc.idx.1 (Register.R csPrefix.nextReg, obseq.LayoutTy.PtrL τ))).placeRegMap.lookup loc'.idx.1 = none
            rw [h_dprm]
            show getPlaceInfo (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))]) dstLoc.idx.1 (Register.R csPrefix.nextReg, obseq.LayoutTy.PtrL τ)) loc'.idx.1 = none
            rw [getPlaceInfo_setPlaceInfo_ne _ h_idxv, getPlaceInfo_emit]
            exact h_unmap loc' h_none'
        · intro idx reg'' τ'' h_look
          rw [h_stmtRun] at h_look ⊢
          rw [getPlaceInfo_emit, getPlaceInfo_emit, getPlaceInfo_setNextReg] at h_look
          have h_cs : getPlaceInfo (setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))]) dstLoc.idx.1 (Register.R csPrefix.nextReg, obseq.LayoutTy.PtrL τ)) idx = some (reg'', τ'') := by
            show ((setPlaceInfo (emit { csPrefix with nextReg := csPrefix.nextReg + 1 } [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal (obseq.LayoutTy.PtrL τ)))]) dstLoc.idx.1 (Register.R csPrefix.nextReg, obseq.LayoutTy.PtrL τ))).placeRegMap.lookup idx = _
            rw [← h_dprm]
            exact h_look
          refine RegisterBelow.mono ?_ (h_prb1 _ _ _ h_cs)
          simp only [emit_nextReg]
          exact Nat.le_trans h_dregmono (Nat.le_succ _)
      · simp at h_w


/-- RESIDUAL (sorried). The only `sorry` left in obseq3; EIGHT call
    sites, in four classes. Re-enumerated 2026-08-31 against the
    dispatcher (the previous list said "non-spine deref srcs", which is
    not a class at all: `PtrChain_flatten_deref` holds for ANY place,
    so every deref src IS a spine once flattened).

    1. a NON-LOCAL SRC under a PROJECTED DST over a local base —
       `t.g := &s.f` and `t.g := &*p`. Only a local src is closed
       there (`ref_local_projzero/projoffset_simulation`).
    2. a PROJECTED DST over a DEREF base — `(*p).g := &_`, any src.
       This is the one class the dst-flattening recursion cannot
       normalize away, since flattening keeps the deref.
    3. a PROJ-TOPPED SRC whose base is NOT a local — `&(s.f).h` and
       `&(*p).f` — under a local dst or a deref dst (four sites).
       The `(s.f).h` half is a src-flattening transfer away from the
       closed proj-over-local leaves; the `(*p).f` half is not.
    4. a DEREF SRC under a DEREF DST — `*chain := &*chain'`.

    CLOSED and no longer residual: the dst-flattening recursion
    (`ref_proj_dst_simulation`, stmt0-threaded); deref dsts with local
    and proj-topped srcs; and, as of 2026-08-31, ALL FOUR unbound
    destination roots (`ref_fresh_projsrc_simulation`,
    `ref_projzero_fresh_simulation`, `ref_projoffset_fresh_simulation`,
    `ref_fresh_derefsrc_simulation`). -/
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

theorem ref_derefdst_projsrc_simulation
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
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
  -- §4 the retag transported: the fresh pair extends ρt
  obtain ⟨tgtP1, h_ref_tgt, h_mint_eq, h_incr_t, h_wf_t', h_tbd', h_psim'⟩ :=
    sb_ref_respects_PermSim h_psim h_wf_t h_tbd h_rtS h_nwS h_ref_src
  subst h_mint_eq
  have h_rt_new : (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag)
      s_mir.perms.NextTag = some s_osea.perms.NextTag :=
    TagRenameMap.extend_self _ _ _
  have h0 : wildcardTag < s_mir.perms.NextTag := (h_tbd _ _ h_wf_t.2).1
  have h_nw_new : (s_mir.perms.NextTag == wildcardTag) = false := by grind
  -- §5 compiler-side scaffolding: the post-Borrow LocalBindingSim feeds
  -- both the mapped-ness of the dst at cs1 and the mother lemma
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
              [Val.Ptr bS.addr (0 + pathOffset f) (blockSize σb) s_osea.perms.NextTag]),
          pc := s_osea.pc + 1 }
      (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
        [Instr.Assgn (Register.R csPrefix.nextReg)
          (Rhs.Borrow kind prot mask (blockSize τ) srcReg (pathOffset f))]) :=
    LocalBindingSim.insert_fresh_reg h_lbs0 h_prb (Nat.le_refl _) rfl
  obtain ⟨dOut0, h_dval0⟩ := placeToRegChecked_ok_of_placeInputsMapped
    (cs := emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
      [Instr.Assgn (Register.R csPrefix.nextReg)
        (Rhs.Borrow kind prot mask (blockSize τ) srcReg (pathOffset f))])
    (kind := RefKind.Mut)
    (placeInputsMapped_of_localBindingSim_resolvePlace
      (s_mir := { s_mir with perms := perms1 }) h_lbs1
      (resolvePlace?_of_resolveAcc h_dres))
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
    simp only [compileStmtChecked, compileRExprPreChecked, placeToBorrowRegChecked,
      CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
      CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
      CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
      h_root, h_lprun, h_lpval, h_lpres]
    simp only [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM]
    simp only [CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
      CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
      CheckedCompilerM.run_pure, CheckedCompilerM.value_pure, h_dval0]
    exact StateIncr.trans (emit_state_incr _ _)
      (StateIncr.trans (emit_state_incr _ _) (emit_state_incr _ _))
  have h_instD : ∀ q' instr,
      q' < (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (Place.deref P))
      (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
        [Instr.Assgn (Register.R csPrefix.nextReg)
          (Rhs.Borrow kind prot mask (blockSize τ) srcReg (pathOffset f))])).nextLabel →
      (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (Place.deref P))
      (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
        [Instr.Assgn (Register.R csPrefix.nextReg)
          (Rhs.Borrow kind prot mask (blockSize τ) srcReg (pathOffset f))])).code q' = some instr →
      compProg q' = some instr := by
    intro q' instr h_lt h_code
    refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
    · exact Nat.lt_of_lt_of_le h_lt h_incr2.nextLabel_le
    · rw [h_incr2.code_eq q' h_lt]
      exact h_code
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
  have h_le1 : bS.addr + 0 + pathOffset f + blockSize τ
      ≤ bS.addr + blockSize σb := by
    have h_fit := PathTo.offset_add_size_le f
    show bS.addr + 0 + pathOffset f + blockSize τ ≤ bS.addr + blockSize σb
    simp only [Nat.add_zero, Nat.add_assoc]
    exact Nat.add_le_add_left h_fit _
  have h_ref_tgt' : MSB.ref s_osea.perms (bS.addr + 0 + pathOffset f)
      (blockSize τ) tagS kind prot mask
      = .ok (tgtP1, s_osea.perms.NextTag) := by
    simpa using h_ref_tgt
  have h_run1 := runN_Assgn_Borrow_step compProg s_osea
    (Register.R csPrefix.nextReg) srcReg kind prot mask (blockSize τ)
    (pathOffset f) h_code1 h_entryS h_le1 h_ref_tgt'
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
  have h_pc1 : s_osea.pc + 1
      = (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
          [Instr.Assgn (Register.R csPrefix.nextReg)
            (Rhs.Borrow kind prot mask (blockSize τ) srcReg (pathOffset f))]).nextLabel := by
    simp only [emit, List.length_cons, List.length_nil]
    omega
  obtain ⟨dOut, n1, s_mid, tres, h_dval, h_dclean, h_drun, h_dpc, h_dmem, h_dpsim,
    h_dnt1, h_dnt2, h_dlbs, h_dentry, h_drt, h_dnw, h_dle, h_drange, h_dbelow,
    h_dprm, h_dregmono, h_dlabmono, h_dframe, -⟩ :=
    ptrChain_lowering_sim h_id_a h_wf_t' h_spine RefKind.Mut
      (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
        [Instr.Assgn (Register.R csPrefix.nextReg)
          (Rhs.Borrow kind prot mask (blockSize τ) srcReg (pathOffset f))])
      { s_osea with
          perms := tgtP1,
          reg := oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
            (obseq.TyVal.PTy,
              [Val.Ptr bS.addr (0 + pathOffset f) (blockSize σb) s_osea.perms.NextTag]),
          pc := s_osea.pc + 1 }
      resolved permsD h_dres h_tbd' h_lbs1 h_prb1 h_sms1 h_psim' h_pc1 h_instD
  have h_stmtRun := (h_run0 csPrefix).trans
    (compileStmt_ref_derefdst_projsrc_run kind prot mask h_root h_piS rfl h_dval h_dclean)
  -- the borrow temp crosses the dst lowering (register frame)
  have h_below1 : RegisterBelow
      (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
        [Instr.Assgn (Register.R csPrefix.nextReg)
          (Rhs.Borrow kind prot mask (blockSize τ) srcReg (pathOffset f))]).nextReg
      (Register.R csPrefix.nextReg) := by
    simp only [emit]
    show csPrefix.nextReg < csPrefix.nextReg + 1
    exact Nat.lt_succ_self _
  have h_borrow_mid : oseair.RegMap.lookup s_mid.reg (Register.R csPrefix.nextReg)
      = some (obseq.TyVal.PTy,
          [Val.Ptr bS.addr (0 + pathOffset f) (blockSize σb) s_osea.perms.NextTag]) := by
    rw [h_dframe _ h_below1]
    exact RegMap.lookup_insert_self _ _ _
  -- §8 the store through the loaded tag (BRIDGE 2)
  have h_code3 : compProg s_mid.pc
      = some (Instr.RStore obseq.TyVal.PTy (Register.R csPrefix.nextReg)
          dOut.result.reg) := by
    rw [h_dpc]
    refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
    · rw [h_stmtRun]
      show _ < _ + 1
      exact Nat.lt_succ_self _
    · rw [h_stmtRun]
      have h := emit_code_at_new (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (Place.deref P))
      (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
        [Instr.Assgn (Register.R csPrefix.nextReg)
          (Rhs.Borrow kind prot mask (blockSize τ) srcReg (pathOffset f))]))
        [Instr.RStore obseq.TyVal.PTy (Register.R csPrefix.nextReg) dOut.result.reg]
        (k := 0) (by simp)
      simpa using h
  have h_w := h_step
  simp only [mirlite.writeResolvedPlace] at h_w
  split at h_w
  · simp at h_w
  · rename_i h_nb
    split at h_w
    · rename_i perms2 h_useMut_src
      cases h_w
      obtain ⟨p3, h_useMut_tgt, h_psim3⟩ :=
        sb_write_respects_PermSim h_dpsim h_wf_t' h_drt h_dnw h_useMut_src
      obtain ⟨h_wtp, h_sms'⟩ :=
        writeThroughPtr_sim (τ := obseq.LayoutTy.PtrL τ)
          (s_osea := s_mid) (resolved := resolved)
          "RStore Invalid Regs"
          [mirlite.MemValue.ptrVal bS.addr (bS.addr + pathOffset f - bS.addr)
            (blockSize σb) s_mir.perms.NextTag]
          [Val.Ptr bS.addr (0 + pathOffset f) (blockSize σb) s_osea.perms.NextTag] rfl
          ⟨⟨h_raS, by simp [Nat.add_sub_cancel_left], rfl, h_rt_new, h_nw_new,
            fun k hk => h_domS k hk⟩, trivial⟩
          h_id_a h_dentry h_useMut_tgt
          (by
            show SourceMemSim ρa
              (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag)
              s_mir.mem s_mid.mem
            rw [h_dmem]
            exact h_sms1)
          h_dle
          (fun k hk => by
            have hk0 : k = 0 := by simpa using hk
            subst hk0
            have h_lt : resolved.addr - resolved.allocBase < resolved.allocSize := by
              grind
            obtain ⟨a', ha'⟩ := h_drange _ h_lt
            have h_eq := h_id_a _ _ ha'
            have h_cancel : resolved.allocBase + (resolved.addr - resolved.allocBase)
                = resolved.addr := Nat.add_sub_cancel' h_dle
            grind)
          h_step
      have h_run3 := runN_RStore_step compProg s_mid _
        obseq.TyVal.PTy (Register.R csPrefix.nextReg) dOut.result.reg
        _ _ h_code3 h_borrow_mid h_dentry h_wtp
      have h_runA := (oseair_runN_add 1 n1 s_osea compProg _ h_run1).trans h_drun
      have h_runB := (oseair_runN_add (1 + n1) 1 s_osea compProg _ h_runA).trans h_run3
      -- §9 rebuild the invariant under the extended ρt
      refine ⟨_, _, 1 + n1 + 1, h_incr_t, h_runB, ?_⟩
      refine ⟨CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix,
        ⟨prefixCompileState_succ h_csAt h_stmt h_stmtOut, ?_⟩, ?_, h_sms', h_psim3,
        h_id_a, h_wf_t', ?_, ?_, ?_, ?_⟩
      · show s_mid.pc + 1 = _
        rw [h_dpc, h_stmtRun]
        simp [emit]
      · intro τ'' loc' binding' h_env'
        obtain ⟨reg', base', tag', h_pi', h_entry', h_ra'', h_rt', h_nw', h_dom'⟩ :=
          h_dlbs loc' binding' h_env'
        refine ⟨reg', base', tag', ?_, h_entry', h_ra'', h_rt', h_nw', h_dom'⟩
        rw [h_stmtRun, getPlaceInfo_emit]
        show (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (Place.deref P))
      (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
        [Instr.Assgn (Register.R csPrefix.nextReg)
          (Rhs.Borrow kind prot mask (blockSize τ) srcReg (pathOffset f))])).placeRegMap.lookup loc'.idx.1 = _
        rw [h_dprm]
        exact h_pi'
      · show TagRenameBounded _ perms2.NextTag p3.NextTag
        rw [sb_write_NextTag h_useMut_src, h_dnt1,
          sb_write_NextTag h_useMut_tgt]
        exact TagRenameBounded.mono h_tbd' (Nat.le_refl _) h_dnt2
      · simp only [AllocLockstep, mirlite_writeWordSeq_addrStart,
          oseair_writeWordSeq_addrStart, h_dmem]
        exact h_alloc
      · intro τ'' loc' h_none
        rw [h_stmtRun, getPlaceInfo_emit]
        show (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (Place.deref P))
      (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
        [Instr.Assgn (Register.R csPrefix.nextReg)
          (Rhs.Borrow kind prot mask (blockSize τ) srcReg (pathOffset f))])).placeRegMap.lookup loc'.idx.1 = none
        rw [h_dprm]
        exact h_unmap loc' h_none
      · intro idx reg'' τ'' h_look
        rw [h_stmtRun] at h_look ⊢
        rw [getPlaceInfo_emit] at h_look
        have h_prm2 : (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (Place.deref P))
      (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
        [Instr.Assgn (Register.R csPrefix.nextReg)
          (Rhs.Borrow kind prot mask (blockSize τ) srcReg (pathOffset f))])).placeRegMap = csPrefix.placeRegMap := h_dprm
        have h_cs : getPlaceInfo csPrefix idx = some (reg'', τ'') := by
          show csPrefix.placeRegMap.lookup idx = _
          rw [← h_prm2]
          exact h_look
        refine RegisterBelow.mono ?_ (h_prb _ _ _ h_cs)
        simp only [emit]
        have h_le := h_dregmono
        simp only [emit] at h_le
        omega
    · simp at h_w


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
                cases h_envS : mirlite.Env.lookup s_mir.env srcLoc with
                | some bS =>
                    -- CLOSED: `dst.g := &kind s` at offset 0, `dst` UNBOUND
                    exact ref_projzero_fresh_simulation kind prot mask h_g0 compProg
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
                cases h_envS : mirlite.Env.lookup s_mir.env srcLoc with
                | some bS =>
                    -- CLOSED: `dst.g := &kind s` at nonzero offset, `dst` UNBOUND
                    exact ref_projoffset_fresh_simulation kind prot mask h_g0 compProg
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
                  cases h_envS : mirlite.Env.lookup s_mir.env srcLoc with
                  | some bS =>
                      -- CLOSED: `dst := &kind s.f`, `dst` UNBOUND (regime B-proj)
                      exact ref_fresh_projsrc_simulation kind prot mask compProg
                        h_comp h_inv h_stmt h_envD h_envS h_step
                  | none =>
                      -- `&s.f` of an unbound local: the source errs at resolution
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
          | proj _ _ =>
              exact ref_place_residual kind prot mask compProg h_comp h_inv h_stmt h_step
          | deref _ =>
              exact ref_place_residual kind prot mask compProg h_comp h_inv h_stmt h_step
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
          cases sbase with
          | «local» srcLoc =>
              cases h_envS : mirlite.Env.lookup s_mir.env srcLoc with
              | some bS =>
                  -- CLOSED: `*chain := &kind s.f` — flatten-normalized, TOTAL
                  rw [stepStmt_assign_dstderef_flatten] at h_step
                  obtain ⟨ρt', s_osea', n, h_incr, h_run, h_inv'⟩ :=
                    ref_derefdst_projsrc_simulation (P := flattenPlace P) kind prot mask
                      compProg (PtrChain_flatten_deref P) h_comp h_inv h_stmt
                      (fun cs => compileStmt_assign_derefdst_flatten_run _ cs)
                      (fun cs so h =>
                        compileStmt_assign_derefdst_flatten_value _ cs so h)
                      h_envS h_step
                  exact ⟨ρa, ρt', s_osea', n, AddrRenameIncr.refl ρa, h_incr,
                    h_run, h_inv'⟩
              | none =>
                  -- `&s.f` of an unbound local: the source errs at resolution
                  exfalso
                  simp only [mirlite.stepStmt, mirlite.doAssign] at h_step
                  cases h_prep : mirlite.preparePlaceAssign MSB s_mir
                      (Place.deref P) with
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
          | proj _ _ =>
              exact ref_place_residual kind prot mask compProg h_comp h_inv h_stmt h_step
          | deref _ =>
              exact ref_place_residual kind prot mask compProg h_comp h_inv h_stmt h_step
      | deref _ =>
          exact ref_place_residual kind prot mask compProg h_comp h_inv h_stmt h_step

end obseq3.proof
