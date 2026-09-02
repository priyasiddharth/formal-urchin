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

/-- Canonical pointer CHAINS — the pending-cleanup generalization of
    `LoadSpine`. A chain is a local, a dereference of a chain, or a
    dereference of a SINGLE projection whose base is a chain. Since
    `placeToRegChecked` reassociates consecutive projections into one,
    this covers every alternation of stars and fields except
    proj-of-proj spellings (a separate normalization transfer) and
    proj-TOPPED places (their pending `Die` is the consumer's business).
    Projections appear only directly under a deref: that deref's source
    dereferenceable check is what pays the interior `Borrow`'s bounds
    obligation. -/
inductive PtrChain {Γ : Ctx} : {τ : LayoutTy} → Place Γ τ → Prop
  | base {τ : LayoutTy} (loc : Local Γ τ) : PtrChain (.local loc)
  | deref {τ : LayoutTy} {p : Place Γ (obseq.LayoutTy.PtrL τ)} :
      PtrChain p → PtrChain (.deref p)
  | derefProj {σ τ : LayoutTy} {b : Place Γ σ}
      (f : PathTo σ (obseq.LayoutTy.PtrL τ)) :
      PtrChain b → PtrChain (.deref (.proj b f))

/-- Chains never carry a projection at the top — the shape
    `placeToRegChecked_proj_root_eq` asks for. -/
theorem PtrChain.not_proj {Γ : Ctx} {σ : LayoutTy} {b : Place Γ σ}
    (h : PtrChain b) :
    ∀ (σ' : LayoutTy) (bb : Place Γ σ') (q : PathTo σ' σ),
      b = bb.proj q → False := by
  intro σ' bb q h_eq
  cases h <;> simp_all

/-- The pure resolver agrees with a successful access-resolution: the
    access variant only ADDS the SB reads and the deref-OOB check, so
    when it succeeds, `resolvePlace?` computes the same `PlaceRes`.
    Connects the overlapping-assignment guard (stated with the pure
    resolver) to the ranges the access resolution establishes. -/
theorem resolvePlace?_of_resolveAcc
    {Γ : Ctx} {τ : LayoutTy} {M : PermissionModel}
    {s : mirlite.State M Γ} :
    ∀ {p : Place Γ τ} {r : mirlite.PlaceRes} {perms : M.State},
      mirlite.resolvePlaceAcc M s p = .ok (r, perms) →
      mirlite.resolvePlace? s p = some r := by
  intro p
  induction p with
  | «local» loc =>
      intro r perms h
      cases h_env : mirlite.Env.lookup s.env loc with
      | none => simp [mirlite.resolvePlaceAcc, h_env] at h
      | some binding =>
          simp only [mirlite.resolvePlaceAcc, h_env, Except.ok.injEq,
            Prod.mk.injEq] at h
          simp only [mirlite.resolvePlace?, h_env]
          rw [h.1]
  | proj base path ih =>
      intro r perms h
      simp only [mirlite.resolvePlaceAcc] at h
      cases h_b : mirlite.resolvePlaceAcc M s base with
      | error e => simp [h_b] at h
      | ok pr =>
          obtain ⟨res, perms'⟩ := pr
          simp only [h_b, Except.ok.injEq, Prod.mk.injEq] at h
          simp only [mirlite.resolvePlace?, ih h_b]
          rw [h.1]
  | deref ptrPlace ih =>
      intro r perms h
      simp only [mirlite.resolvePlaceAcc] at h
      cases h_b : mirlite.resolvePlaceAcc M s ptrPlace with
      | error e => simp [h_b] at h
      | ok pr =>
          obtain ⟨ptrRes, perms'⟩ := pr
          simp only [h_b] at h
          split at h
          · simp at h
          · cases h_rd : M.read perms' ptrRes.addr 1 ptrRes.tag with
            | error e => simp [h_rd] at h
            | ok perms'' =>
                simp only [h_rd] at h
                cases h_find : mirlite.Mem.find? s.mem ptrRes.addr with
                | none => simp [h_find] at h
                | some mv =>
                    cases mv with
                    | undef => simp [h_find] at h
                    | word w => simp [h_find] at h
                    | ptrVal b o sz t =>
                        simp only [h_find, Except.ok.injEq, Prod.mk.injEq] at h
                        simp only [mirlite.resolvePlace?, ih h_b, h_find]
                        rw [h.1]

/-! ## Flattening: nested projections compose, on BOTH machines

The compiler reassociates `.proj (.proj b q) p` to `.proj b (q.append
p)` (GEP of exactly the final field). These lemmas give the SOURCE-side
mirror: resolution and preparation cannot tell the two spellings apart,
and a ZERO-offset projection resolves exactly as its base. -/

theorem resolvePlace?_proj_assoc
    {Γ : Ctx} {σ1 σ2 τ : LayoutTy} {M : PermissionModel}
    {s : mirlite.State M Γ}
    (b : Place Γ σ1) (q : PathTo σ1 σ2) (p : PathTo σ2 τ) :
    mirlite.resolvePlace? s (.proj (.proj b q) p)
      = mirlite.resolvePlace? s (.proj b (q.append p)) := by
  simp only [mirlite.resolvePlace?]
  cases mirlite.resolvePlace? s b with
  | none => rfl
  | some res =>
      simp only [PathTo.offset_append]
      rw [Nat.add_assoc]

theorem resolvePlaceAcc_proj_assoc
    {Γ : Ctx} {σ1 σ2 τ : LayoutTy} {M : PermissionModel}
    {s : mirlite.State M Γ}
    (b : Place Γ σ1) (q : PathTo σ1 σ2) (p : PathTo σ2 τ) :
    mirlite.resolvePlaceAcc M s (.proj (.proj b q) p)
      = mirlite.resolvePlaceAcc M s (.proj b (q.append p)) := by
  simp only [mirlite.resolvePlaceAcc]
  cases mirlite.resolvePlaceAcc M s b with
  | error e => rfl
  | ok pr =>
      simp only [PathTo.offset_append]
      rw [Nat.add_assoc]

theorem preparePlaceAssign_proj_assoc
    {Γ : Ctx} {σ1 σ2 τ : LayoutTy} {M : PermissionModel}
    {s : mirlite.State M Γ}
    (b : Place Γ σ1) (q : PathTo σ1 σ2) (p : PathTo σ2 τ) :
    mirlite.preparePlaceAssign M s (.proj (.proj b q) p)
      = mirlite.preparePlaceAssign M s (.proj b (q.append p)) := by
  simp only [mirlite.preparePlaceAssign, resolvePlace?_proj_assoc b q p]
  cases mirlite.resolvePlace? s (.proj b (q.append p)) with
  | none => simp [mirlite.allocateRoot]
  | some r => rfl

theorem resolvePlaceAcc_proj_base_ok
    {Γ : Ctx} {σ τ : LayoutTy} {M : PermissionModel}
    {s : mirlite.State M Γ} {b : Place Γ σ} {path : PathTo σ τ}
    {r : mirlite.PlaceRes} {p : M.State}
    (h : mirlite.resolvePlaceAcc M s b = .ok (r, p)) :
    mirlite.resolvePlaceAcc M s (.proj b path)
      = .ok ({ r with addr := r.addr + PathTo.offset path }, p) := by
  simp [mirlite.resolvePlaceAcc, h]

theorem resolvePlaceAcc_proj_base_err
    {Γ : Ctx} {σ τ : LayoutTy} {M : PermissionModel}
    {s : mirlite.State M Γ} {b : Place Γ σ} {path : PathTo σ τ}
    {e : String}
    (h : mirlite.resolvePlaceAcc M s b = .error e) :
    mirlite.resolvePlaceAcc M s (.proj b path) = .error e := by
  simp [mirlite.resolvePlaceAcc, h]

/-- A deref lowering leaves no cleanup: the `Load` consumes the pointer
    place's own cleanup and the result is a plain register. Like
    `PtrChain.placeToRegChecked_placeRegMap`, the standalone form is
    needed BEFORE the mother lemma can be invoked — the compiled
    fragment mentions the source's cleanup. -/
theorem placeToRegChecked_local_cleanup {Γ : Ctx} {τ : LayoutTy}
    {kind : RefKind} {loc : Local Γ τ} {cs : CompilerState}
    {out : ResultWithEvidence PtrResult (PlaceToRegEvidence kind (.local loc))}
    (h : CheckedCompilerM.value (placeToRegChecked kind (.local loc)) cs
      = Except.ok out) :
    out.result.cleanup = [] := by
  simp only [CheckedCompilerM.value, CompilerM.value, placeToRegChecked] at h
  split at h
  · cases h; rfl
  · simp at h

theorem placeToRegChecked_deref_cleanup {Γ : Ctx} {τ : LayoutTy}
    {P : Place Γ (obseq.LayoutTy.PtrL τ)} {kind : RefKind} {cs : CompilerState}
    {out : ResultWithEvidence PtrResult (PlaceToRegEvidence kind (.deref P))}
    (h : CheckedCompilerM.value (placeToRegChecked kind (.deref P)) cs
      = Except.ok out) :
    out.result.cleanup = [] := by
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
  rw [h_bindD] at h
  cases hx : CheckedCompilerM.value (placeToRegChecked RefKind.Shared P) cs with
  | error e =>
      exfalso
      simp only [CheckedCompilerM.value_bind, hx] at h
      simp at h
  | ok o =>
      simp only [CheckedCompilerM.value_bind, CheckedCompilerM.value_lift,
        CheckedCompilerM.value_pure, hx] at h
      simp only [CompilerM.value, freshRegM, freshReg, emitM] at h
      cases h
      rfl

/-- A CHAIN's lowering never touches `placeRegMap`: it only LOOKS UP
    locals. The mother lemma carries this as an output conjunct, but the
    standalone form is needed BEFORE the mother can be invoked — to
    transfer `PlaceInputsMapped` past a lowering, which is what licenses
    the SECOND lowering in a two-place statement (a non-local
    destination). Induction on the chain, not on the place: the chain
    grammar has no proj-of-proj, so the recursion is structural. -/
theorem PtrChain.placeToRegChecked_placeRegMap {Γ : Ctx} {τ : LayoutTy}
    {p : Place Γ τ} (h : PtrChain p) :
    ∀ (kind : RefKind) (cs : CompilerState),
      (CheckedCompilerM.run (placeToRegChecked kind p) cs).placeRegMap
        = cs.placeRegMap := by
  induction h with
  | base loc =>
      intro kind cs
      simp only [placeToRegChecked, CheckedCompilerM.run, CompilerM.run]
      split <;> rfl
  | deref h_p ih =>
      intro kind cs
      rename_i τ' pp
      rw [show placeToRegChecked (Γ := Γ) kind (Place.deref pp)
          = (do
              let ptrOut ← placeToRegChecked RefKind.Shared pp
              let ptrRes := ptrOut.result
              let loadedReg ← CheckedCompilerM.lift freshRegM
              let _ ← CheckedCompilerM.lift
                (emitM [Instr.Assgn loadedReg (Rhs.Load obseq.TyVal.PTy ptrRes.reg)])
              let _ ← CheckedCompilerM.lift (emitM (cleanupInstrs ptrRes.cleanup))
              pure {
                result := { reg := loadedReg, cleanup := [] },
                evidence := PlaceToRegEvidence.deref pp ptrRes loadedReg ptrOut.evidence
              }) from by simp only [placeToRegChecked]]
      rw [CheckedCompilerM.run_bind]
      cases h_v : CheckedCompilerM.value (placeToRegChecked RefKind.Shared pp) cs with
      | error e => exact ih RefKind.Shared cs
      | ok a =>
          simp only [CheckedCompilerM.run_bind, CheckedCompilerM.run_lift,
            CheckedCompilerM.value_lift, CheckedCompilerM.run_pure]
          simp only [CompilerM.run, freshRegM, freshReg, emitM, emit]
          exact ih RefKind.Shared cs
  | derefProj f h_b ih =>
      intro kind cs
      rename_i σ τ' b
      have h_inner : ∀ (k : RefKind) (cs' : CompilerState),
          (CheckedCompilerM.run (placeToRegChecked k (Place.proj b f)) cs').placeRegMap
            = cs'.placeRegMap := by
        intro k cs'
        rw [placeToRegChecked_proj_root_eq f (h_b.not_proj), CheckedCompilerM.run_bind]
        cases h_v : CheckedCompilerM.value (placeToRegChecked k b) cs' with
        | error e => exact ih k cs'
        | ok a =>
            by_cases h_o : pathOffset f = 0
            · simp only [h_o, dif_pos, CheckedCompilerM.run_pure]
              exact ih k cs'
            · simp only [dif_neg h_o, CheckedCompilerM.run_bind,
                CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
                CheckedCompilerM.run_pure]
              simp only [CompilerM.run, freshRegM, freshReg, emitM, emit]
              exact ih k cs'
      rw [show placeToRegChecked (Γ := Γ) kind (Place.deref (Place.proj b f))
          = (do
              let ptrOut ← placeToRegChecked RefKind.Shared (Place.proj b f)
              let ptrRes := ptrOut.result
              let loadedReg ← CheckedCompilerM.lift freshRegM
              let _ ← CheckedCompilerM.lift
                (emitM [Instr.Assgn loadedReg (Rhs.Load obseq.TyVal.PTy ptrRes.reg)])
              let _ ← CheckedCompilerM.lift (emitM (cleanupInstrs ptrRes.cleanup))
              pure {
                result := { reg := loadedReg, cleanup := [] },
                evidence := PlaceToRegEvidence.deref (Place.proj b f) ptrRes loadedReg
                  ptrOut.evidence
              }) from by simp only [placeToRegChecked]]
      rw [CheckedCompilerM.run_bind]
      cases h_v : CheckedCompilerM.value
          (placeToRegChecked RefKind.Shared (Place.proj b f)) cs with
      | error e => exact h_inner RefKind.Shared cs
      | ok a =>
          simp only [CheckedCompilerM.run_bind, CheckedCompilerM.run_lift,
            CheckedCompilerM.value_lift, CheckedCompilerM.run_pure]
          simp only [CompilerM.run, freshRegM, freshReg, emitM, emit]
          exact h_inner RefKind.Shared cs

/-! ## Full flattening: EVERY place normalizes into the chain grammar

`flattenPlace` recursively reassociates nested projections. Its output
never stacks two projections, so a flattened place is a `PtrChain` or a
single projection over one — and a flattened DEREF place is always a
chain. Resolution, preparation and the compiled lowering cannot tell a
place from its flattening apart. -/

/-- Attach a path to an already-flattened base, composing if the base is
    itself a projection. -/
def projInto {Γ : Ctx} : {σ τ : LayoutTy} → Place Γ σ → PathTo σ τ → Place Γ τ
  | _, _, .proj b q, p => .proj b (q.append p)
  | _, _, b, p => .proj b p

/-- Recursively reassociate every nested projection. -/
def flattenPlace {Γ : Ctx} : {τ : LayoutTy} → Place Γ τ → Place Γ τ
  | _, .local l => .local l
  | _, .deref p => .deref (flattenPlace p)
  | _, .proj b path => projInto (flattenPlace b) path

theorem resolvePlaceAcc_projInto
    {Γ : Ctx} {σ τ : LayoutTy} {M : PermissionModel}
    {s : mirlite.State M Γ} (b : Place Γ σ) (p : PathTo σ τ) :
    mirlite.resolvePlaceAcc M s (projInto b p)
      = mirlite.resolvePlaceAcc M s (.proj b p) := by
  cases b with
  | proj b' q => exact resolvePlaceAcc_proj_assoc b' q p |>.symm ▸ rfl
  | «local» l => rfl
  | deref pp => rfl

theorem resolvePlaceAcc_flatten
    {Γ : Ctx} {τ : LayoutTy} {M : PermissionModel}
    {s : mirlite.State M Γ} (p : Place Γ τ) :
    mirlite.resolvePlaceAcc M s (flattenPlace p)
      = mirlite.resolvePlaceAcc M s p := by
  induction p with
  | «local» l => rfl
  | deref pp ih =>
      show mirlite.resolvePlaceAcc M s (.deref (flattenPlace pp)) = _
      simp only [mirlite.resolvePlaceAcc, ih]
  | proj b path ih =>
      show mirlite.resolvePlaceAcc M s (projInto (flattenPlace b) path) = _
      rw [resolvePlaceAcc_projInto]
      simp only [mirlite.resolvePlaceAcc, ih]

theorem resolvePlace?_projInto
    {Γ : Ctx} {σ τ : LayoutTy} {M : PermissionModel}
    {s : mirlite.State M Γ} (b : Place Γ σ) (p : PathTo σ τ) :
    mirlite.resolvePlace? s (projInto b p)
      = mirlite.resolvePlace? s (.proj b p) := by
  cases b with
  | proj b' q => exact resolvePlace?_proj_assoc (M := M) b' q p |>.symm ▸ rfl
  | «local» l => rfl
  | deref pp => rfl

theorem resolvePlace?_flatten
    {Γ : Ctx} {τ : LayoutTy} {M : PermissionModel}
    {s : mirlite.State M Γ} (p : Place Γ τ) :
    mirlite.resolvePlace? (M := M) s (flattenPlace p)
      = mirlite.resolvePlace? s p := by
  induction p with
  | «local» l => rfl
  | deref pp ih =>
      show mirlite.resolvePlace? s (.deref (flattenPlace pp)) = _
      simp only [mirlite.resolvePlace?, ih]
  | proj b path ih =>
      show mirlite.resolvePlace? s (projInto (flattenPlace b) path) = _
      rw [resolvePlace?_projInto]
      simp only [mirlite.resolvePlace?, ih]

theorem allocateRoot_projInto
    {Γ : Ctx} {σ τ : LayoutTy} {M : PermissionModel}
    {s : mirlite.State M Γ} (b : Place Γ σ) (p : PathTo σ τ) :
    mirlite.allocateRoot M s (projInto b p) = mirlite.allocateRoot M s b := by
  cases b with
  | proj b' q => rfl
  | «local» l => rfl
  | deref pp => rfl

theorem allocateRoot_flatten
    {Γ : Ctx} {τ : LayoutTy} {M : PermissionModel}
    {s : mirlite.State M Γ} (p : Place Γ τ) :
    mirlite.allocateRoot M s (flattenPlace p) = mirlite.allocateRoot M s p := by
  induction p with
  | «local» l => rfl
  | deref pp ih => rfl
  | proj b path ih =>
      show mirlite.allocateRoot M s (projInto (flattenPlace b) path) = _
      rw [allocateRoot_projInto, ih]
      rfl

theorem preparePlaceAssign_flatten
    {Γ : Ctx} {τ : LayoutTy} {M : PermissionModel}
    {s : mirlite.State M Γ} (p : Place Γ τ) :
    mirlite.preparePlaceAssign M s (flattenPlace p)
      = mirlite.preparePlaceAssign M s p := by
  simp only [mirlite.preparePlaceAssign, resolvePlace?_flatten, allocateRoot_flatten]

theorem ensurePlaceRoot_projInto
    {Γ : Ctx} {σ τ : LayoutTy} (b : Place Γ σ) (p : PathTo σ τ) :
    ensurePlaceRoot (projInto b p) = ensurePlaceRoot b := by
  cases b with
  | proj b' q => rfl
  | «local» l => rfl
  | deref pp => rfl

theorem ensurePlaceRoot_flatten
    {Γ : Ctx} {τ : LayoutTy} (p : Place Γ τ) :
    ensurePlaceRoot (flattenPlace p) = ensurePlaceRoot p := by
  induction p with
  | «local» l => rfl
  | deref pp ih =>
      show ensurePlaceRoot (flattenPlace pp) = _
      exact ih
  | proj b path ih =>
      show ensurePlaceRoot (projInto (flattenPlace b) path) = _
      rw [ensurePlaceRoot_projInto, ih]
      rfl

/-- A flattened place is a chain, or one projection over a chain. -/
theorem flatten_chainish {Γ : Ctx} : {τ : LayoutTy} → (p : Place Γ τ) →
    PtrChain (flattenPlace p) ∨
    ∃ (σ : LayoutTy) (b : Place Γ σ) (path : PathTo σ τ),
      flattenPlace p = .proj b path ∧ PtrChain b
  | _, .local l => .inl (.base l)
  | _, .deref p => by
      rcases flatten_chainish p with h | ⟨σ, b, path, h_eq, h_b⟩
      · exact .inl (.deref h)
      · exact .inl (by
          show PtrChain (.deref (flattenPlace p))
          rw [h_eq]
          exact .derefProj path h_b)
  | _, .proj b path => by
      rcases flatten_chainish b with h | ⟨σ, b', q, h_eq, h_b'⟩
      · refine .inr ⟨_, flattenPlace b, path, ?_, h⟩
        show projInto (flattenPlace b) path = _
        have h_np := PtrChain.not_proj h
        cases h_flat : flattenPlace b with
        | proj bb qq => exact absurd h_flat (fun hh => h_np _ bb qq hh)
        | «local» l => rfl
        | deref pp => rfl
      · refine .inr ⟨_, b', q.append path, ?_, h_b'⟩
        show projInto (flattenPlace b) path = _
        rw [h_eq]
        rfl

/-- A flattened PROJECTION is always exactly one projection over a
    canonical chain (the `.inr` half of `flatten_chainish`, with the
    impossible `.inl` half discharged: `projInto` always produces a
    projection). -/
theorem flatten_proj_chainish {Γ : Ctx} {σ τ : LayoutTy}
    (b : Place Γ σ) (p : PathTo σ τ) :
    ∃ (σ' : LayoutTy) (bb : Place Γ σ') (q : PathTo σ' τ),
      flattenPlace (Place.proj b p) = .proj bb q ∧ PtrChain bb := by
  rcases flatten_chainish b with h | ⟨σ'', b', q, h_eq, h_b'⟩
  · refine ⟨_, flattenPlace b, p, ?_, h⟩
    show projInto (flattenPlace b) p = _
    have h_np := PtrChain.not_proj h
    cases h_flat : flattenPlace b with
    | proj bb qq => exact absurd h_flat (fun hh => h_np _ bb qq hh)
    | «local» l => rfl
    | deref pp => rfl
  · refine ⟨_, b', q.append p, ?_, h_b'⟩
    show projInto (flattenPlace b) p = _
    rw [h_eq]
    rfl

/-- Every flattened DEREF place is a canonical chain — the fact that
    retires the non-chain fallbacks. -/
theorem PtrChain_flatten_deref {Γ : Ctx} {τ : LayoutTy}
    (p : Place Γ (obseq.LayoutTy.PtrL τ)) :
    PtrChain (Place.deref (flattenPlace p)) := by
  rcases flatten_chainish p with h | ⟨σ, b, path, h_eq, h_b⟩
  · exact .deref h
  · rw [h_eq]
    exact .derefProj path h_b

theorem PathTo.append_assoc {a b c d : LayoutTy}
    (x : PathTo a b) (y : PathTo b c) (z : PathTo c d) :
    (x.append y).append z = x.append (y.append z) := by
  induction x with
  | nil => rfl
  | field idx tail ih => simp [PathTo.append, ih]

theorem projInto_projInto {Γ : Ctx} {ρ σ τ : LayoutTy}
    (x : Place Γ ρ) (q : PathTo ρ σ) (p : PathTo σ τ) :
    projInto (projInto x q) p = projInto x (q.append p) := by
  cases x with
  | proj bb qq =>
      show Place.proj bb ((qq.append q).append p)
        = Place.proj bb (qq.append (q.append p))
      rw [PathTo.append_assoc]
  | «local» l => rfl
  | deref pp => rfl

/-- The compiled lowering cannot tell a place from its flattening apart:
    the run is EQUAL and the value's RESULT component (register +
    cleanup — the evidence differs by reassociation wrappers) agrees. -/
theorem placeToRegChecked_flatten_agree {Γ : Ctx} :
    {τ : LayoutTy} → (p : Place Γ τ) → (kind : RefKind) → (cs : CompilerState) →
    CheckedCompilerM.run (placeToRegChecked kind (flattenPlace p)) cs
      = CheckedCompilerM.run (placeToRegChecked kind p) cs ∧
    (CheckedCompilerM.value (placeToRegChecked kind (flattenPlace p)) cs).map
        (fun o => o.result)
      = (CheckedCompilerM.value (placeToRegChecked kind p) cs).map
        (fun o => o.result)
  | _, .local l, _, _ => ⟨rfl, rfl⟩
  | _, .proj (.local l) path, _, _ => ⟨rfl, rfl⟩
  | _, .proj (.proj b q) path, kind, cs => by
      have h_flat : flattenPlace (Place.proj (Place.proj b q) path)
          = flattenPlace (Place.proj b (q.append path)) := by
        show projInto (projInto (flattenPlace b) q) path
          = projInto (flattenPlace b) (q.append path)
        exact projInto_projInto _ q path
      obtain ⟨ihr, ihv⟩ :=
        placeToRegChecked_flatten_agree (Place.proj b (q.append path)) kind cs
      rw [h_flat]
      refine ⟨?_, ?_⟩
      · rw [ihr, placeToRegChecked_proj_assoc_eq q path]
        simp only [CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
          CheckedCompilerM.run_pure, CheckedCompilerM.value_pure]
        split <;> rfl
      · rw [ihv, placeToRegChecked_proj_assoc_eq q path]
        simp only [CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
          CheckedCompilerM.run_pure, CheckedCompilerM.value_pure]
        cases h : CheckedCompilerM.value
            (placeToRegChecked kind (Place.proj b (q.append path))) cs <;>
          simp [Except.map]
  | _, .proj (.deref pp) path, kind, cs => by
      obtain ⟨ihr, ihv⟩ := placeToRegChecked_flatten_agree (Place.deref pp) kind cs
      rw [show flattenPlace (Place.deref pp) = Place.deref (flattenPlace pp)
        from rfl] at ihr ihv
      have h_fl : flattenPlace (Place.proj (Place.deref pp) path)
          = Place.proj (Place.deref (flattenPlace pp)) path := rfl
      rw [h_fl]
      have h_npF : ∀ (σ' : LayoutTy) (bb : Place Γ σ') (qq : PathTo σ' _),
          Place.deref (flattenPlace pp) = bb.proj qq → False := by
        intro _ bb qq h
        cases h
      have h_npO : ∀ (σ' : LayoutTy) (bb : Place Γ σ') (qq : PathTo σ' _),
          Place.deref pp = bb.proj qq → False := by
        intro _ bb qq h
        cases h
      rw [placeToRegChecked_proj_root_eq (kind := kind) path h_npF,
        placeToRegChecked_proj_root_eq (kind := kind) path h_npO]
      cases hF : CheckedCompilerM.value
          (placeToRegChecked kind (Place.deref (flattenPlace pp))) cs with
      | error eF =>
          cases hO : CheckedCompilerM.value
              (placeToRegChecked kind (Place.deref pp)) cs with
          | error eO =>
              have h_e : eF = eO := by
                rw [hF, hO] at ihv
                simpa [Except.map] using ihv
              subst h_e
              constructor <;>
                simp only [csMonad, hF, hO, ihr, Except.map]
          | ok oO =>
              exfalso
              rw [hF, hO] at ihv
              simp [Except.map] at ihv
      | ok oF =>
          cases hO : CheckedCompilerM.value
              (placeToRegChecked kind (Place.deref pp)) cs with
          | error eO =>
              exfalso
              rw [hF, hO] at ihv
              simp [Except.map] at ihv
          | ok oO =>
              have h_res : oF.result = oO.result := by
                rw [hF, hO] at ihv
                simpa [Except.map] using ihv
              constructor <;>
                simp only [csMonad, hF, hO] <;>
                split <;>
                simp [csRun, cleanupInstrs, ihr, h_res, Except.map]
  | _, .deref pp, kind, cs => by
      obtain ⟨ihr, ihv⟩ := placeToRegChecked_flatten_agree pp RefKind.Shared cs
      have h_fl : flattenPlace (Place.deref pp) = Place.deref (flattenPlace pp) := rfl
      rw [h_fl]
      have h_bF : placeToRegChecked (Γ := Γ) kind (.deref (flattenPlace pp))
          = (do
              let ptrOut ← placeToRegChecked RefKind.Shared (flattenPlace pp)
              let ptrRes := ptrOut.result
              let loadedReg ← CheckedCompilerM.lift freshRegM
              let _ ← CheckedCompilerM.lift
                (emitM [Instr.Assgn loadedReg (Rhs.Load obseq.TyVal.PTy ptrRes.reg)])
              let _ ← CheckedCompilerM.lift (emitM (cleanupInstrs ptrRes.cleanup))
              pure {
                result := { reg := loadedReg, cleanup := [] },
                evidence := PlaceToRegEvidence.deref (flattenPlace pp) ptrRes
                  loadedReg ptrOut.evidence
              }) := by simp only [placeToRegChecked]
      have h_bO : placeToRegChecked (Γ := Γ) kind (.deref pp)
          = (do
              let ptrOut ← placeToRegChecked RefKind.Shared pp
              let ptrRes := ptrOut.result
              let loadedReg ← CheckedCompilerM.lift freshRegM
              let _ ← CheckedCompilerM.lift
                (emitM [Instr.Assgn loadedReg (Rhs.Load obseq.TyVal.PTy ptrRes.reg)])
              let _ ← CheckedCompilerM.lift (emitM (cleanupInstrs ptrRes.cleanup))
              pure {
                result := { reg := loadedReg, cleanup := [] },
                evidence := PlaceToRegEvidence.deref pp ptrRes loadedReg
                  ptrOut.evidence
              }) := by simp only [placeToRegChecked]
      rw [h_bF, h_bO]
      cases hF : CheckedCompilerM.value
          (placeToRegChecked RefKind.Shared (flattenPlace pp)) cs with
      | error eF =>
          cases hO : CheckedCompilerM.value
              (placeToRegChecked RefKind.Shared pp) cs with
          | error eO =>
              have h_e : eF = eO := by
                rw [hF, hO] at ihv
                simpa [Except.map] using ihv
              subst h_e
              constructor <;>
                simp only [csMonad, hF, hO, ihr, Except.map]
          | ok oO =>
              exfalso
              rw [hF, hO] at ihv
              simp [Except.map] at ihv
      | ok oF =>
          cases hO : CheckedCompilerM.value
              (placeToRegChecked RefKind.Shared pp) cs with
          | error eO =>
              exfalso
              rw [hF, hO] at ihv
              simp [Except.map] at ihv
          | ok oO =>
              have h_res : oF.result = oO.result := by
                rw [hF, hO] at ihv
                simpa [Except.map] using ihv
              constructor <;>
                simp [csRun, CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
                  CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
                  CheckedCompilerM.run_pure, CheckedCompilerM.value_pure, hF, hO, ihr, h_res,
                  cleanupInstrs, Except.map]
termination_by τ p kind cs => p.depth
decreasing_by all_goals (simp [Place.depth]; try omega)


/-- The BORROW lowering cannot tell a place from its flattening apart
    either. `placeToBorrowRegChecked` carries its own reassociating arm
    for `.proj (.proj b q) p` — the compiler already flattens nested
    projection borrows so that `&mut s.1.0` does not route through a
    wide `Mut` borrow of `s.1` — so this is the ref-side mirror of
    `placeToRegChecked_flatten_agree`, and the two share every case but
    that one. -/
theorem placeToBorrowRegChecked_flatten_agree {Γ : Ctx}
    (kind : RefKind) (prot : Bool) (mask : List Bool) :
    {τ : LayoutTy} → (p : Place Γ τ) → (cs : CompilerState) →
    CheckedCompilerM.run (placeToBorrowRegChecked kind prot mask (flattenPlace p)) cs
      = CheckedCompilerM.run (placeToBorrowRegChecked kind prot mask p) cs ∧
    (CheckedCompilerM.value (placeToBorrowRegChecked kind prot mask (flattenPlace p)) cs).map
        (fun o => o.result)
      = (CheckedCompilerM.value (placeToBorrowRegChecked kind prot mask p) cs).map
        (fun o => o.result)
  | _, .local l, _ => ⟨rfl, rfl⟩
  | _, .proj (.local l) path, _ => ⟨rfl, rfl⟩
  | _, .proj (.proj b q) path, cs => by
      have h_flat : flattenPlace (Place.proj (Place.proj b q) path)
          = flattenPlace (Place.proj b (q.append path)) := by
        show projInto (projInto (flattenPlace b) q) path
          = projInto (flattenPlace b) (q.append path)
        exact projInto_projInto _ q path
      obtain ⟨ihr, ihv⟩ :=
        placeToBorrowRegChecked_flatten_agree kind prot mask
          (Place.proj b (q.append path)) cs
      rw [h_flat]
      refine ⟨?_, ?_⟩
      · rw [ihr]
        show _ = CheckedCompilerM.run
          (placeToBorrowRegChecked kind prot mask (Place.proj (Place.proj b q) path)) cs
        simp only [placeToBorrowRegChecked, CheckedCompilerM.run_bind,
          CheckedCompilerM.value_bind, CheckedCompilerM.run_pure,
          CheckedCompilerM.value_pure]
        split <;> rfl
      · rw [ihv]
        show _ = (CheckedCompilerM.value
          (placeToBorrowRegChecked kind prot mask
            (Place.proj (Place.proj b q) path)) cs).map (fun o => o.result)
        simp only [placeToBorrowRegChecked, CheckedCompilerM.run_bind,
          CheckedCompilerM.value_bind, CheckedCompilerM.run_pure,
          CheckedCompilerM.value_pure]
        cases h : CheckedCompilerM.value
            (placeToBorrowRegChecked kind prot mask (Place.proj b (q.append path))) cs <;>
          simp [Except.map]
  | _, .proj (.deref pp) path, cs => by
      obtain ⟨ihr, ihv⟩ := placeToRegChecked_flatten_agree (Place.deref pp) kind cs
      rw [show flattenPlace (Place.deref pp) = Place.deref (flattenPlace pp)
        from rfl] at ihr ihv
      have h_fl : flattenPlace (Place.proj (Place.deref pp) path)
          = Place.proj (Place.deref (flattenPlace pp)) path := rfl
      rw [h_fl]
      cases hF : CheckedCompilerM.value
          (placeToRegChecked kind (Place.deref (flattenPlace pp))) cs with
      | error eF =>
          cases hO : CheckedCompilerM.value
              (placeToRegChecked kind (Place.deref pp)) cs with
          | error eO =>
              have h_e : eF = eO := by
                rw [hF, hO] at ihv
                simpa [Except.map] using ihv
              subst h_e
              constructor <;>
                simp only [csMonad, placeToBorrowRegChecked, hF, hO, ihr, Except.map]
          | ok oO =>
              exfalso
              rw [hF, hO] at ihv
              simp [Except.map] at ihv
      | ok oF =>
          cases hO : CheckedCompilerM.value
              (placeToRegChecked kind (Place.deref pp)) cs with
          | error eO =>
              exfalso
              rw [hF, hO] at ihv
              simp [Except.map] at ihv
          | ok oO =>
              have h_res : oF.result = oO.result := by
                rw [hF, hO] at ihv
                simpa [Except.map] using ihv
              constructor <;>
                simp [csRun, placeToBorrowRegChecked, CheckedCompilerM.run_bind,
                  CheckedCompilerM.value_bind, CheckedCompilerM.run_lift,
                  CheckedCompilerM.value_lift, CheckedCompilerM.run_pure,
                  CheckedCompilerM.value_pure, hF, hO, ihr, h_res, cleanupInstrs, Except.map]
  | _, .deref pp, cs => by
      obtain ⟨ihr, ihv⟩ := placeToRegChecked_flatten_agree pp RefKind.Shared cs
      have h_fl : flattenPlace (Place.deref pp) = Place.deref (flattenPlace pp) := rfl
      rw [h_fl]
      cases hF : CheckedCompilerM.value
          (placeToRegChecked RefKind.Shared (flattenPlace pp)) cs with
      | error eF =>
          cases hO : CheckedCompilerM.value
              (placeToRegChecked RefKind.Shared pp) cs with
          | error eO =>
              have h_e : eF = eO := by
                rw [hF, hO] at ihv
                simpa [Except.map] using ihv
              subst h_e
              constructor <;>
                simp only [csMonad, placeToBorrowRegChecked, hF, hO, ihr, Except.map]
          | ok oO =>
              exfalso
              rw [hF, hO] at ihv
              simp [Except.map] at ihv
      | ok oF =>
          cases hO : CheckedCompilerM.value
              (placeToRegChecked RefKind.Shared pp) cs with
          | error eO =>
              exfalso
              rw [hF, hO] at ihv
              simp [Except.map] at ihv
          | ok oO =>
              have h_res : oF.result = oO.result := by
                rw [hF, hO] at ihv
                simpa [Except.map] using ihv
              constructor <;>
                simp [csRun, placeToBorrowRegChecked, CheckedCompilerM.run_bind,
                  CheckedCompilerM.value_bind, CheckedCompilerM.run_lift,
                  CheckedCompilerM.value_lift, CheckedCompilerM.run_pure,
                  CheckedCompilerM.value_pure, hF, hO, ihr, h_res, cleanupInstrs, Except.map]
  termination_by τ p cs => p.depth
  decreasing_by all_goals (simp [Place.depth]; try omega)

/-- The SOURCE cannot tell the two spellings of a nested-projection
    assignment apart either: `doAssign` consults the destination only
    through `preparePlaceAssign` and `resolvePlaceAcc`, both of which
    compose offsets. The step-level mirror of
    `compileStmt_assign_proj_assoc_run`. -/
theorem stepStmt_assign_proj_assoc
    {Γ : Ctx} {σ1 σ2 τ : LayoutTy} {M : PermissionModel}
    {s : mirlite.State M Γ}
    (b : Place Γ σ1) (q : PathTo σ1 σ2) (p : PathTo σ2 τ)
    (rhs : RExpr Γ τ) :
    mirlite.stepStmt M s (.assign (.proj (.proj b q) p) rhs)
      = mirlite.stepStmt M s (.assign (.proj b (q.append p)) rhs) := by
  show mirlite.doAssign M s (.proj (.proj b q) p) rhs
    = mirlite.doAssign M s (.proj b (q.append p)) rhs
  simp only [mirlite.doAssign, preparePlaceAssign_proj_assoc b q p,
    resolvePlaceAcc_proj_assoc b q p]

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

/-- Pointer-CHAIN lowering simulation — the pending-cleanup
    generalization of the retired `loadSpine_lowering_sim` (subsumed
    2026-08-29). Interior projections
    lower to a contiguous `Borrow(Shared); Load; Die` triple whose net
    stack effect BRIDGE 1S cancels to the parent pointer-cell read the
    source performs at that deref, so the conclusion still reports an
    empty cleanup and `PermSim` at the UNextended rename — the phantom
    tags die. Only the target counter conjunct weakens to `≤`.
    Original doc: Given a `CompilerInv`-shaped
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
theorem ptrChain_lowering_sim
    {Γ : Ctx}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir : mirlite.State MSB Γ}
    {compProg : oseair.Prog}
    (h_id_a : IdentityOnDomain ρa) (h_wf_t : TagRenameWF ρt)
    {τ : LayoutTy} {p : Place Γ τ}
    (h_chain : PtrChain p) :
    ∀ (kind : RefKind) (cs : CompilerState) (s_osea : oseair.State MSB)
      (resolved : mirlite.PlaceRes) (permsD : MSB.State),
      mirlite.resolvePlaceAcc MSB s_mir p = .ok (resolved, permsD) →
      TagRenameBounded ρt s_mir.perms.NextTag s_osea.perms.NextTag →
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
        s_osea.perms.NextTag ≤ s_osea'.perms.NextTag ∧
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
        cs.nextLabel ≤ (CheckedCompilerM.run (placeToRegChecked kind p) cs).nextLabel ∧
        (∀ r, RegisterBelow cs.nextReg r →
          oseair.RegMap.lookup s_osea'.reg r = oseair.RegMap.lookup s_osea.reg r) ∧
        ρa resolved.allocBase = some resolved.allocBase := by
  induction h_chain with
  | base loc =>
      intro kind cs s_osea resolved permsD h_res h_tbd h_lbs h_prb h_sms h_psim h_pc h_inst
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
        by simp [oseair.runN], ?_, rfl, h_psim, rfl, Nat.le_refl _, h_lbs, ?_, h_rt, h_nw,
        Nat.le_refl _, ?_, ?_, ?_, ?_, ?_, fun _ _ => rfl, h_ra⟩
      · rw [h_prun]; exact h_pc
      · rw [h_pres, Nat.sub_self]
        exact h_entry
      · intro k hk
        exact h_dom k hk
      · rw [h_prun, h_pres]
        exact h_prb _ _ _ h_pi
      · rw [h_prun]
      · rw [h_prun]
        exact Nat.le_refl _
      · rw [h_prun]
        exact Nat.le_refl _
  | deref h_chainQ ih =>
      rename_i τ' q
      intro kind cs s_osea resolved permsD h_res h_tbd h_lbs h_prb h_sms h_psim h_pc h_inst
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
              have h_cancel : qRes.allocBase + (qRes.addr - qRes.allocBase) = qRes.addr := by grind
              have h_off : qRes.addr - qRes.allocBase < qRes.allocSize := by grind
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
                h_qrange, h_qbelow, h_qprm, h_qregmono, h_qlabmono, h_qframe, -⟩ :=
                ih RefKind.Shared cs s_osea qRes permsQ h_qres h_tbd h_lbs h_prb h_sms
                  h_psim h_pc h_instQ
              -- concrete run/value of this level
              have h_runD : CheckedCompilerM.run (placeToRegChecked kind (.deref q)) cs
                  = emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared q) cs) with
                        nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared q) cs).nextReg + 1 }
                      [Instr.Assgn
                        (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared q) cs).nextReg)
                        (Rhs.Load obseq.TyVal.PTy qOut.result.reg)] := by
                rw [h_bind]
                simp only [csMonad, h_qval]
                simp [csRun, cleanupInstrs, h_qclean, emit_nil]
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
                simp only [csMonad, h_qval]
                simp [csRun, cleanupInstrs, h_qclean, emit_nil]
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
                ?_, ?_, ?_, ?_, ?_, h_b⟩
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
              · -- target counter: monotone through the `Load`'s read
                show s_osea.perms.NextTag ≤ p2.NextTag
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
              · -- register frame: this level writes only the fresh loadedReg
                intro r h_below
                have h_ne : r ≠ Register.R
                    (CheckedCompilerM.run (placeToRegChecked RefKind.Shared q) cs).nextReg := by
                  cases r with
                  | R m =>
                      have h_lt : m < cs.nextReg := h_below
                      grind
                show oseair.RegMap.lookup (oseair.RegMap.insert s_mid.reg _ _) r = _
                rw [RegMap.lookup_insert_ne _ h_ne]
                exact h_qframe r h_below

  | derefProj f h_chainB ih =>
      rename_i σb τ' b
      intro kind cs s_osea resolved permsD h_res h_tbd h_lbs h_prb h_sms h_psim h_pc h_inst
      -- one resolveAcc level: the proj is a pure offset add, then this
      -- deref's bounds check, pointer-cell read and content lookup
      simp only [mirlite.resolvePlaceAcc] at h_res
      cases h_bres : mirlite.resolvePlaceAcc MSB s_mir b with
      | error e => simp [h_bres] at h_res
      | ok pr =>
        obtain ⟨bRes, permsB⟩ := pr
        simp only [h_bres] at h_res
        by_cases h_qb : bRes.addr + PathTo.offset f < bRes.allocBase ∨
            bRes.addr + PathTo.offset f ≥ bRes.allocBase + bRes.allocSize
        · rw [if_pos h_qb] at h_res
          exact absurd h_res (by simp)
        · rw [if_neg h_qb] at h_res
          cases h_qread : MSB.read permsB (bRes.addr + PathTo.offset f) 1 bRes.tag with
          | error e => simp [h_qread] at h_res
          | ok permsQ =>
            simp only [h_qread] at h_res
            cases h_qfind : mirlite.Mem.find? s_mir.mem (bRes.addr + PathTo.offset f) with
            | none => simp [h_qfind] at h_res
            | some mv =>
              cases mv with
              | undef => simp [h_qfind] at h_res
              | word w => simp [h_qfind] at h_res
              | ptrVal vb vo vsz vt =>
              simp only [h_qfind, Except.ok.injEq, Prod.mk.injEq] at h_res
              obtain ⟨h_r1, h_r2⟩ := h_res
              subst h_r1
              subst h_r2
              -- this level's compiled shape: proj (root not a proj), then deref
              have h_np := PtrChain.not_proj h_chainB
              have h_bindP :=
                placeToRegChecked_proj_root_eq (kind := RefKind.Shared) f h_np
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
                          ptrOut.evidence }) := by
                simp only [placeToRegChecked]
              have h_incrP : StateIncr
                  (CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs)
                  (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (.proj b f)) cs) := by
                rw [h_bindP, CheckedCompilerM.run_bind]
                split
                · exact CheckedCompilerM.incr _ _
                · exact StateIncr.refl _
              have h_incrD : StateIncr
                  (CheckedCompilerM.run (placeToRegChecked RefKind.Shared (.proj b f)) cs)
                  (CheckedCompilerM.run (placeToRegChecked kind (.deref (.proj b f))) cs) := by
                rw [h_bindD, CheckedCompilerM.run_bind]
                split
                · exact CheckedCompilerM.incr _ _
                · exact StateIncr.refl _
              have h_instB : ∀ q' instr,
                  q' < (CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs).nextLabel →
                  (CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs).code q' = some instr →
                  compProg q' = some instr := by
                intro q' instr h_lt h_code
                have h_i := StateIncr.trans h_incrP h_incrD
                refine h_inst q' instr (Nat.lt_of_lt_of_le h_lt h_i.nextLabel_le) ?_
                rw [h_i.code_eq q' h_lt]
                exact h_code
              obtain ⟨bOut, n1, s_mid, btag, h_bval, h_bclean, h_brun, h_bpc, h_bmem,
                h_bpsim, h_bnt1, h_bnt2, h_blbs, h_bentry, h_brt, h_bnw, h_ble,
                h_brange, h_bbelow, h_bprm, h_bregmono, h_blabmono, h_bframe, -⟩ :=
                ih RefKind.Shared cs s_osea bRes permsB h_bres h_tbd h_lbs h_prb h_sms
                  h_psim h_pc h_instB
              have h_po : pathOffset f = PathTo.offset f := rfl
              have h_one : blockSize (obseq.LayoutTy.PtrL τ') = 1 := rfl
              have h_cancel : bRes.allocBase + (bRes.addr - bRes.allocBase) = bRes.addr := by grind
              by_cases h_off : pathOffset f = 0
              · -- offset ZERO: the projection is a no-op on both machines;
                -- this is the plain deref step with a shifted-by-zero address
                have h_z : PathTo.offset f = 0 := h_off
                rw [h_z, Nat.add_zero] at h_qread h_qfind h_qb
                have h_runD : CheckedCompilerM.run
                    (placeToRegChecked kind (.deref (.proj b f))) cs
                    = emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs) with
                          nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs).nextReg + 1 }
                        [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs).nextReg)
                          (Rhs.Load obseq.TyVal.PTy bOut.result.reg)] := by
                  rw [h_bindD, h_bindP]
                  simp only [csMonad, h_bval, h_off, dif_pos]
                  simp [csRun, cleanupInstrs, h_bclean, emit_nil]
                have h_valD : CheckedCompilerM.value
                    (placeToRegChecked kind (.deref (.proj b f))) cs
                    = Except.ok {
                        result := {
                          reg := Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs).nextReg,
                          cleanup := [] },
                        evidence := PlaceToRegEvidence.deref (.proj b f) bOut.result
                          (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs).nextReg)
                          (PlaceToRegEvidence.projZero b f bOut.result bOut.evidence h_off) } := by
                  rw [h_bindD, h_bindP]
                  simp only [csMonad, h_bval, h_off, dif_pos]
                  simp [csRun, cleanupInstrs, h_bclean, emit_nil]
                obtain ⟨p2, h_read_tgt, h_psim2⟩ :=
                  sb_read_respects_PermSim h_bpsim h_wf_t h_brt h_bnw h_qread
                have h_read_tgt' : MSB.read s_mid.perms
                    (bRes.allocBase + (bRes.addr - bRes.allocBase)) 1 btag = .ok p2 := by
                  rw [h_cancel]
                  exact h_read_tgt
                have h_offP : bRes.addr - bRes.allocBase < bRes.allocSize := by grind
                obtain ⟨addr', value', h_ra', h_find_tgt, h_mvs⟩ := h_sms _ _ h_qfind
                have h_addr' : addr' = bRes.addr := (h_id_a _ _ h_ra').symm
                subst h_addr'
                cases value' with
                | Undef => exact h_mvs.elim
                | Dat _ => exact h_mvs.elim
                | Ptr vb2 vo2 vs2 vt2 =>
                obtain ⟨h_b, h_o, h_s, h_t, h_tnw, h_range⟩ := h_mvs
                have h_vb2 : vb2 = vb := (h_id_a _ _ h_b).symm
                subst h_vb2
                subst h_o
                subst h_s
                have h_code1 : compProg s_mid.pc = some (Instr.Assgn
                    (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs).nextReg)
                    (Rhs.Load obseq.TyVal.PTy bOut.result.reg)) := by
                  rw [h_bpc]
                  refine h_inst _ _ ?_ ?_
                  · rw [h_runD]
                    show _ < _ + 1
                    exact Nat.lt_succ_self _
                  · rw [h_runD]
                    have h := emit_code_at_new
                      { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs) with
                          nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs).nextReg + 1 }
                      [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs).nextReg)
                        (Rhs.Load obseq.TyVal.PTy bOut.result.reg)]
                      (k := 0) (by simp)
                    simpa using h
                have h_run1 := runN_Assgn_Load_ptr_step compProg s_mid
                  (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs).nextReg)
                  bOut.result.reg obseq.TyVal.PTy h_code1 h_bentry h_offP h_read_tgt'
                have h_rws : oseair.readWordSeq s_mid.mem
                    (bRes.allocBase + (bRes.addr - bRes.allocBase))
                    (obseq.typeSize obseq.TyVal.PTy) = [Val.Ptr vb2 vo2 vs2 vt2] := by
                  rw [h_cancel]
                  show oseair.readWordSeq s_mid.mem bRes.addr 1 = _
                  rw [h_bmem]
                  simp [oseair.readWordSeq, h_find_tgt]
                refine ⟨_, n1 + 1, _, vt2, h_valD, rfl,
                  (oseair_runN_add n1 1 s_osea compProg s_mid h_brun).trans h_run1,
                  ?_, ?_, h_psim2, ?_, ?_, ?_, ?_, h_t, h_tnw, Nat.le_add_right vb2 vo2, ?_,
                  ?_, ?_, ?_, ?_, ?_, h_b⟩
                · show s_mid.pc + 1 = _
                  rw [h_bpc, h_runD]
                  simp [emit]
                · show s_mid.mem = s_osea.mem
                  exact h_bmem
                · rw [sb_read_NextTag h_qread]
                  exact h_bnt1
                · show s_osea.perms.NextTag ≤ p2.NextTag
                  rw [sb_read_NextTag h_read_tgt]
                  exact h_bnt2
                · exact LocalBindingSim.insert_fresh_reg h_blbs h_prb h_bregmono rfl
                · show oseair.RegMap.lookup _ _ = _
                  rw [RegMap.lookup_insert_self, h_rws, Nat.add_sub_cancel_left]
                · intro k hk
                  exact h_range k hk
                · rw [h_runD]
                  show _ < _ + 1
                  exact Nat.lt_succ_self _
                · rw [h_runD]
                  exact h_bprm
                · rw [h_runD]
                  exact Nat.le_trans h_bregmono (Nat.le_succ _)
                · rw [h_runD]
                  show cs.nextLabel ≤ _ + 1
                  exact Nat.le_trans h_blabmono (Nat.le_succ _)
                · intro r h_below
                  have h_ne : r ≠ Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs).nextReg := by
                    cases r with
                    | R m =>
                        have h_lt : m < cs.nextReg := h_below
                        grind
                  show oseair.RegMap.lookup (oseair.RegMap.insert s_mid.reg _ _) r = _
                  rw [RegMap.lookup_insert_ne _ h_ne]
                  exact h_bframe r h_below
              · -- offset NONZERO: `Borrow(Shared); Load; Die` — the BRIDGE 1S
                -- level. The Borrow's bound is paid by this deref's SOURCE
                -- dereferenceable check; the triple's net stack effect is the
                -- parent pointer-cell read the source performs here.
                have h_runD : CheckedCompilerM.run
                    (placeToRegChecked kind (.deref (.proj b f))) cs
                    = emit (emit
                        { (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs) with
                              nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs).nextReg + 1 }
                            [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs).nextReg)
                              (Rhs.Borrow RefKind.Shared false []
                                (blockSize (obseq.LayoutTy.PtrL τ'))
                                bOut.result.reg (pathOffset f))]) with
                          nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs).nextReg + 1 + 1 }
                        [Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs).nextReg + 1))
                          (Rhs.Load obseq.TyVal.PTy (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs).nextReg))])
                      [Instr.Die (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs).nextReg)
                        (blockSize (obseq.LayoutTy.PtrL τ'))] := by
                  rw [h_bindD, h_bindP]
                  simp only [csMonad, h_bval, h_off, dif_neg]
                  simp [csRun, cleanupInstrs, borrowRhs, h_bclean, emit_nil]
                  simp [emit]
                have h_valD : CheckedCompilerM.value
                    (placeToRegChecked kind (.deref (.proj b f))) cs
                    = Except.ok {
                        result := {
                          reg := Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs).nextReg + 1),
                          cleanup := [] },
                        evidence := PlaceToRegEvidence.deref (.proj b f)
                          { reg := Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs).nextReg,
                             cleanup := bOut.result.cleanup ++ [(Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs).nextReg,
                               blockSize (obseq.LayoutTy.PtrL τ'))] }
                          (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs).nextReg + 1))
                          (PlaceToRegEvidence.projOffset b f bOut.result
                            (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs).nextReg) bOut.evidence h_off) } := by
                  rw [h_bindD, h_bindP]
                  simp only [csMonad, h_bval, h_off, dif_neg]
                  simp [csRun, cleanupInstrs, borrowRhs, h_bclean, emit_nil]
                  simp [emit]
                  rfl
                -- §the parent read transports; the target's Shared retag succeeds
                obtain ⟨p2, h_read_tgt, h_psim2⟩ :=
                  sb_read_respects_PermSim h_bpsim h_wf_t h_brt h_bnw h_qread
                obtain ⟨q1, h_ref_tgt⟩ := sb_ref_Shared_ok_of_sb_read_ok h_read_tgt
                have h_tbd_mid : TagRenameBounded ρt permsB.NextTag s_mid.perms.NextTag := by
                  rw [h_bnt1]
                  exact TagRenameBounded.mono h_tbd (Nat.le_refl _) h_bnt2
                have h_unprot := freshTag_not_protected h_bpsim h_tbd_mid
                have h0 : wildcardTag < s_mid.perms.NextTag := (h_tbd_mid _ _ h_wf_t.2).2
                have h_ntw : (s_mid.perms.NextTag == wildcardTag) = false := by grind
                -- BRIDGE 1S: ref(Shared); read(t'); die(t') ≡ the parent read
                obtain ⟨q2, q3, qAcc', h_rd1, h_die1, h_rd2, h_sm, h_ex, h_pf, h_ntle⟩ :=
                  sb_ref_read_die_cancels h_ntw h_unprot h_ref_tgt
                have h_qAcc : qAcc' = p2 := by grind
                subst h_qAcc
                -- §execute the Borrow: bound from the source's deref check
                have h_le1 : bRes.allocBase + (bRes.addr - bRes.allocBase) + pathOffset f
                    + blockSize (obseq.LayoutTy.PtrL τ') ≤ bRes.allocBase + bRes.allocSize := by grind
                have h_ref_tgt' : MSB.ref s_mid.perms
                    (bRes.allocBase + (bRes.addr - bRes.allocBase) + pathOffset f)
                    (blockSize (obseq.LayoutTy.PtrL τ')) btag RefKind.Shared false []
                    = .ok (q1, s_mid.perms.NextTag) := by
                  rw [h_cancel, h_one, h_po]
                  exact h_ref_tgt
                have h_code1 : compProg s_mid.pc
                    = some (Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs).nextReg)
                        (Rhs.Borrow RefKind.Shared false []
                          (blockSize (obseq.LayoutTy.PtrL τ'))
                          bOut.result.reg (pathOffset f))) := by
                  rw [h_bpc]
                  refine h_inst _ _ ?_ ?_
                  · rw [h_runD]
                    simp only [emit, List.length_cons, List.length_nil]
                    omega
                  · rw [h_runD]
                    rw [emit_code_lt_nextLabel _ _ (by
                      simp only [emit, List.length_cons, List.length_nil]; omega)]
                    rw [emit_code_lt_nextLabel _ _ (by
                      simp only [emit, List.length_cons, List.length_nil]; omega)]
                    have h := emit_code_at_new
                      { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs) with
                          nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs).nextReg + 1 }
                      [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs).nextReg)
                        (Rhs.Borrow RefKind.Shared false []
                          (blockSize (obseq.LayoutTy.PtrL τ'))
                          bOut.result.reg (pathOffset f))]
                      (k := 0) (by simp)
                    simpa using h
                have h_run1 := runN_Assgn_Borrow_step compProg s_mid
                  (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs).nextReg)
                  bOut.result.reg RefKind.Shared false []
                  (blockSize (obseq.LayoutTy.PtrL τ')) (pathOffset f)
                  h_code1 h_bentry h_le1 h_ref_tgt'
                -- §execute the Load through the fresh tag (BRIDGE 1S phase 2)
                have h_rd1' : MSB.read q1
                    (bRes.allocBase + ((bRes.addr - bRes.allocBase) + pathOffset f)) 1
                    s_mid.perms.NextTag = .ok q2 := by
                  rw [h_po, ← Nat.add_assoc, h_cancel]
                  exact h_rd1
                have h_offlt : (bRes.addr - bRes.allocBase) + pathOffset f
                    < bRes.allocSize := by grind
                have h_entry_tmp : PtrRegisterEntry
                    (oseair.RegMap.insert s_mid.reg
                      (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs).nextReg)
                      (obseq.TyVal.PTy, [Val.Ptr bRes.allocBase
                        ((bRes.addr - bRes.allocBase) + pathOffset f)
                        bRes.allocSize s_mid.perms.NextTag]))
                    (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs).nextReg)
                    bRes.allocBase ((bRes.addr - bRes.allocBase) + pathOffset f)
                    bRes.allocSize s_mid.perms.NextTag :=
                  RegMap.lookup_insert_self _ _ _
                have h_code2 : compProg (s_mid.pc + 1)
                    = some (Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs).nextReg + 1))
                        (Rhs.Load obseq.TyVal.PTy (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs).nextReg))) := by
                  refine h_inst _ _ ?_ ?_
                  · rw [h_runD, h_bpc]
                    simp only [emit, List.length_cons, List.length_nil]
                    omega
                  · rw [h_runD, h_bpc]
                    rw [emit_code_lt_nextLabel _ _ (by
                      simp only [emit, List.length_cons, List.length_nil]; omega)]
                    have h := emit_code_at_new
                      { (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs) with
                            nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs).nextReg + 1 }
                          [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs).nextReg)
                            (Rhs.Borrow RefKind.Shared false []
                              (blockSize (obseq.LayoutTy.PtrL τ'))
                              bOut.result.reg (pathOffset f))]) with
                          nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs).nextReg + 1 + 1 }
                      [Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs).nextReg + 1))
                        (Rhs.Load obseq.TyVal.PTy (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs).nextReg))]
                      (k := 0) (by simp)
                    simpa [emit] using h
                have h_run2 := runN_Assgn_Load_ptr_step compProg
                  { s_mid with
                      perms := q1,
                      reg := oseair.RegMap.insert s_mid.reg
                        (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs).nextReg)
                        (obseq.TyVal.PTy, [Val.Ptr bRes.allocBase
                          ((bRes.addr - bRes.allocBase) + pathOffset f)
                          bRes.allocSize s_mid.perms.NextTag]),
                      pc := s_mid.pc + 1 }
                  (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs).nextReg + 1))
                  (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs).nextReg)
                  obseq.TyVal.PTy h_code2 h_entry_tmp h_offlt h_rd1'
                -- the loaded cell holds the ρ-renamed stored pointer
                obtain ⟨addr', value', h_ra', h_find_tgt, h_mvs⟩ := h_sms _ _ h_qfind
                have h_addr' : addr' = bRes.addr + PathTo.offset f := (h_id_a _ _ h_ra').symm
                subst h_addr'
                cases value' with
                | Undef => exact h_mvs.elim
                | Dat _ => exact h_mvs.elim
                | Ptr vb2 vo2 vs2 vt2 =>
                obtain ⟨h_b, h_o, h_s, h_t, h_tnw, h_range⟩ := h_mvs
                have h_vb2 : vb2 = vb := (h_id_a _ _ h_b).symm
                subst h_vb2
                subst h_o
                subst h_s
                have h_rws : oseair.readWordSeq s_mid.mem
                    (bRes.allocBase + ((bRes.addr - bRes.allocBase) + pathOffset f))
                    (obseq.typeSize obseq.TyVal.PTy) = [Val.Ptr vb2 vo2 vs2 vt2] := by
                  rw [h_po, ← Nat.add_assoc, h_cancel]
                  show oseair.readWordSeq s_mid.mem (bRes.addr + PathTo.offset f) 1 = _
                  rw [h_bmem]
                  simp [oseair.readWordSeq, h_find_tgt]
                -- §execute the Die (BRIDGE 1S phase 3) on the temp
                have h_die1' : MSB.die q2
                    (bRes.allocBase + ((bRes.addr - bRes.allocBase) + pathOffset f))
                    (blockSize (obseq.LayoutTy.PtrL τ')) s_mid.perms.NextTag = .ok q3 := by
                  rw [h_one, h_po, ← Nat.add_assoc, h_cancel]
                  exact h_die1
                have h_regne : Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs).nextReg
                    ≠ Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs).nextReg + 1) := by
                  simp only [ne_eq, Register.R.injEq]
                  omega
                have h_entry_tmp2 : PtrRegisterEntry
                    (oseair.RegMap.insert
                      (oseair.RegMap.insert s_mid.reg
                        (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs).nextReg)
                        (obseq.TyVal.PTy, [Val.Ptr bRes.allocBase
                          ((bRes.addr - bRes.allocBase) + pathOffset f)
                          bRes.allocSize s_mid.perms.NextTag]))
                      (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs).nextReg + 1))
                      (obseq.TyVal.PTy, oseair.readWordSeq s_mid.mem
                        (bRes.allocBase + ((bRes.addr - bRes.allocBase) + pathOffset f))
                        (obseq.typeSize obseq.TyVal.PTy)))
                    (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs).nextReg)
                    bRes.allocBase ((bRes.addr - bRes.allocBase) + pathOffset f)
                    bRes.allocSize s_mid.perms.NextTag := by
                  show oseair.RegMap.lookup _ _ = _
                  rw [RegMap.lookup_insert_ne _ h_regne]
                  exact h_entry_tmp
                have h_code3 : compProg (s_mid.pc + 1 + 1)
                    = some (Instr.Die (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs).nextReg)
                        (blockSize (obseq.LayoutTy.PtrL τ'))) := by
                  refine h_inst _ _ ?_ ?_
                  · rw [h_runD, h_bpc]
                    simp only [emit, List.length_cons, List.length_nil]
                    omega
                  · rw [h_runD, h_bpc]
                    have h := emit_code_at_new
                      (emit { (emit { (CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs) with
                            nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs).nextReg + 1 }
                          [Instr.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs).nextReg)
                            (Rhs.Borrow RefKind.Shared false []
                              (blockSize (obseq.LayoutTy.PtrL τ'))
                              bOut.result.reg (pathOffset f))]) with
                          nextReg := (CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs).nextReg + 1 + 1 }
                        [Instr.Assgn (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs).nextReg + 1))
                          (Rhs.Load obseq.TyVal.PTy (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs).nextReg))])
                      [Instr.Die (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs).nextReg)
                        (blockSize (obseq.LayoutTy.PtrL τ'))]
                      (k := 0) (by simp)
                    simpa [emit] using h
                have h_run3 := runN_Die_step compProg
                  { s_mid with
                      perms := q2,
                      reg := oseair.RegMap.insert
                        (oseair.RegMap.insert s_mid.reg
                          (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs).nextReg)
                          (obseq.TyVal.PTy, [Val.Ptr bRes.allocBase
                            ((bRes.addr - bRes.allocBase) + pathOffset f)
                            bRes.allocSize s_mid.perms.NextTag]))
                        (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs).nextReg + 1))
                        (obseq.TyVal.PTy, oseair.readWordSeq s_mid.mem
                          (bRes.allocBase + ((bRes.addr - bRes.allocBase) + pathOffset f))
                          (obseq.typeSize obseq.TyVal.PTy)),
                      pc := s_mid.pc + 1 + 1 }
                  (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs).nextReg)
                  (blockSize (obseq.LayoutTy.PtrL τ'))
                  h_code3 h_entry_tmp2 h_die1'
                have h_runA := (oseair_runN_add n1 1 s_osea compProg s_mid h_brun).trans h_run1
                have h_runB := (oseair_runN_add (n1 + 1) 1 s_osea compProg _ h_runA).trans h_run2
                have h_runC := (oseair_runN_add (n1 + 1 + 1) 1 s_osea compProg _ h_runB).trans h_run3
                -- §conclusion: the minted tag DIED — `PermSim` at the same ρt
                refine ⟨_, n1 + 1 + 1 + 1, _, vt2, h_valD, rfl, h_runC,
                  ?_, ?_, ?_, ?_, ?_, ?_, ?_, h_t, h_tnw, Nat.le_add_right vb2 vo2, ?_,
                  ?_, ?_, ?_, ?_, ?_, h_b⟩
                · show s_mid.pc + 1 + 1 + 1 = _
                  rw [h_bpc, h_runD]
                  simp [emit]
                · show s_mid.mem = s_osea.mem
                  exact h_bmem
                · exact ⟨by rw [h_sm]; exact h_psim2.1,
                    by rw [h_pf]; exact h_psim2.2.1,
                    by rw [h_ex]; exact h_psim2.2.2.1,
                    Nat.le_trans h_psim2.2.2.2 h_ntle⟩
                · rw [sb_read_NextTag h_qread]
                  exact h_bnt1
                · show s_osea.perms.NextTag ≤ q3.NextTag
                  have h_p2nt : qAcc'.NextTag = s_mid.perms.NextTag :=
                    sb_read_NextTag h_read_tgt
                  grind
                · have h_lbs1 : LocalBindingSim ρa ρt s_mir.env
                      { s_mid with
                          perms := q1,
                          reg := oseair.RegMap.insert s_mid.reg
                            (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs).nextReg)
                            (obseq.TyVal.PTy, [Val.Ptr bRes.allocBase
                              (bRes.addr - bRes.allocBase + pathOffset f)
                              bRes.allocSize s_mid.perms.NextTag]),
                          pc := s_mid.pc + 1 } cs :=
                    LocalBindingSim.insert_fresh_reg h_blbs h_prb h_bregmono rfl
                  have h_lbs2 : LocalBindingSim ρa ρt s_mir.env
                      { s_mid with
                          perms := q2,
                          reg := oseair.RegMap.insert
                            (oseair.RegMap.insert s_mid.reg
                              (Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs).nextReg)
                              (obseq.TyVal.PTy, [Val.Ptr bRes.allocBase
                                (bRes.addr - bRes.allocBase + pathOffset f)
                                bRes.allocSize s_mid.perms.NextTag]))
                            (Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs).nextReg + 1))
                            (obseq.TyVal.PTy, oseair.readWordSeq s_mid.mem
                              (bRes.allocBase + (bRes.addr - bRes.allocBase + pathOffset f))
                              (obseq.typeSize obseq.TyVal.PTy)),
                          pc := s_mid.pc + 1 + 1 } cs :=
                    LocalBindingSim.insert_fresh_reg h_lbs1 h_prb
                      (Nat.le_trans h_bregmono (Nat.le_succ _)) rfl
                  intro τ'' loc' binding' h_env'
                  exact h_lbs2 loc' binding' h_env'
                · show oseair.RegMap.lookup _ _ = _
                  rw [RegMap.lookup_insert_self, h_rws]
                  show some (obseq.TyVal.PTy, [Val.Ptr vb2 vo2 vs2 vt2])
                    = some (obseq.TyVal.PTy, [Val.Ptr vb2 (vb2 + vo2 - vb2) vs2 vt2])
                  rw [Nat.add_sub_cancel_left]
                · intro k hk
                  exact h_range k hk
                · rw [h_runD]
                  simp only [emit]
                  show (CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs).nextReg + 1 < (CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs).nextReg + 1 + 1
                  exact Nat.lt_succ_self _
                · rw [h_runD]
                  exact h_bprm
                · rw [h_runD]
                  exact Nat.le_trans h_bregmono
                    (Nat.le_trans (Nat.le_succ _) (Nat.le_succ _))
                · rw [h_runD]
                  have h_lab := h_blabmono
                  simp only [emit, List.length_cons, List.length_nil]
                  omega
                · intro r h_below
                  have h_ne1 : r ≠ Register.R (CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs).nextReg := by
                    cases r with
                    | R m =>
                        have h_lt : m < cs.nextReg := h_below
                        grind
                  have h_ne2 : r ≠ Register.R ((CheckedCompilerM.run (placeToRegChecked RefKind.Shared b) cs).nextReg + 1) := by
                    cases r with
                    | R m =>
                        have h_lt : m < cs.nextReg := h_below
                        grind
                  show oseair.RegMap.lookup _ r = _
                  rw [RegMap.lookup_insert_ne _ h_ne2, RegMap.lookup_insert_ne _ h_ne1]
                  exact h_bframe r h_below

/-! ## Statement-level flatten congruences: the SOURCE cannot tell a
    statement from its dst/src-flattened spelling apart. -/

/-- FULLY dst-generic: the source cannot tell a statement from its
    dst-flattened spelling apart, for ANY dst and ANY rhs. -/
theorem stepStmt_assign_dstflatten
    {Γ : Ctx} {τ : LayoutTy} {M : PermissionModel}
    (s : mirlite.State M Γ)
    (dst : Place Γ τ) (rhs : RExpr Γ τ) :
    mirlite.stepStmt M s (.assign dst rhs)
      = mirlite.stepStmt M s (.assign (flattenPlace dst) rhs) := by
  have h1 : ∀ st : mirlite.State M Γ,
      mirlite.resolvePlaceAcc M st (flattenPlace dst)
        = mirlite.resolvePlaceAcc M st dst :=
    fun st => resolvePlaceAcc_flatten dst
  have h2 : ∀ st : mirlite.State M Γ,
      mirlite.resolvePlace? st (flattenPlace dst)
        = mirlite.resolvePlace? (M := M) st dst :=
    fun st => resolvePlace?_flatten dst
  have h3 : mirlite.preparePlaceAssign M s (flattenPlace dst)
      = mirlite.preparePlaceAssign M s dst :=
    preparePlaceAssign_flatten dst
  show mirlite.doAssign M s _ rhs = mirlite.doAssign M s _ rhs
  simp only [mirlite.doAssign, h1, h2, h3]

theorem stepStmt_assign_dst_proj_assoc
    {Γ : Ctx} {σ1 σ2 τ : LayoutTy} {M : PermissionModel}
    (s : mirlite.State M Γ)
    (b : Place Γ σ1) (q : PathTo σ1 σ2) (p : PathTo σ2 τ) (rhs : RExpr Γ τ) :
    mirlite.stepStmt M s (.assign (.proj (.proj b q) p) rhs)
      = mirlite.stepStmt M s (.assign (.proj b (q.append p)) rhs) := by
  have h1 : ∀ st : mirlite.State M Γ,
      mirlite.resolvePlaceAcc M st (Place.proj (Place.proj b q) p)
        = mirlite.resolvePlaceAcc M st (Place.proj b (q.append p)) :=
    fun st => resolvePlaceAcc_proj_assoc b q p
  have h2 : ∀ st : mirlite.State M Γ,
      mirlite.resolvePlace? st (Place.proj (Place.proj b q) p)
        = mirlite.resolvePlace? (M := M) st (Place.proj b (q.append p)) :=
    fun st => resolvePlace?_proj_assoc b q p
  have h3 : mirlite.preparePlaceAssign M s (Place.proj (Place.proj b q) p)
      = mirlite.preparePlaceAssign M s (Place.proj b (q.append p)) :=
    preparePlaceAssign_proj_assoc b q p
  show mirlite.doAssign M s _ rhs = mirlite.doAssign M s _ rhs
  simp only [mirlite.doAssign, h1, h2, h3]

theorem stepStmt_assign_dstderef_flatten
    {Γ : Ctx} {τ : LayoutTy} {M : PermissionModel}
    (s : mirlite.State M Γ)
    (P : Place Γ (obseq.LayoutTy.PtrL τ)) (rhs : RExpr Γ τ) :
    mirlite.stepStmt M s (.assign (.deref P) rhs)
      = mirlite.stepStmt M s (.assign (.deref (flattenPlace P)) rhs) :=
  stepStmt_assign_dstflatten s (.deref P) rhs

theorem stepStmt_assign_copysrc_flatten
    {Γ : Ctx} {τ : LayoutTy} {M : PermissionModel}
    (s : mirlite.State M Γ) (dst : Place Γ τ)
    (P : Place Γ (obseq.LayoutTy.PtrL τ)) :
    mirlite.stepStmt M s (.assign dst (.copy (.deref P)))
      = mirlite.stepStmt M s (.assign dst (.copy (.deref (flattenPlace P)))) := by
  have h1 : ∀ st : mirlite.State M Γ,
      mirlite.resolvePlaceAcc M st (Place.deref (flattenPlace P))
        = mirlite.resolvePlaceAcc M st (Place.deref P) :=
    fun st => resolvePlaceAcc_flatten (Place.deref P)
  have h2 : ∀ st : mirlite.State M Γ,
      mirlite.resolvePlace? st (Place.deref (flattenPlace P))
        = mirlite.resolvePlace? (M := M) st (Place.deref P) :=
    fun st => resolvePlace?_flatten (Place.deref P)
  show mirlite.doAssign M s dst _ = mirlite.doAssign M s dst _
  simp only [mirlite.doAssign, mirlite.evalRExpr, h1, h2]

/-- Source-side flatten congruence for a copy SOURCE of any shape (the
    deref case above is the instance the D→L arm uses). -/
theorem stepStmt_assign_copysrc_anyflatten
    {Γ : Ctx} {τ : LayoutTy} {M : PermissionModel}
    (s : mirlite.State M Γ) (dst : Place Γ τ) (src : Place Γ τ) :
    mirlite.stepStmt M s (.assign dst (.copy src))
      = mirlite.stepStmt M s (.assign dst (.copy (flattenPlace src))) := by
  have h1 : ∀ st : mirlite.State M Γ,
      mirlite.resolvePlaceAcc M st (flattenPlace src)
        = mirlite.resolvePlaceAcc M st src :=
    fun st => resolvePlaceAcc_flatten src
  have h2 : ∀ st : mirlite.State M Γ,
      mirlite.resolvePlace? st (flattenPlace src)
        = mirlite.resolvePlace? (M := M) st src :=
    fun st => resolvePlace?_flatten src
  show mirlite.doAssign M s dst _ = mirlite.doAssign M s dst _
  simp only [mirlite.doAssign, mirlite.evalRExpr, h1, h2]

theorem stepStmt_assign_refsrc_flatten
    {Γ : Ctx} {τ : LayoutTy} {M : PermissionModel}
    (s : mirlite.State M Γ) (dst : Place Γ (obseq.LayoutTy.PtrL τ))
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (P : Place Γ (obseq.LayoutTy.PtrL τ)) :
    mirlite.stepStmt M s (.assign dst (.ref kind prot mask (.deref P)))
      = mirlite.stepStmt M s
          (.assign dst (.ref kind prot mask (.deref (flattenPlace P)))) := by
  have h1 : ∀ st : mirlite.State M Γ,
      mirlite.resolvePlaceAcc M st (Place.deref (flattenPlace P))
        = mirlite.resolvePlaceAcc M st (Place.deref P) :=
    fun st => resolvePlaceAcc_flatten (Place.deref P)
  show mirlite.doAssign M s dst _ = mirlite.doAssign M s dst _
  simp only [mirlite.doAssign, mirlite.evalRExpr, h1]

/-- The ref rhs, like the copy rhs, sees a place only through
    `resolvePlaceAcc`, so it cannot tell a source from its flattening
    apart. Generalizes `stepStmt_assign_refsrc_flatten` from a deref
    source to ANY source. -/
theorem stepStmt_assign_refsrc_anyflatten
    {Γ : Ctx} {τ : LayoutTy} {M : PermissionModel}
    (s : mirlite.State M Γ) (dst : Place Γ (obseq.LayoutTy.PtrL τ))
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (src : Place Γ τ) :
    mirlite.stepStmt M s (.assign dst (.ref kind prot mask src))
      = mirlite.stepStmt M s (.assign dst (.ref kind prot mask (flattenPlace src))) := by
  have h1 : ∀ st : mirlite.State M Γ,
      mirlite.resolvePlaceAcc M st (flattenPlace src)
        = mirlite.resolvePlaceAcc M st src :=
    fun st => resolvePlaceAcc_flatten src
  show mirlite.doAssign M s dst _ = mirlite.doAssign M s dst _
  simp only [mirlite.doAssign, mirlite.evalRExpr, h1]

/-! ## The NIL-projection eta: `*P` and `(*P).nil` are the same place

    `flattenPlace` never introduces an empty projection, so it cannot
    relate the two spellings — but they resolve identically (a path
    offset of zero) and lower to literally the same instructions, since
    `placeToRegChecked`'s deref arm leaves an empty cleanup and the
    projection arm's `[] ++ [tmp]` is `[tmp]`. Retagging a deref source
    is therefore expressible in the `.proj (.deref _) _` grammar the
    projected-destination leaves already cover. -/

theorem resolvePlaceAcc_nil
    {Γ : Ctx} {τ : LayoutTy} {M : PermissionModel}
    (s : mirlite.State M Γ) (p : Place Γ τ) :
    mirlite.resolvePlaceAcc M s (Place.proj p PathTo.nil)
      = mirlite.resolvePlaceAcc M s p := by
  cases h : mirlite.resolvePlaceAcc M s p with
  | error e => simp only [mirlite.resolvePlaceAcc, h]
  | ok r => simp only [mirlite.resolvePlaceAcc, h, PathTo.offset, Nat.add_zero]

theorem stepStmt_assign_refsrc_nil
    {Γ : Ctx} {τ : LayoutTy} {M : PermissionModel}
    (s : mirlite.State M Γ) (dst : Place Γ (obseq.LayoutTy.PtrL τ))
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (src : Place Γ τ) :
    mirlite.stepStmt M s (.assign dst (.ref kind prot mask src))
      = mirlite.stepStmt M s
          (.assign dst (.ref kind prot mask (Place.proj src PathTo.nil))) := by
  have h1 : ∀ st : mirlite.State M Γ,
      mirlite.resolvePlaceAcc M st (Place.proj src PathTo.nil)
        = mirlite.resolvePlaceAcc M st src :=
    fun st => resolvePlaceAcc_nil st src
  show mirlite.doAssign M s dst _ = mirlite.doAssign M s dst _
  simp only [mirlite.doAssign, mirlite.evalRExpr, h1]

/-- The compiled side of the nil-projection eta, for a DEREF base: both
    spellings emit the pointer lowering, the `Load`, its cleanup, and one
    `Borrow` at offset zero, in that order, from the same register
    counter. -/
theorem placeToBorrowRegChecked_nil_agree {Γ : Ctx} {τ : LayoutTy}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (P : Place Γ (obseq.LayoutTy.PtrL τ)) (cs : CompilerState) :
    CheckedCompilerM.run
        (placeToBorrowRegChecked kind prot mask
          (Place.proj (Place.deref P) PathTo.nil)) cs
      = CheckedCompilerM.run
          (placeToBorrowRegChecked kind prot mask (Place.deref P)) cs ∧
    (CheckedCompilerM.value
        (placeToBorrowRegChecked kind prot mask
          (Place.proj (Place.deref P) PathTo.nil)) cs).map (fun o => o.result)
      = (CheckedCompilerM.value
          (placeToBorrowRegChecked kind prot mask (Place.deref P)) cs).map
        (fun o => o.result) := by
  refine ⟨?_, ?_⟩ <;>
    cases h : CheckedCompilerM.value (placeToRegChecked RefKind.Shared P) cs <;>
    simp [placeToBorrowRegChecked, placeToRegChecked, PathTo.offset, h, Except.map,
      CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
      CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
      CheckedCompilerM.run_pure, CheckedCompilerM.value_pure]

/-- The `placeToBorrowRegChecked` projection equation for a base that
    is not itself a projection — the borrow mirror of
    `placeToRegChecked_proj_root_eq`. `PtrChain.not_proj` supplies the
    side condition, so a leaf generic in a chain base can unfold. -/
theorem placeToBorrowRegChecked_proj_root_eq {Γ : Ctx} {σ τ : LayoutTy}
    {kind : RefKind} {prot : Bool} {mask : List Bool}
    {base : Place Γ σ} (path : PathTo σ τ)
    (h_np : ∀ (σ' : LayoutTy) (b : Place Γ σ') (q : PathTo σ' σ),
      base = b.proj q → False) :
    placeToBorrowRegChecked kind prot mask (Place.proj base path)
      = (do
          let baseOut ← placeToRegChecked kind base
          let baseRes := baseOut.result
          let offset := pathOffset path
          let tmpReg ← CheckedCompilerM.lift freshRegM
          let _ ← CheckedCompilerM.lift
            (emitM [Instr.Assgn tmpReg
              (Rhs.Borrow kind prot mask (blockSize τ) baseRes.reg offset)])
          pure {
            result := { reg := tmpReg,
                        cleanup := baseRes.cleanup ++ [(tmpReg, blockSize τ)] },
            evidence := PlaceToBorrowRegEvidence.proj base path baseRes tmpReg
              baseOut.evidence
          }) := by
  cases base with
  | «local» l => simp only [placeToBorrowRegChecked]
  | deref pp => simp only [placeToBorrowRegChecked]
  | proj b q => exact absurd rfl (h_np _ b q)

/-- The nil-projection eta for a LOCAL base: the local arm and the
    zero-offset projection arm emit the same `Borrow`, and the local
    lowering's cleanup is literally `[]`. -/
theorem placeToBorrowRegChecked_nil_agree_local {Γ : Ctx} {τ : LayoutTy}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (loc : Local Γ τ) (cs : CompilerState) :
    CheckedCompilerM.run
        (placeToBorrowRegChecked kind prot mask
          (Place.proj (Place.local loc) PathTo.nil)) cs
      = CheckedCompilerM.run
          (placeToBorrowRegChecked kind prot mask (Place.local loc)) cs ∧
    (CheckedCompilerM.value
        (placeToBorrowRegChecked kind prot mask
          (Place.proj (Place.local loc) PathTo.nil)) cs).map (fun o => o.result)
      = (CheckedCompilerM.value
          (placeToBorrowRegChecked kind prot mask (Place.local loc)) cs).map
        (fun o => o.result) := by
  constructor
  · cases hv : CheckedCompilerM.value (placeToRegChecked kind (Place.local loc)) cs <;>
      simp [placeToBorrowRegChecked, PathTo.offset, hv,
        CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
        CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
        CheckedCompilerM.run_pure, CheckedCompilerM.value_pure]
  · cases hv : CheckedCompilerM.value (placeToRegChecked kind (Place.local loc)) cs with
    | error e =>
        simp [placeToBorrowRegChecked, PathTo.offset, hv, Except.map,
          CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
          CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
          CheckedCompilerM.run_pure, CheckedCompilerM.value_pure]
    | ok a =>
        have hc := placeToRegChecked_local_cleanup hv
        simp [placeToBorrowRegChecked, PathTo.offset, hv, hc, Except.map,
          CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
          CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
          CheckedCompilerM.run_pure, CheckedCompilerM.value_pure]

/-- The nil-projection eta for ANY canonical chain base. -/
theorem placeToBorrowRegChecked_nil_agree_chain {Γ : Ctx} {τ : LayoutTy}
    {b : Place Γ τ} (h : PtrChain b)
    (kind : RefKind) (prot : Bool) (mask : List Bool) (cs : CompilerState) :
    CheckedCompilerM.run
        (placeToBorrowRegChecked kind prot mask (Place.proj b PathTo.nil)) cs
      = CheckedCompilerM.run (placeToBorrowRegChecked kind prot mask b) cs ∧
    (CheckedCompilerM.value
        (placeToBorrowRegChecked kind prot mask (Place.proj b PathTo.nil)) cs).map
          (fun o => o.result)
      = (CheckedCompilerM.value
          (placeToBorrowRegChecked kind prot mask b) cs).map (fun o => o.result) := by
  cases h with
  | base loc => exact placeToBorrowRegChecked_nil_agree_local kind prot mask loc cs
  | deref _ => exact placeToBorrowRegChecked_nil_agree kind prot mask _ cs
  | derefProj _ _ => exact placeToBorrowRegChecked_nil_agree kind prot mask _ cs

/-! ## Source lowerings as a PACKAGE

    Every copy leaf lowers its source by calling `ptrChain_lowering_sim`
    and then consuming its twenty-odd conjuncts. That is the only use a
    leaf makes of `PtrChain src`, so naming the conclusion lets a leaf
    take the PACKAGE as a hypothesis and accept any source shape that
    can produce one — not just a canonical chain. At ZERO offset a
    projection over a chain produces one, which is what
    `projZero_lowering_sim` below supplies. -/

def LoweringSim {Γ : Ctx}
    (ρa : AddrRenameMap) (ρt : TagRenameMap)
    (s_mir : mirlite.State MSB Γ) (compProg : oseair.Prog)
    {τ : LayoutTy} (p : Place Γ τ) : Prop :=
  IdentityOnDomain ρa → TagRenameWF ρt →
  ∀ (kind : RefKind) (cs : CompilerState) (s_osea : oseair.State MSB)
    (resolved : mirlite.PlaceRes) (permsD : MSB.State),
    mirlite.resolvePlaceAcc MSB s_mir p = .ok (resolved, permsD) →
    TagRenameBounded ρt s_mir.perms.NextTag s_osea.perms.NextTag →
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
      s_osea.perms.NextTag ≤ s_osea'.perms.NextTag ∧
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
      cs.nextLabel ≤ (CheckedCompilerM.run (placeToRegChecked kind p) cs).nextLabel ∧
      (∀ r, RegisterBelow cs.nextReg r →
        oseair.RegMap.lookup s_osea'.reg r = oseair.RegMap.lookup s_osea.reg r) ∧
      ρa resolved.allocBase = some resolved.allocBase

/-- A canonical chain supplies the package: this IS the mother lemma. -/
theorem PtrChain.loweringSim {Γ : Ctx}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir : mirlite.State MSB Γ} {compProg : oseair.Prog}
    {τ : LayoutTy} {p : Place Γ τ} (h : PtrChain p) :
    LoweringSim ρa ρt s_mir compProg p :=
  fun h_id_a h_wf_t => ptrChain_lowering_sim h_id_a h_wf_t h

/-- At ZERO offset a projection over a place that already supplies the
    package supplies it too. The projection contributes a `+ 0` on the
    resolved address (which collapses) and a `pure` on the compiled side
    (which the two zero-offset bridges make invisible), so every conjunct
    transports by rewriting `run (proj B spath) cs = run B cs`. -/
theorem LoweringSim.projZero {Γ : Ctx}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir : mirlite.State MSB Γ} {compProg : oseair.Prog}
    {σ τ : LayoutTy} {B : Place Γ σ} {spath : PathTo σ τ}
    (h_np : ∀ (σ' : LayoutTy) (b : Place Γ σ') (q : PathTo σ' σ),
      B = b.proj q → False)
    (h_o : pathOffset spath = 0)
    (h : LoweringSim ρa ρt s_mir compProg B) :
    LoweringSim ρa ρt s_mir compProg (Place.proj B spath) := by
  intro h_id_a h_wf_t kind cs s_osea resolved permsD h_res h_tbd h_lbs h_prb
    h_sms h_psim h_pc h_inst
  have h_pr := placeToRegChecked_proj_zero_run (kind := kind) spath h_np h_o cs
  cases h_bres : mirlite.resolvePlaceAcc MSB s_mir B with
  | error e => rw [resolvePlaceAcc_proj_base_err h_bres] at h_res; simp at h_res
  | ok pr =>
  obtain ⟨rb, permsB⟩ := pr
  rw [resolvePlaceAcc_proj_base_ok h_bres] at h_res
  have h_o' : PathTo.offset spath = 0 := h_o
  simp only [h_o', Nat.add_zero, Except.ok.injEq, Prod.mk.injEq] at h_res
  obtain ⟨h_r1, h_r2⟩ := h_res
  subst h_r1
  subst h_r2
  obtain ⟨placeOut, n, s', tres, h_val, h_clean, h_run, h_pc', h_mem, h_ps,
    h_nt1, h_nt2, h_lbs', h_entry, h_rt, h_nw, h_le, h_dom, h_below, h_prm,
    h_regmono, h_labmono, h_frame, h_rabase⟩ :=
    h h_id_a h_wf_t kind cs s_osea rb permsB h_bres h_tbd h_lbs h_prb h_sms
      h_psim h_pc (by rw [h_pr] at h_inst; exact h_inst)
  refine ⟨_, n, s', tres,
    placeToRegChecked_proj_zero_value spath h_np h_o h_val, h_clean, h_run,
    ?_, h_mem, h_ps, h_nt1, h_nt2, h_lbs', h_entry, h_rt, h_nw, h_le, h_dom,
    ?_, ?_, ?_, ?_, h_frame, h_rabase⟩
  · rw [h_pr]; exact h_pc'
  · rw [h_pr]; exact h_below
  · rw [h_pr]; exact h_prm
  · rw [h_pr]; exact h_regmono
  · rw [h_pr]; exact h_labmono

/-- The package at ANY renames and source state. Leaves that allocate
    before lowering the source (regime B) run the source lemma at
    EXTENDED renames and a post-allocation state, so they need this
    stronger, rename-polymorphic form; `PtrChain` supplies it because
    the chain lemma never mentions the renames in its hypotheses. -/
def LoweringSimAny {Γ : Ctx} (compProg : oseair.Prog)
    {τ : LayoutTy} (p : Place Γ τ) : Prop :=
  ∀ (ρa : AddrRenameMap) (ρt : TagRenameMap) (s_mir : mirlite.State MSB Γ),
    LoweringSim ρa ρt s_mir compProg p

theorem PtrChain.loweringSimAny {Γ : Ctx} {compProg : oseair.Prog}
    {τ : LayoutTy} {p : Place Γ τ} (h : PtrChain p) :
    LoweringSimAny compProg p :=
  fun _ _ _ => h.loweringSim

theorem LoweringSimAny.projZero {Γ : Ctx} {compProg : oseair.Prog}
    {σ τ : LayoutTy} {B : Place Γ σ} {spath : PathTo σ τ}
    (h_np : ∀ (σ' : LayoutTy) (b : Place Γ σ') (q : PathTo σ' σ),
      B = b.proj q → False)
    (h_o : pathOffset spath = 0)
    (h : LoweringSimAny compProg B) :
    LoweringSimAny compProg (Place.proj B spath) :=
  fun ρa ρt s_mir => LoweringSim.projZero h_np h_o (h ρa ρt s_mir)

/-- A zero-offset projection over a chain leaves `placeRegMap` alone,
    exactly as the chain does — the companion fact the leaves need
    BEFORE they may invoke the package. -/
theorem projZero_placeRegMap {Γ : Ctx} {σ τ : LayoutTy}
    {B : Place Γ σ} {spath : PathTo σ τ} {kind : RefKind}
    (h_np : ∀ (σ' : LayoutTy) (b : Place Γ σ') (q : PathTo σ' σ),
      B = b.proj q → False)
    (h_o : pathOffset spath = 0)
    (h_B : ∀ cs, (CheckedCompilerM.run (placeToRegChecked kind B) cs).placeRegMap
      = cs.placeRegMap) :
    ∀ cs, (CheckedCompilerM.run (placeToRegChecked kind (Place.proj B spath))
      cs).placeRegMap = cs.placeRegMap := by
  intro cs
  rw [placeToRegChecked_proj_zero_run spath h_np h_o cs]
  exact h_B cs

/-! ## The chain-write seam

    Lives here, not in copy.lean, because ref.lean and copy.lean are
    SIBLINGS: a seam either file can call has to sit in their common
    parent. The theorem itself mentions no rvalue — `stmt0` and the
    fragment equation are hypotheses — and since 2026-09-02 no minting
    facts either, so a leaf whose rvalue MINTS a tag (ref's retag) can
    instantiate it at the extended renames. -/

section
variable {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
variable {ρa : AddrRenameMap} {ρt : TagRenameMap}
variable {s_mir s_mir' : mirlite.State MSB Γ}
variable {s_osea : oseair.State MSB}

/-- The DESTINATION half of a copy into a CHAIN-resolved destination —
    `chain := copy src` and `dst.f := copy src` at zero offset alike —
    stated over an abstract POST-READ state: the
    source has been lowered, loaded into `vreg`, and (if it borrowed) its
    temporary already retired — `sR`/`csR` are whatever states that left
    behind. Every source shape that can deliver these hypotheses gets the
    whole destination argument for free; this is the read-level interface
    the `LoweringSim` package could not be (its `cleanup = []` boundary),
    extracted verbatim from the chain-source leaf. -/
theorem copy_chainwrite_after_read
    {τ σb : LayoutTy}
    {dbase : Place Γ σb}
    (compProg : oseair.Prog)
    (h_dchain : PtrChain dbase)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    {stmt0 : Stmt Γ}
    (h_stmt : prog.get? s_mir.pc = some stmt0)
    {csPrefix : CompilerState}
    (h_csAt : csAt cs0 prog s_mir.pc csPrefix)
    {stmtOut : ResultWithEvidence Unit (fun _ => StmtEvidence stmt0)}
    (h_stmtOut : CheckedCompilerM.value (compileStmtChecked stmt0) csPrefix
      = Except.ok stmtOut)
    (h_id_a : IdentityOnDomain ρa) (h_wf_t : TagRenameWF ρt)
    (h_sms : SourceMemSim ρa ρt s_mir.mem s_osea.mem)
    (h_alloc : AllocLockstep s_mir.mem s_osea.mem)
    (h_unmap : UnboundLocalsUnmapped s_mir.env csPrefix)
    (h_prb : PlaceRegMapBound csPrefix)
    {rd : mirlite.PlaceRes} {permsD : MSB.State} {perms₂ : MSB.State}
    (h_dres : mirlite.resolvePlaceAcc MSB { s_mir with perms := perms₂ } (dbase)
      = .ok (rd, permsD))
    {mvals : List mirlite.MemValue} (h_mlen : mvals.length = blockSize τ)
    (h_step : mirlite.writeResolvedPlace (τ := τ) MSB { s_mir with perms := permsD }
      rd mvals h_mlen = mirlite.Result.ok s_mir')
    {csR : CompilerState} {sR : oseair.State MSB} {vreg : Register}
    {vals : List Val} {nR : Nat}
    (h_runR : oseair.runN MSB nR s_osea compProg = oseair.Result.Ok sR)
    (h_prmR : csR.placeRegMap = csPrefix.placeRegMap)
    (h_regmonoR : csPrefix.nextReg ≤ csR.nextReg)
    (h_lbsR : LocalBindingSim ρa ρt s_mir.env sR csR)
    (h_psimR : PermSim ρt perms₂ sR.perms)
    (h_tbdR : TagRenameBounded ρt perms₂.NextTag sR.perms.NextTag)
    (h_memR : sR.mem = s_osea.mem)
    (h_pcR : sR.pc = csR.nextLabel)
    (h_vregR : oseair.RegMap.lookup sR.reg vreg = some (layoutToTyVal τ, vals))
    (h_vbelow : RegisterBelow csR.nextReg vreg)
    (h_vlen : vals.length = blockSize τ)
    (h_valsRel : ListRel (MemValSim ρa ρt) mvals vals)
    (h_instR : ∀ q instr,
      q < (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (dbase)) csR).nextLabel →
      (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (dbase)) csR).code q
        = some instr →
      compProg q = some instr)
    (h_frag : ∀ (dOut : ResultWithEvidence PtrResult
        (PlaceToRegEvidence RefKind.Mut (dbase))),
      CheckedCompilerM.value (placeToRegChecked RefKind.Mut (dbase)) csR
        = Except.ok dOut →
      dOut.result.cleanup = [] →
      CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix
        = emit (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (dbase)) csR)
            [Instr.RStore (layoutToTyVal τ) vreg dOut.result.reg]) :
    ∃ (s_osea' : oseair.State MSB) (n : Nat),
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa ρt s_mir' s_osea' := by
    -- §7 the DESTINATION mother lemma, at the post-read states
    have h_prmCS1 : csR.placeRegMap = csPrefix.placeRegMap := h_prmR
    have h_lbs1 : LocalBindingSim ρa ρt s_mir.env sR csR := h_lbsR
    have h_prb1 : PlaceRegMapBound csR := by
      intro idx reg τ'' h_look
      have h_cs : getPlaceInfo csPrefix idx = some (reg, τ'') := by
        show csPrefix.placeRegMap.lookup idx = _
        rw [← h_prmR]
        exact h_look
      exact RegisterBelow.mono h_regmonoR (h_prb _ _ _ h_cs)
    have h_tbd1 : TagRenameBounded ρt perms₂.NextTag sR.perms.NextTag := h_tbdR
    obtain ⟨dOut, n2, s_mid2, tresD, h_dval, h_dclean, h_drun, h_dpc, h_dmem,
      h_dpsim, h_dnt1, h_dnt2, h_dlbs, h_dentry, h_drt, h_dnw, h_dle, h_drange,
      h_dbelow, h_dprm, h_dregmono, h_dlabmono, h_dframe, -⟩ :=
      ptrChain_lowering_sim (s_mir := { s_mir with perms := perms₂ })
        (compProg := compProg) h_id_a h_wf_t h_dchain RefKind.Mut csR
        sR rd permsD h_dres h_tbd1 h_lbs1 h_prb1
        (by rw [show sR.mem = s_osea.mem from h_memR]; exact h_sms)
        h_psimR h_pcR h_instR
    -- §8 the WRITE: transport, then execute the `RStore`
    have h_stmtRun := h_frag dOut h_dval h_dclean
    have h_cancelD := resolvedAddr_cancel h_dle
    obtain ⟨h_nb, perms₃, h_useMut_src, rfl⟩ := writeResolvedPlace_ok_inv h_step
    obtain ⟨p3, h_useMut_tgt, h_psim3⟩ :=
      sb_write_respects_PermSim h_dpsim h_wf_t h_drt h_dnw h_useMut_src
    -- the temporary register survives the destination lowering
    have h_regbelow : RegisterBelow csR.nextReg vreg := h_vbelow
    have h_vreg : oseair.RegMap.lookup s_mid2.reg vreg
        = some (layoutToTyVal τ, vals) := by
      rw [h_dframe vreg h_regbelow]
      exact h_vregR
    have h_code2 : compProg s_mid2.pc
        = some (Instr.RStore (layoutToTyVal τ) vreg dOut.result.reg) := by
      rw [h_dpc]
      refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
      · rw [h_stmtRun]
        show _ < _ + 1
        exact Nat.lt_succ_self _
      · rw [h_stmtRun]
        have h := emit_code_at_new
          (CheckedCompilerM.run (placeToRegChecked RefKind.Mut (dbase))
      csR)
          [Instr.RStore (layoutToTyVal τ) vreg dOut.result.reg]
          (k := 0) (by simp)
        simpa using h
    have h_useMut2t : MSB.useMut s_mid2.perms
        (rd.allocBase + (rd.addr - rd.allocBase)) vals.length tresD = .ok p3 := by
      rw [h_cancelD, h_vlen]
      simpa only [h_mlen] using h_useMut_tgt
    have h_wtp : oseair.writeThroughPtr MSB s_mid2 dOut.result.reg vals
        "RStore Invalid Regs"
        = oseair.Result.Ok
          { s_mid2 with
              perms := p3,
              mem := oseair.writeWordSeq s_mid2.mem rd.addr vals,
              pc := s_mid2.pc + 1 } := by
      have h_dl : oseair.RegMap.lookup s_mid2.reg dOut.result.reg
          = some (obseq.TyVal.PTy,
              [Val.Ptr rd.allocBase (rd.addr - rd.allocBase) rd.allocSize
                tresD]) := h_dentry
      simp only [oseair.writeThroughPtr, h_dl]
      rw [if_neg (by
        rw [h_vlen, h_cancelD]
        have h1 := Nat.not_lt.mp h_nb
        simp only [h_mlen] at h1
        exact Nat.not_lt.mpr (by grind))]
      rw [h_cancelD] at h_useMut2t
      simp only [h_useMut2t, h_cancelD]
    have h_run2 := runN_RStore_step compProg s_mid2 _
      (layoutToTyVal τ) vreg dOut.result.reg vals
      _ h_code2 h_vreg h_dentry h_wtp
    have h_runB := (oseair_runN_trans h_runR h_drun)
    have h_run := (oseair_runN_trans h_runB h_run2)
    -- §9 memory: the same values land at the same addresses
    have h_memchain : s_mid2.mem = s_osea.mem := by
      rw [h_dmem]
      exact h_memR
    have h_rel : ListRel (MemValSim ρa ρt) mvals vals := h_valsRel
    have h_dom : ∀ k,
        k < mvals.length →
        ρa (rd.addr + k) = some (rd.addr + k) := by
      intro k hk
      rw [h_mlen] at hk
      have h_lt : rd.addr - rd.allocBase + k < rd.allocSize := by
        have h1 := Nat.not_lt.mp h_nb
        have h2 := h_dle
        simp only [h_mlen] at h1
        grind
      obtain ⟨a', ha'⟩ := h_drange _ h_lt
      have h_addr : rd.allocBase + (rd.addr - rd.allocBase + k) = rd.addr + k := by
        have h2 := h_dle
        grind
      rw [h_addr] at ha'
      grind
    have h_sms' : SourceMemSim ρa ρt
        (mirlite.writeWordSeq s_mir.mem rd.addr
          mvals)
        (oseair.writeWordSeq s_mid2.mem rd.addr vals) := by
      refine SourceMemSim.writeWordSeq_extend h_id_a _ _ _ _ _ h_rel h_dom ?_
      rw [h_memchain]
      exact h_sms
    -- §10 rebuild the invariant
    refine ⟨_, nR + n2 + 1, h_run, ?_⟩
    refine ⟨CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix,
      ⟨prefixCompileState_succ h_csAt h_stmt h_stmtOut, ?_⟩, ?_, ?_, h_psim3,
      h_id_a, h_wf_t, ?_, ?_, ?_, ?_⟩
    · show s_mid2.pc + 1 = _
      rw [h_dpc, h_stmtRun]
      simp [emit]
    · intro τ' loc' binding' h_env'
      obtain ⟨reg', base', tag', h_pi', h_entry', h_ra', h_rt', h_nw', h_dom'⟩ :=
        h_dlbs loc' binding' h_env'
      refine ⟨reg', base', tag', ?_, h_entry', h_ra', h_rt', h_nw', h_dom'⟩
      rw [h_stmtRun, getPlaceInfo_emit]
      show _ = _
      simp only [getPlaceInfo, h_dprm]
      exact h_pi'
    · exact h_sms'
    · show TagRenameBounded ρt perms₃.NextTag p3.NextTag
      rw [sb_write_NextTag h_useMut_src, sb_write_NextTag h_useMut_tgt, h_dnt1]
      show TagRenameBounded ρt perms₂.NextTag _
      exact TagRenameBounded.mono h_tbdR (Nat.le_refl _) h_dnt2
    · simp only [h_memchain]
      exact h_alloc.writeWordSeq _ _ _ _
    · intro τ' loc' h_none
      rw [h_stmtRun, getPlaceInfo_emit]
      show _ = _
      simp only [getPlaceInfo, h_dprm]
      have h_p : csR.placeRegMap = csPrefix.placeRegMap := h_prmR
      simp only [getPlaceInfo] at h_p ⊢
      rw [h_p]
      exact h_unmap loc' h_none
    · intro idx reg'' τ'' h_look
      rw [h_stmtRun] at h_look ⊢
      rw [getPlaceInfo_emit] at h_look
      have h_p : csR.placeRegMap = csPrefix.placeRegMap := h_prmR
      have h_cs : getPlaceInfo csPrefix idx = some (reg'', τ'') := by
        show csPrefix.placeRegMap.lookup idx = _
        rw [← h_p, ← h_dprm]
        exact h_look
      refine RegisterBelow.mono ?_ (h_prb _ _ _ h_cs)
      simp only [emit]
      exact Nat.le_trans h_regmonoR h_dregmono


/-- **The fresh-root write seam** — the destination half of a copy into
    a local the statement itself ALLOCATES, stated over an abstract
    post-source state, exactly as `copy_chainwrite_after_read` is for a
    chain destination.

    A fresh leaf's shape is: allocate the root (mirlite `own`, oseair
    `Alloc`), lower and read the source, `RStore` the value through the
    root register, then rebuild the invariant under the two EXTENDED
    renames. Only the middle step depends on the source shape -- and that
    is a source package -- so everything after it belongs here: the
    write transport, the `RStore`, the memory extension, and all six
    `CompilerInv` bullets.

    The renames are abstract (`ρa'`/`ρt'` with their `Incr` facts) rather
    than the literal `extendBlock`/`extend`, so the leaf's own
    allocation bookkeeping stays where it is. -/
theorem copy_freshroot_write_after_read
    {σ τ : LayoutTy} {dstLoc : Local Γ σ}
    {ρa' : AddrRenameMap} {ρt' : TagRenameMap}
    (compProg : oseair.Prog)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    {stmt0 : Stmt Γ}
    (h_stmt : prog.get? s_mir.pc = some stmt0)
    {csPrefix : CompilerState}
    (h_csAt : csAt cs0 prog s_mir.pc csPrefix)
    {stmtOut : ResultWithEvidence Unit (fun _ => StmtEvidence stmt0)}
    (h_stmtOut : CheckedCompilerM.value (compileStmtChecked stmt0) csPrefix
      = Except.ok stmtOut)
    (h_sms : SourceMemSim ρa ρt s_mir.mem s_osea.mem)
    (h_unmap : UnboundLocalsUnmapped s_mir.env csPrefix)
    (h_prb : PlaceRegMapBound csPrefix)
    -- the allocation, on the mirlite side: the post-`own` state `s1`
    {s1 : mirlite.State MSB Γ}
    (h_lookup_set : mirlite.Env.lookup s1.env dstLoc
      = some { addr := s_mir.mem.addrStart, tag := s_mir.perms.NextTag })
    (h_env1 : s1.env = mirlite.Env.set s_mir.env dstLoc
      { addr := s_mir.mem.addrStart, tag := s_mir.perms.NextTag })
    (h_pc1 : s1.pc = s_mir.pc)
    (h_memstart1 : s1.mem.addrStart = s_mir.mem.addrStart + blockSize σ)
    (h_find1 : ∀ a, mirlite.Mem.find? s1.mem a = mirlite.Mem.find? s_mir.mem a)
    -- ... and on the oseair side: the `Alloc` runs, and the two memories
    -- start together
    (h_addr_eq : s_osea.mem.addrStart = s_mir.mem.addrStart)
    (h_sz : obseq.typeSize (layoutToTyVal σ) = blockSize σ)
    {tgtPerms : MSB.State} {n0 : Nat}
    (h_run0' : oseair.runN MSB n0 s_osea compProg = oseair.Result.Ok
      { s_osea with
      mem := (oseair.allocate s_osea.mem (obseq.typeSize (layoutToTyVal σ))).2,
      perms := tgtPerms,
      reg := oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
        (obseq.TyVal.PTy, [Val.Ptr s_osea.mem.addrStart 0
          (obseq.typeSize (layoutToTyVal σ)) s_osea.perms.NextTag]),
      pc := s_osea.pc + 1 })
    -- the two extended renames
    (h_incr_a : AddrRenameIncr ρa ρa') (h_incr_t : TagRenameIncr ρt ρt')
    (h_id_a' : IdentityOnDomain ρa') (h_wf_t' : TagRenameWF ρt')
    (h_ra_dom : ∀ k, k < blockSize σ →
      ρa' (s_mir.mem.addrStart + k) = some (s_mir.mem.addrStart + k))
    (h_prb1 : PlaceRegMapBound (setPlaceInfo
      (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
        [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
      dstLoc.idx.1 (Register.R csPrefix.nextReg, σ)))
    -- the POST-SOURCE bundle: whatever the source package left behind
    {csR : CompilerState} {sR : oseair.State MSB} {vreg : Register}
    {vals : List Val} {nR : Nat} {perms₂ : MSB.State}
    (h_runR : oseair.runN MSB nR
      { s_osea with
      mem := (oseair.allocate s_osea.mem (obseq.typeSize (layoutToTyVal σ))).2,
      perms := tgtPerms,
      reg := oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
        (obseq.TyVal.PTy, [Val.Ptr s_osea.mem.addrStart 0
          (obseq.typeSize (layoutToTyVal σ)) s_osea.perms.NextTag]),
      pc := s_osea.pc + 1 } compProg = oseair.Result.Ok sR)
    (h_prmR : csR.placeRegMap = ((setPlaceInfo
      (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
        [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
      dstLoc.idx.1 (Register.R csPrefix.nextReg, σ))).placeRegMap)
    (h_regmonoR : ((setPlaceInfo
      (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
        [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
      dstLoc.idx.1 (Register.R csPrefix.nextReg, σ))).nextReg ≤ csR.nextReg)
    (h_lbsR : LocalBindingSim ρa' ρt' s1.env sR csR)
    (h_psimR : PermSim ρt' perms₂ sR.perms)
    (h_tbdR : TagRenameBounded ρt' perms₂.NextTag sR.perms.NextTag)
    (h_smem : sR.mem
      = ({ s_osea with
      mem := (oseair.allocate s_osea.mem (obseq.typeSize (layoutToTyVal σ))).2,
      perms := tgtPerms,
      reg := oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
        (obseq.TyVal.PTy, [Val.Ptr s_osea.mem.addrStart 0
          (obseq.typeSize (layoutToTyVal σ)) s_osea.perms.NextTag]),
      pc := s_osea.pc + 1 }).mem)
    (h_pcR : sR.pc = csR.nextLabel)
    (h_vregR : oseair.RegMap.lookup sR.reg vreg = some (layoutToTyVal τ, vals))
    (h_vlen : vals.length = blockSize τ)
    (h_stmtRun : CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix
      = emit csR [Instr.RStore (layoutToTyVal τ) vreg (Register.R csPrefix.nextReg)])
    -- the mirlite write into the fresh root
    {rd : mirlite.PlaceRes} {mvals : List mirlite.MemValue}
    (h_mlen : mvals.length = blockSize τ)
    (h_fit : blockSize τ ≤ blockSize σ)
    (h_rdaddr : rd.addr = s_mir.mem.addrStart)
    (h_rdtag : rd.tag = s_mir.perms.NextTag)
    (h_valsRel : ListRel (MemValSim ρa' ρt') mvals vals)
    (h_step : mirlite.writeResolvedPlace (τ := τ) MSB
      { s1 with perms := perms₂ } rd mvals h_mlen = mirlite.Result.ok s_mir') :
    ∃ (ρa'' : AddrRenameMap) (ρt'' : TagRenameMap) (s_osea' : oseair.State MSB)
      (n : Nat),
      AddrRenameIncr ρa ρa'' ∧
      TagRenameIncr ρt ρt'' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa'' ρt'' s_mir' s_osea' := by
  -- the write, transported through the post-source binding
  obtain ⟨h_nb, perms₃, h_useMut_src, rfl⟩ := writeResolvedPlace_ok_inv h_step
  have h_useMut_src' : MSB.useMut perms₂ s_mir.mem.addrStart (blockSize τ)
      s_mir.perms.NextTag = .ok perms₃ := by
    rw [← h_rdaddr, ← h_rdtag, ← h_mlen]
    exact h_useMut_src
  have h_pi_new : getPlaceInfo (setPlaceInfo
      (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
        [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
      dstLoc.idx.1 (Register.R csPrefix.nextReg, σ))
      dstLoc.idx.1 = some (Register.R csPrefix.nextReg, σ) :=
    getPlaceInfo_setPlaceInfo_self _ _ _
  obtain ⟨dstReg2, baseD2, tagD2, h_piD2, h_entryD2, h_raD2, h_rtD2,
    h_nwD2, h_domD2⟩ := h_lbsR dstLoc _ h_lookup_set
  have h_piD2' : getPlaceInfo (setPlaceInfo
      (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
        [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
      dstLoc.idx.1 (Register.R csPrefix.nextReg, σ))
      dstLoc.idx.1 = some (dstReg2, σ) := by
    show ((setPlaceInfo
      (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
        [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
      dstLoc.idx.1 (Register.R csPrefix.nextReg, σ))).placeRegMap.lookup _ = _
    rw [← h_prmR]
    exact h_piD2
  have h_dr2 : dstReg2 = Register.R csPrefix.nextReg := by grind
  have h_baseD2 : baseD2 = s_mir.mem.addrStart := (h_id_a' _ _ h_raD2).symm
  rw [h_dr2, h_baseD2] at h_entryD2
  obtain ⟨p3w, h_useMut_tgt, h_psim3w⟩ :=
    sb_write_respects_PermSim h_psimR h_wf_t' h_rtD2 h_nwD2 h_useMut_src'
  -- the resolved destination IS the fresh root
  rw [h_rdaddr]
  have h_dentry2 : oseair.RegMap.lookup sR.reg (Register.R csPrefix.nextReg)
      = some (obseq.TyVal.PTy,
          [Val.Ptr s_mir.mem.addrStart 0 (blockSize σ) tagD2]) := h_entryD2
  -- the `RStore` through the root register
  have h_code2 : compProg sR.pc
      = some (Instr.RStore (layoutToTyVal τ) vreg (Register.R csPrefix.nextReg)) := by
    rw [h_pcR]
    refine compileStmt_emitted_in_compProg h_comp h_csAt h_stmt h_stmtOut ?_ ?_
    · rw [h_stmtRun]
      show _ < _ + 1
      exact Nat.lt_succ_self _
    · rw [h_stmtRun]
      have h := emit_code_at_new csR
        [Instr.RStore (layoutToTyVal τ) vreg (Register.R csPrefix.nextReg)]
        (k := 0) (by simp)
      simpa using h
  have h_useMut2t : MSB.useMut sR.perms (s_mir.mem.addrStart + 0)
      vals.length tagD2 = .ok p3w := by
    rw [Nat.add_zero, h_vlen]
    exact h_useMut_tgt
  have h_wtp : oseair.writeThroughPtr MSB sR (Register.R csPrefix.nextReg) vals
      "RStore Invalid Regs"
      = oseair.Result.Ok
        { sR with
            perms := p3w,
            mem := oseair.writeWordSeq sR.mem s_mir.mem.addrStart vals,
            pc := sR.pc + 1 } := by
    simp only [oseair.writeThroughPtr, h_dentry2]
    rw [if_neg (by
      rw [h_vlen, Nat.add_zero]
      exact Nat.not_lt.mpr (Nat.add_le_add_left h_fit _))]
    simp only [h_useMut2t]
    rfl
  have h_run2 := runN_RStore_step compProg _ _
    (layoutToTyVal τ) vreg (Register.R csPrefix.nextReg) _ _ h_code2
    h_vregR h_dentry2 h_wtp
  have h_run := oseair_runN_trans (oseair_runN_trans h_run0' h_runR) h_run2
  -- memory: the source's write lands at the same address on both sides
  have h_sms1 : SourceMemSim ρa' ρt' s1.mem sR.mem := by
    intro a v h_find
    rw [h_find1] at h_find
    rw [h_smem]
    exact SourceMemSim.rename_mono h_incr_a h_incr_t h_sms a v h_find
  have h_dom : ∀ k, k < mvals.length →
      ρa' (s_mir.mem.addrStart + k) = some (s_mir.mem.addrStart + k) := by
    intro k hk
    exact h_ra_dom k (by rw [h_mlen] at hk; exact Nat.lt_of_lt_of_le hk h_fit)
  have h_sms' := SourceMemSim.writeWordSeq_extend h_id_a' _ _ _ _ _ h_valsRel h_dom
    h_sms1
  -- rebuild the invariant under both extended renames
  refine ⟨_, _, _, _, h_incr_a, h_incr_t, h_run, ?_⟩
  refine ⟨CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix,
    ⟨prefixCompileState_succ (by rw [h_pc1]; exact h_csAt)
      (by rw [h_pc1]; exact h_stmt) h_stmtOut, ?_⟩, ?_, h_sms',
    h_psim3w, h_id_a', h_wf_t', ?_, ?_, ?_, ?_⟩
  · show sR.pc + 1 = _
    rw [h_pcR, h_stmtRun]
    simp [emit]
  · intro σ' loc' binding' h_env'
    obtain ⟨reg', base', tag', h_pi', h_entry', h_ra', h_rt', h_nw', h_dom'⟩ :=
      h_lbsR loc' binding' h_env'
    refine ⟨reg', base', tag', ?_, h_entry', h_ra', h_rt', h_nw', h_dom'⟩
    rw [h_stmtRun, getPlaceInfo_emit]
    exact h_pi'
  · show TagRenameBounded _ perms₃.NextTag p3w.NextTag
    rw [sb_write_NextTag h_useMut_src', sb_write_NextTag h_useMut_tgt]
    exact h_tbdR
  · simp only [AllocLockstep, mirlite_writeWordSeq_addrStart,
      oseair_writeWordSeq_addrStart, h_smem, h_memstart1]
    show (oseair.allocate s_osea.mem (obseq.typeSize (layoutToTyVal σ))).2.addrStart
      = _
    simp only [oseair.allocate]
    rw [h_addr_eq, h_sz]
  · intro σ' loc' h_none
    have h_none1 : mirlite.Env.lookup s1.env loc' = none := h_none
    rw [h_env1] at h_none1
    by_cases h_idx : loc'.idx = dstLoc.idx
    · exfalso
      simp only [mirlite.Env.lookup, mirlite.Env.set, h_idx, if_pos rfl]
        at h_none1
      exact absurd h_none1 (by simp)
    have h_idxv : loc'.idx.1 ≠ dstLoc.idx.1 := fun h => h_idx (Fin.ext h)
    have h_none0 : mirlite.Env.lookup s_mir.env loc' = none := by
      simpa only [mirlite.Env.lookup, mirlite.Env.set, if_neg h_idx]
        using h_none1
    rw [h_stmtRun, getPlaceInfo_emit]
    simp only [getPlaceInfo]
    rw [h_prmR]
    show getPlaceInfo (setPlaceInfo
      (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
        [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
      dstLoc.idx.1 (Register.R csPrefix.nextReg, σ)) _ = _
    rw [getPlaceInfo_setPlaceInfo_ne _ h_idxv]
    exact h_unmap loc' h_none0
  · intro idx reg'' σ'' h_look
    rw [h_stmtRun] at h_look ⊢
    rw [getPlaceInfo_emit] at h_look
    have h_cs : getPlaceInfo (setPlaceInfo
      (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
        [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
      dstLoc.idx.1 (Register.R csPrefix.nextReg, σ)) idx = some (reg'', σ'') := by
      show ((setPlaceInfo
      (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
        [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
      dstLoc.idx.1 (Register.R csPrefix.nextReg, σ))).placeRegMap.lookup _ = _
      rw [← h_prmR]
      exact h_look
    refine RegisterBelow.mono ?_ (h_prb1 _ _ _ h_cs)
    simpa only [emit] using h_regmonoR



/-- **The fresh-root allocation prologue** — everything a leaf whose
    destination local is UNBOUND must establish before it can look at
    the rvalue: mirlite `own`s a fresh block and binds the local, oseair
    `Alloc`s one and binds a fresh register to it, and both renames grow
    (`ρa` by the identity block, `ρt` by the root tag pair).

    The caller does the `preparePlaceAssign` case split itself -- that is
    where its `h_step` lives -- and hands the success equation over; what
    comes back is the whole post-allocation world: the two allocation
    facts, the five `s1` equations, the rename growth, and the
    `LocalBindingSim`/`PlaceRegMapBound` at the post-`Alloc` states,
    which is exactly the start state a SOURCE package takes. -/
theorem copy_freshroot_prologue
    {τ : LayoutTy} {dstLoc : Local Γ τ} {csPrefix : CompilerState}
    {s1 : mirlite.State MSB Γ}
    (h_envD : mirlite.Env.lookup s_mir.env dstLoc = none)
    (h_prep : mirlite.allocateBase MSB s_mir dstLoc = mirlite.Result.ok s1)
    (h_id_a : IdentityOnDomain ρa) (h_wf_t : TagRenameWF ρt)
    (h_tbd : TagRenameBounded ρt s_mir.perms.NextTag s_osea.perms.NextTag)
    (h_psim : PermSim ρt s_mir.perms s_osea.perms)
    (h_alloc : AllocLockstep s_mir.mem s_osea.mem)
    (h_lbs : LocalBindingSim ρa ρt s_mir.env s_osea csPrefix)
    (h_prb : PlaceRegMapBound csPrefix)
    (h_pi_none : getPlaceInfo csPrefix dstLoc.idx.1 = none)
    -- the ADDRESS rename grows however the caller likes -- a whole block for
    -- a copy, a single address for a borrow -- so its four facts come in
    {ρa' : AddrRenameMap}
    (h_incr_a : AddrRenameIncr ρa ρa') (h_id_a' : IdentityOnDomain ρa')
    (h_ra_base : ρa' s_mir.mem.addrStart = some s_mir.mem.addrStart)
    (h_ra_dom : ∀ k, k < blockSize τ →
      ρa' (s_mir.mem.addrStart + k) = some (s_mir.mem.addrStart + k)) :
    ∃ (permsOwned tgtPerms : MSB.State),
      -- the two allocations
      MSB.own s_osea.perms s_osea.mem.addrStart (obseq.typeSize (layoutToTyVal τ))
        = .ok (tgtPerms, s_osea.perms.NextTag) ∧
      -- the post-allocation mirlite state
      s1.perms = permsOwned ∧
      s1.pc = s_mir.pc ∧
      s1.env = mirlite.Env.set s_mir.env dstLoc
        { addr := s_mir.mem.addrStart, tag := s_mir.perms.NextTag } ∧
      mirlite.Env.lookup s1.env dstLoc
        = some { addr := s_mir.mem.addrStart, tag := s_mir.perms.NextTag } ∧
      s1.mem.addrStart = s_mir.mem.addrStart + blockSize τ ∧
      (∀ a, mirlite.Mem.find? s1.mem a = mirlite.Mem.find? s_mir.mem a) ∧
      -- the two renames grow
      TagRenameIncr ρt (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag) ∧
      TagRenameWF (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag) ∧
      TagRenameBounded (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag) permsOwned.NextTag tgtPerms.NextTag ∧
      PermSim (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag) permsOwned tgtPerms ∧
      -- and the post-`Alloc` states are a start state for a source package
      CompilerM.run (ensureLocalRegE dstLoc) csPrefix = (setPlaceInfo
      (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
        [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal τ))])
      dstLoc.idx.1 (Register.R csPrefix.nextReg, τ)) ∧
      PlaceRegMapBound (setPlaceInfo
      (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
        [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal τ))])
      dstLoc.idx.1 (Register.R csPrefix.nextReg, τ)) ∧
      LocalBindingSim ρa' (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag) s1.env
        { s_osea with
      mem := (oseair.allocate s_osea.mem (obseq.typeSize (layoutToTyVal τ))).2,
      perms := tgtPerms,
      reg := oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
        (obseq.TyVal.PTy, [Val.Ptr s_osea.mem.addrStart 0
          (obseq.typeSize (layoutToTyVal τ)) s_osea.perms.NextTag]),
      pc := s_osea.pc + 1 }
        (setPlaceInfo
      (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
        [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal τ))])
      dstLoc.idx.1 (Register.R csPrefix.nextReg, τ)) := by
  simp only [mirAlloc] at h_prep
  cases h_own_src : MSB.own s_mir.perms s_mir.mem.addrStart (blockSize τ) with
  | error e => rw [h_own_src] at h_prep; simp at h_prep
  | ok pr =>
  obtain ⟨permsOwned, tagS⟩ := pr
  rw [h_own_src] at h_prep
  injection h_prep with h_s1
  obtain ⟨tgtPerms, h_own_tgt, h_tagS_eq, h_incr_t, h_wf_t', h_tbd', h_psim'⟩ :=
    sb_own_respects_PermSim h_psim h_wf_t h_tbd h_own_src
  subst h_tagS_eq
  have h_addr_eq : s_osea.mem.addrStart = s_mir.mem.addrStart := h_alloc
  have h_rt_new : (ρt.extend s_mir.perms.NextTag s_osea.perms.NextTag) s_mir.perms.NextTag = some s_osea.perms.NextTag :=
    TagRenameMap.extend_self _ _ _
  have h0 : wildcardTag < s_mir.perms.NextTag := (h_tbd _ _ h_wf_t.2).1
  have h_nw : (s_mir.perms.NextTag == wildcardTag) = false := by grind
  have h_sz : obseq.typeSize (layoutToTyVal τ) = blockSize τ :=
    obseq.typeSize_layoutToTyVal _
  have h_erun : CompilerM.run (ensureLocalRegE dstLoc) csPrefix = (setPlaceInfo
      (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
        [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal τ))])
      dstLoc.idx.1 (Register.R csPrefix.nextReg, τ)) :=
    (ensureLocalRegE_fresh (loc := dstLoc) h_pi_none).1
  have h_pi_new : getPlaceInfo (setPlaceInfo
      (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
        [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal τ))])
      dstLoc.idx.1 (Register.R csPrefix.nextReg, τ))
      dstLoc.idx.1 = some (Register.R csPrefix.nextReg, τ) :=
    getPlaceInfo_setPlaceInfo_self _ _ _
  refine ⟨permsOwned, tgtPerms,
    (by rw [h_sz, h_addr_eq]; exact h_own_tgt),
    (by rw [← h_s1]), (by rw [← h_s1]), (by rw [← h_s1]),
    (by rw [← h_s1]; simp [mirlite.Env.lookup, mirlite.Env.set]),
    (by rw [← h_s1]),
    (fun a => by rw [← h_s1]; rfl),
    h_incr_t, h_wf_t', h_tbd', h_psim',
    h_erun, ?_, ?_⟩
  · intro idx reg τ'' h_look
    by_cases h_i : idx = dstLoc.idx.1
    · subst h_i
      rw [getPlaceInfo_setPlaceInfo_self] at h_look
      grind [emit, setPlaceInfo]
    · rw [getPlaceInfo_setPlaceInfo_ne _ h_i] at h_look
      refine RegisterBelow.mono ?_ (h_prb _ _ _ h_look)
      simp only [emit, setPlaceInfo]
      grind
  · rw [← h_s1]
    intro τ' loc' binding' h_env'
    by_cases h_idx : loc'.idx = dstLoc.idx
    · have h_ty : τ' = τ := by
        rw [← loc'.hTy, h_idx, dstLoc.hTy]
      subst h_ty
      have h_b : binding' = { addr := s_mir.mem.addrStart,
                              tag := s_mir.perms.NextTag } := by grind
      subst h_b
      refine ⟨Register.R csPrefix.nextReg, s_mir.mem.addrStart,
        s_osea.perms.NextTag, ?_, ?_, ?_, h_rt_new, h_nw, ?_⟩
      · rw [show loc'.idx.1 = dstLoc.idx.1 from congrArg Fin.val h_idx]
        exact h_pi_new
      · show oseair.RegMap.lookup _ _ = _
        rw [← h_addr_eq, ← h_sz]
        exact RegMap.lookup_insert_self _ _ _
      · exact h_ra_base
      · intro k hk
        exact ⟨s_mir.mem.addrStart + k, h_ra_dom k hk⟩
    · have h_env'' : mirlite.Env.lookup s_mir.env loc' = some binding' := by
        simpa only [mirlite.Env.lookup, mirlite.Env.set, if_neg h_idx]
          using h_env'
      obtain ⟨reg', base', tag', h_pi', h_entry', h_ra', h_rt', h_nw', h_dom'⟩ :=
        h_lbs loc' binding' h_env''
      have h_idxv : loc'.idx.1 ≠ dstLoc.idx.1 := by grind
      have h_regne : reg' ≠ Register.R csPrefix.nextReg := by
        cases reg' with
        | R n =>
            have h_lt := h_prb _ _ _ h_pi'
            grind
      refine ⟨reg', base', tag', ?_, ?_, h_incr_a _ _ h_ra',
        h_incr_t _ _ h_rt', h_nw',
        fun k hk => ⟨(h_dom' k hk).choose,
          h_incr_a _ _ (h_dom' k hk).choose_spec⟩⟩
      · rw [getPlaceInfo_setPlaceInfo_ne _ h_idxv]
        exact h_pi'
      · show oseair.RegMap.lookup _ _ = _
        rw [RegMap.lookup_insert_ne _ h_regne]
        exact h_entry'



/-- **The projected fresh-root write seam** — the destination half when
    the statement allocates a root and stores into a FIELD of it at a
    nonzero offset. Where `copy_freshroot_write_after_read` stores
    straight through the root register, here the compiler mints an
    interior `Borrow(Mut)` at the offset, stores through THAT, and
    retires it with a `Die`:

        Assgn (R csR.nextReg) (Borrow Mut false [] (blockSize τ) root off)
        RStore (layoutToTyVal τ) vreg (R csR.nextReg)
        Die (R csR.nextReg) (blockSize τ)

    That borrow has no mirlite counterpart — mirlite writes the field
    directly — so the three-step ref/use/die must collapse to the
    parent's single write. That is BRIDGE 1
    (`sb_ref_use_die_cancels`), and it is the only real content here;
    everything else is the same abstract post-source bundle
    `copy_freshroot_write_after_read` takes. -/
theorem copy_freshproj_write_after_read
    {σ τ : LayoutTy} {dstLoc : Local Γ σ}
    {ρa' : AddrRenameMap} {ρt' : TagRenameMap}
    (compProg : oseair.Prog)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    {stmt0 : Stmt Γ}
    (h_stmt : prog.get? s_mir.pc = some stmt0)
    {csPrefix : CompilerState}
    (h_csAt : csAt cs0 prog s_mir.pc csPrefix)
    {stmtOut : ResultWithEvidence Unit (fun _ => StmtEvidence stmt0)}
    (h_stmtOut : CheckedCompilerM.value (compileStmtChecked stmt0) csPrefix
      = Except.ok stmtOut)
    (h_sms : SourceMemSim ρa ρt s_mir.mem s_osea.mem)
    (h_unmap : UnboundLocalsUnmapped s_mir.env csPrefix)
    (h_prb : PlaceRegMapBound csPrefix)
    {s1 : mirlite.State MSB Γ}
    (h_lookup_set : mirlite.Env.lookup s1.env dstLoc
      = some { addr := s_mir.mem.addrStart, tag := s_mir.perms.NextTag })
    (h_env1 : s1.env = mirlite.Env.set s_mir.env dstLoc
      { addr := s_mir.mem.addrStart, tag := s_mir.perms.NextTag })
    (h_pc1 : s1.pc = s_mir.pc)
    (h_memstart1 : s1.mem.addrStart = s_mir.mem.addrStart + blockSize σ)
    (h_find1 : ∀ a, mirlite.Mem.find? s1.mem a = mirlite.Mem.find? s_mir.mem a)
    (h_addr_eq : s_osea.mem.addrStart = s_mir.mem.addrStart)
    (h_sz : obseq.typeSize (layoutToTyVal σ) = blockSize σ)
    {tgtPerms : MSB.State} {n0 : Nat}
    (h_run0' : oseair.runN MSB n0 s_osea compProg = oseair.Result.Ok
      { s_osea with
      mem := (oseair.allocate s_osea.mem (obseq.typeSize (layoutToTyVal σ))).2,
      perms := tgtPerms,
      reg := oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
        (obseq.TyVal.PTy, [Val.Ptr s_osea.mem.addrStart 0
          (obseq.typeSize (layoutToTyVal σ)) s_osea.perms.NextTag]),
      pc := s_osea.pc + 1 })
    (h_incr_a : AddrRenameIncr ρa ρa') (h_incr_t : TagRenameIncr ρt ρt')
    (h_id_a' : IdentityOnDomain ρa') (h_wf_t' : TagRenameWF ρt')
    (h_ra_dom : ∀ k, k < blockSize σ →
      ρa' (s_mir.mem.addrStart + k) = some (s_mir.mem.addrStart + k))
    (h_prb1 : PlaceRegMapBound (setPlaceInfo
      (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
        [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
      dstLoc.idx.1 (Register.R csPrefix.nextReg, σ)))
    -- the destination FIELD: its offset inside the root, and that it fits
    (off : Nat) (h_fit : off + blockSize τ ≤ blockSize σ)
    -- the POST-SOURCE bundle
    {csR : CompilerState} {sR : oseair.State MSB} {vreg : Register}
    {vals : List Val} {nR : Nat} {perms₂ : MSB.State}
    (h_runR : oseair.runN MSB nR
      { s_osea with
      mem := (oseair.allocate s_osea.mem (obseq.typeSize (layoutToTyVal σ))).2,
      perms := tgtPerms,
      reg := oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
        (obseq.TyVal.PTy, [Val.Ptr s_osea.mem.addrStart 0
          (obseq.typeSize (layoutToTyVal σ)) s_osea.perms.NextTag]),
      pc := s_osea.pc + 1 } compProg = oseair.Result.Ok sR)
    (h_prmR : csR.placeRegMap = ((setPlaceInfo
      (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
        [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
      dstLoc.idx.1 (Register.R csPrefix.nextReg, σ))).placeRegMap)
    (h_regmonoR : ((setPlaceInfo
      (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
        [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
      dstLoc.idx.1 (Register.R csPrefix.nextReg, σ))).nextReg ≤ csR.nextReg)
    (h_lbsR : LocalBindingSim ρa' ρt' s1.env sR csR)
    (h_psimR : PermSim ρt' perms₂ sR.perms)
    (h_tbdR : TagRenameBounded ρt' perms₂.NextTag sR.perms.NextTag)
    (h_smem : sR.mem
      = ({ s_osea with
      mem := (oseair.allocate s_osea.mem (obseq.typeSize (layoutToTyVal σ))).2,
      perms := tgtPerms,
      reg := oseair.RegMap.insert s_osea.reg (Register.R csPrefix.nextReg)
        (obseq.TyVal.PTy, [Val.Ptr s_osea.mem.addrStart 0
          (obseq.typeSize (layoutToTyVal σ)) s_osea.perms.NextTag]),
      pc := s_osea.pc + 1 }).mem)
    (h_pcR : sR.pc = csR.nextLabel)
    (h_vregR : oseair.RegMap.lookup sR.reg vreg = some (layoutToTyVal τ, vals))
    (h_vbelow : RegisterBelow csR.nextReg vreg)
    (h_vlen : vals.length = blockSize τ)
    -- the three instructions the destination costs, and the two facts the
    -- rebuild needs about the statement's own compiled state (a leaf proves
    -- all five from its `h_stmtRun`, which spells its tower its own way)
    (h_code1 : compProg sR.pc
      = some (Instr.Assgn (Register.R csR.nextReg)
          (Rhs.Borrow RefKind.Mut false [] (blockSize τ)
            (Register.R csPrefix.nextReg) off)))
    (h_code2 : compProg (sR.pc + 1)
      = some (Instr.RStore (layoutToTyVal τ) vreg (Register.R csR.nextReg)))
    (h_code3 : compProg (sR.pc + 1 + 1)
      = some (Instr.Die (Register.R csR.nextReg) (blockSize τ)))
    (h_lab : sR.pc + 1 + 1 + 1
      = (CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix).nextLabel)
    (h_prmS : (CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix).placeRegMap
      = csR.placeRegMap)
    (h_nextRegLe : csR.nextReg
      ≤ (CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix).nextReg)
    -- the mirlite write, into the FIELD
    {rd : mirlite.PlaceRes} {mvals : List mirlite.MemValue}
    (h_mlen : mvals.length = blockSize τ)
    (h_rdaddr : rd.addr = s_mir.mem.addrStart + off)
    (h_rdtag : rd.tag = s_mir.perms.NextTag)
    (h_rdbase : rd.allocBase = s_mir.mem.addrStart)
    (h_rdsize : rd.allocSize = blockSize σ)
    (h_valsRel : ListRel (MemValSim ρa' ρt') mvals vals)
    (h_step : mirlite.writeResolvedPlace (τ := τ) MSB
      { s1 with perms := perms₂ } rd mvals h_mlen = mirlite.Result.ok s_mir') :
    ∃ (ρa'' : AddrRenameMap) (ρt'' : TagRenameMap) (s_osea' : oseair.State MSB)
      (n : Nat),
      AddrRenameIncr ρa ρa'' ∧
      TagRenameIncr ρt ρt'' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa'' ρt'' s_mir' s_osea' := by
  obtain ⟨h_nb, perms₃, h_useMut_src, rfl⟩ := writeResolvedPlace_ok_inv h_step
  have h_useMut_src' : MSB.useMut perms₂ (s_mir.mem.addrStart + off) (blockSize τ)
      s_mir.perms.NextTag = .ok perms₃ := by
    rw [← h_rdaddr, ← h_rdtag, ← h_mlen]
    exact h_useMut_src
  -- the root's register entry, from the post-source binding
  have h_pi_new : getPlaceInfo (setPlaceInfo
      (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
        [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
      dstLoc.idx.1 (Register.R csPrefix.nextReg, σ))
      dstLoc.idx.1 = some (Register.R csPrefix.nextReg, σ) :=
    getPlaceInfo_setPlaceInfo_self _ _ _
  obtain ⟨dstReg2, baseD2, tagD2, h_piD2, h_entryD2, h_raD2, h_rtD2,
    h_nwD2, h_domD2⟩ := h_lbsR dstLoc _ h_lookup_set
  have h_piD2' : getPlaceInfo (setPlaceInfo
      (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
        [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
      dstLoc.idx.1 (Register.R csPrefix.nextReg, σ))
      dstLoc.idx.1 = some (dstReg2, σ) := by
    show ((setPlaceInfo
      (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
        [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
      dstLoc.idx.1 (Register.R csPrefix.nextReg, σ))).placeRegMap.lookup _ = _
    rw [← h_prmR]
    exact h_piD2
  have h_dr2 : dstReg2 = Register.R csPrefix.nextReg := by grind
  have h_baseD2 : baseD2 = s_mir.mem.addrStart := (h_id_a' _ _ h_raD2).symm
  rw [h_dr2, h_baseD2] at h_entryD2
  -- BRIDGE 3 on the parent write, then BRIDGE 1 on the interior borrow
  obtain ⟨qW, h_useMut_tgt, h_psim3⟩ :=
    sb_write_respects_PermSim h_psimR h_wf_t' h_rtD2 h_nwD2 h_useMut_src'
  obtain ⟨q1, h_ref_dst⟩ := sb_ref_Mut_ok_of_sb_write_ok h_useMut_tgt
  have h_unprot := freshTag_not_protected h_psimR h_tbdR
  have h2 : wildcardTag < sR.perms.NextTag := (h_tbdR _ _ h_wf_t'.2).2
  have h_ntw' : (sR.perms.NextTag == wildcardTag) = false := by grind
  obtain ⟨q2, q3, qAcc', h_wr1, h_die1, h_wr2, h_sm, h_ex, h_pf, h_ntle⟩ :=
    sb_ref_use_die_cancels h_ntw' h_unprot h_ref_dst
  have h_qAcc : qAcc' = qW := by grind
  subst h_qAcc
  -- the interior `Borrow(Mut)` off the root
  have h_off_le : s_mir.mem.addrStart + 0 + off + blockSize τ
      ≤ s_mir.mem.addrStart + blockSize σ := by
    simp only [Nat.add_zero, Nat.add_assoc]
    exact Nat.add_le_add_left h_fit _
  have h_ref_dst' : MSB.ref sR.perms (s_mir.mem.addrStart + 0 + off)
      (blockSize τ) tagD2 RefKind.Mut false []
      = .ok (q1, sR.perms.NextTag) := by
    simp only [Nat.add_zero]
    simpa using h_ref_dst
  have h_run1 := runN_Assgn_Borrow_step compProg sR
    (Register.R csR.nextReg) (Register.R csPrefix.nextReg) RefKind.Mut false []
    (blockSize τ) off h_code1 h_entryD2 h_off_le h_ref_dst'
  -- NAME the post-borrow state: a nested record update does not elaborate
  -- inside a `have` type (durable/transport-compiled-states-by-defeq)
  obtain ⟨sB, hsB⟩ : ∃ sB : oseair.State MSB, sB
      = { sR with
          perms := q1,
          reg := oseair.RegMap.insert sR.reg (Register.R csR.nextReg)
            (obseq.TyVal.PTy, [Val.Ptr s_mir.mem.addrStart (0 + off) (blockSize σ)
              sR.perms.NextTag]),
          pc := sR.pc + 1 } := ⟨_, rfl⟩
  rw [← hsB] at h_run1
  have h_sBreg : sB.reg = oseair.RegMap.insert sR.reg (Register.R csR.nextReg)
      (obseq.TyVal.PTy, [Val.Ptr s_mir.mem.addrStart (0 + off) (blockSize σ)
        sR.perms.NextTag]) := by rw [hsB]
  have h_sBperms : sB.perms = q1 := by rw [hsB]
  have h_sBmem : sB.mem = sR.mem := by rw [hsB]
  have h_sBpc : sB.pc = sR.pc + 1 := by rw [hsB]
  -- the store THROUGH the interior borrow (BRIDGE 2)
  have h_entry_tmp : PtrRegisterEntry sB.reg (Register.R csR.nextReg)
      rd.allocBase (rd.addr - rd.allocBase) rd.allocSize sR.perms.NextTag := by
    rw [h_sBreg, h_rdaddr, h_rdbase, h_rdsize, Nat.add_sub_cancel_left,
      Nat.zero_add]
    exact RegMap.lookup_insert_self _ _ _
  have h_wr1' : MSB.useMut sB.perms rd.addr vals.length sR.perms.NextTag
      = .ok q2 := by
    rw [h_sBperms, h_vlen, h_rdaddr]
    exact h_wr1
  have h_smsB : SourceMemSim ρa' ρt' { s1 with perms := perms₂ }.mem sB.mem := by
    intro a v h_find
    rw [h_find1] at h_find
    rw [h_sBmem, h_smem]
    exact SourceMemSim.rename_mono h_incr_a h_incr_t h_sms a v h_find
  obtain ⟨h_wtp, h_sms'⟩ :=
    writeThroughPtr_sim (τ := τ) (s_osea := sB) (resolved := rd)
      (s_pre := { s1 with perms := perms₂ })
      "RStore Invalid Regs" mvals vals h_mlen h_valsRel h_id_a'
      h_entry_tmp h_wr1' h_smsB
      (by rw [h_rdaddr, h_rdbase]; exact Nat.le_add_right _ _)
      (fun k hk => by
        rw [h_rdaddr, Nat.add_assoc]
        refine h_ra_dom (off + k) ?_
        rw [h_mlen] at hk
        omega)
      h_step
  have h_vregB : oseair.RegMap.lookup sB.reg vreg
      = some (layoutToTyVal τ, vals) := by
    rw [h_sBreg, RegMap.lookup_insert_ne _ (by
      intro h_eq
      cases vreg with
      | R m =>
        injection h_eq with h_eq
        subst h_eq
        exact absurd h_vbelow (Nat.not_lt.mpr (Nat.le_refl _)))]
    exact h_vregR
  have h_run2 := runN_RStore_step compProg sB _
    (layoutToTyVal τ) vreg (Register.R csR.nextReg) vals _
    (by rw [h_sBpc]; exact h_code2) h_vregB h_entry_tmp h_wtp
  -- and the `Die` that retires the interior borrow
  have h_run3 := runN_Die_step compProg
    { sB with
        perms := q2,
        mem := oseair.writeWordSeq sB.mem rd.addr vals,
        pc := sB.pc + 1 }
    (Register.R csR.nextReg) (blockSize τ)
    (by show compProg (sB.pc + 1) = _; rw [h_sBpc]; exact h_code3)
    (by
      show oseair.RegMap.lookup sB.reg _ = _
      exact h_entry_tmp)
    (by
      show MSB.die q2 (rd.allocBase + (rd.addr - rd.allocBase)) (blockSize τ)
        sR.perms.NextTag = _
      rw [h_rdaddr, h_rdbase, Nat.add_sub_cancel_left]
      simpa using h_die1)
  have h_run := oseair_runN_trans
    (oseair_runN_trans (oseair_runN_trans (oseair_runN_trans h_run0' h_runR) h_run1)
      h_run2) h_run3
  -- BRIDGE 1 collapses the triple to the parent's write
  have h_psim4 : PermSim ρt' perms₃ q3 := by
    obtain ⟨hs, hp, he, hn⟩ := h_psim3
    exact ⟨by rw [h_sm]; exact hs, by rw [h_pf]; exact hp,
           by rw [h_ex]; exact he, Nat.le_trans hn h_ntle⟩
  -- rebuild the invariant
  refine ⟨_, _, _, _, h_incr_a, h_incr_t, h_run, ?_⟩
  refine ⟨CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix,
    ⟨prefixCompileState_succ (by rw [h_pc1]; exact h_csAt)
      (by rw [h_pc1]; exact h_stmt) h_stmtOut, ?_⟩, ?_, h_sms',
    h_psim4, h_id_a', h_wf_t', ?_, ?_, ?_, ?_⟩
  · show sB.pc + 1 + 1 = _
    rw [h_sBpc]
    exact h_lab
  · refine LocalBindingSim.placeRegMap_congr ?_
      (LocalBindingSim.insert_fresh_reg h_lbsR
        (by
          intro idx reg τ'' h_look
          have h_cs : getPlaceInfo (setPlaceInfo
      (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
        [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
      dstLoc.idx.1 (Register.R csPrefix.nextReg, σ)) idx = some (reg, τ'') := by
            show ((setPlaceInfo
      (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
        [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
      dstLoc.idx.1 (Register.R csPrefix.nextReg, σ))).placeRegMap.lookup _ = _
            rw [← h_prmR]
            exact h_look
          exact RegisterBelow.mono h_regmonoR (h_prb1 _ _ _ h_cs))
        (Nat.le_refl _) (by show sB.reg = _; exact h_sBreg))
    exact h_prmS
  · show TagRenameBounded _ perms₃.NextTag q3.NextTag
    rw [sb_write_NextTag h_useMut_src']
    exact TagRenameBounded.mono h_tbdR (Nat.le_refl _)
      (by rw [← sb_write_NextTag h_useMut_tgt]; exact h_ntle)
  · simp only [AllocLockstep, mirlite_writeWordSeq_addrStart,
      oseair_writeWordSeq_addrStart, h_sBmem, h_smem, h_memstart1]
    show (oseair.allocate s_osea.mem (obseq.typeSize (layoutToTyVal σ))).2.addrStart
      = _
    simp only [oseair.allocate]
    rw [h_addr_eq, h_sz]
  · intro τ' loc' h_none
    have h_none1 : mirlite.Env.lookup s1.env loc' = none := h_none
    rw [h_env1] at h_none1
    by_cases h_idx : loc'.idx = dstLoc.idx
    · exfalso
      simp only [mirlite.Env.lookup, mirlite.Env.set, h_idx, if_pos rfl]
        at h_none1
      exact absurd h_none1 (by simp)
    have h_idxv : loc'.idx.1 ≠ dstLoc.idx.1 := fun h => h_idx (Fin.ext h)
    have h_none0 : mirlite.Env.lookup s_mir.env loc' = none := by
      simpa only [mirlite.Env.lookup, mirlite.Env.set, if_neg h_idx]
        using h_none1
    show getPlaceInfo _ _ = _
    simp only [getPlaceInfo]
    rw [h_prmS, h_prmR]
    show getPlaceInfo (setPlaceInfo
      (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
        [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
      dstLoc.idx.1 (Register.R csPrefix.nextReg, σ)) _ = _
    rw [getPlaceInfo_setPlaceInfo_ne _ h_idxv]
    exact h_unmap loc' h_none0
  · intro idx reg'' τ'' h_look
    have h_look' : getPlaceInfo csR idx = some (reg'', τ'') := by
      show csR.placeRegMap.lookup _ = _
      rw [← h_prmS]
      exact h_look
    have h_cs : getPlaceInfo (setPlaceInfo
      (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
        [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
      dstLoc.idx.1 (Register.R csPrefix.nextReg, σ)) idx = some (reg'', τ'') := by
      show ((setPlaceInfo
      (emit { csPrefix with nextReg := csPrefix.nextReg + 1 }
        [Instr.Assgn (Register.R csPrefix.nextReg) (Rhs.Alloc (layoutToTyVal σ))])
      dstLoc.idx.1 (Register.R csPrefix.nextReg, σ))).placeRegMap.lookup _ = _
      rw [← h_prmR]
      exact h_look'
    refine RegisterBelow.mono ?_ (h_prb1 _ _ _ h_cs)
    exact Nat.le_trans h_regmonoR h_nextRegLe



/-- **The local-root borrow** — ref's source package, the borrow twin of
    copy's `copy_chainsrc_read`. The rvalue `&kind x` or `&kind x.f`
    lowers to ONE instruction, a `Borrow` off the source local's own
    register at the path offset, so the package is short; what it is
    for is the BUNDLE it hands back, which is exactly what both write
    seams take.

    The offset makes it serve both source shapes: `off = 0` is the plain
    local, `off = pathOffset f` a projection of one, and the borrowed
    pointer keeps the ROOT's size field (`blockSize σs`) either way —
    the borrow narrows the permission, not the provenance.

    Stated at an abstract start `(sM, sA, csA)` like copy's packages, so
    a FRESH leaf can call it at its post-`Alloc` states, with `ρa`/`ρt`
    already extended by the allocation. -/
theorem ref_local_borrow
    (τ σs : LayoutTy) {bS : mirlite.Binding}
    (kind : RefKind) (prot : Bool) (mask : List Bool) (off : Nat)
    (compProg : oseair.Prog)
    (sM : mirlite.State MSB Γ) (sA : oseair.State MSB) (csA : CompilerState)
    (h_id_a : IdentityOnDomain ρa) (h_wf_t : TagRenameWF ρt)
    (h_tbd : TagRenameBounded ρt sM.perms.NextTag sA.perms.NextTag)
    (h_lbs : LocalBindingSim ρa ρt sM.env sA csA)
    (h_prb : PlaceRegMapBound csA)
    (h_psim : PermSim ρt sM.perms sA.perms)
    (h_pc : sA.pc = csA.nextLabel)
    {srcReg : Register} {tagS : Tag}
    (h_entryS : PtrRegisterEntry sA.reg srcReg bS.addr 0 (blockSize σs) tagS)
    (h_raS : ρa bS.addr = some bS.addr)
    (h_rtS : ρt bS.tag = some tagS)
    (h_nwS : (bS.tag == wildcardTag) = false)
    (h_domS : ∀ k, k < blockSize σs → ∃ a, ρa (bS.addr + k) = some a)
    (h_fit : off + blockSize τ ≤ blockSize σs)
    {perms' : MSB.State} {freshTag : Tag}
    (h_ref_src : MSB.ref sM.perms (bS.addr + off) (blockSize τ) bS.tag kind prot mask
      = .ok (perms', freshTag))
    (h_code : compProg sA.pc
      = some (Instr.Assgn (Register.R csA.nextReg)
          (Rhs.Borrow kind prot mask (blockSize τ) srcReg off))) :
    ∃ tgtPerms : MSB.State,
      -- the tag mirlite minted IS its next tag (the caller's `h_step` still
      -- says `freshTag`, so this comes back as an `rfl` to substitute)
      freshTag = sM.perms.NextTag ∧
      TagRenameIncr ρt (ρt.extend sM.perms.NextTag sA.perms.NextTag) ∧
      TagRenameWF (ρt.extend sM.perms.NextTag sA.perms.NextTag) ∧
      TagRenameBounded (ρt.extend sM.perms.NextTag sA.perms.NextTag) perms'.NextTag tgtPerms.NextTag ∧
      PermSim (ρt.extend sM.perms.NextTag sA.perms.NextTag) perms' tgtPerms ∧
      oseair.runN MSB 1 sA compProg = oseair.Result.Ok
        { sA with
        perms := tgtPerms,
        reg := oseair.RegMap.insert sA.reg (Register.R csA.nextReg)
          (obseq.TyVal.PTy, [Val.Ptr bS.addr (0 + off) (blockSize σs) sA.perms.NextTag]),
        pc := sA.pc + 1 } ∧
      LocalBindingSim ρa (ρt.extend sM.perms.NextTag sA.perms.NextTag) sM.env
        { sA with
        perms := tgtPerms,
        reg := oseair.RegMap.insert sA.reg (Register.R csA.nextReg)
          (obseq.TyVal.PTy, [Val.Ptr bS.addr (0 + off) (blockSize σs) sA.perms.NextTag]),
        pc := sA.pc + 1 }
        (emit csA
          [Instr.Assgn (Register.R csA.nextReg)
        (Rhs.Borrow kind prot mask (blockSize τ) srcReg off)]) ∧
      ({ sA with
        perms := tgtPerms,
        reg := oseair.RegMap.insert sA.reg (Register.R csA.nextReg)
          (obseq.TyVal.PTy, [Val.Ptr bS.addr (0 + off) (blockSize σs) sA.perms.NextTag]),
        pc := sA.pc + 1 }).pc
        = (emit csA
            [Instr.Assgn (Register.R csA.nextReg)
        (Rhs.Borrow kind prot mask (blockSize τ) srcReg off)]).nextLabel ∧
      ListRel (MemValSim ρa (ρt.extend sM.perms.NextTag sA.perms.NextTag))
        [mirlite.MemValue.ptrVal bS.addr (bS.addr + off - bS.addr) (blockSize σs)
          sM.perms.NextTag]
        [Val.Ptr bS.addr (0 + off) (blockSize σs) sA.perms.NextTag] := by
  obtain ⟨tgtPerms, h_ref_tgt, h_fresh_eq, h_incr_t, h_wf_t', h_tbd', h_psim'⟩ :=
    sb_ref_respects_PermSim h_psim h_wf_t h_tbd h_rtS h_nwS h_ref_src
  subst h_fresh_eq
  have h_rt_new : (ρt.extend sM.perms.NextTag sA.perms.NextTag) sM.perms.NextTag = some sA.perms.NextTag :=
    TagRenameMap.extend_self _ _ _
  have h0 : wildcardTag < sM.perms.NextTag := (h_tbd _ _ h_wf_t.2).1
  have h_nw_new : (sM.perms.NextTag == wildcardTag) = false := by grind
  have h_ref_tgt' : MSB.ref sA.perms (bS.addr + 0 + off) (blockSize τ) tagS
      kind prot mask = .ok (tgtPerms, sA.perms.NextTag) := by
    simpa using h_ref_tgt
  have h_le : bS.addr + 0 + off + blockSize τ ≤ bS.addr + blockSize σs := by
    simp only [Nat.add_zero, Nat.add_assoc]
    exact Nat.add_le_add_left h_fit _
  have h_run := runN_Assgn_Borrow_step compProg sA
    (Register.R csA.nextReg) srcReg kind prot mask (blockSize τ) off
    h_code h_entryS h_le h_ref_tgt'
  refine ⟨tgtPerms, rfl, h_incr_t, h_wf_t', h_tbd', h_psim', by simpa using h_run, ?_,
    (by show sA.pc + 1 = _
        rw [h_pc]
        simp only [emit, List.length_cons, List.length_nil]),
    ⟨⟨h_raS, by simp [Nat.add_sub_cancel_left], rfl, h_rt_new, h_nw_new,
      h_domS⟩, trivial⟩⟩
  exact LocalBindingSim.placeRegMap_congr rfl
    (LocalBindingSim.insert_fresh_reg
      (LocalBindingSim.rename_mono (AddrRenameIncr.refl ρa) h_incr_t h_lbs)
      h_prb (Nat.le_refl _) rfl)



/-- **The bound-root projected write seam** — the destination half when
    the destination is a FIELD of a local that is already BOUND, at a
    nonzero offset. Same three instructions as
    `copy_freshproj_write_after_read`, and the same BRIDGE 1 collapse of
    the interior `Borrow(Mut)`'s ref/use/die to the parent's write; what
    changes is where the root comes from — an existing binding rather
    than the statement's own `Alloc`, so there is no rename growth and
    no allocation lockstep to re-establish.

    Interface as in the projected fresh seam: the statement's compiled
    tower is NOT a hypothesis, only the three code facts and the two
    summary facts the rebuild needs, which keeps the seam immune to how
    a caller happens to spell its tower. -/
theorem copy_boundproj_write_after_read
    {τ : LayoutTy} {dbase : Word} {dtag : Tag} {dsize : Nat}
    (compProg : oseair.Prog)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    {stmt0 : Stmt Γ}
    (h_stmt : prog.get? s_mir.pc = some stmt0)
    {csPrefix : CompilerState}
    (h_csAt : csAt cs0 prog s_mir.pc csPrefix)
    {stmtOut : ResultWithEvidence Unit (fun _ => StmtEvidence stmt0)}
    (h_stmtOut : CheckedCompilerM.value (compileStmtChecked stmt0) csPrefix
      = Except.ok stmtOut)
    (h_id_a : IdentityOnDomain ρa) (h_wf_t : TagRenameWF ρt)
    (h_unmap : UnboundLocalsUnmapped s_mir.env csPrefix)
    (h_prb : PlaceRegMapBound csPrefix)
    -- the destination's RESOLVED root -- a bound local's binding or a
    -- chain's resolution, the seam does not care which -- and the register
    -- holding it at the POST-SOURCE state
    {dstReg : Register} {tagD : Tag} (boff : Nat)
    (h_raD : ρa dbase = some dbase)
    (h_rtD : ρt dtag = some tagD)
    (h_nwD : (dtag == wildcardTag) = false)
    (h_domD : ∀ k, k < dsize → ∃ a, ρa (dbase + k) = some a)
    (off : Nat) (h_fit : boff + off + blockSize τ ≤ dsize)
    -- the POST-SOURCE bundle
    {csR : CompilerState} {sR : oseair.State MSB} {vreg : Register}
    {vals : List Val} {nR : Nat} {perms₂ : MSB.State}
    (h_runR : oseair.runN MSB nR s_osea compProg = oseair.Result.Ok sR)
    (h_entryD : PtrRegisterEntry sR.reg dstReg dbase boff dsize tagD)
    (h_sms : SourceMemSim ρa ρt s_mir.mem sR.mem)
    (h_alloc : AllocLockstep s_mir.mem sR.mem)
    (h_prmR : csR.placeRegMap = csPrefix.placeRegMap)
    (h_regmonoR : csPrefix.nextReg ≤ csR.nextReg)
    (h_lbsR : LocalBindingSim ρa ρt s_mir.env sR csR)
    (h_psimR : PermSim ρt perms₂ sR.perms)
    (h_tbdR : TagRenameBounded ρt perms₂.NextTag sR.perms.NextTag)
    (h_pcR : sR.pc = csR.nextLabel)
    (h_vregR : oseair.RegMap.lookup sR.reg vreg = some (layoutToTyVal τ, vals))
    (h_vbelow : RegisterBelow csR.nextReg vreg)
    (h_vlen : vals.length = blockSize τ)
    -- the three instructions the destination costs, and the rebuild's two
    (h_code1 : compProg sR.pc
      = some (Instr.Assgn (Register.R csR.nextReg)
          (Rhs.Borrow RefKind.Mut false [] (blockSize τ) dstReg off)))
    (h_code2 : compProg (sR.pc + 1)
      = some (Instr.RStore (layoutToTyVal τ) vreg (Register.R csR.nextReg)))
    (h_code3 : compProg (sR.pc + 1 + 1)
      = some (Instr.Die (Register.R csR.nextReg) (blockSize τ)))
    (h_lab : sR.pc + 1 + 1 + 1
      = (CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix).nextLabel)
    (h_prmS : (CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix).placeRegMap
      = csR.placeRegMap)
    (h_nextRegLe : csR.nextReg
      ≤ (CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix).nextReg)
    -- the mirlite write, into the FIELD of the bound root
    {rd : mirlite.PlaceRes} {mvals : List mirlite.MemValue}
    (h_mlen : mvals.length = blockSize τ)
    (h_rdaddr : rd.addr = dbase + (boff + off))
    (h_rdtag : rd.tag = dtag)
    (h_rdbase : rd.allocBase = dbase)
    (h_rdsize : rd.allocSize = dsize)
    (h_valsRel : ListRel (MemValSim ρa ρt) mvals vals)
    (h_step : mirlite.writeResolvedPlace (τ := τ) MSB
      { s_mir with perms := perms₂ } rd mvals h_mlen = mirlite.Result.ok s_mir') :
    ∃ (s_osea' : oseair.State MSB) (n : Nat),
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa ρt s_mir' s_osea' := by
  obtain ⟨h_nb, perms₃, h_useMut_src, rfl⟩ := writeResolvedPlace_ok_inv h_step
  have h_useMut_src' : MSB.useMut perms₂ (dbase + (boff + off)) (blockSize τ) dtag
      = .ok perms₃ := by
    rw [← h_rdaddr, ← h_rdtag, ← h_mlen]
    exact h_useMut_src
  -- BRIDGE 3 on the parent write, then BRIDGE 1 on the interior borrow
  obtain ⟨qW, h_useMut_tgt, h_psim2⟩ :=
    sb_write_respects_PermSim h_psimR h_wf_t h_rtD h_nwD h_useMut_src'
  obtain ⟨q1, h_ref_dst⟩ := sb_ref_Mut_ok_of_sb_write_ok h_useMut_tgt
  have h_unprot := freshTag_not_protected h_psimR h_tbdR
  have h2 : wildcardTag < sR.perms.NextTag := (h_tbdR _ _ h_wf_t.2).2
  have h_ntw' : (sR.perms.NextTag == wildcardTag) = false := by grind
  obtain ⟨q2, q3, qAcc', h_wr1, h_die1, h_wr2, h_sm, h_ex, h_pf, h_ntle⟩ :=
    sb_ref_use_die_cancels h_ntw' h_unprot h_ref_dst
  have h_qAcc : qAcc' = qW := by grind
  subst h_qAcc
  -- the interior `Borrow(Mut)` off the destination's own register
  have h_off_le : dbase + boff + off + blockSize τ ≤ dbase + dsize := by
    have h := Nat.add_le_add_left h_fit dbase
    simpa only [Nat.add_assoc] using h
  have h_ref_dst' : MSB.ref sR.perms (dbase + boff + off) (blockSize τ) tagD
      RefKind.Mut false [] = .ok (q1, sR.perms.NextTag) := by
    rw [Nat.add_assoc]
    simpa using h_ref_dst
  have h_run1 := runN_Assgn_Borrow_step compProg sR
    (Register.R csR.nextReg) dstReg RefKind.Mut false [] (blockSize τ) off
    h_code1 h_entryD h_off_le h_ref_dst'
  obtain ⟨sB, hsB⟩ : ∃ sB : oseair.State MSB, sB
      = { sR with
          perms := q1,
          reg := oseair.RegMap.insert sR.reg (Register.R csR.nextReg)
            (obseq.TyVal.PTy, [Val.Ptr dbase (boff + off) dsize sR.perms.NextTag]),
          pc := sR.pc + 1 } := ⟨_, rfl⟩
  rw [← hsB] at h_run1
  have h_sBreg : sB.reg = oseair.RegMap.insert sR.reg (Register.R csR.nextReg)
      (obseq.TyVal.PTy, [Val.Ptr dbase (boff + off) dsize sR.perms.NextTag]) := by rw [hsB]
  have h_sBperms : sB.perms = q1 := by rw [hsB]
  have h_sBmem : sB.mem = sR.mem := by rw [hsB]
  have h_sBpc : sB.pc = sR.pc + 1 := by rw [hsB]
  -- the store THROUGH the interior borrow (BRIDGE 2)
  have h_entry_tmp : PtrRegisterEntry sB.reg (Register.R csR.nextReg)
      rd.allocBase (rd.addr - rd.allocBase) rd.allocSize sR.perms.NextTag := by
    rw [h_sBreg, h_rdaddr, h_rdbase, h_rdsize, Nat.add_sub_cancel_left]
    exact RegMap.lookup_insert_self _ _ _
  have h_wr1' : MSB.useMut sB.perms rd.addr vals.length sR.perms.NextTag
      = .ok q2 := by
    rw [h_sBperms, h_vlen, h_rdaddr]
    exact h_wr1
  have h_smsB : SourceMemSim ρa ρt { s_mir with perms := perms₂ }.mem sB.mem := by
    rw [h_sBmem]
    exact h_sms
  obtain ⟨h_wtp, h_sms'⟩ :=
    writeThroughPtr_sim (τ := τ) (s_osea := sB) (resolved := rd)
      (s_pre := { s_mir with perms := perms₂ })
      "RStore Invalid Regs" mvals vals h_mlen h_valsRel h_id_a
      h_entry_tmp h_wr1' h_smsB
      (by rw [h_rdaddr, h_rdbase]; exact Nat.le_add_right _ _)
      (fun k hk => by
        rw [show rd.addr + k = dbase + (boff + off + k) by
          rw [h_rdaddr, Nat.add_assoc]]
        obtain ⟨a', ha'⟩ := h_domD (boff + off + k) (by rw [h_mlen] at hk; omega)
        rw [ha', h_id_a _ _ ha'])
      h_step
  have h_vregB : oseair.RegMap.lookup sB.reg vreg
      = some (layoutToTyVal τ, vals) := by
    rw [h_sBreg, RegMap.lookup_insert_ne _ (by
      intro h_eq
      cases vreg with
      | R m =>
        injection h_eq with h_eq
        subst h_eq
        exact absurd h_vbelow (Nat.not_lt.mpr (Nat.le_refl _)))]
    exact h_vregR
  have h_run2 := runN_RStore_step compProg sB _
    (layoutToTyVal τ) vreg (Register.R csR.nextReg) vals _
    (by rw [h_sBpc]; exact h_code2) h_vregB h_entry_tmp h_wtp
  -- and the `Die` that retires the interior borrow
  have h_run3 := runN_Die_step compProg
    { sB with
        perms := q2,
        mem := oseair.writeWordSeq sB.mem rd.addr vals,
        pc := sB.pc + 1 }
    (Register.R csR.nextReg) (blockSize τ)
    (by show compProg (sB.pc + 1) = _; rw [h_sBpc]; exact h_code3)
    (by
      show oseair.RegMap.lookup sB.reg _ = _
      have h := h_entry_tmp
      rw [h_rdaddr, h_rdbase, h_rdsize, Nat.add_sub_cancel_left] at h
      exact h)
    (by simpa using h_die1)
  have h_run := oseair_runN_trans
    (oseair_runN_trans (oseair_runN_trans h_runR h_run1) h_run2) h_run3
  -- BRIDGE 1 collapses the triple to the parent's write
  have h_psim4 : PermSim ρt perms₃ q3 := by
    obtain ⟨hs, hp, he, hn⟩ := h_psim2
    exact ⟨by rw [h_sm]; exact hs, by rw [h_pf]; exact hp,
           by rw [h_ex]; exact he, Nat.le_trans hn h_ntle⟩
  -- rebuild the invariant
  refine ⟨_, _, h_run, ?_⟩
  refine ⟨CheckedCompilerM.run (compileStmtChecked stmt0) csPrefix,
    ⟨prefixCompileState_succ h_csAt h_stmt h_stmtOut, ?_⟩, ?_, h_sms',
    h_psim4, h_id_a, h_wf_t, ?_, ?_, ?_, ?_⟩
  · show sB.pc + 1 + 1 = _
    rw [h_sBpc]
    exact h_lab
  · refine LocalBindingSim.placeRegMap_congr h_prmS
      (LocalBindingSim.insert_fresh_reg h_lbsR
        (by
          intro idx reg τ'' h_look
          have h_cs : getPlaceInfo csPrefix idx = some (reg, τ'') := by
            show csPrefix.placeRegMap.lookup _ = _
            rw [← h_prmR]
            exact h_look
          exact RegisterBelow.mono h_regmonoR (h_prb _ _ _ h_cs))
        (Nat.le_refl _) (by show sB.reg = _; exact h_sBreg))
  · show TagRenameBounded _ perms₃.NextTag q3.NextTag
    rw [sb_write_NextTag h_useMut_src']
    exact TagRenameBounded.mono h_tbdR (Nat.le_refl _)
      (by rw [← sb_write_NextTag h_useMut_tgt]; exact h_ntle)
  · show AllocLockstep (mirlite.writeWordSeq s_mir.mem rd.addr mvals) _
    rw [h_sBmem]
    exact h_alloc.writeWordSeq _ _ _ _
  · intro τ' loc' h_none
    show getPlaceInfo _ _ = _
    simp only [getPlaceInfo]
    rw [h_prmS, h_prmR]
    exact h_unmap loc' h_none
  · intro idx reg'' τ'' h_look
    have h_look' : getPlaceInfo csR idx = some (reg'', τ'') := by
      show csR.placeRegMap.lookup _ = _
      rw [← h_prmS]
      exact h_look
    have h_cs : getPlaceInfo csPrefix idx = some (reg'', τ'') := by
      show csPrefix.placeRegMap.lookup _ = _
      rw [← h_prmR]
      exact h_look'
    refine RegisterBelow.mono ?_ (h_prb _ _ _ h_cs)
    exact Nat.le_trans h_regmonoR h_nextRegLe


end

end obseq3.proof
