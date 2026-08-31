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
                simp only [CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
                  CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
                  CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
                  hF, hO, ihr, Except.map]
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
                simp only [CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
                  CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
                  CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
                  hF, hO] <;>
                split <;>
                simp [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM,
                  cleanupInstrs, ihr, h_res, Except.map]
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
                simp only [CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
                  CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
                  CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
                  hF, hO, ihr, Except.map]
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
                simp [CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
                  CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
                  CheckedCompilerM.run_pure, CheckedCompilerM.value_pure,
                  hF, hO, ihr, h_res, CompilerM.run, CompilerM.value,
                  freshRegM, freshReg, emitM, cleanupInstrs, Except.map]
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
                simp only [placeToBorrowRegChecked, CheckedCompilerM.run_bind,
                  CheckedCompilerM.value_bind, CheckedCompilerM.run_lift,
                  CheckedCompilerM.value_lift, CheckedCompilerM.run_pure,
                  CheckedCompilerM.value_pure, hF, hO, ihr, Except.map]
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
                simp [placeToBorrowRegChecked, CheckedCompilerM.run_bind,
                  CheckedCompilerM.value_bind, CheckedCompilerM.run_lift,
                  CheckedCompilerM.value_lift, CheckedCompilerM.run_pure,
                  CheckedCompilerM.value_pure, hF, hO, ihr, h_res,
                  CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM,
                  cleanupInstrs, Except.map]
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
                simp only [placeToBorrowRegChecked, CheckedCompilerM.run_bind,
                  CheckedCompilerM.value_bind, CheckedCompilerM.run_lift,
                  CheckedCompilerM.value_lift, CheckedCompilerM.run_pure,
                  CheckedCompilerM.value_pure, hF, hO, ihr, Except.map]
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
                simp [placeToBorrowRegChecked, CheckedCompilerM.run_bind,
                  CheckedCompilerM.value_bind, CheckedCompilerM.run_lift,
                  CheckedCompilerM.value_lift, CheckedCompilerM.run_pure,
                  CheckedCompilerM.value_pure, hF, hO, ihr, h_res,
                  CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM,
                  cleanupInstrs, Except.map]
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
              have h_cancel : qRes.allocBase + (qRes.addr - qRes.allocBase) = qRes.addr := by
                grind
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
              have h_cancel : bRes.allocBase + (bRes.addr - bRes.allocBase) = bRes.addr := by
                grind
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
                  simp only [CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
                    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
                    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure, h_bval, h_off,
                    dif_pos]
                  simp [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM,
                    cleanupInstrs, h_bclean, emit_nil]
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
                  simp only [CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
                    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
                    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure, h_bval, h_off,
                    dif_pos]
                  simp [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM,
                    cleanupInstrs, h_bclean, emit_nil]
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
                  simp only [CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
                    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
                    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure, h_bval, h_off,
                    dif_neg]
                  simp [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM,
                    cleanupInstrs, borrowRhs, h_bclean, emit_nil]
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
                  simp only [CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
                    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift,
                    CheckedCompilerM.run_pure, CheckedCompilerM.value_pure, h_bval, h_off,
                    dif_neg]
                  simp [CompilerM.run, CompilerM.value, freshRegM, freshReg, emitM,
                    cleanupInstrs, borrowRhs, h_bclean, emit_nil]
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
                    + blockSize (obseq.LayoutTy.PtrL τ') ≤ bRes.allocBase + bRes.allocSize := by
                  grind
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
                    < bRes.allocSize := by
                  grind
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

end obseq3.proof
