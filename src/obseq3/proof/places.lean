import obseq3.proof.copy
import obseq3.proof.keystone
import obseq3.proof.permsim_dealloc

/-!
# The place-lowering simulation

A pointer CHAIN place (a local, a deref of a chain, a deref of a field of a
chain — `proof.PtrChain`) lowered by the compiler runs on the
layout-typed target to a register holding the place's resolved pointer,
with the permissions related to the source's access resolution.

The Stacked Borrows half: a deref through
a projection lowers to `Borrow(Shared); Load; Die`, which
`sb_ref_read_die_cancels` (keystone.lean) shows is the source's one read
of the pointer, at any length.

A layout hypothesis: a pointer-typed place has a
pointer-sized layout (`PtrPlacesWF`). The compiler borrows the pointer
FIELD at its layout size and loads 8 bytes through that borrow; a layout
table that gave a pointer field another size would not be a layout of
the program's types.
-/

namespace obseq3.proof

open obseq3 obseq3.bytes obseq3.proof
open obseq3.mirlite (MemValue Binding Env PlaceRes)
open obseq3.oseair (Val Register)
open obseq3.compile

/-- Every pointer-typed place has a pointer-sized layout. -/
def PtrPlacesWF {Γ : Ctx} (L : mirlite.LayEnv Γ) : Prop :=
  ∀ {τ : LayoutTy} (p : Place Γ (LayoutTy.PtrL τ)), (mirlite.placeLayout L p).size = ptrSize

/-! ## Decoding a pointer on both sides -/

theorem decode_ptr_sim {ρt : TagRenameMap} (hwf : TagRenameWF ρt) {mS mT : bytes.Mem}
    (h_mem : ByteMemSim ρt mS mT) {a n : Nat} {b o e sz : Nat} {t : Tag}
    (h : mirlite.decodeV .ptr (mS.read a n) = .ptrVal b o e sz t) :
    ∃ t', mirlite.decodeV .ptr (mT.read a n) = .ptrVal b o e sz t' ∧ ρt t = some t' := by
  have hv := decodeV_sim hwf .ptr (h_mem.read a n)
  rw [h] at hv
  cases hw : mirlite.decodeV .ptr (mT.read a n) with
  | undef => rw [hw] at hv; exact absurd hv (by simp [ValSim, MemValSim, oseair.ofMem])
  | word _ => rw [hw] at hv; exact absurd hv (by simp [ValSim, MemValSim, oseair.ofMem])
  | ptrVal b' o' e' s' t' =>
      rw [hw] at hv
      simp only [ValSim, MemValSim, oseair.ofMem, idA, Option.some.injEq] at hv
      obtain ⟨rfl, rfl, rfl, rfl, ht, -⟩ := hv
      exact ⟨t', rfl, ht⟩

/-! ## The `Load` of a pointer -/

/-- A `Load` of one pointer leaf through a register pointing at `addr`:
    liveness, bounds, the SB read, the decoded pointer into `rN`. -/
theorem runN_Load_ptr {compProg : oseair.Prog} {s : oseair.State MSB}
    {rN preg : Register} {q : BLayout} {base off ext size : Nat} {tagT : Tag}
    {p2 : AccessPerms} {b o e sz : Nat} {t : Tag}
    (h_code : compProg s.pc = some (oseair.Instr.Assgn rN (oseair.Rhs.Load (.ptr q) preg)))
    (h_reg : s.reg.lookup preg = some [Val.Ptr base off ext size tagT])
    (h_freed : s.mem.isFreed base = false)
    (h_bnd : base + off + ptrSize ≤ base + size)
    (h_read : sb_read s.perms (base + off) ptrSize tagT = .ok p2)
    (h_dec : mirlite.decodeV .ptr (s.mem.read (base + off) ptrSize) = .ptrVal b o e sz t) :
    oseair.runN MSB 1 s compProg =
      .Ok { s with perms := p2, reg := s.reg.insert rN [Val.Ptr b o e sz t], pc := s.pc + 1 } := by
  have h_nb : ¬ (base + off + ptrSize > base + size) := by omega
  have h_rl : mirlite.readL s.mem (base + off) (.ptr q) = [.ptrVal b o e sz t] := by
    simp only [mirlite.readL, BLayout.leaves, List.map_cons, List.map_nil, Nat.add_zero]
    rw [show Scalar.size .ptr = ptrSize from rfl, h_dec]
  simp only [oseair.runN, oseair.step, h_code, oseair.evalRhs, h_reg, h_freed,
    Bool.false_eq_true, if_false, BLayout.size, h_nb, PermissionModel.stackedBorrows, h_read,
    h_rl]
  rfl

/-! ## The compiled shapes -/

/-- The compiler state after `freshRegM`. -/
abbrev bumpReg (cs : CompilerState) : CompilerState := { cs with nextReg := cs.nextReg + 1 }

/-- The deref arm: the pointer place's lowering, a `Load` of one pointer
    leaf into a fresh register, then the pointer place's cleanups. -/
theorem deref_lowering {Γ : Ctx} {L : mirlite.LayEnv Γ} {σ : LayoutTy} {kind : RefKind}
    {q : Place Γ (LayoutTy.PtrL σ)} {cs : CompilerState}
    {qOut : ResultWithEvidence PtrResult (PlaceToRegEvidence L RefKind.Shared q)}
    (h_qval : CheckedCompilerM.value (placeToRegChecked L RefKind.Shared q) cs = .ok qOut) :
    CheckedCompilerM.run (placeToRegChecked L kind (.deref q)) cs
      = emit (emit (bumpReg (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared q) cs))
          [oseair.Instr.Assgn
            (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared q) cs).nextReg)
            (oseair.Rhs.Load (derefLoad L q) qOut.result.reg)])
        (cleanupInstrs qOut.result.cleanup) ∧
    ∃ out, CheckedCompilerM.value (placeToRegChecked L kind (.deref q)) cs = .ok out ∧
      out.result = PtrResult.mk
        (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared q) cs).nextReg) [] := by
  have h_bind : placeToRegChecked L kind (.deref q)
      = (do
          let ptrOut ← placeToRegChecked L RefKind.Shared q
          let ptrRes := ptrOut.result
          let loadedReg ← CheckedCompilerM.lift freshRegM
          let _ ← CheckedCompilerM.lift
            (emitM [oseair.Instr.Assgn loadedReg (oseair.Rhs.Load (derefLoad L q) ptrRes.reg)])
          let _ ← CheckedCompilerM.lift (emitM (cleanupInstrs ptrRes.cleanup))
          pure {
            result := { reg := loadedReg, cleanup := [] },
            evidence := PlaceToRegEvidence.deref q ptrRes loadedReg ptrOut.evidence
          }) := by simp only [placeToRegChecked]
  rw [h_bind]
  simp only [CheckedCompilerM.run_bind, CheckedCompilerM.value_bind, h_qval,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift, CheckedCompilerM.run_pure,
    CheckedCompilerM.value_pure]
  exact ⟨rfl, _, rfl, rfl⟩

/-- The projection arm's equation, for a base that is not a projection. -/
theorem proj_eq {Γ : Ctx} {L : mirlite.LayEnv Γ} {ρ τ : LayoutTy} {kind : RefKind}
    {b : Place Γ ρ} (f : PathTo ρ τ)
    (h_np : ∀ (σ' : LayoutTy) (bb : Place Γ σ') (q : PathTo σ' ρ), b = bb.proj q → False) :
    placeToRegChecked L kind (.proj b f)
    = (do
        let baseOut ← placeToRegChecked L kind b
        let baseRes := baseOut.result
        let offset := pathOffset L b f
        if h_offset : offset = 0 then
          pure {
            result := baseRes,
            evidence := PlaceToRegEvidence.projZero b f baseRes baseOut.evidence h_offset
          }
        else
          let tmpReg ← CheckedCompilerM.lift freshRegM
          let _ ← CheckedCompilerM.lift
            (emitM [oseair.Instr.Assgn tmpReg
              (borrowRhs kind (placeSize L (.proj b f)) baseRes.reg offset)])
          pure {
            result := { reg := tmpReg,
                        cleanup := baseRes.cleanup ++ [(tmpReg, placeSize L (.proj b f))] },
            evidence := PlaceToRegEvidence.projOffset b f baseRes tmpReg baseOut.evidence h_offset
          }) := by
  cases b with
  | «local» loc => simp only [placeToRegChecked]
  | proj bb q => exact absurd rfl (h_np _ bb q)
  | deref pp => simp only [placeToRegChecked]

/-- The projection arm, for a base that is not itself a projection: at
    byte offset zero nothing; otherwise one `Borrow` of the field's bytes
    at its byte offset, with its `Die` left to the caller. -/
theorem proj_lowering {Γ : Ctx} {L : mirlite.LayEnv Γ} {ρ τ : LayoutTy} {kind : RefKind}
    {b : Place Γ ρ} (f : PathTo ρ τ) {cs : CompilerState}
    (h_np : ∀ (σ' : LayoutTy) (bb : Place Γ σ') (q : PathTo σ' ρ), b = bb.proj q → False)
    {bOut : ResultWithEvidence PtrResult (PlaceToRegEvidence L kind b)}
    (h_bval : CheckedCompilerM.value (placeToRegChecked L kind b) cs = .ok bOut) :
    (pathOffset L b f = 0 →
      CheckedCompilerM.run (placeToRegChecked L kind (.proj b f)) cs
        = CheckedCompilerM.run (placeToRegChecked L kind b) cs ∧
      ∃ out, CheckedCompilerM.value (placeToRegChecked L kind (.proj b f)) cs = .ok out ∧
        out.result = bOut.result) ∧
    (pathOffset L b f ≠ 0 →
      CheckedCompilerM.run (placeToRegChecked L kind (.proj b f)) cs
        = emit (bumpReg (CheckedCompilerM.run (placeToRegChecked L kind b) cs))
            [oseair.Instr.Assgn
              (Register.R (CheckedCompilerM.run (placeToRegChecked L kind b) cs).nextReg)
              (borrowRhs kind (placeSize L (.proj b f)) bOut.result.reg (pathOffset L b f))] ∧
      ∃ out, CheckedCompilerM.value (placeToRegChecked L kind (.proj b f)) cs = .ok out ∧
        out.result = PtrResult.mk
          (Register.R (CheckedCompilerM.run (placeToRegChecked L kind b) cs).nextReg)
          (bOut.result.cleanup ++
            [(Register.R (CheckedCompilerM.run (placeToRegChecked L kind b) cs).nextReg,
              placeSize L (.proj b f))])) := by
  rw [proj_eq f h_np]
  refine ⟨fun h0 => ?_, fun h0 => ?_⟩
  · simp only [CheckedCompilerM.run_bind, CheckedCompilerM.value_bind, h_bval, h0, dite_true,
      CheckedCompilerM.run_pure, CheckedCompilerM.value_pure]
    exact ⟨by first | trivial | rfl, _, rfl, rfl⟩
  · simp only [CheckedCompilerM.run_bind, CheckedCompilerM.value_bind, h_bval, h0, dite_false,
      CheckedCompilerM.run_lift, CheckedCompilerM.value_lift, CheckedCompilerM.run_pure,
      CheckedCompilerM.value_pure]
    exact ⟨by first | trivial | rfl, _, rfl, rfl⟩

/-! ## Bookkeeping -/

theorem bumpReg_state_incr' (cs : CompilerState) : StateIncr cs (bumpReg cs) :=
  freshReg_state_incr cs

theorem deref_incr {Γ : Ctx} {L : mirlite.LayEnv Γ} {σ : LayoutTy} {kind : RefKind}
    (q : Place Γ (LayoutTy.PtrL σ)) (cs : CompilerState) :
    StateIncr (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared q) cs)
      (CheckedCompilerM.run (placeToRegChecked L kind (.deref q)) cs) := by
  have h_bind : placeToRegChecked L kind (.deref q)
      = (do
          let ptrOut ← placeToRegChecked L RefKind.Shared q
          let ptrRes := ptrOut.result
          let loadedReg ← CheckedCompilerM.lift freshRegM
          let _ ← CheckedCompilerM.lift
            (emitM [oseair.Instr.Assgn loadedReg (oseair.Rhs.Load (derefLoad L q) ptrRes.reg)])
          let _ ← CheckedCompilerM.lift (emitM (cleanupInstrs ptrRes.cleanup))
          pure {
            result := { reg := loadedReg, cleanup := [] },
            evidence := PlaceToRegEvidence.deref q ptrRes loadedReg ptrOut.evidence
          }) := by simp only [placeToRegChecked]
  rw [h_bind, CheckedCompilerM.run_bind]
  split
  · exact CheckedCompilerM.incr _ _
  · exact StateIncr.refl _

theorem proj_incr {Γ : Ctx} {L : mirlite.LayEnv Γ} {ρ τ : LayoutTy} {kind : RefKind}
    {b : Place Γ ρ} (f : PathTo ρ τ) (cs : CompilerState)
    (h_np : ∀ (σ' : LayoutTy) (bb : Place Γ σ') (q : PathTo σ' ρ), b = bb.proj q → False) :
    StateIncr (CheckedCompilerM.run (placeToRegChecked L kind b) cs)
      (CheckedCompilerM.run (placeToRegChecked L kind (.proj b f)) cs) := by
  rw [proj_eq f h_np, CheckedCompilerM.run_bind]
  split
  · exact CheckedCompilerM.incr _ _
  · exact StateIncr.refl _



theorem CodeIncludedB.mono {compProg : oseair.Prog} {cs cs' : CompilerState}
    (h : CodeIncludedB compProg cs') (hi : StateIncr cs cs') : CodeIncludedB compProg cs :=
  fun q instr hq hc => h q instr (Nat.lt_of_lt_of_le hq hi.nextLabel_le)
    (by rw [hi.code_eq q hq]; exact hc)


/-- Bound locals' registers are below the watermark, so a register frame
    below it keeps the binding relation. -/
theorem LocalBindingSimB.of_frame {Γ : Ctx} {L : mirlite.LayEnv Γ} {ρt : TagRenameMap}
    {env : Env Γ} {s s' : oseair.State MSB} {cs : CompilerState}
    (h : LocalBindingSimB L ρt env s cs) (h_prb : PlaceRegMapBoundB cs)
    (h_frame : ∀ r, RegisterBelow cs.nextReg r → s'.reg.lookup r = s.reg.lookup r) :
    LocalBindingSimB L ρt env s' cs := by
  intro τ loc b h_env
  obtain ⟨r, t, hpi, ⟨e, hr⟩, hrt, hnw⟩ := h loc b h_env
  exact ⟨r, t, hpi, ⟨e, by rw [h_frame r (h_prb _ _ _ hpi)]; exact hr⟩, hrt, hnw⟩

/-- A `Borrow` of `n` bytes at `off` past the register's pointer, with the
    liveness and bounds checks as the machine makes them: only for `n ≠ 0`
    (a zero-byte retag needs no live, in-bounds memory). -/
theorem runN_Borrow' {compProg : oseair.Prog} {s : oseair.State MSB}
    {rN preg : Register} {kind : RefKind} {prot : Bool} {mask : List Bool} {n off : Nat}
    {base boff ext size : Nat} {tagT newTag : Tag} {p' : AccessPerms}
    (h_code : compProg s.pc = some (oseair.Instr.Assgn rN
      (oseair.Rhs.Borrow kind prot mask (some n) preg off)))
    (h_reg : s.reg.lookup preg = some [Val.Ptr base boff ext size tagT])
    (h_freed : n ≠ 0 → s.mem.isFreed base = false)
    (h_bnd : n ≠ 0 → base + boff + off + n ≤ base + size)
    (h_ref : sb_ref s.perms (base + boff + off) n tagT kind prot mask = .ok (p', newTag)) :
    oseair.runN MSB 1 s compProg =
      .Ok { s with perms := p', reg := s.reg.insert rN [Val.Ptr base (boff + off) n size newTag],
                   pc := s.pc + 1 } := by
  by_cases hn : n = 0
  · subst hn
    simp only [oseair.runN, oseair.step, h_code, oseair.evalRhs, h_reg, bne_self_eq_false,
      Bool.false_and, Bool.false_eq_true, if_false, PermissionModel.stackedBorrows, h_ref]
  · have h_nb : ¬ (base + boff + off + n > base + size) := by have := h_bnd hn; omega
    have hn' : (n != 0) = true := by simpa using hn
    simp only [oseair.runN, oseair.step, h_code, oseair.evalRhs, h_reg, h_freed hn, hn',
      Bool.true_and, Bool.false_eq_true, if_false, h_nb, decide_false,
      PermissionModel.stackedBorrows, h_ref]

/-- A `Borrow` of `n` bytes at `off` past the register's pointer. -/
theorem runN_Borrow {compProg : oseair.Prog} {s : oseair.State MSB}
    {rN preg : Register} {kind : RefKind} {prot : Bool} {mask : List Bool} {n off : Nat}
    {base boff ext size : Nat} {tagT newTag : Tag} {p' : AccessPerms}
    (h_code : compProg s.pc = some (oseair.Instr.Assgn rN
      (oseair.Rhs.Borrow kind prot mask (some n) preg off)))
    (h_reg : s.reg.lookup preg = some [Val.Ptr base boff ext size tagT])
    (h_freed : s.mem.isFreed base = false)
    (h_bnd : base + boff + off + n ≤ base + size)
    (h_ref : sb_ref s.perms (base + boff + off) n tagT kind prot mask = .ok (p', newTag)) :
    oseair.runN MSB 1 s compProg =
      .Ok { s with perms := p', reg := s.reg.insert rN [Val.Ptr base (boff + off) n size newTag],
                   pc := s.pc + 1 } :=
  runN_Borrow' h_code h_reg (fun _ => h_freed) (fun _ => h_bnd) h_ref

theorem runN_Die {compProg : oseair.Prog} {s : oseair.State MSB} {r : Register} {len : Nat}
    {base off ext size : Nat} {tagT : Tag} {p' : AccessPerms}
    (h_code : compProg s.pc = some (oseair.Instr.Die r len))
    (h_reg : s.reg.lookup r = some [Val.Ptr base off ext size tagT])
    (h_die : sb_die s.perms (base + off) len tagT = .ok p') :
    oseair.runN MSB 1 s compProg = .Ok { s with perms := p', pc := s.pc + 1 } := by
  simp only [oseair.runN, oseair.step, h_code, h_reg, PermissionModel.stackedBorrows, h_die]

/-- One deref level's `Load`, against the source's read of the same
    pointer: the target read transports, the decoded pointer is the
    source's with its tag renamed. -/
theorem load_level {ρt : TagRenameMap} (hwf : TagRenameWF ρt) {compProg : oseair.Prog}
    {s : oseair.State MSB} {rN preg : Register} {q : BLayout} {base boff ext size : Nat}
    {tT tS : Tag} {mS : bytes.Mem} {pS pS' : AccessPerms} {b o e sz : Nat} {t : Tag}
    (h_code : compProg s.pc = some (oseair.Instr.Assgn rN (oseair.Rhs.Load (.ptr q) preg)))
    (h_reg : s.reg.lookup preg = some [Val.Ptr base boff ext size tT])
    (h_rt : ρt tS = some tT) (h_psim : PermSim ρt pS s.perms) (h_mem : ByteMemSim ρt mS s.mem)
    (h_lock : ByteAllocLockstep mS s.mem) (h_freeS : ¬ mS.isFreed base = true)
    (h_bnd : base + boff + ptrSize ≤ base + size)
    (h_read : sb_read pS (base + boff) ptrSize tS = .ok pS')
    (h_dec : mirlite.readOne mS (base + boff) .ptr = .ptrVal b o e sz t) :
    ∃ p2 t', ρt t = some t' ∧ PermSim ρt pS' p2 ∧ p2.NextTag = s.perms.NextTag ∧
      oseair.runN MSB 1 s compProg =
        .Ok { s with perms := p2, reg := s.reg.insert rN [Val.Ptr b o e sz t'],
                     pc := s.pc + 1 } := by
  obtain ⟨p2, h_read', h_psim'⟩ := sb_read_respects_PermSim h_psim hwf h_rt h_read
  obtain ⟨t', h_dec', h_t⟩ := decode_ptr_sim hwf h_mem h_dec
  have h_freeT : s.mem.isFreed base = false := by
    simp only [bytes.Mem.isFreed, ← h_lock.2.2] at h_freeS ⊢
    simpa using h_freeS
  exact ⟨p2, t', h_t, h_psim', sb_read_NextTag h_read',
    runN_Load_ptr h_code h_reg h_freeT h_bnd h_read' h_dec'⟩

/-! ## The simulation -/

/-- What lowering a chain place delivers. -/
structure LoweredB {Γ : Ctx} (L : mirlite.LayEnv Γ) (ρt : TagRenameMap)
    (compProg : oseair.Prog) (kind : RefKind) {τ : LayoutTy} (p : Place Γ τ)
    (cs : CompilerState) (sM : mirlite.State MSB Γ) (sA : oseair.State MSB)
    (resolved : PlaceRes) (permsD : MSB.State)
    (placeOut : ResultWithEvidence PtrResult (PlaceToRegEvidence L kind p))
    (n : Nat) (s' : oseair.State MSB) (tres : Tag) : Prop where
  val : CheckedCompilerM.value (placeToRegChecked L kind p) cs = .ok placeOut
  clean : placeOut.result.cleanup = []
  run : oseair.runN MSB n sA compProg = .Ok s'
  pc : s'.pc = (CheckedCompilerM.run (placeToRegChecked L kind p) cs).nextLabel
  mem : s'.mem = sA.mem
  psim : PermSim ρt permsD s'.perms
  srcNT : permsD.NextTag = sM.perms.NextTag
  tgtNT : sA.perms.NextTag ≤ s'.perms.NextTag
  entry : ∃ ext, s'.reg.lookup placeOut.result.reg = some
    [Val.Ptr resolved.allocBase (resolved.addr - resolved.allocBase) ext resolved.allocSize tres]
  rt : ρt resolved.tag = some tres
  le : resolved.allocBase ≤ resolved.addr
  below : RegisterBelow (CheckedCompilerM.run (placeToRegChecked L kind p) cs).nextReg
    placeOut.result.reg
  prm : (CheckedCompilerM.run (placeToRegChecked L kind p) cs).placeRegMap = cs.placeRegMap
  regmono : cs.nextReg ≤ (CheckedCompilerM.run (placeToRegChecked L kind p) cs).nextReg
  labmono : cs.nextLabel ≤ (CheckedCompilerM.run (placeToRegChecked L kind p) cs).nextLabel
  frame : ∀ r, RegisterBelow cs.nextReg r → s'.reg.lookup r = sA.reg.lookup r

/-- One deref level: given the pointer place's lowering (`hQ`) and the
    source's checked read of the pointer, the deref's `Load` lands the
    resolved pointer in a fresh register. -/
theorem deref_level {Γ : Ctx} {L : mirlite.LayEnv Γ} {ρt : TagRenameMap}
    {sM : mirlite.State MSB Γ} {compProg : oseair.Prog} (hwf : TagRenameWF ρt)
    {σ : LayoutTy} {q : Place Γ (LayoutTy.PtrL σ)} {kind : RefKind} {cs : CompilerState}
    {sA : oseair.State MSB} {qRes : PlaceRes} {permsQ permsQ' : MSB.State}
    {qOut : ResultWithEvidence PtrResult (PlaceToRegEvidence L RefKind.Shared q)}
    {n1 : Nat} {s_mid : oseair.State MSB} {qtag : Tag}
    (hQ : LoweredB L ρt compProg RefKind.Shared q cs sM sA qRes permsQ qOut n1 s_mid qtag)
    (h_mem : ByteMemSim ρt sM.mem sA.mem) (h_lock : ByteAllocLockstep sM.mem sA.mem)
    (h_inc : CodeIncludedB compProg (CheckedCompilerM.run (placeToRegChecked L kind (.deref q)) cs))
    (h_free : ¬ sM.mem.isFreed qRes.allocBase = true)
    (h_qb : ¬ (qRes.addr < qRes.allocBase ∨ qRes.addr + ptrSize > qRes.allocBase + qRes.allocSize))
    (h_qread : MSB.read permsQ qRes.addr ptrSize qRes.tag = .ok permsQ')
    {vb vo ve vsz : Nat} {vt : Tag}
    (h_dec : mirlite.readOne sM.mem qRes.addr .ptr = .ptrVal vb vo ve vsz vt) :
    ∃ out n s' t', LoweredB L ρt compProg kind (.deref q) cs sM sA
      { addr := vb + vo, tag := vt, allocBase := vb, allocSize := vsz } permsQ' out n s' t' := by
  obtain ⟨h_runD, out, h_valD, h_outres⟩ := deref_lowering (kind := kind) hQ.val
  rw [hQ.clean] at h_runD
  simp only [cleanupInstrs, List.reverse_nil, List.map_nil, emit_nil] at h_runD
  obtain ⟨ext, h_qentry⟩ := hQ.entry
  have hA : qRes.allocBase + (qRes.addr - qRes.allocBase) = qRes.addr :=
    Nat.add_sub_cancel' hQ.le
  have h_qb' : qRes.addr + ptrSize ≤ qRes.allocBase + qRes.allocSize :=
    Nat.le_of_not_gt fun h => h_qb (Or.inr h)
  have h_code : compProg s_mid.pc = some (oseair.Instr.Assgn
      (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared q) cs).nextReg)
      (oseair.Rhs.Load (derefLoad L q) qOut.result.reg)) := by
    rw [hQ.pc]
    apply h_inc
    · rw [h_runD]; simp [emit]
    · rw [h_runD]
      simpa using emit_code_at_new (bumpReg _) [oseair.Instr.Assgn
        (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared q) cs).nextReg)
        (oseair.Rhs.Load (derefLoad L q) qOut.result.reg)] (k := 0) (by simp)
  obtain ⟨p2, t', h_t, h_psim2, h_nt2, h_run1⟩ :=
    load_level hwf h_code h_qentry hQ.rt hQ.psim (hQ.mem ▸ h_mem) (hQ.mem ▸ h_lock) h_free
      (by rw [hA]; exact h_qb') (by rw [hA]; exact h_qread) (by rw [hA]; exact h_dec)
  refine ⟨out, n1 + 1, _, t', {
    val := h_valD
    clean := by rw [h_outres]
    run := runN_trans hQ.run h_run1
    pc := by rw [h_runD]; simp [emit, hQ.pc]
    mem := hQ.mem
    psim := h_psim2
    srcNT := by rw [sb_read_NextTag h_qread]; exact hQ.srcNT
    tgtNT := by
      show sA.perms.NextTag ≤ p2.NextTag
      rw [h_nt2]; exact hQ.tgtNT
    entry := ⟨ve, by
      rw [h_outres]
      simp only [Nat.add_sub_cancel_left]
      exact RegMap.lookup_insert_self _ _ _⟩
    rt := h_t
    le := Nat.le_add_right _ _
    below := by
      rw [h_runD, h_outres]
      show _ < _ + 1
      exact Nat.lt_succ_self _
    prm := by rw [h_runD]; exact hQ.prm
    regmono := by rw [h_runD]; exact Nat.le_trans hQ.regmono (Nat.le_succ _)
    labmono := by
      have := hQ.labmono
      rw [h_runD]; simp only [emit, List.length_cons, List.length_nil]; omega
    frame := fun r hr => by
      have hne : r ≠ Register.R
          (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared q) cs).nextReg :=
        RegisterBelow.ne_fresh (RegisterBelow.mono hQ.regmono hr)
      show (s_mid.reg.insert _ _).lookup r = _
      rw [RegMap.lookup_insert_ne _ _ hne]
      exact hQ.frame r hr }⟩


/-- The three labels a deref-through-a-field emits. -/
theorem code_three (rb : CompilerState) (i1 i2 i3 : oseair.Instr) :
    (emit (emit (bumpReg (emit (bumpReg rb) [i1])) [i2]) [i3]).code rb.nextLabel = some i1 ∧
    (emit (emit (bumpReg (emit (bumpReg rb) [i1])) [i2]) [i3]).code (rb.nextLabel + 1) = some i2 ∧
    (emit (emit (bumpReg (emit (bumpReg rb) [i1])) [i2]) [i3]).code (rb.nextLabel + 2) = some i3 ∧
    (emit (emit (bumpReg (emit (bumpReg rb) [i1])) [i2]) [i3]).nextLabel = rb.nextLabel + 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [emit]
  all_goals (repeat (first | rw [if_neg (by omega)] | rw [if_pos (by omega)])) <;> rfl

theorem ptrChain_lowering_simB {Γ : Ctx} {L : mirlite.LayEnv Γ} {ρt : TagRenameMap}
    {sM : mirlite.State MSB Γ} {compProg : oseair.Prog}
    (hWF : PtrPlacesWF L) (hwf : TagRenameWF ρt)
    {τ : LayoutTy} {p : Place Γ τ} (h_chain : PtrChain p) :
    ∀ (kind : RefKind) (cs : CompilerState) (sA : oseair.State MSB)
      (resolved : PlaceRes) (permsD : MSB.State),
      mirlite.resolvePlaceAcc MSB L sM p = .ok (resolved, permsD) →
      TagRenameBounded ρt sM.perms.NextTag sA.perms.NextTag →
      LocalBindingSimB L ρt sM.env sA cs →
      PlaceRegMapBoundB cs →
      ByteMemSim ρt sM.mem sA.mem →
      ByteAllocLockstep sM.mem sA.mem →
      PermSim ρt sM.perms sA.perms →
      sA.pc = cs.nextLabel →
      CodeIncludedB compProg (CheckedCompilerM.run (placeToRegChecked L kind p) cs) →
      ∃ placeOut n s' tres, LoweredB L ρt compProg kind p cs sM sA resolved permsD
        placeOut n s' tres := by
  induction h_chain with
  | base loc =>
      intro kind cs sA resolved permsD h_res h_tbd h_lbs h_prb h_mem h_lock h_psim h_pc h_inc
      cases h_env : sM.env.lookup loc with
      | none => simp [mirlite.resolvePlaceAcc, h_env] at h_res
      | some bnd =>
      simp only [mirlite.resolvePlaceAcc, h_env, Except.ok.injEq, Prod.mk.injEq] at h_res
      obtain ⟨rfl, rfl⟩ := h_res
      obtain ⟨reg, tag, h_pi, ⟨ext, h_reg⟩, h_rt, -⟩ := h_lbs loc bnd h_env
      obtain ⟨h_prun, placeOut, h_pval, h_pres⟩ :=
        placeToRegChecked_local_existing (L := L) (kind := kind) h_pi
      refine ⟨placeOut, 0, sA, tag, {
        val := h_pval
        clean := by rw [h_pres]
        run := by simp [oseair.runN]
        pc := by rw [h_prun]; exact h_pc
        mem := rfl
        psim := h_psim
        srcNT := rfl
        tgtNT := Nat.le_refl _
        entry := ⟨ext, by rw [h_pres, Nat.sub_self]; exact h_reg⟩
        rt := h_rt
        le := Nat.le_refl _
        below := by rw [h_prun, h_pres]; exact h_prb _ _ _ h_pi
        prm := by rw [h_prun]
        regmono := by rw [h_prun]; exact Nat.le_refl _
        labmono := by rw [h_prun]; exact Nat.le_refl _
        frame := fun _ _ => rfl }⟩
  | deref h_chainQ ih =>
      rename_i σ q
      intro kind cs sA resolved permsD h_res h_tbd h_lbs h_prb h_mem h_lock h_psim h_pc h_inc
      simp only [mirlite.resolvePlaceAcc] at h_res
      cases h_qres : mirlite.resolvePlaceAcc MSB L sM q with
      | error e => simp [h_qres] at h_res
      | ok pr =>
      obtain ⟨qRes, permsQ⟩ := pr
      simp only [h_qres] at h_res
      split at h_res
      · cases h_res
      rename_i h_free
      split at h_res
      · cases h_res
      rename_i h_qb
      split at h_res
      · cases h_res
      rename_i permsQ' h_qread
      split at h_res
      · rename_i vb vo ve vsz vt h_dec
        simp only [Except.ok.injEq, Prod.mk.injEq] at h_res
        obtain ⟨rfl, rfl⟩ := h_res
        -- the pointer place's own lowering
        obtain ⟨qOut, n1, s_mid, qtag, hQ⟩ :=
          ih RefKind.Shared cs sA qRes permsQ h_qres h_tbd h_lbs h_prb h_mem h_lock h_psim h_pc
            (h_inc.mono (deref_incr q cs))
        exact deref_level hwf hQ h_mem h_lock h_inc h_free h_qb h_qread h_dec
      · cases h_res
  | derefProj f h_chainB ih =>
      rename_i σb τ' b
      intro kind cs sA resolved permsD h_res h_tbd h_lbs h_prb h_mem h_lock h_psim h_pc h_inc
      have h_np := PtrChain.not_proj h_chainB
      simp only [mirlite.resolvePlaceAcc] at h_res
      cases h_bres : mirlite.resolvePlaceAcc MSB L sM b with
      | error e => simp [h_bres] at h_res
      | ok pr =>
      obtain ⟨bRes, permsB⟩ := pr
      simp only [h_bres] at h_res
      split at h_res
      · cases h_res
      rename_i h_free
      split at h_res
      · cases h_res
      rename_i h_qb
      split at h_res
      · cases h_res
      rename_i permsQ' h_qread
      split at h_res
      case h_2 => cases h_res
      rename_i vb vo ve vsz vt h_dec
      simp only [Except.ok.injEq, Prod.mk.injEq] at h_res
      obtain ⟨rfl, rfl⟩ := h_res
      obtain ⟨bOut, n1, s_mid, btag, hB⟩ :=
        ih RefKind.Shared cs sA bRes permsB h_bres h_tbd h_lbs h_prb h_mem h_lock h_psim h_pc
          (h_inc.mono ((proj_incr (kind := RefKind.Shared) f cs h_np).trans
            (deref_incr (.proj b f) cs)))
      obtain ⟨hz, hnz⟩ := proj_lowering (kind := RefKind.Shared) f h_np hB.val
      by_cases h0 : pathOffset L b f = 0
      · -- offset ZERO: the field IS the base; one deref level
        obtain ⟨h_runP, outP, h_valP, h_resP⟩ := hz h0
        have h0' : mirlite.fieldOffset (mirlite.placeLayout L b) f.indices = 0 := h0
        have hP : LoweredB L ρt compProg RefKind.Shared (.proj b f) cs sM sA
            { bRes with addr := bRes.addr + mirlite.fieldOffset (mirlite.placeLayout L b) f.indices }
            permsB outP n1 s_mid btag := {
          val := h_valP
          clean := by rw [h_resP]; exact hB.clean
          run := hB.run
          pc := by rw [h_runP]; exact hB.pc
          mem := hB.mem
          psim := hB.psim
          srcNT := hB.srcNT
          tgtNT := hB.tgtNT
          entry := by
            obtain ⟨e, he⟩ := hB.entry
            exact ⟨e, by rw [h_resP]; simpa [h0'] using he⟩
          rt := hB.rt
          le := by simpa [h0'] using hB.le
          below := by rw [h_runP, h_resP]; exact hB.below
          prm := by rw [h_runP]; exact hB.prm
          regmono := by rw [h_runP]; exact hB.regmono
          labmono := by rw [h_runP]; exact hB.labmono
          frame := hB.frame }
        exact deref_level hwf hP h_mem h_lock h_inc h_free h_qb h_qread h_dec
      · -- offset NONZERO: `Borrow(Shared); Load; Die`, which is the source's
        -- one read of the pointer field (keystone's `sb_ref_read_die_cancels`)
        obtain ⟨h_runP, outP, h_valP, h_resP⟩ := hnz h0
        obtain ⟨h_runD, out, h_valD, h_outres⟩ := deref_lowering (kind := kind) h_valP
        rw [h_resP, hB.clean, h_runP] at h_runD
        simp only [List.nil_append, cleanupInstrs, List.reverse_cons, List.reverse_nil,
          List.map_cons, List.map_nil] at h_runD
        rw [h_runP] at h_outres
        simp only [emit] at h_outres
        obtain ⟨ext, h_bentry⟩ := hB.entry
        have hn : placeSize L (.proj b f) = ptrSize := hWF (.proj b f)
        have hA : bRes.allocBase + (bRes.addr - bRes.allocBase) = bRes.addr :=
          Nat.add_sub_cancel' hB.le
        have h_qb' : bRes.addr + pathOffset L b f + ptrSize ≤ bRes.allocBase + bRes.allocSize :=
          Nat.le_of_not_gt fun h => h_qb (Or.inr h)
        -- the source read, transported; the target's Shared retag succeeds
        obtain ⟨p2, h_read', h_psim2⟩ :=
          sb_read_respects_PermSim hB.psim hwf hB.rt h_qread
        obtain ⟨q1, h_ref⟩ := sb_ref_Shared_ok_of_sb_read_ok h_read'
        have h_tbd_mid : TagRenameBounded ρt permsB.NextTag s_mid.perms.NextTag := by
          rw [hB.srcNT]; exact TagRenameBounded.mono h_tbd (Nat.le_refl _) hB.tgtNT
        have h_unprot := freshTag_not_protected hB.psim h_tbd_mid
        have h0w : wildcardTag < s_mid.perms.NextTag := (h_tbd_mid _ _ hwf.2).2
        have h_ntw : (s_mid.perms.NextTag == wildcardTag) = false := by
          simp only [beq_eq_false_iff_ne]; exact (Nat.ne_of_lt h0w).symm
        obtain ⟨q2, q3, sAcc, h_rd1, h_die1, h_rd2, h_sm, h_ex, h_pf, h_ntle, h_wk⟩ :=
          sb_ref_read_die_cancels h_ntw h_unprot h_ref
        have h_acc : sAcc = p2 := by
          have := h_rd2.symm.trans h_read'
          exact Except.ok.inj this
        subst h_acc
        -- the source pointer, decoded on the target
        have h_decS : mirlite.decodeV .ptr
            (sM.mem.read (bRes.addr + pathOffset L b f) ptrSize) = .ptrVal vb vo ve vsz vt := h_dec
        obtain ⟨t', h_decT, h_t⟩ := decode_ptr_sim hwf h_mem h_decS
        have h_freeT : s_mid.mem.isFreed bRes.allocBase = false := by
          rw [hB.mem]
          simp only [bytes.Mem.isFreed, ← h_lock.2.2] at h_free ⊢
          simpa using h_free
        -- the code
        have hct := fun i1 i2 i3 => code_three
          (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared b) cs) i1 i2 i3
        have hc1 : (CheckedCompilerM.run (placeToRegChecked L kind (.deref (.proj b f))) cs).code
            ((CheckedCompilerM.run (placeToRegChecked L RefKind.Shared b) cs).nextLabel + 0)
            = some (oseair.Instr.Assgn
              (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared b) cs).nextReg)
              (borrowRhs RefKind.Shared (placeSize L (.proj b f)) bOut.result.reg
                (pathOffset L b f))) := by
          rw [h_runD]; exact (hct _ _ _).1
        have hc2 : (CheckedCompilerM.run (placeToRegChecked L kind (.deref (.proj b f))) cs).code
            ((CheckedCompilerM.run (placeToRegChecked L RefKind.Shared b) cs).nextLabel + 1)
            = some (oseair.Instr.Assgn
              (Register.R ((CheckedCompilerM.run (placeToRegChecked L RefKind.Shared b) cs).nextReg + 1))
              (oseair.Rhs.Load (derefLoad L (.proj b f))
                (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared b) cs).nextReg))) := by
          rw [h_runD]; exact (hct _ _ _).2.1
        have hc3 : (CheckedCompilerM.run (placeToRegChecked L kind (.deref (.proj b f))) cs).code
            ((CheckedCompilerM.run (placeToRegChecked L RefKind.Shared b) cs).nextLabel + 2)
            = some (oseair.Instr.Die
              (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared b) cs).nextReg)
              (placeSize L (.proj b f))) := by
          rw [h_runD]; exact (hct _ _ _).2.2.1
        have hnl : (CheckedCompilerM.run (placeToRegChecked L kind (.deref (.proj b f))) cs).nextLabel
            = (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared b) cs).nextLabel + 3 := by
          rw [h_runD]; exact (hct _ _ _).2.2.2
        have h_at : ∀ k instr, k < 3 →
            (CheckedCompilerM.run (placeToRegChecked L kind (.deref (.proj b f))) cs).code
              ((CheckedCompilerM.run (placeToRegChecked L RefKind.Shared b) cs).nextLabel + k)
              = some instr →
            compProg (s_mid.pc + k) = some instr := by
          intro k instr hk hc
          rw [hB.pc]
          exact h_inc _ instr (by rw [hnl]; omega) hc
        -- §1 the Borrow
        have h1 := runN_Borrow (s := s_mid) (h_at 0 _ (by omega) hc1) h_bentry h_freeT
          (by rw [hA, hn]; exact h_qb') (by rw [hA, hn]; exact h_ref)
        -- §2 the Load through the fresh tag
        let S1 : oseair.State MSB :=
          { s_mid with
              perms := q1,
              reg := s_mid.reg.insert
                (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared b) cs).nextReg)
                [Val.Ptr bRes.allocBase (bRes.addr - bRes.allocBase + pathOffset L b f)
                  (placeSize L (.proj b f)) bRes.allocSize s_mid.perms.NextTag],
              pc := s_mid.pc + 1 }
        have h2 := runN_Load_ptr (s := S1) (q := mirlite.placeLayout L (.deref (.proj b f)))
          (h_at 1 _ (by omega) hc2) (RegMap.lookup_insert_self _ _ _)
          (by simpa [S1] using h_freeT)
          (by rw [← Nat.add_assoc, hA]; exact h_qb')
          (by rw [← Nat.add_assoc, hA]; exact h_rd1)
          (by rw [← Nat.add_assoc, hA]; simpa [S1, hB.mem] using h_decT)
        -- §3 the Die
        have hne : Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared b) cs).nextReg
            ≠ Register.R ((CheckedCompilerM.run (placeToRegChecked L RefKind.Shared b) cs).nextReg + 1) := by
          simp
        let S2 : oseair.State MSB :=
          { S1 with
              perms := q2,
              reg := S1.reg.insert
                (Register.R ((CheckedCompilerM.run (placeToRegChecked L RefKind.Shared b) cs).nextReg + 1))
                [Val.Ptr vb vo ve vsz t'],
              pc := S1.pc + 1 }
        have h3 := runN_Die (s := S2) (h_at 2 _ (by omega) hc3)
          (by rw [RegMap.lookup_insert_ne _ _ hne]; exact RegMap.lookup_insert_self _ _ _)
          (by rw [← Nat.add_assoc, hA, hn]; exact h_die1)
        refine ⟨out, n1 + 1 + 1 + 1, _, t', {
          val := h_valD
          clean := by rw [h_outres]
          run := runN_trans (runN_trans (runN_trans hB.run h1) h2) h3
          pc := by
            show s_mid.pc + 1 + 1 + 1 = _
            rw [hnl, hB.pc]
          mem := hB.mem
          psim := ⟨by rw [h_sm]; exact h_psim2.1, by rw [h_pf]; exact h_psim2.2.1,
            by rw [h_ex]; exact h_psim2.2.2.1, Nat.le_trans h_psim2.2.2.2.1 h_ntle,
            by rw [h_wk]; exact h_psim2.2.2.2.2⟩
          srcNT := by rw [sb_read_NextTag h_qread]; exact hB.srcNT
          tgtNT := by
            show sA.perms.NextTag ≤ q3.NextTag
            exact Nat.le_trans hB.tgtNT (by rw [← sb_read_NextTag h_read']; exact h_ntle)
          entry := ⟨ve, by
            rw [h_outres]
            simp only [Nat.add_sub_cancel_left]
            exact RegMap.lookup_insert_self _ _ _⟩
          rt := h_t
          le := Nat.le_add_right _ _
          below := by
            rw [h_outres, h_runD]
            show _ < _ + 1 + 1
            omega
          prm := by rw [h_runD]; exact hB.prm
          regmono := by
            have := hB.regmono
            rw [h_runD]; show _ ≤ _ + 1 + 1; omega
          labmono := by
            have := hB.labmono
            rw [hnl]; omega
          frame := fun r hr => by
            have hr' := RegisterBelow.mono hB.regmono hr
            have hne1 := RegisterBelow.ne_fresh hr'
            have hne2 : r ≠ Register.R
                ((CheckedCompilerM.run (placeToRegChecked L RefKind.Shared b) cs).nextReg + 1) :=
              RegisterBelow.ne_fresh (RegisterBelow.mono (Nat.le_succ _) hr')
            show ((s_mid.reg.insert _ _).insert _ _).lookup r = _
            rw [RegMap.lookup_insert_ne _ _ hne2, RegMap.lookup_insert_ne _ _ hne1]
            exact hB.frame r hr }⟩

end obseq3.proof
