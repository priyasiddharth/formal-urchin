import obseq3.proof.route_seg
import obseq3.proof.places
import obseq3.proof.assoc

/-!
# Route brackets in emitted code: the compiler

Each compile function's emitted segment satisfies `Seg` (`route_seg.lean`);
a place lowering may end in an OPEN bracket (its route borrow), which the
caller closes with one access and the `Die` (`Seg.close`).
-/

namespace obseq3.proof

open obseq3 obseq3.compile obseq3.oseair
open obseq3.mirlite (LayEnv placeLayout)

/-- The locals' registers. -/
def LiveOf (cs : CompilerState) (x : Register) : Prop :=
  ∃ idx τ, (idx, (x, τ)) ∈ cs.placeRegMap

def NoIns : Register → Prop := fun _ => False

theorem lookup_mem {α β : Type} [BEq α] [LawfulBEq α] {a : α} {b : β} :
    ∀ {l : List (α × β)}, l.lookup a = some b → (a, b) ∈ l
  | [], h => by simp at h
  | (k, v) :: rest, h => by
      simp only [List.lookup] at h
      split at h
      · rename_i hk
        have : a = k := by simpa using hk
        subst this; cases h; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (lookup_mem h)

theorem Emits.bump_emit (cs : CompilerState) (l : List Instr) :
    Emits cs (compile.emit (bumpReg cs) l) l :=
  ⟨rfl, fun k hk => by
    simp only [compile.emit, bumpReg]
    rw [if_pos ⟨by omega, by omega⟩]
    simp [hk]⟩

theorem StateIncr.bump (cs : CompilerState) : StateIncr cs (bumpReg cs) :=
  bumpReg_state_incr' cs

theorem StateIncr.bump_emit (cs : CompilerState) (l : List Instr) :
    StateIncr cs (compile.emit (bumpReg cs) l) :=
  (StateIncr.bump cs).trans (emit_state_incr _ l)

/-- What a place lowering hands its caller: the segment, and the pointer
    register — closed (a local's, or one it made and did not die), or the
    route borrow it just opened. -/
def PlaceOut (live : Register → Prop) (lo hi : Nat) (kind : RefKind) (seg : List Instr)
    (res : PtrResult) : Prop :=
  Seg live NoIns lo hi seg ∧
  ((res.cleanup = [] ∧ RegOK live NoIns lo hi seg res.reg) ∨
   (∃ n pre base off, res.cleanup = [(res.reg, n)] ∧
      seg = pre ++ [.Assgn res.reg (.Borrow kind false [] (some n) base off)] ∧
      (∀ i ∈ pre, res.reg ∉ i.regs) ∧ lo ≤ regIdx res.reg ∧ regIdx res.reg < hi))

theorem RegOK.mono {live ins : Register → Prop} {lo hi hi' : Nat} {seg : List Instr} {x : Register}
    (h : RegOK live ins lo hi seg x) (hle : hi ≤ hi') : RegOK live ins lo hi' seg x := by
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨h.1, by omega, h.2.2⟩)

theorem RegOK.snoc {live ins : Register → Prop} {lo hi : Nat} {seg : List Instr} {x : Register}
    {i : Instr} (h : RegOK live ins lo hi seg x) (hi' : ∀ n, i ≠ .Die x n) :
    RegOK live ins lo hi (seg ++ [i]) x := by
  rcases h with h | h | ⟨h1, h2, h3⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · refine Or.inr (Or.inr ⟨h1, h2, fun ⟨n, hn⟩ => ?_⟩)
    rcases List.mem_append.mp hn with hn | hn
    · exact h3 ⟨n, hn⟩
    · simp at hn; exact hi' n hn.symm

/-- The not-a-projection condition `proj_eq` takes. -/
def NotProj {Γ : Ctx} {τ : LayoutTy} (p : Place Γ τ) : Prop :=
  ∀ (σ' : LayoutTy) (bb : Place Γ σ') (q : PathTo σ' τ), p = bb.proj q → False

/-- The facts of a place lowering. -/
def PlaceSpec {Γ : Ctx} (L : LayEnv Γ) (kind : RefKind) {τ : LayoutTy} (p : Place Γ τ)
    (cs : CompilerState) (out : PtrResult) : Prop :=
  ∃ seg, Emits cs (CheckedCompilerM.run (placeToRegChecked L kind p) cs) seg ∧
    (CheckedCompilerM.run (placeToRegChecked L kind p) cs).placeRegMap = cs.placeRegMap ∧
    cs.nextReg ≤ (CheckedCompilerM.run (placeToRegChecked L kind p) cs).nextReg ∧
    PlaceOut (LiveOf cs) cs.nextReg (CheckedCompilerM.run (placeToRegChecked L kind p) cs).nextReg
      kind seg out ∧
    (NotProj p → out.cleanup = [])

theorem placeToReg_spec_local {Γ : Ctx} {L : LayEnv Γ} (kind : RefKind) {τ : LayoutTy}
    (loc : Local Γ τ) (cs : CompilerState)
    {out : ResultWithEvidence PtrResult (PlaceToRegEvidence L kind (.local loc))}
    (hv : CheckedCompilerM.value (placeToRegChecked L kind (.local loc)) cs = .ok out) :
    PlaceSpec L kind (.local loc) cs out.result := by
  cases hl : getPlaceInfo cs loc.idx.1 with
  | none =>
      exfalso
      simp only [CheckedCompilerM.value, CompilerM.value, placeToRegChecked] at hv
      split at hv
      · rename_i h'; rw [hl] at h'; cases h'
      · cases hv
  | some info =>
      obtain ⟨reg, layout⟩ := info
      obtain ⟨hrun, out', hv', hres⟩ := placeToRegChecked_local_existing (kind := kind) (L := L) hl
      rw [hv] at hv'
      obtain rfl := Except.ok.inj hv'
      unfold PlaceSpec
      rw [hrun]
      refine ⟨[], Emits.nil cs, rfl, Nat.le_refl _, ⟨Seg.nil _ _ _ _, Or.inl ⟨by rw [hres], ?_⟩⟩,
        fun _ => by rw [hres]⟩
      rw [hres]
      exact Or.inl ⟨loc.idx.1, layout, lookup_mem hl⟩

theorem placeToReg_spec_proj {Γ : Ctx} {L : LayEnv Γ} (kind : RefKind) {ρ τ : LayoutTy}
    {b : Place Γ ρ} (f : PathTo ρ τ) (h_np : NotProj b) (cs : CompilerState)
    (hlive : ∀ x, LiveOf cs x → regIdx x < cs.nextReg)
    (ihb : ∀ bOut : ResultWithEvidence PtrResult (PlaceToRegEvidence L kind b),
      CheckedCompilerM.value (placeToRegChecked L kind b) cs = .ok bOut →
      PlaceSpec L kind b cs bOut.result)
    {out : ResultWithEvidence PtrResult (PlaceToRegEvidence L kind (.proj b f))}
    (hv : CheckedCompilerM.value (placeToRegChecked L kind (.proj b f)) cs = .ok out) :
    PlaceSpec L kind (.proj b f) cs out.result := by
  cases hb : CheckedCompilerM.value (placeToRegChecked L kind b) cs with
  | error e =>
      exfalso
      rw [proj_eq f h_np] at hv
      simp only [CheckedCompilerM.value_bind, hb] at hv
      cases hv
  | ok bOut =>
      obtain ⟨segb, hEb, hpmb, hleb, ⟨hsegb, hresb⟩, hnpb⟩ := ihb bOut hb
      have hcl : bOut.result.cleanup = [] := hnpb h_np
      have hnot : ¬ NotProj (Place.proj b f) := fun h => h _ b f rfl
      obtain ⟨h0, h1⟩ := proj_lowering (kind := kind) f h_np hb
      by_cases hoff : pathOffsetB L b f = 0
      · obtain ⟨hrun, out', hv', hres⟩ := h0 hoff
        rw [hv] at hv'
        obtain rfl := Except.ok.inj hv'
        unfold PlaceSpec
        rw [hrun, hres]
        exact ⟨segb, hEb, hpmb, hleb, ⟨hsegb, hresb⟩, fun h => absurd h hnot⟩
      · obtain ⟨hrun, out', hv', hres⟩ := h1 hoff
        rw [hv] at hv'
        obtain rfl := Except.ok.inj hv'
        unfold PlaceSpec
        rw [hrun, hres, hcl]
        generalize CheckedCompilerM.run (placeToRegChecked L kind b) cs = csb at *
        have hreg : RegOK (LiveOf cs) NoIns cs.nextReg csb.nextReg segb bOut.result.reg := by
          rcases hresb with ⟨-, h⟩ | ⟨n, pre, base, off, hc, -⟩
          · exact h
          · rw [hcl] at hc; cases hc
        refine ⟨segb ++ [.Assgn (Register.R csb.nextReg)
            (borrowRhs kind (placeSizeB L (.proj b f)) bOut.result.reg (pathOffsetB L b f))],
          hEb.trans (StateIncr.bump_emit csb _) (Emits.bump_emit csb _), by rw [← hpmb]; rfl,
          by simp only [compile.emit, bumpReg]; omega, ⟨?_, ?_⟩, fun h => absurd h hnot⟩
        · refine hsegb.snoc (fun x hx => by have := hlive x hx; omega) (fun x h => h.elim)
            (fun x hx => ?_) (fun r n h => by cases h) rfl (fun _ _ _ h => by cases h)
            (Nat.le_succ _) hleb
          simp only [Instr.regs, borrowRhs, Rhs.regs, List.mem_cons, List.mem_singleton,
            List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl
          · exact Or.inr (Or.inr ⟨hleb, by simp [regIdx, compile.emit, bumpReg], fun ⟨n, hn⟩ => by
              obtain ⟨-, -, h2⟩ := (hsegb.died_fresh (fun x hx => by have := hlive x hx; omega)
                (fun x h => h.elim) ⟨n, hn⟩).2
              simp [regIdx] at h2⟩)
          · exact hreg.mono (Nat.le_succ _)
        · right
          refine ⟨placeSizeB L (.proj b f), segb, bOut.result.reg, pathOffsetB L b f, rfl, rfl,
            fun i hi hr => ?_, hleb, by simp [regIdx, compile.emit, bumpReg]⟩
          rcases hsegb.regs i hi _ hr with h | h | h
          · have := hlive _ h; simp [regIdx] at this; omega
          · exact h.elim
          · simp [regIdx] at h <;> omega

theorem placeToReg_spec_deref {Γ : Ctx} {L : LayEnv Γ} (kind : RefKind) {σ : LayoutTy}
    (q : Place Γ (LayoutTy.PtrL σ)) (cs : CompilerState)
    (hlive : ∀ x, LiveOf cs x → regIdx x < cs.nextReg)
    (ihq : ∀ qOut : ResultWithEvidence PtrResult (PlaceToRegEvidence L RefKind.Shared q),
      CheckedCompilerM.value (placeToRegChecked L RefKind.Shared q) cs = .ok qOut →
      PlaceSpec L RefKind.Shared q cs qOut.result)
    {out : ResultWithEvidence PtrResult (PlaceToRegEvidence L kind (.deref q))}
    (hv : CheckedCompilerM.value (placeToRegChecked L kind (.deref q)) cs = .ok out) :
    PlaceSpec L kind (.deref q) cs out.result := by
  cases hq : CheckedCompilerM.value (placeToRegChecked L RefKind.Shared q) cs with
  | error e =>
      exfalso
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
      rw [h_bind] at hv
      simp only [CheckedCompilerM.value_bind, hq] at hv
      cases hv
  | ok qOut =>
      obtain ⟨segq, hEq, hpmq, hleq, ⟨hsegq, hresq⟩, -⟩ := ihq qOut hq
      obtain ⟨hrun, out', hv', hres⟩ := deref_lowering (kind := kind) hq
      rw [hv] at hv'
      obtain rfl := Except.ok.inj hv'
      unfold PlaceSpec
      rw [hrun, hres]
      generalize CheckedCompilerM.run (placeToRegChecked L RefKind.Shared q) cs = csq at *
      have hlive' : ∀ x, LiveOf cs x → regIdx x < cs.nextReg := hlive
      have hl0 : ∀ x, LiveOf cs x → regIdx x < cs.nextReg := hlive
      let ld : Register := Register.R csq.nextReg
      let acc : Instr := .Assgn ld (.Load (derefLoad L q) qOut.result.reg)
      have hE1 : Emits cs (compile.emit (bumpReg csq) [acc]) (segq ++ [acc]) :=
        hEq.trans (StateIncr.bump_emit csq _) (Emits.bump_emit csq _)
      have hld_fresh : ∀ i ∈ segq, ld ∉ i.regs := fun i hi hr => by
        rcases hsegq.regs i hi _ hr with h | h | h
        · have := hlive _ h; simp [ld, regIdx] at this; omega
        · exact h.elim
        · simp [ld, regIdx] at h <;> omega
      have hld_nd : ¬ DiedIn segq ld := fun ⟨n, hn⟩ => hld_fresh _ hn (by simp [Instr.regs])
      rcases hresq with ⟨hcl, hreg⟩ | ⟨n, pre, base, off, hcl, hseg, hfresh, hw1, hw2⟩
      · -- the pointer was closed: one load
        rw [hcl]
        simp only [cleanupInstrs, List.reverse_nil, List.map_nil]
        have hE := hE1.trans (emit_state_incr _ []) (Emits.emit _ [])
        rw [List.append_nil] at hE
        have hseg : Seg (LiveOf cs) NoIns cs.nextReg (csq.nextReg + 1) (segq ++ [acc]) :=
          hsegq.snoc (fun x hx => by have := hlive x hx; omega) (fun x h => h.elim)
            (fun x hx => by
              simp only [acc, Instr.regs, Rhs.regs, List.mem_cons, List.mem_singleton,
                List.not_mem_nil, or_false] at hx
              rcases hx with rfl | rfl
              · exact Or.inr (Or.inr ⟨hleq, by simp [ld, regIdx], hld_nd⟩)
              · exact hreg.mono (Nat.le_succ _))
            (fun r n h => by simp [acc] at h) (by simp [acc, Instr.noPtrConst])
            (fun _ _ _ h => by simp [acc] at h) (Nat.le_succ _) hleq
        refine ⟨segq ++ [acc], hE, by rw [← hpmq]; rfl,
          by simp only [compile.emit, bumpReg]; omega, ⟨by simpa [compile.emit, bumpReg] using hseg,
            Or.inl ⟨rfl, Or.inr (Or.inr ⟨by simp [ld, regIdx]; omega,
              by simp [ld, regIdx, compile.emit, bumpReg], fun ⟨n, hn⟩ => by
                rcases List.mem_append.mp hn with hn | hn
                · exact hld_nd ⟨n, hn⟩
                · simp [acc] at hn⟩)⟩⟩, fun _ => by first | rfl | trivial⟩
      · -- an open route borrow: the load is its access, then its `Die`
        rw [hcl]
        simp only [cleanupInstrs, List.reverse_cons, List.reverse_nil, List.nil_append,
          List.map_cons, List.map_nil]
        have hE := hE1.trans (emit_state_incr _ _) (Emits.emit _ [.Die qOut.result.reg n])
        have hacc : acc.through qOut.result.reg = true := by
          simp only [acc, Instr.through, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, true_and]
          intro h; rw [← h] at hw2; simp [ld, regIdx] at hw2
        have hseg1 : Seg (LiveOf cs) NoIns cs.nextReg (csq.nextReg + 1) (segq ++ [acc]) :=
          hsegq.snoc (fun x hx => by have := hlive x hx; omega) (fun x h => h.elim)
            (fun x hx => by
              simp only [acc, Instr.regs, Rhs.regs, List.mem_cons, List.mem_singleton,
                List.not_mem_nil, or_false] at hx
              rcases hx with rfl | rfl
              · exact Or.inr (Or.inr ⟨hleq, by simp [ld, regIdx], hld_nd⟩)
              · refine Or.inr (Or.inr ⟨hw1, by omega, fun ⟨m, hm⟩ => ?_⟩)
                rw [hseg] at hm
                rcases List.mem_append.mp hm with hm | hm
                · exact hfresh _ hm (by simp [Instr.regs])
                · simp at hm)
            (fun r n h => by simp [acc] at h) (by simp [acc, Instr.noPtrConst])
            (fun _ _ _ h => by simp [acc] at h) (Nat.le_succ _) hleq
        rw [hseg, List.append_assoc] at hseg1
        have hclose := hseg1.close (by trivial : PushKind RefKind.Shared) hacc hfresh ⟨hw1, by omega⟩
        refine ⟨segq ++ [acc] ++ [.Die qOut.result.reg n], hE, by rw [← hpmq]; rfl,
          by simp only [compile.emit, bumpReg]; omega, ⟨?_, Or.inl ⟨rfl, ?_⟩⟩, fun _ => by first | rfl | trivial⟩
        · rw [hseg]
          simpa [compile.emit, bumpReg, List.append_assoc] using hclose
        · refine Or.inr (Or.inr ⟨by simp [ld, regIdx]; omega,
            by simp [ld, regIdx, compile.emit, bumpReg], fun ⟨m, hm⟩ => ?_⟩)
          simp only [List.mem_append, List.mem_singleton] at hm
          rcases hm with (hm | hm) | hm
          · exact hld_nd ⟨m, hm⟩
          · simp [acc] at hm
          · simp only [Instr.Die.injEq] at hm
            obtain ⟨hm, -⟩ := hm
            rw [← hm] at hw2; simp [ld, regIdx] at hw2 <;> omega

theorem notProj_local {Γ : Ctx} {τ : LayoutTy} (loc : Local Γ τ) : NotProj (Place.local loc) :=
  fun _ _ _ h => by cases h

theorem notProj_deref {Γ : Ctx} {σ : LayoutTy} (q : Place Γ (LayoutTy.PtrL σ)) :
    NotProj (Place.deref q) :=
  fun _ _ _ h => by cases h

/-- Every place lowering satisfies `PlaceSpec`. -/
theorem placeToReg_spec {Γ : Ctx} {L : LayEnv Γ} :
    ∀ (kind : RefKind) {τ : LayoutTy} (p : Place Γ τ) (cs : CompilerState),
      (∀ x, LiveOf cs x → regIdx x < cs.nextReg) →
      ∀ (out : ResultWithEvidence PtrResult (PlaceToRegEvidence L kind p)),
      CheckedCompilerM.value (placeToRegChecked L kind p) cs = .ok out →
      PlaceSpec L kind p cs out.result
  | kind, _, .local loc, cs, _, out, hv => placeToReg_spec_local kind loc cs hv
  | kind, _, .proj (.proj b q) f, cs, hlive, out, hv => by
      obtain ⟨hrun, hval⟩ := placeToReg_assoc (L := L) kind b q f cs
      rw [hv] at hval
      cases hi : CheckedCompilerM.value (placeToRegChecked L kind (.proj b (q.append f))) cs with
      | error e => rw [hi] at hval; cases hval
      | ok out' =>
          rw [hi] at hval
          have hres : out.result = out'.result := by
            simp only [Except.map] at hval
            exact Except.ok.inj hval
          obtain ⟨seg, hE, hpm, hle, hpo, -⟩ :=
            placeToReg_spec kind (.proj b (q.append f)) cs hlive out' hi
          unfold PlaceSpec
          rw [hrun, hres]
          exact ⟨seg, hE, hpm, hle, hpo, fun h => absurd rfl (h _ (b.proj q) f)⟩
  | kind, _, .proj (.local loc) f, cs, hlive, out, hv =>
      placeToReg_spec_proj kind f (notProj_local loc) cs hlive
        (fun bOut hb => placeToReg_spec kind (.local loc) cs hlive bOut hb) hv
  | kind, _, .proj (.deref q) f, cs, hlive, out, hv =>
      placeToReg_spec_proj kind f (notProj_deref q) cs hlive
        (fun bOut hb => placeToReg_spec kind (.deref q) cs hlive bOut hb) hv
  | kind, _, .deref q, cs, hlive, out, hv =>
      placeToReg_spec_deref kind q cs hlive
        (fun qOut hq => placeToReg_spec RefKind.Shared q cs hlive qOut hq) hv
  termination_by _ _ p => p.depth
  decreasing_by all_goals (simp [Place.depth]; try omega)

/-! ## Borrow lowering -/

@[simp] theorem CompilerM.run_freshRegM (cs : CompilerState) :
    CompilerM.run freshRegM cs = bumpReg cs := rfl
@[simp] theorem CompilerM.value_freshRegM (cs : CompilerState) :
    CompilerM.value freshRegM cs = Register.R cs.nextReg := rfl
@[simp] theorem CompilerM.run_emitM (l : List Instr) (cs : CompilerState) :
    CompilerM.run (emitM l) cs = compile.emit cs l := rfl

/-- What a borrow lowering hands its caller: an open route borrow (of any
    protector flag and mask). -/
def BorrowOut (live : Register → Prop) (lo hi : Nat) (kind : RefKind) (prot : Bool)
    (mask : List Bool) (seg : List Instr) (res : PtrResult) : Prop :=
  Seg live NoIns lo hi seg ∧
  ∃ n pre base off, res.cleanup = [(res.reg, n)] ∧
    seg = pre ++ [.Assgn res.reg (.Borrow kind prot mask (some n) base off)] ∧
    (∀ i ∈ pre, res.reg ∉ i.regs) ∧ lo ≤ regIdx res.reg ∧ regIdx res.reg < hi

def BorrowSpec {Γ : Ctx} (L : LayEnv Γ) (kind : RefKind) (prot : Bool) (mask : List Bool)
    {τ : LayoutTy} (p : Place Γ τ) (cs : CompilerState) (out : PtrResult) : Prop :=
  ∃ seg, Emits cs (CheckedCompilerM.run (placeToBorrowRegChecked L kind prot mask p) cs) seg ∧
    (CheckedCompilerM.run (placeToBorrowRegChecked L kind prot mask p) cs).placeRegMap
      = cs.placeRegMap ∧
    cs.nextReg ≤ (CheckedCompilerM.run (placeToBorrowRegChecked L kind prot mask p) cs).nextReg ∧
    BorrowOut (LiveOf cs) cs.nextReg
      (CheckedCompilerM.run (placeToBorrowRegChecked L kind prot mask p) cs).nextReg
      kind prot mask seg out

/-- A borrow of a fresh register from a closed pointer register. -/
theorem borrow_after {live : Register → Prop} {cs csb : CompilerState} {seg : List Instr}
    (hlive : ∀ x, live x → regIdx x < cs.nextReg)
    (hE : Emits cs csb seg) (hseg : Seg live NoIns cs.nextReg csb.nextReg seg)
    (hle : cs.nextReg ≤ csb.nextReg) {reg : Register}
    (hreg : RegOK live NoIns cs.nextReg csb.nextReg seg reg)
    (kind : RefKind) (prot : Bool) (mask : List Bool) (n off : Nat) :
    Emits cs (compile.emit (bumpReg csb)
        [.Assgn (Register.R csb.nextReg) (.Borrow kind prot mask (some n) reg off)])
      (seg ++ [.Assgn (Register.R csb.nextReg) (.Borrow kind prot mask (some n) reg off)]) ∧
    BorrowOut live cs.nextReg (csb.nextReg + 1) kind prot mask
      (seg ++ [.Assgn (Register.R csb.nextReg) (.Borrow kind prot mask (some n) reg off)])
      ⟨Register.R csb.nextReg, [(Register.R csb.nextReg, n)]⟩ := by
  have hfresh : ∀ i ∈ seg, Register.R csb.nextReg ∉ i.regs := fun i hi hr => by
    rcases hseg.regs i hi _ hr with h | h | h
    · have := hlive _ h; simp [regIdx] at this; omega
    · exact h.elim
    · simp [regIdx] at h
  refine ⟨hE.trans (StateIncr.bump_emit csb _) (Emits.bump_emit csb _), ?_,
    n, seg, reg, off, rfl, rfl, hfresh, by simp [regIdx]; omega, by simp [regIdx]⟩
  refine hseg.snoc (fun x hx => by have := hlive x hx; omega) (fun x h => h.elim)
    (fun x hx => ?_) (fun r n h => by cases h) rfl (fun _ _ _ h => by cases h) (Nat.le_succ _) hle
  simp only [Instr.regs, Rhs.regs, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact Or.inr (Or.inr ⟨by simp [regIdx]; omega, by simp [regIdx],
      fun ⟨m, hm⟩ => hfresh _ hm (by simp [Instr.regs])⟩)
  · exact hreg.mono (Nat.le_succ _)

theorem PlaceSpec.np {Γ : Ctx} {L : LayEnv Γ} {kind : RefKind} {τ : LayoutTy}
    {p : Place Γ τ} {cs : CompilerState} {out : PtrResult} (h : PlaceSpec L kind p cs out)
    (hn : NotProj p) : out.cleanup = [] := by
  obtain ⟨_, _, _, _, _, h5⟩ := h
  exact h5 hn

/-- A closed place lowering's facts. -/
theorem PlaceSpec.closed {Γ : Ctx} {L : LayEnv Γ} {kind : RefKind} {τ : LayoutTy}
    {p : Place Γ τ} {cs : CompilerState} {out : PtrResult} (h : PlaceSpec L kind p cs out)
    (hc : out.cleanup = []) :
    ∃ seg, Emits cs (CheckedCompilerM.run (placeToRegChecked L kind p) cs) seg ∧
      (CheckedCompilerM.run (placeToRegChecked L kind p) cs).placeRegMap = cs.placeRegMap ∧
      cs.nextReg ≤ (CheckedCompilerM.run (placeToRegChecked L kind p) cs).nextReg ∧
      Seg (LiveOf cs) NoIns cs.nextReg (CheckedCompilerM.run (placeToRegChecked L kind p) cs).nextReg seg ∧
      RegOK (LiveOf cs) NoIns cs.nextReg
        (CheckedCompilerM.run (placeToRegChecked L kind p) cs).nextReg seg out.reg := by
  obtain ⟨seg, hE, hpm, hle, ⟨hseg, hres⟩, -⟩ := h
  rcases hres with ⟨-, hr⟩ | ⟨n, pre, base, off, hc', -⟩
  · exact ⟨seg, hE, hpm, hle, hseg, hr⟩
  · rw [hc] at hc'; cases hc'

/-- A borrow lowering of a non-projection base place `b` at offset `off`:
    the base place's code, then one route borrow from its register. -/
theorem borrowSpec_of {Γ : Ctx} {L : LayEnv Γ} {kind : RefKind} {prot : Bool} {mask : List Bool}
    {τ ρ : LayoutTy} {p : Place Γ τ} {b : Place Γ ρ} {kb : RefKind} {cs : CompilerState}
    (hlive : ∀ x, LiveOf cs x → regIdx x < cs.nextReg)
    {bOut : PtrResult} (hbs : PlaceSpec L kb b cs bOut) (hc : bOut.cleanup = [])
    {n off : Nat}
    (hrun : CheckedCompilerM.run (placeToBorrowRegChecked L kind prot mask p) cs =
      compile.emit (bumpReg (CheckedCompilerM.run (placeToRegChecked L kb b) cs))
        [.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked L kb b) cs).nextReg)
          (.Borrow kind prot mask (some n) bOut.reg off)])
    {res : PtrResult}
    (hres : res = ⟨Register.R (CheckedCompilerM.run (placeToRegChecked L kb b) cs).nextReg,
      [(Register.R (CheckedCompilerM.run (placeToRegChecked L kb b) cs).nextReg, n)]⟩) :
    BorrowSpec L kind prot mask p cs res := by
  obtain ⟨seg, hE, hpm, hle, hseg, hreg⟩ := hbs.closed hc
  obtain ⟨hE', hbo⟩ := borrow_after hlive hE hseg hle hreg kind prot mask n off
  unfold BorrowSpec
  rw [hrun, hres]
  exact ⟨_, hE', by rw [← hpm]; rfl, by simp only [compile.emit, bumpReg]; omega,
    by simpa [compile.emit, bumpReg] using hbo⟩

theorem placeToBorrowReg_spec {Γ : Ctx} {L : LayEnv Γ} (kind : RefKind) (prot : Bool)
    (mask : List Bool) :
    ∀ {τ : LayoutTy} (p : Place Γ τ) (cs : CompilerState),
      (∀ x, LiveOf cs x → regIdx x < cs.nextReg) →
      ∀ (out : ResultWithEvidence PtrResult (PlaceToBorrowRegEvidence L kind p)),
      CheckedCompilerM.value (placeToBorrowRegChecked L kind prot mask p) cs = .ok out →
      BorrowSpec L kind prot mask p cs out.result
  | _, .local loc, cs, hlive, out, hv => by
      cases hb : CheckedCompilerM.value (placeToRegChecked L kind (.local loc)) cs with
      | error e =>
          exfalso
          simp only [placeToBorrowRegChecked, CheckedCompilerM.value_bind, hb] at hv
          cases hv
      | ok bOut =>
          have hbs := placeToReg_spec kind (.local loc) cs hlive bOut hb
          refine borrowSpec_of hlive hbs (hbs.np (notProj_local loc)) ?_ ?_
            (n := placeSizeB L (.local loc)) (off := 0)
          · simp only [placeToBorrowRegChecked, CheckedCompilerM.run_bind,
              CheckedCompilerM.value_bind, hb, CheckedCompilerM.run_lift,
              CheckedCompilerM.value_lift, CheckedCompilerM.run_pure]
            rfl
          · simp only [placeToBorrowRegChecked, CheckedCompilerM.value_bind, hb,
              CheckedCompilerM.value_lift, CheckedCompilerM.run_lift,
              CheckedCompilerM.value_pure] at hv
            cases hv
            rfl
  | _, .proj (.proj b q) f, cs, hlive, out, hv => by
      obtain ⟨hrun, hval⟩ := placeToBorrowReg_assoc (L := L) kind prot mask b q f cs
      rw [hv] at hval
      cases hi : CheckedCompilerM.value
          (placeToBorrowRegChecked L kind prot mask (.proj b (q.append f))) cs with
      | error e => rw [hi] at hval; cases hval
      | ok out' =>
          rw [hi] at hval
          have hres : out.result = out'.result := by
            simp only [Except.map] at hval
            exact Except.ok.inj hval
          have := placeToBorrowReg_spec kind prot mask (.proj b (q.append f)) cs hlive out' hi
          unfold BorrowSpec at this ⊢
          rw [hrun, hres]
          exact this
  | _, .proj (.local loc) f, cs, hlive, out, hv => by
      cases hb : CheckedCompilerM.value (placeToRegChecked L kind (.local loc)) cs with
      | error e =>
          exfalso
          simp only [placeToBorrowRegChecked, CheckedCompilerM.value_bind, hb] at hv
          cases hv
      | ok bOut =>
          have hbs := placeToReg_spec kind (.local loc) cs hlive bOut hb
          refine borrowSpec_of hlive hbs (hbs.np (notProj_local loc)) ?_ ?_
            (n := placeSizeB L (.proj (.local loc) f)) (off := pathOffsetB L (.local loc) f)
          · simp only [placeToBorrowRegChecked, CheckedCompilerM.run_bind,
              CheckedCompilerM.value_bind, hb, CheckedCompilerM.run_lift,
              CheckedCompilerM.value_lift, CheckedCompilerM.run_pure]
            rfl
          · simp only [placeToBorrowRegChecked, CheckedCompilerM.value_bind, hb,
              CheckedCompilerM.value_lift, CheckedCompilerM.run_lift,
              CheckedCompilerM.value_pure] at hv
            cases hv
            simp only [hbs.np (notProj_local loc), List.nil_append]
            rfl
  | _, .proj (.deref q) f, cs, hlive, out, hv => by
      cases hb : CheckedCompilerM.value (placeToRegChecked L kind (.deref q)) cs with
      | error e =>
          exfalso
          simp only [placeToBorrowRegChecked, CheckedCompilerM.value_bind, hb] at hv
          cases hv
      | ok bOut =>
          have hbs := placeToReg_spec kind (.deref q) cs hlive bOut hb
          refine borrowSpec_of hlive hbs (hbs.np (notProj_deref q)) ?_ ?_
            (n := placeSizeB L (.proj (.deref q) f)) (off := pathOffsetB L (.deref q) f)
          · simp only [placeToBorrowRegChecked, CheckedCompilerM.run_bind,
              CheckedCompilerM.value_bind, hb, CheckedCompilerM.run_lift,
              CheckedCompilerM.value_lift, CheckedCompilerM.run_pure]
            rfl
          · simp only [placeToBorrowRegChecked, CheckedCompilerM.value_bind, hb,
              CheckedCompilerM.value_lift, CheckedCompilerM.run_lift,
              CheckedCompilerM.value_pure] at hv
            cases hv
            simp only [hbs.np (notProj_deref q), List.nil_append]
            rfl
  | _, .deref q, cs, hlive, out, hv => by
      cases hq : CheckedCompilerM.value (placeToRegChecked L RefKind.Shared q) cs with
      | error e =>
          exfalso
          simp only [placeToBorrowRegChecked, CheckedCompilerM.value_bind, hq] at hv
          cases hv
      | ok qOut =>
          obtain ⟨hrun_d, out_d, hv_d, hres_d⟩ := deref_lowering (kind := kind) hq
          have hbs := placeToReg_spec kind (.deref q) cs hlive out_d hv_d
          refine borrowSpec_of hlive hbs (hbs.np (notProj_deref q)) ?_ ?_
            (n := placeSizeB L (.deref q)) (off := 0)
          · rw [hrun_d, hres_d]
            simp only [placeToBorrowRegChecked, CheckedCompilerM.run_bind,
              CheckedCompilerM.value_bind, hq, CheckedCompilerM.run_lift,
              CheckedCompilerM.value_lift, CheckedCompilerM.run_pure]
            rfl
          · simp only [placeToBorrowRegChecked, CheckedCompilerM.value_bind, hq,
              CheckedCompilerM.value_lift, CheckedCompilerM.run_lift,
              CheckedCompilerM.value_pure] at hv
            cases hv
            rw [hrun_d]
            rfl
  termination_by _ p => p.depth
  decreasing_by all_goals (simp [Place.depth]; try omega)

/-! ## Closing a place with one access -/

/-- A place lowering, then one access that reads or writes through its
    register (and mentions only allowed registers), then the cleanup: the
    bracket, if open, is closed. -/
theorem close_access {live : Register → Prop} {lo mid hi : Nat} {kind : RefKind}
    {seg : List Instr} {res : PtrResult}
    (hlive : ∀ x, live x → regIdx x < lo) (hpo : PlaceOut live lo mid kind seg res)
    (hk : res.cleanup ≠ [] → PushKind kind) (hlm : lo ≤ mid) (hmh : mid ≤ hi)
    {acc : Instr} (hnd : ∀ r n, acc ≠ .Die r n) (hns : ∀ dr v skip, acc ≠ .SkipIf dr v skip)
    (hc : acc.noPtrConst = true) (hthr : res.cleanup ≠ [] → acc.through res.reg = true)
    (hregs : ∀ x ∈ acc.regs, x = res.reg ∨ RegOK live NoIns lo hi seg x) :
    Seg live NoIns lo hi (seg ++ [acc] ++ cleanupInstrs res.cleanup) ∧
      ∀ x, DiedIn (seg ++ [acc] ++ cleanupInstrs res.cleanup) x → DiedIn seg x ∨ x = res.reg := by
  obtain ⟨hseg, hres⟩ := hpo
  have hins : ∀ x, NoIns x → regIdx x < lo := fun x h => h.elim
  rcases hres with ⟨hcl, hreg⟩ | ⟨n, pre, base, off, hcl, hsegeq, hfresh, hw1, hw2⟩
  · rw [hcl]
    simp only [cleanupInstrs, List.reverse_nil, List.map_nil, List.append_nil]
    refine ⟨hseg.snoc hlive hins (fun x hx => ?_) hnd hc hns hmh hlm, fun x ⟨m, hm⟩ => ?_⟩
    · rcases hregs x hx with rfl | h
      · exact hreg.mono hmh
      · exact h
    · rcases List.mem_append.mp hm with hm | hm
      · exact Or.inl ⟨m, hm⟩
      · simp at hm; exact absurd hm.symm (hnd x m)
  · have hne : res.cleanup ≠ [] := by rw [hcl]; simp
    rw [hcl]
    simp only [cleanupInstrs, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.map_cons, List.map_nil]
    have hrok : RegOK live NoIns lo hi seg res.reg := by
      refine Or.inr (Or.inr ⟨hw1, by omega, fun ⟨m, hm⟩ => ?_⟩)
      rw [hsegeq] at hm
      rcases List.mem_append.mp hm with hm | hm
      · exact hfresh _ hm (by simp [Instr.regs])
      · simp at hm
    have h1 := hseg.snoc hlive hins (fun x hx => by
        rcases hregs x hx with rfl | h
        · exact hrok
        · exact h) hnd hc hns hmh hlm
    rw [hsegeq, List.append_assoc] at h1
    have h2 := h1.close (hk hne) (hthr hne) hfresh ⟨hw1, by omega⟩
    refine ⟨by rw [hsegeq]; simpa [List.append_assoc] using h2, fun x ⟨m, hm⟩ => ?_⟩
    simp only [List.mem_append, List.mem_singleton] at hm
    rcases hm with (hm | hm) | hm
    · exact Or.inl ⟨m, hm⟩
    · exact absurd hm.symm (hnd x m)
    · simp only [Instr.Die.injEq] at hm; exact Or.inr hm.1

/-- The facts of a value lowering: a segment, and the register holding
    the value. -/
def ValSpec (cs cs' : CompilerState) (seg : List Instr) (reg : Register) : Prop :=
  Emits cs cs' seg ∧ cs'.placeRegMap = cs.placeRegMap ∧ cs.nextReg ≤ cs'.nextReg ∧
    Seg (LiveOf cs) NoIns cs.nextReg cs'.nextReg seg ∧
    RegOK (LiveOf cs) NoIns cs.nextReg cs'.nextReg seg reg

theorem readToReg_spec {Γ : Ctx} {L : LayEnv Γ} {τ : LayoutTy} (p : Place Γ τ)
    (cs : CompilerState) (hlive : ∀ x, LiveOf cs x → regIdx x < cs.nextReg)
    {reg : Register} (hv : CheckedCompilerM.value (readToReg L p) cs = .ok reg) :
    ∃ seg, ValSpec cs (CheckedCompilerM.run (readToReg L p) cs) seg reg := by
  cases hp : CheckedCompilerM.value (placeToRegChecked L RefKind.Shared p) cs with
  | error e =>
      exfalso
      simp only [readToReg, CheckedCompilerM.value_bind, hp] at hv
      cases hv
  | ok pOut =>
      obtain ⟨segp, hE, hpm, hle, hpo, -⟩ := placeToReg_spec RefKind.Shared p cs hlive pOut hp
      have hrun : CheckedCompilerM.run (readToReg L p) cs =
          compile.emit (bumpReg (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared p) cs))
            ([.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared p) cs).nextReg)
              (.Load (placeLayout L p) pOut.result.reg)] ++ cleanupInstrs pOut.result.cleanup) := by
        simp only [readToReg, CheckedCompilerM.run_bind, CheckedCompilerM.value_bind, hp,
          CheckedCompilerM.run_lift, CheckedCompilerM.value_lift, CheckedCompilerM.run_pure]
        rfl
      have hreg : reg = Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared p) cs).nextReg := by
        simp only [readToReg, CheckedCompilerM.value_bind, hp, CheckedCompilerM.value_lift,
          CheckedCompilerM.run_lift, CheckedCompilerM.value_pure] at hv
        exact (Except.ok.inj hv).symm
      rw [hrun, hreg]
      generalize CheckedCompilerM.run (placeToRegChecked L RefKind.Shared p) cs = csp at *
      have hfresh : ∀ i ∈ segp, Register.R csp.nextReg ∉ i.regs := fun i hi hr => by
        rcases hpo.1.regs i hi _ hr with h | h | h
        · have := hlive _ h; simp [regIdx] at this; omega
        · exact h.elim
        · simp [regIdx] at h
      obtain ⟨hseg, hdied⟩ := close_access (hi := csp.nextReg + 1) hlive hpo (fun _ => trivial) hle
        (Nat.le_succ _) (acc := .Assgn (Register.R csp.nextReg) (.Load (placeLayout L p) pOut.result.reg))
        (fun r n h => by cases h) (fun _ _ _ h => by cases h) rfl
        (fun _ => by
          simp only [Instr.through, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, true_and]
          intro h
          rcases hpo.2 with ⟨hc, -⟩ | ⟨n, pre, base, off, hc, -, -, hw1, hw2⟩
          · contradiction
          · rw [← h] at hw2; simp [regIdx] at hw2)
        (fun x hx => by
          simp only [Instr.regs, Rhs.regs, List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl
          · exact Or.inr (Or.inr (Or.inr ⟨by simp [regIdx]; omega, by simp [regIdx],
              fun ⟨m, hm⟩ => hfresh _ hm (by simp [Instr.regs])⟩))
          · exact Or.inl rfl)
      refine ⟨segp ++ ([_] ++ cleanupInstrs pOut.result.cleanup),
        hE.trans (StateIncr.bump_emit csp _) (Emits.bump_emit csp _), by rw [← hpm]; rfl,
        by simp only [compile.emit, bumpReg]; omega, ?_, ?_⟩
      · rw [← List.append_assoc]
        simpa [compile.emit, bumpReg] using hseg
      · refine Or.inr (Or.inr ⟨by simp [regIdx]; omega,
          by simp [regIdx, compile.emit, bumpReg], fun hd => ?_⟩)
        rw [← List.append_assoc] at hd
        rcases hdied _ hd with ⟨m, hm⟩ | h
        · exact hfresh _ hm (by simp [Instr.regs])
        · rcases hpo.2 with ⟨hc, -⟩ | ⟨n, pre, base, off, hc, -, -, hw1, hw2⟩
          · -- a closed register: it is the place's, which is not fresh
            rcases hpo.2 with ⟨-, hr⟩ | ⟨_, _, _, _, hc', -⟩
            · rcases hr with hr | hr | hr
              · rw [← h] at hr; have := hlive _ hr; simp [regIdx] at this; omega
              · exact hr.elim
              · rw [← h] at hr; simp [regIdx] at hr
            · rw [hc] at hc'; cases hc'
          · rw [← h] at hw2; simp [regIdx] at hw2

/-! ## Composition helpers -/

theorem LiveOf.eq {cs cs' : CompilerState} (h : cs'.placeRegMap = cs.placeRegMap) :
    LiveOf cs' = LiveOf cs := by
  funext x; unfold LiveOf; rw [h]

/-- A register the first segment may hand on stays usable after a second
    segment of fresh registers. -/
theorem RegOK.append {live ins2 : Register → Prop} {lo hi1 hi2 : Nat} {s1 s2 : List Instr}
    {x : Register} (h : RegOK live NoIns lo hi1 s1 x) (h2 : Seg live ins2 hi1 hi2 s2)
    (hle : hi1 ≤ hi2) : RegOK live NoIns lo hi2 (s1 ++ s2) x := by
  rcases h with h | h | ⟨h1, h2', h3⟩
  · exact Or.inl h
  · exact h.elim
  · refine Or.inr (Or.inr ⟨h1, by omega, fun ⟨n, hn⟩ => ?_⟩)
    rcases List.mem_append.mp hn with hn | hn
    · exact h3 ⟨n, hn⟩
    · obtain ⟨p, hp, hpe⟩ := List.getElem_of_mem hn
      obtain ⟨-, hlo, -⟩ := h2.dies p x n (by rw [List.getElem?_eq_getElem hp, hpe])
      omega

/-- One fresh assignment. -/
theorem emit_fresh {live : Register → Prop} {cs csb : CompilerState} {seg : List Instr}
    (hlive : ∀ x, live x → regIdx x < cs.nextReg) (hE : Emits cs csb seg)
    (hseg : Seg live NoIns cs.nextReg csb.nextReg seg) (hle : cs.nextReg ≤ csb.nextReg)
    {rhs : Rhs} (hr : ∀ x ∈ rhs.regs, RegOK live NoIns cs.nextReg csb.nextReg seg x) :
    Emits cs (compile.emit (bumpReg csb) [.Assgn (Register.R csb.nextReg) rhs])
        (seg ++ [.Assgn (Register.R csb.nextReg) rhs]) ∧
      Seg live NoIns cs.nextReg (csb.nextReg + 1) (seg ++ [.Assgn (Register.R csb.nextReg) rhs]) ∧
      RegOK live NoIns cs.nextReg (csb.nextReg + 1) (seg ++ [.Assgn (Register.R csb.nextReg) rhs])
        (Register.R csb.nextReg) ∧
      (∀ x, RegOK live NoIns cs.nextReg csb.nextReg seg x →
        RegOK live NoIns cs.nextReg (csb.nextReg + 1) (seg ++ [.Assgn (Register.R csb.nextReg) rhs]) x) := by
  have hfresh : ∀ i ∈ seg, Register.R csb.nextReg ∉ i.regs := fun i hi hr => by
    rcases hseg.regs i hi _ hr with h | h | h
    · have := hlive _ h; simp [regIdx] at this; omega
    · exact h.elim
    · simp [regIdx] at h
  refine ⟨hE.trans (StateIncr.bump_emit csb _) (Emits.bump_emit csb _), ?_, ?_, fun x hx => ?_⟩
  · refine hseg.snoc hlive (fun x h => h.elim) (fun x hx => ?_) (fun r n h => by cases h) rfl
      (fun _ _ _ h => by cases h) (Nat.le_succ _) hle
    simp only [Instr.regs, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact Or.inr (Or.inr ⟨by simp [regIdx]; omega, by simp [regIdx],
        fun ⟨m, hm⟩ => hfresh _ hm (by simp [Instr.regs])⟩)
    · exact (hr x hx).mono (Nat.le_succ _)
  · exact Or.inr (Or.inr ⟨by simp [regIdx]; omega, by simp [regIdx], fun ⟨m, hm⟩ => by
      rcases List.mem_append.mp hm with hm | hm
      · exact hfresh _ hm (by simp [Instr.regs])
      · simp at hm⟩)
  · exact (hx.mono (Nat.le_succ _)).snoc (fun n h => by cases h)

/-- Two value lowerings in sequence. -/
theorem ValSpec.seq {cs cs1 cs2 : CompilerState} {s1 s2 : List Instr} {r1 r2 : Register}
    (hlive : ∀ x, LiveOf cs x → regIdx x < cs.nextReg)
    (h1 : ValSpec cs cs1 s1 r1) (hi : StateIncr cs1 cs2) (h2 : ValSpec cs1 cs2 s2 r2) :
    Emits cs cs2 (s1 ++ s2) ∧ cs2.placeRegMap = cs.placeRegMap ∧ cs.nextReg ≤ cs2.nextReg ∧
      Seg (LiveOf cs) NoIns cs.nextReg cs2.nextReg (s1 ++ s2) ∧
      RegOK (LiveOf cs) NoIns cs.nextReg cs2.nextReg (s1 ++ s2) r1 ∧
      RegOK (LiveOf cs) NoIns cs.nextReg cs2.nextReg (s1 ++ s2) r2 := by
  obtain ⟨hE1, hpm1, hle1, hseg1, hr1⟩ := h1
  obtain ⟨hE2, hpm2, hle2, hseg2, hr2⟩ := h2
  rw [LiveOf.eq hpm1] at hseg2 hr2
  refine ⟨hE1.trans hi hE2, hpm2.trans hpm1, by omega,
    hseg1.append hseg2 hlive (fun x h => h.elim) (fun x h => h.elim) hle1 hle2,
    hr1.append hseg2 hle2, ?_⟩
  rcases hr2 with h | h | ⟨h1', h2', h3⟩
  · exact Or.inl h
  · exact h.elim
  · refine Or.inr (Or.inr ⟨by omega, h2', fun ⟨n, hn⟩ => ?_⟩)
    rcases List.mem_append.mp hn with hn | hn
    · obtain ⟨p, hp, hpe⟩ := List.getElem_of_mem hn
      obtain ⟨-, -, hhi⟩ := hseg1.dies p r2 n (by rw [List.getElem?_eq_getElem hp, hpe])
      omega
    · exact h3 ⟨n, hn⟩

/-! ## Rvalues -/

/-- The store an rvalue hands its assignment: from a register the rvalue
    made, or of literals without pointers. -/
def StoreOK (lo hi : Nat) (seg : List Instr) (store : Register → List Instr) : Prop :=
  ∀ d, (∃ lay v, store d = [.RStore lay v d] ∧ lo ≤ regIdx v ∧ regIdx v < hi ∧ ¬ DiedIn seg v) ∨
       (∃ lay vals, store d = [.CStore lay vals d] ∧ ∀ w ∈ vals, w.isPtr = false)

def RhsSpec (cs cs' : CompilerState) (seg : List Instr) (store : Register → List Instr)
    (post : List (Register × Nat)) : Prop :=
  Emits cs cs' seg ∧ cs'.placeRegMap = cs.placeRegMap ∧ cs.nextReg ≤ cs'.nextReg ∧
    Seg (LiveOf cs) NoIns cs.nextReg cs'.nextReg seg ∧ post = [] ∧
    StoreOK cs.nextReg cs'.nextReg seg store

/-- Instructions that mention only the register `d`, after it is made. -/
theorem Seg.append_only {live : Register → Prop} {lo hi : Nat} {seg : List Instr} {d : Register}
    (hlive : ∀ x, live x → regIdx x < lo) (hlo : lo ≤ hi) (h : Seg live NoIns lo hi seg)
    (hd : RegOK live NoIns lo hi seg d) :
    ∀ (l : List Instr), (∀ i ∈ l, (∀ x ∈ i.regs, x = d) ∧ (∀ r n, i ≠ .Die r n) ∧
      (∀ dr v skip, i ≠ .SkipIf dr v skip) ∧ i.noPtrConst = true) →
      Seg live NoIns lo hi (seg ++ l) ∧ RegOK live NoIns lo hi (seg ++ l) d := by
  intro l
  induction l generalizing seg with
  | nil => intro _; simpa using ⟨h, hd⟩
  | cons i l ih =>
      intro hl
      obtain ⟨hx, hnd, hns, hc⟩ := hl i List.mem_cons_self
      have h1 := h.snoc hlive (fun x h => h.elim) (fun x hx' => by rw [hx x hx']; exact hd) hnd hc hns
        (Nat.le_refl _) hlo
      have hd1 := hd.snoc (fun n h => hnd d n h)
      have := ih h1 hd1 (fun j hj => hl j (List.mem_cons_of_mem _ hj))
      simpa using this

theorem readRhsPre_spec {Γ : Ctx} {L : LayEnv Γ} {dstL : bytes.BLayout} {σ τ : LayoutTy}
    {rhs : RExpr Γ τ} {src : Place Γ σ} {mk : Register → Rhs} {post : Register → List Instr}
    {ev : (srcRes : PtrResult) → PlaceToRegEvidence L RefKind.Shared src srcRes →
      (dstPtr : Register) → RExprToEvidence L dstPtr rhs}
    (hmk : ∀ r, (mk r).regs = [r])
    (hthr : ∀ r d, d ≠ r → (Instr.Assgn d (mk r)).through r = true)
    (hpost : ∀ d, ∀ i ∈ post d, (∀ x ∈ i.regs, x = d) ∧ (∀ r n, i ≠ .Die r n) ∧
      (∀ dr v skip, i ≠ .SkipIf dr v skip) ∧ i.noPtrConst = true)
    (cs : CompilerState) (hlive : ∀ x, LiveOf cs x → regIdx x < cs.nextReg)
    {pre : RhsPre L τ rhs}
    (hv : CheckedCompilerM.value (readRhsPre L dstL rhs src mk post ev) cs = .ok pre) :
    ∃ seg, RhsSpec cs (CheckedCompilerM.run (readRhsPre L dstL rhs src mk post ev) cs) seg
      pre.store pre.postCleanup := by
  cases hp : CheckedCompilerM.value (placeToRegChecked L RefKind.Shared src) cs with
  | error e =>
      exfalso
      simp only [readRhsPre, CheckedCompilerM.value_bind, hp] at hv
      cases hv
  | ok pOut =>
      obtain ⟨segp, hE, hpm, hle, hpo, -⟩ := placeToReg_spec RefKind.Shared src cs hlive pOut hp
      have hrun : CheckedCompilerM.run (readRhsPre L dstL rhs src mk post ev) cs =
          compile.emit (bumpReg (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared src) cs))
            ([.Assgn (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared src) cs).nextReg)
              (mk pOut.result.reg)] ++ cleanupInstrs pOut.result.cleanup ++
              post (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared src) cs).nextReg)) := by
        simp only [readRhsPre, CheckedCompilerM.run_bind, CheckedCompilerM.value_bind, hp,
          CheckedCompilerM.run_lift, CheckedCompilerM.value_lift, CheckedCompilerM.run_pure]
        rfl
      have hpre : pre.store = (fun d => [.RStore dstL
            (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared src) cs).nextReg) d]) ∧
          pre.postCleanup = [] := by
        simp only [readRhsPre, CheckedCompilerM.value_bind, hp, CheckedCompilerM.value_lift,
          CheckedCompilerM.run_lift, CheckedCompilerM.value_pure] at hv
        cases hv
        exact ⟨rfl, rfl⟩
      rw [hrun, hpre.1, hpre.2]
      generalize CheckedCompilerM.run (placeToRegChecked L RefKind.Shared src) cs = csp at *
      let t : Register := Register.R csp.nextReg
      have hfresh : ∀ i ∈ segp, t ∉ i.regs := fun i hi hr => by
        rcases hpo.1.regs i hi _ hr with h | h | h
        · have := hlive _ h; simp [t, regIdx] at this; omega
        · exact h.elim
        · simp [t, regIdx] at h
      have htne : t ≠ pOut.result.reg := by
        intro h
        rcases hpo.2 with ⟨-, hr⟩ | ⟨n, pre', base, off, -, -, -, hw1, hw2⟩
        · rcases hr with hr | hr | hr
          · rw [← h] at hr; have := hlive _ hr; simp [t, regIdx] at this; omega
          · exact hr.elim
          · rw [← h] at hr; simp [t, regIdx] at hr
        · rw [← h] at hw2; simp [t, regIdx] at hw2
      obtain ⟨hseg, hdied⟩ := close_access (hi := csp.nextReg + 1) hlive hpo (fun _ => trivial) hle
        (Nat.le_succ _) (acc := .Assgn t (mk pOut.result.reg))
        (fun r n h => by cases h) (fun _ _ _ h => by cases h) rfl
        (fun _ => hthr _ _ htne)
        (fun x hx => by
          simp only [Instr.regs, hmk, List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl
          · exact Or.inr (Or.inr (Or.inr ⟨by simp [t, regIdx]; omega, by simp [t, regIdx],
              fun ⟨m, hm⟩ => hfresh _ hm (by simp [Instr.regs])⟩))
          · exact Or.inl rfl)
      have htok : RegOK (LiveOf cs) NoIns cs.nextReg (csp.nextReg + 1)
          (segp ++ [.Assgn t (mk pOut.result.reg)] ++ cleanupInstrs pOut.result.cleanup) t := by
        refine Or.inr (Or.inr ⟨by simp [t, regIdx]; omega, by simp [t, regIdx], fun hd => ?_⟩)
        rcases hdied _ hd with ⟨m, hm⟩ | h
        · exact hfresh _ hm (by simp [Instr.regs])
        · exact htne h
      obtain ⟨hseg2, htok2⟩ := Seg.append_only (fun x hx => hlive x hx) (by omega) hseg htok
        (post t) (hpost t)
      refine ⟨_, hE.trans (StateIncr.bump_emit csp _) (Emits.bump_emit csp _), by rw [← hpm]; rfl,
        by simp only [compile.emit, bumpReg]; omega, ?_, rfl, fun d => Or.inl ⟨dstL, t, rfl, ?_⟩⟩
      · simpa [compile.emit, bumpReg, List.append_assoc] using hseg2
      · rcases htok2 with h | h | ⟨h1, h2, h3⟩
        · have := hlive _ h; simp [t, regIdx] at this; omega
        · exact h.elim
        · exact ⟨h1, by simpa [compile.emit, bumpReg] using h2, by simpa [List.append_assoc] using h3⟩

theorem RegOK.window {live : Register → Prop} {lo hi : Nat} {seg : List Instr} {v : Register}
    (h : RegOK live NoIns lo hi seg v) (hlive : ∀ x, live x → regIdx x < lo)
    (hv : lo ≤ regIdx v) : lo ≤ regIdx v ∧ regIdx v < hi ∧ ¬ DiedIn seg v := by
  rcases h with h | h | h
  · have := hlive _ h; omega
  · exact h.elim
  · exact h

/-- An rvalue that ends in one fresh assignment, stored from its register. -/
theorem rhsSpec_fresh {cs csb : CompilerState} {seg : List Instr}
    (hlive : ∀ x, LiveOf cs x → regIdx x < cs.nextReg) (hE : Emits cs csb seg)
    (hpm : csb.placeRegMap = cs.placeRegMap) (hle : cs.nextReg ≤ csb.nextReg)
    (hseg : Seg (LiveOf cs) NoIns cs.nextReg csb.nextReg seg) {rhs : Rhs}
    (hr : ∀ x ∈ rhs.regs, RegOK (LiveOf cs) NoIns cs.nextReg csb.nextReg seg x)
    (dstL : bytes.BLayout) :
    RhsSpec cs (compile.emit (bumpReg csb) [.Assgn (Register.R csb.nextReg) rhs])
      (seg ++ [.Assgn (Register.R csb.nextReg) rhs])
      (fun d => [.RStore dstL (Register.R csb.nextReg) d]) [] := by
  obtain ⟨hE', hseg', hreg', -⟩ := emit_fresh hlive hE hseg hle hr
  refine ⟨hE', by rw [← hpm]; rfl, by simp only [compile.emit, bumpReg]; omega,
    by simpa [compile.emit, bumpReg] using hseg', rfl, fun d => Or.inl ⟨dstL, _, rfl, ?_⟩⟩
  have := hreg'.window hlive (by simp [regIdx]; omega)
  simpa [compile.emit, bumpReg] using this

theorem allocLen_spec {Γ : Ctx} {L : LayEnv Γ} {pointee : bytes.BLayout} (len : AllocLen Γ)
    (cs : CompilerState) (hlive : ∀ x, LiveOf cs x → regIdx x < cs.nextReg)
    {reg : Register} (hv : CheckedCompilerM.value (compileAllocLenChecked L pointee len) cs = .ok reg) :
    ∃ seg, ValSpec cs (CheckedCompilerM.run (compileAllocLenChecked L pointee len) cs) seg reg ∧
      cs.nextReg ≤ regIdx reg := by
  cases len with
  | const n =>
      simp only [compileAllocLenChecked, CheckedCompilerM.value_bind, CheckedCompilerM.value_lift,
        CheckedCompilerM.run_lift, CheckedCompilerM.value_pure] at hv
      cases hv
      have hrun : CheckedCompilerM.run (compileAllocLenChecked L pointee (.const n)) cs =
          compile.emit (bumpReg cs) [.Assgn (Register.R cs.nextReg) (.AllocN pointee n)] := by
        simp only [compileAllocLenChecked, CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
          CheckedCompilerM.run_lift, CheckedCompilerM.value_lift, CheckedCompilerM.run_pure]
        rfl
      rw [hrun]
      obtain ⟨hE, hseg, hreg, -⟩ := emit_fresh (rhs := .AllocN pointee n) hlive (Emits.nil cs)
        (Seg.nil _ _ _ _) (Nat.le_refl _) (fun x hx => by simp [Rhs.regs] at hx)
      refine ⟨_, ⟨hE, rfl, by simp only [compile.emit, bumpReg]; omega,
        by simpa [compile.emit, bumpReg] using hseg, by simpa [compile.emit, bumpReg] using hreg⟩,
        by simp [regIdx]⟩
  | fromPlace p =>
      cases h1 : CheckedCompilerM.value (readToReg L p) cs with
      | error e =>
          exfalso
          simp only [compileAllocLenChecked, guardRead, CheckedCompilerM.value_bind, h1] at hv
          cases hv
      | ok r =>
          obtain ⟨s1, hE1, hpm1, hle1, hseg1, hr1⟩ := readToReg_spec p cs hlive h1
          simp only [compileAllocLenChecked, guardRead, CheckedCompilerM.value_bind, h1,
            CheckedCompilerM.value_lift, CheckedCompilerM.run_lift, CheckedCompilerM.value_pure] at hv
          cases hv
          have hrun : CheckedCompilerM.run (compileAllocLenChecked L pointee (.fromPlace p)) cs =
              compile.emit (bumpReg (CheckedCompilerM.run (readToReg L p) cs))
                [.Assgn (Register.R (CheckedCompilerM.run (readToReg L p) cs).nextReg)
                  (.AllocDyn pointee r)] := by
            simp only [compileAllocLenChecked, guardRead, CheckedCompilerM.run_bind,
              CheckedCompilerM.value_bind, h1, CheckedCompilerM.run_lift,
              CheckedCompilerM.value_lift, CheckedCompilerM.run_pure]
            rfl
          rw [hrun]
          generalize CheckedCompilerM.run (readToReg L p) cs = c1 at *
          obtain ⟨hE, hseg, hreg, -⟩ := emit_fresh (rhs := .AllocDyn pointee r) hlive hE1 hseg1 hle1
            (fun x hx => by simp [Rhs.regs] at hx; rw [hx]; exact hr1)
          refine ⟨_, ⟨hE, by rw [← hpm1]; rfl, by simp only [compile.emit, bumpReg]; omega,
            by simpa [compile.emit, bumpReg] using hseg, by simpa [compile.emit, bumpReg] using hreg⟩,
            by simp [regIdx]; omega⟩

theorem thr_load (lay : bytes.BLayout) : ∀ r d, d ≠ r → (Instr.Assgn d (.Load lay r)).through r = true :=
  fun r d h => by simp [Instr.through, h]

theorem post_nil : ∀ (d : Register), ∀ i ∈ ([] : List Instr), (∀ x ∈ i.regs, x = d) ∧
    (∀ r n, i ≠ .Die r n) ∧ (∀ dr v skip, i ≠ .SkipIf dr v skip) ∧ i.noPtrConst = true :=
  fun _ _ h => by cases h

/-- A borrow lowering of kind `Mut`, no protector, no mask, is an open
    place lowering. -/
theorem BorrowOut.placeOut {live : Register → Prop} {lo hi : Nat} {kind : RefKind}
    {seg : List Instr} {res : PtrResult} (h : BorrowOut live lo hi kind false [] seg res) :
    PlaceOut live lo hi kind seg res :=
  ⟨h.1, Or.inr h.2⟩

theorem BorrowOut.reg {live : Register → Prop} {lo hi : Nat} {kind : RefKind} {prot : Bool}
    {mask : List Bool} {seg : List Instr} {res : PtrResult} (h : BorrowOut live lo hi kind prot mask seg res) :
    lo ≤ regIdx res.reg ∧ regIdx res.reg < hi ∧ ¬ DiedIn seg res.reg := by
  obtain ⟨-, n, pre, base, off, -, hseg, hfresh, hw1, hw2⟩ := h
  refine ⟨hw1, hw2, fun ⟨m, hm⟩ => ?_⟩
  rw [hseg] at hm
  rcases List.mem_append.mp hm with hm | hm
  · exact hfresh _ hm (by simp [Instr.regs])
  · simp at hm

/-- Extending a segment with a value lowering. -/
theorem seg_extend {cs csm cs' : CompilerState} {sm s : List Instr} {r : Register}
    (hlive : ∀ x, LiveOf cs x → regIdx x < cs.nextReg) (hE : Emits cs csm sm)
    (hpm : csm.placeRegMap = cs.placeRegMap) (hle : cs.nextReg ≤ csm.nextReg)
    (hseg : Seg (LiveOf cs) NoIns cs.nextReg csm.nextReg sm) (hi : StateIncr csm cs')
    (h2 : ValSpec csm cs' s r) :
    Emits cs cs' (sm ++ s) ∧ cs'.placeRegMap = cs.placeRegMap ∧ cs.nextReg ≤ cs'.nextReg ∧
      Seg (LiveOf cs) NoIns cs.nextReg cs'.nextReg (sm ++ s) ∧
      (∀ x, RegOK (LiveOf cs) NoIns cs.nextReg csm.nextReg sm x →
        RegOK (LiveOf cs) NoIns cs.nextReg cs'.nextReg (sm ++ s) x) ∧
      RegOK (LiveOf cs) NoIns cs.nextReg cs'.nextReg (sm ++ s) r := by
  obtain ⟨hE2, hpm2, hle2, hseg2, hr2⟩ := h2
  rw [LiveOf.eq hpm] at hseg2 hr2
  refine ⟨hE.trans hi hE2, hpm2.trans hpm, by omega,
    hseg.append hseg2 hlive (fun x h => h.elim) (fun x h => h.elim) hle hle2,
    fun x hx => hx.append hseg2 hle2, ?_⟩
  rcases hr2 with h | h | ⟨h1', h2', h3⟩
  · exact Or.inl h
  · exact h.elim
  · refine Or.inr (Or.inr ⟨by omega, h2', fun ⟨n, hn⟩ => ?_⟩)
    rcases List.mem_append.mp hn with hn | hn
    · obtain ⟨p, hp, hpe⟩ := List.getElem_of_mem hn
      obtain ⟨-, -, hhi⟩ := hseg.dies p r n (by rw [List.getElem?_eq_getElem hp, hpe])
      omega
    · exact h3 ⟨n, hn⟩

theorem rexpr_spec {Γ : Ctx} {L : LayEnv Γ} (dstL : bytes.BLayout) {τ : LayoutTy}
    (expr : RExpr Γ τ) (cs : CompilerState) (hlive : ∀ x, LiveOf cs x → regIdx x < cs.nextReg)
    {pre : RhsPre L τ expr}
    (hv : CheckedCompilerM.value (compileRExprPreChecked L dstL expr) cs = .ok pre) :
    ∃ seg, RhsSpec cs (CheckedCompilerM.run (compileRExprPreChecked L dstL expr) cs) seg
      pre.store pre.postCleanup := by
  cases expr with
  | constInit value =>
      simp only [compileRExprPreChecked, CheckedCompilerM.value_pure] at hv
      cases hv
      exact ⟨[], Emits.nil cs, rfl, Nat.le_refl _, Seg.nil _ _ _ _, rfl,
        fun d => Or.inr ⟨dstL, _, rfl, by simp [Val.isPtr]⟩⟩
  | uninit =>
      simp only [compileRExprPreChecked, CheckedCompilerM.value_pure] at hv
      cases hv
      exact ⟨[], Emits.nil cs, rfl, Nat.le_refl _, Seg.nil _ _ _ _, rfl,
        fun d => Or.inr ⟨dstL, _, rfl, by simp [Val.isPtr]⟩⟩
  | copy src =>
      simp only [compileRExprPreChecked] at hv ⊢
      exact readRhsPre_spec (fun r => rfl) (thr_load _) post_nil cs hlive hv
  | ptrCast src =>
      simp only [compileRExprPreChecked] at hv ⊢
      exact readRhsPre_spec (fun r => rfl) (thr_load _) post_nil cs hlive hv
  | addr src =>
      simp only [compileRExprPreChecked] at hv ⊢
      exact readRhsPre_spec (fun r => rfl) (thr_load _) post_nil cs hlive hv
  | exposeAddr src =>
      simp only [compileRExprPreChecked] at hv ⊢
      exact readRhsPre_spec (fun r => rfl) (fun r d h => by simp [Instr.through, h]) post_nil cs
        hlive hv
  | fromExposed src =>
      simp only [compileRExprPreChecked] at hv ⊢
      exact readRhsPre_spec (fun r => rfl) (fun r d h => by simp [Instr.through, h]) post_nil cs
        hlive hv
  | ptrOffset src delta inbounds =>
      simp only [compileRExprPreChecked] at hv ⊢
      exact readRhsPre_spec (fun r => rfl) (fun r d h => by simp [Instr.through, h]) post_nil cs
        hlive hv
  | refSlice kind prot src =>
      simp only [compileRExprPreChecked] at hv ⊢
      exact readRhsPre_spec (fun r => rfl) (thr_load _)
        (fun d i hi => by
          simp at hi; subst hi
          refine ⟨fun x hx => by simpa [Instr.regs, Rhs.regs] using hx, (fun r n h => by cases h),
            (fun _ _ _ h => by cases h), rfl⟩) cs hlive hv
  | ref kind prot mask src =>
      cases hb : CheckedCompilerM.value (placeToBorrowRegChecked L kind prot
          (mirlite.maskBytes (placeLayout L src) mask) src) cs with
      | error e =>
          exfalso
          simp only [compileRExprPreChecked, CheckedCompilerM.value_bind, hb] at hv
          cases hv
      | ok bOut =>
          obtain ⟨seg, hE, hpm, hle, hbo⟩ := placeToBorrowReg_spec kind prot _ src cs hlive bOut hb
          simp only [compileRExprPreChecked, CheckedCompilerM.value_bind, hb,
            CheckedCompilerM.value_pure] at hv
          cases hv
          have hrun : CheckedCompilerM.run (compileRExprPreChecked L dstL (.ref kind prot mask src)) cs
              = CheckedCompilerM.run (placeToBorrowRegChecked L kind prot
                  (mirlite.maskBytes (placeLayout L src) mask) src) cs := by
            simp only [compileRExprPreChecked, CheckedCompilerM.run_bind,
              CheckedCompilerM.value_bind, hb, CheckedCompilerM.run_pure]
          rw [hrun]
          exact ⟨seg, hE, hpm, hle, hbo.1, rfl, fun d => Or.inl ⟨dstL, _, rfl, hbo.reg⟩⟩
  | move src =>
      cases hb : CheckedCompilerM.value (placeToBorrowRegChecked L RefKind.Mut false [] src) cs with
      | error e =>
          exfalso
          simp only [compileRExprPreChecked, CheckedCompilerM.value_bind, hb] at hv
          cases hv
      | ok bOut =>
          obtain ⟨segb, hE, hpm, hle, hbo⟩ :=
            placeToBorrowReg_spec RefKind.Mut false [] src cs hlive bOut hb
          simp only [compileRExprPreChecked, CheckedCompilerM.value_bind, hb,
            CheckedCompilerM.value_lift, CheckedCompilerM.run_lift, CheckedCompilerM.value_pure] at hv
          cases hv
          have hrun : CheckedCompilerM.run (compileRExprPreChecked L dstL (.move src)) cs =
              compile.emit (bumpReg (CheckedCompilerM.run
                  (placeToBorrowRegChecked L RefKind.Mut false [] src) cs))
                ([.Assgn (Register.R (CheckedCompilerM.run
                    (placeToBorrowRegChecked L RefKind.Mut false [] src) cs).nextReg)
                  (.Load (placeLayout L src) bOut.result.reg)] ++ cleanupInstrs bOut.result.cleanup) := by
            simp only [compileRExprPreChecked, CheckedCompilerM.run_bind,
              CheckedCompilerM.value_bind, hb, CheckedCompilerM.run_lift,
              CheckedCompilerM.value_lift, CheckedCompilerM.run_pure]
            rfl
          rw [hrun]
          generalize CheckedCompilerM.run (placeToBorrowRegChecked L RefKind.Mut false [] src) cs
            = csb at *
          let t : Register := Register.R csb.nextReg
          have hfresh : ∀ i ∈ segb, t ∉ i.regs := fun i hi hr => by
            rcases hbo.1.regs i hi _ hr with h | h | h
            · have := hlive _ h; simp [t, regIdx] at this; omega
            · exact h.elim
            · simp [t, regIdx] at h
          have hreg := hbo.reg
          have htne : t ≠ bOut.result.reg := by
            intro h; rw [← h] at hreg; simp [t, regIdx] at hreg
          obtain ⟨hseg, hdied⟩ := close_access (hi := csb.nextReg + 1) hlive hbo.placeOut
            (fun _ => trivial) hle (Nat.le_succ _) (acc := .Assgn t (.Load (placeLayout L src) bOut.result.reg))
            (fun r n h => by cases h) (fun _ _ _ h => by cases h) rfl
            (fun _ => thr_load _ _ _ htne)
            (fun x hx => by
              simp only [Instr.regs, Rhs.regs, List.mem_cons, List.not_mem_nil, or_false] at hx
              rcases hx with rfl | rfl
              · exact Or.inr (Or.inr (Or.inr ⟨by simp [t, regIdx]; omega, by simp [t, regIdx],
                  fun ⟨m, hm⟩ => hfresh _ hm (by simp [Instr.regs])⟩))
              · exact Or.inl rfl)
          refine ⟨_, hE.trans (StateIncr.bump_emit csb _) (Emits.bump_emit csb _), by rw [← hpm]; rfl,
            by simp only [compile.emit, bumpReg]; omega, ?_, rfl, fun d => Or.inl ⟨_, t, rfl, ?_⟩⟩
          · simpa [compile.emit, bumpReg, List.append_assoc] using hseg
          · refine ⟨by simp [t, regIdx]; omega, by simp [t, regIdx, compile.emit, bumpReg],
              fun hd => ?_⟩
            rw [← List.append_assoc] at hd
            rcases hdied _ hd with ⟨m, hm⟩ | h
            · exact hfresh _ hm (by simp [Instr.regs])
            · exact htne h
  | @alloc σ len =>
      cases ha : CheckedCompilerM.value
          (compileAllocLenChecked L (mirlite.allocPointee dstL σ) len) cs with
      | error e =>
          exfalso
          simp only [compileRExprPreChecked, CheckedCompilerM.value_bind, ha] at hv
          cases hv
      | ok r =>
          obtain ⟨seg, ⟨hE, hpm, hle, hseg, hr⟩, hge⟩ := allocLen_spec len cs hlive ha
          simp only [compileRExprPreChecked, CheckedCompilerM.value_bind, ha,
            CheckedCompilerM.value_pure] at hv
          cases hv
          have hrun : CheckedCompilerM.run (compileRExprPreChecked L dstL (RExpr.alloc (τ := σ) len)) cs
              = CheckedCompilerM.run (compileAllocLenChecked L (mirlite.allocPointee dstL σ) len) cs := by
            simp only [compileRExprPreChecked, CheckedCompilerM.run_bind,
              CheckedCompilerM.value_bind, ha, CheckedCompilerM.run_pure]
          rw [hrun]
          exact ⟨seg, hE, hpm, hle, hseg, rfl, fun d => Or.inl ⟨dstL, r, rfl, hr.window hlive hge⟩⟩
  | sliceLen src =>
      cases h1 : CheckedCompilerM.value (readToReg L src) cs with
      | error e =>
          exfalso
          simp only [compileRExprPreChecked, CheckedCompilerM.value_bind, h1] at hv
          cases hv
      | ok r =>
          obtain ⟨s1, hE1, hpm1, hle1, hseg1, hr1⟩ := readToReg_spec src cs hlive h1
          simp only [compileRExprPreChecked, CheckedCompilerM.value_bind, h1,
            CheckedCompilerM.value_lift, CheckedCompilerM.run_lift, CheckedCompilerM.value_pure] at hv
          cases hv
          simp only [compileRExprPreChecked, CheckedCompilerM.run_bind,
              CheckedCompilerM.value_bind, h1, CheckedCompilerM.run_lift,
              CheckedCompilerM.value_lift, CheckedCompilerM.run_pure, CompilerM.run_freshRegM, CompilerM.value_freshRegM,
            CompilerM.run_emitM]
          exact ⟨_, rhsSpec_fresh hlive hE1 hpm1 hle1 hseg1
            (fun x hx => by simp [Rhs.regs] at hx; rw [hx]; exact hr1) dstL⟩
  | addrOf loc path =>
      cases h1 : CheckedCompilerM.value (placeToRegChecked L RefKind.Shared (.local loc)) cs with
      | error e =>
          exfalso
          simp only [compileRExprPreChecked, CheckedCompilerM.value_bind, h1] at hv
          cases hv
      | ok out =>
          have hps := placeToReg_spec RefKind.Shared (.local loc) cs hlive out h1
          obtain ⟨s1, hE1, hpm1, hle1, hseg1, hr1⟩ := hps.closed (hps.np (notProj_local loc))
          simp only [compileRExprPreChecked, CheckedCompilerM.value_bind, h1,
            CheckedCompilerM.value_lift, CheckedCompilerM.run_lift, CheckedCompilerM.value_pure] at hv
          cases hv
          simp only [compileRExprPreChecked, CheckedCompilerM.run_bind,
              CheckedCompilerM.value_bind, h1, CheckedCompilerM.run_lift,
              CheckedCompilerM.value_lift, CheckedCompilerM.run_pure, CompilerM.run_freshRegM, CompilerM.value_freshRegM,
            CompilerM.run_emitM]
          exact ⟨_, rhsSpec_fresh hlive hE1 hpm1 hle1 hseg1
            (fun x hx => by simp [Rhs.regs] at hx; rw [hx]; exact hr1) dstL⟩
  | binOp op a b =>
      cases h1 : CheckedCompilerM.value (readToReg L a) cs with
      | error e =>
          exfalso
          simp only [compileRExprPreChecked, CheckedCompilerM.value_bind, h1] at hv
          cases hv
      | ok r1 =>
      cases h2 : CheckedCompilerM.value (readToReg L b) (CheckedCompilerM.run (readToReg L a) cs) with
      | error e =>
          exfalso
          simp only [compileRExprPreChecked, CheckedCompilerM.value_bind, h1, h2] at hv
          cases hv
      | ok r2 =>
          obtain ⟨s1, hv1⟩ := readToReg_spec a cs hlive h1
          have hlive1 : ∀ x, LiveOf (CheckedCompilerM.run (readToReg L a) cs) x →
              regIdx x < (CheckedCompilerM.run (readToReg L a) cs).nextReg := by
            rw [LiveOf.eq hv1.2.1]; intro x hx; have := hlive x hx; have := hv1.2.2.1; omega
          obtain ⟨s2, hv2⟩ := readToReg_spec b _ hlive1 h2
          obtain ⟨hE, hpm, hle, hseg, hr1', hr2'⟩ :=
            ValSpec.seq hlive hv1 (CheckedCompilerM.incr _ _) hv2
          simp only [compileRExprPreChecked, CheckedCompilerM.value_bind, h1, h2,
            CheckedCompilerM.value_lift, CheckedCompilerM.run_lift, CheckedCompilerM.value_pure] at hv
          cases hv
          simp only [compileRExprPreChecked, CheckedCompilerM.run_bind,
              CheckedCompilerM.value_bind, h1, h2, CheckedCompilerM.run_lift,
              CheckedCompilerM.value_lift, CheckedCompilerM.run_pure, CompilerM.run_freshRegM, CompilerM.value_freshRegM,
            CompilerM.run_emitM]
          exact ⟨_, rhsSpec_fresh hlive hE hpm hle hseg
            (fun x hx => by
              simp [Rhs.regs] at hx
              rcases hx with rfl | rfl
              · exact hr1'
              · exact hr2') dstL⟩
  | ptrOffsetBy src idx inbounds =>
      cases h1 : CheckedCompilerM.value (readToReg L src) cs with
      | error e =>
          exfalso
          simp only [compileRExprPreChecked, CheckedCompilerM.value_bind, h1] at hv
          cases hv
      | ok r1 =>
      cases h2 : CheckedCompilerM.value (readToReg L idx) (CheckedCompilerM.run (readToReg L src) cs) with
      | error e =>
          exfalso
          simp only [compileRExprPreChecked, CheckedCompilerM.value_bind, h1, h2] at hv
          cases hv
      | ok r2 =>
          obtain ⟨s1, hv1⟩ := readToReg_spec src cs hlive h1
          have hlive1 : ∀ x, LiveOf (CheckedCompilerM.run (readToReg L src) cs) x →
              regIdx x < (CheckedCompilerM.run (readToReg L src) cs).nextReg := by
            rw [LiveOf.eq hv1.2.1]; intro x hx; have := hlive x hx; have := hv1.2.2.1; omega
          obtain ⟨s2, hv2⟩ := readToReg_spec idx _ hlive1 h2
          obtain ⟨hE, hpm, hle, hseg, hr1', hr2'⟩ :=
            ValSpec.seq hlive hv1 (CheckedCompilerM.incr _ _) hv2
          simp only [compileRExprPreChecked, CheckedCompilerM.value_bind, h1, h2,
            CheckedCompilerM.value_lift, CheckedCompilerM.run_lift, CheckedCompilerM.value_pure] at hv
          cases hv
          rename_i t
          simp only [compileRExprPreChecked, CheckedCompilerM.run_bind,
              CheckedCompilerM.value_bind, h1, h2, CheckedCompilerM.run_lift,
              CheckedCompilerM.value_lift, CheckedCompilerM.run_pure, CompilerM.run_freshRegM, CompilerM.value_freshRegM,
            CompilerM.run_emitM]
          exact ⟨_, rhsSpec_fresh hlive hE hpm hle hseg
            (fun x hx => by
              simp [Rhs.regs] at hx
              rcases hx with rfl | rfl
              · exact hr1'
              · exact hr2') dstL⟩
  | subSlice src lo hi =>
      cases h1 : CheckedCompilerM.value (readToReg L src) cs with
      | error e =>
          exfalso
          simp only [compileRExprPreChecked, CheckedCompilerM.value_bind, h1] at hv
          cases hv
      | ok r1 =>
      cases h2 : CheckedCompilerM.value (readToReg L lo) (CheckedCompilerM.run (readToReg L src) cs) with
      | error e =>
          exfalso
          simp only [compileRExprPreChecked, CheckedCompilerM.value_bind, h1, h2] at hv
          cases hv
      | ok r2 =>
      cases h3 : CheckedCompilerM.value (readToReg L hi) (CheckedCompilerM.run (readToReg L lo)
          (CheckedCompilerM.run (readToReg L src) cs)) with
      | error e =>
          exfalso
          simp only [compileRExprPreChecked, CheckedCompilerM.value_bind, h1, h2, h3] at hv
          cases hv
      | ok r3 =>
          obtain ⟨s1, hv1⟩ := readToReg_spec src cs hlive h1
          have hlive1 : ∀ x, LiveOf (CheckedCompilerM.run (readToReg L src) cs) x →
              regIdx x < (CheckedCompilerM.run (readToReg L src) cs).nextReg := by
            rw [LiveOf.eq hv1.2.1]; intro x hx; have := hlive x hx; have := hv1.2.2.1; omega
          obtain ⟨s2, hv2⟩ := readToReg_spec lo _ hlive1 h2
          obtain ⟨hE, hpm, hle, hseg, hr1', hr2'⟩ :=
            ValSpec.seq hlive hv1 (CheckedCompilerM.incr _ _) hv2
          have hlive2 : ∀ x, LiveOf (CheckedCompilerM.run (readToReg L lo)
              (CheckedCompilerM.run (readToReg L src) cs)) x →
              regIdx x < (CheckedCompilerM.run (readToReg L lo)
                (CheckedCompilerM.run (readToReg L src) cs)).nextReg := by
            rw [LiveOf.eq hpm]; intro x hx; have := hlive x hx; omega
          obtain ⟨s3, hv3⟩ := readToReg_spec hi _ hlive2 h3
          obtain ⟨hE', hpm', hle', hseg', hold, hr3'⟩ :=
            seg_extend hlive hE hpm hle hseg (CheckedCompilerM.incr _ _) hv3
          simp only [compileRExprPreChecked, CheckedCompilerM.value_bind, h1, h2, h3,
            CheckedCompilerM.value_lift, CheckedCompilerM.run_lift, CheckedCompilerM.value_pure] at hv
          cases hv
          simp only [compileRExprPreChecked, CheckedCompilerM.run_bind,
              CheckedCompilerM.value_bind, h1, h2, h3, CheckedCompilerM.run_lift,
              CheckedCompilerM.value_lift, CheckedCompilerM.run_pure, CompilerM.run_freshRegM, CompilerM.value_freshRegM,
            CompilerM.run_emitM]
          exact ⟨_, rhsSpec_fresh hlive hE' hpm' hle' hseg'
            (fun x hx => by
              simp [Rhs.regs] at hx
              rcases hx with rfl | rfl | rfl
              · exact hold _ hr1'
              · exact hold _ hr2'
              · exact hr3') dstL⟩

/-! ## Roots -/

/-- What rooting a place leaves: at most one `Alloc` into a fresh
    register, which becomes a local's. -/
def EnsureSpec (cs cs' : CompilerState) (E : List Instr) : Prop :=
  Emits cs cs' E ∧ StateIncr cs cs' ∧ cs.nextReg ≤ cs'.nextReg ∧
    (∀ x, LiveOf cs' x → LiveOf cs x ∨ (cs.nextReg ≤ regIdx x ∧ regIdx x < cs'.nextReg)) ∧
    (∀ x, LiveOf cs x → LiveOf cs' x) ∧
    (∀ i ∈ E, ∀ x ∈ i.regs, LiveOf cs' x ∧ cs.nextReg ≤ regIdx x ∧ regIdx x < cs'.nextReg) ∧
    (∀ i ∈ E, (∀ r n, i ≠ .Die r n) ∧ (∀ dr v skip, i ≠ .SkipIf dr v skip) ∧ i.noPtrConst = true)

theorem EnsureSpec.refl (cs : CompilerState) : EnsureSpec cs cs [] :=
  ⟨Emits.nil cs, StateIncr.refl cs, Nat.le_refl _, fun x h => Or.inl h, fun x h => h,
    by simp, by simp⟩

theorem ensureLocal_spec {Γ : Ctx} {L : LayEnv Γ} {τ : LayoutTy} (loc : Local Γ τ)
    (cs : CompilerState) :
    ∃ E, EnsureSpec cs (CompilerM.run (ensureLocalRegE L loc) cs) E := by
  cases hl : getPlaceInfo cs loc.idx.1 with
  | some info =>
      obtain ⟨reg, layout⟩ := info
      rw [ensureLocalRegE_existing hl]
      exact ⟨[], EnsureSpec.refl cs⟩
  | none =>
      have hrun : CompilerM.run (ensureLocalRegE L loc) cs =
          setPlaceInfo (compile.emit (bumpReg cs) [.Assgn (Register.R cs.nextReg) (.Alloc (L loc.idx))])
            loc.idx.1 (Register.R cs.nextReg, τ) := by
        unfold CompilerM.run ensureLocalRegE
        split
        · rename_i h'; rw [hl] at h'; cases h'
        · rfl
      rw [hrun]
      refine ⟨[.Assgn (Register.R cs.nextReg) (.Alloc (L loc.idx))],
        ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
      · simpa using (Emits.bump_emit cs _).trans (setPlaceInfo_state_incr _ _ _) (Emits.of_eq rfl)
      · exact (StateIncr.bump_emit cs _).trans (setPlaceInfo_state_incr _ _ _)
      · simp [setPlaceInfo, compile.emit, bumpReg]
      · intro x ⟨idx, τ', hx⟩
        simp only [setPlaceInfo, List.mem_cons] at hx
        rcases hx with hx | hx
        · simp only [Prod.mk.injEq] at hx
          obtain ⟨-, rfl, -⟩ := hx
          exact Or.inr ⟨by simp [regIdx], by simp [regIdx, setPlaceInfo, compile.emit, bumpReg]⟩
        · exact Or.inl ⟨idx, τ', hx⟩
      · intro x ⟨idx, τ', hx⟩
        exact ⟨idx, τ', List.mem_cons_of_mem _ hx⟩
      · intro i hi x hx
        simp only [List.mem_singleton] at hi; subst hi
        simp only [Instr.regs, Rhs.regs, List.mem_singleton] at hx; subst hx
        exact ⟨⟨loc.idx.1, τ, List.mem_cons_self⟩, by simp [regIdx],
          by simp [regIdx, setPlaceInfo, compile.emit, bumpReg]⟩
      · intro i hi
        simp only [List.mem_singleton] at hi; subst hi
        exact ⟨(fun r n h => by cases h), (fun _ _ _ h => by cases h), rfl⟩

theorem ensurePlaceRoot_spec {Γ : Ctx} {L : LayEnv Γ} :
    ∀ {τ : LayoutTy} (p : Place Γ τ) (cs : CompilerState),
      ∃ E, EnsureSpec cs (CompilerM.run (ensurePlaceRoot L p) cs) E
  | _, .local loc, cs => by
      have : CompilerM.run (ensurePlaceRoot L (.local loc)) cs =
          CompilerM.run (ensureLocalRegE L loc) cs := by
        simp only [ensurePlaceRoot, CompilerM.run_bind, CompilerM.run_pure]
      rw [this]
      exact ensureLocal_spec loc cs
  | _, .proj base _, cs => by
      simp only [ensurePlaceRoot]
      exact ensurePlaceRoot_spec base cs
  | _, .deref q, cs => by
      simp only [ensurePlaceRoot]
      exact ensurePlaceRoot_spec q cs

/-! ## Statements -/

/-- A statement's segment. Unlike `Seg`, it may hold a `SkipIf`, which
    jumps to the segment's end. -/
structure StmtOK (cs cs' : CompilerState) (seg : List Instr) : Prop where
  emits : Emits cs cs' seg
  incr : StateIncr cs cs'
  le : cs.nextReg ≤ cs'.nextReg
  live : ∀ x, LiveOf cs' x → regIdx x < cs'.nextReg
  fresh : ∀ x, LiveOf cs' x → LiveOf cs x ∨ cs.nextReg ≤ regIdx x
  regs : ∀ i ∈ seg, ∀ x ∈ i.regs, LiveOf cs' x ∨ (cs.nextReg ≤ regIdx x ∧ regIdx x < cs'.nextReg)
  dies : ∀ p r n, seg[p]? = some (.Die r n) →
    ClosedAt seg p r n ∧ cs.nextReg ≤ regIdx r ∧ regIdx r < cs'.nextReg ∧ ¬ LiveOf cs' r
  cst : ∀ i ∈ seg, i.noPtrConst = true
  skips : ∀ p dr v skip, seg[p]? = some (.SkipIf dr v skip) → p + 1 + skip = seg.length

/-- A place lowering after a segment of the same frame. -/
theorem PlaceOut.prepend {live : Register → Prop} {lo mid hi : Nat} {kind : RefKind}
    {R D : List Instr} {res : PtrResult} (hlive : ∀ x, live x → regIdx x < lo)
    (hR : Seg live NoIns lo mid R) (hD : PlaceOut live mid hi kind D res) (hlm : lo ≤ mid)
    (hmh : mid ≤ hi) :
    PlaceOut live lo hi kind (R ++ D) res := by
  obtain ⟨hsegD, hres⟩ := hD
  have hseg := hR.append hsegD hlive (fun x h => h.elim) (fun x h => h.elim) hlm hmh
  refine ⟨hseg, ?_⟩
  rcases hres with ⟨hc, hr⟩ | ⟨n, pre, base, off, hc, hD, hfresh, hw1, hw2⟩
  · refine Or.inl ⟨hc, ?_⟩
    rcases hr with h | h | ⟨h1, h2, h3⟩
    · exact Or.inl h
    · exact h.elim
    · refine Or.inr (Or.inr ⟨by omega, h2, fun ⟨m, hm⟩ => ?_⟩)
      rcases List.mem_append.mp hm with hm | hm
      · obtain ⟨p, hp, hpe⟩ := List.getElem_of_mem hm
        obtain ⟨-, -, hhi⟩ := hR.dies p res.reg m (by rw [List.getElem?_eq_getElem hp, hpe])
        omega
      · exact h3 ⟨m, hm⟩
  · refine Or.inr ⟨n, R ++ pre, base, off, hc, by rw [hD, List.append_assoc], fun i hi hr => ?_,
      by omega, hw2⟩
    rcases List.mem_append.mp hi with hi | hi
    · rcases hR.regs i hi _ hr with h | h | h
      · have := hlive _ h; omega
      · exact h.elim
      · omega
    · exact hfresh i hi hr

theorem StmtOK.of_root {cs csE cs' : CompilerState} {E rest : List Instr}
    (hlive : ∀ x, LiveOf cs x → regIdx x < cs.nextReg) (hE : EnsureSpec cs csE E)
    (hEr : Emits csE cs' rest) (hi : StateIncr csE cs') (hpm : cs'.placeRegMap = csE.placeRegMap)
    (hle : csE.nextReg ≤ cs'.nextReg) (hseg : Seg (LiveOf csE) NoIns csE.nextReg cs'.nextReg rest) :
    StmtOK cs cs' (E ++ rest) := by
  obtain ⟨hEm, hEi, hEle, hEfresh, hEmono, hEregs, hEinstr⟩ := hE
  have hliveE : ∀ x, LiveOf csE x → regIdx x < csE.nextReg := fun x hx => by
    rcases hEfresh x hx with h | h
    · have := hlive x h; omega
    · exact h.2
  have hL : LiveOf cs' = LiveOf csE := LiveOf.eq hpm
  refine ⟨hEm.trans hi hEr, hEi.trans hi, by omega, by rw [hL]; intro x hx; have := hliveE x hx; omega,
    fun x hx => by
      rw [hL] at hx
      rcases hEfresh x hx with h | h
      · exact Or.inl h
      · exact Or.inr h.1,
    fun i hi x hx => ?_, fun p r n hp => ?_, fun i hi => ?_, fun p dr v skip hp => ?_⟩
  · rw [hL]
    rcases List.mem_append.mp hi with hi | hi
    · exact Or.inl (hEregs i hi x hx).1
    · rcases hseg.regs i hi x hx with h | h | h
      · exact Or.inl h
      · exact h.elim
      · exact Or.inr ⟨by omega, h.2⟩
  · rw [hL]
    have hnot : ∀ (q : Nat) (j : Instr), E[q]? = some j → ∀ r n, j ≠ .Die r n := fun q j hq =>
      (hEinstr j (List.mem_of_getElem? hq)).1
    by_cases hpl : p < E.length
    · rw [List.getElem?_append_left hpl] at hp
      exact absurd hp (fun h => hnot p _ h r n rfl)
    · rw [List.getElem?_append_right (by omega)] at hp
      obtain ⟨hc, hlo, hhi⟩ := hseg.dies _ r n hp
      have hrE : ∀ i ∈ E, r ∉ i.regs := fun i hi hr => by
        have := (hEregs i hi r hr).2.2; omega
      have := hc.append_left hrE
      rw [show E.length + (p - E.length) = p by omega] at this
      exact ⟨this, by omega, hhi, fun hl => by have := hliveE r hl; omega⟩
  · rcases List.mem_append.mp hi with hi | hi
    · exact (hEinstr i hi).2.2
    · exact hseg.cst i hi
  · exfalso
    have := List.mem_of_getElem? hp
    rcases List.mem_append.mp this with h | h
    · exact (hEinstr _ h).2.1 dr v skip rfl
    · exact hseg.noskip _ h dr v skip rfl

theorem compileAssign_spec {Γ : Ctx} {L : LayEnv Γ} {τ : LayoutTy} (dst : Place Γ τ)
    (rhs : RExpr Γ τ) (cs : CompilerState) (hlive : ∀ x, LiveOf cs x → regIdx x < cs.nextReg)
    {out : ResultWithEvidence Unit (fun _ => StmtEvidence L (.assign dst rhs))}
    (hv : CheckedCompilerM.value (compileAssignChecked L dst rhs) cs = .ok out) :
    ∃ seg, StmtOK cs (CheckedCompilerM.run (compileAssignChecked L dst rhs) cs) seg := by
  obtain ⟨E, hE⟩ := ensurePlaceRoot_spec (L := L) dst cs
  generalize hcsE : CompilerM.run (ensurePlaceRoot L dst) cs = csE at hE
  have hliveE : ∀ x, LiveOf csE x → regIdx x < csE.nextReg := fun x hx => by
    rcases hE.2.2.2.1 x hx with h | h
    · have := hlive x h; have := hE.2.2.1; omega
    · exact h.2
  cases hR : CheckedCompilerM.value (compileRExprPreChecked L (placeLayout L dst) rhs) csE with
  | error e =>
      exfalso
      simp only [compileAssignChecked, CheckedCompilerM.value_bind, CheckedCompilerM.value_lift,
        CheckedCompilerM.run_lift, hcsE, hR] at hv
      cases hv
  | ok pre =>
  cases hD : CheckedCompilerM.value (placeToRegChecked L RefKind.Mut dst)
      (CheckedCompilerM.run (compileRExprPreChecked L (placeLayout L dst) rhs) csE) with
  | error e =>
      exfalso
      simp only [compileAssignChecked, CheckedCompilerM.value_bind, CheckedCompilerM.value_lift,
        CheckedCompilerM.run_lift, hcsE, hR, hD] at hv
      cases hv
  | ok dOut =>
      have hrun : CheckedCompilerM.run (compileAssignChecked L dst rhs) cs =
          compile.emit (compile.emit (compile.emit
            (CheckedCompilerM.run (placeToRegChecked L RefKind.Mut dst)
              (CheckedCompilerM.run (compileRExprPreChecked L (placeLayout L dst) rhs) csE))
            (pre.store dOut.result.reg)) (cleanupInstrs pre.postCleanup))
            (cleanupInstrs dOut.result.cleanup) := by
        simp only [compileAssignChecked, CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
          CheckedCompilerM.value_lift, CheckedCompilerM.run_lift, hcsE, hR, hD,
          CheckedCompilerM.run_pure, CompilerM.run_emitM]
      rw [hrun]
      obtain ⟨segR, hER, hpmR, hleR, hsegR, hpost, hstore⟩ := rexpr_spec _ rhs csE hliveE hR
      have hiR := CheckedCompilerM.incr (compileRExprPreChecked L (placeLayout L dst) rhs) csE
      generalize CheckedCompilerM.run (compileRExprPreChecked L (placeLayout L dst) rhs) csE = csR
        at hER hpmR hleR hsegR hstore hD hiR ⊢
      have hliveR : ∀ x, LiveOf csR x → regIdx x < csR.nextReg := by
        rw [LiveOf.eq hpmR]; intro x hx; have := hliveE x hx; omega
      obtain ⟨segD, hED, hpmD, hleD, hpoD, -⟩ := placeToReg_spec RefKind.Mut dst csR hliveR dOut hD
      have hiD := CheckedCompilerM.incr (placeToRegChecked L RefKind.Mut dst) csR
      generalize CheckedCompilerM.run (placeToRegChecked L RefKind.Mut dst) csR = csD
        at hED hpmD hleD hpoD hiD ⊢
      rw [LiveOf.eq hpmR] at hpoD
      rw [hpost]
      simp only [cleanupInstrs, List.reverse_nil, List.map_nil, emit_nil]
      have hpo := PlaceOut.prepend hliveE hsegR hpoD hleR hleD
      -- the store is the access
      rcases hstore dOut.result.reg with ⟨lay, v, hst, hv1, hv2, hv3⟩ | ⟨lay, vals, hst, hnp⟩
      · rw [hst]
        have hvne : v ≠ dOut.result.reg → True := fun _ => trivial
        have hvok : RegOK (LiveOf csE) NoIns csE.nextReg csD.nextReg (segR ++ segD) v :=
          Or.inr (Or.inr ⟨hv1, by omega, fun ⟨m, hm⟩ => by
            rcases List.mem_append.mp hm with hm | hm
            · exact hv3 ⟨m, hm⟩
            · obtain ⟨p, hp, hpe⟩ := List.getElem_of_mem hm
              obtain ⟨-, hlo, -⟩ := hpoD.1.dies p v m (by rw [List.getElem?_eq_getElem hp, hpe])
              omega⟩)
        obtain ⟨hseg, -⟩ := close_access hliveE hpo (fun _ => trivial) (by omega) (Nat.le_refl _)
          (acc := .RStore lay v dOut.result.reg) (fun r n h => by cases h) (fun _ _ _ h => by cases h)
          rfl
          (fun hne => by
            simp only [Instr.through, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, true_and]
            intro h
            rcases hpoD.2 with ⟨hc, -⟩ | ⟨n, pre', base, off, hc, -, -, hw1, hw2⟩
            · exact hne hc
            · rw [h] at hv2; omega)
          (fun x hx => by
            simp only [Instr.regs, List.mem_cons, List.not_mem_nil, or_false] at hx
            rcases hx with rfl | rfl
            · exact Or.inr hvok
            · exact Or.inl rfl)
        have hE2 : Emits csE (compile.emit (compile.emit csD [.RStore lay v dOut.result.reg])
            (cleanupInstrs dOut.result.cleanup))
            (segR ++ segD ++ [.RStore lay v dOut.result.reg] ++ cleanupInstrs dOut.result.cleanup) :=
          ((hER.trans hiD hED).trans (emit_state_incr _ _) (Emits.emit _ _)).trans
            (emit_state_incr _ _) (Emits.emit _ _)
        refine ⟨E ++ (segR ++ segD ++ [.RStore lay v dOut.result.reg] ++
            cleanupInstrs dOut.result.cleanup), StmtOK.of_root hlive (by rw [← hcsE] at hE ⊢; exact hE)
          hE2 ((hiR.trans hiD).trans ((emit_state_incr _ _).trans (emit_state_incr _ _)))
          (by simp only [compile.emit]; rw [hpmD, hpmR]) (by simp only [compile.emit]; omega)
          (by simpa [compile.emit] using hseg)⟩
      · rw [hst]
        obtain ⟨hseg, -⟩ := close_access hliveE hpo (fun _ => trivial) (by omega) (Nat.le_refl _)
          (acc := .CStore lay vals dOut.result.reg) (fun r n h => by cases h)
          (fun _ _ _ h => by cases h)
          (by
            simp only [Instr.noPtrConst, Bool.not_eq_true', List.any_eq_false]
            intro w hw
            simp [hnp w hw])
          (fun _ => by simp [Instr.through])
          (fun x hx => by
            simp only [Instr.regs, List.mem_singleton] at hx
            exact Or.inl hx)
        have hE2 : Emits csE (compile.emit (compile.emit csD [.CStore lay vals dOut.result.reg])
            (cleanupInstrs dOut.result.cleanup))
            (segR ++ segD ++ [.CStore lay vals dOut.result.reg] ++ cleanupInstrs dOut.result.cleanup) :=
          ((hER.trans hiD hED).trans (emit_state_incr _ _) (Emits.emit _ _)).trans
            (emit_state_incr _ _) (Emits.emit _ _)
        refine ⟨E ++ (segR ++ segD ++ [.CStore lay vals dOut.result.reg] ++
            cleanupInstrs dOut.result.cleanup), StmtOK.of_root hlive (by rw [← hcsE] at hE ⊢; exact hE)
          hE2 ((hiR.trans hiD).trans ((emit_state_incr _ _).trans (emit_state_incr _ _)))
          (by simp only [compile.emit]; rw [hpmD, hpmR]) (by simp only [compile.emit]; omega)
          (by simpa [compile.emit] using hseg)⟩

/-! ## Code: segments that compose under concatenation -/

structure Code (live : Register → Prop) (lo hi : Nat) (seg : List Instr) : Prop where
  regs : ∀ i ∈ seg, ∀ x ∈ i.regs, live x ∨ (lo ≤ regIdx x ∧ regIdx x < hi)
  dies : ∀ p r n, seg[p]? = some (.Die r n) →
    ClosedAt seg p r n ∧ lo ≤ regIdx r ∧ regIdx r < hi ∧ ¬ live r
  cst : ∀ i ∈ seg, i.noPtrConst = true
  skips : ∀ p dr v skip, seg[p]? = some (.SkipIf dr v skip) → p + 1 + skip ≤ seg.length ∧
    ∀ d r n, seg[d]? = some (.Die r n) → ¬ (d - 2 < p + 1 + skip ∧ p + 1 + skip ≤ d)

theorem Code.nil (live : Register → Prop) (lo hi : Nat) : Code live lo hi [] :=
  ⟨by simp, fun p r n h => by simp at h, by simp, fun p dr v skip h => by simp at h⟩

theorem Code.append {live : Register → Prop} {lo mid hi : Nat} {s1 s2 : List Instr}
    (h1 : Code live lo mid s1) (h2 : Code live mid hi s2) (hlm : lo ≤ mid) (hmh : mid ≤ hi) :
    Code live lo hi (s1 ++ s2) := by
  have h12 : ∀ p r n, s1[p]? = some (Instr.Die r n) → ∀ i ∈ s2, r ∉ i.regs := fun p r n hp i hi hr => by
    obtain ⟨-, -, hhi, hnl⟩ := h1.dies p r n hp
    rcases h2.regs i hi r hr with h | h
    · exact hnl h
    · omega
  have h21 : ∀ p r n, s2[p]? = some (Instr.Die r n) → ∀ i ∈ s1, r ∉ i.regs := fun p r n hp i hi hr => by
    obtain ⟨-, hlo, -, hnl⟩ := h2.dies p r n hp
    rcases h1.regs i hi r hr with h | h
    · exact hnl h
    · omega
  refine ⟨fun i hi x hx => ?_, fun p r n hp => ?_, fun i hi => ?_, fun p dr v skip hp => ?_⟩
  · rcases List.mem_append.mp hi with hi | hi
    · rcases h1.regs i hi x hx with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h.1, by omega⟩
    · rcases h2.regs i hi x hx with h | h
      · exact Or.inl h
      · exact Or.inr ⟨by omega, h.2⟩
  · by_cases hpl : p < s1.length
    · rw [List.getElem?_append_left hpl] at hp
      obtain ⟨hc, h1', h2', h3'⟩ := h1.dies p r n hp
      exact ⟨hc.append_right hpl (h12 p r n hp), h1', by omega, h3'⟩
    · rw [List.getElem?_append_right (by omega)] at hp
      obtain ⟨hc, h1', h2', h3'⟩ := h2.dies _ r n hp
      have := hc.append_left (h21 _ r n hp)
      rw [show s1.length + (p - s1.length) = p by omega] at this
      exact ⟨this, by omega, h2', h3'⟩
  · rcases List.mem_append.mp hi with hi | hi
    · exact h1.cst i hi
    · exact h2.cst i hi
  · by_cases hpl : p < s1.length
    · rw [List.getElem?_append_left hpl] at hp
      obtain ⟨hlen, hns⟩ := h1.skips p dr v skip hp
      refine ⟨by simp; omega, fun d r n hd => ?_⟩
      by_cases hdl : d < s1.length
      · rw [List.getElem?_append_left hdl] at hd; exact hns d r n hd
      · rw [List.getElem?_append_right (by omega)] at hd
        have := (h2.dies _ r n hd).1.1
        omega
    · rw [List.getElem?_append_right (by omega)] at hp
      obtain ⟨hlen, hns⟩ := h2.skips _ dr v skip hp
      refine ⟨by simp; omega, fun d r n hd => ?_⟩
      by_cases hdl : d < s1.length
      · omega
      · rw [List.getElem?_append_right (by omega)] at hd
        have := hns _ r n hd
        omega

theorem Code.mono_live {live live' : Register → Prop} {lo hi : Nat} {seg : List Instr}
    (h : Code live lo hi seg) (h1 : ∀ x, live x → live' x)
    (h2 : ∀ x, live' x → live x ∨ hi ≤ regIdx x) : Code live' lo hi seg := by
  refine ⟨fun i hi x hx => ?_, fun p r n hp => ?_, h.cst, h.skips⟩
  · rcases h.regs i hi x hx with h' | h'
    · exact Or.inl (h1 x h')
    · exact Or.inr h'
  · obtain ⟨hc, hlo, hhi, hnl⟩ := h.dies p r n hp
    refine ⟨hc, hlo, hhi, fun hl => ?_⟩
    rcases h2 r hl with h' | h'
    · exact hnl h'
    · omega

theorem Seg.code {live : Register → Prop} {lo hi : Nat} {seg : List Instr}
    (h : Seg live NoIns lo hi seg) (hlive : ∀ x, live x → regIdx x < lo) : Code live lo hi seg := by
  refine ⟨fun i hi x hx => ?_, fun p r n hp => ?_, h.cst, fun p dr v skip hp => ?_⟩
  · rcases h.regs i hi x hx with h' | h' | h'
    · exact Or.inl h'
    · exact h'.elim
    · exact Or.inr h'
  · obtain ⟨hc, hlo, hhi⟩ := h.dies p r n hp
    exact ⟨hc, hlo, hhi, fun hl => by have := hlive r hl; omega⟩
  · exact absurd rfl (h.noskip _ (List.mem_of_getElem? hp) dr v skip)

theorem StmtOK.code {cs cs' : CompilerState} {seg : List Instr} (h : StmtOK cs cs' seg) :
    Code (LiveOf cs') cs.nextReg cs'.nextReg seg := by
  refine ⟨h.regs, h.dies, h.cst, fun p dr v skip hp => ?_⟩
  have hl := h.skips p dr v skip hp
  refine ⟨by omega, fun d r n hd => ?_⟩
  have := getElem?_some_lt hd
  omega

/-- A guard jumping over the code that follows it. -/
theorem Code.cons_skip {live : Register → Prop} {lo mid hi : Nat} {B : List Instr} {g : Register}
    {v : Word} (hB : Code live mid hi B) (hg : live g ∨ (lo ≤ regIdx g ∧ regIdx g < mid))
    (hlm : lo ≤ mid) (hmh : mid ≤ hi) :
    Code live lo hi (.SkipIf g v B.length :: B) := by
  have hrB : ∀ p r n, B[p]? = some (Instr.Die r n) → r ≠ g := fun p r n hp hrg => by
    obtain ⟨-, hlo, -, hnl⟩ := hB.dies p r n hp
    rcases hg with h | h
    · exact hnl (hrg ▸ h)
    · rw [hrg] at hlo; omega
  have hcons : Instr.SkipIf g v B.length :: B = [.SkipIf g v B.length] ++ B := rfl
  refine ⟨fun i hi x hx => ?_, fun p r n hp => ?_, fun i hi => ?_, fun p dr w skip hp => ?_⟩
  · rcases List.mem_cons.mp hi with rfl | hi
    · simp only [Instr.regs, List.mem_singleton] at hx; subst hx
      rcases hg with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h.1, by omega⟩
    · rcases hB.regs i hi x hx with h | h
      · exact Or.inl h
      · exact Or.inr ⟨by omega, h.2⟩
  · cases p with
    | zero => simp at hp
    | succ p =>
        simp only [List.getElem?_cons_succ] at hp
        obtain ⟨hc, hlo, hhi, hnl⟩ := hB.dies p r n hp
        have := hc.append_left (seg := [.SkipIf g v B.length]) (fun i hi hr => by
          simp only [List.mem_singleton] at hi; subst hi
          simp only [Instr.regs, List.mem_singleton] at hr
          exact hrB p r n hp hr)
        rw [← hcons, show [Instr.SkipIf g v B.length].length + p = p + 1 by simp; omega] at this
        exact ⟨this, by omega, hhi, hnl⟩
  · rcases List.mem_cons.mp hi with rfl | hi
    · rfl
    · exact hB.cst i hi
  · cases p with
    | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, Instr.SkipIf.injEq] at hp
        obtain ⟨-, -, rfl⟩ := hp
        refine ⟨by simp; omega, fun d r n hd => ?_⟩
        have := getElem?_some_lt hd
        simp at this
        omega
    | succ p =>
        simp only [List.getElem?_cons_succ] at hp
        obtain ⟨hlen, hns⟩ := hB.skips p dr w skip hp
        refine ⟨by simp; omega, fun d r n hd => ?_⟩
        cases d with
        | zero => simp at hd
        | succ d =>
            simp only [List.getElem?_cons_succ] at hd
            have := hns d r n hd
            have := (hB.dies d r n hd).1.1
            omega

/-! ## Statements and programs -/

def StmtSpec (cs cs' : CompilerState) (seg : List Instr) : Prop :=
  Emits cs cs' seg ∧ StateIncr cs cs' ∧ cs.nextReg ≤ cs'.nextReg ∧
    (∀ x, LiveOf cs' x → regIdx x < cs'.nextReg) ∧
    (∀ x, LiveOf cs' x → LiveOf cs x ∨ cs.nextReg ≤ regIdx x) ∧
    (∀ x, LiveOf cs x → LiveOf cs' x) ∧
    Code (LiveOf cs') cs.nextReg cs'.nextReg seg

theorem LiveOf.mono {cs cs' : CompilerState} (h : StateIncr cs cs') :
    ∀ x, LiveOf cs x → LiveOf cs' x :=
  fun x ⟨idx, τ, hx⟩ => ⟨idx, τ, h.placeRegMap_mono idx (x, τ) hx⟩

theorem StmtOK.spec {cs cs' : CompilerState} {seg : List Instr} (h : StmtOK cs cs' seg) :
    StmtSpec cs cs' seg :=
  ⟨h.emits, h.incr, h.le, h.live, h.fresh, LiveOf.mono h.incr, h.code⟩

theorem StmtSpec.seq {cs cs1 cs2 : CompilerState} {s1 s2 : List Instr}
    (h1 : StmtSpec cs cs1 s1) (h2 : StmtSpec cs1 cs2 s2) : StmtSpec cs cs2 (s1 ++ s2) := by
  obtain ⟨hE1, hi1, hle1, hl1, hf1, hm1, hc1⟩ := h1
  obtain ⟨hE2, hi2, hle2, hl2, hf2, hm2, hc2⟩ := h2
  refine ⟨hE1.trans hi2 hE2, hi1.trans hi2, by omega, hl2, fun x hx => ?_,
    fun x hx => hm2 x (hm1 x hx), ?_⟩
  · rcases hf2 x hx with h | h
    · rcases hf1 x h with h' | h'
      · exact Or.inl h'
      · exact Or.inr h'
    · exact Or.inr (by omega)
  · exact (hc1.mono_live hm2 fun x hx => hf2 x hx).append hc2 hle1 hle2

/-- A one-instruction statement without registers. -/
theorem stmtSpec_single (cs : CompilerState) (hlive : ∀ x, LiveOf cs x → regIdx x < cs.nextReg)
    {i : Instr} (hr : i.regs = []) (hnd : ∀ r n, i ≠ .Die r n)
    (hns : ∀ dr v skip, i ≠ .SkipIf dr v skip) (hc : i.noPtrConst = true) :
    StmtSpec cs (compile.emit cs [i]) [i] := by
  refine ⟨Emits.emit cs [i], emit_state_incr cs [i], Nat.le_refl _, hlive, fun x h => Or.inl h,
    fun x h => h, ⟨fun j hj x hx => ?_, fun p r n hp => ?_, fun j hj => ?_, fun p dr v skip hp => ?_⟩⟩
  · simp at hj; subst hj; rw [hr] at hx; cases hx
  · cases p with
    | zero => simp at hp; exact absurd hp (hnd r n)
    | succ p => simp at hp
  · simp at hj; subst hj; exact hc
  · cases p with
    | zero => simp at hp; exact absurd hp (hns dr v skip)
    | succ p => simp at hp

theorem skipIfAround_ok {α : Type} (g : Register) (v : Word) (body : CheckedCompilerM α)
    (cs : CompilerState) {a : α} (hb : CheckedCompilerM.value body (reserveLabel cs) = .ok a) :
    CheckedCompilerM.value (emitSkipIfAround g v body) cs = .ok () ∧
    CheckedCompilerM.run (emitSkipIfAround g v body) cs =
      patchLabel (CheckedCompilerM.run body (reserveLabel cs)) cs.nextLabel
        (.SkipIf g v ((CheckedCompilerM.run body (reserveLabel cs)).nextLabel -
          (reserveLabel cs).nextLabel)) := by
  simp only [CheckedCompilerM.value, CheckedCompilerM.run, CompilerM.value, CompilerM.run,
    emitSkipIfAround] at hb ⊢
  split
  · rename_i e he; rw [hb] at he; cases he
  · exact ⟨rfl, rfl⟩

theorem skipIfAround_err {α : Type} (g : Register) (v : Word) (body : CheckedCompilerM α)
    (cs : CompilerState) {e : CompilerError}
    (hb : CheckedCompilerM.value body (reserveLabel cs) = .error e) :
    CheckedCompilerM.value (emitSkipIfAround g v body) cs = .error e := by
  simp only [CheckedCompilerM.value, CheckedCompilerM.run, CompilerM.value, CompilerM.run,
    emitSkipIfAround] at hb ⊢
  split
  · rename_i e' he; rw [hb] at he; cases he; rfl
  · rename_i a ha; rw [hb] at ha; cases ha

theorem Emits.skip {cs csB : CompilerState} {B : List Instr} (h : Emits (reserveLabel cs) csB B)
    (g : Register) (v : Word) :
    Emits cs (patchLabel csB cs.nextLabel (.SkipIf g v (csB.nextLabel - (reserveLabel cs).nextLabel)))
      (.SkipIf g v B.length :: B) := by
  obtain ⟨hl, hc⟩ := h
  have hn : csB.nextLabel - (reserveLabel cs).nextLabel = B.length := by
    rw [hl]; omega
  rw [hn]
  refine ⟨by simp only [patchLabel, List.length_cons]; rw [hl]; simp [reserveLabel]; omega,
    fun k hk => ?_⟩
  simp only [patchLabel]
  cases k with
  | zero => simp
  | succ k =>
      rw [if_neg (by omega)]
      have := hc k (by simp at hk; omega)
      simp only [reserveLabel] at this
      rw [show cs.nextLabel + (k + 1) = cs.nextLabel + 1 + k by omega, this]
      simp

/-- A guard after a segment, jumping over the code that follows; the
    guard's register may be one the segment made (not died). -/
theorem Code.append_guard {live : Register → Prop} {lo mid hi : Nat} {s1 B : List Instr}
    {g : Register} {v : Word} (h1 : Code live lo mid s1) (h2 : Code live mid hi B)
    (hg : live g ∨ (lo ≤ regIdx g ∧ regIdx g < mid ∧ ∀ (p : Nat) r n, s1[p]? = some (Instr.Die r n) → r ≠ g))
    (hlm : lo ≤ mid) (hmh : mid ≤ hi) :
    Code live lo hi (s1 ++ .SkipIf g v B.length :: B) := by
  let live' : Register → Prop := fun x => live x ∨ x = g
  have hB' : Code live' mid hi B := by
    refine ⟨fun i hi x hx => ?_, fun p r n hp => ?_, h2.cst, h2.skips⟩
    · rcases h2.regs i hi x hx with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · obtain ⟨hc, hlo, hhi, hnl⟩ := h2.dies p r n hp
      refine ⟨hc, hlo, hhi, fun h => ?_⟩
      rcases h with h | h
      · exact hnl h
      · subst h
        rcases hg with h' | h'
        · exact hnl h'
        · omega
  have hS := hB'.cons_skip (v := v) (lo := mid) (Or.inl (Or.inr rfl)) (Nat.le_refl _) hmh
  have h1' : Code live' lo mid s1 := by
    refine ⟨fun i hi x hx => ?_, fun p r n hp => ?_, h1.cst, h1.skips⟩
    · rcases h1.regs i hi x hx with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · obtain ⟨hc, hlo, hhi, hnl⟩ := h1.dies p r n hp
      refine ⟨hc, hlo, hhi, fun h => ?_⟩
      rcases h with h | h
      · exact hnl h
      · subst h
        rcases hg with h' | h'
        · exact hnl h'
        · exact h'.2.2 p _ n hp rfl
  have hc := h1'.append hS hlm hmh
  refine ⟨fun i hi x hx => ?_, fun p r n hp => ?_, hc.cst, hc.skips⟩
  · rcases hc.regs i hi x hx with (h | h) | h
    · exact Or.inl h
    · subst h
      rcases hg with h' | h'
      · exact Or.inl h'
      · exact Or.inr ⟨h'.1, by omega⟩
    · exact Or.inr h
  · obtain ⟨hc', hlo, hhi, hnl⟩ := hc.dies p r n hp
    exact ⟨hc', hlo, hhi, fun h => hnl (Or.inl h)⟩

theorem compileStmt_spec {Γ : Ctx} {L : LayEnv Γ} (stmt : Stmt Γ) (cs : CompilerState)
    (hlive : ∀ x, LiveOf cs x → regIdx x < cs.nextReg)
    {out : ResultWithEvidence Unit (fun _ => StmtEvidence L stmt)}
    (hv : CheckedCompilerM.value (compileStmtChecked L stmt) cs = .ok out) :
    ∃ seg, StmtSpec cs (CheckedCompilerM.run (compileStmtChecked L stmt) cs) seg := by
  cases stmt with
  | halt =>
      have : CheckedCompilerM.run (compileStmtChecked L .halt) cs = compile.emit cs [.Halt] := by
        simp only [compileStmtChecked, CheckedCompilerM.run_bind, CheckedCompilerM.value_lift,
          CheckedCompilerM.run_lift, CheckedCompilerM.run_pure, CompilerM.run_emitM]
      rw [this]
      exact ⟨_, stmtSpec_single cs hlive rfl (fun _ _ h => by cases h) (fun _ _ _ h => by cases h) rfl⟩
  | pushProtectors =>
      have : CheckedCompilerM.run (compileStmtChecked L .pushProtectors) cs =
          compile.emit cs [.PushProt] := by
        simp only [compileStmtChecked, CheckedCompilerM.run_bind, CheckedCompilerM.value_lift,
          CheckedCompilerM.run_lift, CheckedCompilerM.run_pure, CompilerM.run_emitM]
      rw [this]
      exact ⟨_, stmtSpec_single cs hlive rfl (fun _ _ h => by cases h) (fun _ _ _ h => by cases h) rfl⟩
  | popProtectors =>
      have : CheckedCompilerM.run (compileStmtChecked L .popProtectors) cs =
          compile.emit cs [.PopProt] := by
        simp only [compileStmtChecked, CheckedCompilerM.run_bind, CheckedCompilerM.value_lift,
          CheckedCompilerM.run_lift, CheckedCompilerM.run_pure, CompilerM.run_emitM]
      rw [this]
      exact ⟨_, stmtSpec_single cs hlive rfl (fun _ _ h => by cases h) (fun _ _ _ h => by cases h) rfl⟩
  | assign dst rhs =>
      simp only [compileStmtChecked] at hv ⊢
      obtain ⟨seg, h⟩ := compileAssign_spec dst rhs cs hlive hv
      exact ⟨seg, h.spec⟩
  | dealloc dst =>
      cases h1 : CheckedCompilerM.value (readToReg L dst) cs with
      | error e =>
          exfalso
          simp only [compileStmtChecked, CheckedCompilerM.value_bind, h1] at hv
          cases hv
      | ok r =>
          obtain ⟨s1, hE1, hpm1, hle1, hseg1, hr1⟩ := readToReg_spec dst cs hlive h1
          have hrun : CheckedCompilerM.run (compileStmtChecked L (.dealloc dst)) cs =
              compile.emit (CheckedCompilerM.run (readToReg L dst) cs) [.Dealloc r] := by
            simp only [compileStmtChecked, CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
              h1, CheckedCompilerM.value_lift, CheckedCompilerM.run_lift, CheckedCompilerM.run_pure,
              CompilerM.run_emitM]
          rw [hrun]
          have hi1 := CheckedCompilerM.incr (readToReg L dst) cs
          generalize CheckedCompilerM.run (readToReg L dst) cs = c1 at *
          have hseg := hseg1.snoc (i := .Dealloc r) hlive (fun x h => h.elim)
            (fun x hx => by simp [Instr.regs] at hx; rw [hx]; exact hr1)
            (fun _ _ h => by cases h) rfl (fun _ _ _ h => by cases h) (Nat.le_refl _) hle1
          have hL : LiveOf (compile.emit c1 [.Dealloc r]) = LiveOf cs := by
            rw [← LiveOf.eq hpm1]; rfl
          refine ⟨s1 ++ [.Dealloc r], hE1.trans (emit_state_incr _ _) (Emits.emit _ _),
            hi1.trans (emit_state_incr _ _), hle1, ?_, ?_, ?_, ?_⟩
          · rw [hL]; intro x hx; have := hlive x hx; simp only [compile.emit]; omega
          · rw [hL]; exact fun x h => Or.inl h
          · rw [hL]; exact fun x h => h
          · rw [hL]; exact hseg.code hlive
  | check discr vals member =>
      cases h1 : CheckedCompilerM.value (readToReg L discr) cs with
      | error e =>
          exfalso
          simp only [compileStmtChecked, guardRead, CheckedCompilerM.value_bind, h1] at hv
          cases hv
      | ok r =>
          obtain ⟨s1, hE1, hpm1, hle1, hseg1, hr1⟩ := readToReg_spec discr cs hlive h1
          have hrun : CheckedCompilerM.run (compileStmtChecked L (.check discr vals member)) cs =
              compile.emit (CheckedCompilerM.run (readToReg L discr) cs) [.Check r vals member] := by
            simp only [compileStmtChecked, guardRead, CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
              h1, CheckedCompilerM.value_lift, CheckedCompilerM.run_lift, CheckedCompilerM.run_pure,
              CompilerM.run_emitM]
          rw [hrun]
          have hi1 := CheckedCompilerM.incr (readToReg L discr) cs
          generalize CheckedCompilerM.run (readToReg L discr) cs = c1 at *
          have hseg := hseg1.snoc (i := .Check r vals member) hlive (fun x h => h.elim)
            (fun x hx => by simp [Instr.regs] at hx; rw [hx]; exact hr1)
            (fun _ _ h => by cases h) rfl (fun _ _ _ h => by cases h) (Nat.le_refl _) hle1
          have hL : LiveOf (compile.emit c1 [.Check r vals member]) = LiveOf cs := by
            rw [← LiveOf.eq hpm1]; rfl
          refine ⟨s1 ++ [.Check r vals member], hE1.trans (emit_state_incr _ _) (Emits.emit _ _),
            hi1.trans (emit_state_incr _ _), hle1, ?_, ?_, ?_, ?_⟩
          · rw [hL]; intro x hx; have := hlive x hx; simp only [compile.emit]; omega
          · rw [hL]; exact fun x h => Or.inl h
          · rw [hL]; exact fun x h => h
          · rw [hL]; exact hseg.code hlive
  | assignIf discr val dst rhs =>
      obtain ⟨E, hE⟩ := ensurePlaceRoot_spec (L := L) dst cs
      generalize hcsE : CompilerM.run (ensurePlaceRoot L dst) cs = csE at hE
      have hliveE : ∀ x, LiveOf csE x → regIdx x < csE.nextReg := fun x hx => by
        rcases hE.2.2.2.1 x hx with h | h
        · have := hlive x h; have := hE.2.2.1; omega
        · exact h.2
      cases hG : CheckedCompilerM.value (readToReg L discr) csE with
      | error e =>
          exfalso
          simp only [compileStmtChecked, guardRead, CheckedCompilerM.value_bind,
            CheckedCompilerM.value_lift, CheckedCompilerM.run_lift, hcsE, hG] at hv
          cases hv
      | ok g =>
      cases hB : CheckedCompilerM.value (compileAssignChecked L dst rhs)
          (reserveLabel (CheckedCompilerM.run (readToReg L discr) csE)) with
      | error e =>
          exfalso
          simp only [compileStmtChecked, guardRead, CheckedCompilerM.value_bind,
            CheckedCompilerM.value_lift, CheckedCompilerM.run_lift, hcsE, hG,
            skipIfAround_err g val _ _ hB] at hv
          cases hv
      | ok bOut =>
          obtain ⟨-, hrunS⟩ := skipIfAround_ok g val (compileAssignChecked L dst rhs) _ hB
          have hrun : CheckedCompilerM.run (compileStmtChecked L (.assignIf discr val dst rhs)) cs =
              CheckedCompilerM.run (emitSkipIfAround g val (compileAssignChecked L dst rhs))
                (CheckedCompilerM.run (readToReg L discr) csE) := by
            simp only [compileStmtChecked, guardRead, CheckedCompilerM.run_bind,
              CheckedCompilerM.value_bind, CheckedCompilerM.value_lift, CheckedCompilerM.run_lift,
              hcsE, hG, (skipIfAround_ok g val _ _ hB).1, CheckedCompilerM.run_pure]
          rw [hrun, hrunS]
          obtain ⟨sG, hEG, hpmG, hleG, hsegG, hgok⟩ := readToReg_spec discr csE hliveE hG
          have hiG := CheckedCompilerM.incr (readToReg L discr) csE
          generalize CheckedCompilerM.run (readToReg L discr) csE = csG at *
          have hlive1 : ∀ x, LiveOf (reserveLabel csG) x → regIdx x < (reserveLabel csG).nextReg := by
            have : LiveOf (reserveLabel csG) = LiveOf csE := by rw [← LiveOf.eq hpmG]; rfl
            rw [this]; intro x hx; have := hliveE x hx; simp only [reserveLabel]; omega
          obtain ⟨sB, hok⟩ := compileAssign_spec dst rhs (reserveLabel csG) hlive1 hB
          generalize CheckedCompilerM.run (compileAssignChecked L dst rhs) (reserveLabel csG) = csB
            at hok ⊢
          have hL1 : LiveOf (reserveLabel csG) = LiveOf csE := by rw [← LiveOf.eq hpmG]; rfl
          have hLf : LiveOf (patchLabel csB csG.nextLabel
              (.SkipIf g val (csB.nextLabel - (reserveLabel csG).nextLabel))) = LiveOf csB := rfl
          obtain ⟨hEE, hiE, hleE, hfE, hmE, hrE, hiE'⟩ := hE
          have hmB : ∀ x, LiveOf csE x → LiveOf csB x := fun x hx =>
            LiveOf.mono hok.incr x (by rw [hL1]; exact hx)
          have hfB : ∀ x, LiveOf csB x → LiveOf csE x ∨ csG.nextReg ≤ regIdx x := fun x hx => by
            rcases hok.fresh x hx with h | h
            · rw [hL1] at h; exact Or.inl h
            · exact Or.inr h
          -- the pieces as `Code` over the final locals
          have hcE : Code (LiveOf csB) cs.nextReg csE.nextReg E :=
            ⟨fun i hi x hx => Or.inl (hmB x (hrE i hi x hx).1), fun p r n hp => absurd hp
              (fun h => (hiE' _ (List.mem_of_getElem? h)).1 r n rfl),
             fun i hi => (hiE' i hi).2.2,
             fun p dr v skip hp => absurd rfl ((hiE' _ (List.mem_of_getElem? hp)).2.1 dr v skip)⟩
          have hcG : Code (LiveOf csB) csE.nextReg csG.nextReg sG :=
            (hsegG.code hliveE).mono_live hmB hfB
          have hcB : Code (LiveOf csB) csG.nextReg csB.nextReg sB := by
            have := hok.code; simpa [reserveLabel] using this
          have hgok' : LiveOf csB g ∨ (csE.nextReg ≤ regIdx g ∧ regIdx g < csG.nextReg ∧
              ∀ (p : Nat) r n, sG[p]? = some (Instr.Die r n) → r ≠ g) := by
            rcases hgok with h | h | h
            · exact Or.inl (hmB g h)
            · exact h.elim
            · exact Or.inr ⟨h.1, h.2.1, fun p r n hp hrg => h.2.2 ⟨n, by
                rw [← hrg]; exact List.mem_of_getElem? hp⟩⟩
          have hleB : csG.nextReg ≤ csB.nextReg := by
            have := hok.le; simpa [reserveLabel] using this
          have hcode := hcE.append (hcG.append_guard (v := val) hcB hgok' hleG hleB) hleE
            (by omega)
          have hltL : csG.nextLabel < csB.nextLabel := by
            have := hok.incr.nextLabel_le; simp only [reserveLabel] at this; omega
          have hpatch : StateIncr csG (patchLabel csB csG.nextLabel
              (.SkipIf g val (csB.nextLabel - (reserveLabel csG).nextLabel))) :=
            StateIncr.patchLabel ((reserveLabel_state_incr csG).trans hok.incr) (Nat.le_refl _)
              hltL _
          refine ⟨E ++ (sG ++ (.SkipIf g val sB.length :: sB)),
            hEE.trans (hiG.trans hpatch) (hEG.trans hpatch (Emits.skip hok.emits g val)),
            hiE.trans (hiG.trans hpatch), ?_, ?_, ?_, ?_, ?_⟩
          · show cs.nextReg ≤ csB.nextReg; omega
          · rw [hLf]; exact hok.live
          · rw [hLf]; intro x hx
            rcases hfB x hx with h | h
            · rcases hfE x h with h' | h'
              · exact Or.inl h'
              · exact Or.inr h'.1
            · exact Or.inr (by omega)
          · rw [hLf]; exact fun x hx => hmB x (hmE x hx)
          · rw [hLf]; exact hcode

theorem compileStmts_spec {Γ : Ctx} {L : LayEnv Γ} :
    ∀ (prog : obseq3.Prog Γ) (cs : CompilerState),
      (∀ x, LiveOf cs x → regIdx x < cs.nextReg) →
      ∀ {u : Unit}, CheckedCompilerM.value (compileStmtsChecked L prog) cs = .ok u →
      ∃ seg, StmtSpec cs (CheckedCompilerM.run (compileStmtsChecked L prog) cs) seg
  | [], cs, hlive, _, _ => by
      refine ⟨[], ?_⟩
      simp only [compileStmtsChecked, CheckedCompilerM.run_pure]
      exact ⟨Emits.nil cs, StateIncr.refl cs, Nat.le_refl _, hlive, fun x h => Or.inl h,
        fun x h => h, Code.nil _ _ _⟩
  | stmt :: rest, cs, hlive, u, hv => by
      cases h1 : CheckedCompilerM.value (compileStmtChecked L stmt) cs with
      | error e =>
          exfalso
          simp only [compileStmtsChecked, CheckedCompilerM.value_bind, h1] at hv
          cases hv
      | ok out =>
          obtain ⟨s1, hs1⟩ := compileStmt_spec stmt cs hlive h1
          simp only [compileStmtsChecked, CheckedCompilerM.value_bind, h1] at hv
          obtain ⟨s2, hs2⟩ := compileStmts_spec rest _ hs1.2.2.2.1 hv
          refine ⟨s1 ++ s2, ?_⟩
          simp only [compileStmtsChecked, CheckedCompilerM.run_bind, CheckedCompilerM.value_bind, h1]
          exact hs1.seq hs2

/-- A whole program laid down as one `Code` segment from label 0 is a
    route-bracket program. -/
theorem Code.routeProg {live : Register → Prop} {hi : Nat} {seg : List Instr}
    (h : Code live 0 hi seg) {prog : oseair.Prog} (hp : ∀ l, prog l = seg[l]?) :
    RouteProg prog := by
  refine ⟨fun d r n hd => ?_, fun l lay vals ptr hl v hv b o e s t he => ?_⟩
  · rw [hp] at hd
    obtain ⟨⟨h2, ⟨k, base, off, hk, hb⟩, ⟨i, hi, ht⟩, hm⟩, -, -, -⟩ := h.dies d r n hd
    refine ⟨d - 2, by omega, ⟨⟨k, base, off, hk, by rw [hp]; exact hb⟩,
      ⟨i, by rw [hp, show d - 2 + 1 = d - 1 by omega]; exact hi, ht⟩,
      by rw [hp, show d - 2 + 2 = d by omega]; exact hd,
      fun l j hl hr => by rw [hp] at hl; have := hm l j hl hr; omega,
      fun l dr w skip hl => by
        rw [hp] at hl
        have := (h.skips l dr w skip hl).2 d r n hd
        omega⟩⟩
  · rw [hp] at hl
    have := h.cst _ (List.mem_of_getElem? hl)
    simp only [Instr.noPtrConst, Bool.not_eq_true', List.any_eq_false] at this
    have := this v hv
    rw [he] at this
    simp [Val.isPtr] at this

/-- Every compiled program is a route-bracket program: the compiler always
    passes the check. -/
theorem compiled_routeProg {Γ : Ctx} {L : LayEnv Γ} {P : obseq3.Prog Γ}
    {Q : compile.TargetProg} (hc : compile.compileProg L P = .ok Q) : RouteProg Q := by
  have hnone := compileProg_code_none hc
  unfold compile.compileProg at hc
  split at hc
  · rename_i u hv
    cases hc
    obtain ⟨seg, hE, -, -, -, -, -, hcode⟩ :=
      compileStmts_spec P (initialState Γ) (fun x ⟨idx, τ, hx⟩ => by
        simp [initialState] at hx) hv
    refine hcode.routeProg fun l => ?_
    by_cases hl : l < seg.length
    · have := hE.2 l hl
      have h0 : (initialState Γ).nextLabel + l = l := by simp [initialState]
      rw [h0] at this
      rw [this, List.getElem?_eq_getElem hl]
    · rw [List.getElem?_eq_none (by omega)]
      apply hnone
      unfold compile.emittedLabels
      rw [hE.1]; simp [initialState]; omega
  · cases hc

/-- Die elision for compiled code, unconditionally: every compiled program
    reaches the same verdict on OSEA-IR and OSEA-IR_B at every step count. -/
theorem compiled_die_elision {Γ : Ctx} (L : LayEnv Γ) (P : obseq3.Prog Γ)
    {Q : compile.TargetProg} (hc : compile.compileProg L P = .ok Q) (n : Nat) :
    (∃ s, runN MSB n (oseair.State.initial MSB) Q = .Ok s) ↔
      (∃ s, runN MSB_B n (oseair.State.initial MSB_B) Q = .Ok s) :=
  die_elision_iff Q (compiled_routeProg hc) n

end obseq3.proof
