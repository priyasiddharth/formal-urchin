import obseq3.proof.die_back_run
import obseq3.compile

/-!
# Die elision, backward: the decidable check

`routeOK_sound`: a program that passes `oseair.routeOK` over its emitted
labels, and has nothing beyond them, is a `RouteProg`. A compiled program
has nothing beyond its emitted labels (`compileProg_code_none`), so
`compiled_die_elision_iff` holds of every compiled program the check
accepts — the conformance runner and the witness corpus run it on all of
theirs.
-/

namespace obseq3.proof

open obseq3 obseq3.bytes obseq3.oseair

theorem all_range_true {f : Nat → Bool} {len : Nat} (h : (List.range len).all f = true)
    {l : Nat} (hl : l < len) : f l = true :=
  List.all_eq_true.mp h l (List.mem_range.mpr hl)

theorem routeBorrowOf_true {r : Register} {n : Nat} {i : Instr}
    (h : i.routeBorrowOf r n = true) :
    ∃ k base off, PushKind k ∧ i = .Assgn r (.Borrow k false [] (some n) base off) := by
  unfold Instr.routeBorrowOf at h
  split at h
  · rename_i r' k n' base off
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨rfl, rfl⟩, hk⟩ := h
    refine ⟨k, base, off, ?_, rfl⟩
    cases k with
    | Raw m => cases m <;> simp_all [RefKind.pushes, PushKind]
    | _ => simp_all [RefKind.pushes, PushKind]
  · cases h

theorem routeOK_sound {prog : Nat → Option Instr} {len : Nat} (h : routeOK prog len = true)
    (hnone : ∀ l, len ≤ l → prog l = none) : RouteProg prog := by
  simp only [routeOK, Bool.and_eq_true] at h
  obtain ⟨hb, hc⟩ := h
  have hlt : ∀ {l i}, prog l = some i → l < len := fun {l i} hl =>
    Nat.lt_of_not_le fun hge => by rw [hnone l hge] at hl; cases hl
  refine ⟨fun d r n hd => ?_, fun l lay vals ptr hl v hv b o e s t he => ?_⟩
  · have hbd := all_range_true hb (hlt hd)
    simp only [bracketAt, hd, Bool.and_eq_true, decide_eq_true_eq] at hbd
    obtain ⟨⟨⟨h2, hbor⟩, hthr⟩, honly⟩ := hbd
    refine ⟨d - 2, by omega, ?_, ?_, ?_, ?_⟩
    · cases hp : prog (d - 2) with
      | none => rw [hp] at hbor; cases hbor
      | some i =>
          rw [hp] at hbor
          obtain ⟨k, base, off, hk, rfl⟩ := routeBorrowOf_true hbor
          exact ⟨k, base, off, hk, rfl⟩
    · cases hp : prog (d - 1) with
      | none => rw [hp] at hthr; cases hthr
      | some i =>
          rw [hp] at hthr
          exact ⟨i, by rw [show d - 2 + 1 = d - 1 by omega]; exact hp, hthr⟩
    · rw [show d - 2 + 2 = d by omega]; exact hd
    · intro l i hl hr
      have := all_range_true honly (hlt hl)
      rw [hl] at this
      simp only [Option.map_some, Option.getD_some, Bool.or_eq_true, Bool.and_eq_true,
        decide_eq_true_eq, Bool.not_eq_true'] at this
      rcases this with ⟨h1, h2⟩ | hc'
      · exact ⟨h1, by omega⟩
      · exfalso
        have : i.regs.contains r = true := by simpa using hr
        rw [this] at hc'; cases hc'
  · have := all_range_true hc (hlt hl)
    rw [hl] at this
    simp only [Option.map_some, Option.getD_some, Instr.noPtrConst, Bool.not_eq_true',
      List.any_eq_false] at this
    have := this v hv
    rw [he] at this
    simp [Val.isPtr] at this

/-- A compiled program has nothing beyond its emitted labels. -/
theorem compileProg_code_none {Γ : Ctx} {L : mirlite.LayEnv Γ} {P : obseq3.Prog Γ}
    {Q : compile.TargetProg} (hc : compile.compileProg L P = .ok Q) :
    ∀ l, compile.emittedLabels L P ≤ l → Q l = none := by
  unfold compile.compileProg at hc
  split at hc
  · cases hc
    exact (compile.CheckedCompilerM.incr _ _).code_none (fun _ _ => rfl)
  · cases hc

/-- Die elision for compiled code: a compiled program the route-bracket
    check accepts reaches the same verdict on OSEA-IR and OSEA-IR_B, at
    every step count. -/
theorem compiled_die_elision_iff {Γ : Ctx} (L : mirlite.LayEnv Γ) (P : obseq3.Prog Γ)
    {Q : compile.TargetProg} (hc : compile.compileProg L P = .ok Q)
    (hok : routeOK Q (compile.emittedLabels L P) = true) (n : Nat) :
    (∃ s, runN MSB n (oseair.State.initial MSB) Q = .Ok s) ↔
      (∃ s, runN MSB_B n (oseair.State.initial MSB_B) Q = .Ok s) :=
  die_elision_iff Q (routeOK_sound hok (compileProg_code_none hc)) n

end obseq3.proof
