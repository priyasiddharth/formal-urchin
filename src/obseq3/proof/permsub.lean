import obseq3.proof.cellsub
import obseq3.proof.permsim_dealloc

/-!
# Die elision, per permission state

`PermSub A B`: B is A's permission state with every `Die` skipped. The
counters, protector frames, exposed and weakly-protected sets agree; B has
retired nothing; and every cell's B-stack is A's with died items (the
EXTRAS) interleaved (`CellRel`). An extra's tag is retired in A and
unprotected (`Extra A`); a retired tag is never exposed (`disj`, from the
`sb_die`/`sb_expose` checks), so a wildcard never resolves to an extra.

Every range operation that succeeds on A succeeds on B and keeps the
relation (`sb_read_sub`, …); A's `die` keeps it with B unchanged
(`sb_die_sub`).
-/

namespace obseq3.proof

open obseq3

/-- The tags B may still carry after A died them. -/
def Extra (A : AccessPerms) (t : Tag) : Prop :=
  t ∈ A.retired ∧ isProtectedIn A.protFrames t = false

/-- A cell relation lifted to stack maps, address by address (the shape of
    `StackMapSim`). -/
def StackMapRel (R : BorrowStack → BorrowStack → Prop) (x y : SB) : Prop :=
  ∀ a : Word,
    match SB.find? x a, SB.find? y a with
    | none, none => True
    | some s, some s' => R s s'
    | _, _ => False

namespace StackMapRel

variable {R R' : BorrowStack → BorrowStack → Prop}

theorem find?_some {x y : SB} (h : StackMapRel R x y) {a : Word} {s : BorrowStack}
    (hf : SB.find? x a = some s) : ∃ s', SB.find? y a = some s' ∧ R s s' := by
  have := h a
  rw [hf] at this
  cases hy : SB.find? y a with
  | none => rw [hy] at this; exact this.elim
  | some s' => rw [hy] at this; exact ⟨s', rfl, this⟩

theorem find?_none {x y : SB} (h : StackMapRel R x y) {a : Word}
    (hf : SB.find? x a = none) : SB.find? y a = none := by
  have := h a
  rw [hf] at this
  cases hy : SB.find? y a with
  | none => rfl
  | some s' => rw [hy] at this; exact this.elim

theorem mono {x y : SB} (h : StackMapRel R x y) (hR : ∀ s s', R s s' → R' s s') :
    StackMapRel R' x y := by
  intro a
  have := h a
  revert this
  cases SB.find? x a <;> cases SB.find? y a <;> simp only [imp_self] <;>
    first | exact id | exact hR _ _

theorem set {x y : SB} (h : StackMapRel R x y) {a : Word} {v v' : BorrowStack} (hv : R v v') :
    StackMapRel R (SB.set x a v) (SB.set y a v') := by
  intro b
  by_cases hb : b = a
  · subst hb
    rw [SB.find?_set_self, SB.find?_set_self]
    exact hv
  · rw [SB.find?_set_ne _ hb, SB.find?_set_ne _ hb]
    exact h b

theorem setChain_chain {x y : SB} {W W' : Nat → BorrowStack} {addr : Word} {i lenB : Nat}
    (h : StackMapRel R x y) (hW : ∀ j, i ≤ j → j < lenB → R (W j) (W' j)) :
    StackMapRel R (setChain x (chain W addr i lenB)) (setChain y (chain W' addr i lenB)) := by
  by_cases hi : i < lenB
  · rw [chain_step hi, chain_step hi, setChain, setChain]
    exact setChain_chain (h.set (hW i (Nat.le_refl i) hi))
      (fun j h1 h2 => hW j (by omega) h2)
  · rw [chain_stop hi, chain_stop hi]
    exact h
  termination_by lenB - i

theorem filter_cell {x y : SB} (h : StackMapRel R x y) (a : Word) :
    StackMapRel R (x.filter (fun (e : Word × BorrowStack) => e.1 != a))
      (y.filter (fun (e : Word × BorrowStack) => e.1 != a)) := by
  intro b
  by_cases hb : b = a
  · subst hb
    rw [SB.find?_filter_self, SB.find?_filter_self]
    trivial
  · rw [SB.find?_filter_ne hb, SB.find?_filter_ne hb]
    exact h b

end StackMapRel

/-- B is A with every `Die` skipped. -/
structure PermSub (A B : AccessPerms) : Prop where
  stacks : StackMapRel (CellRel (Extra A) A.NextTag) A.StackMap B.StackMap
  next : B.NextTag = A.NextTag
  prot : B.protFrames = A.protFrames
  exp : B.exposed = A.exposed
  wk : B.weakProt = A.weakProt
  ret : B.retired = []
  disj : ∀ t ∈ A.retired, A.exposed.contains t = false

theorem PermSub.hEp {A B : AccessPerms} (_ : PermSub A B) :
    ∀ t, Extra A t → isProtectedIn A.protFrames t = false := fun _ h => h.2

theorem PermSub.hEx {A B : AccessPerms} (hs : PermSub A B) :
    ∀ t, Extra A t → A.exposed.contains t = false := fun t h => hs.disj t h.1

theorem PermSub.initial : PermSub AccessPerms.init AccessPerms.init :=
  ⟨fun a => by simp [AccessPerms.init, SB.find?], rfl, rfl, rfl, rfl, rfl,
    fun t h => by simp [AccessPerms.init] at h⟩

/-! ## The content-driven fold, lifted -/

/-- A cell transport for a content-driven op lifts to the whole fold: A's
    success gives B's, with related per-cell results. -/
theorem foldCells_sub
    {opA opB : AccessPerms → Word → Except String AccessPerms}
    {CA CB : Word → BorrowStack → Except String BorrowStack}
    {mA mB : Word → String}
    {R R' : BorrowStack → BorrowStack → Prop}
    {A B A' : AccessPerms} {addr : Word} {lenB : Nat}
    (hA_op : ∀ ap a, ap.protFrames = A.protFrames → ap.exposed = A.exposed →
      ap.NextTag = A.NextTag →
      opA ap a =
        match SB.find? ap.StackMap a with
        | none => .error (mA a)
        | some stack =>
          match CA a stack with
          | .error e => .error e
          | .ok v => .ok { ap with StackMap := SB.set ap.StackMap a v })
    (hB_op : ∀ ap a, ap.protFrames = B.protFrames → ap.exposed = B.exposed →
      ap.NextTag = B.NextTag →
      opB ap a =
        match SB.find? ap.StackMap a with
        | none => .error (mB a)
        | some stack =>
          match CB a stack with
          | .error e => .error e
          | .ok v => .ok { ap with StackMap := SB.set ap.StackMap a v })
    (hC : ∀ a sa sb wa, R sa sb → CA a sa = .ok wa → ∃ wb, CB a sb = .ok wb ∧ R' wa wb)
    (hrel : StackMapRel R A.StackMap B.StackMap)
    (h : foldCells opA A addr lenB = .ok A') :
    ∃ W W' : Nat → BorrowStack,
      foldCells opB B addr lenB =
        .ok { B with StackMap := setChain B.StackMap (chain W' addr 0 lenB) } ∧
      A' = { A with StackMap := setChain A.StackMap (chain W addr 0 lenB) } ∧
      ∀ j, j < lenB → R' (W j) (W' j) := by
  have h0 : foldCells opA A (addr + 0) lenB = .ok A' := h
  obtain ⟨V, W, h_cells, hA'⟩ :=
    foldCells_ok_inv (C := CA) (msgNone := mA) hA_op lenB 0 A A' rfl rfl rfl h0
  have h_pkg : ∀ j, ∃ vj, ∃ wj, j < lenB →
      SB.find? B.StackMap (addr + j) = some vj ∧ CB (addr + j) vj = .ok wj ∧
        R' (W j) wj := by
    intro j
    by_cases hj : j < lenB
    · have hc := h_cells j (Nat.zero_le j) (by omega)
      obtain ⟨s', hf', hr⟩ := hrel.find?_some hc.1
      obtain ⟨w', hw', hR'⟩ := hC _ _ _ _ hr hc.2
      exact ⟨s', w', fun _ => ⟨hf', hw', hR'⟩⟩
    · exact ⟨[], [], fun h => absurd h hj⟩
  have h_pkg' := fun j (hj : j < lenB) => (h_pkg j).choose_spec.choose_spec hj
  have hB := foldCells_ok_of_cells (C := CB) (msgNone := mB) hB_op lenB 0 B
    (fun j => (h_pkg j).choose) (fun j => (h_pkg j).choose_spec.choose) rfl rfl rfl
    (fun j _ h2 => (h_pkg' j (by omega)).1) (fun j _ h2 => (h_pkg' j (by omega)).2.1)
  rw [Nat.zero_add] at hB hA'
  exact ⟨W, _, hB, hA', fun j hj => (h_pkg' j hj).2.2⟩

/-! ## Read and write -/

theorem sb_write_sub {A B A' : AccessPerms} {addr : Word} {lenB : Nat} {t : Tag}
    (hs : PermSub A B) (h : sb_write A addr lenB t = .ok A') :
    ∃ B', sb_write B addr lenB t = .ok B' ∧ PermSub A' B' := by
  obtain ⟨W, W', hB, rfl, hW⟩ := foldCells_sub
    (CA := fun a stack => writeCellContent A.protFrames A.exposed a t stack)
    (CB := fun a stack => writeCellContent B.protFrames B.exposed a t stack)
    (R' := CellRel (Extra A) A.NextTag)
    (fun ap a h_pf h_ex _ => writeCell_content_form t ap a h_pf h_ex)
    (fun ap a h_pf h_ex _ => writeCell_content_form t ap a h_pf h_ex)
    (fun a sa sb wa hr hA => by
      rw [hs.prot, hs.exp]; exact writeCellContent_cell hs.hEp hs.hEx hr hA)
    hs.stacks h
  exact ⟨_, hB, ⟨hs.stacks.setChain_chain fun j _ hj => hW j hj, hs.next, hs.prot, hs.exp,
    hs.wk, hs.ret, hs.disj⟩⟩

theorem sb_read_sub {A B A' : AccessPerms} {addr : Word} {lenB : Nat} {t : Tag}
    (hs : PermSub A B) (h : sb_read A addr lenB t = .ok A') :
    ∃ B', sb_read B addr lenB t = .ok B' ∧ PermSub A' B' := by
  obtain ⟨W, W', hB, rfl, hW⟩ := foldCells_sub
    (CA := fun a stack => readCellContent A.protFrames A.exposed a t stack)
    (CB := fun a stack => readCellContent B.protFrames B.exposed a t stack)
    (R' := CellRel (Extra A) A.NextTag)
    (fun ap a h_pf h_ex _ => readCell_content_form t ap a h_pf h_ex)
    (fun ap a h_pf h_ex _ => readCell_content_form t ap a h_pf h_ex)
    (fun a sa sb wa hr hA => by
      rw [hs.prot, hs.exp]; exact readCellContent_cell hs.hEp hs.hEx hr hA)
    hs.stacks h
  exact ⟨_, hB, ⟨hs.stacks.setChain_chain fun j _ hj => hW j hj, hs.next, hs.prot, hs.exp,
    hs.wk, hs.ret, hs.disj⟩⟩

/-! ## Retag -/

/-- `sb_ref`'s protector registration, as a function of the frames. -/
def regProt (N : Tag) (kind : RefKind) (prot : Bool) (pf : List (List Tag)) (wk : List Tag) :
    Except String (List (List Tag) × List Tag) :=
  if prot then
    match pf with
    | [] => .error "sb-ref: protected retag outside any protector frame"
    | frame :: rest => .ok ((N :: frame) :: rest, if kind = .BoxMut then N :: wk else wk)
  else .ok (pf, wk)

theorem sb_ref_eq (ap : AccessPerms) (addr : Word) (lenB : Nat) (tag : Tag) (kind : RefKind)
    (prot : Bool) (mask : List Bool) :
    sb_ref ap addr lenB tag kind prot mask =
      match foldCellsIdx (refCellOp tag kind ap.NextTag mask)
          { ap with NextTag := ap.NextTag + 1 } addr 0 lenB with
      | .error e => .error e
      | .ok apR =>
        match regProt ap.NextTag kind prot apR.protFrames apR.weakProt with
        | .error e => .error e
        | .ok (pf, wk) => .ok ({ apR with protFrames := pf, weakProt := wk }, ap.NextTag) := by
  simp only [sb_ref, freshTag, bind, Except.bind, pure, Except.pure]
  cases hf : foldCellsIdx (refCellOp tag kind ap.NextTag mask)
      { ap with NextTag := ap.NextTag + 1 } addr 0 lenB with
  | error e => rfl
  | ok apR =>
    simp only
    cases prot with
    | false => rfl
    | true =>
        simp only [regProt, if_true]
        cases apR.protFrames with
        | nil => rfl
        | cons f r => by_cases hk : kind = .BoxMut <;> simp [hk]

/-- Registration protects only the fresh tag. -/
theorem regProt_prot {N : Tag} {kind : RefKind} {prot : Bool} {pf : List (List Tag)}
    {wk : List Tag} {pf' : List (List Tag)} {wk' : List Tag}
    (h : regProt N kind prot pf wk = .ok (pf', wk')) {t : Tag} (ht : t ≠ N)
    (hp : isProtectedIn pf t = false) : isProtectedIn pf' t = false := by
  unfold regProt at h
  cases prot with
  | false => simp only [Bool.false_eq_true, if_false, Except.ok.injEq, Prod.mk.injEq] at h; rw [← h.1]; exact hp
  | true =>
      simp only [if_true] at h
      cases pf with
      | nil => cases h
      | cons f r =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          rw [← h.1]
          simp only [isProtectedIn, List.any_cons, List.contains_cons] at hp ⊢
          simp only [Bool.or_eq_false_iff] at hp ⊢
          refine ⟨⟨?_, hp.1⟩, hp.2⟩
          simpa using fun h' => ht h'

/-- The cell relation with the extras' bound made explicit. -/
theorem CellRel.restrict {E : Tag → Prop} {N : Tag} {sa sb : BorrowStack}
    (h : CellRel E N sa sb) : CellRel (fun t => E t ∧ t < N) N sa sb := by
  have hbd := h.2.2.1
  exact h.mono (fun x hx he => ⟨he, hbd x hx⟩) (Nat.le_refl _)

theorem sb_ref_sub {A B A' : AccessPerms} {addr : Word} {lenB : Nat} {t : Tag}
    {kind : RefKind} {prot : Bool} {mask : List Bool} {n : Tag}
    (hs : PermSub A B) (h : sb_ref A addr lenB t kind prot mask = .ok (A', n)) :
    ∃ B', sb_ref B addr lenB t kind prot mask = .ok (B', n) ∧ PermSub A' B' := by
  rw [sb_ref_eq] at h
  rw [sb_ref_eq]
  split at h
  · cases h
  rename_i apR hgo
  obtain ⟨W, h_cells, rfl⟩ :=
    foldCellsIdx_ok_inv
      (op := refCellOp t kind A.NextTag mask)
      (C := fun j v? => refCellStep A.protFrames A.exposed (addr + j) t kind A.NextTag mask j v?)
      (P := A.protFrames) (E := A.exposed) (N := A.NextTag + 1)
      (refCellOp_content_form (addr := addr) t kind A.NextTag mask)
      { A with NextTag := A.NextTag + 1 } _ rfl rfl rfl hgo
  let E0 : Tag → Prop := fun t => Extra A t ∧ t < A.NextTag
  have hEp0 : ∀ t, E0 t → isProtectedIn A.protFrames t = false := fun _ h => h.1.2
  have hEx0 : ∀ t, E0 t → A.exposed.contains t = false := fun t h => hs.disj t h.1.1
  have hrel0 : StackMapRel (CellRel E0 A.NextTag) A.StackMap B.StackMap :=
    hs.stacks.mono fun _ _ h => h.restrict
  have h_pkg : ∀ j, ∃ wj, j < lenB →
      refCellStep B.protFrames B.exposed (addr + j) t kind B.NextTag mask j
          (SB.find? B.StackMap (addr + j)) = .ok wj ∧
        CellRel E0 (A.NextTag + 1) (W j) wj := by
    intro j
    by_cases hj : j < lenB
    · obtain ⟨vj, hf, hc⟩ := refCellStep_ok_inv (h_cells j (Nat.zero_le j) hj)
      obtain ⟨s', hf', hr⟩ := hrel0.find?_some hf
      obtain ⟨wb, hwb, hR⟩ := refCellContent_cell hEp0 hEx0 hr hc
      refine ⟨wb, fun _ => ⟨?_, hR⟩⟩
      rw [hf', hs.prot, hs.exp, hs.next]
      exact hwb
    · exact ⟨[], fun h => absurd h hj⟩
  obtain ⟨W', h_W'⟩ : ∃ W' : Nat → BorrowStack, ∀ j, j < lenB →
      refCellStep B.protFrames B.exposed (addr + j) t kind B.NextTag mask j
          (SB.find? B.StackMap (addr + j)) = .ok (W' j) ∧
        CellRel E0 (A.NextTag + 1) (W j) (W' j) :=
    ⟨fun j => (h_pkg j).choose, fun j hj => (h_pkg j).choose_spec hj⟩
  have h_goB :=
    foldCellsIdx_ok_of_cells
      (op := refCellOp t kind B.NextTag mask)
      (C := fun j v? => refCellStep B.protFrames B.exposed (addr + j) t kind B.NextTag mask j v?)
      (P := B.protFrames) (E := B.exposed) (N := B.NextTag + 1)
      (refCellOp_content_form (addr := addr) t kind B.NextTag mask)
      (i := 0) (lenB := lenB)
      { B with NextTag := B.NextTag + 1 } W' rfl rfl rfl
      (fun j _ h2 => (h_W' j h2).1)
  rw [h_goB]
  simp only at h ⊢
  split at h
  · cases h
  rename_i pf' wk' hreg
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rw [hs.prot, hs.wk, hs.next, hreg]
  refine ⟨_, rfl, ⟨?_, by simp, rfl, hs.exp, rfl, hs.ret, hs.disj⟩⟩
  have hm : StackMapRel (CellRel E0 (A.NextTag + 1))
      (setChain A.StackMap (chain W addr 0 lenB)) (setChain B.StackMap (chain W' addr 0 lenB)) :=
    (hrel0.mono fun _ _ h => h.mono (fun _ _ h => h) (Nat.le_succ _)).setChain_chain
      fun j _ hj => (h_W' j hj).2
  exact hm.mono fun _ _ h => h.mono (fun x _ he =>
    ⟨he.1.1, regProt_prot hreg (Nat.ne_of_lt he.2) he.1.2⟩) (Nat.le_refl _)

/-! ## Allocation -/

theorem sb_own_eq (ap : AccessPerms) (addr : Word) (lenB : Nat) :
    sb_own ap addr lenB =
      match foldCells (fun q a => ownCell q a ap.NextTag) { ap with NextTag := ap.NextTag + 1 }
          addr lenB with
      | .error e => .error e
      | .ok ap' => .ok (ap', ap.NextTag) := by
  simp only [sb_own, freshTag, bind, Except.bind, pure, Except.pure]
  cases hf : foldCells (fun q a => ownCell q a ap.NextTag) { ap with NextTag := ap.NextTag + 1 }
    addr lenB <;> rfl

/-- A's allocation finds the cell absent (a present A-stack is never
    empty), so B's is absent too. -/
theorem ownCellStep_sub {E : Tag → Prop} {N T : Tag} {x y : SB} {a b : Word} {w : BorrowStack}
    (hrel : StackMapRel (CellRel E N) x y) (h : ownCellStep a T (SB.find? x b) = .ok w) :
    ownCellStep a T (SB.find? y b) = .ok w ∧ w = [.Own T] := by
  cases hf : SB.find? x b with
  | none =>
      rw [hf] at h
      rw [hrel.find?_none hf]
      simp only [ownCellStep, Except.ok.injEq] at h ⊢
      exact ⟨h, h.symm⟩
  | some s =>
      rw [hf] at h
      obtain ⟨s', -, hr⟩ := hrel.find?_some hf
      obtain ⟨-, -, -, t0, hl⟩ := hr
      cases s with
      | nil => simp at hl
      | cons k r => simp [ownCellStep] at h

theorem sb_own_sub {A B A' : AccessPerms} {addr : Word} {lenB : Nat} {n : Tag}
    (hs : PermSub A B) (h : sb_own A addr lenB = .ok (A', n)) :
    ∃ B', sb_own B addr lenB = .ok (B', n) ∧ PermSub A' B' := by
  rw [sb_own_eq] at h
  rw [sb_own_eq, hs.next]
  split at h
  · cases h
  rename_i apR hgo
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hgo0 : foldCells (fun ap a => ownCell ap a A.NextTag) { A with NextTag := A.NextTag + 1 }
      (addr + 0) lenB = .ok apR := hgo
  rw [foldCells_ok_iff_foldCellsIdx_ok] at hgo0
  obtain ⟨W, h_cells, rfl⟩ :=
    foldCellsIdx_ok_inv (op := fun ap a _ => ownCell ap a A.NextTag)
      (C := fun i o => ownCellStep (addr + i) A.NextTag o)
      (P := A.protFrames) (E := A.exposed) (N := A.NextTag + 1)
      (fun ap i _ _ _ => ownCell_content_form A.NextTag ap (addr + i))
      { A with NextTag := A.NextTag + 1 } _ rfl rfl rfl hgo0
  have hcB := fun j h1 h2 => ownCellStep_sub hs.stacks (h_cells j h1 h2)
  have hgoB :=
    foldCellsIdx_ok_of_cells (op := fun ap a _ => ownCell ap a A.NextTag)
      (C := fun i o => ownCellStep (addr + i) A.NextTag o)
      (P := B.protFrames) (E := B.exposed) (N := A.NextTag + 1)
      (fun ap i _ _ _ => ownCell_content_form A.NextTag ap (addr + i))
      (i := 0) (lenB := 0 + lenB) { B with NextTag := A.NextTag + 1 } W rfl rfl rfl
      (fun j h1 h2 => (hcB j h1 h2).1)
  have hgoB' := (foldCells_ok_iff_foldCellsIdx_ok _ addr lenB 0 _ _).mpr hgoB
  rw [Nat.zero_add] at hgoB'
  rw [show foldCells (fun ap a => ownCell ap a A.NextTag) { B with NextTag := A.NextTag + 1 }
      addr lenB = _ from hgoB']
  refine ⟨_, rfl, ⟨?_, rfl, hs.prot, hs.exp, hs.wk, hs.ret, hs.disj⟩⟩
  simp only [Nat.zero_add]
  exact (hs.stacks.mono fun _ _ h => h.mono (fun _ _ h => h) (Nat.le_succ _)).setChain_chain
    fun j h1 h2 => by rw [(hcB j h1 (by omega)).2]; exact own_cell _

/-! ## Deallocation -/

/-- An extra never blocks a deallocation: it is unprotected. -/
theorem strongProt_extra {pf : List (List Tag)} {wk : List Tag} {k : Item}
    (hp : isProtectedIn pf k.tag = false) : strongProt pf wk k = false := by
  simp only [strongProt, firstProtectedIn_singleton_isSome, hp, Bool.and_false,
    Bool.false_and]

theorem sb_dealloc_sub {tag : Tag} :
    ∀ (lenB : Nat) (addr : Word) {A B A' : AccessPerms},
      PermSub A B → sb_dealloc A addr lenB tag = .ok A' →
      ∃ B', sb_dealloc B addr lenB tag = .ok B' ∧ PermSub A' B' := by
  intro lenB
  induction lenB with
  | zero =>
      intro addr A B A' hs h
      rw [sb_dealloc_eq] at h
      simp only [foldCells] at h
      cases h
      exact ⟨B, rfl, hs⟩
  | succ n ih =>
      intro addr A B A' hs h
      rw [sb_dealloc_eq] at h ⊢
      simp only [foldCells] at h
      split at h
      · simp at h
      rename_i A1 h_cell
      obtain ⟨stack, ab, item, bl, h_find, h_split, h_gw, h_fp, h_sp, rfl⟩ :=
        deallocCellOp_ok_inv h_cell
      obtain ⟨s', h_find', hr⟩ := hs.stacks.find?_some h_find
      obtain ⟨⟨b, hsub⟩, hnd, -, -⟩ := hr
      obtain ⟨ab', bb', h_split', ⟨b1, h1, -⟩, ⟨b2, h2, -⟩⟩ := splitStack_sub hsub hnd h_split
      have h_fp' : firstProtectedIn B.protFrames ab' = none := by
        rw [hs.prot]
        exact firstProtectedIn_none_sub hs.hEp (fun k hk => h1.mem_right hk) h_fp
      have h_sp' : (item :: bb').find? (strongProt B.protFrames B.weakProt) = none := by
        rw [hs.prot, hs.wk]
        rw [List.find?_eq_none] at h_sp ⊢
        intro k hk
        rcases List.mem_cons.mp hk with rfl | hk
        · exact h_sp _ List.mem_cons_self
        · rcases h2.mem_right hk with hk | he
          · exact h_sp _ (List.mem_cons_of_mem _ hk)
          · simp [strongProt_extra (wk := A.weakProt) he.2]
      have hs1 : PermSub { A with StackMap := A.StackMap.filter (fun (x, _) => x != addr) }
          { B with StackMap := B.StackMap.filter (fun (x, _) => x != addr) } :=
        ⟨hs.stacks.filter_cell addr, hs.next, hs.prot, hs.exp, hs.wk, hs.ret, hs.disj⟩
      obtain ⟨B', h_tgt, hs'⟩ := ih (addr + 1) hs1 h
      refine ⟨B', ?_, hs'⟩
      simp only [foldCells]
      rw [deallocCellOp_ok_eq B addr tag h_find' h_split' h_gw h_fp' h_sp']
      rw [sb_dealloc_eq] at h_tgt
      exact h_tgt

/-! ## Die, expose, frames -/

/-- A's `die` keeps the relation with B unchanged: each popped top item
    stays in B, now an extra. -/
theorem sb_die_sub {A B A' : AccessPerms} {addr : Word} {lenB : Nat} {tag : Tag}
    (hs : PermSub A B) (h : sb_die A addr lenB tag = .ok A') : PermSub A' B := by
  obtain ⟨h_ex, q, h_fold, rfl⟩ := sb_die_ok_inv h
  have h0 : foldCells (dieCellOp tag) A (addr + 0) lenB = .ok q := h_fold
  obtain ⟨V, W, h_cells, rfl⟩ :=
    foldCells_ok_inv (C := fun _ stack => dieCellContent A.protFrames tag stack)
      (msgNone := fun a => s!"sb-die: no borrow stack at address {a}")
      (P := A.protFrames) (E := A.exposed) (N := A.NextTag)
      (fun ap a h_pf h_ex _ => die_content_form tag ap a h_pf h_ex)
      lenB 0 A q rfl rfl rfl h0
  -- the new extras' predicate
  let A' : AccessPerms := { A with StackMap := setChain A.StackMap (chain W addr 0 (0 + lenB)),
                                   retired := tag :: A.retired }
  have hE : ∀ t, Extra A t → Extra A' t := fun t h => ⟨List.mem_cons_of_mem _ h.1, h.2⟩
  refine ⟨?_, hs.next, hs.prot, hs.exp, hs.wk, hs.ret, ?_⟩
  · intro a
    show match SB.find? (setChain A.StackMap (chain W addr 0 (0 + lenB))) a, SB.find? B.StackMap a with
      | none, none => True | some s, some s' => CellRel (Extra A') A.NextTag s s' | _, _ => False
    by_cases hm : a ∈ keysOf (chain W addr 0 (0 + lenB))
    · obtain ⟨j, h1, h2, rfl⟩ := mem_keysOf_chain hm
      rw [setChain_chain_find? _ j h1 h2]
      obtain ⟨hf, hc⟩ := h_cells j h1 h2
      obtain ⟨s', hf', hr⟩ := hs.stacks.find?_some hf
      rw [hf']
      have hp : isProtectedIn A.protFrames tag = false := by
        cases hv : V j with
        | nil => rw [hv] at hc; simp [dieCellContent] at hc
        | cons it r => rw [hv] at hc; exact (dieCellContent_cons_inv hc).2.2.1
      exact dieCellContent_cell hr hc (fun x _ hx => hE _ hx) ⟨List.mem_cons_self, hp⟩
    · rw [setChain_find?_not_mem _ _ hm]
      have := hs.stacks a
      revert this
      cases SB.find? A.StackMap a <;> cases SB.find? B.StackMap a <;> simp only [imp_self] <;>
        first | exact id | exact fun h => h.mono (fun x _ hx => hE _ hx) (Nat.le_refl _)
  · intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact h_ex
    · exact hs.disj t ht

theorem sb_expose_sub {A B A' : AccessPerms} {t : Tag}
    (hs : PermSub A B) (h : sb_expose A t = .ok A') :
    ∃ B', sb_expose B t = .ok B' ∧ PermSub A' B' := by
  unfold sb_expose at h ⊢
  by_cases hw : (t == wildcardTag) = true
  · rw [if_pos hw] at h ⊢
    cases h
    exact ⟨B, rfl, hs⟩
  · rw [if_neg hw] at h ⊢
    have hB : B.retired.contains t = false := by rw [hs.ret]; rfl
    rw [if_neg (by rw [hB]; exact Bool.false_ne_true)]
    split at h
    · cases h
    rename_i hr
    cases h
    refine ⟨_, rfl, ⟨hs.stacks, hs.next, hs.prot, by rw [hs.exp], hs.wk, hs.ret, ?_⟩⟩
    intro u hu
    have hne : u ≠ t := fun he => hr (by rw [← he]; simpa using hu)
    simp only [List.contains_cons, Bool.or_eq_false_iff]
    exact ⟨by simpa using hne, hs.disj u hu⟩

theorem PermSub.pushFrame {A B : AccessPerms} (hs : PermSub A B) :
    PermSub (sb_push_frame A) (sb_push_frame B) := by
  refine ⟨hs.stacks.mono fun _ _ h => h.mono (fun x _ he => ⟨he.1, ?_⟩) (Nat.le_refl _),
    hs.next, by simp [sb_push_frame, hs.prot], hs.exp, hs.wk, hs.ret, hs.disj⟩
  have := he.2
  simp only [isProtectedIn] at this
  simp only [sb_push_frame, isProtectedIn, List.any_cons, List.contains_nil, Bool.false_or]
  exact this

theorem PermSub.popFrame {A B A' : AccessPerms} (hs : PermSub A B)
    (h : sb_pop_frame A = .ok A') : ∃ B', sb_pop_frame B = .ok B' ∧ PermSub A' B' := by
  unfold sb_pop_frame at h ⊢
  rw [hs.prot]
  cases hp : A.protFrames with
  | nil => rw [hp] at h; cases h
  | cons f rest =>
      rw [hp] at h
      cases h
      refine ⟨_, rfl, ⟨hs.stacks.mono fun _ _ h => h.mono (fun x _ he => ⟨he.1, ?_⟩)
        (Nat.le_refl _), hs.next, rfl, hs.exp, hs.wk, hs.ret, hs.disj⟩⟩
      have := he.2
      rw [hp] at this
      simp only [isProtectedIn, List.any_cons, Bool.or_eq_false_iff] at this ⊢
      exact this.2

end obseq3.proof
