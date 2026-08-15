import obseq3.sb

/-!
BRIDGE 1 — the keystone lemma of the compiler-correctness proofs, CLOSED:
the compiled place-write pattern `Borrow(Mut) ; useMut via the fresh tag ;
Die` has exactly the stack effect of the source's bare `useMut` via the
parent tag, up to the tag counter.

Proof architecture: every per-cell SB operation involved rewrites its own
cell as `StackMap.set a v` with `v` computed from `find? a` and the
(constant) `protFrames`/`exposed`. A fold over distinct cells therefore
normalizes to a `setChain`, and `setChain`s over the same key sequence
collapse (`SB.set` is move-to-front, so this needs the explicit normal
form `reverse entries ++ filtered original`, not just pointwise equality —
`PermSim` compares raw stack-map lists). The three target phases then
collapse onto the source's single phase entry-for-entry.
-/

namespace obseq3.proof

open obseq3

/-! ## Assoc-list (`SB`) primitives -/

theorem SB.find?_set_self (sb : SB) (a : Word) (v : BorrowStack) :
    SB.find? (SB.set sb a v) a = some v := by
  simp [SB.set, SB.find?]

theorem SB.find?_filter_ne {a b : Word} (h : b ≠ a) :
    ∀ (sb : SB), SB.find? (sb.filter (fun e => e.1 != a)) b = SB.find? sb b
  | [] => rfl
  | (k, s) :: rest => by
      by_cases hk : k = a
      · subst hk
        have hkb : (k == b) = false := by
          simp [Ne.symm h]
        rw [List.filter_cons_of_neg (by simp)]
        rw [SB.find?_filter_ne h rest]
        simp [SB.find?, hkb]
      · rw [List.filter_cons_of_pos (by simp [hk])]
        by_cases hkb : k = b
        · subst hkb
          simp [SB.find?]
        · have hb : (k == b) = false := by simp [hkb]
          simp [SB.find?, hb]
          exact SB.find?_filter_ne h rest

theorem SB.find?_set_ne (sb : SB) {a b : Word} (h : b ≠ a) (v : BorrowStack) :
    SB.find? (SB.set sb a v) b = SB.find? sb b := by
  have ha : (a == b) = false := by simp [Ne.symm h]
  simp [SB.set, SB.find?, ha]
  exact SB.find?_filter_ne h sb

theorem SB.filter_ne_idem (a : Word) :
    ∀ (sb : SB), (sb.filter (fun e => e.1 != a)).filter (fun e => e.1 != a)
      = sb.filter (fun e => e.1 != a)
  | [] => rfl
  | (k, s) :: rest => by
      by_cases hk : k = a
      · subst hk
        rw [List.filter_cons_of_neg (by simp)]
        exact SB.filter_ne_idem k rest
      · rw [List.filter_cons_of_pos (by simp [hk]),
            List.filter_cons_of_pos (by simp [hk]),
            SB.filter_ne_idem a rest]

theorem SB.set_set (sb : SB) (a : Word) (v w : BorrowStack) :
    SB.set (SB.set sb a v) a w = SB.set sb a w := by
  simp only [SB.set]
  rw [List.filter_cons_of_neg (by simp)]
  rw [SB.filter_ne_idem]

/-! ## `setChain` and its normal form -/

/-- Apply a list of `(key, value)` sets left to right. -/
def setChain (sb : SB) : List (Word × BorrowStack) → SB
  | [] => sb
  | (a, v) :: M => setChain (SB.set sb a v) M

def keysOf (M : List (Word × BorrowStack)) : List Word := M.map Prod.fst

theorem setChain_find?_not_mem {b : Word} :
    ∀ (M : List (Word × BorrowStack)) (sb : SB), b ∉ keysOf M →
      SB.find? (setChain sb M) b = SB.find? sb b
  | [], _, _ => rfl
  | (a, v) :: M, sb, h => by
      have hb : b ≠ a := by
        intro hba; exact h (by simp [keysOf, hba])
      have hM : b ∉ keysOf M := by
        intro hm; exact h (by simp [keysOf] at hm ⊢; exact Or.inr hm)
      rw [setChain, setChain_find?_not_mem M _ hM, SB.find?_set_ne sb hb]

/-- The normal form of a `setChain` with distinct keys: the entries in
    reverse order, followed by the original list purged of those keys.
    (This is where `SB.set`'s move-to-front behavior is pinned down.) -/
theorem setChain_normal :
    ∀ (M : List (Word × BorrowStack)) (sb : SB), (keysOf M).Nodup →
      setChain sb M = M.reverse ++ sb.filter (fun e => !((keysOf M).contains e.1))
  | [], sb, _ => by
      simp only [setChain, keysOf, List.map_nil, List.reverse_nil, List.nil_append]
      have : ∀ (l : SB), l.filter (fun _ => true) = l := by
        intro l
        induction l with
        | nil => rfl
        | cons x xs ih => simp [List.filter_cons, ih]
      simp [this]
  | (a, v) :: M, sb, h_nodup => by
      have h_notin : a ∉ keysOf M := by
        simp [keysOf] at h_nodup ⊢
        exact h_nodup.1
      have h_tail : (keysOf M).Nodup := by
        simp [keysOf] at h_nodup ⊢
        exact h_nodup.2
      rw [setChain, setChain_normal M _ h_tail]
      simp only [SB.set]
      rw [List.filter_cons_of_pos (by
        simp [keysOf] at h_notin ⊢
        simpa using h_notin)]
      have h_filters :
          ((sb.filter (fun e => e.1 != a)).filter
              (fun e => !((keysOf M).contains e.1)))
            = sb.filter (fun e => !((keysOf ((a, v) :: M)).contains e.1)) := by
        rw [List.filter_filter]
        apply List.filter_congr
        intro e _
        show (!(keysOf M).contains e.1 && e.1 != a)
            = !((keysOf ((a, v) :: M)).contains e.1)
        simp [keysOf, Bool.not_or, bne, Bool.and_comm]
      rw [h_filters]
      simp

/-- `setChain`s over the same (nodup) key sequence collapse: only the last
    chain's contents survive, in the same layout. -/
theorem setChain_override
    {M M' : List (Word × BorrowStack)}
    (h_keys : keysOf M = keysOf M')
    (h_nodup : (keysOf M').Nodup)
    (sb : SB) :
    setChain (setChain sb M) M' = setChain sb M' := by
  have h_nodupM : (keysOf M).Nodup := h_keys ▸ h_nodup
  rw [setChain_normal M sb h_nodupM,
      setChain_normal M' _ h_nodup,
      setChain_normal M' sb h_nodup]
  congr 1
  rw [List.filter_append]
  have h_rev_nil :
      (M.reverse.filter (fun e => !((keysOf M').contains e.1))) = [] := by
    rw [List.filter_eq_nil_iff]
    intro e h_mem
    have h_key : e.1 ∈ keysOf M :=
      List.mem_map_of_mem (List.mem_reverse.mp h_mem)
    rw [h_keys] at h_key
    simp [h_key]
  rw [h_rev_nil]
  simp only [List.nil_append]
  rw [List.filter_filter]
  apply List.filter_congr
  intro e _
  rw [h_keys]
  cases h : (keysOf M').contains e.1 <;> simp [h]

/-! ## The per-index entry chain of a fold over `[addr+i, addr+len)` -/

/-- The entries a cell fold writes: `(addr+j, W j)` for `j ∈ [i, len)`. -/
def chain (W : Nat → BorrowStack) (addr : Word) (i len : Nat) :
    List (Word × BorrowStack) :=
  if i < len then (addr + i, W i) :: chain W addr (i + 1) len else []
  termination_by len - i

theorem chain_stop {W : Nat → BorrowStack} {addr : Word} {i len : Nat}
    (h : ¬ i < len) : chain W addr i len = [] := by
  rw [chain.eq_def, if_neg h]

theorem chain_step {W : Nat → BorrowStack} {addr : Word} {i len : Nat}
    (h : i < len) :
    chain W addr i len = (addr + i, W i) :: chain W addr (i + 1) len := by
  rw [chain.eq_def]
  exact if_pos h

theorem chain_congr {W W' : Nat → BorrowStack} {addr : Word} {i len : Nat}
    (h_agree : ∀ j, i ≤ j → j < len → W j = W' j) :
    chain W addr i len = chain W' addr i len := by
  by_cases h : i < len
  · rw [chain_step h, chain_step h, h_agree i (Nat.le_refl i) h,
        chain_congr (i := i + 1) (fun j h1 h2 => h_agree j (by omega) h2)]
  · rw [chain_stop h, chain_stop h]
  termination_by len - i

theorem mem_keysOf_chain {W : Nat → BorrowStack} {addr : Word} {b : Word}
    {i len : Nat}
    (h_mem : b ∈ keysOf (chain W addr i len)) :
    ∃ j, i ≤ j ∧ j < len ∧ b = addr + j := by
  by_cases h : i < len
  · rw [chain_step h] at h_mem
    simp [keysOf] at h_mem
    cases h_mem with
    | inl h_eq => exact ⟨i, Nat.le_refl i, h, h_eq⟩
    | inr h_tail =>
        obtain ⟨j, h1, h2, h3⟩ :=
          mem_keysOf_chain (i := i + 1) (by simpa [keysOf] using h_tail)
        exact ⟨j, by omega, h2, h3⟩
  · rw [chain_stop h] at h_mem
    simp [keysOf] at h_mem
  termination_by len - i

theorem keysOf_chain_eq {W W' : Nat → BorrowStack} {addr : Word} {i len : Nat} :
    keysOf (chain W addr i len) = keysOf (chain W' addr i len) := by
  by_cases h : i < len
  · rw [chain_step h, chain_step h]
    simp only [keysOf, List.map_cons, List.cons.injEq]
    exact ⟨trivial, keysOf_chain_eq (i := i + 1)⟩

  · rw [chain_stop h, chain_stop h]
  termination_by len - i

theorem nodup_keysOf_chain {W : Nat → BorrowStack} {addr : Word} {i len : Nat} :
    (keysOf (chain W addr i len)).Nodup := by
  by_cases h : i < len
  · rw [chain_step h]
    simp only [keysOf, List.map_cons, List.nodup_cons]
    constructor
    · intro h_mem
      obtain ⟨j, h1, _, h3⟩ := mem_keysOf_chain (b := addr + i) h_mem
      have h_ij : i = j := Nat.add_left_cancel h3
      omega
    · exact nodup_keysOf_chain (i := i + 1)
  · rw [chain_stop h]
    simp [keysOf]
  termination_by len - i

theorem setChain_chain_find? {W : Nat → BorrowStack} {addr : Word} {i len : Nat}
    (sb : SB) (j : Nat) (h1 : i ≤ j) (h2 : j < len) :
    SB.find? (setChain sb (chain W addr i len)) (addr + j) = some (W j) := by
  have h : i < len := by omega
  rw [chain_step h, setChain]
  by_cases hj : j = i
  · subst hj
    rw [setChain_find?_not_mem _ _ (by
      intro h_mem
      obtain ⟨k, hk1, _, hk3⟩ := mem_keysOf_chain (b := addr + j) h_mem
      have h_jk : j = k := Nat.add_left_cancel hk3
      omega)]
    exact SB.find?_set_self sb (addr + j) (W j)
  · exact setChain_chain_find? (i := i + 1) _ j (by omega) h2
  termination_by len - i

/-! ## Fold characterizations -/

/-- Inversion for `foldCellsIdx` whose per-cell op is a content-driven
    rewrite of its own cell (`protFrames`/`exposed`/`NextTag` constant). -/
theorem foldCellsIdx_ok_inv
    {op : AccessPerms → Word → Nat → Except String AccessPerms}
    {C : Nat → Option BorrowStack → Except String BorrowStack}
    {P : List (List Tag)} {E : List Tag} {N : Tag} {addr : Word}
    (h_op : ∀ ap i, ap.protFrames = P → ap.exposed = E → ap.NextTag = N →
      op ap (addr + i) i =
        match C i (SB.find? ap.StackMap (addr + i)) with
        | .error e => .error e
        | .ok v => .ok { ap with StackMap := SB.set ap.StackMap (addr + i) v }) :
    ∀ {i len : Nat} (ap ap' : AccessPerms),
      ap.protFrames = P → ap.exposed = E → ap.NextTag = N →
      foldCellsIdx op ap addr i len = .ok ap' →
      ∃ W : Nat → BorrowStack,
        (∀ j, i ≤ j → j < len → C j (SB.find? ap.StackMap (addr + j)) = .ok (W j)) ∧
        ap' = { ap with StackMap := setChain ap.StackMap (chain W addr i len) } := by
  intro i len ap ap' h_pf h_ex h_nt h_fold
  by_cases h : i < len
  · rw [foldCellsIdx.eq_def, if_pos h, h_op ap i h_pf h_ex h_nt] at h_fold
    cases h_C : C i (SB.find? ap.StackMap (addr + i)) with
    | error e => rw [h_C] at h_fold; simp at h_fold
    | ok v =>
        rw [h_C] at h_fold
        simp only at h_fold
        obtain ⟨W', h_cells', h_ap'⟩ :=
          foldCellsIdx_ok_inv h_op (i := i + 1)
            { ap with StackMap := SB.set ap.StackMap (addr + i) v } ap'
            h_pf h_ex h_nt h_fold
        refine ⟨fun j => if j = i then v else W' j, ?_, ?_⟩
        · intro j h1 h2
          by_cases hj : j = i
          · subst hj; simp [h_C]
          · have h_ne : addr + j ≠ addr + i :=
              fun hc => hj (Nat.add_left_cancel hc)
            have := h_cells' j (by omega) h2
            rw [SB.find?_set_ne _ h_ne] at this
            simp [hj, this]
        · have h_tail :
              chain (fun j => if j = i then v else W' j) addr (i + 1) len
                = chain W' addr (i + 1) len :=
            chain_congr (fun j h1 _ => by
              have : j ≠ i := by omega
              simp [this])
          rw [h_ap', chain_step h, setChain, if_pos rfl, h_tail]
  · rw [foldCellsIdx.eq_def, if_neg h] at h_fold
    cases h_fold
    refine ⟨fun _ => [], fun j h1 h2 => by omega, ?_⟩
    rw [chain_stop h]
    rfl
  termination_by i len => len - i

/-- Construction for `foldCells` whose per-cell op is a content-driven
    rewrite: if every cell's stack is known and every content computation
    succeeds, the fold succeeds with the corresponding `setChain`. -/
theorem foldCells_ok_of_cells
    {op : AccessPerms → Word → Except String AccessPerms}
    {C : Word → BorrowStack → Except String BorrowStack}
    {msgNone : Word → String}
    {P : List (List Tag)} {E : List Tag} {N : Tag} {addr : Word}
    (h_op : ∀ ap a, ap.protFrames = P → ap.exposed = E → ap.NextTag = N →
      op ap a =
        match SB.find? ap.StackMap a with
        | none => .error (msgNone a)
        | some stack =>
          match C a stack with
          | .error e => .error e
          | .ok v => .ok { ap with StackMap := SB.set ap.StackMap a v }) :
    ∀ (len i : Nat) (ap : AccessPerms) (V W : Nat → BorrowStack),
      ap.protFrames = P → ap.exposed = E → ap.NextTag = N →
      (∀ j, i ≤ j → j < i + len → SB.find? ap.StackMap (addr + j) = some (V j)) →
      (∀ j, i ≤ j → j < i + len → C (addr + j) (V j) = .ok (W j)) →
      foldCells op ap (addr + i) len =
        .ok { ap with StackMap := setChain ap.StackMap (chain W addr i (i + len)) } := by
  intro len
  induction len with
  | zero =>
      intro i ap V W h_pf h_ex h_nt h_find h_content
      rw [foldCells, chain_stop (by omega)]
      rfl
  | succ n ih =>
      intro i ap V W h_pf h_ex h_nt h_find h_content
      have h_cell : op ap (addr + i)
          = .ok { ap with StackMap := SB.set ap.StackMap (addr + i) (W i) } := by
        rw [h_op ap (addr + i) h_pf h_ex h_nt, h_find i (Nat.le_refl i) (by omega)]
        simp [h_content i (Nat.le_refl i) (by omega)]
      have h_rest := ih (i + 1)
        { ap with StackMap := SB.set ap.StackMap (addr + i) (W i) } V W
        h_pf h_ex h_nt
        (fun j h1 h2 => by
          have h_ne : addr + j ≠ addr + i := fun hc => by
            have := Nat.add_left_cancel hc
            omega
          rw [SB.find?_set_ne _ h_ne]
          exact h_find j (by omega) (by omega))
        (fun j h1 h2 => h_content j (by omega) (by omega))
      simp only [foldCells, h_cell]
      rw [show addr + i + 1 = addr + (i + 1) from rfl, h_rest,
          chain_step (show i < i + (n + 1) from Nat.lt_add_of_pos_right (Nat.succ_pos n))]
      rw [show i + 1 + n = i + (n + 1) from Nat.add_right_comm i 1 n]
      rfl

/-! ## Content-level facts -/

theorem writeCellContent_top_mutref
    {pf : List (List Tag)} {ex : List Tag} {a : Word} {t : Tag}
    (h_t : (t == wildcardTag) = false) (rest : BorrowStack) :
    writeCellContent pf ex a t (.MutRef t :: rest) = .ok (.MutRef t :: rest) := by
  simp [writeCellContent, h_t, splitStack, Item.tag, Item.grantsWrite, firstProtectedIn]

theorem dieCellContent_top
    {pf : List (List Tag)} {t : Tag}
    (h_np : isProtectedIn pf t = false) (rest : BorrowStack) :
    dieCellContent pf t (.MutRef t :: rest) = .ok rest := by
  simp [dieCellContent, Item.tag, h_np]

/-! ## The keystone -/

/-- BRIDGE 1 (keystone), CLOSED: the compiled place-write pattern
    `Borrow(Mut) ; useMut via the fresh tag ; Die` has exactly the stack
    effect of the source's bare `useMut` via the parent tag, up to the tag
    counter. The two extra hypotheses are invariants of every reachable
    `AccessPerms` (tags are minted from 1 upward, and protector frames only
    ever contain already-minted tags): the fresh tag is not the wildcard
    and is not protected. -/
theorem sb_ref_use_die_cancels
    {s s1 : AccessPerms} {addr : Word} {len : Nat} {tag t' : Tag}
    (h_nt : (s.NextTag == wildcardTag) = false)
    (h_unprot : isProtectedIn s.protFrames s.NextTag = false)
    (h_ref : sb_ref s addr len tag .Mut false [] = .ok (s1, t')) :
    ∃ s2 s3 sAcc,
      sb_write s1 addr len t' = .ok s2 ∧
      sb_die s2 addr len t' = .ok s3 ∧
      sb_write s addr len tag = .ok sAcc ∧
      s3.StackMap = sAcc.StackMap ∧
      s3.exposed = sAcc.exposed ∧
      s3.protFrames = sAcc.protFrames ∧
      sAcc.NextTag ≤ s3.NextTag := by
  -- Unpack sb_ref: mint, run the per-cell fold, no protector registration.
  simp only [sb_ref, freshTag, RefKind.toItem] at h_ref
  cases h_go : foldCellsIdx
      (fun ap a _ => do pushCell (← writeCell ap a tag) a (Item.MutRef s.NextTag))
      { s with NextTag := s.NextTag + 1 } addr 0 len with
  | error e =>
      rw [h_go] at h_ref
      simp [Functor.map, Except.map] at h_ref
  | ok apR =>
      rw [h_go] at h_ref
      simp [Functor.map, Except.map] at h_ref
      obtain ⟨h_eq1, h_eq2⟩ := h_ref
      subst h_eq1
      subst h_eq2
      -- Now apR = apR and t' = s.NextTag.
      -- Phase 1 inversion: characterize the ref fold as a setChain.
      obtain ⟨W₁, h_cells₁, h_apR⟩ :=
        foldCellsIdx_ok_inv
          (op := fun ap a _ => do pushCell (← writeCell ap a tag) a (Item.MutRef s.NextTag))
          (C := fun i v? =>
            match v? with
            | none => .error s!"sb-write: no borrow stack at address {addr + i}"
            | some stack =>
              match writeCellContent s.protFrames s.exposed (addr + i) tag stack with
              | .error e => .error e
              | .ok v => .ok (.MutRef s.NextTag :: v))
          (P := s.protFrames) (E := s.exposed) (N := s.NextTag + 1)
          (fun ap i h_pf h_ex h_nt' => by
            cases h_find : SB.find? ap.StackMap (addr + i) with
            | none =>
                simp only [writeCell, h_pf, h_ex, h_find, bind, Except.bind]
            | some stack =>
                cases h_content : writeCellContent s.protFrames s.exposed
                    (addr + i) tag stack with
                | error e =>
                    simp only [writeCell, h_pf, h_ex, h_find, h_content, bind, Except.bind]
                | ok v =>
                    simp only [writeCell, h_pf, h_ex, h_find, h_content, bind, Except.bind,
                      pushCell, SB.find?_set_self, SB.set_set])
          { s with NextTag := s.NextTag + 1 } apR rfl rfl rfl h_go
      rw [show ({ s with NextTag := s.NextTag + 1 } : AccessPerms).StackMap
            = s.StackMap from rfl] at h_cells₁
      -- Extract per-cell source stacks and write contents (total functions).
      have h_split : ∀ j, ∃ vj, ∃ wj, j < len →
          SB.find? s.StackMap (addr + j) = some vj ∧
            writeCellContent s.protFrames s.exposed (addr + j) tag vj = .ok wj ∧
            W₁ j = .MutRef s.NextTag :: wj := by
        intro j
        by_cases hj : j < len
        · have h := h_cells₁ j (Nat.zero_le j) hj
          cases h_find : SB.find? s.StackMap (addr + j) with
          | none =>
              simp [h_find] at h
          | some vj =>
              simp only [h_find] at h
              cases h_content : writeCellContent s.protFrames s.exposed (addr + j) tag vj with
              | error e =>
                  simp [h_content] at h
              | ok wj =>
                  simp only [h_content, Except.ok.injEq] at h
                  exact ⟨vj, wj, fun _ => ⟨rfl, h_content, h.symm⟩⟩
        · exact ⟨[], [], fun h => absurd h hj⟩
      let V : Nat → BorrowStack := fun j => (h_split j).choose
      let W : Nat → BorrowStack := fun j => (h_split j).choose_spec.choose
      have h_VW : ∀ j, j < len →
          SB.find? s.StackMap (addr + j) = some (V j) ∧
            writeCellContent s.protFrames s.exposed (addr + j) tag (V j) = .ok (W j) ∧
            W₁ j = .MutRef s.NextTag :: W j :=
        fun j hj => (h_split j).choose_spec.choose_spec hj
      have h_V : ∀ j, j < len → SB.find? s.StackMap (addr + j) = some (V j) :=
        fun j hj => (h_VW j hj).1
      have h_W : ∀ j, j < len →
          writeCellContent s.protFrames s.exposed (addr + j) tag (V j) = .ok (W j) :=
        fun j hj => (h_VW j hj).2.1
      have h_W₁ : ∀ j, j < len → W₁ j = .MutRef s.NextTag :: W j :=
        fun j hj => (h_VW j hj).2.2
      -- h_op for the plain write fold (shared by source and phase 2).
      have h_op_write : ∀ (t : Tag) (ap : AccessPerms) (a : Word),
          ap.protFrames = s.protFrames → ap.exposed = s.exposed →
          writeCell ap a t =
            match SB.find? ap.StackMap a with
            | none => .error s!"sb-write: no borrow stack at address {a}"
            | some stack =>
              match writeCellContent s.protFrames s.exposed a t stack with
              | .error e => .error e
              | .ok v => .ok { ap with StackMap := SB.set ap.StackMap a v } := by
        intro t ap a h_pf h_ex
        cases h_find : SB.find? ap.StackMap a with
        | none => simp only [writeCell, h_find]
        | some stack =>
            cases h_content : writeCellContent s.protFrames s.exposed a t stack with
            | error e =>
                simp only [writeCell, h_pf, h_ex, h_find, h_content]
            | ok v =>
                simp only [writeCell, h_pf, h_ex, h_find, h_content]
      -- SOURCE: sb_write s tag succeeds with contents W.
      have h_src : sb_write s addr len tag =
          .ok { s with StackMap := setChain s.StackMap (chain W addr 0 len) } := by
        show foldCells (fun ap a => writeCell ap a tag) s addr len = _
        have := foldCells_ok_of_cells
          (C := fun a stack => writeCellContent s.protFrames s.exposed a tag stack)
          (msgNone := fun a => s!"sb-write: no borrow stack at address {a}")
          (P := s.protFrames) (E := s.exposed) (N := s.NextTag)
          (fun ap a h_pf h_ex _ => h_op_write tag ap a h_pf h_ex)
          len 0 s V W
          rfl rfl rfl
          (fun j h1 h2 => by simp only [Nat.zero_add] at h2; exact h_V j h2)
          (fun j h1 h2 => by simp only [Nat.zero_add] at h2; exact h_W j h2)
        rw [show addr + 0 = addr from rfl] at this
        rw [show (0 : Nat) + len = len from Nat.zero_add len] at this
        rw [this]
      -- Fields of apR.
      have h_apR_pf : apR.protFrames = s.protFrames := by rw [h_apR]
      have h_apR_ex : apR.exposed = s.exposed := by rw [h_apR]
      have h_apR_nt : apR.NextTag = s.NextTag + 1 := by rw [h_apR]
      have h_apR_sm : apR.StackMap = setChain s.StackMap (chain W₁ addr 0 len) := by
        rw [h_apR]
      -- PHASE 2: sb_write apR t' rewrites each cell to itself.
      have h_phase2 : sb_write apR addr len s.NextTag =
          .ok { apR with StackMap := setChain apR.StackMap (chain W₁ addr 0 len) } := by
        show foldCells (fun ap a => writeCell ap a s.NextTag) apR addr len = _
        have := foldCells_ok_of_cells
          (C := fun a stack => writeCellContent s.protFrames s.exposed a s.NextTag stack)
          (msgNone := fun a => s!"sb-write: no borrow stack at address {a}")
          (P := s.protFrames) (E := s.exposed) (N := s.NextTag + 1)
          (fun ap a h_pf h_ex _ => h_op_write s.NextTag ap a h_pf h_ex)
          len 0 apR W₁ W₁
          h_apR_pf h_apR_ex h_apR_nt
          (fun j h1 h2 => by
            simp only [Nat.zero_add] at h2
            rw [h_apR_sm]
            exact setChain_chain_find? s.StackMap j (Nat.zero_le j) h2)
          (fun j h1 h2 => by
            simp only [Nat.zero_add] at h2
            rw [h_W₁ j h2]
            exact writeCellContent_top_mutref h_nt (W j))
        rw [show addr + 0 = addr from rfl] at this
        rw [show (0 : Nat) + len = len from Nat.zero_add len] at this
        exact this
      -- PHASE 3: sb_die pops the fresh item at each cell.
      have h_phase3 : sb_die { apR with StackMap := setChain apR.StackMap (chain W₁ addr 0 len) }
            addr len s.NextTag =
          .ok { apR with StackMap := setChain (setChain apR.StackMap (chain W₁ addr 0 len)) (chain W addr 0 len) } := by
        show foldCells _ _ addr len = _
        have := foldCells_ok_of_cells
          (op := fun ap a =>
            match ap.StackMap.find? a with
            | none => .error s!"sb-die: no borrow stack at address {a}"
            | some stack =>
                match dieCellContent ap.protFrames s.NextTag stack with
                | .error e => .error e
                | .ok below => .ok { ap with StackMap := SB.set ap.StackMap a below })
          (C := fun _ stack => dieCellContent s.protFrames s.NextTag stack)
          (msgNone := fun a => s!"sb-die: no borrow stack at address {a}")
          (P := s.protFrames) (E := s.exposed) (N := s.NextTag + 1)
          (fun ap a h_pf h_ex _ => by
            cases h_find : SB.find? ap.StackMap a with
            | none => simp only [h_find]
            | some stack =>
                cases h_content : dieCellContent s.protFrames s.NextTag stack with
                | error e => simp only [h_pf, h_find, h_content]
                | ok below => simp only [h_pf, h_find, h_content])
          len 0 { apR with StackMap := setChain apR.StackMap (chain W₁ addr 0 len) }
          W₁ W
          h_apR_pf h_apR_ex h_apR_nt
          (fun j h1 h2 => by
            simp only [Nat.zero_add] at h2
            exact setChain_chain_find? apR.StackMap j (Nat.zero_le j) h2)
          (fun j h1 h2 => by
            simp only [Nat.zero_add] at h2
            rw [h_W₁ j h2]
            exact dieCellContent_top h_unprot (W j))
        rw [show addr + 0 = addr from rfl] at this
        rw [show (0 : Nat) + len = len from Nat.zero_add len] at this
        exact this
      -- Assemble.
      refine ⟨_, _, _, h_phase2, h_phase3, h_src, ?_, ?_, ?_, ?_⟩
      · -- StackMap: collapse the three chains onto the source's one.
        show setChain (setChain apR.StackMap (chain W₁ addr 0 len))
            (chain W addr 0 len)
          = setChain s.StackMap (chain W addr 0 len)
        rw [h_apR_sm]
        rw [setChain_override (keysOf_chain_eq) nodup_keysOf_chain,
            setChain_override (keysOf_chain_eq) nodup_keysOf_chain]
      · exact h_apR_ex
      · exact h_apR_pf
      · rw [h_apR_nt]
        exact Nat.le_succ s.NextTag

end obseq3.proof
