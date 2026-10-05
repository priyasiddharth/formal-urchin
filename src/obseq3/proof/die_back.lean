import obseq3.proof.permsub_rev
import obseq3.proof.die_elision
import obseq3.proof.tagsin
import obseq3.brackets

/-!
# Die elision, backward: compiled code reaches the same verdict

For programs whose `Die`s all close ROUTE BRACKETS (`RouteProg`, the Prop
form of `oseair.bracketIssues`), a run that succeeds on OSEA-IR_B succeeds
on OSEA-IR, in lockstep (`die_elision_back`). With `die_elision` the two
machines then reach the same verdict.

The invariant (`Inv`) adds to the forward relation (`PermSub`) where tags
can be: every tag in memory or a register is below the counter; no
retired tag is in memory, and one in a register only in a DEAD bracket
register (its `Die` already ran, so nothing reads it again). Inside a
bracket (`Pending`), the route tag sits on top of every byte of its
range, is unexposed and unprotected, and is held by its register alone:
that is what makes A's `Die` succeed, and after it the tag is nowhere
live.
-/

namespace obseq3.proof

open obseq3 obseq3.bytes obseq3.oseair

/-! ## Field lemmas: what each operation leaves alone -/

theorem sb_read_fields {A A' : AccessPerms} {addr : Word} {lenB : Nat} {t : Tag}
    (h : sb_read A addr lenB t = .ok A') : ∃ sm, A' = { A with StackMap := sm } := by
  have h0 : foldCells (fun ap a => readCell ap a t) A (addr + 0) lenB = .ok A' := h
  obtain ⟨V, W, -, rfl⟩ :=
    foldCells_ok_inv
      (C := fun a stack => readCellContent A.protFrames A.exposed a t stack)
      (msgNone := fun a => s!"sb-read: no borrow stack at address {a}")
      (P := A.protFrames) (E := A.exposed) (N := A.NextTag)
      (fun ap a h_pf h_ex _ => readCell_content_form t ap a h_pf h_ex)
      lenB 0 A A' rfl rfl rfl h0
  exact ⟨_, rfl⟩

theorem sb_write_fields {A A' : AccessPerms} {addr : Word} {lenB : Nat} {t : Tag}
    (h : sb_write A addr lenB t = .ok A') : ∃ sm, A' = { A with StackMap := sm } := by
  have h0 : foldCells (fun ap a => writeCell ap a t) A (addr + 0) lenB = .ok A' := h
  obtain ⟨V, W, -, rfl⟩ :=
    foldCells_ok_inv
      (C := fun a stack => writeCellContent A.protFrames A.exposed a t stack)
      (msgNone := fun a => s!"sb-write: no borrow stack at address {a}")
      (P := A.protFrames) (E := A.exposed) (N := A.NextTag)
      (fun ap a h_pf h_ex _ => writeCell_content_form t ap a h_pf h_ex)
      lenB 0 A A' rfl rfl rfl h0
  exact ⟨_, rfl⟩

theorem sb_dealloc_fields {t : Tag} :
    ∀ (lenB : Nat) (addr : Word) {A A' : AccessPerms},
      sb_dealloc A addr lenB t = .ok A' → ∃ sm, A' = { A with StackMap := sm } := by
  intro lenB
  induction lenB with
  | zero =>
      intro addr A A' h
      rw [sb_dealloc_eq] at h
      simp only [foldCells] at h
      cases h
      exact ⟨_, rfl⟩
  | succ n ih =>
      intro addr A A' h
      rw [sb_dealloc_eq] at h
      simp only [foldCells] at h
      split at h
      · simp at h
      rename_i A1 h_cell
      obtain ⟨-, -, -, -, -, -, -, -, -, rfl⟩ := deallocCellOp_ok_inv h_cell
      rw [← sb_dealloc_eq] at h
      obtain ⟨sm, rfl⟩ := ih (addr + 1) h
      exact ⟨sm, rfl⟩

theorem sb_own_fields {A A' : AccessPerms} {addr : Word} {lenB : Nat} {n : Tag}
    (h : sb_own A addr lenB = .ok (A', n)) :
    n = A.NextTag ∧ ∃ sm, A' = { A with StackMap := sm, NextTag := A.NextTag + 1 } := by
  rw [sb_own_eq] at h
  split at h
  · cases h
  rename_i apR hgo
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hgo0 : foldCells (fun ap a => ownCell ap a A.NextTag) { A with NextTag := A.NextTag + 1 }
      (addr + 0) lenB = .ok apR := hgo
  rw [foldCells_ok_iff_foldCellsIdx_ok] at hgo0
  obtain ⟨W, -, rfl⟩ :=
    foldCellsIdx_ok_inv (op := fun ap a _ => ownCell ap a A.NextTag)
      (C := fun i o => ownCellStep (addr + i) A.NextTag o)
      (P := A.protFrames) (E := A.exposed) (N := A.NextTag + 1)
      (fun ap i _ _ _ => ownCell_content_form A.NextTag ap (addr + i))
      { A with NextTag := A.NextTag + 1 } _ rfl rfl rfl hgo0
  exact ⟨rfl, _, rfl⟩

/-- A retag: the fresh tag is the counter, which moves by one; the
    frames gain at most the fresh tag. -/
theorem sb_ref_fields {A A' : AccessPerms} {addr : Word} {lenB : Nat} {t : Tag}
    {kind : RefKind} {prot : Bool} {mask : List Bool} {n : Tag}
    (h : sb_ref A addr lenB t kind prot mask = .ok (A', n)) :
    n = A.NextTag ∧ A'.NextTag = A.NextTag + 1 ∧ A'.retired = A.retired ∧
      A'.exposed = A.exposed ∧
      (∀ u, isProtectedIn A'.protFrames u = true → u = A.NextTag ∨ isProtectedIn A.protFrames u = true) ∧
      (prot = false → A'.protFrames = A.protFrames) := by
  rw [sb_ref_eq] at h
  split at h
  · cases h
  rename_i apR hgo
  obtain ⟨W, -, rfl⟩ :=
    foldCellsIdx_ok_inv
      (op := refCellOp t kind A.NextTag mask)
      (C := fun j v? => refCellStep A.protFrames A.exposed (addr + j) t kind A.NextTag mask j v?)
      (P := A.protFrames) (E := A.exposed) (N := A.NextTag + 1)
      (refCellOp_content_form (addr := addr) t kind A.NextTag mask)
      { A with NextTag := A.NextTag + 1 } _ rfl rfl rfl hgo
  simp only at h
  split at h
  · cases h
  rename_i pf' wk' hreg
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro u hu
    by_cases hun : u = A.NextTag
    · exact Or.inl hun
    · right
      cases hc : isProtectedIn A.protFrames u with
      | true => rfl
      | false =>
          have := regProt_prot hreg hun hc
          simp only at hu
          rw [this] at hu; cases hu
  · intro hp
    subst hp
    simp only [regProt, Bool.false_eq_true, if_false, Except.ok.injEq, Prod.mk.injEq] at hreg
    exact hreg.1.symm

theorem sb_expose_fields {A A' : AccessPerms} {t : Tag} (h : sb_expose A t = .ok A') :
    A' = A ∨ A' = { A with exposed := t :: A.exposed } := by
  unfold sb_expose at h
  split at h
  · cases h; exact Or.inl rfl
  split at h
  · cases h
  · cases h; exact Or.inr rfl

/-! ## The programs -/

/-- The retag kinds that PUSH their item on top (no insert-above). -/
def PushKind : RefKind → Prop
  | .Mut | .BoxMut | .Shared | .Raw false => True
  | _ => False

/-- `prog (b+2) = Die r n` closes a route bracket opened at `b`. -/
structure IsBracket (prog : oseair.Prog) (b : Nat) (r : Register) (n : Nat) : Prop where
  borrow : ∃ k base off, PushKind k ∧
    prog b = some (.Assgn r (.Borrow k false [] (some n) base off))
  access : ∃ i, prog (b + 1) = some i ∧ i.through r = true
  die : prog (b + 2) = some (.Die r n)
  only : ∀ l i, prog l = some i → r ∈ i.regs → b ≤ l ∧ l ≤ b + 2
  nojump : ∀ l dr v skip, prog l = some (.SkipIf dr v skip) →
    ¬ (b < l + 1 + skip ∧ l + 1 + skip ≤ b + 2)

/-- Every `Die` closes a route bracket, and no `CStore` stores a pointer
    literal. -/
def RouteProg (prog : oseair.Prog) : Prop :=
  (∀ d r n, prog d = some (.Die r n) → ∃ b, d = b + 2 ∧ IsBracket prog b r n) ∧
  (∀ l lay vals ptr, prog l = some (.CStore lay vals ptr) → ∀ v ∈ vals,
    ∀ b o e s t, v ≠ .Ptr b o e s t)

/-- `x`'s bracket has closed: nothing at or after `pc` mentions it. -/
def Dead (prog : oseair.Prog) (pc : Nat) (x : Register) : Prop :=
  ∃ d n, prog d = some (.Die x n) ∧ d < pc

theorem Dead.mono {prog : oseair.Prog} {pc pc' : Nat} {x : Register} (h : Dead prog pc x)
    (hle : pc ≤ pc') : Dead prog pc' x := by
  obtain ⟨d, n, hd, hlt⟩ := h
  exact ⟨d, n, hd, Nat.lt_of_lt_of_le hlt hle⟩

/-- The tags of every register's values satisfy `P` (which may depend on
    the register). -/
def RegsOK (P : Register → Tag → Prop) (reg : RegMap) : Prop :=
  ∀ x vs, reg.lookup x = some vs → ValsOK (P x) vs

theorem RegsOK.mono {P Q : Register → Tag → Prop} {reg : RegMap} (h : RegsOK P reg)
    (hPQ : ∀ x t, P x t → Q x t) : RegsOK Q reg :=
  fun x vs hl => (h x vs hl).mono (hPQ x)

theorem RegMap.lookup_insert_self (reg : RegMap) (x : Register) (vs : List Val) :
    (reg.insert x vs).lookup x = some vs := by
  simp [RegMap.insert, RegMap.lookup, List.lookup]

theorem RegMap.lookup_insert_ne (reg : RegMap) {x y : Register} (vs : List Val) (h : y ≠ x) :
    (reg.insert x vs).lookup y = reg.lookup y := by
  simp only [RegMap.insert, RegMap.lookup, List.lookup]
  have : (y == x) = false := by simpa using h
  rw [this]
  exact lookup_filter_ne h reg

theorem RegsOK.insert {P : Register → Tag → Prop} {reg : RegMap} (h : RegsOK P reg)
    {x : Register} {vs : List Val} (hv : ValsOK (P x) vs) : RegsOK P (reg.insert x vs) := by
  intro y ws hl
  by_cases hy : y = x
  · subst hy
    rw [RegMap.lookup_insert_self] at hl
    cases hl; exact hv
  · rw [RegMap.lookup_insert_ne _ _ hy] at hl
    exact h y ws hl

/-! ## The invariant -/

/-- A tag that may appear in memory or a live register. -/
def Good (A : AccessPerms) (t : Tag) : Prop := t < A.NextTag ∧ t ∉ A.retired

/-- Bounds every reachable permission state keeps: retired, exposed and
    protected tags are minted ones; the wildcard is never retired. -/
structure PInv (A : AccessPerms) : Prop where
  pos : 0 < A.NextTag
  ret : ∀ t ∈ A.retired, 0 < t ∧ t < A.NextTag
  exb : ∀ t ∈ A.exposed, t < A.NextTag
  prot : ∀ t, isProtectedIn A.protFrames t = true → t < A.NextTag

theorem PInv.good_wild {A : AccessPerms} (h : PInv A) : Good A wildcardTag :=
  ⟨h.pos, fun hr => Nat.lt_irrefl _ (h.ret _ hr).1⟩

/-- Inside a route bracket whose register holds `[Ptr base off _ _ N0]`. -/
structure PendAt (sA : oseair.State MSB) (r : Register) (n base off N0 : Nat) : Prop where
  pos : 0 < N0
  notret : N0 ∉ sA.perms.retired
  notex : sA.perms.exposed.contains N0 = false
  notprot : isProtectedIn sA.perms.protFrames N0 = false
  top : ∀ j < n, ∃ it rest, SB.find? sA.perms.StackMap (base + off + j) = some (it :: rest) ∧
    it.tag = N0 ∧ (∀ t0, it ≠ .Own t0) ∧ (∀ t0, it ≠ .Disabled t0)
  regs : RegsOK (fun x t => t = N0 → x = r) sA.reg
  mem : MemOK (· ≠ N0) sA.mem

def Pending (sA : oseair.State MSB) (r : Register) (n : Nat) : Prop :=
  ∃ base off ext size N0, sA.reg.lookup r = some [.Ptr base off ext size N0] ∧
    PendAt sA r n base off N0

structure Inv (prog : oseair.Prog) (sA : oseair.State MSB) (sB : oseair.State MSB_B) : Prop where
  rel : StateRel (fun a b => PermSub a b) sA sB
  pinv : PInv sA.perms
  mem : MemOK (Good sA.perms) sA.mem
  regs : RegsOK (fun x t => t < sA.perms.NextTag ∧
    (t ∈ sA.perms.retired → Dead prog sA.pc x)) sA.reg
  pend : ∀ b r n, IsBracket prog b r n → (sA.pc = b + 1 ∨ sA.pc = b + 2) → Pending sA r n

theorem Inv.initial (prog : oseair.Prog) :
    Inv prog (oseair.State.initial MSB) (oseair.State.initial MSB_B) where
  rel := ⟨rfl, rfl, rfl, PermSub.initial⟩
  pinv := ⟨Nat.one_pos, (fun t h => by cases h), (fun t h => by cases h),
    (fun t h => by simp [isProtectedIn, oseair.State.initial, MSB, PermissionModel.stackedBorrows, AccessPerms.init] at h)⟩
  mem := MemOK_iff.mpr fun a b p h => by cases h
  regs := fun x vs h => by cases h
  pend := fun b r n _ h => by
    simp only [oseair.State.initial] at h
    omega

/-- A register the instruction at `pc` mentions holds no retired tag. -/
theorem Inv.act_ok {prog : oseair.Prog} {sA : oseair.State MSB} {sB : oseair.State MSB_B}
    (hp : RouteProg prog) (hI : Inv prog sA sB) {i : Instr} (hi : prog sA.pc = some i)
    {x : Register} (hx : x ∈ i.regs) {vs : List Val} (hl : sA.reg.lookup x = some vs)
    {v : Val} (hv : v ∈ vs) {b o e s t : Nat} (he : v = .Ptr b o e s t) :
    t < sA.perms.NextTag ∧ t ∉ sA.perms.retired := by
  obtain ⟨hlt, hret⟩ := hI.regs x vs hl v hv b o e s t he
  refine ⟨hlt, fun hr => ?_⟩
  obtain ⟨d, n, hd, hdlt⟩ := hret hr
  obtain ⟨bb, rfl, hb⟩ := hp.1 d x n hd
  have := (hb.only sA.pc i hi hx).2
  omega

end obseq3.proof
