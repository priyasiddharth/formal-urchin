import obseq3.proof.readsrc
import obseq3.proof.stmts
import obseq3.proof.permsim_dealloc

/-!
# The program theorem

The per-statement leaves assembled into the compiler-correctness theorem
for the compiler: if the program compiles and every statement of it
has a simulation (`StmtSimB`), every successful source run is matched by
a successful target run, with the byte invariant `InvAtB` at the
statement-prefix compile state. Coverage is then a list of `StmtSimB`
instances, one per supported statement shape.
-/

namespace obseq3.proof

open obseq3 obseq3.bytes obseq3.proof
open obseq3.mirlite (MemValue Binding Env PlaceRes)
open obseq3.oseair (Val Register)
open obseq3.compile

/-! ## The source pc -/

theorem evalAllocLen_pc {Γ : Ctx} {L : mirlite.LayEnv Γ} {s s1 : mirlite.State MSB Γ}
    {len : AllocLen Γ} {n : Nat} (h : mirlite.evalAllocLen MSB L s len = .ok (n, s1)) :
    s1.pc = s.pc := by
  cases len with
  | const k =>
      simp only [mirlite.evalAllocLen, Except.ok.injEq, Prod.mk.injEq] at h
      rw [← h.2]
  | fromPlace p =>
      obtain ⟨out, h_e, -, rfl⟩ := evalAllocLen_fromPlace_inv h
      rw [evalCopy_state h_e]

theorem evalCopy_pc {Γ : Ctx} {L : mirlite.LayEnv Γ} {s : mirlite.State MSB Γ}
    {σ : LayoutTy} {p : Place Γ σ} {out : mirlite.EvalOutput MSB Γ}
    (h : mirlite.evalCopy MSB L s p = .ok out) : out.state.pc = s.pc := by
  rw [evalCopy_state h]

theorem evalRExpr_pc {Γ : Ctx} {L : mirlite.LayEnv Γ} {s : mirlite.State MSB Γ} {dstL : BLayout}
    {τ : LayoutTy} {rhs : RExpr Γ τ} {out : mirlite.EvalOutput MSB Γ}
    (h : mirlite.evalRExpr MSB L s dstL rhs = .ok out) : out.state.pc = s.pc := by
  cases rhs
  case binOp op a b =>
    simp only [mirlite.evalRExpr] at h
    split at h
    · cases h
    rename_i out1 h1
    split at h
    case h_2 => cases h
    split at h
    · cases h
    rename_i out2 h2
    split at h
    case h_2 => cases h
    split at h
    · cases h
    simp only [mirlite.EvalResult.ok.injEq] at h
    subst h
    dsimp only
    exact (evalCopy_pc h2).trans (evalCopy_pc h1)
  case alloc len =>
    simp only [mirlite.evalRExpr] at h
    split at h
    · cases h
    rename_i hal
    split at h
    · cases h
    simp only [mirlite.EvalResult.ok.injEq] at h
    subst h
    dsimp only
    exact evalAllocLen_pc hal
  case sliceLen src =>
    simp only [mirlite.evalRExpr] at h
    split at h
    · cases h
    rename_i out1 h1
    split at h
    case h_2 => cases h
    simp only [mirlite.EvalResult.ok.injEq] at h
    subst h
    dsimp only
    exact evalCopy_pc h1
  case subSlice src lo hi =>
    simp only [mirlite.evalRExpr] at h
    split at h
    · cases h
    rename_i out1 h1
    split at h
    case h_2 => cases h
    split at h
    · cases h
    rename_i out2 h2
    split at h
    case h_2 => cases h
    split at h
    · cases h
    rename_i out3 h3
    split at h
    case h_2 => cases h
    split at h
    · cases h
    simp only [mirlite.EvalResult.ok.injEq] at h
    subst h
    dsimp only
    exact (evalCopy_pc h3).trans ((evalCopy_pc h2).trans (evalCopy_pc h1))
  case addrOf loc path =>
    simp only [mirlite.evalRExpr] at h
    split at h
    · cases h
    simp only [mirlite.EvalResult.ok.injEq] at h
    subst h
    rfl
  case ptrOffsetBy src idx inb =>
    simp only [mirlite.evalRExpr] at h
    split at h
    · cases h
    rename_i out1 h1
    split at h
    case h_2 => cases h
    split at h
    · cases h
    rename_i out2 h2
    split at h
    case h_2 => cases h
    split at h
    · cases h
    simp only [mirlite.EvalResult.ok.injEq] at h
    subst h
    dsimp only
    exact (evalCopy_pc h2).trans (evalCopy_pc h1)
  case copy src =>
    exact evalCopy_pc (by simpa [mirlite.evalRExpr] using h)
  all_goals simp only [mirlite.evalRExpr] at h
  all_goals (
    repeat' split at h
    all_goals first
      | (cases h; done)
      | (simp only [mirlite.EvalResult.ok.injEq] at h; subst h
         first
           | rfl
           | simp_all))

theorem allocateBase_pc {Γ : Ctx} {L : mirlite.LayEnv Γ} {s s1 : mirlite.State MSB Γ}
    {τ : LayoutTy} {loc : Local Γ τ} (h : mirlite.allocateBase MSB L s loc = .ok s1) :
    s1.pc = s.pc := by
  simp only [mirlite.allocateBase] at h
  split at h
  · cases h
  · simp only [mirlite.Result.ok.injEq] at h
    rw [← h]

theorem allocateRoot_pc {Γ : Ctx} {L : mirlite.LayEnv Γ} {s : mirlite.State MSB Γ} :
    ∀ {τ : LayoutTy} (p : Place Γ τ) {s1 : mirlite.State MSB Γ},
      mirlite.allocateRoot MSB L s p = .ok s1 → s1.pc = s.pc
  | _, .local loc, _, h => allocateBase_pc h
  | _, .proj base _, _, h => allocateRoot_pc base h
  | _, .deref _, _, h => by simp [mirlite.allocateRoot] at h

theorem ensureRoot_pc {Γ : Ctx} {L : mirlite.LayEnv Γ} {s : mirlite.State MSB Γ} :
    ∀ {τ : LayoutTy} (p : Place Γ τ) {s1 : mirlite.State MSB Γ},
      mirlite.ensureRoot MSB L s p = .ok s1 → s1.pc = s.pc
  | _, .local loc, _, h => by
      simp only [mirlite.ensureRoot] at h
      split at h
      · simp only [mirlite.Result.ok.injEq] at h; rw [← h]
      · exact allocateBase_pc h
  | _, .proj base _, _, h => ensureRoot_pc base h
  | _, .deref q, _, h => ensureRoot_pc q h

theorem preparePlaceAssign_pc {Γ : Ctx} {L : mirlite.LayEnv Γ} {s s1 : mirlite.State MSB Γ}
    {τ : LayoutTy} {dst : Place Γ τ}
    (h : mirlite.preparePlaceAssign MSB L s dst = .ok s1) : s1.pc = s.pc := by
  simp only [mirlite.preparePlaceAssign] at h
  split at h
  · simp only [mirlite.Result.ok.injEq] at h; rw [← h]
  · exact allocateRoot_pc dst h

theorem doAssign_pc {Γ : Ctx} {L : mirlite.LayEnv Γ} {s s' : mirlite.State MSB Γ}
    {τ : LayoutTy} {dst : Place Γ τ} {rhs : RExpr Γ τ}
    (h : mirlite.doAssign MSB L s dst rhs = .ok s') : s'.pc = s.pc + 1 := by
  simp only [mirlite.doAssign] at h
  split at h
  · cases h
  rename_i s1 h1
  split at h
  · cases h
  rename_i out h2
  split at h
  · cases h
  simp only [mirlite.writeResolvedPlace] at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · split at h
    · simp only [mirlite.Result.ok.injEq] at h
      rw [← h]
      show out.state.pc + 1 = s.pc + 1
      rw [evalRExpr_pc h2, preparePlaceAssign_pc h1]
    · cases h
  · cases h

/-- Every successful non-halt step advances the source pc by one. -/
theorem stepStmt_pc {Γ : Ctx} {L : mirlite.LayEnv Γ} {s s' : mirlite.State MSB Γ}
    {stmt : Stmt Γ} (h_nh : stmt ≠ .halt)
    (h : mirlite.stepStmt MSB L s stmt = .ok s') : s'.pc = s.pc + 1 := by
  cases stmt with
  | halt => exact absurd rfl h_nh
  | pushProtectors =>
      simp only [mirlite.stepStmt, mirlite.Result.ok.injEq] at h; rw [← h]
  | popProtectors =>
      simp only [mirlite.stepStmt] at h
      split at h
      · simp only [mirlite.Result.ok.injEq] at h; rw [← h]
      · cases h
  | assign dst rhs => exact doAssign_pc h
  | check discr vals member =>
      simp only [mirlite.stepStmt] at h
      split at h
      · cases h
      rename_i out h_e
      split at h
      · split at h
        · simp only [mirlite.Result.ok.injEq] at h
          rw [← h]
          show out.state.pc + 1 = s.pc + 1
          rw [evalCopy_pc h_e]
        · cases h
      · cases h
  | dealloc dst =>
      simp only [mirlite.stepStmt] at h
      split at h
      · cases h
      rename_i out h_e
      split at h
      · split at h
        · cases h
        · split at h
          · cases h
          · simp only [mirlite.Result.ok.injEq] at h
            rw [← h]
            show out.state.pc + 1 = s.pc + 1
            rw [evalCopy_pc h_e]
      · cases h

/-! ## Prefix compile states -/

/-- The compiler state before statement `i`: the first `i` statements'
    runs, in order. -/
def csAtB {Γ : Ctx} (L : mirlite.LayEnv Γ) : CompilerState → Prog Γ → Nat → CompilerState
  | cs, _, 0 => cs
  | cs, [], _ + 1 => cs
  | cs, stmt :: rest, i + 1 => csAtB L (CheckedCompilerM.run (compileStmtChecked L stmt) cs) rest i

/-- In a program that compiles, statement `i`'s run from the prefix
    state is the next prefix state, and the whole program's run only
    grows it. -/
theorem stmt_in_prog {Γ : Ctx} {L : mirlite.LayEnv Γ} :
    ∀ (prog : Prog Γ) (cs : CompilerState) (i : Nat) (stmt : Stmt Γ) (u : Unit),
      CheckedCompilerM.value (compileStmtsChecked L prog) cs = .ok u →
      prog.get? i = some stmt →
      StateIncr (CheckedCompilerM.run (compileStmtChecked L stmt) (csAtB L cs prog i))
        (CheckedCompilerM.run (compileStmtsChecked L prog) cs) ∧
      csAtB L cs prog (i + 1)
        = CheckedCompilerM.run (compileStmtChecked L stmt) (csAtB L cs prog i)
  | [], _, i, _, _, _, h_get => by simp [List.get?] at h_get
  | s :: rest, cs, i, stmt, u, h_val, h_get => by
      simp only [compileStmtsChecked, CheckedCompilerM.value_bind] at h_val
      split at h_val
      · rename_i _ h_s
        have h_run : CheckedCompilerM.run (compileStmtsChecked L (s :: rest)) cs
            = CheckedCompilerM.run (compileStmtsChecked L rest)
                (CheckedCompilerM.run (compileStmtChecked L s) cs) := by
          simp only [compileStmtsChecked, CheckedCompilerM.run_bind, h_s]
        rw [h_run]
        cases i with
        | zero =>
            have h_eq : s = stmt := by simpa [List.get?] using h_get
            subst h_eq
            exact ⟨CheckedCompilerM.incr _ _, by cases rest <;> rfl⟩
        | succ j =>
            have h_get' : rest.get? j = some stmt := by simpa [List.get?] using h_get
            exact stmt_in_prog rest _ j stmt u h_val h_get'
      · cases h_val

/-! ## The initial invariant -/

theorem InvAtB_initial {Γ : Ctx} (L : mirlite.LayEnv Γ) :
    InvAtB L initialTagRename (mirlite.State.initial MSB Γ) (oseair.State.initial MSB)
      (initialState Γ) := by
  have h_psim : PermSim initialTagRename (mirlite.State.initial MSB Γ).perms
      (oseair.State.initial MSB).perms := by
    -- empty stacks, no protector frames, nothing exposed, no weak tags
    refine ⟨?_, trivial, trivial, Nat.le_refl _, trivial, ?_, ?_⟩
    · intro a
      simp [SB.find?, mirlite.State.initial, oseair.State.initial, MSB,
        PermissionModel.stackedBorrows, AccessPerms.init]
    · intro t t' _ h
      simp [oseair.State.initial, MSB, PermissionModel.stackedBorrows, AccessPerms.init] at h
    · intro t' h
      simp [oseair.State.initial, MSB, PermissionModel.stackedBorrows, AccessPerms.init] at h
  have h_wf : TagRenameWF initialTagRename := by
    -- injective (one point) and fixes the wildcard
    refine ⟨?_, by simp [initialTagRename]⟩
    intro t1 t2 t' h1 h2
    by_cases hc1 : t1 = wildcardTag <;> by_cases hc2 : t2 = wildcardTag <;>
      simp [initialTagRename, hc1, hc2] at h1 h2 ⊢
  have h_tbd : TagRenameBounded initialTagRename (mirlite.State.initial MSB Γ).perms.NextTag
      (oseair.State.initial MSB).perms.NextTag := by
    -- the only mapped tag is 0, and both start at 1
    intro t t' h
    by_cases hc : t = wildcardTag
    · subst hc
      simp [initialTagRename] at h
      subst h
      refine ⟨?_, ?_⟩ <;>
        simp [wildcardTag, mirlite.State.initial, oseair.State.initial,
          PermissionModel.stackedBorrows, AccessPerms.init]
    · simp [initialTagRename, hc] at h
  exact {
    pc := rfl
    lbs := fun loc b h => by
      simp [mirlite.Env.lookup, mirlite.Env.empty, mirlite.State.initial] at h
    mem := fun _ => trivial
    alloc := ⟨rfl, rfl, rfl⟩
    psim := h_psim
    wf_t := h_wf
    tbd := h_tbd
    unmap := fun loc _ => by simp [getPlaceInfo, initialState]
    prb := fun idx reg τ h => by simp [getPlaceInfo, initialState] at h
  }

/-! ## The theorem -/

/-- A statement's simulation: from the byte invariant at any compiler
    state whose run of the statement is in the program, a successful
    source step is matched by target steps re-establishing the invariant
    at the statement's run. Every leaf proves one of these. -/
def StmtSimB {Γ : Ctx} (L : mirlite.LayEnv Γ) (compProg : oseair.Prog) (stmt : Stmt Γ) : Prop :=
  ∀ (ρt : TagRenameMap) (s_mir s_mir' : mirlite.State MSB Γ) (s_osea : oseair.State MSB)
    (cs : CompilerState),
    InvAtB L ρt s_mir s_osea cs →
    CodeIncludedB compProg (CheckedCompilerM.run (compileStmtChecked L stmt) cs) →
    mirlite.stepStmt MSB L s_mir stmt = .ok s_mir' →
    ∃ (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      TagRenameIncr ρt ρt' ∧ oseair.runN MSB n s_osea compProg = .Ok s_osea' ∧
      InvAtB L ρt' s_mir' s_osea' (CheckedCompilerM.run (compileStmtChecked L stmt) cs)

/--
  h_comp : the statement's compilation succeeds
  h_sim : the statement's simulation holds for every non-halt statement in the program
-/
theorem compileB_run_sim {Γ : Ctx} {L : mirlite.LayEnv Γ} {prog : Prog Γ} {cs0 : CompilerState}
    {u : Unit} (h_comp : CheckedCompilerM.value (compileStmtsChecked L prog) cs0 = .ok u)
    (h_sim : ∀ stmt, stmt ∈ prog → stmt ≠ .halt →
      StmtSimB L (CheckedCompilerM.run (compileStmtsChecked L prog) cs0).code stmt) :
    ∀ (n : Nat) (ρt : TagRenameMap) (s_mir s_mir' : mirlite.State MSB Γ)
      (s_osea : oseair.State MSB),
      InvAtB L ρt s_mir s_osea (csAtB L cs0 prog s_mir.pc) →
      mirlite.runN MSB L n s_mir prog = .ok s_mir' →
      ∃ (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (m : Nat),
        TagRenameIncr ρt ρt' ∧
        oseair.runN MSB m s_osea (CheckedCompilerM.run (compileStmtsChecked L prog) cs0).code
          = .Ok s_osea' ∧
        InvAtB L ρt' s_mir' s_osea' (csAtB L cs0 prog s_mir'.pc) := by
  intro n
  induction n with
  | zero =>
      intro ρt s_mir s_mir' s_osea h_inv h_run
      simp only [mirlite.runN, mirlite.Result.ok.injEq] at h_run
      subst h_run
      exact ⟨ρt, s_osea, 0, TagRenameIncr.refl ρt, rfl, h_inv⟩
  | succ n ih =>
      intro ρt s_mir s_mir' s_osea h_inv h_run
      simp only [mirlite.runN] at h_run
      split at h_run
      · simp only [mirlite.Result.ok.injEq] at h_run
        subst h_run
        exact ⟨ρt, s_osea, 0, TagRenameIncr.refl ρt, rfl, h_inv⟩
      · simp only [mirlite.Result.ok.injEq] at h_run
        subst h_run
        exact ⟨ρt, s_osea, 0, TagRenameIncr.refl ρt, rfl, h_inv⟩
      · rename_i stmt h_nh h_get
        split at h_run
        · rename_i s1 h_step
          have h_ne : stmt ≠ .halt := h_nh
          obtain ⟨h_incr, h_next⟩ := stmt_in_prog prog cs0 s_mir.pc stmt u h_comp h_get
          have h_code : CodeIncludedB (CheckedCompilerM.run (compileStmtsChecked L prog) cs0).code
              (CheckedCompilerM.run (compileStmtChecked L stmt) (csAtB L cs0 prog s_mir.pc)) :=
            fun q instr hq hc => by rw [h_incr.code_eq q hq]; exact hc
          obtain ⟨ρt1, s1', n1, h_i1, h_r1, h_inv1⟩ :=
            h_sim stmt (by
              obtain ⟨hi, he⟩ := List.get?_eq_some_iff.mp h_get
              exact he ▸ List.get_mem prog ⟨_, hi⟩) h_ne ρt s_mir s1 s_osea _ h_inv h_code h_step
          rw [← h_next, ← stepStmt_pc h_ne h_step] at h_inv1
          obtain ⟨ρt2, s2', n2, h_i2, h_r2, h_inv2⟩ := ih ρt1 s1 s_mir' s1' h_inv1 h_run
          exact ⟨ρt2, s2', n1 + n2, h_i1.trans h_i2, runN_trans h_r1 h_r2, h_inv2⟩
        · cases h_run

/-- Compiler correctness for the compiler: if `prog` compiles and
    each of its statements has a simulation, every successful source run
    from the initial state is matched by a successful target run from the
    initial state, related by the byte invariant. -/
theorem compile_correct {Γ : Ctx} (L : mirlite.LayEnv Γ) (prog : Prog Γ)
    (compProg : oseair.Prog) (h_comp : compileProg L prog = .ok compProg)
    (h_sim : ∀ stmt, stmt ∈ prog → stmt ≠ .halt → StmtSimB L compProg stmt)
    (n : Nat) {s_mir' : mirlite.State MSB Γ}
    (h_run : mirlite.runN MSB L n (mirlite.State.initial MSB Γ) prog = .ok s_mir') :
    ∃ (ρt : TagRenameMap) (s_osea' : oseair.State MSB) (m : Nat),
      oseair.runN MSB m (oseair.State.initial MSB) compProg = .Ok s_osea' ∧
      InvAtB L ρt s_mir' s_osea' (csAtB L (initialState Γ) prog s_mir'.pc) := by
  simp only [compileProg] at h_comp
  split at h_comp
  · rename_i u h_val
    simp only [Except.ok.injEq] at h_comp
    subst h_comp
    obtain ⟨ρt, s', m, -, h_r, h_inv⟩ :=
      compileB_run_sim h_val h_sim n initialTagRename _ s_mir' _
        (by cases prog <;> exact InvAtB_initial L) h_run
    exact ⟨ρt, s', m, h_r, h_inv⟩
  · cases h_comp

end obseq3.proof
