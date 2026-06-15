import obseq2.compile
import obseq2.mirlite_semantics
import obseq2.permission

namespace obseq2.proof

open obseq2
open obseq2.compile
open obseq2.oseair (Instr Register Rhs Val)

/-- Clear the code map of a compiler state, leaving allocation counters unchanged. -/
def resetCode (cs : CompilerState) : CompilerState :=
  { cs with code := fun _ => none }

/-- Compile the first `stmtIdx` statements of `prog` starting from initial state `cs0`,
    returning the accumulated compiler state when that prefix compiles successfully. -/
def prefixCompileState
  {Γ : Ctx}
  (cs0 : CompilerState)
  (prog : obseq2.Prog Γ)
  (stmtIdx : Nat) : Except CompilerError CompilerState :=
  match CheckedCompilerM.value (compileStmtsChecked (prog.take stmtIdx)) cs0 with
  | .ok _ => .ok (CheckedCompilerM.run (compileStmtsChecked (prog.take stmtIdx)) cs0)
  | .error err => .error err

/-- Witness that `csPrefix` is the compiler state at the start of source statement `stmtIdx`.
    This is meaningful only when compiling the prefix of length `stmtIdx` succeeds. -/
def csAt
  {Γ : Ctx}
  (cs0 : CompilerState)
  (prog : obseq2.Prog Γ)
  (stmtIdx : Nat)
  (csPrefix : CompilerState) : Prop :=
  prefixCompileState cs0 prog stmtIdx = Except.ok csPrefix

/-- Witness that `label` is the target label corresponding to source statement `stmtIdx`,
    computed from the successful prefix compiler state `csPrefix`. -/
def targetLabelAt
  {Γ : Ctx}
  (cs0 : CompilerState)
  (prog : obseq2.Prog Γ)
  (stmtIdx : Nat)
  (csPrefix : CompilerState)
  (label : Nat) : Prop :=
  csAt cs0 prog stmtIdx csPrefix ∧
  label = csPrefix.nextLabel

/-- Compile an entire program starting from `cs0`, returning the target code map when
    whole-program compilation succeeds. -/
def compileProgFrom
  {Γ : Ctx}
  (cs0 : CompilerState)
  (prog : obseq2.Prog Γ) : Except CompilerError obseq2.oseair.Prog :=
  compileProgFromChecked cs0 prog

/-- A place is supported in source state `s` when it already resolves to a concrete
    location. Direct-local writes are handled separately by `preparePlaceAssign`, so
    this predicate captures the non-fresh branch. -/
def SupportedPlace
  {Γ : Ctx} {τ : LayoutTy}
  (s : obseq2.mirlite.State PermissionModel.stackedBorrows Γ)
  (p : Place Γ τ) : Prop :=
  ∃ resolved, obseq2.mirlite.resolvePlace? s p = some resolved

/-- A statement is supported in source state `s` when either it is trivially enabled
    (`halt`), it writes directly to a local (which may allocate lazily), or its
    destination place already resolves in `s`. -/
def SupportedStmt
  {Γ : Ctx}
  (s : obseq2.mirlite.State PermissionModel.stackedBorrows Γ)
  (stmt : Stmt Γ) : Prop :=
  match stmt with
  | .halt => True
  | .assign (.local _) _ => True
  | .assign dst _ => SupportedPlace s dst

theorem csAt_value_ok
  {Γ : Ctx}
  {cs0 : CompilerState}
  {prog : obseq2.Prog Γ}
  {stmtIdx : Nat}
  {csPrefix : CompilerState}
  (h_csAt : csAt cs0 prog stmtIdx csPrefix) :
  CheckedCompilerM.value (compileStmtsChecked (prog.take stmtIdx)) cs0 = Except.ok () := by
  unfold csAt prefixCompileState at h_csAt
  cases h_val : CheckedCompilerM.value (compileStmtsChecked (prog.take stmtIdx)) cs0 with
  | ok u =>
    cases u
    rfl
  | error err =>
    simp [h_val] at h_csAt

theorem csAt_run_eq
  {Γ : Ctx}
  {cs0 : CompilerState}
  {prog : obseq2.Prog Γ}
  {stmtIdx : Nat}
  {csPrefix : CompilerState}
  (h_csAt : csAt cs0 prog stmtIdx csPrefix) :
  CheckedCompilerM.run (compileStmtsChecked (prog.take stmtIdx)) cs0 = csPrefix := by
  unfold csAt prefixCompileState at h_csAt
  cases h_val : CheckedCompilerM.value (compileStmtsChecked (prog.take stmtIdx)) cs0 with
  | ok u =>
    cases u
    simpa [h_val] using h_csAt
  | error err =>
    simp [h_val] at h_csAt

theorem compileProgFrom_run_eq
  {Γ : Ctx}
  {cs0 : CompilerState}
  {prog : obseq2.Prog Γ}
  {compProg : obseq2.oseair.Prog}
  (h_comp : compileProgFrom cs0 prog = Except.ok compProg) :
  compProg = (CheckedCompilerM.run (compileStmtsChecked prog) cs0).code := by
  unfold compileProgFrom compileProgFromChecked at h_comp
  cases h_val : CheckedCompilerM.value (compileStmtsChecked prog) cs0 with
  | ok u =>
    cases u
    simpa [h_val] using h_comp.symm
  | error err =>
    simp [h_val] at h_comp

theorem take_succ_eq_take_append_get
    {xs : List α} {n : Nat} {x : α}
    (h_get : xs.get? n = some x) :
    xs.take (n + 1) = xs.take n ++ [x] := by
  induction xs generalizing n with
  | nil =>
      cases n <;> cases h_get
  | cons y ys ih =>
      cases n with
      | zero =>
          simp [List.get?] at h_get
          cases h_get
          simp
      | succ n =>
          simp [List.get?] at h_get ⊢
          exact ih h_get

theorem drop_eq_get_cons
    {xs : List α} {n : Nat} {x : α}
    (h_get : xs.get? n = some x) :
    xs.drop n = x :: xs.drop (n + 1) := by
  induction xs generalizing n with
  | nil =>
      cases n <;> cases h_get
  | cons y ys ih =>
      cases n with
      | zero =>
          simp at h_get
          cases h_get
          simp
      | succ n =>
          simp [List.get?, List.drop] at h_get ⊢
          exact ih h_get

theorem compileStmts_append
    {Γ : Ctx}
    (xs ys : obseq2.Prog Γ) (cs : CompilerState) :
    CheckedCompilerM.value (compileStmtsChecked xs) cs = Except.ok () →
    CheckedCompilerM.value (compileStmtsChecked (xs ++ ys)) cs =
      CheckedCompilerM.value (compileStmtsChecked ys)
        (CheckedCompilerM.run (compileStmtsChecked xs) cs) := by
  induction xs generalizing cs with
  | nil =>
      intro _
      simp [compileStmtsChecked]
  | cons stmt rest ih =>
      intro h_ok
      cases h_stmt : CheckedCompilerM.value (compileStmtChecked stmt) cs with
      | error err =>
          simp [compileStmtsChecked, h_stmt] at h_ok
      | ok stmtOut =>
          have h_rest_ok :
              CheckedCompilerM.value (compileStmtsChecked rest)
                (CheckedCompilerM.run (compileStmtChecked stmt) cs) = Except.ok () := by
            simpa [compileStmtsChecked, h_stmt] using h_ok
          simpa [compileStmtsChecked, h_stmt] using
            ih (cs := CheckedCompilerM.run (compileStmtChecked stmt) cs) h_rest_ok

theorem compileStmts_append_run
    {Γ : Ctx}
    (xs ys : obseq2.Prog Γ) (cs : CompilerState) :
    CheckedCompilerM.value (compileStmtsChecked xs) cs = Except.ok () →
    CheckedCompilerM.run (compileStmtsChecked (xs ++ ys)) cs =
      CheckedCompilerM.run (compileStmtsChecked ys)
        (CheckedCompilerM.run (compileStmtsChecked xs) cs) := by
  induction xs generalizing cs with
  | nil =>
      intro _
      simp [compileStmtsChecked]
  | cons stmt rest ih =>
      intro h_ok
      cases h_stmt : CheckedCompilerM.value (compileStmtChecked stmt) cs with
      | error err =>
          simp [compileStmtsChecked, h_stmt] at h_ok
      | ok stmtOut =>
          have h_rest_ok :
              CheckedCompilerM.value (compileStmtsChecked rest)
                (CheckedCompilerM.run (compileStmtChecked stmt) cs) = Except.ok () := by
            simpa [compileStmtsChecked, h_stmt] using h_ok
          simpa [compileStmtsChecked, h_stmt] using
            ih (cs := CheckedCompilerM.run (compileStmtChecked stmt) cs) h_rest_ok

theorem prefixCompileState_succ
    {Γ : Ctx}
    {cs0 : CompilerState}
    {prog : obseq2.Prog Γ}
    {stmtIdx : Nat}
    {stmt : Stmt Γ}
    {csPrefix : CompilerState}
    {stmtOut : ResultWithEvidence Unit (fun _ => StmtEvidence stmt)}
    (h_prefix : csAt cs0 prog stmtIdx csPrefix)
    (h_get : prog.get? stmtIdx = some stmt)
    (h_stmt : CheckedCompilerM.value (compileStmtChecked stmt) csPrefix = Except.ok stmtOut) :
    prefixCompileState cs0 prog (Nat.succ stmtIdx) =
      Except.ok (CheckedCompilerM.run (compileStmtChecked stmt) csPrefix) := by
  have h_prefix_ok := csAt_value_ok h_prefix
  have h_prefix_run := csAt_run_eq h_prefix
  rw [prefixCompileState, take_succ_eq_take_append_get h_get]
  have h_val :
      CheckedCompilerM.value (compileStmtsChecked (prog.take stmtIdx ++ [stmt])) cs0 = Except.ok () := by
    have h_append := compileStmts_append (xs := prog.take stmtIdx) (ys := [stmt]) cs0 h_prefix_ok
    simpa [compileStmtsChecked, h_stmt, h_prefix_run] using h_append
  have h_run :
      CheckedCompilerM.run (compileStmtsChecked (prog.take stmtIdx ++ [stmt])) cs0 =
        CheckedCompilerM.run (compileStmtChecked stmt) csPrefix := by
    have h_append := compileStmts_append_run (xs := prog.take stmtIdx) (ys := [stmt]) cs0 h_prefix_ok
    simpa [compileStmtsChecked, h_stmt, h_prefix_run] using h_append
  simp [h_val, h_run]

theorem compileProgFrom_code_eq_compileStmt
    {Γ : Ctx}
    (cs0 : CompilerState) (prog : obseq2.Prog Γ)
    (compProg : obseq2.oseair.Prog)
    (h_comp : compileProgFrom cs0 prog = Except.ok compProg)
    {stmtIdx : Nat} {stmt : Stmt Γ}
    {csPrefix : CompilerState}
    {stmtOut : ResultWithEvidence Unit (fun _ => StmtEvidence stmt)}
    (h_prefix : csAt cs0 prog stmtIdx csPrefix)
    (h_get : prog.get? stmtIdx = some stmt)
    (h_stmt : CheckedCompilerM.value (compileStmtChecked stmt) csPrefix = Except.ok stmtOut)
    {q : Nat}
    (h_lt : q < (CheckedCompilerM.run (compileStmtChecked stmt) csPrefix).nextLabel) :
    compProg q =
      (CheckedCompilerM.run (compileStmtChecked stmt) csPrefix).code q := by
  let csStmt := CheckedCompilerM.run (compileStmtChecked stmt) csPrefix
  have h_csStmt : csAt cs0 prog (Nat.succ stmtIdx) csStmt := by
    simpa [csStmt] using prefixCompileState_succ h_prefix h_get h_stmt
  have h_csStmt_ok := csAt_value_ok h_csStmt
  have h_csStmt_run := csAt_run_eq h_csStmt
  have h_prog_run :
      CheckedCompilerM.run (compileStmtsChecked prog) cs0 =
        CheckedCompilerM.run (compileStmtsChecked (prog.drop (Nat.succ stmtIdx))) csStmt := by
    have h_append :=
      compileStmts_append_run
        (xs := prog.take (Nat.succ stmtIdx))
        (ys := prog.drop (Nat.succ stmtIdx))
        cs0 h_csStmt_ok
    simpa [List.take_append_drop (Nat.succ stmtIdx) prog, h_csStmt_run, csStmt] using h_append
  have h_comp_run := compileProgFrom_run_eq h_comp
  calc
    compProg q = (CheckedCompilerM.run (compileStmtsChecked prog) cs0).code q := by
      simp [h_comp_run]
    _ = (CheckedCompilerM.run (compileStmtsChecked (prog.drop (Nat.succ stmtIdx))) csStmt).code q := by
      simp [h_prog_run]
    _ = csStmt.code q := by
      exact (CheckedCompilerM.incr (compileStmtsChecked (prog.drop (Nat.succ stmtIdx))) csStmt).code_eq q h_lt
    _ = (CheckedCompilerM.run (compileStmtChecked stmt) csPrefix).code q := by
      rfl

/- Supporting lemmas needed later:
- `freshReg` preserves all old register bounds and introduces one fresh bounded register.
- `emit` preserves `InstrsRegsBelow` when the appended fragment is bounded.
- `cleanupInstrs` only emits `Die` instructions over already bounded registers.
- `placeToReg` and `placeToBorrowReg` preserve `CompilerStateWF`.
- `compileRExprTo`, `compileRExpr`, `compileStmt`, and `prefixCompileState` preserve `CompilerStateWF`.
- direct local assignment emits the allocation that establishes the local pointer register.
- successful `targetLabelAt` witnesses agree with actual execution of the compiled prefix.
- End-of-write obligation: for every `RStore ty src ptr` or `CStore ty vals ptr` emitted by the
  compiler, `vals.length = typeSize ty` and the destination pointer satisfies
  `offset + typeSize ty ≤ size`. This is derived from MIRLite's type-system guarantee
  (`Place.offset + blockSize τ ≤ blockSize σ`) and must be proved as part of `CompiledWF`.
  `writeThroughPtr` only checks `addr >= base + size` (start-of-write), matching MIRLite's own
  lack of an explicit bounds check; the end-of-write safety is a static obligation, not a
  runtime one.
-/
/-- A register whose numeric index is strictly less than `bound`. -/
def RegisterBelow (bound : Nat) : Register → Prop
  | .R idx => idx < bound

/-- All registers mentioned in an `Rhs` have index strictly less than `bound`. -/
def RhsRegsBelow (bound : Nat) : Rhs → Prop
  | .Load _ reg => RegisterBelow bound reg
  | .Alloc _ => True
  | .BorOffset base _ => RegisterBelow bound base
  | .MutBorOffset base _ => RegisterBelow bound base
  | .CopyOffset base _ => RegisterBelow bound base
  | .BinOp lhs rhs => RegisterBelow bound lhs ∧ RegisterBelow bound rhs

/-- All registers mentioned in an `Instr` have index strictly less than `bound`. -/
def InstrRegsBelow (bound : Nat) : Instr → Prop
  | .Assgn reg rhs => RegisterBelow bound reg ∧ RhsRegsBelow bound rhs
  | .RStore _ src ptr => RegisterBelow bound src ∧ RegisterBelow bound ptr
  | .CStore _ _ ptr => RegisterBelow bound ptr
  | .Memcpy dst src _ => RegisterBelow bound dst ∧ RegisterBelow bound src
  | .Die reg => RegisterBelow bound reg
  | .Halt => True

/-- Every populated code slot satisfies `InstrRegsBelow bound`. -/
def CodeRegsBelow (bound : Nat) (code : Nat → Option Instr) : Prop :=
  ∀ pc instr, code pc = some instr → InstrRegsBelow bound instr

/-- The instruction does not write any register below `bound`.
    Only `Assgn` writes a register; all other instructions leave registers unchanged. -/
def InstrPreservesRegsBelow (bound : Nat) : Instr → Prop
  | .Assgn reg _ => ¬ RegisterBelow bound reg
  | _            => True

/-- RHS forms that do not mutate target memory.
    `Alloc` is excluded because it advances the allocator-backed memory state. -/
def RhsPreservesMem : Rhs → Prop
  | .Alloc _ => False
  | _        => True

/-- Instructions that do not mutate target memory and advance the PC when they succeed.
    This is tailored to emitted straight-line fragments: stores and `Memcpy` write memory,
    `Assgn Alloc` allocates memory, and `Halt` does not advance. -/
def InstrPreservesMem : Instr → Prop
  | .Assgn _ rhs => RhsPreservesMem rhs
  | .RStore _ _ _ => False
  | .CStore _ _ _ => False
  | .Memcpy _ _ _ => False
  | .Die _ => True
  | .Halt => False

theorem evalRhsWith_preserves_mem
    {A : oseair.AllocatorSpec} {s s1 : oseair.State}
    {rhs : Rhs} {vals : List Val} {ty : obseq.TyVal}
    (h_rhs : RhsPreservesMem rhs)
    (h_eval : oseair.evalRhsWith A s rhs = oseair.RhsResult.Ok vals ty s1) :
    s1.mem = s.mem := by
  cases rhs <;> simp [RhsPreservesMem, oseair.evalRhsWith] at h_rhs h_eval
  all_goals
    repeat (split at h_eval <;> try contradiction)
    cases h_eval
    rfl

theorem step_preserves_mem_and_pc
    {s s' : oseair.State} {prog : oseair.Prog} {instr : Instr}
    (h_instr : prog s.pc = some instr)
    (h_mem : InstrPreservesMem instr)
    (h_step : oseair.step s prog = oseair.Result.Ok s') :
    s'.mem = s.mem ∧ s'.pc = s.pc + 1 := by
  cases instr with
  | Assgn reg rhs =>
      simp [oseair.step, oseair.stepWith, h_instr, InstrPreservesMem] at h_step h_mem
      split at h_step
      · rename_i vals ty s1 h_eval
        cases h_step
        constructor
        · change s1.mem = s.mem
          exact evalRhsWith_preserves_mem h_mem h_eval
        · rfl
      · contradiction
  | RStore ty src ptr =>
      cases h_mem
  | CStore ty vals ptr =>
      cases h_mem
  | Memcpy dst src ty =>
      cases h_mem
  | Die reg =>
      simp [oseair.step, oseair.stepWith, h_instr] at h_step
      repeat (split at h_step <;> try contradiction)
      cases h_step
      constructor <;> rfl
  | Halt =>
      cases h_mem

theorem runN_preserves_mem
    {n : Nat} {s s' : oseair.State} {prog : oseair.Prog}
    (h_run : oseair.runN n s prog = oseair.Result.Ok s')
    (h_mem : ∀ (k : Fin n) instr,
      prog (s.pc + k.1) = some instr → InstrPreservesMem instr) :
    s'.mem = s.mem := by
  induction n generalizing s with
  | zero =>
      simp at h_run
      cases h_run
      rfl
  | succ n ih =>
      cases h_step : oseair.step s prog with
      | Err msg =>
          simp [oseair.runN_succ, h_step] at h_run
      | Ok s1 =>
          have h_run_tail : oseair.runN n s1 prog = oseair.Result.Ok s' := by
            simpa [oseair.runN_succ, h_step] using h_run
          cases h_prog : prog s.pc with
          | none =>
              simp [oseair.step, oseair.stepWith, h_prog] at h_step
              cases h_step
              apply ih h_run_tail
              intro k instr h_prog'
              exact h_mem ⟨k.1, Nat.lt_trans k.2 (Nat.lt_succ_self n)⟩ instr h_prog'
          | some instr =>
              have h_step_props := step_preserves_mem_and_pc h_prog
                (h_mem ⟨0, Nat.succ_pos n⟩ instr (by simpa)) h_step
              have h_tail_mem : s'.mem = s1.mem := by
                apply ih h_run_tail
                intro k instr' h_prog'
                have hk : k.1 + 1 < n + 1 := Nat.succ_lt_succ k.2
                exact h_mem ⟨k.1 + 1, hk⟩ instr' (by
                  simpa [h_step_props.2, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
                    using h_prog')
              exact h_tail_mem.trans h_step_props.1

/-- A well-formed compiler state:
    every emitted instruction only references registers below `nextReg`.
    Locals are no longer assigned fixed reserved registers; their base registers
    live in `CompilerState.placeRegMap`. -/
def CompilerStateWF (_Γ : Ctx) (cs : CompilerState) : Prop :=
  CodeRegsBelow cs.nextReg cs.code

/-- Register `reg` in `regMap` holds a pointer value with the given `base` address,
    `offset`, `size`, and `tag`. -/
def PtrRegisterEntry
  (regMap : obseq2.oseair.RegMap)
  (reg : Register)
  (base offset size : Word)
  (tag : Tag) : Prop :=
  obseq2.oseair.RegMap.lookup regMap reg = some (obseq.TyVal.PTy, [Val.Ptr base offset size tag])

/-- Placeholder for target local readiness under lazy allocation.
    The actual bound-local correspondence is carried by `LocalBindingSim`; unbound locals
    intentionally do not have a target allocation yet. -/
def TargetLocalsReady (_Γ : Ctx) (_s_osea : obseq2.oseair.State) : Prop :=
  True

/-- Address rename maps grow monotonically: any source address already mapped by
    `ρa` is mapped to the same target address by `ρa'`. -/
def AddrRenameIncr (ρa ρa' : AddrRenameMap) : Prop :=
  ∀ addr addr', ρa addr = some addr' → ρa' addr = some addr'

/-- Tag rename maps grow monotonically: any source tag already mapped by `ρt` is
    mapped to the same target tag by `ρt'`. -/
def TagRenameIncr (ρt ρt' : TagRenameMap) : Prop :=
  ∀ tag tag', ρt tag = some tag' → ρt' tag = some tag'

namespace AddrRenameIncr

theorem refl (ρa : AddrRenameMap) : AddrRenameIncr ρa ρa :=
  fun _ _ h => h

theorem trans {ρa ρa' ρa'' : AddrRenameMap}
    (h₁ : AddrRenameIncr ρa ρa') (h₂ : AddrRenameIncr ρa' ρa'') :
    AddrRenameIncr ρa ρa'' :=
  fun addr addr' h => h₂ addr addr' (h₁ addr addr' h)

end AddrRenameIncr

namespace TagRenameIncr

theorem refl (ρt : TagRenameMap) : TagRenameIncr ρt ρt :=
  fun _ _ h => h

theorem trans {ρt ρt' ρt'' : TagRenameMap}
    (h₁ : TagRenameIncr ρt ρt') (h₂ : TagRenameIncr ρt' ρt'') :
    TagRenameIncr ρt ρt'' :=
  fun tag tag' h => h₂ tag tag' (h₁ tag tag' h)

end TagRenameIncr

/- Supporting lemmas needed later:
- direct local assignment records the allocated target register in `placeRegMap`.
- direct source allocation updates `LocalBindingSim` only at the assigned local.
- target-side pointer tags created by compiled `ref` fragments respect the tag rename map.
-/
/-- Every local reached while structurally traversing `p` already has a compiler
  mapping in `placeRegMap`. This is the compile-side availability condition needed
  for `placeToRegChecked` to avoid `.missingLocal`. -/
def PlaceInputsMapped
  {Γ : Ctx}
  (cs : CompilerState) : {τ : LayoutTy} → Place Γ τ → Prop
  | _, .local loc =>
    ∃ reg layout, getPlaceInfo cs loc.idx.1 = some (reg, layout)
  | _, .proj base _ =>
    PlaceInputsMapped cs base
  | _, .deref ptrPlace =>
    PlaceInputsMapped cs ptrPlace

/-- Simulation relation between source local bindings and target register values.
    For every local `loc` with source binding `binding`, the compiler state maps that
    local's base index to a target register, and the target holds a pointer in that
    register whose base and tag are the images of `binding.addr` and `binding.tag`
    under the rename maps `ρa` and `ρt` respectively. -/
def LocalBindingSim
  {Γ : Ctx}
  (ρa : AddrRenameMap)
  (ρt : TagRenameMap)
  (env : obseq2.mirlite.Env Γ)
  (s_osea : obseq2.oseair.State)
  (cs : CompilerState) : Prop :=
  ∀ {τ : LayoutTy} (loc : Local Γ τ) (binding : obseq2.mirlite.Binding),
    obseq2.mirlite.Env.lookup env loc = some binding →
    ∃ reg base tag,
      getPlaceInfo cs loc.idx.1 = some (reg, τ) ∧
      PtrRegisterEntry s_osea.reg reg base 0 (blockSize τ) tag ∧
      ρa binding.addr = some base ∧
      ρt binding.tag = some tag

/-- A resolved local place is enough to prove checked local lowering succeeds once the
    stronger simulation invariant supplies the corresponding `getPlaceInfo` entry. -/
theorem placeToRegChecked_local_ok_of_resolvePlace
    {Γ : Ctx} {τ : LayoutTy}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir : obseq2.mirlite.State PermissionModel.stackedBorrows Γ}
    {s_osea : oseair.State}
    {cs : CompilerState}
    {kind : RefKind}
    {loc : Local Γ τ}
    {resolved : obseq2.mirlite.PlaceRes}
    (h_lbs : LocalBindingSim ρa ρt s_mir.env s_osea cs)
    (h_res : obseq2.mirlite.resolvePlace? s_mir (.local loc) = some resolved) :
    ∃ placeOut,
      CheckedCompilerM.value (placeToRegChecked kind (.local loc)) cs = Except.ok placeOut := by
  cases h_lookup : obseq2.mirlite.Env.lookup s_mir.env loc with
  | none =>
      simp [obseq2.mirlite.resolvePlace?, h_lookup] at h_res
  | some binding =>
      rcases h_lbs loc binding h_lookup with ⟨reg, base, tag, h_placeInfo, _, _, _⟩
      exact placeToRegChecked_local_ok_of_getPlaceInfo
        (kind := kind) (loc := loc) (cs := cs) (reg := reg) (layout := τ) h_placeInfo

/-- Source-side resolvability plus `LocalBindingSim` implies the weaker compile-side
    availability invariant `PlaceInputsMapped` for every local leaf of the place. -/
theorem placeInputsMapped_of_localBindingSim_resolvePlace
  {Γ : Ctx} {τ : LayoutTy}
  {ρa : AddrRenameMap} {ρt : TagRenameMap}
  {s_mir : obseq2.mirlite.State PermissionModel.stackedBorrows Γ}
  {s_osea : oseair.State}
  {cs : CompilerState}
  {p : Place Γ τ}
  {resolved : obseq2.mirlite.PlaceRes}
  (h_lbs : LocalBindingSim ρa ρt s_mir.env s_osea cs)
  (h_res : obseq2.mirlite.resolvePlace? s_mir p = some resolved) :
  PlaceInputsMapped cs p := by
induction p generalizing resolved with
| «local» loc =>
    cases h_lookup : obseq2.mirlite.Env.lookup s_mir.env loc with
    | none =>
        simp [obseq2.mirlite.resolvePlace?, h_lookup] at h_res
    | some binding =>
        rcases h_lbs loc binding h_lookup with ⟨reg, base, tag, h_placeInfo, _, _, _⟩
        exact ⟨reg, _, h_placeInfo⟩
| proj base path ih =>
    cases h_base : obseq2.mirlite.resolvePlace? s_mir base with
    | none =>
        simp [obseq2.mirlite.resolvePlace?, h_base] at h_res
    | some resolvedBase =>
        exact ih h_base
| deref ptrPlace ih =>
    cases h_ptr : obseq2.mirlite.resolvePlace? s_mir ptrPlace with
    | none =>
        simp [obseq2.mirlite.resolvePlace?, h_ptr] at h_res
    | some resolvedPtr =>
        exact ih h_ptr

/-- Projection lowering cannot fail once the base place has already lowered
    successfully; the proof just reconstructs the appropriate evidence for the
    zero-offset and nonzero-offset cases. -/
theorem placeToRegChecked_proj_ok_of_baseOk
    {Γ : Ctx} {σ τ : LayoutTy}
    {kind : RefKind} {cs : CompilerState}
    {base : Place Γ σ} {path : PathTo σ τ}
    (baseOut : ResultWithEvidence PtrResult (PlaceToRegEvidence kind base))
    (h_baseOut : CheckedCompilerM.value (placeToRegChecked kind base) cs = Except.ok baseOut) :
    ∃ placeOut,
      CheckedCompilerM.value (placeToRegChecked kind (.proj base path)) cs = Except.ok placeOut := by
  by_cases h_offset : pathOffset path = 0
  · let baseRes := baseOut.result
    refine ⟨{
      result := baseRes,
      evidence := PlaceToRegEvidence.projZero base path baseRes baseOut.evidence h_offset
    }, ?_⟩
    simp [placeToRegChecked, h_baseOut, h_offset, baseRes]
  · let tmpReg := CompilerM.value freshRegM (CheckedCompilerM.run (placeToRegChecked kind base) cs)
    refine ⟨{
      result := { reg := tmpReg, cleanup := baseOut.result.cleanup ++ [tmpReg] },
      evidence := PlaceToRegEvidence.projOffset base path baseOut.result tmpReg
        baseOut.evidence h_offset
    }, ?_⟩
    simp [placeToRegChecked, h_baseOut, h_offset, tmpReg]

/-- Dereference lowering cannot fail once the shared pointer subplace has already
    lowered successfully; the proof reuses the generated pointer result and rebuilds
    the dereference evidence. -/
theorem placeToRegChecked_deref_ok_of_ptrOk
    {Γ : Ctx} {σ : LayoutTy}
    {kind : RefKind} {cs : CompilerState}
    {ptrPlace : Place Γ (obseq.LayoutTy.PtrL σ)}
    (ptrOut : ResultWithEvidence PtrResult (PlaceToRegEvidence RefKind.Shared ptrPlace))
    (h_ptrOut : CheckedCompilerM.value (placeToRegChecked RefKind.Shared ptrPlace) cs = Except.ok ptrOut) :
    ∃ placeOut,
      CheckedCompilerM.value (placeToRegChecked kind (.deref ptrPlace)) cs = Except.ok placeOut := by
  let loadedReg := CompilerM.value freshRegM
    (CheckedCompilerM.run (placeToRegChecked RefKind.Shared ptrPlace) cs)
  refine ⟨{
    result := { reg := loadedReg, cleanup := [loadedReg] },
    evidence := PlaceToRegEvidence.deref ptrPlace ptrOut.result loadedReg ptrOut.evidence
  }, ?_⟩
  simp [placeToRegChecked, h_ptrOut, loadedReg]

/-- The proof-facing checked place lowering succeeds whenever the compiler state already
    contains mappings for every local leaf that can be reached while traversing `p`. -/
theorem placeToRegChecked_ok_of_placeInputsMapped
    {Γ : Ctx} {τ : LayoutTy}
    {cs : CompilerState}
    {kind : RefKind}
    {p : Place Γ τ}
    (h_mapped : PlaceInputsMapped cs p) :
    ∃ placeOut,
      CheckedCompilerM.value (placeToRegChecked kind p) cs = Except.ok placeOut := by
  induction p generalizing kind with
  | «local» loc =>
      rcases h_mapped with ⟨reg, layout, h_lookup⟩
      exact placeToRegChecked_local_ok_of_getPlaceInfo
        (kind := kind) (loc := loc) (cs := cs) (reg := reg) (layout := layout) h_lookup
  | proj base path ih =>
      rcases ih (kind := kind) h_mapped with ⟨baseOut, h_baseOut⟩
      exact placeToRegChecked_proj_ok_of_baseOk (kind := kind) (cs := cs)
        (base := base) (path := path) baseOut h_baseOut
  | deref ptrPlace ih =>
      rcases ih (kind := RefKind.Shared) h_mapped with ⟨ptrOut, h_ptrOut⟩
      exact placeToRegChecked_deref_ok_of_ptrOk (kind := kind) (cs := cs)
        (ptrPlace := ptrPlace) ptrOut h_ptrOut

/-- Compatibility wrapper: source-side resolvability together with `LocalBindingSim`
    is first downgraded to `PlaceInputsMapped`, then the purely compile-side success
    theorem is applied. -/
theorem placeToRegChecked_ok_of_resolvePlace
    {Γ : Ctx} {τ : LayoutTy}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir : obseq2.mirlite.State PermissionModel.stackedBorrows Γ}
    {s_osea : oseair.State}
    {cs : CompilerState}
    {kind : RefKind}
    {p : Place Γ τ}
    {resolved : obseq2.mirlite.PlaceRes}
    (h_lbs : LocalBindingSim ρa ρt s_mir.env s_osea cs)
    (h_res : obseq2.mirlite.resolvePlace? s_mir p = some resolved) :
    ∃ placeOut,
      CheckedCompilerM.value (placeToRegChecked kind p) cs = Except.ok placeOut := by
  exact placeToRegChecked_ok_of_placeInputsMapped
    (cs := cs)
    (kind := kind)
    (p := p)
    (placeInputsMapped_of_localBindingSim_resolvePlace h_lbs h_res)

/- Supporting lemmas needed later:
- source reads from allocated blocks correspond to target reads at renamed addresses.
- source writes preserve `MemValSim` at unaffected addresses.
- `ptrVal` stored by `ref` corresponds to `Val.Ptr` in the target under the rename maps.
-/
/-- Pointwise simulation between a source `MemValue` and a target `Val`.
    With the concrete pointer representation (Option B), env is no longer needed here:
    - `undef`   ↔ `Undef`
    - `word v`  ↔ `Dat v`       (value equality)
    - `ptrVal b o s t` ↔ `Ptr b' o s t'`  (base renamed by ρa, tag renamed by ρt,
                                             offset and size equal) -/
def MemValSim
  (ρa : AddrRenameMap)
  (ρt : TagRenameMap) : obseq2.mirlite.MemValue → Val → Prop
  | .undef,           .Undef             => True
  | .word v,          .Dat v'            => v' = v
  | .ptrVal b o s t,  .Ptr b' o' s' t'  =>
      ρa b = some b' ∧ o' = o ∧ s' = s ∧ ρt t = some t'
  | _, _                                 => False

theorem MemValSim.rename_mono
    {ρa ρa' : AddrRenameMap} {ρt ρt' : TagRenameMap}
    {mv : obseq2.mirlite.MemValue} {v : Val}
    (h_addr : AddrRenameIncr ρa ρa')
    (h_tag : TagRenameIncr ρt ρt')
    (h_sim : MemValSim ρa ρt mv v) :
    MemValSim ρa' ρt' mv v := by
  cases mv <;> cases v <;> simp [MemValSim] at h_sim ⊢
  · exact h_sim
  · rcases h_sim with ⟨h_base, h_off, h_size, h_tag_old⟩
    exact ⟨h_addr _ _ h_base, h_off, h_size, h_tag _ _ h_tag_old⟩

/- Supporting lemmas needed later:
- compiled `Alloc`, `Memcpy`, `CStore`, and `RStore` fragments preserve or extend
  `SourceMemSim` at renamed addresses.
-/
/-- For every address/value pair present in the source memory, there exists a corresponding
    renamed address in the target memory whose value is related by `MemValSim`.
    `env` is no longer a parameter — `MemValSim` is self-contained with the concrete pointer repr. -/
def SourceMemSim
  (ρa : AddrRenameMap)
  (ρt : TagRenameMap)
  (mem_mir : obseq2.mirlite.Mem)
  (mem_osea : obseq2.oseair.Mem) : Prop :=
  ∀ addr value,
    obseq2.mirlite.Mem.find? mem_mir addr = some value →
    ∃ addr' value',
      ρa addr = some addr' ∧
      obseq2.oseair.Mem.find? mem_osea addr' = some value' ∧
      MemValSim ρa ρt value value'

/- Blocking factors for stronger invariants:
- a generic permission-state relation is not definable yet because the target runtime stores
  concrete stacked-borrows permissions in `oseair.State`, while `mirlite.State` is abstract
  over `PermissionModel`; this scaffold therefore specializes the source side to
  `PermissionModel.stackedBorrows`.
- a bidirectional memory relation is premature until fresh allocation extends the address
  rename map in lockstep with target allocation.
- temp-register ownership produced by `placeToReg` and `placeToBorrowReg` is not included in
  `CompilerInv` yet because the required preservation lemmas are still missing.
-/
/-- The main simulation invariant between a source `mirlite` state and a target `oseair` state.
    Asserts:
    - Label agreement: the target runtime `pc` equals the compile-time target label
      for the current source statement index via a successful prefix compile witness.
    - Well-formedness of the compiled prefix's compiler state witness.
    - Source local bindings are simulated by target registers (`LocalBindingSim`);
      unbound locals have not been allocated yet.
    - Source memory is forward-simulated in target memory (`SourceMemSim`).
    - Permission states are equal. -/
def CompilerInv
  {Γ : Ctx}
  (cs0 : CompilerState)
  (prog : obseq2.Prog Γ)
  (ρa : AddrRenameMap)
  (ρt : TagRenameMap)
  (s_mir : obseq2.mirlite.State PermissionModel.stackedBorrows Γ)
  (s_osea : obseq2.oseair.State) : Prop :=
  ∃ csPrefix,
    targetLabelAt cs0 prog s_mir.pc csPrefix s_osea.pc ∧
    CompilerStateWF Γ csPrefix ∧
    TargetLocalsReady Γ s_osea ∧
    LocalBindingSim ρa ρt s_mir.env s_osea csPrefix ∧
    SourceMemSim ρa ρt s_mir.mem s_osea.mem ∧
    s_osea.ap = s_mir.perms ∧
    PermissionModel.stackedBorrows.WellFormed s_mir.perms

-- Register `reg` holds a pointer to `resolved`, and the tag stored there has
-- mutable write permission at the target address in `s_ap`.
--
-- The tag t' in the register is NOT necessarily ρt(resolved.tag):
--   local   : t' = ρt(resolved.tag), from LocalBindingSim via `placeRegMap`.
--   proj    : t' is a fresh borrow created by MutBorOffset/BorOffset; it has
--             write permission in s_ap because sb_ref just pushed it onto the stack.
--   deref   : t' is whatever was stored in the pointer cell; writability comes
--             from the reference creation that stored it.
-- In all cases, write permission is captured by the `useMut` conjunct rather than
-- a static tag-rename relation.
def PlaceRegReady
    (ρa : AddrRenameMap)
    (s_ap : AccessPerms)
    (regMap : oseair.RegMap)
    (reg : Register)
    (resolved : obseq2.mirlite.PlaceRes) : Prop :=
  ∃ (b' : Word) (t' : Tag),
    ρa resolved.allocBase = some b' ∧
    PtrRegisterEntry regMap reg b' (resolved.addr - resolved.allocBase) resolved.allocSize t' ∧
    ∃ ap2,
      PermissionModel.stackedBorrows.useMut s_ap
        (b' + (resolved.addr - resolved.allocBase)) t' = some ap2

/-- The instructions emitted by `m cs` are installed at compile-time label `baseLabel`
    in `prog`. This is a pure code-layout property; it does not mention runtime control. -/
def FragmentInstalledAtLabel {α} (m : CompilerM α) (cs : CompilerState)
    (baseLabel : Nat) (prog : oseair.Prog) : Prop :=
  let n := (CompilerM.run m cs).nextLabel - cs.nextLabel
  ∀ (i : Fin n), prog (baseLabel + i.1) = (CompilerM.run m cs).code (cs.nextLabel + i.1)

/-- The instructions emitted by `m cs` are installed at the current runtime PC in `prog`. -/
def FragInstalled {α} (m : CompilerM α) (cs : CompilerState)
    (s : oseair.State) (prog : oseair.Prog) : Prop :=
  let n := (CompilerM.run m cs).nextLabel - cs.nextLabel
  ∀ (i : Fin n), prog (s.pc + i.1) = (CompilerM.run m cs).code (cs.nextLabel + i.1)

def FragmentLength {α} (m : CompilerM α) (cs : CompilerState) : Nat :=
  (CompilerM.run m cs).nextLabel - cs.nextLabel

def FragmentEndLabel {α} (m : CompilerM α) (cs : CompilerState) : Nat :=
  (CompilerM.run m cs).nextLabel

theorem FragmentInstalledAtLabel.toFragInstalled
    {α} {m : CompilerM α} {cs : CompilerState}
    {baseLabel : Nat} {s : oseair.State} {prog : oseair.Prog}
    (h_label : s.pc = baseLabel)
    (h_inst : FragmentInstalledAtLabel m cs baseLabel prog) :
    FragInstalled m cs s prog := by
  intro i
  rw [h_label]
  exact h_inst i

/-- Every instruction emitted by a compiler computation preserves memory. -/
def EmitsPreservesMem {α} (m : CompilerM α) : Prop :=
  ∀ (cs : CompilerState) (label : Nat),
    cs.nextLabel ≤ label →
    label < (CompilerM.run m cs).nextLabel →
    ∀ instr, (CompilerM.run m cs).code label = some instr → InstrPreservesMem instr

theorem emitsPreservesMem_pure {α} (a : α) :
    EmitsPreservesMem (pure a : CompilerM α) := by
  intro cs label h_lo h_hi instr h_code
  simp [CompilerM.run] at h_hi
  exact False.elim ((Nat.not_lt_of_ge h_lo) h_hi)

theorem emitsPreservesMem_bind {α β}
    {m : CompilerM α} {f : α → CompilerM β}
    (hm : EmitsPreservesMem m)
    (hf : ∀ a, EmitsPreservesMem (f a)) :
    EmitsPreservesMem (m >>= f) := by
  intro cs label h_lo h_hi instr h_code
  let a := CompilerM.value m cs
  let cs1 := CompilerM.run m cs
  by_cases h_in_m : label < cs1.nextLabel
  · have h_code_m : cs1.code label = some instr := by
      have h_eq :=
        (CompilerM.incr (f a) cs1).code_eq label h_in_m
      have h_code_final :
          (CompilerM.run (f a) cs1).code label = some instr := by
        simpa [a, cs1, CompilerM.run_bind] using h_code
      rw [h_eq] at h_code_final
      exact h_code_final
    exact hm cs label h_lo h_in_m instr h_code_m
  · have h_lo_f : cs1.nextLabel ≤ label := Nat.le_of_not_gt h_in_m
    exact hf a cs1 label h_lo_f (by simpa [a, cs1, CompilerM.run_bind] using h_hi)
      instr (by simpa [a, cs1, CompilerM.run_bind] using h_code)

theorem checkedEmitsPreservesMem_pure {α} (a : α) :
    EmitsPreservesMem ((pure a : CheckedCompilerM α).toCompilerM) := by
  simpa using (emitsPreservesMem_pure (a := (Except.ok a : Except CompilerError α)))

theorem checkedEmitsPreservesMem_bind {α β}
    {m : CheckedCompilerM α} {f : α → CheckedCompilerM β}
    (hm : EmitsPreservesMem m.toCompilerM)
    (hf : ∀ a, EmitsPreservesMem (f a).toCompilerM) :
    EmitsPreservesMem ((m >>= f).toCompilerM) := by
  change EmitsPreservesMem
    (do
      match ← m.toCompilerM with
      | Except.error err => pure (Except.error err)
      | Except.ok a => (f a).toCompilerM)
  apply emitsPreservesMem_bind hm
  intro res
  cases res with
  | error err =>
      exact emitsPreservesMem_pure (Except.error err)
  | ok a =>
      simpa using hf a

theorem checkedEmitsPreservesMem_lift {α} {m : CompilerM α}
    (hm : EmitsPreservesMem m) :
    EmitsPreservesMem (CheckedCompilerM.lift m).toCompilerM := by
  unfold CheckedCompilerM.lift
  apply emitsPreservesMem_bind hm
  intro a
  exact emitsPreservesMem_pure (Except.ok a)

theorem freshRegM_emits_preserves_mem :
    EmitsPreservesMem freshRegM := by
  intro cs label h_lo h_hi instr h_code
  simp [freshRegM, freshReg, CompilerM.run] at h_hi
  exact False.elim ((Nat.not_lt_of_ge h_lo) h_hi)

theorem cleanupInstrs_mem_preserves
    {regs : List Register} {instr : Instr}
    (h_mem : instr ∈ cleanupInstrs regs) :
    InstrPreservesMem instr := by
  simp [cleanupInstrs] at h_mem
  rcases h_mem with ⟨reg, _h_reg, h_eq⟩
  cases h_eq
  simp [InstrPreservesMem]

theorem emitM_emits_preserves_mem
    (instrs : List Instr)
    (h_all : ∀ instr, instr ∈ instrs → InstrPreservesMem instr) :
    EmitsPreservesMem (emitM instrs) := by
  intro cs label h_lo h_hi instr h_code
  have h_hi' : label < cs.nextLabel + instrs.length := by
    simpa [CompilerM.run, emitM, emit] using h_hi
  have h_range : cs.nextLabel ≤ label ∧ label < cs.nextLabel + instrs.length :=
    ⟨h_lo, h_hi'⟩
  have h_get : instrs.get? (label - cs.nextLabel) = some instr := by
    simpa [CompilerM.run, emitM, emit, h_range] using h_code
  rcases List.get?_eq_some_iff.mp h_get with ⟨h_idx, h_get_fin⟩
  exact h_all instr (by
    rw [← h_get_fin]
    exact List.get_mem instrs ⟨label - cs.nextLabel, h_idx⟩)

theorem emitM_single_borrow_preserves_mem
    (kind : RefKind) (dst base : Register) (offset : Word) :
    EmitsPreservesMem
      (emitM [Instr.Assgn dst (borrowOffsetRhs kind base offset)]) := by
  apply emitM_emits_preserves_mem
  intro instr h_mem
  simp [borrowOffsetRhs, InstrPreservesMem, RhsPreservesMem] at h_mem ⊢
  cases kind <;> simp_all

theorem emitM_single_load_preserves_mem
    (dst src : Register) :
    EmitsPreservesMem
      (emitM [Instr.Assgn dst (Rhs.Load obseq.TyVal.PTy src)]) := by
  apply emitM_emits_preserves_mem
  intro instr h_mem
  simp at h_mem
  subst instr
  simp [InstrPreservesMem, RhsPreservesMem]

theorem emitM_cleanup_preserves_mem
    (regs : List Register) :
    EmitsPreservesMem (emitM (cleanupInstrs regs)) := by
  apply emitM_emits_preserves_mem
  intro instr h_mem
  exact cleanupInstrs_mem_preserves h_mem

theorem placeToRegE_emits_preserves_mem
    {Γ : Ctx} {τ : LayoutTy}
    (kind : RefKind) (p : Place Γ τ) :
    EmitsPreservesMem (placeToRegE kind p) := by
  induction p generalizing kind with
  | «local» loc =>
      intro cs label h_lo h_hi instr h_code
      have h_next :
          (CompilerM.run (placeToRegE kind (.local loc)) cs).nextLabel = cs.nextLabel := by
        unfold CompilerM.run placeToRegE
        split <;> rfl
      rw [h_next] at h_hi
      exact False.elim ((Nat.not_lt_of_ge h_lo) h_hi)
  | proj base path ih =>
      by_cases hoff : pathOffset path = 0
      · simpa [placeToRegE, hoff] using
          (emitsPreservesMem_bind (ih kind)
            (fun _ => emitsPreservesMem_pure _))
      · apply emitsPreservesMem_bind (ih kind)
        intro baseChecked
        simp [hoff]
        apply emitsPreservesMem_bind freshRegM_emits_preserves_mem
        intro tmpReg
        apply emitsPreservesMem_bind
          (emitM_single_borrow_preserves_mem kind tmpReg baseChecked.result.reg (pathOffset path))
        intro _
        exact emitsPreservesMem_pure _
  | deref ptrPlace ih =>
      apply emitsPreservesMem_bind (ih RefKind.Shared)
      intro ptrChecked
      apply emitsPreservesMem_bind freshRegM_emits_preserves_mem
      intro loadedReg
      apply emitsPreservesMem_bind (emitM_single_load_preserves_mem loadedReg ptrChecked.result.reg)
      intro _
      apply emitsPreservesMem_bind (emitM_cleanup_preserves_mem ptrChecked.result.cleanup)
      intro _
      exact emitsPreservesMem_pure _

-- Every instruction emitted by proof-facing `placeToRegE` preserves memory.
-- This is a pure compile-time fact: proved by structural induction on `p`,
-- inspecting the constructors emitted at each step.
theorem placeToRegE_emits_no_mem_effects
    {Γ : Ctx} {τ : LayoutTy}
    (cs : CompilerState) (kind : RefKind) (p : Place Γ τ)
    (label : Nat)
    (h_lo  : cs.nextLabel ≤ label)
    (h_hi  : label < (CompilerM.run (placeToRegE kind p) cs).nextLabel)
    (instr : Instr)
    (h_code : (CompilerM.run (placeToRegE kind p) cs).code label = some instr) :
    InstrPreservesMem instr :=
  placeToRegE_emits_preserves_mem kind p cs label h_lo h_hi instr h_code

-- Simulation lemma for a single-word write: if source writeResolvedPlace succeeds
-- and the target register holds a suitably renamed pointer (PlaceRegReady), then
-- writeThroughPtr succeeds and memory simulation is preserved.
--
-- Key correspondences required (proved via sorry for now):
--   (1) bounds: resolved.addr + 1 ≤ allocBase + allocSize
--               ↔ (b' + offset) + 1 ≤ b' + size
--       (arithmetic; needs ρa(base + k) = ρa(base) + k within allocations)
--   (2) permission: PlaceRegReady already contains ∃ ap2, useMut s_osea.ap addr' t' = some ap2;
--       no separate ρt tag-rename needed.
--   (3) memory: writeWordSeq at b'+offset corresponds to source writeWordSeq at resolved.addr;
--       MemValSim (word v) (Dat v) extends SourceMemSim at the written cell.
--
-- Note: s_osea'.ap is the post-write ap (from sb_use_mb).  The full ap correspondence
-- s_osea_final.ap = s_mir'.perms is restored by the Die cleanup phase, not here.
-- theorem writeThroughPtr_sim
--     {Γ : Ctx}
--     (ρa : AddrRenameMap) (ρt : TagRenameMap)
--     {s_mir  : obseq2.mirlite.State PermissionModel.stackedBorrows Γ}
--     {s_mir' : obseq2.mirlite.State PermissionModel.stackedBorrows Γ}
--     {s_osea : oseair.State}
--     {resolved : obseq2.mirlite.PlaceRes}
--     {dstReg : Register}
--     (v : Word)
--     (h_ptr   : PlaceRegReady ρa s_osea.ap s_osea.reg dstReg resolved)
--     (h_sms   : SourceMemSim ρa ρt s_mir.mem s_osea.mem)
--     (h_write : obseq2.mirlite.writeResolvedPlace (τ := obseq.LayoutTy.NatL)
--                  PermissionModel.stackedBorrows s_mir resolved
--                  [obseq2.mirlite.MemValue.word v] rfl
--                = obseq2.mirlite.Result.ok s_mir') :
--     ∃ s_osea',
--       oseair.writeThroughPtr s_osea dstReg [Val.Dat v] "CStore Invalid Ptr"
--         = oseair.Result.Ok s_osea' ∧
--       SourceMemSim ρa ρt s_mir'.mem s_osea'.mem ∧
--       s_osea'.reg = s_osea.reg ∧
--       s_osea'.pc = s_osea.pc + 1 := by
--   sorry

-- A CStore instruction at position s.pc in compProg, with vals.length = typeSize ty,
-- executes as a single runN step via writeThroughPtr.
-- theorem runN_CStore_step
--     (compProg : oseair.Prog) (s s' : oseair.State)
--     (ty : obseq.TyVal) (vals : List Val) (ptr : Register)
--     (h_instr : compProg s.pc = some (Instr.CStore ty vals ptr))
--     (h_size : vals.length = obseq.typeSize ty)
--     (h_wtp : oseair.writeThroughPtr s ptr vals "CStore Invalid Ptr" = oseair.Result.Ok s') :
--     oseair.runN 1 s compProg = oseair.Result.Ok s' := by
--   sorry

-- Running cleanupInstrs dies (a sequence of Die instructions) from s in compProg
-- succeeds and leaves mem and reg unchanged, advancing pc by the cleanup length.
-- Die-succeeds relies on ap coherence after useMut; that obligation is deferred.
-- theorem runN_cleanupInstrs
--     (compProg : oseair.Prog) (s : oseair.State) (dies : List Register)
--     (h_instrs : ∀ (i : Fin (cleanupInstrs dies).length),
--       compProg (s.pc + i.1) = some ((cleanupInstrs dies).get i)) :
--     ∃ s' : oseair.State,
--       oseair.runN (cleanupInstrs dies).length s compProg = oseair.Result.Ok s' ∧
--       s'.mem = s.mem ∧ s'.reg = s.reg ∧ s'.pc = s.pc + (cleanupInstrs dies).length := by
--   sorry

-- runN is composable: running m steps then n more equals m+n steps.
theorem oseair_runN_add
    (m n : Nat) (s : oseair.State) (prog : oseair.Prog) (s' : oseair.State)
    (h : oseair.runN m s prog = oseair.Result.Ok s') :
    oseair.runN (m + n) s prog = oseair.runN n s' prog := by
  induction m generalizing s with
  | zero =>
      simp [oseair.runN] at h
      simp [oseair.runN, h]
  | succ m ih =>
      simp only [Nat.succ_add, oseair.runN, oseair.runNWith_succ] at *
      split at h
      · exact ih _ h
      · simp at h

end obseq2.proof
