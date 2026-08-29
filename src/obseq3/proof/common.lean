import obseq3.compile
import obseq3.mirlite_semantics
import obseq3.permission

/-!
Shared vocabulary and machinery for the mirlite-v3 → OSEA-IR-v3 compiler
correctness proofs. Skeleton-first port of `src/obseq2/proof/common.lean`:
the compiler-monad/prefix machinery and lowering-totality lemmas are ported
with full proofs; the simulation bridges are STATED with documented sorries
(see the audit in `obseq3/proof/compiler.lean`).

Invariant-design changes vs obseq2 (see the 2026-08-15 journal entry):
- obseq2's conjunct `s_osea.ap = s_mir.perms` (literal equality) is false as
  soon as one internal borrow is minted: `die` pops the item but does not
  roll back `NextTag`, and once the counters split every subsequent
  corresponding borrow gets DIFFERENT tag values on the two machines. The
  honest relation is `PermSim ρt`: item-wise ρt-renamed stack equality
  (position- and constructor-preserving), renamed `exposed`/`protFrames`,
  and `NextTag ≤`.
- consequently ρt is monotone-injective (`TagRenameWF`), not identity;
  ρa stays `IdentityOnDomain` (addresses are lockstep).
- `Die` remains load-bearing: ρt absorbs tag-VALUE divergence, `Die`
  collapses stack-STRUCTURE divergence (extra items with no source
  counterpart) at each statement boundary. Without it the relation would
  need junk-tolerance in every SB-op lemma.
-/

namespace obseq3.proof

open obseq3
open obseq3.compile
open obseq3.oseair (Instr Register Rhs Val)

/-- The permission model both sides of the simulation are instantiated at. -/
abbrev MSB : PermissionModel := PermissionModel.stackedBorrows

/-! ## §A Compiler-monad / prefix-state machinery (ported from obseq2) -/

/-- Clear the code map of a compiler state, leaving allocation counters unchanged. -/
def resetCode (cs : CompilerState) : CompilerState :=
  { cs with code := fun _ => none }

/-- Compile the first `stmtIdx` statements of `prog` starting from initial state `cs0`,
    returning the accumulated compiler state when that prefix compiles successfully. -/
def prefixCompileState
  {Γ : Ctx}
  (cs0 : CompilerState)
  (prog : obseq3.Prog Γ)
  (stmtIdx : Nat) : Except CompilerError CompilerState :=
  match CheckedCompilerM.value (compileStmtsChecked (prog.take stmtIdx)) cs0 with
  | .ok _ => .ok (CheckedCompilerM.run (compileStmtsChecked (prog.take stmtIdx)) cs0)
  | .error err => .error err

/-- Witness that `csPrefix` is the compiler state at the start of source statement `stmtIdx`. -/
def csAt
  {Γ : Ctx}
  (cs0 : CompilerState)
  (prog : obseq3.Prog Γ)
  (stmtIdx : Nat)
  (csPrefix : CompilerState) : Prop :=
  prefixCompileState cs0 prog stmtIdx = Except.ok csPrefix

/-- Witness that `label` is the target label corresponding to source statement `stmtIdx`. -/
def targetLabelAt
  {Γ : Ctx}
  (cs0 : CompilerState)
  (prog : obseq3.Prog Γ)
  (stmtIdx : Nat)
  (csPrefix : CompilerState)
  (label : Nat) : Prop :=
  csAt cs0 prog stmtIdx csPrefix ∧
  label = csPrefix.nextLabel

/-- Compile an entire program starting from `cs0`. -/
def compileProgFrom
  {Γ : Ctx}
  (cs0 : CompilerState)
  (prog : obseq3.Prog Γ) : Except CompilerError obseq3.oseair.Prog :=
  compileProgFromChecked cs0 prog

/-- Rvalues in the proof-core fragment. The v3 compiler is TOTAL, so this
    predicate scopes the correctness THEOREMS (obseq2's proof scope), not
    the compiler. -/
def CoreRhs {Γ : Ctx} {τ : LayoutTy} : RExpr Γ τ → Prop
  | .constInit _ => True
  | .copy _ => True
  | .ref _ _ _ _ => True
  | _ => False

/-- Statements in the proof-core fragment: `halt` and assignments with a
    core rvalue. -/
def CoreStmt {Γ : Ctx} : Stmt Γ → Prop
  | .halt => True
  | .assign _ rhs => CoreRhs rhs
  | _ => False

/-- Every statement of the program is in the proof-core fragment. -/
def CoreProg {Γ : Ctx} (prog : obseq3.Prog Γ) : Prop :=
  ∀ i stmt, prog.get? i = some stmt → CoreStmt stmt

/-- One source step at the current pc, mirroring the inner match of
    `mirlite.runN` (v3 has no standalone `step`). -/
def srcStep {Γ : Ctx} (s : mirlite.State MSB Γ) (prog : obseq3.Prog Γ) :
    mirlite.Result MSB Γ :=
  match prog.get? s.pc with
  | some .halt => .ok s
  | none => .ok s
  | some stmt => mirlite.stepStmt MSB s stmt

theorem csAt_value_ok
  {Γ : Ctx}
  {cs0 : CompilerState}
  {prog : obseq3.Prog Γ}
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
  {prog : obseq3.Prog Γ}
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
  {prog : obseq3.Prog Γ}
  {compProg : obseq3.oseair.Prog}
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
    (xs ys : obseq3.Prog Γ) (cs : CompilerState) :
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
    (xs ys : obseq3.Prog Γ) (cs : CompilerState) :
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
    {prog : obseq3.Prog Γ}
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
    (cs0 : CompilerState) (prog : obseq3.Prog Γ)
    (compProg : obseq3.oseair.Prog)
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

/-! ## §B Register-bound / memory-effect statics (re-cased over the v3 sets) -/

/-- A register whose numeric index is strictly less than `bound`. -/
def RegisterBelow (bound : Nat) : Register → Prop
  | .R idx => idx < bound

theorem RegisterBelow.mono {b b' : Nat} (h : b ≤ b') :
    ∀ {r : Register}, RegisterBelow b r → RegisterBelow b' r
  | .R _, h_lt => Nat.lt_of_lt_of_le h_lt h

/-- All registers mentioned in an `Rhs` have index strictly less than `bound`. -/
def RhsRegsBelow (bound : Nat) : Rhs → Prop
  | .Load _ reg => RegisterBelow bound reg
  | .Alloc _ => True
  | .AllocN _ _ => True
  | .AllocDyn _ lenPtr => RegisterBelow bound lenPtr
  | .Borrow _ _ _ _ base _ => RegisterBelow bound base
  | .ExposeAddr src => RegisterBelow bound src
  | .FromExposed src => RegisterBelow bound src
  | .PtrOffset src _ => RegisterBelow bound src
  | .BorrowRest _ _ src => RegisterBelow bound src

/-- All registers mentioned in an `Instr` have index strictly less than `bound`. -/
def InstrRegsBelow (bound : Nat) : Instr → Prop
  | .Assgn reg rhs => RegisterBelow bound reg ∧ RhsRegsBelow bound rhs
  | .RStore _ src ptr => RegisterBelow bound src ∧ RegisterBelow bound ptr
  | .CStore _ _ ptr => RegisterBelow bound ptr
  | .Memcpy dst src _ => RegisterBelow bound dst ∧ RegisterBelow bound src
  | .Die reg _ => RegisterBelow bound reg
  | .Dealloc ptr => RegisterBelow bound ptr
  | .SkipIf discr _ _ => RegisterBelow bound discr
  | .PushProt => True
  | .PopProt => True
  | .Halt => True

/-- Every populated code slot satisfies `InstrRegsBelow bound`. -/
def CodeRegsBelow (bound : Nat) (code : Nat → Option Instr) : Prop :=
  ∀ pc instr, code pc = some instr → InstrRegsBelow bound instr

/-- RHS forms that do not mutate target memory (the three allocators advance
    the allocator-backed memory state and are excluded). -/
def RhsPreservesMem : Rhs → Prop
  | .Alloc _ => False
  | .AllocN _ _ => False
  | .AllocDyn _ _ => False
  | _ => True

/-- Instructions that neither mutate target memory nor branch, and advance
    the PC by exactly one when they succeed. `SkipIf` is excluded because it
    may advance by more than one; `Dealloc` removes memory; stores and
    `Memcpy` write it; `Halt` does not advance. -/
def InstrPreservesMem : Instr → Prop
  | .Assgn _ rhs => RhsPreservesMem rhs
  | .RStore _ _ _ => False
  | .CStore _ _ _ => False
  | .Memcpy _ _ _ => False
  | .Die _ _ => True
  | .Dealloc _ => False
  | .SkipIf _ _ _ => False
  | .PushProt => True
  | .PopProt => True
  | .Halt => False

theorem evalRhsWith_preserves_mem
    {A : oseair.AllocatorSpec} {s s1 : oseair.State MSB}
    {rhs : Rhs} {vals : List Val} {ty : obseq.TyVal}
    (h_rhs : RhsPreservesMem rhs)
    (h_eval : oseair.evalRhsWith MSB A s rhs = oseair.RhsResult.Ok vals ty s1) :
    s1.mem = s.mem := by
  cases rhs <;> simp [RhsPreservesMem, oseair.evalRhsWith] at h_rhs h_eval
  all_goals
    repeat (split at h_eval <;> try contradiction)
    cases h_eval
    rfl

theorem step_preserves_mem_and_pc
    {s s' : oseair.State MSB} {prog : oseair.Prog} {instr : Instr}
    (h_instr : prog s.pc = some instr)
    (h_mem : InstrPreservesMem instr)
    (h_step : oseair.step MSB s prog = oseair.Result.Ok s') :
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
  | Die reg len =>
      simp [oseair.step, oseair.stepWith, h_instr] at h_step
      repeat (split at h_step <;> try contradiction)
      cases h_step
      constructor <;> rfl
  | Dealloc ptr =>
      cases h_mem
  | SkipIf discr v skip =>
      cases h_mem
  | PushProt =>
      simp [oseair.step, oseair.stepWith, h_instr] at h_step
      cases h_step
      constructor <;> rfl
  | PopProt =>
      simp [oseair.step, oseair.stepWith, h_instr] at h_step
      repeat (split at h_step <;> try contradiction)
      cases h_step
      constructor <;> rfl
  | Halt =>
      cases h_mem

theorem runN_preserves_mem
    {n : Nat} {s s' : oseair.State MSB} {prog : oseair.Prog}
    (h_run : oseair.runN MSB n s prog = oseair.Result.Ok s')
    (h_mem : ∀ (k : Fin n) instr,
      prog (s.pc + k.1) = some instr → InstrPreservesMem instr) :
    s'.mem = s.mem := by
  induction n generalizing s with
  | zero =>
      simp at h_run
      cases h_run
      rfl
  | succ n ih =>
      cases h_step : oseair.step MSB s prog with
      | Err msg =>
          simp [oseair.runN_succ, h_step] at h_run
      | Ok s1 =>
          have h_run_tail : oseair.runN MSB n s1 prog = oseair.Result.Ok s' := by
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

/-! ## §C Invariant vocabulary -/

/-- A well-formed compiler state: every emitted instruction only references
    registers below `nextReg`. -/
def CompilerStateWF (_Γ : Ctx) (cs : CompilerState) : Prop :=
  CodeRegsBelow cs.nextReg cs.code

/-- Every register recorded in the place-register map is below `nextReg` —
    so a freshly minted register (`freshRegM` returns `nextReg`) can never
    collide with a register the target uses to address a bound local. This
    is the first installment of the strengthened `CompilerStateWF` the
    proj/deref write regimes need; the fragment-internal `CodeRegsBelow`
    half stays deferred. -/
def PlaceRegMapBound (cs : CompilerState) : Prop :=
  ∀ idx reg τ, getPlaceInfo cs idx = some (reg, τ) → RegisterBelow cs.nextReg reg

/-- Register `reg` in `regMap` holds a pointer value with the given fields. -/
def PtrRegisterEntry
  (regMap : obseq3.oseair.RegMap)
  (reg : Register)
  (base offset size : Word)
  (tag : Tag) : Prop :=
  obseq3.oseair.RegMap.lookup regMap reg = some (obseq.TyVal.PTy, [Val.Ptr base offset size tag])

abbrev AddrRenameMap := Word → Option Word
abbrev TagRenameMap := Tag → Option Tag

/-- Address rename maps grow monotonically. -/
def AddrRenameIncr (ρa ρa' : AddrRenameMap) : Prop :=
  ∀ addr addr', ρa addr = some addr' → ρa' addr = some addr'

/-- Tag rename maps grow monotonically. -/
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

/-- A rename map is the identity wherever it is defined. In v3 this is kept
    ONLY for ρa: lockstep bump allocation shares the address namespace. -/
def IdentityOnDomain {α : Type} (ρ : α → Option α) : Prop :=
  ∀ a a', ρ a = some a' → a = a'

theorem IdentityOnDomain.apply {α : Type} {ρ : α → Option α} {a a' : α}
    (h_id : IdentityOnDomain ρ) (h : ρ a = some a') : a = a' :=
  h_id a a' h

/-- v3's ρt discipline (replacing obseq2's identity): injective, and fixing
    the wildcard tag (int-to-ptr pointers carry `wildcardTag` on BOTH
    machines, so `MemValSim` needs it mapped to itself). Monotonicity of the
    tag ORDER (srcTag ≤ tgtTag) holds for the maps the simulation builds but
    is not required by any stated obligation, so it is not carried. -/
def TagRenameWF (ρt : TagRenameMap) : Prop :=
  (∀ t1 t2 t', ρt t1 = some t' → ρt t2 = some t' → t1 = t2) ∧
  ρt wildcardTag = some wildcardTag

/-! ### The tag bound — what makes ρt EXTENSIBLE

`TagRenameWF` alone is not enough for the one case that grows ρt (`ref`):
extending an injective map at a fresh pair stays injective only if the new
target tag is outside the map's range. Both machines mint at their own
`NextTag`, so the range bound below is exactly the fact that discharges it
(and the domain bound gives `ρt srcFresh = none`, i.e. the extension really
is an extension). It is the tag half of the strengthened WF the audit named;
`PlaceRegMapBound` (in `CompilerInv`) is the register half. -/
def TagRenameBounded (ρt : TagRenameMap) (nS nT : Tag) : Prop :=
  ∀ t t', ρt t = some t' → t < nS ∧ t' < nT

/-- Extend a rename map at one fresh pair. -/
def TagRenameMap.extend (ρt : TagRenameMap) (s t : Tag) : TagRenameMap :=
  fun x => if x = s then some t else ρt x

@[simp] theorem TagRenameMap.extend_self (ρt : TagRenameMap) (s t : Tag) :
    ρt.extend s t s = some t := by
  simp [TagRenameMap.extend]

theorem TagRenameMap.extend_ne {ρt : TagRenameMap} {s t x : Tag} (h : x ≠ s) :
    ρt.extend s t x = ρt x := by
  simp [TagRenameMap.extend, h]

/-- Above the domain bound the map is undefined — so the fresh source tag
    is genuinely unmapped. -/
theorem TagRenameBounded.eq_none {ρt : TagRenameMap} {nS nT s : Tag}
    (h_bd : TagRenameBounded ρt nS nT) (h_s : nS ≤ s) : ρt s = none := by
  cases h : ρt s with
  | none => rfl
  | some t' => grind [TagRenameBounded]

/-- Extending at a pair beyond both bounds is a growth of the map. -/
theorem TagRenameIncr.extend {ρt : TagRenameMap} {nS nT s t : Tag}
    (h_bd : TagRenameBounded ρt nS nT) (h_s : nS ≤ s) :
    TagRenameIncr ρt (ρt.extend s t) := by
  intro x x' hx
  grind [TagRenameMap.extend, TagRenameBounded]

/-- `TagRenameWF` survives the fresh-pair extension: injectivity because the
    new target is outside the old range (the range bound), and the wildcard
    mapping because `wildcardTag = 0 < nS ≤ s`. -/
theorem TagRenameWF.extend {ρt : TagRenameMap} {nS nT s t : Tag}
    (h_wf : TagRenameWF ρt) (h_bd : TagRenameBounded ρt nS nT)
    (h_s : nS ≤ s) (h_t : nT ≤ t) :
    TagRenameWF (ρt.extend s t) := by
  obtain ⟨h_inj, h_wc⟩ := h_wf
  constructor
  · intro t1 t2 t' h1 h2
    grind [TagRenameMap.extend, TagRenameBounded]
  · grind [TagRenameMap.extend, TagRenameBounded]

/-- The bound itself grows with the counters. -/
theorem TagRenameBounded.extend {ρt : TagRenameMap} {nS nT nS' nT' s t : Tag}
    (h_bd : TagRenameBounded ρt nS nT)
    (h_le : nS ≤ nS') (h_le' : nT ≤ nT') (h_s : s < nS') (h_t : t < nT') :
    TagRenameBounded (ρt.extend s t) nS' nT' := by
  intro x x' hx
  grind [TagRenameMap.extend, TagRenameBounded]

/-- The bound is monotone in the counters (both machines only ever mint). -/
theorem TagRenameBounded.mono {ρt : TagRenameMap} {nS nT nS' nT' : Tag}
    (h_bd : TagRenameBounded ρt nS nT) (h_le : nS ≤ nS') (h_le' : nT ≤ nT') :
    TagRenameBounded ρt nS' nT' := by
  grind [TagRenameBounded]

/-! ### PermSim — the corrected permission relation

obseq2 asserted `s_osea.ap = s_mir.perms` verbatim. That is false as soon as
one internal borrow is minted (NextTag diverges, and with it every later
corresponding tag VALUE). The honest relation renames item-wise through ρt.
Both machines perform identical op SEQUENCES on their stacks, so cell order
and stack shapes agree exactly; only tag values differ. -/

/-- Pointwise relation between two lists of equal length (a local stand-in
    for Mathlib's `List.Forall₂`, which this project does not depend on). -/
def ListRel (R : α → β → Prop) : List α → List β → Prop
  | [], [] => True
  | a :: as, b :: bs => R a b ∧ ListRel R as bs
  | _, _ => False

theorem ListRel.imp {α β} {R S : α → β → Prop}
    (h : ∀ a b, R a b → S a b) :
    ∀ {as : List α} {bs : List β}, ListRel R as bs → ListRel S as bs := by
  intro as
  induction as with
  | nil =>
      intro bs hr
      cases bs with
      | nil => trivial
      | cons b bs => simp [ListRel] at hr
  | cons a as ih =>
      intro bs hr
      cases bs with
      | nil => simp [ListRel] at hr
      | cons b bs =>
          simp only [ListRel] at hr ⊢
          exact ⟨h a b hr.1, ih hr.2⟩

theorem ListRel.length_eq {α β} {R : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, ListRel R as bs → as.length = bs.length := by
  intro as
  induction as with
  | nil =>
      intro bs hr
      cases bs with
      | nil => rfl
      | cons b bs => simp [ListRel] at hr
  | cons a as ih =>
      intro bs hr
      cases bs with
      | nil => simp [ListRel] at hr
      | cons b bs =>
          simp only [ListRel] at hr
          simp [ih hr.2]

/-- Item-wise simulation: same constructor, tag mapped by ρt. Preserving the
    constructor (incl. `Disabled`) keeps SRW-grouping structure identical. -/
def ItemSim (ρt : TagRenameMap) : Item → Item → Prop
  | .Own t, .Own t' => ρt t = some t'
  | .MutRef t, .MutRef t' => ρt t = some t'
  | .Ref t, .Ref t' => ρt t = some t'
  | .RawPtr m t, .RawPtr m' t' => m' = m ∧ ρt t = some t'
  | .Disabled t, .Disabled t' => ρt t = some t'
  | _, _ => False

theorem ItemSim.mono {ρt ρt' : TagRenameMap} (h_incr : TagRenameIncr ρt ρt')
    (i i' : Item) (hi : ItemSim ρt i i') : ItemSim ρt' i i' := by
  cases i <;> cases i' <;> simp [ItemSim] at hi ⊢ <;>
    first
      | exact h_incr _ _ hi
      | exact ⟨hi.1, h_incr _ _ hi.2⟩

/-- Position-preserving stack simulation. -/
def StackSim (ρt : TagRenameMap) (src tgt : List Item) : Prop :=
  ListRel (ItemSim ρt) src tgt

/-- Per-cell entry simulation: same address, simulated stack. -/
def CellSim (ρt : TagRenameMap) : (Word × List Item) → (Word × List Item) → Prop
  | (a, s), (a', s') => a' = a ∧ StackSim ρt s s'

/-- Stack-map simulation at the OBSERVATION level: same domain, related
    stacks per ADDRESS (`SB.find?`) — not per list position. Quotienting
    out the representation order is what lets disjoint-range operation
    sequences commute even though `SB.set` is move-to-front: the copy
    leaf's interleaved `Die` (2026-08-28) leaves different cells at the
    list FRONT than the source's op order, with identical `find?`
    semantics — the assoclist tradeoff, realized. -/
def StackMapSim (ρt : TagRenameMap) (x y : SB) : Prop :=
  ∀ a : Word,
    match SB.find? x a, SB.find? y a with
    | none, none => True
    | some s, some s' => StackSim ρt s s'
    | _, _ => False

theorem StackMapSim.find?_some {ρt : TagRenameMap} {x y : SB}
    (h : StackMapSim ρt x y) {a : Word} {s : BorrowStack}
    (hf : SB.find? x a = some s) :
    ∃ s', SB.find? y a = some s' ∧ StackSim ρt s s' := by
  have h' := h a
  rw [hf] at h'
  cases hy : SB.find? y a with
  | none => rw [hy] at h'; exact absurd h' (by simp)
  | some s' => rw [hy] at h'; exact ⟨s', rfl, h'⟩

theorem StackMapSim.find?_none {ρt : TagRenameMap} {x y : SB}
    (h : StackMapSim ρt x y) {a : Word}
    (hf : SB.find? x a = none) : SB.find? y a = none := by
  have h' := h a
  rw [hf] at h'
  cases hy : SB.find? y a with
  | none => rfl
  | some s' => rw [hy] at h'; exact absurd h' (by simp)

/-- The target side of a `StackMapSim` can be swapped for any
    `find?`-identical map — the disjoint-range commutation produces its
    result only up to representation order. -/
theorem StackMapSim.congr_right {ρt : TagRenameMap} {x y y' : SB}
    (h_eq : ∀ a, SB.find? y' a = SB.find? y a)
    (h : StackMapSim ρt x y) : StackMapSim ρt x y' := by
  intro a
  rw [h_eq a]
  exact h a

theorem StackMapSim.imp {ρt ρt' : TagRenameMap} {x y : SB}
    (h_i : ∀ i i', ItemSim ρt i i' → ItemSim ρt' i i')
    (h : StackMapSim ρt x y) : StackMapSim ρt' x y := by
  intro a
  have h' := h a
  cases hx : SB.find? x a with
  | none =>
      rw [hx] at h'
      cases hy : SB.find? y a with
      | none => simp
      | some s' => rw [hy] at h'; exact absurd h' (by simp)
  | some s =>
      rw [hx] at h'
      cases hy : SB.find? y a with
      | none => rw [hy] at h'; exact absurd h' (by simp)
      | some s' =>
          rw [hy] at h'
          simp only [hx, hy]
          exact ListRel.imp h_i h'

/-- Tag-list simulation (protector frames, exposed set). -/
def TagListSim (ρt : TagRenameMap) (src tgt : List Tag) : Prop :=
  ListRel (fun t t' => ρt t = some t') src tgt

/-- The v3 permission relation: ρt-renamed stacks (position- and
    constructor-preserving), renamed protector frames and exposed set, and a
    target counter at least the source's (the target mints extra tags for
    its internal borrows; `Die` pops the items but not the counter). -/
def PermSim (ρt : TagRenameMap) (src tgt : AccessPerms) : Prop :=
  StackMapSim ρt src.StackMap tgt.StackMap ∧
  ListRel (TagListSim ρt) src.protFrames tgt.protFrames ∧
  TagListSim ρt src.exposed tgt.exposed ∧
  src.NextTag ≤ tgt.NextTag

/-- `PermSim` transports along rename growth (renames only appear
    positively). -/
theorem PermSim.rename_mono
    {ρt ρt' : TagRenameMap} {src tgt : AccessPerms}
    (h_incr : TagRenameIncr ρt ρt')
    (h_sim : PermSim ρt src tgt) :
    PermSim ρt' src tgt := by
  obtain ⟨h_stacks, h_prot, h_exp, h_next⟩ := h_sim
  refine ⟨?_, ?_, ?_, h_next⟩
  · exact StackMapSim.imp (fun i i' => ItemSim.mono h_incr i i') h_stacks
  · exact ListRel.imp (fun f f' hf =>
      ListRel.imp (fun t t' ht => h_incr _ _ ht) hf) h_prot
  · exact ListRel.imp (fun t t' ht => h_incr _ _ ht) h_exp

/-- Every local reached while structurally traversing `p` already has a
    compiler mapping in `placeRegMap`. -/
def PlaceInputsMapped
  {Γ : Ctx}
  (cs : CompilerState) : {τ : LayoutTy} → Place Γ τ → Prop
  | _, .local loc =>
    ∃ reg layout, getPlaceInfo cs loc.idx.1 = some (reg, layout)
  | _, .proj base _ =>
    PlaceInputsMapped cs base
  | _, .deref ptrPlace =>
    PlaceInputsMapped cs ptrPlace

/-- Simulation between source local bindings and target register values. -/
def LocalBindingSim
  {Γ : Ctx}
  (ρa : AddrRenameMap)
  (ρt : TagRenameMap)
  (env : mirlite.Env Γ)
  (s_osea : oseair.State MSB)
  (cs : CompilerState) : Prop :=
  ∀ {τ : LayoutTy} (loc : Local Γ τ) (binding : mirlite.Binding),
    mirlite.Env.lookup env loc = some binding →
    ∃ reg base tag,
      getPlaceInfo cs loc.idx.1 = some (reg, τ) ∧
      PtrRegisterEntry s_osea.reg reg base 0 (blockSize τ) tag ∧
      ρa binding.addr = some base ∧
      ρt binding.tag = some tag ∧
      (binding.tag == wildcardTag) = false ∧
      -- the local's WHOLE block is in ρa's domain, not just its base.
      -- Mirrors `MemValSim`'s referent-range conjunct, and is what a
      -- `&local` supplies to `writeThroughPtr_sim` when the resulting
      -- pointer is stored: the stored value's `MemValSim` needs the range.
      (∀ k, k < blockSize τ → ∃ a', ρa (binding.addr + k) = some a')

/-- The converse of `LocalBindingSim`'s mapping component: a local the
    source has not bound is not mapped by the compiler either.

    Source `preparePlaceAssign` and target `ensurePlaceRoot` allocate the
    root of an assignment destination at the same statement, so the two
    notions of "exists yet" agree. Regime B needs exactly this direction:
    it is what says the compiled fragment really does begin with the root
    `Alloc`, rather than being the bare `CStore` of regime A. -/
def UnboundLocalsUnmapped {Γ : Ctx}
  (env : mirlite.Env Γ) (cs : CompilerState) : Prop :=
  ∀ {τ : LayoutTy} (loc : Local Γ τ),
    mirlite.Env.lookup env loc = none → getPlaceInfo cs loc.idx.1 = none

/-- Pointwise simulation between a source `MemValue` and a target `Val`. -/
def MemValSim
  (ρa : AddrRenameMap)
  (ρt : TagRenameMap) : mirlite.MemValue → Val → Prop
  -- undef refines ANY target value: an unwritten (or explicitly undef)
  -- source cell carries no information, and every source operation that
  -- would OBSERVE the word (branching, alloc-length reads, pointer
  -- loads) errs on undef, discharging the simulation obligation. This
  -- is what lets a copy relate `mirlite.readWordSeq` to
  -- `oseair.readWordSeq` cell-by-cell when the source range has holes
  -- (`readWordSeq_sim`) without a reverse-domain memory invariant.
  | .undef,           _                  => True
  | .word v,          .Dat v'            => v' = v
  | .ptrVal b o s t,  .Ptr b' o' s' t'  =>
      ρa b = some b' ∧ o' = o ∧ s' = s ∧ ρt t = some t' ∧
      -- core programs cannot mint wildcard pointers (`fromExposed` is not
      -- a core rvalue), so stored pointer tags are non-wildcard — this is
      -- what lets BRIDGE 3 fire on writes THROUGH loaded pointers
      (t == wildcardTag) = false ∧
      -- the referent block is in ρa's domain (allocations are lockstep),
      -- which is what supplies `writeThroughPtr_sim`'s `h_dom` for deref
      -- destinations
      (∀ k, k < s → ∃ a', ρa (b + k) = some a')
  | _, _                                 => False

theorem MemValSim.rename_mono
    {ρa ρa' : AddrRenameMap} {ρt ρt' : TagRenameMap}
    {mv : mirlite.MemValue} {v : Val}
    (h_addr : AddrRenameIncr ρa ρa')
    (h_tag : TagRenameIncr ρt ρt')
    (h_sim : MemValSim ρa ρt mv v) :
    MemValSim ρa' ρt' mv v := by
  cases mv <;> cases v <;> simp [MemValSim] at h_sim ⊢
  · exact h_sim
  · rcases h_sim with ⟨h_base, h_off, h_size, h_tag_old, h_nw, h_dom⟩
    exact ⟨h_addr _ _ h_base, h_off, h_size, h_tag _ _ h_tag_old, h_nw,
      fun k hk => ⟨(h_dom k hk).choose, h_addr _ _ (h_dom k hk).choose_spec⟩⟩

/-- Extend an address rename at one fresh address. Unlike ρt, ρa is
    IDENTITY on its domain (lockstep bump allocation shares the address
    namespace), so the only extension the simulation ever performs is
    `a ↦ a`. -/
def AddrRenameMap.extend (ρa : AddrRenameMap) (a b : Word) : AddrRenameMap :=
  fun x => if x = a then some b else ρa x

@[simp] theorem AddrRenameMap.extend_self (ρa : AddrRenameMap) (a b : Word) :
    ρa.extend a b a = some b := by
  simp [AddrRenameMap.extend]

theorem AddrRenameMap.extend_ne {ρa : AddrRenameMap} {a b x : Word} (h : x ≠ a) :
    ρa.extend a b x = ρa x := by
  simp [AddrRenameMap.extend, h]

/-- An identity extension is always a growth — no freshness side condition
    needed, because if `a` were already mapped `IdentityOnDomain` forces it
    to be mapped to `a`. -/
theorem AddrRenameIncr.extend_id {ρa : AddrRenameMap}
    (h_id : IdentityOnDomain ρa) (a : Word) :
    AddrRenameIncr ρa (ρa.extend a a) := by
  intro x x' hx
  grind [AddrRenameMap.extend, IdentityOnDomain]

theorem IdentityOnDomain.extend_id {ρa : AddrRenameMap}
    (h_id : IdentityOnDomain ρa) (a : Word) :
    IdentityOnDomain (ρa.extend a a) := by
  intro x x' hx
  grind [AddrRenameMap.extend, IdentityOnDomain]

/-- Identity extension over a whole block: every cell of `[base, base+n)`
    maps to itself. Regime B for MULTI-CELL roots (a projected dst whose
    fresh root is a tuple) needs the rename defined on the entire block,
    not just its base — `LocalBindingSim`'s block-domain conjunct
    quantifies over all `k < blockSize`. -/
def AddrRenameMap.extendIdRange (ρa : AddrRenameMap) (base : Word) (n : Nat) :
    AddrRenameMap :=
  fun x => if base ≤ x ∧ x < base + n then some x else ρa x

theorem AddrRenameMap.extendIdRange_mem {ρa : AddrRenameMap} {base x : Word}
    {n : Nat} (h1 : base ≤ x) (h2 : x < base + n) :
    ρa.extendIdRange base n x = some x := by
  simp [AddrRenameMap.extendIdRange, h1, h2]

theorem AddrRenameIncr.extendIdRange {ρa : AddrRenameMap}
    (h_id : IdentityOnDomain ρa) (base : Word) (n : Nat) :
    AddrRenameIncr ρa (ρa.extendIdRange base n) := by
  intro x x' hx
  grind [AddrRenameMap.extendIdRange, IdentityOnDomain]

theorem IdentityOnDomain.extendIdRange {ρa : AddrRenameMap}
    (h_id : IdentityOnDomain ρa) (base : Word) (n : Nat) :
    IdentityOnDomain (ρa.extendIdRange base n) := by
  intro x x' hx
  grind [AddrRenameMap.extendIdRange, IdentityOnDomain]

/-- `readWordSeq` only observes memory through `find?`, so two memories
    that agree there read alike (allocation bumps `addrStart`/`allocs`
    but leaves the cell map untouched). -/
theorem mirlite_readWordSeq_congr {m1 m2 : mirlite.Mem}
    (h : ∀ a, mirlite.Mem.find? m1 a = mirlite.Mem.find? m2 a) :
    ∀ (n : Nat) (a : Word), mirlite.readWordSeq m1 a n = mirlite.readWordSeq m2 a n
  | 0, _ => rfl
  | n + 1, a => by
      simp only [mirlite.readWordSeq, h a]
      cases mirlite.Mem.find? m2 a <;>
        simp [mirlite_readWordSeq_congr h n (a + 1)]

/-- A fresh block's identity extension that ALSO maps the block's base
    when the block is EMPTY (a zero-sized local still has an address and
    a binding, and `LocalBindingSim` asks for `ρa base = some base`).
    `extendIdRange` alone leaves a ZST's base unmapped, since its range
    `[base, base)` is empty. -/
def AddrRenameMap.extendBlock (ρa : AddrRenameMap) (base : Word) (n : Nat) :
    AddrRenameMap :=
  (ρa.extend base base).extendIdRange base n

theorem AddrRenameMap.extendBlock_base (ρa : AddrRenameMap) (base : Word) (n : Nat) :
    ρa.extendBlock base n base = some base := by
  by_cases h : base < base + n
  · simp [AddrRenameMap.extendBlock, AddrRenameMap.extendIdRange, h]
  · simp [AddrRenameMap.extendBlock, AddrRenameMap.extendIdRange, h,
      AddrRenameMap.extend]

theorem AddrRenameMap.extendBlock_mem {ρa : AddrRenameMap} {base : Word} {n k : Nat}
    (h : k < n) : ρa.extendBlock base n (base + k) = some (base + k) :=
  AddrRenameMap.extendIdRange_mem (Nat.le_add_right _ _) (Nat.add_lt_add_left h _)

theorem AddrRenameIncr.extendBlock {ρa : AddrRenameMap}
    (h_id : IdentityOnDomain ρa) (base : Word) (n : Nat) :
    AddrRenameIncr ρa (ρa.extendBlock base n) :=
  AddrRenameIncr.trans (AddrRenameIncr.extend_id h_id base)
    (AddrRenameIncr.extendIdRange (IdentityOnDomain.extend_id h_id base) base n)

theorem IdentityOnDomain.extendBlock {ρa : AddrRenameMap}
    (h_id : IdentityOnDomain ρa) (base : Word) (n : Nat) :
    IdentityOnDomain (ρa.extendBlock base n) :=
  IdentityOnDomain.extendIdRange (IdentityOnDomain.extend_id h_id base) base n

/-! ### Lockstep allocation

Both machines allocate with the same bump allocator (`mirlite.allocate`
and `oseair.allocate` are the same function on their own `Mem`), so as
long as their watermarks agree, a fresh allocation on both sides returns the
SAME base address. That is what lets ρa be extended by `.refl` at a fresh
local — `IdentityOnDomain ρa` would be false the moment the two machines
handed out different addresses for corresponding allocations. -/

/-- The two allocators are at the same watermark. -/
def AllocLockstep (mem_mir : mirlite.Mem) (mem_osea : oseair.Mem) : Prop :=
  mem_osea.addrStart = mem_mir.addrStart

/-- Stores do not move the watermark (source side). -/
theorem mirlite_writeWordSeq_addrStart :
    ∀ (values : List mirlite.MemValue) (m : mirlite.Mem) (addr : Word),
      (mirlite.writeWordSeq m addr values).addrStart = m.addrStart
  | [], _, _ => rfl
  | v :: vs, m, addr => by
      rw [mirlite.writeWordSeq, mirlite_writeWordSeq_addrStart vs]
      rfl

/-- Stores do not move the watermark (target side). -/
theorem oseair_writeWordSeq_addrStart :
    ∀ (vals : List Val) (m : oseair.Mem) (addr : Word),
      (oseair.writeWordSeq m addr vals).addrStart = m.addrStart
  | [], _, _ => rfl
  | v :: vs, m, addr => by
      rw [oseair.writeWordSeq, oseair_writeWordSeq_addrStart vs]
      rfl

/-- `AllocLockstep` survives a store on both machines. -/
theorem AllocLockstep.writeWordSeq {m : mirlite.Mem} {m' : oseair.Mem}
    (h : AllocLockstep m m') (addr addr' : Word)
    (values : List mirlite.MemValue) (vals : List Val) :
    AllocLockstep (mirlite.writeWordSeq m addr values)
      (oseair.writeWordSeq m' addr' vals) := by
  unfold AllocLockstep at h ⊢
  rw [oseair_writeWordSeq_addrStart, mirlite_writeWordSeq_addrStart]
  exact h

/-- Lockstep allocation is exactly the statement that corresponding fresh
    allocations agree — the fact ρa's extension needs. -/
theorem AllocLockstep.allocate_eq {m : mirlite.Mem} {m' : oseair.Mem}
    (h : AllocLockstep m m') (sz : Nat) :
    (oseair.allocate m' sz).1 = (mirlite.allocate m sz).1 ∧
      AllocLockstep (mirlite.allocate m sz).2 (oseair.allocate m' sz).2 := by
  unfold AllocLockstep at h ⊢
  exact ⟨h, by simp [mirlite.allocate, oseair.allocate, h]⟩

/-- Forward memory simulation at renamed addresses. -/
def SourceMemSim
  (ρa : AddrRenameMap)
  (ρt : TagRenameMap)
  (mem_mir : mirlite.Mem)
  (mem_osea : oseair.Mem) : Prop :=
  ∀ addr value,
    mirlite.Mem.find? mem_mir addr = some value →
    ∃ addr' value',
      ρa addr = some addr' ∧
      oseair.Mem.find? mem_osea addr' = some value' ∧
      MemValSim ρa ρt value value'

/-- `SourceMemSim` transports along rename growth (renames appear only
    positively). -/
theorem SourceMemSim.rename_mono
    {ρa ρa' : AddrRenameMap} {ρt ρt' : TagRenameMap}
    {m : mirlite.Mem} {m' : oseair.Mem}
    (h_a : AddrRenameIncr ρa ρa') (h_t : TagRenameIncr ρt ρt')
    (h : SourceMemSim ρa ρt m m') : SourceMemSim ρa' ρt' m m' := by
  intro addr value h_find
  obtain ⟨addr', value', h_ra, h_find', h_mvs⟩ := h addr value h_find
  exact ⟨addr', value', h_a _ _ h_ra, h_find', MemValSim.rename_mono h_a h_t h_mvs⟩

/-- Reading the same range on both sides yields `MemValSim`-related
    value lists: found source cells transport through `SourceMemSim`
    (landing at the SAME address, ρa being the identity), and source
    holes read as `.undef`, which refines anything the target holds.
    The copy analog of BRIDGE 2's read half. -/
theorem readWordSeq_sim
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {m : mirlite.Mem} {m' : oseair.Mem}
    (h_id : IdentityOnDomain ρa)
    (h_sms : SourceMemSim ρa ρt m m') :
    ∀ (sz : Nat) (addr : Word),
      ListRel (MemValSim ρa ρt) (mirlite.readWordSeq m addr sz)
        (oseair.readWordSeq m' addr sz) := by
  intro sz
  induction sz with
  | zero =>
      intro addr
      simp [mirlite.readWordSeq, oseair.readWordSeq, ListRel]
  | succ n ih =>
      intro addr
      simp only [mirlite.readWordSeq, oseair.readWordSeq]
      cases h_find : mirlite.Mem.find? m addr with
      | none =>
          cases h_find' : oseair.Mem.find? m' addr with
          | none => exact ⟨trivial, ih (addr + 1)⟩
          | some v' => exact ⟨trivial, ih (addr + 1)⟩
      | some v =>
          obtain ⟨addr', v', h_ra, h_find', h_mvs⟩ := h_sms addr v h_find
          have h_a : addr' = addr := (h_id _ _ h_ra).symm
          rw [h_a] at h_find'
          rw [h_find']
          exact ⟨h_mvs, ih (addr + 1)⟩

/-- The main simulation invariant between a source mirlite state and a
    target OSEA state, both at `stackedBorrows`.
    vs obseq2: `TargetLocalsReady` (a `True` placeholder), `WellFormed`
    (never consumed) and the code half of `CompilerStateWF` are dropped;
    the register half returned 2026-08-21 as `PlaceRegMapBound` (the
    deref/proj write regimes mint temp registers and need them clear of
    bound locals' registers); the perms
    conjunct is `PermSim ρt` instead of literal equality; ρt is
    `TagRenameWF` instead of identity, and `LocalBindingSim` additionally
    records that bound locals carry non-wildcard tags (they are minted by
    `sb_own`), which is what lets BRIDGE 3 fire on local writes.
    `TagRenameBounded` (2026-08-22) is the tag half of the same
    strengthening: every mapped pair sits below both machines' `NextTag`.
    It is what makes ρt EXTENSIBLE — the range bound keeps the extension
    at a fresh pair injective, the domain bound makes it an extension
    rather than an overwrite — and it is therefore a hypothesis of
    `sb_ref_respects_PermSim` (and, when it lands, of the `sb_own`
    member). Re-establishing it is free for every access-only step:
    `sb_write`/`sb_read`/`sb_die` do not touch `NextTag`
    (`sb_*_NextTag` in proof/permsim_transport.lean).
    `AllocLockstep` (2026-08-22) is the memory analogue: the two bump
    allocators sit at the same watermark, so corresponding fresh
    allocations return the SAME base address. Without it `IdentityOnDomain
    ρa` could not survive a fresh local — the two machines would hand out
    different addresses for the same allocation. Re-establishing it is
    free for any fragment that only stores
    (`AllocLockstep.writeWordSeq`).
    `UnboundLocalsUnmapped` (2026-08-22) is `LocalBindingSim`'s converse on
    the mapping component; regime B needs it to know its fragment starts
    with the root `Alloc`. -/
def CompilerInv
  {Γ : Ctx}
  (cs0 : CompilerState)
  (prog : obseq3.Prog Γ)
  (ρa : AddrRenameMap)
  (ρt : TagRenameMap)
  (s_mir : mirlite.State MSB Γ)
  (s_osea : oseair.State MSB) : Prop :=
  ∃ csPrefix,
    targetLabelAt cs0 prog s_mir.pc csPrefix s_osea.pc ∧
    LocalBindingSim ρa ρt s_mir.env s_osea csPrefix ∧
    SourceMemSim ρa ρt s_mir.mem s_osea.mem ∧
    PermSim ρt s_mir.perms s_osea.perms ∧
    IdentityOnDomain ρa ∧
    TagRenameWF ρt ∧
    TagRenameBounded ρt s_mir.perms.NextTag s_osea.perms.NextTag ∧
    AllocLockstep s_mir.mem s_osea.mem ∧
    UnboundLocalsUnmapped s_mir.env csPrefix ∧
    PlaceRegMapBound csPrefix

/-- Register `reg` holds a pointer to `resolved`, and the tag stored there
    grants a mutable write of `len` cells in `perms`. The tag is NOT in
    general `ρt resolved.tag` (proj: fresh internal borrow; deref: whatever
    was stored in the pointer cell) — writability is captured by the
    embedded `useMut` conjunct. -/
def PlaceRegReady
    (ρa : AddrRenameMap)
    (perms : AccessPerms)
    (regMap : oseair.RegMap)
    (reg : Register)
    (resolved : mirlite.PlaceRes)
    (len : Nat) : Prop :=
  ∃ (b' : Word) (t' : Tag),
    ρa resolved.allocBase = some b' ∧
    PtrRegisterEntry regMap reg b' (resolved.addr - resolved.allocBase) resolved.allocSize t' ∧
    ∃ p2,
      MSB.useMut perms
        (b' + (resolved.addr - resolved.allocBase)) len t' = Except.ok p2

/-! ## §D Place-lowering totality -/

theorem placeToRegChecked_local_ok_of_getPlaceInfo
    {Γ : Ctx} {τ layout : LayoutTy}
    {kind : RefKind} {loc : Local Γ τ} {cs : CompilerState} {reg : Register}
    (h_lookup : getPlaceInfo cs loc.idx.1 = some (reg, layout)) :
    ∃ placeOut,
      CheckedCompilerM.value (placeToRegChecked kind (.local loc)) cs = Except.ok placeOut := by
  refine ⟨{
    result := { reg := reg, cleanup := [] },
    evidence := PlaceToRegEvidence.local loc cs reg layout h_lookup
  }, ?_⟩
  simp only [placeToRegChecked, CheckedCompilerM.value, CompilerM.value]
  split
  · rename_i reg' layout' h_branch
    have h_eq : reg' = reg ∧ layout' = layout := by
      simpa [h_branch] using h_lookup
    rcases h_eq with ⟨rfl, rfl⟩
    have h_same : h_branch = h_lookup := Subsingleton.elim _ _
    cases h_same
    rfl
  · rename_i h_branch
    simp [h_branch] at h_lookup

/-- Compute `placeToRegChecked` on an already-mapped local: no compiler-state
    change, and the returned pointer result is the mapped register with no
    cleanup. The run/value pair that lets fragment-computation lemmas step
    over the local arm without touching its dependent match. -/
theorem placeToRegChecked_local_existing
    {Γ : Ctx} {τ layout : LayoutTy}
    {kind : RefKind} {loc : Local Γ τ} {cs : CompilerState} {reg : Register}
    (h : getPlaceInfo cs loc.idx.1 = some (reg, layout)) :
    CheckedCompilerM.run (placeToRegChecked kind (.local loc)) cs = cs ∧
    ∃ placeOut,
      CheckedCompilerM.value (placeToRegChecked kind (.local loc)) cs
        = Except.ok placeOut ∧
      placeOut.result = { reg := reg, cleanup := [] } := by
  simp only [CheckedCompilerM.run, CheckedCompilerM.value, CompilerM.run,
    CompilerM.value, placeToRegChecked]
  refine ⟨?_, ?_⟩
  · split <;> rfl
  · split
    · rename_i reg' layout' h'
      rw [h'] at h
      injection h with h2
      have h_eq : reg' = reg := congrArg Prod.fst h2
      subst h_eq
      exact ⟨_, rfl, rfl⟩
    · rename_i h'
      rw [h'] at h
      cases h

/-- The general-projection arm's equation, for a base that is NOT itself a
    projection (the reassociation arm handles those). `placeToRegChecked`
    is well-founded since the reassociation arm landed (2026-08-27), so
    this is proved from the equation lemmas per root constructor rather
    than by `rfl`. -/
theorem placeToRegChecked_proj_root_eq
    {Γ : Ctx} {σ τ : LayoutTy}
    {kind : RefKind} {base : Place Γ σ} (path : PathTo σ τ)
    (h_np : ∀ (σ' : LayoutTy) (b : Place Γ σ') (q : PathTo σ' σ),
      base = b.proj q → False) :
    placeToRegChecked kind (.proj base path)
      = (do
          let baseOut ← placeToRegChecked kind base
          let baseRes := baseOut.result
          let offset := pathOffset path
          if h_offset : offset = 0 then
            pure {
              result := baseRes,
              evidence := PlaceToRegEvidence.projZero base path baseRes
                baseOut.evidence h_offset
            }
          else
            let tmpReg ← CheckedCompilerM.lift freshRegM
            let _ ← CheckedCompilerM.lift
              (emitM [Instr.Assgn tmpReg (borrowRhs kind (blockSize τ) baseRes.reg offset)])
            pure {
              result := { reg := tmpReg,
                          cleanup := baseRes.cleanup ++ [(tmpReg, blockSize τ)] },
              evidence := PlaceToRegEvidence.projOffset base path baseRes tmpReg
                baseOut.evidence h_offset
            }) := by
  cases base with
  | «local» loc => simp only [placeToRegChecked]
  | proj b q => exact absurd rfl (h_np _ b q)
  | deref pp => simp only [placeToRegChecked]

/-- The reassociation arm's equation. -/
theorem placeToRegChecked_proj_assoc_eq
    {Γ : Ctx} {ρ σ τ : LayoutTy}
    {kind : RefKind} {b : Place Γ ρ} (q : PathTo ρ σ) (p : PathTo σ τ) :
    placeToRegChecked kind (.proj (.proj b q) p)
      = (do
          let out ← placeToRegChecked kind (.proj b (q.append p))
          pure {
            result := out.result,
            evidence := PlaceToRegEvidence.projAssoc b q p out.result out.evidence
          }) := by
  simp only [placeToRegChecked]

/-! ## Flattening transfer: the two spellings of a nested-projection
    assignment compile to the SAME run (the lowering reassociates), and
    the composed spelling's success transfers back to the nested one. -/

theorem compileStmt_assign_proj_assoc_run
    {Γ : Ctx} {σ1 σ2 τ : LayoutTy}
    (b : Place Γ σ1) (q : PathTo σ1 σ2) (p : PathTo σ2 τ)
    (rhs : RExpr Γ τ) (cs : CompilerState) :
    CheckedCompilerM.run
        (compileStmtChecked (.assign (.proj (.proj b q) p) rhs)) cs
      = CheckedCompilerM.run
          (compileStmtChecked (.assign (.proj b (q.append p)) rhs)) cs := by
  have h_bind_n : compileStmtChecked (.assign (.proj (.proj b q) p) rhs)
      = (do
          let _ ← CheckedCompilerM.lift
            (ensurePlaceRoot (Place.proj (Place.proj b q) p))
          let pre ← compileRExprPreChecked rhs
          let dstOut ← placeToRegChecked RefKind.Mut (.proj (.proj b q) p)
          let dstRes := dstOut.result
          let _ ← CheckedCompilerM.lift (emitM (pre.store dstRes.reg))
          let _ ← CheckedCompilerM.lift (emitM (cleanupInstrs pre.postCleanup))
          let _ ← CheckedCompilerM.lift (emitM (cleanupInstrs dstRes.cleanup))
          pure {
            result := (),
            evidence := StmtEvidence.assignPlace (.proj (.proj b q) p) rhs dstRes
              dstOut.evidence (pre.ev dstRes.reg)
          }) := rfl
  have h_bind_c : compileStmtChecked (.assign (.proj b (q.append p)) rhs)
      = (do
          let _ ← CheckedCompilerM.lift
            (ensurePlaceRoot (Place.proj b (q.append p)))
          let pre ← compileRExprPreChecked rhs
          let dstOut ← placeToRegChecked RefKind.Mut (.proj b (q.append p))
          let dstRes := dstOut.result
          let _ ← CheckedCompilerM.lift (emitM (pre.store dstRes.reg))
          let _ ← CheckedCompilerM.lift (emitM (cleanupInstrs pre.postCleanup))
          let _ ← CheckedCompilerM.lift (emitM (cleanupInstrs dstRes.cleanup))
          pure {
            result := (),
            evidence := StmtEvidence.assignPlace (.proj b (q.append p)) rhs dstRes
              dstOut.evidence (pre.ev dstRes.reg)
          }) := rfl
  rw [h_bind_n, h_bind_c]
  have h_ens : (ensurePlaceRoot (Place.proj (Place.proj b q) p) : CompilerM Unit)
      = ensurePlaceRoot (Place.proj b (q.append p)) := rfl
  rw [h_ens]
  rw [CheckedCompilerM.run_bind, CheckedCompilerM.run_bind]
  simp only [CheckedCompilerM.value_lift, CheckedCompilerM.run_lift]
  rw [CheckedCompilerM.run_bind, CheckedCompilerM.run_bind]
  cases h_pre : CheckedCompilerM.value (compileRExprPreChecked rhs)
      ((ensurePlaceRoot (Place.proj b (q.append p))).run cs) with
  | error e => rfl
  | ok pre =>
      simp only
      rw [CheckedCompilerM.run_bind, CheckedCompilerM.run_bind,
        placeToRegChecked_proj_assoc_eq q p,
        CheckedCompilerM.run_bind, CheckedCompilerM.value_bind]
      cases h_dst : CheckedCompilerM.value
          (placeToRegChecked RefKind.Mut (.proj b (q.append p)))
          (CheckedCompilerM.run (compileRExprPreChecked rhs)
            ((ensurePlaceRoot (Place.proj b (q.append p))).run cs)) with
      | error e => rfl
      | ok out =>
          simp only [CheckedCompilerM.value_pure, CheckedCompilerM.run_pure]
          rfl

/-- The composed spelling's lowering success transfers to the nested
    spelling. -/
theorem compileStmt_assign_proj_assoc_value
    {Γ : Ctx} {σ1 σ2 τ : LayoutTy}
    (b : Place Γ σ1) (q : PathTo σ1 σ2) (p : PathTo σ2 τ)
    (rhs : RExpr Γ τ) (cs : CompilerState) {so} :
    CheckedCompilerM.value
        (compileStmtChecked (.assign (.proj b (q.append p)) rhs)) cs
      = Except.ok so →
    ∃ so', CheckedCompilerM.value
        (compileStmtChecked (.assign (.proj (.proj b q) p) rhs)) cs
      = Except.ok so' := by
  intro h
  have h_run := compileStmt_assign_proj_assoc_run b q p rhs cs
  -- value follows the same bind spine; mirror the run proof
  revert h
  have h_bind_n : compileStmtChecked (.assign (.proj (.proj b q) p) rhs)
      = (do
          let _ ← CheckedCompilerM.lift
            (ensurePlaceRoot (Place.proj (Place.proj b q) p))
          let pre ← compileRExprPreChecked rhs
          let dstOut ← placeToRegChecked RefKind.Mut (.proj (.proj b q) p)
          let dstRes := dstOut.result
          let _ ← CheckedCompilerM.lift (emitM (pre.store dstRes.reg))
          let _ ← CheckedCompilerM.lift (emitM (cleanupInstrs pre.postCleanup))
          let _ ← CheckedCompilerM.lift (emitM (cleanupInstrs dstRes.cleanup))
          pure {
            result := (),
            evidence := StmtEvidence.assignPlace (.proj (.proj b q) p) rhs dstRes
              dstOut.evidence (pre.ev dstRes.reg)
          }) := rfl
  have h_bind_c : compileStmtChecked (.assign (.proj b (q.append p)) rhs)
      = (do
          let _ ← CheckedCompilerM.lift
            (ensurePlaceRoot (Place.proj b (q.append p)))
          let pre ← compileRExprPreChecked rhs
          let dstOut ← placeToRegChecked RefKind.Mut (.proj b (q.append p))
          let dstRes := dstOut.result
          let _ ← CheckedCompilerM.lift (emitM (pre.store dstRes.reg))
          let _ ← CheckedCompilerM.lift (emitM (cleanupInstrs pre.postCleanup))
          let _ ← CheckedCompilerM.lift (emitM (cleanupInstrs dstRes.cleanup))
          pure {
            result := (),
            evidence := StmtEvidence.assignPlace (.proj b (q.append p)) rhs dstRes
              dstOut.evidence (pre.ev dstRes.reg)
          }) := rfl
  rw [h_bind_n, h_bind_c]
  have h_ens : (ensurePlaceRoot (Place.proj (Place.proj b q) p) : CompilerM Unit)
      = ensurePlaceRoot (Place.proj b (q.append p)) := rfl
  rw [h_ens]
  rw [CheckedCompilerM.value_bind, CheckedCompilerM.value_bind]
  simp only [CheckedCompilerM.value_lift, CheckedCompilerM.run_lift]
  rw [CheckedCompilerM.value_bind, CheckedCompilerM.value_bind]
  cases h_pre : CheckedCompilerM.value (compileRExprPreChecked rhs)
      ((ensurePlaceRoot (Place.proj b (q.append p))).run cs) with
  | error e => intro h; simp at h
  | ok pre =>
      simp only
      rw [CheckedCompilerM.value_bind,
        placeToRegChecked_proj_assoc_eq q p,
        CheckedCompilerM.value_bind, CheckedCompilerM.value_bind,
        CheckedCompilerM.run_bind]
      cases h_dst : CheckedCompilerM.value
          (placeToRegChecked RefKind.Mut (.proj b (q.append p)))
          (CheckedCompilerM.run (compileRExprPreChecked rhs)
            ((ensurePlaceRoot (Place.proj b (q.append p))).run cs)) with
      | error e => intro h; simp at h
      | ok out =>
          simp only [CheckedCompilerM.value_pure, CheckedCompilerM.run_pure]
          intro h
          exact ⟨_, rfl⟩

theorem placeToRegChecked_proj_ok_of_baseOk
    {Γ : Ctx} {σ τ : LayoutTy}
    {kind : RefKind} {cs : CompilerState}
    {base : Place Γ σ} {path : PathTo σ τ}
    (h_np : ∀ (σ' : LayoutTy) (b : Place Γ σ') (q : PathTo σ' σ),
      base = b.proj q → False)
    (baseOut : ResultWithEvidence PtrResult (PlaceToRegEvidence kind base))
    (h_baseOut : CheckedCompilerM.value (placeToRegChecked kind base) cs = Except.ok baseOut) :
    ∃ placeOut,
      CheckedCompilerM.value (placeToRegChecked kind (.proj base path)) cs = Except.ok placeOut := by
  rw [placeToRegChecked_proj_root_eq path h_np]
  by_cases h_offset : pathOffset path = 0
  · let baseRes := baseOut.result
    refine ⟨{
      result := baseRes,
      evidence := PlaceToRegEvidence.projZero base path baseRes baseOut.evidence h_offset
    }, ?_⟩
    simp [h_baseOut, h_offset, baseRes]
  · let tmpReg := CompilerM.value freshRegM (CheckedCompilerM.run (placeToRegChecked kind base) cs)
    refine ⟨{
      result := { reg := tmpReg, cleanup := baseOut.result.cleanup ++ [(tmpReg, blockSize τ)] },
      evidence := PlaceToRegEvidence.projOffset base path baseOut.result tmpReg
        baseOut.evidence h_offset
    }, ?_⟩
    simp [h_baseOut, h_offset, tmpReg]

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
    result := { reg := loadedReg, cleanup := [] },
    evidence := PlaceToRegEvidence.deref ptrPlace ptrOut.result loadedReg ptrOut.evidence
  }, ?_⟩
  simp [placeToRegChecked, h_ptrOut, loadedReg]

theorem placeToRegChecked_ok_of_placeInputsMapped
    {Γ : Ctx} {τ : LayoutTy}
    {cs : CompilerState}
    {kind : RefKind}
    {p : Place Γ τ}
    (h_mapped : PlaceInputsMapped cs p) :
    ∃ placeOut,
      CheckedCompilerM.value (placeToRegChecked kind p) cs = Except.ok placeOut := by
  induction τ, kind, p using placeToRegChecked.induct with
  | case1 kind τ loc =>
      rcases h_mapped with ⟨reg, layout, h_lookup⟩
      exact placeToRegChecked_local_ok_of_getPlaceInfo
        (kind := kind) (loc := loc) (cs := cs) (reg := reg) (layout := layout) h_lookup
  | case2 kind τ σ ρ b q path ih =>
      rcases ih h_mapped with ⟨out, h_out⟩
      refine ⟨{ result := out.result,
                evidence := PlaceToRegEvidence.projAssoc b q path out.result out.evidence }, ?_⟩
      rw [placeToRegChecked_proj_assoc_eq]
      simp [CheckedCompilerM.value_bind, h_out, CheckedCompilerM.value_pure]
  | case3 kind τ σ base path h_np ih =>
      rcases ih h_mapped with ⟨baseOut, h_baseOut⟩
      exact placeToRegChecked_proj_ok_of_baseOk (kind := kind) (cs := cs)
        (base := base) (path := path) h_np baseOut h_baseOut
  | case4 kind τ ptrPlace ih =>
      rcases ih h_mapped with ⟨ptrOut, h_ptrOut⟩
      exact placeToRegChecked_deref_ok_of_ptrOk (kind := kind) (cs := cs)
        (ptrPlace := ptrPlace) ptrOut h_ptrOut

theorem placeInputsMapped_of_localBindingSim_resolvePlace
  {Γ : Ctx} {τ : LayoutTy}
  {ρa : AddrRenameMap} {ρt : TagRenameMap}
  {s_mir : mirlite.State MSB Γ}
  {s_osea : oseair.State MSB}
  {cs : CompilerState}
  {p : Place Γ τ}
  {resolved : mirlite.PlaceRes}
  (h_lbs : LocalBindingSim ρa ρt s_mir.env s_osea cs)
  (h_res : mirlite.resolvePlace? s_mir p = some resolved) :
  PlaceInputsMapped cs p := by
  induction p generalizing resolved with
  | «local» loc =>
      cases h_lookup : mirlite.Env.lookup s_mir.env loc with
      | none =>
          simp [mirlite.resolvePlace?, h_lookup] at h_res
      | some binding =>
          rcases h_lbs loc binding h_lookup with ⟨reg, base, tag, h_placeInfo, _, _, _, _⟩
          exact ⟨reg, _, h_placeInfo⟩
  | proj base path ih =>
      cases h_base : mirlite.resolvePlace? s_mir base with
      | none =>
          simp [mirlite.resolvePlace?, h_base] at h_res
      | some resolvedBase =>
          exact ih h_base
  | deref ptrPlace ih =>
      cases h_ptr : mirlite.resolvePlace? s_mir ptrPlace with
      | none =>
          simp [mirlite.resolvePlace?, h_ptr] at h_res
      | some resolvedPtr =>
          exact ih h_ptr

theorem placeToRegChecked_ok_of_resolvePlace
    {Γ : Ctx} {τ : LayoutTy}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {cs : CompilerState}
    {kind : RefKind}
    {p : Place Γ τ}
    {resolved : mirlite.PlaceRes}
    (h_lbs : LocalBindingSim ρa ρt s_mir.env s_osea cs)
    (h_res : mirlite.resolvePlace? s_mir p = some resolved) :
    ∃ placeOut,
      CheckedCompilerM.value (placeToRegChecked kind p) cs = Except.ok placeOut := by
  exact placeToRegChecked_ok_of_placeInputsMapped
    (cs := cs)
    (kind := kind)
    (p := p)
    (placeInputsMapped_of_localBindingSim_resolvePlace h_lbs h_res)

/-- When every local leaf of `p` is already mapped, `ensurePlaceRoot` is a
    no-op on the compiler state (its `ensureLocalRegE` hits the `existing`
    branch). Needed because the v3 assign-place case runs `ensurePlaceRoot`
    before `placeToRegChecked`. -/
theorem ensurePlaceRoot_run_eq_of_mapped
    {Γ : Ctx} {τ : LayoutTy}
    {cs : CompilerState}
    {p : Place Γ τ}
    (h_mapped : PlaceInputsMapped cs p) :
    CompilerM.run (ensurePlaceRoot p) cs = cs := by
  induction p with
  | «local» loc =>
      rcases h_mapped with ⟨reg, layout, h_lookup⟩
      simp only [ensurePlaceRoot, CompilerM.run_bind]
      have h_run : CompilerM.run (ensureLocalRegE loc) cs = cs := by
        unfold CompilerM.run ensureLocalRegE
        split
        · rfl
        · rename_i h_none
          simp [h_none] at h_lookup
      simp [h_run]
  | proj base path ih =>
      exact ih h_mapped
  | deref ptrPlace ih =>
      exact ih h_mapped

/-- `ensurePlaceRoot` establishes its own postcondition: after it runs,
    every local leaf reachable from the ROOT of `p` is mapped (the fresh
    branch of `ensureLocalRegE` records the allocation in `placeRegMap`).
    Since `PlaceInputsMapped` only constrains the root chain, this is
    exactly `PlaceInputsMapped` for `p`. -/
theorem ensurePlaceRoot_maps_root
    {Γ : Ctx} {τ : LayoutTy}
    (p : Place Γ τ) (cs : CompilerState) :
    PlaceInputsMapped (CompilerM.run (ensurePlaceRoot p) cs) p := by
  induction p with
  | «local» loc =>
      show ∃ reg layout,
        getPlaceInfo (CompilerM.run (ensurePlaceRoot (.local loc)) cs) loc.idx.1
          = some (reg, layout)
      simp only [ensurePlaceRoot, CompilerM.run_bind, CompilerM.run_pure]
      unfold CompilerM.run ensureLocalRegE
      split
      · rename_i reg layout h_lookup
        exact ⟨reg, layout, h_lookup⟩
      · rename_i h_lookup
        exact ⟨_, _, by
          simp only [setPlaceInfo, getPlaceInfo, freshReg, List.lookup, beq_self_eq_true]
          exact rfl⟩
  | proj base path ih => exact ih
  | deref ptrPlace ih => exact ih

/-- Compute `ensureLocalRegE` on an already-mapped local: no compiler-state
    change, and the returned pointer result is the mapped register. -/
theorem ensureLocalRegE_existing
    {Γ : Ctx} {τ : LayoutTy} {loc : Local Γ τ} {cs : CompilerState}
    {reg : Register}
    (h : getPlaceInfo cs loc.idx.1 = some (reg, τ)) :
    CompilerM.run (ensureLocalRegE loc) cs = cs ∧
    (CompilerM.value (ensureLocalRegE loc) cs).result = { reg := reg, cleanup := [] } := by
  unfold CompilerM.run CompilerM.value ensureLocalRegE
  split
  · rename_i reg' layout' h'
    rw [h'] at h
    injection h with h2
    have h_eq : reg' = reg := congrArg Prod.fst h2
    subst h_eq
    exact ⟨rfl, rfl⟩
  · rename_i h'
    rw [h'] at h
    cases h

/-- `setPlaceInfo` at the same index. -/
theorem getPlaceInfo_setPlaceInfo_self (cs : CompilerState) (idx : Nat)
    (info : PlaceInfo) :
    getPlaceInfo (setPlaceInfo cs idx info) idx = some info := by
  simp [setPlaceInfo, getPlaceInfo, List.lookup]

/-- `setPlaceInfo` at a different index. -/
theorem getPlaceInfo_setPlaceInfo_ne (cs : CompilerState) {idx idx' : Nat}
    (h : idx' ≠ idx) (info : PlaceInfo) :
    getPlaceInfo (setPlaceInfo cs idx info) idx' = getPlaceInfo cs idx' := by
  have hb : (idx' == idx) = false := by
    cases h_eq : idx' == idx
    · rfl
    · exact absurd (eq_of_beq h_eq) h
  simp [setPlaceInfo, getPlaceInfo, List.lookup, hb]

/-- A `nextReg` bump touches only the register counter. -/
theorem getPlaceInfo_setNextReg (cs : CompilerState) (n idx : Nat) :
    getPlaceInfo { cs with nextReg := n } idx = getPlaceInfo cs idx := rfl

/-- `emit` touches only code and labels. -/
theorem getPlaceInfo_emit (cs : CompilerState) (is : List Instr) (idx : Nat) :
    getPlaceInfo (emit cs is) idx = getPlaceInfo cs idx := rfl

/-- Compute `ensureLocalRegE` on an UNMAPPED local: a fresh register, an
    emitted `Alloc`, and the register recorded in `placeRegMap`. -/
theorem ensureLocalRegE_fresh
    {Γ : Ctx} {τ : LayoutTy} {loc : Local Γ τ} {cs : CompilerState}
    (h : getPlaceInfo cs loc.idx.1 = none) :
    CompilerM.run (ensureLocalRegE loc) cs
      = setPlaceInfo
          (emit { cs with nextReg := cs.nextReg + 1 }
            [Instr.Assgn (Register.R cs.nextReg) (Rhs.Alloc (layoutToTyVal τ))])
          loc.idx.1 (Register.R cs.nextReg, τ) ∧
    (CompilerM.value (ensureLocalRegE loc) cs).result
      = { reg := Register.R cs.nextReg, cleanup := [] } := by
  unfold CompilerM.run CompilerM.value ensureLocalRegE
  split
  · rename_i reg layout h'
    rw [h'] at h
    exact absurd h (by simp)
  · exact ⟨rfl, rfl⟩

/-- Emitting the empty instruction list is a no-op on the compiler state
    (the deref/cleanup lowering paths emit `cleanupInstrs [] = []`). -/
theorem emit_nil (cs : CompilerState) : emit cs [] = cs := by
  show ({ cs with
    nextLabel := cs.nextLabel + 0,
    code := fun label =>
      if cs.nextLabel ≤ label ∧ label < cs.nextLabel + 0 then
        ([] : List Instr).get? (label - cs.nextLabel)
      else cs.code label } : CompilerState) = cs
  have h_code : (fun label =>
      if cs.nextLabel ≤ label ∧ label < cs.nextLabel + 0 then
        ([] : List Instr).get? (label - cs.nextLabel)
      else cs.code label) = cs.code := by
    funext label
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact absurd (Nat.lt_of_le_of_lt h1 h2) (Nat.lt_irrefl _)
  rw [h_code]
  show ({ cs with nextLabel := cs.nextLabel + 0 } : CompilerState) = cs
  rw [Nat.add_zero]

/-- The compiled fragment of a constant write to an UNMAPPED local is two
    instructions: the root `Alloc` that `ensurePlaceRoot` emits (mirroring
    mirlite's `preparePlaceAssign`) followed by the `CStore`. -/
theorem compileStmt_local_fresh_run
    {Γ : Ctx} {loc : Local Γ obseq.LayoutTy.NatL} {cs : CompilerState}
    (v : Word)
    (h : getPlaceInfo cs loc.idx.1 = none) :
    CheckedCompilerM.run
        (compileStmtChecked (Stmt.assign (.local loc) (.constInit v))) cs
      = emit
          (setPlaceInfo
            (emit { cs with nextReg := cs.nextReg + 1 }
              [Instr.Assgn (Register.R cs.nextReg)
                (Rhs.Alloc (layoutToTyVal obseq.LayoutTy.NatL))])
            loc.idx.1 (Register.R cs.nextReg, obseq.LayoutTy.NatL))
          [Instr.CStore obseq.TyVal.NatTy [Val.Dat v] (Register.R cs.nextReg)] := by
  obtain ⟨h_run, h_val⟩ := ensureLocalRegE_fresh (loc := loc) h
  have h_pi : getPlaceInfo
      (setPlaceInfo
        (emit { cs with nextReg := cs.nextReg + 1 }
          [Instr.Assgn (Register.R cs.nextReg)
            (Rhs.Alloc (layoutToTyVal obseq.LayoutTy.NatL))])
        loc.idx.1 (Register.R cs.nextReg, obseq.LayoutTy.NatL))
      loc.idx.1 = some (Register.R cs.nextReg, obseq.LayoutTy.NatL) :=
    getPlaceInfo_setPlaceInfo_self _ _ _
  simp [compileStmtChecked, compileRExprToChecked, compileRExprPreChecked,
    CompilerM.run_bind, CompilerM.run_pure, h_run, h_val,
    placeToRegChecked, h_pi]
  simp [CompilerM.run, CompilerM.value, emitM, cleanupInstrs, emit_nil]

/-! ## §E Fragment layout + emit-preserves-memory -/

def FragmentInstalledAtLabel {α} (m : CompilerM α) (cs : CompilerState)
    (baseLabel : Nat) (prog : oseair.Prog) : Prop :=
  let n := (CompilerM.run m cs).nextLabel - cs.nextLabel
  ∀ (i : Fin n), prog (baseLabel + i.1) = (CompilerM.run m cs).code (cs.nextLabel + i.1)

def FragInstalled {α} (m : CompilerM α) (cs : CompilerState)
    (s : oseair.State MSB) (prog : oseair.Prog) : Prop :=
  let n := (CompilerM.run m cs).nextLabel - cs.nextLabel
  ∀ (i : Fin n), prog (s.pc + i.1) = (CompilerM.run m cs).code (cs.nextLabel + i.1)

def FragmentLength {α} (m : CompilerM α) (cs : CompilerState) : Nat :=
  (CompilerM.run m cs).nextLabel - cs.nextLabel

def FragmentEndLabel {α} (m : CompilerM α) (cs : CompilerState) : Nat :=
  (CompilerM.run m cs).nextLabel

theorem FragmentInstalledAtLabel.toFragInstalled
    {α} {m : CompilerM α} {cs : CompilerState}
    {baseLabel : Nat} {s : oseair.State MSB} {prog : oseair.Prog}
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
    {regs : List (Register × Nat)} {instr : Instr}
    (h_mem : instr ∈ cleanupInstrs regs) :
    InstrPreservesMem instr := by
  simp [cleanupInstrs] at h_mem
  rcases h_mem with ⟨reg, len, _h_reg, h_eq⟩
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
    (kind : RefKind) (dst base : Register) (len : Nat) (offset : Word) :
    EmitsPreservesMem
      (emitM [Instr.Assgn dst (borrowRhs kind len base offset)]) := by
  apply emitM_emits_preserves_mem
  intro instr h_mem
  simp [borrowRhs] at h_mem
  subst instr
  simp [InstrPreservesMem, RhsPreservesMem]

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
    (regs : List (Register × Nat)) :
    EmitsPreservesMem (emitM (cleanupInstrs regs)) := by
  apply emitM_emits_preserves_mem
  intro instr h_mem
  exact cleanupInstrs_mem_preserves h_mem

/-- Everything `placeToRegChecked` emits preserves target memory —
    borrows, loads, and cleanup `Die`s only. Structural induction over the
    place, gluing the `checkedEmitsPreservesMem_*` combinators. -/
theorem placeToRegChecked_emits_preserves_mem
    {Γ : Ctx} {τ : LayoutTy}
    (kind : RefKind) (p : Place Γ τ) :
    EmitsPreservesMem (placeToRegChecked kind p).toCompilerM := by
  induction τ, kind, p using placeToRegChecked.induct with
  | case1 kind τ loc =>
      intro cs label h_lo h_hi instr h_code
      have h_next :
          (CompilerM.run (placeToRegChecked kind (.local loc)).toCompilerM cs).nextLabel
            = cs.nextLabel := by
        show ((placeToRegChecked kind (.local loc)).toCompilerM cs).2.1.nextLabel
          = cs.nextLabel
        simp only [placeToRegChecked]
        split <;> rfl
      rw [h_next] at h_hi
      exact False.elim ((Nat.not_lt_of_ge h_lo) h_hi)
  | case2 kind τ σ ρ b q path ih =>
      -- reassociated nested projection: bind of the recursion + pure
      simp only [placeToRegChecked]
      exact checkedEmitsPreservesMem_bind
        (m := placeToRegChecked kind (.proj b (q.append path))) ih
        (fun _ => checkedEmitsPreservesMem_pure _)
  | case3 kind τ σ base path h_np ih =>
      simp only [placeToRegChecked]
      refine checkedEmitsPreservesMem_bind (m := placeToRegChecked kind base)
        ih (fun baseOut => ?_)
      by_cases hoff : pathOffset path = 0
      · simp only [hoff, dite_true]
        exact checkedEmitsPreservesMem_pure _
      · simp only [hoff, dite_false]
        refine checkedEmitsPreservesMem_bind
          (checkedEmitsPreservesMem_lift freshRegM_emits_preserves_mem)
          (fun tmpReg => ?_)
        refine checkedEmitsPreservesMem_bind
          (checkedEmitsPreservesMem_lift
            (emitM_single_borrow_preserves_mem kind tmpReg baseOut.result.reg
              _ (pathOffset path)))
          (fun _ => ?_)
        exact checkedEmitsPreservesMem_pure _
  | case4 kind τ ptrPlace ih =>
      simp only [placeToRegChecked]
      refine checkedEmitsPreservesMem_bind (m := placeToRegChecked RefKind.Shared ptrPlace)
        ih (fun ptrOut => ?_)
      refine checkedEmitsPreservesMem_bind
        (checkedEmitsPreservesMem_lift freshRegM_emits_preserves_mem)
        (fun loadedReg => ?_)
      refine checkedEmitsPreservesMem_bind
        (checkedEmitsPreservesMem_lift
          (emitM_single_load_preserves_mem loadedReg ptrOut.result.reg))
        (fun _ => ?_)
      refine checkedEmitsPreservesMem_bind
        (checkedEmitsPreservesMem_lift (emitM_cleanup_preserves_mem ptrOut.result.cleanup))
        (fun _ => ?_)
      exact checkedEmitsPreservesMem_pure _

/-! ## §F Execution helpers -/

theorem lookup_filter_ne {α β : Type} [BEq α] [LawfulBEq α] {a addr : α} (hne : a ≠ addr) :
    (l : List (α × β)) →
    List.lookup a (l.filter (fun p => p.1 != addr)) = List.lookup a l
  | [] => rfl
  | (k, val) :: ps => by
      have ih := lookup_filter_ne (β := β) hne ps
      by_cases hk : k = addr
      · subst hk
        rw [List.filter_cons_of_neg (by simp)]
        rw [ih, List.lookup_cons]
        have hb : (a == k) = false := by simp [hne]
        rw [hb]
      · rw [List.filter_cons_of_pos (by simp [hk]), List.lookup_cons, List.lookup_cons, ih]

instance : LawfulBEq Register where
  eq_of_beq {a b} h := by
    cases a with | R n => cases b with | R m =>
      have h' : (n == m) = true := h
      simp only [beq_iff_eq] at h'
      simp [h']
  rfl {a} := by
    cases a with | R n =>
      show (n == n) = true
      simp

theorem RegMap.lookup_insert_self (r : oseair.RegMap) (reg : Register)
    (v : obseq.TyVal × List Val) :
    oseair.RegMap.lookup (oseair.RegMap.insert r reg v) reg = some v := by
  simp [oseair.RegMap.insert, oseair.RegMap.lookup, List.lookup]

theorem RegMap.lookup_insert_ne (r : oseair.RegMap) {reg' reg : Register}
    (h : reg' ≠ reg) (v : obseq.TyVal × List Val) :
    oseair.RegMap.lookup (oseair.RegMap.insert r reg v) reg'
      = oseair.RegMap.lookup r reg' := by
  show List.lookup reg' ((reg, v) :: r.filter (fun p => p.1 != reg))
      = List.lookup reg' r
  rw [List.lookup_cons]
  have hb : (reg' == reg) = false := by
    cases h_eq : reg' == reg
    · rfl
    · exact absurd (eq_of_beq h_eq) h
  rw [hb]
  exact lookup_filter_ne h r

/-- `LocalBindingSim` transports along rename growth (renames appear only
    positively). -/
theorem LocalBindingSim.rename_mono
    {Γ : Ctx} {ρa ρa' : AddrRenameMap} {ρt ρt' : TagRenameMap}
    {env : mirlite.Env Γ} {s : oseair.State MSB} {cs : CompilerState}
    (h_a : AddrRenameIncr ρa ρa') (h_t : TagRenameIncr ρt ρt')
    (h_lbs : LocalBindingSim ρa ρt env s cs) :
    LocalBindingSim ρa' ρt' env s cs := by
  intro τ loc binding h_env
  obtain ⟨reg, base, tag, h_pi, h_entry, h_ra, h_rt, h_nw, h_dom⟩ :=
    h_lbs loc binding h_env
  exact ⟨reg, base, tag, h_pi, h_entry, h_a _ _ h_ra, h_t _ _ h_rt, h_nw,
    fun k hk => ⟨(h_dom k hk).choose, h_a _ _ (h_dom k hk).choose_spec⟩⟩

/-- `LocalBindingSim` reads the target state only through its register
    file. -/
theorem LocalBindingSim.reg_congr
    {Γ : Ctx} {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {env : mirlite.Env Γ} {s s' : oseair.State MSB} {cs : CompilerState}
    (h_reg : s'.reg = s.reg)
    (h : LocalBindingSim ρa ρt env s cs) :
    LocalBindingSim ρa ρt env s' cs := by
  intro τ loc binding h_env
  obtain ⟨reg, base, tag, h_pi, h_entry, h_ra, h_rt, h_nw, h_dom⟩ := h loc binding h_env
  exact ⟨reg, base, tag, h_pi, by rw [show s'.reg = s.reg from h_reg]; exact h_entry,
    h_ra, h_rt, h_nw, h_dom⟩

/-- Inserting a value at a fresh register (index at or above the compiler's
    `nextReg`) preserves `LocalBindingSim`: no bound local can be mapped to
    it, by `PlaceRegMapBound`. Reused by every fragment that mints a temp
    register (deref `Load`, proj `Borrow`, copy's value registers). -/
theorem LocalBindingSim.insert_fresh_reg
    {Γ : Ctx} {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {env : mirlite.Env Γ} {s s' : oseair.State MSB} {cs : CompilerState}
    {n : Nat} {val : obseq.TyVal × List Val}
    (h_lbs : LocalBindingSim ρa ρt env s cs)
    (h_prb : PlaceRegMapBound cs)
    (h_ge : cs.nextReg ≤ n)
    (h_reg : s'.reg = oseair.RegMap.insert s.reg (Register.R n) val) :
    LocalBindingSim ρa ρt env s' cs := by
  intro τ loc binding h_env
  obtain ⟨reg, base, tag, h_pi, h_entry, h_ra, h_rt, h_nw, h_dom⟩ := h_lbs loc binding h_env
  refine ⟨reg, base, tag, h_pi, ?_, h_ra, h_rt, h_nw, h_dom⟩
  have h_below := h_prb _ _ _ h_pi
  show oseair.RegMap.lookup s'.reg reg = _
  rw [h_reg]
  cases reg with
  | R m =>
    have h_ne : Register.R m ≠ Register.R n := by
      intro h_eq
      injection h_eq with h_eq
      subst h_eq
      exact absurd h_below (Nat.not_lt.mpr h_ge)
    rw [RegMap.lookup_insert_ne _ h_ne]
    exact h_entry

/-- `LocalBindingSim` only consults the compiler state through
    `getPlaceInfo`, so it transfers across compiler states with equal
    place-register maps (fragment runs never shrink the map). -/
theorem LocalBindingSim.placeRegMap_congr
    {Γ : Ctx} {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {env : mirlite.Env Γ} {s : oseair.State MSB} {cs cs' : CompilerState}
    (h_prm : cs'.placeRegMap = cs.placeRegMap)
    (h_lbs : LocalBindingSim ρa ρt env s cs) :
    LocalBindingSim ρa ρt env s cs' := by
  intro τ loc binding h_env
  obtain ⟨reg, base, tag, h_pi, h_entry, h_ra, h_rt, h_nw, h_dom⟩ := h_lbs loc binding h_env
  refine ⟨reg, base, tag, ?_, h_entry, h_ra, h_rt, h_nw, h_dom⟩
  show cs'.placeRegMap.lookup loc.idx.1 = _
  rw [h_prm]
  exact h_pi

/-- Invert a successful mirlite access-resolution of `*ploc` for a bound
    pointer local: the pointer cell was SB-read through the binding tag and
    holds a `ptrVal`, whose fields are the resolved place. Reused by the
    deref regimes of const-write, copy, and ref. -/
theorem resolvePlaceAcc_deref_local_inversion
    {Γ : Ctx} {τ : LayoutTy}
    {s : mirlite.State MSB Γ}
    {ploc : Local Γ (obseq.LayoutTy.PtrL τ)}
    {pbind : mirlite.Binding}
    {resolved : mirlite.PlaceRes} {permsD : MSB.State}
    (h_env : mirlite.Env.lookup s.env ploc = some pbind)
    (h_res : mirlite.resolvePlaceAcc MSB s (.deref (.local ploc)) = .ok (resolved, permsD)) :
    ∃ (b o sz : Word) (t : Tag),
      MSB.read s.perms pbind.addr 1 pbind.tag = .ok permsD ∧
      mirlite.Mem.find? s.mem pbind.addr = some (.ptrVal b o sz t) ∧
      resolved = { addr := b + o, tag := t, allocBase := b, allocSize := sz } := by
  simp only [mirlite.resolvePlaceAcc, h_env] at h_res
  rw [if_neg (by
    rintro (h | h)
    · exact absurd h (Nat.lt_irrefl _)
    · exact absurd h (Nat.not_succ_le_self _))] at h_res
  split at h_res
  · exact absurd h_res (by simp)
  · rename_i perms'' h_read
    split at h_res
    · rename_i b o sz t h_find
      simp only [Except.ok.injEq, Prod.mk.injEq] at h_res
      obtain ⟨h_r, h_p⟩ := h_res
      exact ⟨b, o, sz, t, h_p ▸ h_read, h_find, h_r.symm⟩
    · exact absurd h_res (by simp)

/-- A pointer-typed `Load` executes in one `runN` step: the pointer register
    is read, the SB read through the stored tag succeeds, and the loaded
    cells land in the destination register. The permission success is the
    caller's obligation — that is where the PermSim transport lives. -/
theorem runN_Assgn_Load_ptr_step
    (compProg : oseair.Prog) (s : oseair.State MSB)
    (dst preg : Register) (ty : obseq.TyVal)
    {b o sz : Word} {t : Tag} {p2 : AccessPerms}
    (h_instr : compProg s.pc = some (Instr.Assgn dst (Rhs.Load ty preg)))
    (h_entry : PtrRegisterEntry s.reg preg b o sz t)
    (h_lt : o < sz)
    (h_read : MSB.read s.perms (b + o) (obseq.typeSize ty) t = .ok p2) :
    oseair.runN MSB 1 s compProg = oseair.Result.Ok
      { s with perms := p2,
               reg := oseair.RegMap.insert s.reg dst
                 (ty, oseair.readWordSeq s.mem (b + o) (obseq.typeSize ty)),
               pc := s.pc + 1 } := by
  have h_lookup : oseair.RegMap.lookup s.reg preg
      = some (obseq.TyVal.PTy, [Val.Ptr b o sz t]) := h_entry
  have h_bounds : ((b + o < b) || (b + o ≥ b + sz)) = false := by
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
    exact ⟨Nat.not_lt.mpr (Nat.le_add_right b o),
           Nat.not_le.mpr (Nat.add_lt_add_left h_lt b)⟩
  have h_step : oseair.step MSB s compProg = oseair.Result.Ok
      { s with perms := p2,
               reg := oseair.RegMap.insert s.reg dst
                 (ty, oseair.readWordSeq s.mem (b + o) (obseq.typeSize ty)),
               pc := s.pc + 1 } := by
    simp only [oseair.step, oseair.stepWith, h_instr, oseair.evalRhsWith, h_lookup,
      h_bounds, Bool.false_eq_true, if_false, h_read]
  simp [oseair.runN_succ, oseair.runN_zero, h_step]



/-- Fragment locator: an instruction populated in the per-statement code map
    appears verbatim at the same slot in the whole compiled program. -/
theorem compileStmt_emitted_in_compProg
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {compProg : obseq3.oseair.Prog}
    (h_comp : compileProgFrom cs0 prog = Except.ok compProg)
    {stmtIdx : Nat} {stmt : Stmt Γ} {csPrefix : CompilerState}
    {stmtOut : ResultWithEvidence Unit (fun _ => StmtEvidence stmt)}
    (h_prefix : csAt cs0 prog stmtIdx csPrefix)
    (h_get : prog.get? stmtIdx = some stmt)
    (h_stmt : CheckedCompilerM.value (compileStmtChecked stmt) csPrefix = Except.ok stmtOut)
    {q : Nat} {instr : Instr}
    (h_lt : q < (CheckedCompilerM.run (compileStmtChecked stmt) csPrefix).nextLabel)
    (h_code : (CheckedCompilerM.run (compileStmtChecked stmt) csPrefix).code q = some instr) :
    compProg q = some instr := by
  rw [compileProgFrom_code_eq_compileStmt cs0 prog compProg h_comp h_prefix h_get h_stmt h_lt]
  exact h_code

/-- One-step execution of an `RStore`: the source register's cells are
    written through the destination pointer register. The instruction's
    `srcTy != ty` guard is discharged by `LawfulBEq TyVal` — which is why
    `BEq TyVal` is hand-written (see obseq/types.lean): the derived
    instance was opaque and made this lemma unprovable (2026-08-22). -/
theorem runN_RStore_step
    (compProg : oseair.Prog) (s s' : oseair.State MSB)
    (ty : obseq.TyVal) (src ptr : Register) (vals : List Val)
    (x : obseq.TyVal × List Val)
    (h_instr : compProg s.pc = some (Instr.RStore ty src ptr))
    (h_src : oseair.RegMap.lookup s.reg src = some (ty, vals))
    (h_ptr : oseair.RegMap.lookup s.reg ptr = some x)
    (h_wtp : oseair.writeThroughPtr MSB s ptr vals "RStore Invalid Regs"
      = oseair.Result.Ok s') :
    oseair.runN MSB 1 s compProg = oseair.Result.Ok s' := by
  have h_step : oseair.step MSB s compProg = oseair.Result.Ok s' := by
    simp only [oseair.step, oseair.stepWith, h_instr, h_src, h_ptr, bne_self_eq_false,
      Bool.false_eq_true, if_false]
    exact h_wtp
  simp [oseair.runN_succ, oseair.runN_zero, h_step]

/-- One-step execution of a `Borrow` assignment: the base register is read,
    the retag through its tag succeeds, and the destination register
    receives the child pointer (same block and size, offset shifted by the
    projection offset). The retag's success is the caller's obligation —
    that is where the `sb_ref` transport lives. -/
theorem runN_Assgn_Borrow_step
    (compProg : oseair.Prog) (s : oseair.State MSB)
    (dst baseReg : Register) (kind : RefKind) (prot : Bool) (mask : List Bool)
    (len : Nat) (offset : Word)
    {b bo sz : Word} {t newTag : Tag} {p2 : AccessPerms}
    (h_instr : compProg s.pc
      = some (Instr.Assgn dst (Rhs.Borrow kind prot mask len baseReg offset)))
    (h_entry : PtrRegisterEntry s.reg baseReg b bo sz t)
    (h_le : b + bo + offset + len ≤ b + sz)
    (h_ref : MSB.ref s.perms (b + bo + offset) len t kind prot mask
      = .ok (p2, newTag)) :
    oseair.runN MSB 1 s compProg = oseair.Result.Ok
      { s with perms := p2,
               reg := oseair.RegMap.insert s.reg dst
                 (obseq.TyVal.PTy, [Val.Ptr b (bo + offset) sz newTag]),
               pc := s.pc + 1 } := by
  have h_lookup : oseair.RegMap.lookup s.reg baseReg
      = some (obseq.TyVal.PTy, [Val.Ptr b bo sz t]) := h_entry
  have h_step : oseair.step MSB s compProg = oseair.Result.Ok
      { s with perms := p2,
               reg := oseair.RegMap.insert s.reg dst
                 (obseq.TyVal.PTy, [Val.Ptr b (bo + offset) sz newTag]),
               pc := s.pc + 1 } := by
    simp only [oseair.step, oseair.stepWith, h_instr, oseair.evalRhsWith, h_lookup]
    rw [if_neg (Nat.not_lt.mpr h_le)]
    simp only [h_ref]
  simp [oseair.runN_succ, oseair.runN_zero, h_step]

/-- One-step execution of an `Alloc` assignment: the bump allocator hands
    out `mem.addrStart`, `M.own` roots the range at a fresh tag, and the
    destination register receives the pointer to the new block. -/
theorem runN_Assgn_Alloc_step
    (compProg : oseair.Prog) (s : oseair.State MSB)
    (dst : Register) (ty : obseq.TyVal)
    {perms2 : AccessPerms} {tag : Tag}
    (h_instr : compProg s.pc = some (Instr.Assgn dst (Rhs.Alloc ty)))
    (h_own : MSB.own s.perms s.mem.addrStart (obseq.typeSize ty)
      = .ok (perms2, tag)) :
    oseair.runN MSB 1 s compProg = oseair.Result.Ok
      { s with
        mem := (oseair.allocate s.mem (obseq.typeSize ty)).2,
        perms := perms2,
        reg := oseair.RegMap.insert s.reg dst
          (obseq.TyVal.PTy, [Val.Ptr s.mem.addrStart 0 (obseq.typeSize ty) tag]),
        pc := s.pc + 1 } := by
  have h_step : oseair.step MSB s compProg = oseair.Result.Ok
      { s with
        mem := (oseair.allocate s.mem (obseq.typeSize ty)).2,
        perms := perms2,
        reg := oseair.RegMap.insert s.reg dst
          (obseq.TyVal.PTy, [Val.Ptr s.mem.addrStart 0 (obseq.typeSize ty) tag]),
        pc := s.pc + 1 } := by
    simp only [oseair.step, oseair.stepWith, h_instr, oseair.evalRhsWith,
      oseair.bumpAllocator, oseair.allocate, h_own]
  simp [oseair.runN_succ, oseair.runN_zero, h_step]

/-- A `CStore` whose value count matches the declared type size executes in
    exactly one `runN` step via `writeThroughPtr`. -/
theorem runN_CStore_step
    (compProg : oseair.Prog) (s s' : oseair.State MSB)
    (ty : obseq.TyVal) (vals : List Val) (ptr : Register)
    (h_instr : compProg s.pc = some (Instr.CStore ty vals ptr))
    (h_size : vals.length = obseq.typeSize ty)
    (h_wtp : oseair.writeThroughPtr MSB s ptr vals "CStore Invalid Ptr" = oseair.Result.Ok s') :
    oseair.runN MSB 1 s compProg = oseair.Result.Ok s' := by
  have h_step : oseair.step MSB s compProg = oseair.Result.Ok s' := by
    simp only [oseair.step, oseair.stepWith, h_instr]
    split
    · rename_i hc; simp [h_size] at hc
    · exact h_wtp
  simp [oseair.runN_succ, oseair.runN_zero, h_step]

/-- One-step execution of a `Memcpy`: both registers hold pointers, the
    ranges are in bounds, the source range is READ through the source
    tag and the destination range useMut-WRITTEN through the destination
    tag — the same two events mirlite's `.copy` performs — and the read
    word sequence is copied. Registers are untouched. -/
theorem runN_Memcpy_step
    (compProg : oseair.Prog) (s : oseair.State MSB)
    (dst src : Register) (ty : obseq.TyVal)
    {dB dO dS sB sO sS : Word} {dT sT : Tag} {p2 p3 : AccessPerms}
    (h_instr : compProg s.pc = some (Instr.Memcpy dst src ty))
    (h_dentry : PtrRegisterEntry s.reg dst dB dO dS dT)
    (h_sentry : PtrRegisterEntry s.reg src sB sO sS sT)
    (h_dle : dB + dO + obseq.typeSize ty ≤ dB + dS)
    (h_sle : sB + sO + obseq.typeSize ty ≤ sB + sS)
    (h_disj : ¬(dB + dO < sB + sO + obseq.typeSize ty ∧
                sB + sO < dB + dO + obseq.typeSize ty))
    (h_read : MSB.read s.perms (sB + sO) (obseq.typeSize ty) sT = .ok p2)
    (h_useMut : MSB.useMut p2 (dB + dO) (obseq.typeSize ty) dT = .ok p3) :
    oseair.runN MSB 1 s compProg = oseair.Result.Ok
      { s with perms := p3,
               mem := oseair.writeWordSeq s.mem (dB + dO)
                 (oseair.readWordSeq s.mem (sB + sO) (obseq.typeSize ty)),
               pc := s.pc + 1 } := by
  have h_dl : oseair.RegMap.lookup s.reg dst
      = some (obseq.TyVal.PTy, [Val.Ptr dB dO dS dT]) := h_dentry
  have h_sl : oseair.RegMap.lookup s.reg src
      = some (obseq.TyVal.PTy, [Val.Ptr sB sO sS sT]) := h_sentry
  have h_step : oseair.step MSB s compProg = oseair.Result.Ok
      { s with perms := p3,
               mem := oseair.writeWordSeq s.mem (dB + dO)
                 (oseair.readWordSeq s.mem (sB + sO) (obseq.typeSize ty)),
               pc := s.pc + 1 } := by
    simp only [oseair.step, oseair.stepWith, h_instr, h_dl, h_sl]
    rw [if_neg (by
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_lt]
      exact ⟨h_dle, h_sle⟩)]
    rw [if_neg (by
      simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]
      intro h1 h2
      exact h_disj ⟨h1, h2⟩)]
    simp only [h_read, h_useMut]
  simp [oseair.runN_succ, oseair.runN_zero, h_step]

/-- One-step execution of a `Die`: the register's pointer is read and the
    tag killed over `len` cells. Memory and registers are untouched. -/
theorem runN_Die_step
    (compProg : oseair.Prog) (s : oseair.State MSB) (r : Register) (len : Nat)
    {b o sz : Word} {t : Tag} {p2 : AccessPerms}
    (h_instr : compProg s.pc = some (Instr.Die r len))
    (h_entry : PtrRegisterEntry s.reg r b o sz t)
    (h_die : MSB.die s.perms (b + o) len t = .ok p2) :
    oseair.runN MSB 1 s compProg = oseair.Result.Ok
      { s with perms := p2, pc := s.pc + 1 } := by
  have h_lookup : oseair.RegMap.lookup s.reg r
      = some (obseq.TyVal.PTy, [Val.Ptr b o sz t]) := h_entry
  have h_step : oseair.step MSB s compProg = oseair.Result.Ok
      { s with perms := p2, pc := s.pc + 1 } := by
    simp only [oseair.step, oseair.stepWith, h_instr, h_lookup, h_die]
  simp [oseair.runN_succ, oseair.runN_zero, h_step]

/-- A single `Die` step leaves the register file unchanged. -/
theorem step_Die_preserves_reg
    {s s' : oseair.State MSB} {prog : oseair.Prog} {r : Register} {len : Nat}
    (h_instr : prog s.pc = some (Instr.Die r len))
    (h_step : oseair.step MSB s prog = oseair.Result.Ok s') :
    s'.reg = s.reg := by
  simp only [oseair.step, oseair.stepWith, h_instr] at h_step
  repeat (split at h_step <;> try contradiction)
  injection h_step with h_eq
  subst h_eq
  rfl

/-- If a run consisting solely of `Die` instructions completes, it preserves
    memory and the register file and advances the pc by the number of dies.
    Whether it completes (each `sb_die` succeeds) is the caller's obligation
    — that is where the borrow facts live. -/
theorem runN_allDie_preserves
    (compProg : oseair.Prog) :
    ∀ (instrs : List Instr),
      (∀ instr ∈ instrs, ∃ r len, instr = Instr.Die r len) →
      ∀ (s s' : oseair.State MSB),
        (∀ (i : Fin instrs.length), compProg (s.pc + i.1) = some (instrs.get i)) →
        oseair.runN MSB instrs.length s compProg = oseair.Result.Ok s' →
        s'.mem = s.mem ∧ s'.reg = s.reg ∧ s'.pc = s.pc + instrs.length := by
  intro instrs
  induction instrs with
  | nil =>
      intro _ s s' _ h_run
      simp only [List.length_nil, oseair.runN_zero, oseair.Result.Ok.injEq] at h_run
      subst h_run
      exact ⟨rfl, rfl, by simp⟩
  | cons instr rest ih =>
      intro h_die s s' h_instrs h_run
      obtain ⟨r, len, rfl⟩ := h_die instr (List.mem_cons_self)
      have h0 : compProg s.pc = some (Instr.Die r len) := by
        have h := h_instrs ⟨0, by simp⟩
        simpa using h
      cases h_step : oseair.step MSB s compProg with
      | Err msg =>
          simp [List.length_cons, oseair.runN_succ, h_step] at h_run
      | Ok s1 =>
          have h_tail : oseair.runN MSB rest.length s1 compProg = oseair.Result.Ok s' := by
            have h := h_run
            simp only [List.length_cons, oseair.runN_succ, h_step] at h
            exact h
          have h_mp := step_preserves_mem_and_pc h0 (by simp [InstrPreservesMem]) h_step
          have h_reg := step_Die_preserves_reg h0 h_step
          have h_rest_die : ∀ instr ∈ rest, ∃ r len, instr = Instr.Die r len :=
            fun i hi => h_die i (List.mem_cons_of_mem _ hi)
          have h_rest_instrs : ∀ (i : Fin rest.length),
              compProg (s1.pc + i.1) = some (rest.get i) := by
            intro i
            have h := h_instrs ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩
            simp only [List.get_cons_succ] at h
            rw [h_mp.2, show s.pc + 1 + i.1 = s.pc + (i.1 + 1) from by omega]
            exact h
          obtain ⟨hm, hr, hp⟩ := ih h_rest_die s1 s' h_rest_instrs h_tail
          refine ⟨hm.trans h_mp.1, hr.trans h_reg, ?_⟩
          rw [hp, h_mp.2, List.length_cons]
          omega

/-- Running the `cleanupInstrs` from `s`, if it completes, leaves memory and
    the register file unchanged and advances the pc by the cleanup length. -/
theorem runN_cleanupInstrs
    (compProg : oseair.Prog) (s s' : oseair.State MSB) (dies : List (Register × Nat))
    (h_instrs : ∀ (i : Fin (cleanupInstrs dies).length),
        compProg (s.pc + i.1) = some ((cleanupInstrs dies).get i))
    (h_run : oseair.runN MSB (cleanupInstrs dies).length s compProg = oseair.Result.Ok s') :
    s'.mem = s.mem ∧ s'.reg = s.reg ∧ s'.pc = s.pc + (cleanupInstrs dies).length := by
  refine runN_allDie_preserves compProg (cleanupInstrs dies) ?_ s s' h_instrs h_run
  intro instr h_in
  simp only [cleanupInstrs, List.mem_map] at h_in
  obtain ⟨⟨r, len⟩, _, rfl⟩ := h_in
  exact ⟨r, len, rfl⟩

/-! ## §G Memory framing + the SB bridges -/

theorem mirlite_find?_write_self (m : mirlite.Mem) (addr : Word)
    (v : mirlite.MemValue) :
    (m.write addr v).find? addr = some v := by
  simp only [mirlite.Mem.write, mirlite.Mem.find?, List.lookup_cons,
    beq_self_eq_true]

theorem mirlite_find?_write_ne (m : mirlite.Mem) (a addr : Word)
    (v : mirlite.MemValue) (hne : a ≠ addr) :
    (m.write addr v).find? a = m.find? a := by
  have hb : (a == addr) = false := by simp [hne]
  simp only [mirlite.Mem.write, mirlite.Mem.find?, List.lookup_cons, hb]
  exact lookup_filter_ne hne m.mMap

theorem oseair_find?_write_self (m : oseair.Mem) (addr : Word) (v : Val) :
    (m.write addr v).find? addr = some v := by
  simp only [oseair.Mem.write, oseair.Mem.find?, List.lookup_cons, beq_self_eq_true]

theorem oseair_find?_write_ne (m : oseair.Mem) (a addr : Word) (v : Val) (hne : a ≠ addr) :
    (m.write addr v).find? a = m.find? a := by
  have hb : (a == addr) = false := by simp [hne]
  simp only [oseair.Mem.write, oseair.Mem.find?, List.lookup_cons, hb]
  exact lookup_filter_ne hne m.mMap

/-- runN is composable: running m steps then n more equals m+n steps. -/
theorem oseair_runN_add
    (m n : Nat) (s : oseair.State MSB) (prog : oseair.Prog) (s' : oseair.State MSB)
    (h : oseair.runN MSB m s prog = oseair.Result.Ok s') :
    oseair.runN MSB (m + n) s prog = oseair.runN MSB n s' prog := by
  induction m generalizing s with
  | zero =>
      simp [oseair.runN] at h
      simp [oseair.runN, h]
  | succ m ih =>
      simp only [Nat.succ_add, oseair.runN, oseair.runNWith_succ] at *
      split at h
      · exact ih _ h
      · simp at h

/-! ### The three bridge sorries (see the audit in `proof/compiler.lean`)

These are the lemmas whose ABSENCE is where obseq2's three simulation
sorries bottom out. They are stated here against the v3 range-based ops so
the obligation graph is explicit. -/

/- BRIDGE 1 (keystone) — `sb_ref_use_die_cancels` — is CLOSED in
   `obseq3/proof/keystone.lean` (it needs only `obseq3.sb`, no simulation
   vocabulary; kept separate so this file stays the invariant layer). -/

/-- Single-cell `SourceMemSim` extension under identity-ρa: writing
    `MemValSim`-related values at an identity-renamed address preserves
    the forward memory simulation. -/
theorem SourceMemSim.write_extend
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {m : mirlite.Mem} {m' : oseair.Mem} {addr : Word}
    {v : mirlite.MemValue} {v' : Val}
    (h_id : IdentityOnDomain ρa)
    (h_addr : ρa addr = some addr)
    (h_v : MemValSim ρa ρt v v')
    (h_sms : SourceMemSim ρa ρt m m') :
    SourceMemSim ρa ρt (m.write addr v) (m'.write addr v') := by
  intro a value h_find
  by_cases ha : a = addr
  · subst ha
    rw [mirlite_find?_write_self] at h_find
    injection h_find with h_val
    subst h_val
    exact ⟨a, v', h_addr, oseair_find?_write_self _ _ _, h_v⟩
  · rw [mirlite_find?_write_ne _ _ _ _ ha] at h_find
    obtain ⟨a', value', h_ra, h_of, h_mvs⟩ := h_sms a value h_find
    have haa' : a = a' := h_id a a' h_ra
    refine ⟨a', value', h_ra, ?_, h_mvs⟩
    rw [oseair_find?_write_ne m' a' addr v' (by rw [← haa']; exact ha)]
    exact h_of

/-- Range extension: writing `ListRel`-related value sequences at
    identity-renamed addresses preserves `SourceMemSim`. -/
theorem SourceMemSim.writeWordSeq_extend
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    (h_id : IdentityOnDomain ρa) :
    ∀ (values : List mirlite.MemValue) (vals : List Val)
      (m : mirlite.Mem) (m' : oseair.Mem) (addr : Word),
      ListRel (MemValSim ρa ρt) values vals →
      (∀ k, k < values.length → ρa (addr + k) = some (addr + k)) →
      SourceMemSim ρa ρt m m' →
      SourceMemSim ρa ρt (mirlite.writeWordSeq m addr values)
        (oseair.writeWordSeq m' addr vals) := by
  intro values
  induction values with
  | nil =>
      intro vals m m' addr h_rel h_dom h_sms
      cases vals with
      | nil => exact h_sms
      | cons b bs => simp [ListRel] at h_rel
  | cons v values ih =>
      intro vals m m' addr h_rel h_dom h_sms
      cases vals with
      | nil => simp [ListRel] at h_rel
      | cons v' vals =>
          simp only [ListRel] at h_rel
          show SourceMemSim ρa ρt
            (mirlite.writeWordSeq (m.write addr v) (addr + 1) values)
            (oseair.writeWordSeq (m'.write addr v') (addr + 1) vals)
          refine ih vals _ _ _ h_rel.2 ?_
            (SourceMemSim.write_extend h_id
              (h_dom 0 (Nat.succ_pos _)) h_rel.1 h_sms)
          intro k hk
          have h := h_dom (k + 1) (by simpa using Nat.succ_lt_succ hk)
          rw [Nat.add_assoc addr 1 k, Nat.add_comm 1 k]
          exact h

/-- BRIDGE 2, CLOSED: range memory-write simulation. A source
    `writeResolvedPlace` of `values` is matched by a target
    `writeThroughPtr` of `ListRel`-related `vals` through a register
    holding a pointer to the resolved allocation whose tag grants the
    write: the target write succeeds with the CONCRETE result state
    (perms from the given `useMut`, memory the written sequence, pc+1),
    and `SourceMemSim` is re-established cell-by-cell. -/
theorem writeThroughPtr_sim
    {Γ : Ctx} {τ : LayoutTy}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_pre s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {resolved : mirlite.PlaceRes}
    {dstReg : Register} {t' : Tag} {p2 : AccessPerms}
    (msg : String)
    (values : List mirlite.MemValue) (vals : List Val)
    (h_vl : values.length = blockSize τ)
    (h_rel : ListRel (MemValSim ρa ρt) values vals)
    (h_id_a : IdentityOnDomain ρa)
    (h_entry : PtrRegisterEntry s_osea.reg dstReg resolved.allocBase
        (resolved.addr - resolved.allocBase) resolved.allocSize t')
    (h_useMut : MSB.useMut s_osea.perms resolved.addr vals.length t' = .ok p2)
    (h_sms  : SourceMemSim ρa ρt s_pre.mem s_osea.mem)
    (h_le   : resolved.allocBase ≤ resolved.addr)
    (h_dom  : ∀ k, k < values.length → ρa (resolved.addr + k) = some (resolved.addr + k))
    (h_write : mirlite.writeResolvedPlace (τ := τ) MSB s_pre resolved values h_vl
               = mirlite.Result.ok s_mir') :
    oseair.writeThroughPtr MSB s_osea dstReg vals msg
      = oseair.Result.Ok { s_osea with perms := p2, mem := oseair.writeWordSeq s_osea.mem resolved.addr vals, pc := s_osea.pc + 1 } ∧
    SourceMemSim ρa ρt s_mir'.mem (oseair.writeWordSeq s_osea.mem resolved.addr vals) := by
  have h_addr : resolved.allocBase + (resolved.addr - resolved.allocBase)
      = resolved.addr := Nat.add_sub_cancel' h_le
  have h_len : values.length = vals.length := ListRel.length_eq h_rel
  simp only [mirlite.writeResolvedPlace] at h_write
  split at h_write
  · simp at h_write
  · rename_i h_nb
    split at h_write
    · rename_i perms' h_useMut_src
      cases h_write
      constructor
      · have h_lookup : oseair.RegMap.lookup s_osea.reg dstReg =
            some (obseq.TyVal.PTy, [Val.Ptr resolved.allocBase
              (resolved.addr - resolved.allocBase) resolved.allocSize t']) := h_entry
        simp only [oseair.writeThroughPtr, h_lookup, h_addr]
        rw [if_neg (by rw [← h_len]; exact h_nb)]
        simp [h_useMut]
      · exact SourceMemSim.writeWordSeq_extend h_id_a values vals _ _ _
          h_rel h_dom h_sms
    · simp at h_write

/- BRIDGE 3 — `sb_write_respects_PermSim` — is CLOSED for the write in
   `obseq3/proof/permsim_transport.lean` (which holds the whole transport
   lemma family; the read/die/ref members are stated there when their
   consumers close). -/

end obseq3.proof
