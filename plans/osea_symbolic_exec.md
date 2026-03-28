# OSEA-IR Symbolic Execution Plan

## Goal

Create a tactic that automatically proves goals of the form:
```lean
oseair.runN n s_osea prog_osea = oseair.Result.Ok final_state
```

given hypotheses about the initial state and program.

## Architecture

### Layer 1: Per-Instruction Step Lemmas

Create lemmas for each instruction that compute `step s prog = Result.Ok s'`:

```lean
-- Assgn with MutBorOffset
theorem step_Assgn_MutBorOffset
  (s : State) (prog : Prog) (tmpReg baseReg : Register) (off : Word)
  (h_pc : prog.get? s.pc = some (Instr.Assgn tmpReg (Rhs.MutBorOffset baseReg off)))
  (h_base_reg : s.reg.lookup baseReg = some (TyVal.PTy, [Val.Ptr addr baseOff size tag]))
  (h_off : baseOff + off < size)
  (h_ref : sb_ref s.ap (addr + baseOff + off) tag RefOpKind.Mut = (SBResult.Ok ap', newTag)) :
  step s prog = Result.Ok { s with 
    reg := s.reg.insert tmpReg (TyVal.PTy, [Val.Ptr addr (baseOff + off) size newTag]),
    ap := ap',
    pc := s.pc + 1 }

-- CStore
theorem step_CStore
  (s : State) (prog : Prog) (layout : LayoutTy) (vals : List Val) (ptrReg : Register)
  (h_pc : prog.get? s.pc = some (Instr.CStore (layoutToTyVal layout) vals ptrReg))
  (h_ptr_reg : s.reg.lookup ptrReg = some (TyVal.PTy, [Val.Ptr base off size tag]))
  (h_off : off < size)
  (h_use : sb_use_mb s.ap (base + off) tag = SBResult.Ok ap') :
  step s prog = Result.Ok { s with 
    ap := ap',
    mem := writeWordSeq s.mem (base + off) vals,
    pc := s.pc + 1 }

-- Die
theorem step_Die
  (s : State) (prog : Prog) (reg : Register)
  (h_pc : prog.get? s.pc = some (Instr.Die reg))
  (h_ptr_reg : s.reg.lookup reg = some (TyVal.PTy, [Val.Ptr base off size tag]))
  (h_die : sb_die s.ap (base + off) tag = SBResult.Ok ap') :
  step s prog = Result.Ok { s with 
    ap := ap',
    pc := s.pc + 1 }
```

### Layer 2: runN Chaining Lemma

```lean
theorem runN_step_succ
  (n : Nat) (s0 s1 : State) (prog : Prog)
  (h_step : step s0 prog = Result.Ok s1)
  (h_rest : runN n s1 prog = Result.Ok s_final) :
  runN (n + 1) s0 prog = Result.Ok s_final
```

### Layer 3: Symbolic Execution Tactic

The tactic `osea_symbolic_exec` would:

1. Parse the goal to extract `n`, `s0`, `prog`, and `s_final`
2. For each step from 0 to n-1:
   - Look up the instruction at `s_i.pc` in `prog`
   - Match the instruction type
   - Apply the appropriate step lemma
   - Generate subgoals for hypotheses that can't be discharged automatically
3. Chain the steps together using `runN_step_succ`

### Implementation Strategy

**Phase 1: Manual Step Lemmas**
- Create the step lemmas manually
- Use them to simplify existing proofs like `osea_run_projected_cstore_embedded_ok`

**Phase 2: Tactic Foundation**
- Create `runN_step_succ` lemma
- Create a `simp_step` tactic that tries all step lemmas

**Phase 3: Full Tactic**
- Create `osea_symbolic_exec` tactic using Lean 4 metaprogramming
- The tactic inspects the goal, applies step lemmas iteratively

## Example Usage

Before (current):
```lean
theorem osea_run_projected_cstore_embedded_ok ... := by
  have h_stmt0 : prog_osea.get? s_osea.pc = some (Instr.Assgn tmpReg (Rhs.MutBorOffset baseReg off)) := ...
  rcases List.get?_eq_some_iff.mp h_stmt0 with ⟨h_pc0, h_get0⟩
  let s1 : oseair.State := { ... }
  have h_step0 : oseair.step s_osea prog_osea = oseair.Result.Ok s1 := by
    unfold oseair.step oseair.evalRhs
    rw [dif_pos h_pc0, h_get0]
    ... -- many lines
  have h_start1 : StartsAt prog_osea (s_osea.pc + 1) [...] := ...
  -- repeat for step 1 and step 2
  simp [oseair.runN, h_step0, h_step1, h_step2]
```

After (with tactic):
```lean
theorem osea_run_projected_cstore_embedded_ok ... := by
  osea_symbolic_exec
  -- subgoals: h_base_reg, h_off, h_ref, h_use, h_die
  all_goals assumption
```

## Challenges

1. **StartsAt handling**: The tactic needs to track `StartsAt` facts to know what instructions are at each PC
2. **State threading**: Each step produces a new state that must be threaded to the next step
3. **Hypothesis generation**: The tactic needs to identify which hypotheses are needed and generate appropriate subgoals
4. **Error handling**: If a step fails, provide a useful error message

## Next Steps

1. Implement `step_Assgn_MutBorOffset`, `step_CStore`, `step_Die` lemmas
2. Implement `runN_step_succ` lemma
3. Test on `osea_run_projected_cstore_embedded_ok`
4. Implement the full tactic
