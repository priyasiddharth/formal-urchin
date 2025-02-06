import FormalUrchin.mirlight

open mir

  def testProgram : List Stmt :=
    [Stmt.Assgn [1] (RExpr.CopyOp [0])]

  def testEnvWithValues : Env :=
    Lean.AssocList.cons 0 (0, TyVal.NatTy 42, 0) Lean.AssocList.nil

  def testMemWithValues : Mem :=
    { mMap := Lean.AssocList.cons 0 (MemValue.Val 42) Lean.AssocList.nil
    , addrStart := 1 }

  def testAP : AccessPerms :=
    { StackedMap := Lean.AssocList.nil, NextTag := 1 }

  def expectedEnv : Env :=
    Lean.AssocList.cons 1 (1, TyVal.NatTy 42, 1) (Lean.AssocList.cons 0 (0, TyVal.NatTy 42, 0) Lean.AssocList.nil)

  def expectedMem : Mem :=
    { mMap := Lean.AssocList.cons 1 (MemValue.Val 42) (Lean.AssocList.cons 0 (MemValue.Val 42) Lean.AssocList.nil)
    , addrStart := 2 }

  def expectedAP : AccessPerms :=
    { StackedMap := Lean.AssocList.nil, NextTag := 2 }



theorem test_eval : Eval (0, testProgram, testEnvWithValues, testMemWithValues, testAP) (1, testProgram, expectedEnv, expectedMem, expectedAP) :=
  by
    apply Eval.AssgnRel
    have h_inbounds_idx : 0 < testProgram.length := by
      exact Nat.zero_lt_succ 0
    have h_stmt : testProgram.get ⟨0, h_inbounds_idx⟩ = Stmt.Assgn [1] (RExpr.CopyOp [0]) :=
    by simp [testProgram]
    exact h_stmt
    have h_r2val : RExprToValFn (RExpr.CopyOp [0]) testEnvWithValues testMemWithValues testAP =
      RhsResult.Ok [MemValue.Val 42] (TyVal.NatTy 42) testAP testMemWithValues  := by
      rw [RExprToValFn]
      simp [testEnvWithValues]
      rw [getPlaceAddr]

      have h_getPlaceAddr : getPlaceAddr [0] testEnvWithValues = some 0 := by
        simp [getPlaceAddr, testEnvWithValues]

/-
 theorem test_eval :
  EvalStmtRel
    (0, testProgram, testEnvWithValues, testMemWithValues, testAP)
    (1, testProgram, expectedEnv, expectedMem, expectedAP) :=
  by
 -/
  /- have h_inbounds_idx : 0 < testProgram.length := by
    exact Nat.zero_lt_succ 0
  have h_stmt : testProgram.get ⟨0, h_inbounds_idx⟩ = Stmt.Assgn [1] (RExpr.CopyOp [0]) := by
    simp [testProgram]


  -- proof steps
  have h_env : testEnvWithValues.find? 0 = some (0, TyVal.NatTy 42, 0) := by
    simp [testEnvWithValues]
  have h_mem : testMemWithValues.mMap.find? 0 = some (MemValue.Val 42) := by
    simp [testMemWithValues]
  have h_ap : testAP.NextTag = 1 := by
    simp [testAP]
  have h_r2v : RExprToValFn [0] testEnvWithValues testMemWithValues testAP = Val.mk (TyVal.NatTy 42) 0 := by
    simp [RExprToValFn, getPlaceAddr, getPlaceType, ReadWordSeq, testEnvWithValues, testMemWithValues, testAP] -/

  /- theorem test_eval_star :
    EvalStar
      (0, testProgram, testEnvWithValues, testMemWithValues, testAP)
      (1, testProgram, expectedEnv, expectedMem, expectedAP) := by
    apply EvalStar.step
    apply EvalStmtRel.AssgnRel
    exact Nat.zero_lt_succ 1
    -- Prove that the first statement in the test program is the assignment.
    simp [testProgram]
    -- Prove that the evaluation of the RHS expression produces the expected result.
    simp [RExprToValFn, getPlaceAddr, getPlaceType, ReadWordSeq]
    simp [testEnvWithValues, testMemWithValues, testAP, freshTag]
    rfl -- Prove the equality of LHS result
    -- Finally, finish the proof with the reflexive base case.
    apply EvalStar.refl -/
