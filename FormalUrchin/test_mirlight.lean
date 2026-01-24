import FormalUrchin.mirlight
import FormalUrchin.accessperm

def assert (cond : Bool) (msg : String) : IO Unit :=
  if cond then pure () else panic! s!"Assertion failed: {msg}"

open mir

def printTestResult (name : String) (env : Env) (mem : Mem) : IO Unit := do
  IO.println s!"{name}"
  IO.println s!"Environment: {env}"
  IO.println s!"Memory: {mem}"

-- Test copy operation

def testEnv1 : Env := Lean.AssocList.empty

def testMem1 : Mem := { mMap := Lean.AssocList.empty, addrStart := 0 }

def testAP1 : accessperm.AccessPerms := { StackMap := Lean.AssocList.empty, NextTag := 0 }

def testProgram1 : Prog :=
  Lean.AssocList.empty.insert 0 [Stmt.Assgn (LhsPlace.Place [0]) (RExpr.CopyOp [1]), Stmt.Halt]

def testEnvWithValues1 : Env :=
  testEnv1.insert 1 (0, TyVal.NatTy, 0)

def testMemWithValues1 : Mem :=
  {{ testMem1 with mMap := testMem1.mMap.insert 0 (MemValue.Val 42) } with addrStart := 1 }

def expectedEnv1 : Env :=
  testEnvWithValues1.insert 0 (1, TyVal.NatTy, 0)

def expectedMem1 : Mem :=
  {{ testMem1 with mMap := testMemWithValues1.mMap.insert 1 (MemValue.Val 42) } with addrStart := 2 }

def testEvalProg1 :=
  match EvalProg { bb := 0, stmt := 0 } testProgram1 testEnvWithValues1 testMemWithValues1 testAP1 with
  | LhsResult.Ok env _ap mem => do
    printTestResult "Test 1: CopyOp" env mem
    assert (env == expectedEnv1) "Env is not as expected"
    assert (mem == expectedMem1) "Mem is not as expected"
  | LhsResult.Err (String.mk msg) => do
    assert false s!"Test 1 should not fail: {msg}"

#eval testEvalProg1

-- Test from ref/dref op

def testEnv2 : Env := Lean.AssocList.empty

def testMem2 : Mem := { mMap := Lean.AssocList.empty, addrStart := 0 }

def testAP2 : accessperm.AccessPerms := { StackMap := Lean.AssocList.empty, NextTag := 1 }

def testProgram2 : Prog :=
  Lean.AssocList.empty.insert 0
  [Stmt.Assgn (LhsPlace.Place [1]) (RExpr.RefrOp RefOp.MutRef [0]),
    Stmt.Assgn (LhsPlace.Place [2]) (RExpr.DrefOp [1]),
    Stmt.Halt]

def testEnvWithValues2 : Env :=
  testEnv2.insert 0 (0, TyVal.NatTy, 0)

def testMemWithValues2 : Mem :=
  {{ testMem2 with mMap := testMem2.mMap.insert 0 (MemValue.Val 42) } with addrStart := 1 }

def expectedEnv2 : Env :=
  (testEnvWithValues2.insert 1 (1, TyVal.PTy, 2)).insert 2 (2, TyVal.NatTy, 3)

def expectedMem2 : Mem :=
  {{ testMem2 with mMap :=
  (testMemWithValues2.mMap.insert 1 (MemValue.PlaceTag [0] 1)).insert 2 (MemValue.Val 42) } with addrStart := 3 }

def testEvalProg2 :=
  match EvalProg { bb := 0, stmt := 0  } testProgram2 testEnvWithValues2 testMemWithValues2 testAP2 with
  | LhsResult.Ok env _ap mem => do
    printTestResult "Test 2: Ref and Dref" env mem
    assert (env == expectedEnv2) "Env is not as expected"
    assert (mem == expectedMem2) "Mem is not as expected"
  | LhsResult.Err (String.mk msg) => do
    assert false s!"Test 2 should not fail: {msg}"

#eval testEvalProg2

-- Test binary addition

def testEnv3 : Env :=
  (Lean.AssocList.empty : Lean.AssocList Nat (Word × TyVal × mir.Tag))
    |>.insert 0 (0, TyVal.NatTy, 0)
    |>.insert 1 (1, TyVal.NatTy, 1)

def testMem3 : Mem :=
  { mMap := ((Lean.AssocList.empty : Lean.AssocList Word MemValue)
            |>.insert 0 (MemValue.Val 42)
            |>.insert 1 (MemValue.Val 1)),
    addrStart := 2 }

def testAP3 : accessperm.AccessPerms :=
  { StackMap := Lean.AssocList.empty, NextTag := 2 }

def testProgram3 : Prog :=
  Lean.AssocList.empty.insert 0
    [Stmt.Assgn (LhsPlace.Place [2]) (RExpr.BinaryOp (RExpr.CopyOp [0]) (RExpr.CopyOp [1])),
     Stmt.Halt]

def expectedEnv3 : Env :=
  testEnv3
    |>.insert 2 (2, TyVal.NatTy, 2)

def expectedMem3 : Mem :=
  { mMap := testMem3.mMap
      |>.insert 2 (MemValue.Val 43),
    addrStart := 4 }

def testEvalProg3 :=
  match EvalProg { bb := 0, stmt := 0 } testProgram3 testEnv3 testMem3 testAP3 with
  | LhsResult.Ok env _ap mem => do
    printTestResult "Test 3: Binary addition to new place" env mem
    assert (env == expectedEnv3) "Env is not as expected"
    assert (mem.mMap.find? 2 == some (MemValue.Val 43)) "Memory at _2 is not 43"
  | LhsResult.Err (String.mk msg) => do
    assert false s!"Test 3 should not fail: {msg}"

#eval testEvalProg3

-- Test Struct initialization

def testEnv4 : Env :=
  (Lean.AssocList.empty : Lean.AssocList Nat (Word × TyVal × mir.Tag))
    |>.insert 0 (0, TyVal.NatTy, 0)
    |>.insert 1 (1, TyVal.NatTy, 1)

def testMem4 : Mem :=
  { mMap := ((Lean.AssocList.empty : Lean.AssocList Word MemValue)
            |>.insert 0 (MemValue.Val 42)
            |>.insert 1 (MemValue.Val 43)),
    addrStart := 2 }

def testAP4 : accessperm.AccessPerms :=
  { StackMap := Lean.AssocList.empty, NextTag := 2 }

def testProgram4 : Prog :=
  Lean.AssocList.empty.insert 0
    [Stmt.Assgn (LhsPlace.Place [2]) (RExpr.StructInitOp [RExpr.CopyOp [0], RExpr.CopyOp [1]]),
     Stmt.Halt]

def expectedEnv4 : Env :=
  testEnv4
    |>.insert 2 (2, TyVal.TupTy [TyVal.NatTy, TyVal.NatTy], 2)

def expectedMem4 : Mem :=
  { mMap := testMem4.mMap
      |>.insert 2 (MemValue.Val 42)
      |>.insert 3 (MemValue.Val 43),
    addrStart := 4 }

def testEvalProg4 :=
  match EvalProg { bb := 0, stmt := 0 } testProgram4 testEnv4 testMem4 testAP4 with
  | LhsResult.Ok env _ap mem => do
    printTestResult "Test 4: Struct initialization" env mem
    assert (env == expectedEnv4) "Env is not as expected"
    assert (mem.mMap.find? 2 == some (MemValue.Val 42)) "Memory at struct field 0 is not 42"
    assert (mem.mMap.find? 3 == some (MemValue.Val 43)) "Memory at struct field 1 is not 43"
  | LhsResult.Err (String.mk msg) => do
    assert false s!"Test 4 should not fail: {msg}"

#eval testEvalProg4

-- Test indirect store

def testEnv5 : Env :=
  Lean.AssocList.empty

def testMem5 : Mem :=
  { mMap := Lean.AssocList.empty, addrStart := 0 }

def testAP5 : accessperm.AccessPerms :=
  { StackMap := Lean.AssocList.empty, NextTag := 1 }

def testProgram5 : Prog :=
  Lean.AssocList.empty.insert 0
    [Stmt.Assgn (LhsPlace.Place [0]) (RExpr.ConstOp 41),                  -- _0 = 41
     Stmt.Assgn (LhsPlace.Place [1]) (RExpr.ConstOp 42),                  -- _1 = 42
     Stmt.Assgn (LhsPlace.Place [2]) (RExpr.RefrOp RefOp.MutRef [0]),     -- _2 = Ref _0
     Stmt.Assgn (LhsPlace.RExpr.DrefOp [2]) (RExpr.CopyOp [1]),           -- *(_2) = copy _1
     Stmt.Halt]

def expectedMem5 : Mem :=
  { mMap := Lean.AssocList.empty
      |>.insert 0 (MemValue.Val 42)   -- _0 should now be 42
      |>.insert 1 (MemValue.PlaceTag [0] 1)
      |>.insert 2 (MemValue.Val 42),
    addrStart := 3 }

def testEvalProg5 :=
  match EvalProg { bb := 0, stmt := 0 } testProgram5 testEnv5 testMem5 testAP5 with
  | LhsResult.Ok env _ap mem => do
    printTestResult "Test 5: Reference and dereference" env mem
    assert (mem.mMap.find? 0 == some (MemValue.Val 42)) "Memory at _0 is not 42"
  | LhsResult.Err (String.mk msg) => do
    assert false s!"Test 5 should not fail: {msg}"

#eval testEvalProg5
-- Test struct initialization and field access with binary addition

def testEnv6 : Env :=
  Lean.AssocList.empty

def testMem6 : Mem :=
  { mMap := Lean.AssocList.empty, addrStart := 0 }

def testAP6 : accessperm.AccessPerms :=
  { StackMap := Lean.AssocList.empty, NextTag := 0 }

def testProgram6 : Prog :=
  Lean.AssocList.empty.insert 0
    [Stmt.Assgn (LhsPlace.Place [0]) (RExpr.ConstOp 1),                                   -- _0 = 1
     Stmt.Assgn (LhsPlace.Place [1]) (RExpr.ConstOp 2),                                   -- _1 = 2
     Stmt.Assgn (LhsPlace.Place [3]) (RExpr.StructInitOp [RExpr.MoveOp [0], RExpr.MoveOp [1]]), -- _3 = struct {move _0, move _1}
     Stmt.Assgn (LhsPlace.Place [4]) (RExpr.BinaryOp (RExpr.CopyOp [3, 0]) (RExpr.CopyOp [3, 1])), -- _4 = copy _3.0 + copy _3.1
     Stmt.Halt]

def expectedEnv6 : Env :=
  Lean.AssocList.empty
    |>.insert 0 (0, TyVal.NatTy, 0)
    |>.insert 1 (1, TyVal.NatTy, 1)
    |>.insert 3 (2, TyVal.TupTy [TyVal.NatTy, TyVal.NatTy], 2)
    |>.insert 4 (4, TyVal.NatTy, 3)

def expectedMem6 : Mem :=
  { mMap := Lean.AssocList.empty
      |>.insert 0 (MemValue.Val 1)
      |>.insert 1 (MemValue.Val 2)
      |>.insert 2 (MemValue.Val 1)
      |>.insert 3 (MemValue.Val 2)
      |>.insert 4 (MemValue.Val 3),
    addrStart := 5 }

def testEvalProg6 :=
  match EvalProg { bb := 0, stmt := 0 } testProgram6 testEnv6 testMem6 testAP6 with
  | LhsResult.Ok env _ap mem => do
    printTestResult "Test 6: StructInitOp and field addition" env mem
    assert (mem.mMap.find? 4 == some (MemValue.Val 3)) "Memory at _4 is not 3"
    assert (env == expectedEnv6) "Env is not as expected"
    assert (mem == expectedMem6) "Mem is not as expected"
  | LhsResult.Err (String.mk msg) => do
    assert false s!"Test 6 should not fail: {msg}"

#eval testEvalProg6

-- Test deref where the value is a struct

def testEnv7 : Env := Lean.AssocList.empty

def testMem7 : Mem := { mMap := Lean.AssocList.empty, addrStart := 0 }

def testAP7 : accessperm.AccessPerms := { StackMap := Lean.AssocList.empty, NextTag := 1 }

def testProgram7 : Prog :=
  Lean.AssocList.empty.insert 0
    [Stmt.Assgn (LhsPlace.Place [0]) (RExpr.StructInitOp [RExpr.ConstOp 10, RExpr.ConstOp 20]), -- _0 = struct {10, 20}
     Stmt.Assgn (LhsPlace.Place [1]) (RExpr.RefrOp RefOp.MutRef [0]),                           -- _1 = Ref _0
     Stmt.Assgn (LhsPlace.Place [2]) (RExpr.DrefOp [1]),                                        -- _2 = *(_1)
     Stmt.Halt]

def testEnvWithValues7 : Env :=
  Lean.AssocList.empty
    |>.insert 0 (0, TyVal.TupTy [TyVal.NatTy, TyVal.NatTy], 0)

def testMemWithValues7 : Mem :=
  { mMap := Lean.AssocList.empty
      |>.insert 0 (MemValue.Val 10)
      |>.insert 1 (MemValue.Val 20),
    addrStart := 2 }

def expectedEnv7 : Env :=
  testEnvWithValues7
    |>.insert 1 (2, TyVal.PTy, 2 /- tag is two since _0 is tag 0 and Ref _0 is tag 1 -/)
    |>.insert 2 (3, TyVal.TupTy [TyVal.NatTy, TyVal.NatTy], 3)

def expectedMem7 : Mem :=
  { mMap := testMemWithValues7.mMap
      |>.insert 2 (MemValue.PlaceTag [0] 1)
      |>.insert 3 (MemValue.Val 10)
      |>.insert 4 (MemValue.Val 20),
    addrStart := 5 }

def testEvalProg7 :=
  match EvalProg { bb := 0, stmt := 0 } testProgram7 testEnvWithValues7 testMemWithValues7 testAP7 with
  | LhsResult.Ok env _ap mem => do
    printTestResult "Test 7: Ref and Dref of struct" env mem
    assert (env == expectedEnv7) "Env is not as expected"
    assert (mem == expectedMem7) "Mem is not as expected"
    assert (mem.mMap.find? 3 == some (MemValue.Val 10)) "Struct field 0 is not 10"
    assert (mem.mMap.find? 4 == some (MemValue.Val 20)) "Struct field 1 is not 20"
  | LhsResult.Err (String.mk msg) => do
    assert false s!"Test 7 should not fail: {msg}"

#eval testEvalProg7
