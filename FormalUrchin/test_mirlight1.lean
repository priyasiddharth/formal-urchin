import FormalUrchin.mirlight
import FormalUrchin.accessperm

def assert (cond : Bool) (msg : String) : IO Unit :=
  if cond then
    pure ()
  else
    panic! s!"Assertion failed: {msg}"

open mir

def testEnv : Env := Lean.AssocList.empty
def testMem : Mem := { mMap := Lean.AssocList.empty, addrStart := 0 }
def testAP : accessperm.AccessPerms := { StackMap := Lean.AssocList.empty, NextTag := 0 }

def testProgram : Prog :=
  Lean.AssocList.empty.insert 0 [Stmt.Assgn [0] (RExpr.CopyOp [1]), Stmt.Halt]

def testEnvWithValues : Env :=
  testEnv.insert 1 (0, TyVal.NatTy, 0)

def testMemWithValues : Mem :=
  {{ testMem with mMap := testMem.mMap.insert 0 (MemValue.Val 42) } with addrStart := 1 }

def expectedEnv : Env :=
  testEnvWithValues.insert 0 (1, TyVal.NatTy, 0)

def expectedMem : Mem :=
  {{ testMem with mMap := testMemWithValues.mMap.insert 1 (MemValue.Val 42) } with addrStart := 2 }

def expectedAP : accessperm.AccessPerms := { testAP with NextTag := 1 }

def testEvalProg :=
  match EvalProg { bb := 0, stmt := 0 } testProgram testEnvWithValues testMemWithValues testAP with
  | LhsResult.Ok env _ap mem => do
    IO.println s!"Environment: {env}"
    IO.println s!"Memory: {mem}"
    --IO.println s!"Access Permissions: {ap}"
    assert (env == expectedEnv) "Env is not as expected"
    assert (mem == expectedMem) "Mem is not as expected"
    --assert (ap == expectedAP) "AccessPerms is not as expected"
  | LhsResult.Err (String.mk _msg) => do
    assert false "Test should not fail"

#eval testEvalProg
