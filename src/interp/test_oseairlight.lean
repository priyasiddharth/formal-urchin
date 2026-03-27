import interp.oseairlight
import interp.accessperm

open oseair

def assert (cond : Bool) (msg : String) : IO Unit :=
  if cond then pure () else panic! s!"Assertion failed: {msg}"

  def printMachineState (testName : String) (regMap : RegMap) (mem : Mem) : IO Unit := do
    IO.println s!"{testName}"
    IO.println s!"regMap: {regMap}"
    IO.println s!"mem: {mem}"

-- Test 1: Alloc and load

def testRegMap1 : RegMap :=
  Lean.AssocList.empty

def testMem1 : Mem :=
  { mMap := Lean.AssocList.empty, addrStart := 0 }

def testAP1 : accessperm.AccessPerms :=
  { StackMap := Lean.AssocList.empty, NextTag := 0 }

def testProg1 : Prog :=
  Lean.AssocList.empty.insert 0
    [Stmt.assgn (Register.P 0) (Rhs.alloc TyVal.NatTy),
     Stmt.halt]


-- Expected state after executing testProg1 (alloc NatTy)
def expectedRegMap1 : RegMap :=
  Lean.AssocList.empty.insert (Register.P 0) (TyVal.PTy, [Val.Ptr 0 0 (typeSize TyVal.NatTy) 0])

def expectedMem1 : Mem :=
  { mMap := testMem1.mMap, addrStart := 1 }

def testEval1 := do
  -- Allocate a NatTy, should get a pointer in P0
  let result := EvalProg { bb := 0, stmt := 0 } testProg1 testRegMap1 testMem1 testAP1
  match result with
  | LhsResult.Ok regMap _ap mem =>
    do
      printMachineState "Test 1: Alloc" regMap mem
      assert (regMap == expectedRegMap1) "RegMap does not match expected"
      assert (mem == expectedMem1) "Mem does not match expected"
  | LhsResult.Err msg => do
      assert false s!"Test 1 failed: {msg}"

#eval testEval1

-- Test 2: Store and load

def testRegMap2 : RegMap :=
  Lean.AssocList.empty
    |>.insert (Register.P 0) (TyVal.PTy, [Val.Ptr 0 0 (typeSize TyVal.NatTy) 0])
    |>.insert (Register.R 1) (TyVal.NatTy, [Val.Dat 42])

def testMem2 : Mem :=
  { mMap := Lean.AssocList.empty, addrStart := 1 }

def testAP2 : accessperm.AccessPerms :=
  { StackMap := Lean.AssocList.empty, NextTag := 2 }

def testProg2 : Prog :=
  -- Program:
  --   ;assume: P0 points to memory at address 0
  --   ;assume: R1 holds the value 42
  --   store R1, (NatTy), P0
  --   R2 = load (NatTy), P0
  --   halt
  Lean.AssocList.empty.insert 0
    [Stmt.rstore TyVal.NatTy (Register.R 1) (Register.P 0),
     Stmt.assgn (Register.R 2) (Rhs.load TyVal.NatTy (Register.P 0)),
     Stmt.halt]
    -- Expected state after executing testProg2 (store 42 at addr 0, then load into R2)
    def expectedRegMap2 : RegMap :=
      Lean.AssocList.empty
        |>.insert (Register.P 0) (TyVal.PTy, [Val.Ptr 0 0 (typeSize TyVal.NatTy) 0])
        |>.insert (Register.R 1) (TyVal.NatTy, [Val.Dat 42])
        |>.insert (Register.R 2) (TyVal.NatTy, [Val.Dat 42])

    def expectedMem2 : Mem :=
      { mMap := Lean.AssocList.empty
          |>.insert 0 (Val.Dat 42),
        addrStart := 1 }

    def testEval2 := do
      let result := EvalProg { bb := 0, stmt := 0 } testProg2 testRegMap2 testMem2 testAP2
      match result with
      | LhsResult.Ok regMap _ap mem =>
        printMachineState "Test 2: Store and Load" regMap mem
        assert (regMap == expectedRegMap2) "RegMap does not match expected"
        assert (mem == expectedMem2) "Mem does not match expected"
      | LhsResult.Err msg =>
        assert false s!"Test 2 failed: {msg}"

#eval testEval2

-- Test 3: Memcpy

def testRegMap3 : RegMap :=
  Lean.AssocList.empty
    |>.insert (Register.P 0) (TyVal.PTy, [Val.Ptr 0 0 (typeSize TyVal.NatTy) 0])
    |>.insert (Register.P 1) (TyVal.PTy, [Val.Ptr 1 0 (typeSize TyVal.NatTy) 1])

def testMem3 : Mem :=
  { mMap := Lean.AssocList.empty
      |>.insert 0 (Val.Dat 99)
      |>.insert 1 (Val.Dat 0),
    addrStart := 2 }

def testAP3 : accessperm.AccessPerms :=
  { StackMap := Lean.AssocList.empty, NextTag := 3 }

def expectedRegMap3 : RegMap :=
  Lean.AssocList.empty
    |>.insert (Register.P 0) (TyVal.PTy, [Val.Ptr 0 0 (typeSize TyVal.NatTy) 0])
    |>.insert (Register.P 1) (TyVal.PTy, [Val.Ptr 1 0 (typeSize TyVal.NatTy) 1])

def expectedMem3 : Mem :=
  { mMap := Lean.AssocList.empty
      |>.insert 0 (Val.Dat 99)
      |>.insert 1 (Val.Dat 99),
    addrStart := 2 }
-- Program:
--   ;assume: P0 points to memory at address 0 (contains 99)
--   ;assume: P1 points to memory at address 1 (contains 0)
--   memcpy P1, P0, (NatTy)
--   halt
def testProg3 : Prog :=
  Lean.AssocList.empty.insert 0
    [Stmt.memcpy (Register.P 1) (Register.P 0) TyVal.NatTy,
     Stmt.halt]

def testEval3 :=
  -- Memcpy from address 0 to address 1
  let result := EvalProg { bb := 0, stmt := 0 } testProg3 testRegMap3 testMem3 testAP3
  match result with
  | LhsResult.Ok regMap _ap mem => do
    printMachineState "Test 3: Memcpy" regMap mem
    assert (regMap == expectedRegMap3) "RegMap does not match expected"
    assert (mem == expectedMem3) "Mem does not match expected"
  | LhsResult.Err msg =>
    assert false s!"Test 3 failed: {msg}"

#eval testEval3

-- Test: struct initialization and field access with binary addition (OseairLight style)

def testRegMap_add : oseair.RegMap :=
  Lean.AssocList.empty

def testMem_add : oseair.Mem :=
  { mMap := Lean.AssocList.empty, addrStart := 0 }

def testAP_add : accessperm.AccessPerms :=
  { StackMap := Lean.AssocList.empty, NextTag := 0 }

def testProg_add : oseair.Prog :=
  Lean.AssocList.empty.insert 0
    [ oseair.Stmt.assgn (oseair.Register.P 0) (oseair.Rhs.alloc TyVal.NatTy), -- P0 = alloc NatTy
      oseair.Stmt.assgn (oseair.Register.P 1) (oseair.Rhs.alloc TyVal.NatTy), -- P1 = alloc NatTy
      oseair.Stmt.cstore TyVal.NatTy [oseair.Val.Dat 1] (oseair.Register.P 0), -- cstore 1 to P0
      oseair.Stmt.cstore TyVal.NatTy [oseair.Val.Dat 2] (oseair.Register.P 1), -- cstore 2 to P1
      oseair.Stmt.assgn (oseair.Register.R 0) (oseair.Rhs.load TyVal.NatTy (oseair.Register.P 0)), -- R0 = load NatTy from P0
      oseair.Stmt.assgn (oseair.Register.R 1) (oseair.Rhs.load TyVal.NatTy (oseair.Register.P 1)), -- R1 = load NatTy from P1
      oseair.Stmt.assgn (oseair.Register.R 2) (oseair.Rhs.binop (oseair.Register.R 0) (oseair.Register.R 1)), -- R2 = R0 + R1
      oseair.Stmt.halt ]

def expectedRegMap_add : oseair.RegMap :=
  Lean.AssocList.empty
    |>.insert (oseair.Register.P 0) (TyVal.PTy, [oseair.Val.Ptr 0 0 (typeSize TyVal.NatTy) 0])
    |>.insert (oseair.Register.P 1) (TyVal.PTy, [oseair.Val.Ptr 1 0 (typeSize TyVal.NatTy) 1])
    |>.insert (oseair.Register.R 0) (TyVal.NatTy, [oseair.Val.Dat 1])
    |>.insert (oseair.Register.R 1) (TyVal.NatTy, [oseair.Val.Dat 2])
    |>.insert (oseair.Register.R 2) (TyVal.NatTy, [oseair.Val.Dat 3])

def expectedMem_add : oseair.Mem :=
  { mMap := Lean.AssocList.empty
      |>.insert 0 (oseair.Val.Dat 1)
      |>.insert 1 (oseair.Val.Dat 2),
    addrStart := 2 }

def testEval_add : IO Unit := do
  let pc : oseair.ProgCount := { bb := 0, stmt := 0 }
  let result := oseair.EvalProg pc testProg_add testRegMap_add testMem_add testAP_add
  match result with
  | oseair.LhsResult.Ok regMap _ap mem => do
      IO.println s!"Test: testEval_add"
      IO.println s!"RegMap: {regMap}"
      IO.println s!"Memory: {mem}"
      assert (regMap == expectedRegMap_add) "RegMap does not match expected"
      assert (mem == expectedMem_add) "Mem does not match expected"
  | oseair.LhsResult.Err msg =>
      assert false s!"Test failed: {msg}"
#eval testEval_add

-- Test: borrow_offset and load
def testRegMap_borrow : oseair.RegMap :=
  Lean.AssocList.empty

def testMem_borrow : oseair.Mem :=
  { mMap := Lean.AssocList.empty, addrStart := 0 }

def testAP_borrow : accessperm.AccessPerms :=
  { StackMap := Lean.AssocList.empty, NextTag := 0 }

-- P0 = alloc {NatTy, NatTy}
-- R0 = cstore {4, 5}, P0
-- P1 = borrow_offset P0, (typesize NatTy)
-- R1 = load NatTy, P1
-- assert (R1 == 5)
def testProg_borrow : oseair.Prog :=
  Lean.AssocList.empty.insert 0
    [ oseair.Stmt.assgn (oseair.Register.P 0) (oseair.Rhs.alloc (TyVal.TupTy [TyVal.NatTy, TyVal.NatTy])), -- P0 = alloc {NatTy, NatTy}
      oseair.Stmt.cstore (TyVal.TupTy [TyVal.NatTy, TyVal.NatTy]) [oseair.Val.Dat 4, oseair.Val.Dat 5] (oseair.Register.P 0), -- cstore {4, 5} to P0
      oseair.Stmt.assgn (oseair.Register.P 1) (oseair.Rhs.bor_offset (oseair.Register.P 0) (typeSize TyVal.NatTy)), -- P1 = borrow_offset P0, offset = typeSize NatTy
      oseair.Stmt.assgn (oseair.Register.R 1) (oseair.Rhs.load TyVal.NatTy (oseair.Register.P 1)), -- R1 = load NatTy, P1
      oseair.Stmt.halt ]

def expectedRegMap_borrow : oseair.RegMap :=
  Lean.AssocList.empty
    |>.insert (oseair.Register.P 0) (TyVal.PTy, [oseair.Val.Ptr 0 0 (typeSize (TyVal.TupTy [TyVal.NatTy, TyVal.NatTy])) 0])
    |>.insert (oseair.Register.P 1) (TyVal.PTy, [oseair.Val.Ptr 0 (typeSize TyVal.NatTy) (typeSize (TyVal.TupTy [TyVal.NatTy, TyVal.NatTy])) 1])
    |>.insert (oseair.Register.R 1) (TyVal.NatTy, [oseair.Val.Dat 5])

def expectedMem_borrow : oseair.Mem :=
  { mMap := Lean.AssocList.empty
      |>.insert 0 (oseair.Val.Dat 4)
      |>.insert 1 (oseair.Val.Dat 5),
    addrStart := 2 }

def testEval_borrow : IO Unit := do
  let pc : oseair.ProgCount := { bb := 0, stmt := 0 }
  let result := oseair.EvalProg pc testProg_borrow testRegMap_borrow testMem_borrow testAP_borrow
  match result with
  | oseair.LhsResult.Ok regMap _ap mem => do
      IO.println s!"Test: testEval_borrow"
      IO.println s!"RegMap: {regMap}"
      IO.println s!"Memory: {mem}"
      assert (regMap == expectedRegMap_borrow) "RegMap does not match expected"
      assert (mem == expectedMem_borrow) "Mem does not match expected"
      match regMap.find? (oseair.Register.R 1) with
      | some (_ty, [oseair.Val.Dat v]) => assert (v == 5) "R1 does not contain 5"
      | _ => assert false "R1 not found or incorrect value"
  | oseair.LhsResult.Err msg =>
      assert false s!"Test failed: {msg}"
#eval testEval_borrow

-- Test: mutable borrow (mutref) and dereference (deref) like in MIR

def testRegMap_mutref : oseair.RegMap :=
  Lean.AssocList.empty
    |>.insert (oseair.Register.R 0) (TyVal.NatTy, [oseair.Val.Dat 123])

def testMem_mutref : oseair.Mem :=
  { mMap := Lean.AssocList.empty, addrStart := 0 }

def testAP_mutref : accessperm.AccessPerms :=
  { StackMap := Lean.AssocList.empty, NextTag := 0 }

-- Program:
-- P0 = alloc NatTy
-- cstore 42, P0
-- P1 = mutbor_offset P0, 0
-- P2 = alloc PTy
-- rstore P1, P2
-- P3 = load PTy, P2
-- R0 = load NatTy, P3
-- halt
def testProg_mutref : oseair.Prog :=
  Lean.AssocList.empty.insert 0
    [ oseair.Stmt.assgn (oseair.Register.P 0) (oseair.Rhs.alloc TyVal.NatTy), -- P0 = alloc NatTy
      oseair.Stmt.cstore TyVal.NatTy [oseair.Val.Dat 42] (oseair.Register.P 0), -- cstore 42, P0
      oseair.Stmt.assgn (oseair.Register.P 1) (oseair.Rhs.mutbor_offset (oseair.Register.P 0) 0), -- P1 = mutbor_offset P0, 0
      oseair.Stmt.assgn (oseair.Register.P 2) (oseair.Rhs.alloc TyVal.PTy), -- P2 = alloc PTy
      oseair.Stmt.rstore TyVal.PTy (oseair.Register.P 1) (oseair.Register.P 2), -- rstore P1, P2
      oseair.Stmt.assgn (oseair.Register.P 3) (oseair.Rhs.load TyVal.PTy (oseair.Register.P 2)), -- P3 = load PTy, P2
      oseair.Stmt.assgn (oseair.Register.R 0) (oseair.Rhs.load TyVal.NatTy (oseair.Register.P 3)), -- R0 = load NatTy, P3
      oseair.Stmt.halt ]

def expectedRegMap_mutref : oseair.RegMap :=
  Lean.AssocList.empty
    |>.insert (oseair.Register.P 0) (TyVal.PTy, [oseair.Val.Ptr 0 0 (typeSize TyVal.NatTy) 0])
    |>.insert (oseair.Register.P 1) (TyVal.PTy, [oseair.Val.Ptr 0 0 (typeSize TyVal.NatTy) 1])
    |>.insert (oseair.Register.P 2) (TyVal.PTy, [oseair.Val.Ptr 1 0 (typeSize TyVal.PTy) 2])
    |>.insert (oseair.Register.P 3) (TyVal.PTy, [oseair.Val.Ptr 0 0 (typeSize TyVal.NatTy) 1])
    |>.insert (oseair.Register.R 0) (TyVal.NatTy, [oseair.Val.Dat 42])

def expectedMem_mutref : oseair.Mem :=
  { mMap := Lean.AssocList.empty
      |>.insert 0 (oseair.Val.Dat 42)
      |>.insert 1 (oseair.Val.Ptr 0 0 (typeSize TyVal.NatTy) 1),
    addrStart := 2 }

def testEval_mutref : IO Unit := do
  let pc : oseair.ProgCount := { bb := 0, stmt := 0 }
  let result := oseair.EvalProg pc testProg_mutref testRegMap_mutref testMem_mutref testAP_mutref
  match result with
  | oseair.LhsResult.Ok regMap _ap mem => do
      IO.println s!"Test: testEval_mutref"
      IO.println s!"RegMap: {regMap}"
      IO.println s!"Memory: {mem}"
      assert (regMap == expectedRegMap_mutref) "RegMap does not match expected"
      assert (mem == expectedMem_mutref) "Mem does not match expected"
  | oseair.LhsResult.Err msg =>
      assert false s!"Test failed: {msg}"

#eval testEval_mutref
