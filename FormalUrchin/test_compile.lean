import FormalUrchin.compile
import FormalUrchin.oseairlight
def assert (cond : Bool) (msg : String) : IO Unit :=
  if cond then pure () else panic! s!"Assertion failed: {msg}"

-- Test: Compile CopyOp from MIR to OseairLight
def testCompileCopy_mirProg : mir.Prog :=
  Lean.AssocList.empty.insert 0 [
    mir.Stmt.Assgn (mir.LhsPlace.Place [1]) (mir.RExpr.ConstOp 42),
    mir.Stmt.Assgn (mir.LhsPlace.Place [2]) (mir.RExpr.CopyOp [1]),
    mir.Stmt.Halt
  ]

def testCompileCopy_expected : oseair.Prog :=
  Lean.AssocList.empty.insert 0 [
    oseair.Stmt.assgn (oseair.Register.P 0) (oseair.Rhs.alloc TyVal.NatTy),
    oseair.Stmt.cstore TyVal.NatTy [oseair.Val.Dat 42] (oseair.Register.P 0),
    oseair.Stmt.assgn (oseair.Register.P 1) (oseair.Rhs.alloc TyVal.NatTy),
    oseair.Stmt.memcpy (oseair.Register.P 1) (oseair.Register.P 0) TyVal.NatTy,
    oseair.Stmt.halt
  ]

def testCompileCopy : IO Unit := do
  let ctx : compiler.CompileCtx := { placemap := Lean.AssocList.empty, prog := Lean.AssocList.empty.insert 0 [], regSuffix := 0, currBB := 0, layoutmap := Lean.AssocList.empty }
  let result := compiler.CompileBB testCompileCopy_mirProg 0 ctx
  match result with
  | compiler.CompileResult.Ok cctx =>
      IO.println s!"testCompileCopy: compiled prog = \n{cctx.prog}"
      assert (cctx.prog == testCompileCopy_expected) "Compiled program does not match expected"
  | compiler.CompileResult.Err msg =>
      assert false s!"testCompileCopy failed: {msg}"

#eval testCompileCopy

-- Test: Compile and check memory for _2 = 1 + 41

-- _0  = 1
-- _1  = 41
-- _2  = _0 + _1
def testCompileAdd_mirProg : mir.Prog :=
  Lean.AssocList.empty.insert 0 [
    mir.Stmt.Assgn (mir.LhsPlace.Place [0]) (mir.RExpr.ConstOp 1),
    mir.Stmt.Assgn (mir.LhsPlace.Place [1]) (mir.RExpr.ConstOp 41),
    mir.Stmt.Assgn (mir.LhsPlace.Place [2]) (mir.RExpr.BinaryOp (mir.RExpr.CopyOp [0]) (mir.RExpr.CopyOp [1])),
    mir.Stmt.Halt
  ]

def testCompileAdd_expectedOseair : oseair.Prog :=
  Lean.AssocList.empty.insert 0 [
    oseair.Stmt.assgn (oseair.Register.P 0) (oseair.Rhs.alloc TyVal.NatTy),
    oseair.Stmt.cstore TyVal.NatTy [oseair.Val.Dat 1] (oseair.Register.P 0),
    oseair.Stmt.assgn (oseair.Register.P 1) (oseair.Rhs.alloc TyVal.NatTy),
    oseair.Stmt.cstore TyVal.NatTy [oseair.Val.Dat 41] (oseair.Register.P 1),
    oseair.Stmt.assgn (oseair.Register.P 2) (oseair.Rhs.alloc TyVal.NatTy),
    oseair.Stmt.assgn (oseair.Register.R 0) (oseair.Rhs.load TyVal.NatTy (oseair.Register.P 0)),
    oseair.Stmt.assgn (oseair.Register.R 1) (oseair.Rhs.load TyVal.NatTy (oseair.Register.P 1)),
    oseair.Stmt.assgn (oseair.Register.R 2) (oseair.Rhs.binop (oseair.Register.R 0) (oseair.Register.R 1)),
    oseair.Stmt.cstore TyVal.NatTy [oseair.Val.Dat 42] (oseair.Register.P 2),
    oseair.Stmt.halt
  ]

def testCompileAdd : IO Unit := do
  -- Compile MIR to OseairLight
  let ctx : compiler.CompileCtx := { placemap := Lean.AssocList.empty, prog := Lean.AssocList.empty.insert 0 [], regSuffix := 0, currBB := 0, layoutmap := Lean.AssocList.empty }
  let result := compiler.CompileBB testCompileAdd_mirProg 0 ctx
  match result with
  | compiler.CompileResult.Ok cctx =>
      IO.println s!"testCompileAdd: compiled prog = \n{cctx.prog}"
      -- Run OseairLight interpreter
      let regMap : oseair.RegMap := Lean.AssocList.empty
      let mem : oseair.Mem := { mMap := Lean.AssocList.empty, addrStart := 0 }
      let ap : accessperm.AccessPerms := { StackMap := Lean.AssocList.empty, NextTag := 0 }
      let pc : oseair.ProgCount := { bb := 0, stmt := 0 }
      let evalResult := oseair.EvalProg pc cctx.prog regMap mem ap
      match evalResult with
      | oseair.LhsResult.Ok regMap _ap mem =>
          IO.println s!"OseairLight final regMap: {regMap}"
          IO.println s!"OseairLight final memory: {mem}"
          -- Find the register for _2 from the placemap
          match cctx.placemap.find? 2 with
          | some (_, oseair.Register.P reg2) =>
            match mem.mMap.find? reg2 with
            | some (oseair.Val.Dat 42) => pure ()
            | _ => assert false "OseairLight memory at _2's pointer does not contain 42"
          | _ => assert false "Could not find placemap entry for _2"
      | oseair.LhsResult.Err msg => assert false s!"OseairLight eval failed: {msg}"
  | compiler.CompileResult.Err msg => assert false s!"Compile failed: {msg}"

  -- Run MIR interpreter and check memory
  let env : mir.Env := Lean.AssocList.empty
  let mem : mir.Mem := { mMap := Lean.AssocList.empty, addrStart := 0 }
  let ap : accessperm.AccessPerms := { StackMap := Lean.AssocList.empty, NextTag := 0 }
  let pc : mir.ProgCount := { bb := 0, stmt := 0 }
  let evalResult := mir.EvalProg pc testCompileAdd_mirProg env mem ap
  match evalResult with
  | mir.LhsResult.Ok env _ap mem =>
      IO.println s!"MIR final env: {env}"
      IO.println s!"MIR final memory: {mem}"
      -- Find the address for _2 in the environment and check memory
      match env.find? 2 with
      | some (addr, _ty, _tag) =>
        match mem.mMap.find? addr with
        | some (mir.MemValue.Val 42) => pure ()
        | _ => assert false "MIR memory at _2's address does not contain 42"
      | none => assert false "Could not find environment entry for _2"
  | mir.LhsResult.Err msg => assert false s!"MIR eval failed: {msg}"

#eval testCompileAdd
-- Additional test: Compile MIR program with MutRef and DrefOp

def testProgram2_mirProg : mir.Prog :=
  Lean.AssocList.empty.insert 0 [
    mir.Stmt.Assgn (mir.LhsPlace.Place [0]) (mir.RExpr.ConstOp 42),
    mir.Stmt.Assgn (mir.LhsPlace.Place [1]) (mir.RExpr.RefrOp mir.RefOp.MutRef [0]),
    mir.Stmt.Assgn (mir.LhsPlace.Place [2]) (mir.RExpr.DrefOp [1]),
    mir.Stmt.Halt
  ]

def testProgram2_expectedOseair : oseair.Prog :=
  Lean.AssocList.empty.insert 0
    [ oseair.Stmt.assgn (oseair.Register.P 0) (oseair.Rhs.alloc TyVal.NatTy), -- P0 = alloc NatTy
      oseair.Stmt.cstore TyVal.NatTy [oseair.Val.Dat 42] (oseair.Register.P 0), -- cstore 42, P0
      oseair.Stmt.assgn (oseair.Register.P 1) (oseair.Rhs.alloc TyVal.PTy), -- P1 = alloc PlaceTy
      oseair.Stmt.assgn (oseair.Register.P 2) (oseair.Rhs.mutbor_offset (oseair.Register.P 0) 0), -- P2 = mutbor_offset P0 0
      oseair.Stmt.rstore TyVal.PTy (oseair.Register.P 2) (oseair.Register.P 1), -- rstore P2, P1
      -- now we generate the rderef part
      -- Note that we create a copy of the value at P0 into a new location P3
      -- We can only do this operation for types that implement Copy trait
      oseair.Stmt.assgn (oseair.Register.P 3) (oseair.Rhs.alloc TyVal.NatTy), -- P3 = alloc NatTy
      oseair.Stmt.assgn (oseair.Register.P 4) (oseair.Rhs.load TyVal.PTy (oseair.Register.P 1)), -- P4 = load PlaceTy, P1
      oseair.Stmt.memcpy (oseair.Register.P 3) (oseair.Register.P 4) TyVal.NatTy, -- memcpy P3, P4, NatTy
      oseair.Stmt.halt ]

def testCompileProgram2 : IO Unit := do
  let ctx : compiler.CompileCtx := { placemap := Lean.AssocList.empty, prog := Lean.AssocList.empty.insert 0 [], regSuffix := 0, currBB := 0, layoutmap := Lean.AssocList.empty }
  let result := compiler.CompileBB testProgram2_mirProg 0 ctx
  match result with
  | compiler.CompileResult.Ok cctx =>
      IO.println s!"testCompileProgram2: compiled prog = \n{cctx.prog}"
      assert (cctx.prog == testProgram2_expectedOseair) "Compiled program does not match expected"
  | compiler.CompileResult.Err msg =>
      assert false s!"testCompileProgram2 failed: {msg}"

#eval testCompileProgram2

-- Test: Compile and check memory for mutref assignment
-- _0 = 41
-- _1 = &mut _0
-- *(_1) = 42

def testCompileMutRefAssign_mirProg : mir.Prog :=
  Lean.AssocList.empty.insert 0 [
    mir.Stmt.Assgn (mir.LhsPlace.Place [0]) (mir.RExpr.ConstOp 41),
    mir.Stmt.Assgn (mir.LhsPlace.Place [1]) (mir.RExpr.RefrOp mir.RefOp.MutRef [0]),
    mir.Stmt.Assgn (mir.LhsPlace.RExpr.DrefOp [1]) (mir.RExpr.ConstOp 42),
    mir.Stmt.Halt
  ]

def testCompileMutRefAssign : IO Unit := do
  -- Compile MIR to OseairLight
  let ctx : compiler.CompileCtx := { placemap := Lean.AssocList.empty, prog := Lean.AssocList.empty.insert 0 [], regSuffix := 0, currBB := 0, layoutmap := Lean.AssocList.empty }
  let result := compiler.CompileBB testCompileMutRefAssign_mirProg 0 ctx
  match result with
  | compiler.CompileResult.Ok cctx =>
      IO.println s!"testCompileMutRefAssign: compiled prog = \n{cctx.prog}"
      -- Run OseairLight interpreter
      let regMap : oseair.RegMap := Lean.AssocList.empty
      let mem : oseair.Mem := { mMap := Lean.AssocList.empty, addrStart := 0 }
      let ap : accessperm.AccessPerms := { StackMap := Lean.AssocList.empty, NextTag := 0 }
      let pc : oseair.ProgCount := { bb := 0, stmt := 0 }
      let evalResult := oseair.EvalProg pc cctx.prog regMap mem ap
      match evalResult with
      | oseair.LhsResult.Ok regMap _ap mem =>
          IO.println s!"OseairLight final regMap: {regMap}"
          IO.println s!"OseairLight final memory: {mem}"
          match cctx.placemap.find? 0 with
          | some (_, oseair.Register.P reg0) =>
            match mem.mMap.find? reg0 with
            | some (oseair.Val.Dat 42) => IO.println "OseairLight: PASS"
            | _ => assert false "OseairLight memory at _0's pointer does not contain 42"
          | _ => assert false "Could not find placemap entry for _0"
      | oseair.LhsResult.Err msg => assert false s!"OseairLight eval failed: {msg}"
  | compiler.CompileResult.Err msg => assert false s!"Compile failed: {msg}"

  -- Run MIR interpreter and check memory
  let env : mir.Env := Lean.AssocList.empty
  let mem : mir.Mem := { mMap := Lean.AssocList.empty, addrStart := 0 }
  let ap : accessperm.AccessPerms := { StackMap := Lean.AssocList.empty, NextTag := 0 }
  let pc : mir.ProgCount := { bb := 0, stmt := 0 }
  let evalResult := mir.EvalProg pc testCompileMutRefAssign_mirProg env mem ap
  match evalResult with
  | mir.LhsResult.Ok env _ap mem =>
      IO.println s!"MIR final env: {env}"
      IO.println s!"MIR final memory: {mem}"
      match env.find? 0 with
      | some (addr, _ty, _tag) =>
        match mem.mMap.find? addr with
        | some (mir.MemValue.Val 42) => IO.println "MIR: PASS"
        | _ => assert false "MIR memory at _0's address does not contain 42"
      | none => assert false "Could not find environment entry for _0"
  | mir.LhsResult.Err msg => assert false s!"MIR eval failed: {msg}"

#eval testCompileMutRefAssign

-- Test: Tuple, reference, dereference, and binary operations
-- _0 = {0: 1, 1: 2}
-- _1 = {0: 1, 1: 41}
-- _2 = &_0.0
-- _3 = &_1
-- _4 = *_2
-- _5 = (*_3).1
-- _6 = copy _4 + copy _5
-- Note that we interpret (*_3).1 as deref _3 to get the tuple, then access field 1
-- We DO NOT interpret it as *(_3.1), that support is lacking.
def testCompileTupleRefDerefAdd_mirProg : mir.Prog :=
  Lean.AssocList.empty.insert 0 [
    mir.Stmt.Assgn (mir.LhsPlace.Place [0]) (mir.RExpr.StructInitOp [mir.RExpr.ConstOp 1, mir.RExpr.ConstOp 2]),
    mir.Stmt.Assgn (mir.LhsPlace.Place [1]) (mir.RExpr.StructInitOp [mir.RExpr.ConstOp 1, mir.RExpr.ConstOp 41]),
    mir.Stmt.Assgn (mir.LhsPlace.Place [2]) (mir.RExpr.RefrOp mir.RefOp.BorrowRef [0, 0]),
    mir.Stmt.Assgn (mir.LhsPlace.Place [3]) (mir.RExpr.RefrOp mir.RefOp.BorrowRef [1]),
    mir.Stmt.Assgn (mir.LhsPlace.Place [4]) (mir.RExpr.DrefOp [2]),
    mir.Stmt.Assgn (mir.LhsPlace.Place [5]) (mir.RExpr.DrefOp [3, 1]),
    mir.Stmt.Assgn (mir.LhsPlace.Place [6]) (mir.RExpr.BinaryOp (mir.RExpr.CopyOp [4]) (mir.RExpr.CopyOp [5])),
    mir.Stmt.Halt
  ]

def testCompileTupleRefDerefAdd : IO Unit := do
  -- Compile MIR to OseairLight
  let ctx : compiler.CompileCtx := { placemap := Lean.AssocList.empty, prog := Lean.AssocList.empty.insert 0 [], regSuffix := 0, currBB := 0, layoutmap := Lean.AssocList.empty }
  let result := compiler.CompileBB testCompileTupleRefDerefAdd_mirProg 0 ctx
  match result with
  | compiler.CompileResult.Ok cctx =>
      IO.println s!"testCompileTupleRefDerefAdd: compiled prog = \n{cctx.prog}"
      -- Run OseairLight interpreter
      let regMap : oseair.RegMap := Lean.AssocList.empty
      let mem : oseair.Mem := { mMap := Lean.AssocList.empty, addrStart := 0 }
      let ap : accessperm.AccessPerms := { StackMap := Lean.AssocList.empty, NextTag := 0 }
      let pc : oseair.ProgCount := { bb := 0, stmt := 0 }
      let evalResult := oseair.EvalProg pc cctx.prog regMap mem ap
      match evalResult with
      | oseair.LhsResult.Ok regMap _ap mem =>
          IO.println s!"OseairLight final regMap: {regMap}"
          IO.println s!"OseairLight final memory: {mem}"
          -- Map _6 to pointer reg using placemap, then to address using regMap, then check mem.mMap
          match cctx.placemap.find? 6 with
          | some (_, oseair.Register.P reg6) =>
            match regMap.find? (oseair.Register.P reg6) with
            | some (_ty, [oseair.Val.Ptr base offset _sz _tag]) =>
              match mem.mMap.find? (base + offset) with
              | some (oseair.Val.Dat 42) => IO.println "OseairLight: PASS (_6 == 42)"
              | _ => assert false "OseairLight memory at _6's address does not contain 42"
            | _ => assert false "Could not find address for _6's pointer register in regMap"
          | _ => assert false "Could not find placemap entry for _6"
      | oseair.LhsResult.Err msg => assert false s!"OseairLight eval failed: {msg}"
  | compiler.CompileResult.Err msg => assert false s!"Compile failed: {msg}"

  -- Run MIR interpreter and check memory
  let env : mir.Env := Lean.AssocList.empty
  let mem : mir.Mem := { mMap := Lean.AssocList.empty, addrStart := 0 }
  let ap : accessperm.AccessPerms := { StackMap := Lean.AssocList.empty, NextTag := 0 }
  let pc : mir.ProgCount := { bb := 0, stmt := 0 }
  let evalResult := mir.EvalProg pc testCompileTupleRefDerefAdd_mirProg env mem ap
  match evalResult with
  | mir.LhsResult.Ok env _ap mem =>
      IO.println s!"MIR final env: {env}"
      IO.println s!"MIR final memory: {mem}"
      -- Check memory location for _6 contains 42
      match env.find? 6 with
      | some (addr, _ty, _tag) =>
        match mem.mMap.find? addr with
        | some (mir.MemValue.Val 42) => IO.println "MIR: PASS (_6 == 42)"
        | _ => assert false "MIR memory at _6's address does not contain 42"
      | none => assert false "Could not find environment entry for _6"
  | mir.LhsResult.Err msg => assert false s!"MIR eval failed: {msg}"

#eval testCompileTupleRefDerefAdd
