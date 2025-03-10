import FormalUrchin.compile

def testProgram : mir.Prog :=
  Lean.AssocList.empty.insert 0 [mir.Stmt.Assgn [2] (mir.RExpr.CopyOp [1]), mir.Stmt.Halt]


  def test_placemap := Lean.AssocList.empty.insert 1 (TyVal.NatTy, oseair.Register.P 0)

  def test_CompileBB : IO Unit :=
    let ctx : compiler.CompileCtx := { placemap := test_placemap, prog := Lean.AssocList.empty.insert 0 [], regSuffix := 1, currBB := 0 }
    let result := compiler.CompileBB testProgram 0 ctx
    match result with
    | compiler.CompileResult.Ok cctx => IO.println cctx.prog
    | compiler.CompileResult.Err msg => IO.println msg

    def main : IO Unit :=
      test_CompileBB

    #eval main
