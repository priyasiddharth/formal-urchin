import Lake
open Lake DSL

package formal_urchin

@[default_target]
lean_lib Core where
  srcDir := "src"
  roots := #[`obseq, `obseq2, `interp]

lean_lib Obseq where
  srcDir := "src"
  roots := #[`obseq]

lean_lib Obseq2 where
  srcDir := "src"
  roots := #[`obseq2]

lean_lib Obseq2Proof where
  srcDir := "src"
  roots := #[`obseq2.proof.common, `obseq2.proof.compiler, `obseq2.proof.copy, `obseq2.proof.ref, `obseq2.proof.const_write]

lean_lib Obseq3 where
  srcDir := "src"
  roots := #[`obseq3]

lean_lib Conformance where
  srcDir := "src"
  roots := #[`conformance]

lean_lib Interp where
  srcDir := "src"
  roots := #[`interp]

lean_lib InterpTests where
  srcDir := "src"
  roots := #[`InterpTests]

lean_exe formal_urchin where
  srcDir := "src"
  root := `Main

lean_exe sb_conformance where
  srcDir := "src"
  root := `conformance.main

lean_exe interp_tests where
  srcDir := "src"
  root := `InterpTests

lean_lib Obseq3Proof where
  srcDir := "src"
  roots := #[`obseq3.proof.common, `obseq3.proof.const_write, `obseq3.proof.copy, `obseq3.proof.ref, `obseq3.proof.compiler]
