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
  roots := #[`obseq3.proof.basis, `obseq3.proof.keystone, `obseq3.proof.permsim_transport, `obseq3.proof.permsim_dealloc,
            `obseq3.proof.memsim, `obseq3.proof.spine, `obseq3.proof.assoc, `obseq3.proof.const_write, `obseq3.proof.copy, `obseq3.proof.places, `obseq3.proof.derefdst, `obseq3.proof.copy_chain, `obseq3.proof.freshroot, `obseq3.proof.projdst, `obseq3.proof.ref, `obseq3.proof.chainb, `obseq3.proof.move, `obseq3.proof.leafops, `obseq3.proof.readreg, `obseq3.proof.readsrc, `obseq3.proof.leaffield, `obseq3.proof.binop, `obseq3.proof.slice, `obseq3.proof.alloc, `obseq3.proof.refslice, `obseq3.proof.refslicefield, `obseq3.proof.exposefield, `obseq3.proof.stmts, `obseq3.proof.program, `obseq3.proof.fragment, `obseq3.proof.prmpres, `obseq3.proof.assignif, `obseq3.proof.correct, `obseq3.proof.coverage, `obseq3.proof.layoutagree]
