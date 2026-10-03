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

lean_lib Obseq3ByteProof where
  srcDir := "src"
  roots := #[`obseq3.byteproof.memsim, `obseq3.byteproof.spine, `obseq3.byteproof.assoc, `obseq3.byteproof.const_write, `obseq3.byteproof.copy, `obseq3.byteproof.places, `obseq3.byteproof.derefdst, `obseq3.byteproof.copy_chain, `obseq3.byteproof.freshroot, `obseq3.byteproof.projdst, `obseq3.byteproof.ref, `obseq3.byteproof.chainb, `obseq3.byteproof.move, `obseq3.byteproof.leafops, `obseq3.byteproof.readreg, `obseq3.byteproof.readsrc, `obseq3.byteproof.leaffield, `obseq3.byteproof.binop, `obseq3.byteproof.slice, `obseq3.byteproof.alloc, `obseq3.byteproof.refslice, `obseq3.byteproof.refslicefield, `obseq3.byteproof.exposefield, `obseq3.byteproof.stmts, `obseq3.byteproof.program, `obseq3.byteproof.fragment, `obseq3.byteproof.prmpres, `obseq3.byteproof.assignif, `obseq3.byteproof.correct, `obseq3.byteproof.coverage]

lean_lib Obseq3Proof where
  srcDir := "src"
  roots := #[`obseq3.proof.common, `obseq3.proof.keystone, `obseq3.proof.permsim_transport, `obseq3.proof.spine, `obseq3.proof.const_write, `obseq3.proof.copy, `obseq3.proof.ref, `obseq3.proof.casts, `obseq3.proof.ptrarith,
            `obseq3.proof.protectors, `obseq3.proof.alloc, `obseq3.proof.binop, `obseq3.proof.dealloc, `obseq3.proof.slice, `obseq3.proof.assign_if, `obseq3.proof.compiler]
