import Lean
import obseq3.proof.memsim
import obseq3.proof.const_write
import obseq3.proof.copy
import obseq3.proof.places
import obseq3.proof.derefdst
import obseq3.proof.copy_chain
import obseq3.proof.freshroot
import obseq3.proof.projdst
import obseq3.proof.ref
import obseq3.proof.move
import obseq3.proof.leafops
import obseq3.proof.readreg
import obseq3.proof.readsrc
import obseq3.proof.leaffield
import obseq3.proof.binop
import obseq3.proof.slice
import obseq3.proof.alloc
import obseq3.proof.refslice
import obseq3.proof.refslicefield
import obseq3.proof.exposefield
import obseq3.proof.addr
import obseq3.proof.addrof
import obseq3.proof.stmts
import obseq3.proof.program
import obseq3.proof.fragment
import obseq3.proof.assoc
import obseq3.proof.chainb
import obseq3.proof.prmpres
import obseq3.proof.assignif
import obseq3.proof.correct
import obseq3.proof.coverage
import obseq3.proof.layoutagree
import obseq3.proof.die_elision
import obseq3.proof.die_back_check
open Lean Elab Command

-- The byte-level proof (obseq3.proof, branch `byteaddress`) may rest
-- only on the three axioms the main audit whitelists. This fails — and the
-- work must STOP for a decision — if any declaration under
-- `obseq3.proof` reaches another axiom (`sorryAx` included).
#eval show CommandElabM Unit from do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let env ← getEnv
  let decls := env.constants.toList.filterMap fun (n, _) =>
    if (`obseq3.proof).isPrefixOf n && !n.isInternal then some n else none
  let mut bad : Array (Name × Name) := #[]
  let mut used : Array Name := #[]
  for n in decls do
    for a in (← liftCoreM (Lean.collectAxioms n)) do
      if !used.contains a then used := used.push a
      if !allowed.contains a then bad := bad.push (n, a)
  if bad.isEmpty then
    logInfo m!"proof axiom check OK: {decls.length} declarations; axioms used: {used.qsort (·.toString < ·.toString)}"
  else
    throwError m!"proof axiom check FAILED — new axioms: {bad}"
