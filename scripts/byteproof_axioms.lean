import obseq3.byteproof.memsim
import obseq3.byteproof.const_write
import obseq3.byteproof.copy
import obseq3.byteproof.places
import obseq3.byteproof.derefdst
import obseq3.byteproof.copy_chain
import obseq3.byteproof.freshroot
import obseq3.byteproof.projdst
import obseq3.byteproof.ref
import obseq3.byteproof.move
import obseq3.byteproof.leafops
import obseq3.byteproof.readreg
import obseq3.byteproof.readsrc
import obseq3.byteproof.binop
import obseq3.byteproof.slice
import obseq3.byteproof.alloc
import obseq3.byteproof.refslice
import obseq3.byteproof.stmts
open Lean Elab Command

-- The byte-level proof (obseq3.byteproof, branch `byteaddress`) may rest
-- only on the three axioms the main audit whitelists. This fails — and the
-- work must STOP for a decision — if any declaration under
-- `obseq3.byteproof` reaches another axiom (`sorryAx` included).
#eval show CommandElabM Unit from do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let env ← getEnv
  let decls := env.constants.toList.filterMap fun (n, _) =>
    if (`obseq3.byteproof).isPrefixOf n && !n.isInternal then some n else none
  let mut bad : Array (Name × Name) := #[]
  let mut used : Array Name := #[]
  for n in decls do
    for a in (← liftCoreM (Lean.collectAxioms n)) do
      if !used.contains a then used := used.push a
      if !allowed.contains a then bad := bad.push (n, a)
  if bad.isEmpty then
    logInfo m!"byteproof axiom check OK: {decls.length} declarations; axioms used: {used.qsort (·.toString < ·.toString)}"
  else
    throwError m!"byteproof axiom check FAILED — new axioms: {bad}"
