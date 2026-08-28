import Lean
import obseq3.proof.compiler

/-!
# Axiom audit

Elaborating this file audits the MAIN correctness theorem's transitive
axiom closure against a pinned whitelist, and pins the exact set of
sorried declarations it rests on. Any drift — a new axiom (including
`ofReduceBool` from `native_decide`, or a project-local `axiom`), or a
new/removed `sorry` — fails elaboration, so

    lake env lean scripts/axiom_audit.lean      # or scripts/audit_axioms.sh

exits nonzero. `Lean.collectAxioms` walks the FULL dependency tree of
the root, so axioms smuggled in through any lemma the proof consumes
are caught; declarations not reachable from the root are by definition
irrelevant to the correctness statement.

When a residual is closed (or a new audited sorry is introduced), update
`expectedSorryRoots` in the same commit — the audit is the machine-checked
mirror of the SORRY AUDIT block in `obseq3/proof/compiler.lean`.
-/

open Lean

/-- The roots whose closures are audited. -/
def auditRoots : List Name :=
  [``obseq3.proof.compile_correct]

/-- The only axioms the correctness theorem may rest on. `sorryAx` is
    admitted ONLY through the audited residuals pinned below. -/
def axiomWhitelist : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound, ``sorryAx]

/-- The audited sorry roots (must match the SORRY AUDIT block). -/
def expectedSorryRoots : List Name :=
  [``obseq3.proof.copy_place_residual,
   ``obseq3.proof.ref_place_residual,
   ``obseq3.proof.const_write_deref_deep_residual,
   ``obseq3.proof.const_write_proj_nonlocal_residual]

/-- Constants directly referenced by a declaration's type and value. -/
private def usedConsts (ci : ConstantInfo) : Array Name :=
  ci.type.getUsedConstants ++
    (match ci.value? with | some v => v.getUsedConstants | none => #[])

/-- All declarations reachable from `root` whose OWN body mentions
    `sorryAx` — the sorry roots, as opposed to their consumers. -/
private partial def sorryRootsFrom (env : Environment) (root : Name) :
    Array Name := Id.run do
  let mut visited : NameSet := {}
  let mut out : Array Name := #[]
  let mut stack : Array Name := #[root]
  while h : stack.size > 0 do
    let n := stack.back h
    stack := stack.pop
    if visited.contains n then
      continue
    visited := visited.insert n
    match env.find? n with
    | none => continue
    | some ci =>
      let used := usedConsts ci
      if used.contains ``sorryAx && n != ``sorryAx then
        out := out.push n
      for d in used do
        unless visited.contains d do
          stack := stack.push d
  return out

open Elab Command in
#eval show CoreM Unit from do
  let env ← getEnv
  let mut allAxioms : NameSet := {}
  let mut allSorryRoots : NameSet := {}
  for root in auditRoots do
    unless env.contains root do
      throwError "axiom audit: root {root} not found"
    let axs ← collectAxioms root
    for a in axs do
      allAxioms := allAxioms.insert a
    for s in sorryRootsFrom env root do
      allSorryRoots := allSorryRoots.insert s
  -- 1. no axiom outside the whitelist
  let rogue := allAxioms.toList.filter (fun a => !axiomWhitelist.contains a)
  unless rogue.isEmpty do
    throwError "axiom audit FAILED — axioms outside the whitelist: {rogue}"
  -- 2. the sorry set is EXACTLY the audited one
  let unexpected := allSorryRoots.toList.filter
    (fun s => !expectedSorryRoots.contains s)
  let closed := expectedSorryRoots.filter
    (fun s => !allSorryRoots.contains s)
  unless unexpected.isEmpty do
    throwError "axiom audit FAILED — UNAUDITED sorries reachable from the root: {unexpected}\n(add to expectedSorryRoots only with an audit entry)"
  unless closed.isEmpty do
    throwError "axiom audit FAILED — pinned sorries no longer present (closed?): {closed}\n(remove them from expectedSorryRoots)"
  IO.println s!"axiom audit OK
  roots        : {auditRoots}
  axioms used  : {allAxioms.toList}
  sorry roots  : {allSorryRoots.toList} ({allSorryRoots.size} audited)"
