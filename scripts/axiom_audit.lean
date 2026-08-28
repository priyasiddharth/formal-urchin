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

/-- The whitelist lives in a data file next to this script; the audit
    compares the CURRENT state against it in both directions. -/
def whitelistPath : System.FilePath := "scripts/axiom_whitelist.txt"

/-- Parse the whitelist file: `[axioms]` / `[sorries]` sections, one name
    per line, `#` comments. -/
def parseWhitelist (text : String) : Except String (List String × List String) := Id.run do
  let mut axioms : List String := []
  let mut sorries : List String := []
  let mut section? : Option String := none
  for line in text.splitOn "\n" do
    let line := line.trimAscii.toString
    if line.isEmpty || line.startsWith "#" then
      continue
    else if line == "[axioms]" || line == "[sorries]" then
      section? := some line
    else
      match section? with
      | some "[axioms]" => axioms := axioms ++ [line]
      | some "[sorries]" => sorries := sorries ++ [line]
      | _ => return .error s!"whitelist entry outside a section: {line}"
  return .ok (axioms, sorries)

/-- Both-direction set comparison; returns (extra-in-current, stale-in-whitelist). -/
def diffSets (current whitelist : List String) : List String × List String :=
  (current.filter (fun c => !whitelist.contains c),
   whitelist.filter (fun w => !current.contains w))

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
  let text ← IO.FS.readFile whitelistPath
  let (wlAxioms, wlSorries) ← match parseWhitelist text with
    | .ok v => pure v
    | .error e => throwError "axiom audit: bad whitelist file: {e}"
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
  -- exact comparison, both directions, both sections
  let (rogueAx, staleAx) :=
    diffSets (allAxioms.toList.map toString) wlAxioms
  let (rogueSorry, staleSorry) :=
    diffSets (allSorryRoots.toList.map toString) wlSorries
  let mut failures : List String := []
  unless rogueAx.isEmpty do
    failures := failures ++ [s!"axioms NOT in the whitelist: {rogueAx}"]
  unless staleAx.isEmpty do
    failures := failures ++ [s!"whitelisted axioms no longer used (stale): {staleAx}"]
  unless rogueSorry.isEmpty do
    failures := failures ++ [s!"UNAUDITED sorries reachable from the root: {rogueSorry}"]
  unless staleSorry.isEmpty do
    failures := failures ++ [s!"pinned sorries no longer present (closed?): {staleSorry}"]
  unless failures.isEmpty do
    throwError "axiom audit FAILED — current state ≠ {whitelistPath}:\n  {String.intercalate "\n  " failures}\n(update the whitelist file only together with the SORRY AUDIT block)"
  IO.println s!"axiom audit OK — matches {whitelistPath}
  roots        : {auditRoots}
  axioms used  : {allAxioms.toList}
  sorry roots  : {allSorryRoots.toList} ({allSorryRoots.size} audited)"
