import conformance.harness
import obseq3.tests
import obseq3.compile_tests

/-!
`sb_conformance` executable.

Usage:
  sb_conformance --manifest <path> --charon-dir <path> [--filter <substr>]
                 [--record] [--dump <test-id>] [--unit] [--osea] [--layouts]

- default: run the manifest, print per-test outcomes and a summary;
  exit 1 on any FAIL/XPASS.
- --record: additionally print each observed verdict (for curating
  expected lines in the manifest).
- --dump <id>: print the lowered untyped program of one test (loader
  golden-check / curation aid).
- --unit: run the obseq3 unit tests first.
- the verdict is mirlite's on byte-addressed memory, at the loader's real
  layouts.
- --osea: differential mode — additionally compile each loaded program to
  OSEA-IR (`compile.lean`, same layouts) and require the same verdict
  as mirlite (mismatch = failure).
- --layouts: instead of running, check each loaded program's byte layouts
  against its locals' types (`bytes.Agrees`; the byte proof's layout
  conditions, `proof.compile_correct_agrees`) and list disagreements.
-/

namespace conformance

structure Args where
  manifest : Option String := none
  charonDir : Option String := none
  filter : Option String := none
  record : Bool := false
  dump : Option String := none
  unit : Bool := false
  osea : Bool := false
  layouts : Bool := false

def parseArgs : List String → Except String Args
  | [] => .ok {}
  | "--manifest" :: v :: rest => do return { ← parseArgs rest with manifest := some v }
  | "--charon-dir" :: v :: rest => do return { ← parseArgs rest with charonDir := some v }
  | "--filter" :: v :: rest => do return { ← parseArgs rest with filter := some v }
  | "--record" :: rest => do return { ← parseArgs rest with record := true }
  | "--dump" :: v :: rest => do return { ← parseArgs rest with dump := some v }
  | "--unit" :: rest => do return { ← parseArgs rest with unit := true }
  | "--osea" :: rest => do return { ← parseArgs rest with osea := true }
  | "--layouts" :: rest => do return { ← parseArgs rest with layouts := true }
  | arg :: _ => .error s!"unknown argument {arg}"

def dumpTest (charonDir : String) (m : Manifest) (id : String) : IO UInt32 := do
  match m.tests.find? (·.id == id) with
  | none => IO.eprintln s!"no test {id} in manifest"; return 1
  | some e =>
      let content ← IO.FS.readFile s!"{charonDir}/{e.artifact}"
      match Lean.Json.parse content with
      | .error err => IO.eprintln s!"json parse: {err}"; return 1
      | .ok json =>
          match parseCrate json with
          | .error err => IO.eprintln s!"parse: {err}"; return 1
          | .ok crate =>
              let cert? ← match ← loadCert charonDir e with
                | .ok c => pure c
                | .error err => IO.eprintln s!"certificate: {err}"; pure none
              match lowerCrate crate cert? with
              | .error err => IO.eprintln s!"lowering: {err}"; return 1
              | .ok lp => do
                  if lp.stats.used then
                    IO.println s!"certificate: {lp.stats.checked} checked, {lp.stats.pinned} unchecked"
                  IO.println s!"locals ({lp.locals.length}):"
                  for (i, ty) in lp.locals.zipIdx.map (fun (a, b) => (b, a)) do
                    IO.println s!"  _{i}: {reprStr ty}"
                  IO.println s!"statements ({lp.stmts.length}):"
                  for s in lp.stmts do
                    let tag (line : Nat) : String :=
                      if line ≥ 3 * certLineBase then s!"[assume {line - 3 * certLineBase}]"
                      else if line ≥ 2 * certLineBase then s!"[poison {line - 2 * certLineBase}]"
                      else if line ≥ certLineBase then s!"[cert {line - certLineBase}]"
                      else s!"[line {line}]"
                    match s with
                    | .assign dst rv line =>
                        IO.println s!"  {tag line} {reprStr dst} := {reprStr rv}"
                    | .assignIf discr v dst rv line =>
                        IO.println s!"  {tag line} if {reprStr discr} == {v}: {reprStr dst} := {reprStr rv}"
                    | .alloc dst sz line =>
                        IO.println s!"  [line {line}] {reprStr dst} := alloc {reprStr sz}"
                    | .dealloc p line =>
                        IO.println s!"  [line {line}] dealloc {reprStr p}"
                    | .check discr vs m line =>
                        IO.println s!"  {tag line} check {reprStr discr} {if m then "∈" else "∉"} {vs}"
                    | .pushProt line => IO.println s!"  [line {line}] pushProtectors"
                    | .popProt line => IO.println s!"  [line {line}] popProtectors"
                  match elabProg lp with
                  | .error err => IO.println s!"elaboration: {err}"; return 1
                  | .ok loaded => do
                      IO.println s!"elaborated ok: {loaded.prog.length} statements (incl. halt)"
                      IO.println s!"verdict: {(runLoadedBytes loaded loaded.layEnv).render}"
                      return 0

def realMain (args : List String) : IO UInt32 := do
  match parseArgs args with
  | .error e => IO.eprintln e; return 2
  | .ok a => do
    if a.unit then
      obseq3.Tests.runAll
      obseq3.CompileTests.runAll
    match a.manifest, a.charonDir with
    | some mPath, some cDir => do
        let content ← IO.FS.readFile mPath
        match Lean.Json.parse content with
        | .error err => IO.eprintln s!"manifest json: {err}"; return 2
        | .ok json =>
            match parseManifest json with
            | .error err => IO.eprintln s!"manifest: {err}"; return 2
            | .ok m =>
                match a.dump with
                | some id => dumpTest cDir m id
                | none => do
                    let tests := match a.filter with
                      | some f => m.tests.filter (fun (t : TestEntry) => (t.id.splitOn f).length > 1)
                      | none => m.tests
                    if a.layouts then
                      let mut ok := 0
                      let mut bad := 0
                      let mut unloaded := 0
                      for e in tests do
                        match ← layoutCheck cDir e with
                        | none => unloaded := unloaded + 1
                        | some [] => ok := ok + 1
                        | some ds =>
                            bad := bad + 1
                            IO.println s!"{e.id}:"
                            for (i, τ, l) in ds do
                              IO.println s!"  _{i}: {reprStr τ} vs {reprStr l}"
                      IO.println s!"layouts agree: {ok}, disagree: {bad}, not loaded: {unloaded}"
                      return (if bad == 0 then 0 else 1)
                    let mut results := []
                    for e in tests do
                      let r ← runEntry cDir a.osea e
                      reportResult r a.record
                      results := r :: results
                    summarize results.reverse
    | _, _ =>
        if a.unit then return 0
        else do IO.eprintln "usage: sb_conformance --manifest <path> --charon-dir <path>"; return 2

end conformance

def main (args : List String) : IO UInt32 :=
  conformance.realMain args
