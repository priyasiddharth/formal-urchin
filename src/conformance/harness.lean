import conformance.elab
import obseq3.compile

/-!
Conformance harness: reads a manifest of Miri-derived tests, loads each
Charon ULLBC artifact through the loader/elaborator, runs it under the
obseq3 mirlite semantics, and compares the verdict with the manifest's
expectation.

Outcomes:
- `pass`        — verdict (and line, when specified) matches expectation
- `fail`        — mismatch; a fail-test verdicting ok (missed UB) is the
                  dangerous direction and is always a hard failure
- `xfail`       — expected model divergence (status `xfail-model`)
- `xpass`       — an xfail-model test unexpectedly agreed with Miri:
                  reported as a failure so the manifest gets recurated
- `unsupported` — loader rejected the test, as the manifest expects
- `promote`     — a test marked unsupported now loads and runs: warning
Verdicts are matched structurally (ok vs ub@line); Miri's error *text* is
never matched.
-/

namespace conformance

open obseq3 obseq3.mirlite
open Lean (Json)

abbrev M := PermissionModel.stackedBorrows

inductive Verdict
| ok
| ub (stmtIdx : Nat) (line : Nat) (msg : String)
| loadError (msg : String)
| fuelExhausted
-- a certificate CHECK failed: the branch Miri recorded was not the one
-- mirlite's state selects at this source line — never a program verdict
| certRejected (stmtIdx : Nat) (line : Nat)
-- mirlite ran past the point where Miri's execution ended in UB/panic
| certExhausted (stmtIdx : Nat) (line : Nat)
deriving Repr, BEq

def Verdict.render : Verdict → String
  | .ok => "ok"
  | .ub _ line msg => s!"ub@line {line}: {msg}"
  | .loadError msg => s!"load error: {msg}"
  | .fuelExhausted => "fuel exhausted"
  | .certRejected _ line => s!"certificate rejected at line {line} (Miri's recorded branch was not taken)"
  | .certExhausted _ line => s!"ran past Miri's UB point (line {line})"

def runLoaded (l : Loaded) : Verdict :=
  go (l.prog.length + 2) (State.initial M l.Γ)
where
  go : Nat → State M l.Γ → Verdict
    | 0, _ => .fuelExhausted
    | fuel + 1, st =>
        match l.prog[st.pc]? with
        | none => .ok
        | some .halt => .ok
        | some stmt =>
            match stepStmt M st stmt with
            | .ok st' => go fuel st'
            | .err msg =>
                let line := l.lines[st.pc]?.getD 0
                if line ≥ 2 * certLineBase then .certExhausted st.pc (line - 2 * certLineBase)
                else if line ≥ certLineBase then .certRejected st.pc (line - certLineBase)
                else .ub st.pc line msg

/-! ## Differential mode (`--osea`)

Compile the loaded program to OSEA-IR-v3 and require the SAME verdict as
mirlite: ok↔ok, or UB attributed (via the compiler's per-statement label
ranges) to the same source statement. The compiler covers only the
proof-core subset (constInit/copy/ref/halt); everything else is reported
as skipped with the compiler's reason. A verdict mismatch is a hard
failure of the suite. -/

inductive OseaRun
| ok
| ub (label : Nat) (msg : String)
| fuelExhausted

def runOseaProg (tprog : obseq3.oseair.Prog) (fuel : Nat) : OseaRun :=
  go fuel (oseair.State.initial M)
where
  go : Nat → oseair.State M → OseaRun
    | 0, _ => .fuelExhausted
    | n + 1, st =>
        match tprog st.pc with
        | none => .ok
        | some .Halt => .ok
        | some _ =>
            match oseair.step M st tprog with
            | .Ok st' => go n st'
            | .Err msg => .ub st.pc msg

inductive OseaStatus
| skipped (reason : String)
| matched
| mismatch (why : String)
deriving Repr

def oseaStatus (l : Loaded) (src : Verdict) : OseaStatus :=
  match compile.compileProg l.prog with
  | .error (.unsupported w) => .skipped w
  | .error (.missingLocal i) => .skipped s!"local _{i} read before assignment"
  | .ok tprog =>
      let ranges := compile.stmtLabelRanges l.prog
      let fuel := compile.emittedLabels l.prog + 2
      -- a certificate check that failed is UB at its statement on both
      -- machines (the `copy` of an uninitialised cell), attributed alike
      let srcErr? : Option Nat := match src with
        | .ub i _ _ => some i
        | .certRejected i _ => some i
        | .certExhausted i _ => some i
        | _ => none
      match runOseaProg tprog fuel, src, srcErr? with
      | .ok, .ok, _ => .matched
      | .ub label msg, _, some srcIdx =>
          match ranges.findIdx? (fun r => r.1 ≤ label && label < r.2) with
          | some i =>
              if i == srcIdx then .matched
              else .mismatch
                s!"target UB at stmt {i} (label {label}: {msg}), source UB at stmt {srcIdx}"
          | none => .mismatch s!"target UB at unattributable label {label}: {msg}"
      | .ok, v, _ => .mismatch s!"target ok, source {v.render}"
      | .ub label msg, v, _ => .mismatch s!"target UB (label {label}: {msg}), source {v.render}"
      | .fuelExhausted, _, _ => .mismatch "target fuel exhausted"

/-! ## Manifest -/

inductive TestStatus
| supported
| unsupported (reason : String)
| xfailModel (reason : String)
deriving Repr, BEq

structure TestEntry where
  id : String
  artifact : String
  status : TestStatus
  expectUB : Bool
  expectLine : Option Nat
  certificate : Option String := none   -- `<name>.cert.json` beside the artifact
deriving Repr

structure Manifest where
  tests : List TestEntry

def parseManifest (j : Json) : Except String Manifest := do
  let testsJ ← match getK j "tests" with
    | some t => pure (asArr t)
    | none => .error "manifest has no tests field"
  let tests ← testsJ.mapM fun t => do
    let id ← match getK t "id" >>= asStr with
      | some s => pure s
      | none => .error "test entry without id"
    -- unsupported entries may have no artifact; the read then fails,
    -- which is exactly the expected loadError outcome
    let artifact := (getK t "artifact" >>= asStr).getD "<none>"
    let reason := (getK t "reason" >>= asStr).getD "unspecified"
    let status ← match getK t "status" >>= asStr with
      | some "supported" => pure TestStatus.supported
      | some "unsupported" => pure (TestStatus.unsupported reason)
      | some "xfail-model" => pure (TestStatus.xfailModel reason)
      | some s => .error s!"{id}: unknown status {s}"
      | none => .error s!"{id}: no status"
    let expected := getK t "expected"
    let expectUB := (expected >>= (getK · "verdict") >>= asStr) == some "ub"
    let expectLine := expected >>= (getK · "line") >>= asNat
    let certificate := getK t "certificate" >>= asStr
    pure { id, artifact, status, expectUB, expectLine, certificate : TestEntry }
  return { tests }

/-! ## Outcomes -/

inductive Outcome
| pass | fail (why : String) | xfail | xpass | unsupportedOk | promote
deriving Repr, BEq

def Outcome.isFailure : Outcome → Bool
  | .fail _ | .xpass => true
  | _ => false

def verdictMatches (e : TestEntry) (v : Verdict) : Bool :=
  match v, e.expectUB with
  | .ok, false => true
  | .ub _ line _, true =>
      match e.expectLine with
      | some l => l == line
      | none => true
  | _, _ => false

def judge (e : TestEntry) (v : Verdict) : Outcome :=
  match e.status with
  | .supported =>
      match v with
      | .loadError msg => .fail s!"loader rejected a supported test: {msg}"
      | .fuelExhausted => .fail "fuel exhausted"
      | .certRejected _ line => .fail s!"certificate rejected at line {line}: mirlite did not take Miri's recorded branch"
      | .certExhausted _ line => .fail s!"missed UB: ran past Miri's UB point (line {line})"
      | v =>
          if verdictMatches e v then .pass
          else if e.expectUB then .fail s!"missed UB: expected ub, got {v.render}"
          else .fail s!"false positive: expected ok, got {v.render}"
  | .unsupported _ =>
      match v with
      | .loadError _ => .unsupportedOk
      | _ => .promote
  | .xfailModel _ =>
      if verdictMatches e v then .xpass else .xfail

structure TestResult where
  entry : TestEntry
  verdict : Verdict
  outcome : Outcome
  osea : Option OseaStatus := none
  stats : CertStats := {}

/-- Read and parse an entry's certificate, if it names one. -/
def loadCert (charonDir : String) (e : TestEntry) : IO (Except String (Option Cert)) := do
  match e.certificate with
  | none => return .ok none
  | some name =>
      try
        let content ← IO.FS.readFile s!"{charonDir}/{name}"
        match Json.parse content with
        | .error err => return .error s!"certificate json parse: {err}"
        | .ok json =>
            match parseCert json with
            | .error err => return .error err
            | .ok c => return .ok (some c)
      catch ex =>
        return .error s!"certificate io: {ex}"

def runEntry (charonDir : String) (osea : Bool) (e : TestEntry) : IO TestResult := do
  let path := s!"{charonDir}/{e.artifact}"
  let (verdict, oseaSt, stats) ←
    try
      let content ← IO.FS.readFile path
      match Json.parse content with
      | .error err => pure (Verdict.loadError s!"json parse: {err}", none, {})
      | .ok json =>
          match ← loadCert charonDir e with
          | .error err => pure (Verdict.loadError err, none, {})
          | .ok cert? =>
            match loadCrate json cert? with
            | .error err => pure (Verdict.loadError err, none, {})
            | .ok loaded =>
                let v := runLoaded loaded
                pure (v, if osea then some (oseaStatus loaded v) else none, loaded.stats)
    catch ex =>
      pure (Verdict.loadError s!"io: {ex}", none, {})
  return { entry := e, verdict, outcome := judge e verdict, osea := oseaSt, stats }

def outcomeLabel : Outcome → String
  | .pass => "PASS"
  | .fail _ => "FAIL"
  | .xfail => "XFAIL"
  | .xpass => "XPASS(!)"
  | .unsupportedOk => "UNSUPPORTED"
  | .promote => "PROMOTE(!)"

def reportResult (r : TestResult) (record : Bool) : IO Unit := do
  let base := s!"{outcomeLabel r.outcome}  {r.entry.id}"
  match r.outcome with
  | .fail why => IO.println s!"{base}\n        {why}"
  | .promote => IO.println s!"{base}\n        loads and runs ({r.verdict.render}); promote in manifest"
  | _ =>
      if record then IO.println s!"{base}  [observed: {r.verdict.render}]"
      else IO.println base
  if r.stats.used && (record || r.stats.pinned > 0) then
    IO.println s!"        [certified: {r.stats.checked} checked, {r.stats.pinned} unchecked]"
  match r.osea with
  | some .matched => IO.println s!"        [osea: matched]"
  | some (.mismatch why) => IO.println s!"        OSEA MISMATCH: {why}"
  | some (.skipped reason) =>
      if record then IO.println s!"        [osea: skipped — {reason}]"
  | none => pure ()

def summarize (rs : List TestResult) : IO UInt32 := do
  let count (f : Outcome → Bool) := rs.filter (f ·.outcome) |>.length
  let passes := count (· == .pass)
  let fails := count (fun o => match o with | .fail _ => true | _ => false)
  let xfails := count (· == .xfail)
  let xpasses := count (· == .xpass)
  let unsup := count (· == .unsupportedOk)
  let promotes := count (· == .promote)
  IO.println ""
  IO.println s!"pass {passes} | fail {fails} | xfail {xfails} | xpass {xpasses} | unsupported {unsup} | promote {promotes} | total {rs.length}"
  let certified := rs.filter (·.stats.used)
  if !certified.isEmpty then
    let checked := certified.foldl (· + ·.stats.checked) 0
    let pinned := certified.foldl (· + ·.stats.pinned) 0
    IO.println s!"certificates: {certified.length} entries | checked {checked} | unchecked {pinned}"
    for r in certified do
      if r.stats.pinned > 0 then
        IO.println s!"  unchecked pins: {r.entry.id} ({r.stats.pinned})"
  let oseaSts := rs.filterMap (·.osea)
  let oseaMismatches ←
    if oseaSts.isEmpty then pure 0
    else do
      let cnt (f : OseaStatus → Bool) := (oseaSts.filter f).length
      let matched := cnt (fun s => match s with | .matched => true | _ => false)
      let mism := cnt (fun s => match s with | .mismatch _ => true | _ => false)
      let skipped := cnt (fun s => match s with | .skipped _ => true | _ => false)
      IO.println s!"osea: matched {matched} | mismatch {mism} | skipped {skipped}"
      pure mism
  return if fails > 0 || xpasses > 0 || oseaMismatches > 0 then 1 else 0

end conformance
