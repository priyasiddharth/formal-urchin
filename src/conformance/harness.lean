import conformance.elab
import obseq3.compile_bytes
import obseq3.mirlite_bytes
import obseq3.layout_agree

/-!
Conformance harness: reads a manifest of Miri-derived tests, loads each
Charon ULLBC artifact through the loader/elaborator, runs it under the
obseq3 mirlite semantics on bytes (`mirlite_bytes.lean`, at the loader's
real layouts), and compares the verdict with the manifest's expectation.
`--osea` also compiles each program (`compile_bytes.lean`, same layouts)
and requires its target (`oseair_layout.lean`) to reach the same verdict.

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

/-! ## The model's verdict

mirlite on byte-addressed memory (`obseq3/mirlite_bytes.lean`) with the
loader's real layouts gives the verdict judged against Miri. -/

/-- The loader's byte layouts as an environment (a local without one — none
    should be missing — falls back to the uniform layout). -/
def Loaded.layEnv (l : Loaded) : mirliteB.LayEnv l.Γ :=
  fun i => l.blay.getD i.val (bytes.ofLayoutTy (l.Γ.get i))

/-- Locals whose byte layout does not have their type's shape
    (`bytes.Agrees`). Empty means the byte proof's two layout conditions
    hold for every place of the program
    (`byteproof.compileB_correct_agrees`). -/
def Loaded.layoutDisagreements (l : Loaded) : List (Nat × obseq3.LayoutTy × bytes.BLayout) :=
  (List.finRange l.Γ.length).filterMap fun i =>
    if bytes.Agrees (l.Γ.get i) (l.layEnv i) then none else some (i.val, l.Γ.get i, l.layEnv i)

/-- The byte model's verdict, and on UB the memory it failed in (the
    reason check turns a failing address into an allocation offset). -/
def runLoadedBytesFull (l : Loaded) (L : mirliteB.LayEnv l.Γ) : Verdict × Option bytes.Mem :=
  go (l.prog.length + 2) (mirliteB.State.initial M l.Γ)
where
  go : Nat → mirliteB.State M l.Γ → Verdict × Option bytes.Mem
    | 0, _ => (.fuelExhausted, none)
    | fuel + 1, st =>
        match l.prog[st.pc]? with
        | none => (.ok, none)
        | some .halt => (.ok, none)
        | some stmt =>
            match mirliteB.stepStmt M L st stmt with
            | .ok st' => go fuel st'
            | .err msg =>
                let line := l.lines[st.pc]?.getD 0
                if line ≥ 2 * certLineBase then (.certExhausted st.pc (line - 2 * certLineBase), none)
                else if line ≥ certLineBase then (.certRejected st.pc (line - certLineBase), none)
                else (.ub st.pc line msg, some st.mem)

def runLoadedBytes (l : Loaded) (L : mirliteB.LayEnv l.Γ) : Verdict :=
  (runLoadedBytesFull l L).1

/-! ## The reason check

A UB verdict is matched against Miri at the line; the REASON is matched
against Miri's own account of the UB (`<artifact>.miri.txt`, recorded by
`scripts/live.py` from the pinned Miri). Both sides are reduced to the
same small description — the operation that failed, why, and the byte
offset in the allocation where it failed — and must agree. -/

structure UBReason where
  /-- read | write | access (Miri: read or write) | retag | dealloc | other -/
  op : String
  /-- missing (tag not in the stack) | permission (tag too weak) |
      protector | no-exposed (wildcard) | uninit | oob | other -/
  cause : String
  /-- byte offset in the allocation where the check failed -/
  offset : Option Nat
deriving Repr, BEq

def UBReason.render (r : UBReason) : String :=
  s!"{r.op}/{r.cause}" ++ (match r.offset with | some o => s!"@{o}" | none => "")

private def has (s sub : String) : Bool := (s.splitOn sub).length > 1

private def hexVal (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

/-- The hex number right after the first `[0x` in `s`. -/
private def hexAfterBracket (s : String) : Option Nat :=
  match s.splitOn "[0x" with
  | _ :: rest :: _ =>
      let ds := rest.toList.takeWhile (fun c => (hexVal c).isSome)
      if ds.isEmpty then none
      else some (ds.foldl (fun acc c => acc * 16 + (hexVal c).getD 0) 0)
  | _ => none

/-- The first decimal number following " at " in `s`. -/
private def addrAfterAt (s : String) : Option Nat :=
  ((s.splitOn " at ").drop 1).findSome? fun piece =>
    let ds := piece.toList.takeWhile Char.isDigit
    if ds.isEmpty then none else (String.mk ds).toNat?

def causeOf (s : String) : String :=
  if has s "protected" then "protector"
  else if has s "no exposed tags" then "no-exposed"
  else if has s "does not exist in the borrow stack" || has s "no borrow stack" then "missing"
  else if has s "only grants" || has s "does not grant" then "permission"
  else if has s "uninitialized" then "uninit"
  else if has s "out-of-bounds" || has s "out of bounds" || has s "dangling"
    || has s "has been freed" || has s "not dereferenceable"
    -- an access that starts in bounds and runs past the end
    || has s "bytes from the end of the allocation" then "oob"
  else "other"

/-- Miri's report: its UB line (and the "occurs as part of" label). -/
def classifyMiri (report : String) : UBReason :=
  let lines := report.splitOn "\n"
  let main := lines.headD ""
  let part := String.intercalate " " (lines.drop 1)
  let op :=
    if has main "read access" then "read"
    else if has main "write access" then "write"
    else if has main "retag" then "retag"
    else if has main "deallocat" then "dealloc"
    else if has part "part of retag" then "retag"
    else if has part "part of a deallocation" then "dealloc"
    else if has part "part of an access" || has main "not granting access" then "access"
    else if has main "uninitialized" then "read"
    else "other"
  { op, cause := causeOf main, offset := hexAfterBracket main }

/-- Our model's UB message; a failing address becomes an offset in the
    allocation that contains it. -/
def classifyOurs (msg : String) (mem? : Option bytes.Mem) : UBReason :=
  let op :=
    if msg.startsWith "read access failed" || msg.startsWith "dealloc pointer read failed"
      || msg.startsWith "read of uninitialized" then "read"
    else if msg.startsWith "write access failed" then "write"
    else if msg.startsWith "retag failed" || msg.startsWith "move retag failed" then "retag"
    else if msg.startsWith "deallocation failed" then "dealloc"
    else "other"
  let offset := do
    let a ← addrAfterAt msg
    let m ← mem?
    let (base, _) ← m.allocOf a
    pure (a - base)
  { op, cause := causeOf msg, offset }

/-- Do two reasons agree? The cause must; the operation must (Miri's
    `access` is a read or a write); the offset must when both report one. -/
def reasonsAgree (miri ours : UBReason) : Bool :=
  miri.cause == ours.cause &&
  (miri.op == ours.op ||
   -- Miri's "access" is a read or a write; its protector message does not
   -- name the operation at all, and a retag and a deallocation both
   -- perform one (Miri's `Stack::dealloc`: "Step 1: Make a write access")
   (miri.op == "access" && (ours.op == "read" || ours.op == "write"
      || (miri.cause == "protector" && (ours.op == "retag" || ours.op == "dealloc"))))) &&
  (match miri.offset, ours.offset with
   | some a, some b => a == b
   | _, _ => true)

inductive ReasonStatus
| same (r : UBReason)
-- a difference the manifest records and explains (`"reason_known"`): a
-- documented model approximation, not a silent disagreement
| known (ours miri : UBReason) (why : String)
| differ (ours miri : UBReason)
| unchecked (why : String)
deriving Repr

/-- The statement a verdict blames, if any. -/
def Verdict.stmt? : Verdict → Option Nat
  | .ub i _ _ | .certRejected i _ | .certExhausted i _ => some i
  | _ => none

/-- Do two verdicts agree (ok↔ok, or UB at the same statement)? -/
def Verdict.agrees : Verdict → Verdict → Bool
  | .ok, .ok | .fuelExhausted, .fuelExhausted => true
  | a, b =>
      match a.stmt?, b.stmt? with
      | some i, some j => i == j
      | _, _ => false

/-! ## Differential mode (`--osea`)

Compile the loaded program to OSEA-IR (`compile_bytes.lean`, at the
loader's layouts) and require the SAME verdict as mirlite: ok↔ok, or UB
attributed (via the compiler's per-statement label ranges) to the same
source statement. A verdict mismatch is a hard failure of the suite. -/

inductive OseaRun
| ok
| ub (label : Nat) (msg : String)
| fuelExhausted

inductive OseaStatus
| skipped (reason : String)
| matched
| mismatch (why : String)
deriving Repr

/-- The byte compiler's output on its target (`oseair_layout.lean`). -/
def runOseaProgL (tprog : obseq3.oseairL.Prog) (fuel : Nat) : OseaRun :=
  go fuel (oseairL.State.initial M)
where
  go : Nat → oseairL.State M → OseaRun
    | 0, _ => .fuelExhausted
    | n + 1, st =>
        match tprog st.pc with
        | none => .ok
        | some .Halt => .ok
        | some _ =>
            match oseairL.step M st tprog with
            | .Ok st' => go n st'
            | .Err msg => .ub st.pc msg

/-- `--osea`: compiled at the loader's real layouts and run on the
    target, against the source's (judged) verdict `src` on the same
    layouts. -/
def oseaStatus (l : Loaded) (src : Verdict) : OseaStatus :=
  match compileB.compileProg l.layEnv l.prog with
  | .error (.unsupported w) => .skipped w
  | .error (.missingLocal i) => .skipped s!"local _{i} read before assignment"
  | .ok tprog =>
      let ranges := compileB.stmtLabelRanges l.layEnv l.prog
      let fuel := compileB.emittedLabels l.layEnv l.prog + 2
      match runOseaProgL tprog fuel, src, src.stmt? with
      | .ok, .ok, _ => .matched
      | .ub label msg, _, some srcIdx =>
          match ranges.findIdx? (fun r => r.1 ≤ label && label < r.2) with
          | some i =>
              if i == srcIdx then .matched
              else .mismatch
                s!"target UB at stmt {i} (label {label}: {msg}), source UB at stmt {srcIdx}"
          | none => .mismatch s!"target UB at unattributable label {label}: {msg}"
      | .ok, v, _ => .mismatch s!"target ok, source {v.render}"
      | .ub label msg, v, _ =>
          .mismatch s!"target UB (label {label}: {msg}), source {v.render}"
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
  -- `"reason_known"`: why this entry's UB reason is known to differ from
  -- Miri's (the verdict and line still match)
  reasonKnown : Option String := none
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
    let reasonKnown := getK t "reason_known" >>= asStr
    pure { id, artifact, status, expectUB, expectLine, certificate, reasonKnown : TestEntry }
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
  reason : Option ReasonStatus := none
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

/-- `--layouts`: load one entry and list the locals whose loader layout
    disagrees with its type (`none`: the entry does not load). -/
def layoutCheck (charonDir : String) (e : TestEntry) :
    IO (Option (List (Nat × obseq3.LayoutTy × bytes.BLayout))) := do
  try
    let content ← IO.FS.readFile s!"{charonDir}/{e.artifact}"
    match Json.parse content with
    | .error _ => pure none
    | .ok json =>
        match ← loadCert charonDir e with
        | .error _ => pure none
        | .ok cert? =>
            match loadCrate json cert? with
            | .error _ => pure none
            | .ok loaded => pure (some loaded.layoutDisagreements)
  catch _ => pure none

def runEntry (charonDir : String) (osea : Bool) (e : TestEntry) :
    IO TestResult := do
  let path := s!"{charonDir}/{e.artifact}"
  -- Miri's account of the UB, when live.py recorded one
  let reportPath := if e.artifact.endsWith ".ullbc.json"
    then some s!"{charonDir}/{(e.artifact.dropRight ".ullbc.json".length)}.miri.txt" else none
  let miriReport? : Option String ← match reportPath with
    | some p => do
        if ← System.FilePath.pathExists p then pure (some (← IO.FS.readFile p)) else pure none
    | none => pure none
  let (verdict, oseaSt, reasonSt, stats) ←
    try
      let content ← IO.FS.readFile path
      match Json.parse content with
      | .error err => pure (Verdict.loadError s!"json parse: {err}", none, none, {})
      | .ok json =>
          match ← loadCert charonDir e with
          | .error err => pure (Verdict.loadError err, none, none, {})
          | .ok cert? =>
            match loadCrate json cert? with
            | .error err => pure (Verdict.loadError err, none, none, {})
            | .ok loaded =>
                -- the JUDGED verdict, on the real layouts
                let (v, mem?) := runLoadedBytesFull loaded loaded.layEnv
                let reason : Option ReasonStatus := match v, miriReport? with
                  | .ub _ _ msg, some rep =>
                      let ours := classifyOurs msg mem?
                      let miri := classifyMiri rep
                      some (if reasonsAgree miri ours then .same ours
                            else match e.reasonKnown with
                              | some why => .known ours miri why
                              | none => .differ ours miri)
                  | .ub _ _ _, none => some (.unchecked "no Miri report recorded")
                  | _, _ => none
                pure (v, if osea then some (oseaStatus loaded v) else none,
                  reason, loaded.stats)
    catch ex =>
      pure (Verdict.loadError s!"io: {ex}", none, none, {})
  return { entry := e, verdict, outcome := judge e verdict, osea := oseaSt,
           reason := reasonSt, stats }

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
    IO.println s!"        [certified: {r.stats.checked} checked ({r.stats.runtime} at runtime), {r.stats.pinned} unchecked]"
  match r.osea with
  | some .matched => if record then IO.println s!"        [osea: matched]"
  | some (.mismatch why) => IO.println s!"        OSEA MISMATCH: {why}"
  | some (.skipped reason) =>
      if record then IO.println s!"        [osea: skipped — {reason}]"
  | none => pure ()
  match r.reason with
  | some (.same rr) => if record then IO.println s!"        [reason: as Miri — {rr.render}]"
  | some (.differ ours miri) =>
      IO.println s!"        REASON DIFFERS: ours {ours.render}, Miri {miri.render}"
  | some (.known ours miri why) =>
      if record then IO.println s!"        [reason: known difference — ours {ours.render}, Miri {miri.render}: {why}]"
  | some (.unchecked why) => if record then IO.println s!"        [reason: unchecked — {why}]"
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
    let runtime := certified.foldl (· + ·.stats.runtime) 0
    let pinned := certified.foldl (· + ·.stats.pinned) 0
    let withRuntime := certified.filter (·.stats.runtime > 0) |>.length
    -- a branch the lowering FOLDS is cross-checked against Miri's arm at
    -- lowering time (T1); one it cannot fold gets a check the PROGRAM
    -- runs (T2), which is the tier with teeth against a wrong pin
    IO.println s!"certificates: {certified.length} entries | checked {checked} ({checked - runtime} static, {runtime} runtime in {withRuntime} entries) | unchecked {pinned}"
    for r in certified do
      if r.stats.runtime > 0 then
        IO.println s!"  runtime-checked: {r.entry.id} ({r.stats.runtime})"
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
  let reasons := rs.filterMap (·.reason)
  if !reasons.isEmpty then
    let rc (f : ReasonStatus → Bool) := (reasons.filter f).length
    IO.println s!"reasons: as Miri {rc fun s => match s with | .same _ => true | _ => false} | known differences {rc fun s => match s with | .known _ _ _ => true | _ => false} | differ {rc fun s => match s with | .differ _ _ => true | _ => false} | unchecked {rc fun s => match s with | .unchecked _ => true | _ => false}"
  -- an UNRECORDED reason difference fails the suite, as a wrong line does
  let reasonDiffs := (rs.filterMap (·.reason)).filter (fun s => match s with | .differ _ _ => true | _ => false) |>.length
  return if fails > 0 || xpasses > 0 || oseaMismatches > 0 || reasonDiffs > 0 then 1 else 0

end conformance
