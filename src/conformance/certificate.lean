import conformance.ullbc_ast

/-!
# Execution certificates

A conformance program is closed and deterministic, so it has exactly one
execution. A CERTIFICATE records that execution's branch outcomes — the
arm every `switch` took, whether every `assert` passed — as Miri saw
them (`MIRI_LOG=info`; see conformance/scripts/miri_cert.py). The seam
consumes it to emit the one path that runs as straight-line mirlite,
unrolling loops, and to emit runtime CHECKS (built from `uninit`,
`assignIf` and `copy` alone) that reject a wrong branch before any code
that depends on it runs. Since mirlite gained `binOp` (2026-09-24) the
discriminant of every recorded branch is a word the program actually
computed, so every branch is either folded-and-cross-checked or
runtime-checked — none is taken on Miri's word alone.

Events are matched by KIND in execution ORDER per user-frame instance —
never by block or local numbers, which differ between charon's built MIR
and the runtime MIR Miri executes. Frame instances are in Miri's entry
(pre-order) order, which is the order `inlineCall` visits callees.
-/

namespace conformance

open Lean (Json)

inductive CertOutcome
| ok | ub | panic
deriving Repr, BEq, Inhabited

inductive CertKind
| switch (arm : Option Nat)   -- `none` = the `otherwise` arm
| assert (success : Bool)
deriving Repr, BEq, Inhabited

structure CertEvent where
  kind : CertKind
  dropFlag : Bool := false   -- a runtime-MIR drop-flag switch: skipped
  descr : String := ""       -- Miri's terminator text, for messages
deriving Repr, Inhabited

structure CertFrame where
  fn : String
  events : Array CertEvent
deriving Repr, Inhabited

structure Cert where
  outcome : CertOutcome
  frames : Array CertFrame
deriving Repr, Inhabited

def parseCertEvent (j : Json) : Except String CertEvent := do
  let descr := (getK j "descr" >>= asStr).getD ""
  let dropFlag := (getK j "drop_flag") == some (Json.bool true)
  match getK j "k" >>= asStr with
  | some "switch" =>
      let arm ← match getK j "arm" with
        | some (Json.str "otherwise") => pure none
        | some (Json.str s) =>
            match s.toNat? with
            | some n => pure (some n)
            | none => .error s!"certificate: bad switch arm {s}"
        | some v =>
            match asNat v with
            | some n => pure (some n)
            | none => .error s!"certificate: bad switch arm {v.compress}"
        | none => .error "certificate: switch event without arm"
      return { kind := .switch arm, dropFlag, descr }
  | some "assert" =>
      match getK j "outcome" >>= asStr with
      | some "success" => return { kind := .assert true, dropFlag, descr }
      | some "panic" => return { kind := .assert false, dropFlag, descr }
      | _ => .error "certificate: assert event without outcome"
  | some k => .error s!"certificate: unknown event kind {k}"
  | none => .error "certificate: event without kind"

def parseCert (j : Json) : Except String Cert := do
  let outcome ← match getK j "outcome" >>= asStr with
    | some "ok" => pure CertOutcome.ok
    | some "ub" => pure CertOutcome.ub
    | some "panic" => pure CertOutcome.panic
    | some o => .error s!"certificate: unknown outcome {o}"
    | none => .error "certificate: no outcome"
  let framesJ := (getK j "frames").map asArr |>.getD []
  let frames ← framesJ.mapM fun fj => do
    let fn ← match getK fj "fn" >>= asStr with
      | some s => pure s
      | none => .error "certificate: frame without fn"
    let events ← ((getK fj "events").map asArr |>.getD []).mapM parseCertEvent
    pure ({ fn, events := events.toArray } : CertFrame)
  return { outcome, frames := frames.toArray }

/-- What the lowering did with a certificate, for the harness report. -/
structure CertStats where
  used : Bool := false
  checked : Nat := 0   -- T1 cross-checks and T2 runtime checks
  pinned : Nat := 0    -- arms followed on Miri's word alone: 0 since `binOp`
deriving Repr, Inhabited

/-- A cursor over the certificate: which frame instance is next to open,
    and for each open frame (innermost first) how many events it has
    consumed. -/
structure CertCursor where
  cert : Cert
  nextFrame : Nat := 0
  stack : List (Nat × Nat) := []   -- (frame index, next event index)
  checked : Nat := 0   -- T1 cross-checks + T2 runtime checks emitted
  pinned : Nat := 0    -- arms followed on Miri's word alone: 0 since `binOp`
deriving Inhabited

namespace CertCursor

/-- Enter the next user-frame instance; its recorded name must agree. -/
def openFrame (c : CertCursor) (fn : String) : Except String CertCursor :=
  match c.cert.frames[c.nextFrame]? with
  | none => .error s!"certificate: lowering entered {fn} but Miri recorded no further frame"
  | some fr =>
      if fr.fn != fn then
        .error s!"certificate: frame {c.nextFrame} is {fr.fn}, lowering entered {fn}"
      else
        .ok { c with nextFrame := c.nextFrame + 1, stack := (c.nextFrame, 0) :: c.stack }

/-- Remaining non-drop-flag events of the innermost open frame. -/
def remaining (c : CertCursor) : Nat :=
  match c.stack with
  | (fi, ei) :: _ =>
      match c.cert.frames[fi]? with
      | some fr => (fr.events.toList.drop ei).filter (fun e => !e.dropFlag) |>.length
      | none => 0
  | [] => 0

/-- Leave the innermost frame; every real event must have been consumed. -/
def closeFrame (c : CertCursor) (fn : String) : Except String CertCursor :=
  match c.stack with
  | [] => .error s!"certificate: closing {fn} with no open frame"
  | _ :: rest =>
      let k := c.remaining
      if k > 0 then
        .error s!"certificate: frame for {fn} has {k} unconsumed events (lowering took fewer branches than Miri)"
      else .ok { c with stack := rest }

/-- The next real event of the innermost frame, if any. -/
partial def nextEvent (c : CertCursor) : Option (CertEvent × CertCursor) :=
  match c.stack with
  | [] => none
  | (fi, ei) :: rest =>
      match c.cert.frames[fi]? with
      | none => none
      | some fr =>
          match fr.events[ei]? with
          | none => none
          | some e =>
              let c' := { c with stack := (fi, ei + 1) :: rest }
              if e.dropFlag then nextEvent c' else some (e, c')

end CertCursor

end conformance
