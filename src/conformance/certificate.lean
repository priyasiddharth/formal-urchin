import conformance.ullbc_ast

/-!
# Execution certificates

A conformance program is closed and deterministic, so it has exactly one
execution. A CERTIFICATE records that execution's branch outcomes — the
arm every `switch` took, whether every `assert` passed — as Miri saw
them (`MIRI_LOG=info`; see conformance/scripts/miri_cert.py). The seam
consumes it to emit the one path that runs as straight-line mirlite,
unrolling loops, and to emit runtime CHECKS (`check` statements) that
reject a wrong branch before any code
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

/-- One Box destructor Miri ran (`<Box<T> as Drop>::drop`), attributed to
    the innermost user frame. `after` = how many real (non-drop-flag)
    branch events of that frame precede it: the lowering must drop the
    same Box at the same point between branches. -/
structure CertDrop where
  after : Nat
  ty : String := ""       -- Miri's `Box<T>` type text, for messages
  descr : String := ""
deriving Repr, Inhabited

/-- The active variant of an enum inside a call argument, as Miri's
    fn-entry retags walked it (formal-urchin's Miri fork logs it after the
    arguments are passed): argument local `arg` (1-based), field path
    `path` (field indices; inside an enum, of its active variant). A lookup
    table, not an ordered event: the lowering asks for the enums it
    retags, and CHECKS each answer when the program runs. -/
structure CertVariant where
  arg : Nat
  path : List Nat
  variant : Nat
  ty : String := ""
deriving Repr, Inhabited

structure CertFrame where
  fn : String
  events : Array CertEvent
  drops : Array CertDrop := #[]
  variants : Array CertVariant := #[]
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
    let evsJ := (getK fj "events").map asArr |>.getD []
    -- drop events are matched separately (`consumeDrop`), each positioned
    -- by the real branch events before it
    let mut events : Array CertEvent := #[]
    let mut drops : Array CertDrop := #[]
    for ej in evsJ do
      if (getK ej "k" >>= asStr) == some "drop" then
        drops := drops.push { after := (events.filter (!·.dropFlag)).size,
                              ty := (getK ej "ty" >>= asStr).getD "",
                              descr := (getK ej "descr" >>= asStr).getD "" }
      else
        events := events.push (← parseCertEvent ej)
    let varsJ := (getK fj "variants").map asArr |>.getD []
    let variants ← varsJ.toArray.mapM fun vj => do
      let some arg := getK vj "arg" >>= asNat | .error "certificate: variant without arg"
      let some v := getK vj "variant" >>= asNat | .error "certificate: variant without variant"
      let path := ((getK vj "path").map asArr |>.getD []).filterMap asNat
      pure ({ arg, path, variant := v, ty := (getK vj "ty" >>= asStr).getD "" } : CertVariant)
    pure ({ fn, events, drops, variants } : CertFrame)
  return { outcome, frames := frames.toArray }

/-- What the lowering did with a certificate, for the harness report. -/
structure CertStats where
  used : Bool := false
  checked : Nat := 0   -- T1 cross-checks + T2 runtime checks
  runtime : Nat := 0   -- of those, the T2 ones: checks the PROGRAM performs
  pinned : Nat := 0    -- arms followed on Miri's word alone: 0 since `binOp`
deriving Repr, Inhabited

/-- A cursor over the certificate: which frame instance is next to open,
    and for each open frame (innermost first) how many events it has
    consumed. -/
structure CertCursor where
  cert : Cert
  nextFrame : Nat := 0
  stack : List (Nat × Nat) := []   -- (frame index, next event index)
  dropsDone : List Nat := []        -- per open frame (innermost first): drops consumed
  -- match Box drops against Miri's: on once the lowering models Box drop
  -- glue (until then it emits no drops, and drop events are ignored)
  checkDrops : Bool := false
  checked : Nat := 0   -- T1 cross-checks + T2 runtime checks emitted
  runtime : Nat := 0   -- of those, the T2 ones (emitted check statements)
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
        .ok { c with nextFrame := c.nextFrame + 1, stack := (c.nextFrame, 0) :: c.stack,
                     dropsDone := 0 :: c.dropsDone }

/-- Remaining non-drop-flag events of the innermost open frame. -/
def remaining (c : CertCursor) : Nat :=
  match c.stack with
  | (fi, ei) :: _ =>
      match c.cert.frames[fi]? with
      | some fr => (fr.events.toList.drop ei).filter (fun e => !e.dropFlag) |>.length
      | none => 0
  | [] => 0

/-- Real branch events of the innermost frame consumed so far. -/
def realConsumed (c : CertCursor) : Nat :=
  match c.stack with
  | (fi, ei) :: _ =>
      match c.cert.frames[fi]? with
      | some fr => ((fr.events.toList.take ei).filter (!·.dropFlag)).length
      | none => 0
  | [] => 0

/-- The innermost frame's next unconsumed Miri drop, if any. -/
def nextDrop? (c : CertCursor) : Option CertDrop :=
  match c.stack, c.dropsDone with
  | (fi, _) :: _, d :: _ => c.cert.frames[fi]? >>= (·.drops[d]?)
  | _, _ => none

/-- Nothing of the certificate is left: no later frame, and every open
    frame has consumed all its real branch events and all its drops. For a
    UB/panic certificate this is the end of Miri's prefix. -/
def allConsumed (c : CertCursor) : Bool :=
  c.nextFrame ≥ c.cert.frames.size &&
  (c.stack.zip c.dropsDone).all fun ((fi, ei), d) =>
    match c.cert.frames[fi]? with
    | some fr => (fr.events.toList.drop ei).all (·.dropFlag) && d ≥ fr.drops.size
    | none => true

/-- With `checkDrops`: a Miri drop that should already have happened (it
    precedes the branch about to be taken, or the end of the frame or of
    the UB prefix) but the lowering has not emitted. -/
def missedDrop? (c : CertCursor) (fn : String) : Option String :=
  if !c.checkDrops then none else
  match c.nextDrop? with
  | some dr =>
      if dr.after ≤ c.realConsumed then
        some s!"certificate: Miri dropped a {dr.ty} in {fn} after {dr.after} branches; the lowering did not drop it there"
      else none
  | none => none

/-- The lowering drops a Box here: with `checkDrops`, it must be Miri's
    next drop in this frame, at the same point between branches. -/
def consumeDrop (c : CertCursor) (fn : String) : Except String CertCursor :=
  if !c.checkDrops then .ok c else
  match c.stack, c.dropsDone with
  | _ :: _, d :: ds =>
      match c.nextDrop? with
      | none => .error s!"certificate: the lowering drops a Box in {fn} that Miri did not drop"
      | some dr =>
          if dr.after != c.realConsumed then
            .error s!"certificate: the lowering drops a Box in {fn} after {c.realConsumed} branches; Miri's next drop ({dr.ty}) came after {dr.after}"
          else .ok { c with dropsDone := (d + 1) :: ds }
  | _, _ => .error s!"certificate: drop in {fn} with no open frame"

/-- Leave the innermost frame; every real event must have been consumed
    (and, with `checkDrops`, every Miri drop). -/
def closeFrame (c : CertCursor) (fn : String) : Except String CertCursor :=
  match c.stack with
  | [] => .error s!"certificate: closing {fn} with no open frame"
  | _ :: rest =>
      let k := c.remaining
      if k > 0 then
        .error s!"certificate: frame for {fn} has {k} unconsumed events (lowering took fewer branches than Miri)"
      else match c.missedDrop? fn with
        | some msg => .error msg
        | none => .ok { c with stack := rest, dropsDone := c.dropsDone.drop 1 }

/-- The recorded variant of the enum at field path `path` of argument
    `arg` of the innermost open frame (`CertVariant`), if Miri logged it. -/
def variantOf? (c : CertCursor) (arg : Nat) (path : List Nat) : Option Nat :=
  match c.stack with
  | (fi, _) :: _ =>
      (c.cert.frames[fi]? >>= fun fr =>
        fr.variants.find? (fun v => v.arg == arg && v.path == path)).map (·.variant)
  | [] => none

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
