import conformance.stdlite
import conformance.certificate

/-!
ULLBC → flat statement list, in the obseq3-expressible fragment.

Passes (fused into one walk):
1. **Inline** all calls in `main` (callee locals renumbered into one global
   local space; recursion/indirect calls rejected).
2. **Linearize**: follow `goto`/call-target edges from bb0; a revisited
   block means a loop → unsupported. Unwind edges are never followed.
3. **Drop** StorageLive/Dead, Borrowck/FakeRead, Nop, PlaceMention.
   Unit-aggregate assignments are kept as access-free `uninit` inits:
   no memory access in Miri either, but the ZST destination still gets
   allocated, so it can be borrowed.
4. **Desugar** non-empty tuple aggregates into per-field assignments.
5. **Seam retags**: reference-typed arguments and return values are
   re-tagged at inline seams (`arg := &mut *callerPtr`), mirroring Miri's
   Retag-on-function-entry/exit. Raw-typed args are copied untagged.

Any construct outside the fragment yields `.error "unsupported: …"`,
which the harness reports as the test's unsupported-reason.

Files: `emit.lean` (the state and the statement emitters, incl. seam
retags), `stdlite.lean` (the std shims: one handler per modelled std
path, in `stdlite.table`), and this file (certificate checks and the
block walker that inlines calls and dispatches bodyless ones to
`shimCall`).

## Coverage: what is and isn't interpreted, and why

The fragment is deliberately small: the suite's purpose is to score the
*Stacked Borrows rule set* against Miri, so it covers exactly the language
surface the corpus needs to exercise every SB mechanism (granting, pops,
protectors, retags, UnsafeCell masks, exposed provenance, dealloc, …).
Everything else is rejected — not because it is uninteresting, but because
it adds *language* complexity (control flow, drop glue, threads, …)
without exercising any *additional* SB rule. The conformance claim in
`conformance/README.md` spells this out: remaining unsupported tests use
unimplemented language/std features, not un-modeled SB rules.

Covered (interpreted):
- straight-line assignments: copies/moves, `ref` retags (all kinds,
  with seam protection), aggregates (tuple desugaring + enum
  discriminant/payload writes), `uninit`;
- pointer/provenance ops: `exposeAddr`/`fromExposed`, constant
  `ptrOffset`, runtime-length `refSlice` retags;
- slice metadata: `<[T]>::len` and `_p.PtrMetadata` become mirlite's
  `sliceLen` — the extent the fat pointer carries, in elements
  (2026-09-24), so a bounds check on a runtime length is a real check;
- range SUB-SLICING (`&s[lo..hi]`, `&a[..]`): the std `Index`/`array`
  chain is shimmed into the two retags it performs — the receiver's,
  then the mint over the narrowed range — with mirlite's `subSlice`
  (pure pointer arithmetic) between them (2026-09-25);
- heap: `alloc`/`dealloc` via the std shims (`Box::new`, `alloc::alloc`,
  `Layout::*`), incl. `Box` unique retags at seams;
- interior mutability: `UnsafeCell`/`Cell`/`RefCell` shims with freeze
  masks (RefCell flag elided — SB-irrelevant);
- calls: inlined up to depth 8, with fn-entry/exit seam retags;
  statically-resolved indirect calls;
- statics: hoisted to locals, materialized `uninit` (initializers NOT
  run — documented divergence);
- arithmetic: folded when both operands are known (the static value is
  what indices, offsets and sizes need), otherwise EMITTED as mirlite's
  `binOp` on two word places (2026-09-24); statically-true asserts
  (bounds checks);
- **certificate-guided control flow** (2026-09-23, `certificate.lean`):
  with a `<name>.cert.json` recording Miri's branch outcomes, `switch`
  terminators follow the recorded arm (loops unroll), asserts follow
  the recorded outcome, and each is either cross-checked against the
  folded value (T1) or CHECKED AT RUNTIME (T2, with
  `uninit`/`assignIf`/`copy`) against the word the program computed —
  the same word Miri's own `switchInt`/`assert` read. Since `binOp`
  landed there is no third tier: every recorded branch is checked.

Not covered (rejected as `unsupported`), with the reason:
- **loops / `switchInt` / real branches WITHOUT a certificate** — the
  target has only forward-only `SkipIf`; general CFGs are language
  complexity, and no SB rule needs them;
- **unwind paths / `abort` / certified panic paths** — exception
  machinery, no SB content;
- **some run-time array indices** — mirlite has no array type (`[T; N]`
  is a tuple; N ≤ `maxArrayLen`). `ptr.add(i)`/`offset(i)`, slice data
  `(*s)[i]`, a local array `a[i]` and an array behind a pointer `(*p)[i]`
  all lower to the run-time `ptrOffsetBy` from the element-0 address
  (`addrOf` for a local, the pointer itself otherwise; no retag, as Miri's
  place projection). Not covered: an index after a field of a
  dereference, `(*p).f[i]`, and an index inside an operation's operand;
- **recursion & deep (>8) call chains, unknown/bodyless callees,
  unresolved indirect calls** — inlining must terminate statically;
- **drop glue, closures, containers, threads, unions** (as they arise in
  the corpus) — std/language machinery beyond the fragment; the SB rules
  they would exercise are already witnessed by simpler tests;
- **nested references in enum payloads** — would need per-variant
  recursive retag emission; not exercised by the corpus;
- **fn pointers stored into projections** — fn-pointer tracking is a
  flat local↦defId map, sufficient for the corpus's call patterns.

The consolidated inventory of blockers/approximations lives in
`notes/loose-ends/parked.md`; per-test reasons in `conformance/manifest.json`.
-/

namespace conformance

/-! ## Certificate checks, from existing statements only

Every recorded branch outcome the lowering cannot fold is CHECKED at
runtime with `uninit`/`assignIf`/
`copy` alone: "UB unless `d == v`" is `bad := uninit; assignIf d v (bad :=
0); tmp := copy bad` — the copy reads an uninitialised cell exactly when
the pin is wrong. The check statements carry a SENTINEL line so the
harness reports a failure as "certificate rejected", not as a program
verdict. -/

/-- UB unless `discr ∉ vs` (the `otherwise` arm of a switch). -/
def emitCheckNotIn (st : LowerSt) (line : Nat) (discr : UPlace) (vs : List Nat) : LowerSt :=
  -- an `otherwise` arm with NO cases to exclude is vacuous: nothing to
  -- check at runtime, and nothing the certificate could get wrong
  if vs.isEmpty then certBump st 1 else
  certBump (pushOut st (.check discr vs false (certLineBase + line))) 1 1

/-- Take the next recorded event. `none` with `halted` set means the
    certificate's UB/panic prefix ended here. -/
def consumeEvent (st : LowerSt) (line : Nat) : Except String (Option CertEvent × LowerSt) :=
  match st.cert with
  | none => .ok (none, st)
  | some c =>
      -- a Box Miri dropped before this branch (or before the end of its
      -- UB prefix) must already have been dropped by the lowering
      if let some msg := c.missedDrop? s!"the frame at line {line}" then .error msg else
      match c.nextEvent with
      | some (e, c') => .ok (some e, { st with cert := some c' })
      | none =>
          match c.cert.outcome with
          | .ok => .error s!"certificate exhausted at line {line}: the lowering needs more branch events than Miri recorded"
          | _ => .ok (none, emitPoison st line)

/-- The block a recorded switch arm selects among charon's targets. -/
def switchTarget (cases : List (Nat × Nat)) (otherwise : Nat) : Option Nat → Nat
  | some v => (cases.lookup v).getD otherwise
  | none => otherwise

mutual

/-- Walk fn body blocks from `bb`, appending lowered statements.
    Returns the state at the fn's `Return`. -/
partial def walkBlock (crate : UCrate) (depth : Nat) (st : LowerSt)
    (f : UFun) (offset : Nat) (bb : Nat) (visited : List Nat) :
    Except String LowerSt := do
  if st.halted then return st else
  -- without a certificate a revisited block is a loop and the fragment
  -- is straight-line only; with one, loops UNROLL along the recorded
  -- branches, and only a branch-free cycle (which Miri would not have
  -- finished either) is rejected, by a visit budget
  if st.cert.isNone && visited.contains bb then
    .error s!"unsupported: control-flow loop in {f.name}"
  else if st.cert.isSome &&
      visited.length > ((st.cert.map (·.remaining)).getD 0 + 2) * (f.blocks.length + 1) then
    .error s!"unsupported: loop without a certified branch in {f.name}"
  else
  match f.blocks[bb]? with
  | none => .error s!"unsupported: dangling block bb{bb} in {f.name}"
  | some blk => do
    let mut st := st
    for s in blk.stmts do
      match s.kind with
      | .storage => pure ()
      | .unsupported d => throw s!"unsupported: {d} (line {s.line})"
      | .assign dst rv =>
          let dst := rebasePlace offset dst
          let rv := rebaseRvalue offset rv
          st ← emitAssign st s.line dst rv
          st := markInit (rv.movedPlaces.foldl markMoved st) dst
    let line := blk.termLine
    match blk.term with
    | .ret => return st
    | .goto t => walkBlock crate depth st f offset t (bb :: visited)
    | .drop p t => do
        st ← emitDropGlue st line (rebasePlace offset p)
        walkBlock crate depth st f offset t (bb :: visited)
    | .assert cond expected t kind =>
        let c := rebaseOperand offset cond
        let expectedW : Nat := if expected then 1 else 0
        match st.cert with
        | none =>
            -- no certificate: asserts must be statically satisfied
            match constOf st c with
            | some v =>
                if (v != 0) == expected then
                  walkBlock crate depth st f offset t (bb :: visited)
                else
                  .error s!"unsupported: statically failing assert (line {line})"
            | none => .error s!"unsupported: dynamic assert condition (line {line})"
        | some _ => do
            let (ev?, stE) ← consumeEvent st line
            st := stE
            match ev? with
            | none => return st   -- the certificate's UB prefix ended here
            | some ev =>
              match ev.kind with
              | .switch _ =>
                  .error s!"certificate: expected an assert ({kind}) at line {line}, Miri recorded a switch — event order mismatch ({ev.descr})"
              | .assert success =>
                if !success then
                  .error s!"unsupported: certified panic path ({kind}) at line {line}"
                else
                  match constOf st c with
                  | some v =>
                      -- T1: the lowering knows the condition; Miri must agree
                      if (v != 0) == expected then
                        walkBlock crate depth (certBump st 1) f offset t (bb :: visited)
                      else
                        .error s!"certificate disagrees with lowering at line {line}: assert ({kind}) condition folds to {v}, Miri passed it"
                  | none =>
                      match operandPlace? c with
                      | none => .error s!"certificate: assert condition is not a place (line {line})"
                      | some cp =>
                          -- T2: the condition is a runtime word — the same
                          -- word Miri's assert read — so CHECK it
                          walkBlock crate depth (emitCheckEq st line cp expectedW) f offset t (bb :: visited)
    | .switch discr cases otherwise =>
        let d := rebaseOperand offset discr
        match st.cert with
        | none => .error s!"unsupported: dynamic branch without a certificate (line {line})"
        | some _ => do
            let (ev?, stE) ← consumeEvent st line
            st := stE
            match ev? with
            | none => return st
            | some ev =>
              match ev.kind with
              | .assert _ =>
                  .error s!"certificate: expected a switch at line {line}, Miri recorded an assert — event order mismatch ({ev.descr})"
              | .switch arm =>
                let target := switchTarget cases otherwise arm
                match constOf st d with
                | some v =>
                    -- T1: cross-check the folded discriminant against Miri's arm
                    let mine := switchTarget cases otherwise (if v < 0 then none else some v.toNat)
                    if mine == target then
                      walkBlock crate depth (certBump st 1) f offset target (bb :: visited)
                    else
                      .error s!"certificate disagrees with lowering at line {line}: discriminant folds to {v}, Miri took arm {reprStr arm}"
                | none =>
                    match operandPlace? d with
                    | none => .error s!"certificate: switch on a non-place operand (line {line})"
                    | some dp =>
                      -- T2: the discriminant is a runtime word — the word
                      -- Miri's own `switchInt` read — so CHECK Miri's arm
                      -- against it before following the branch
                      st := match arm with
                        | some v => emitCheckEq st line dp v
                        | none => emitCheckNotIn st line dp (cases.map (·.1))
                      walkBlock crate depth st f offset target (bb :: visited)
    -- unwinding and aborts are exception machinery with no SB content
    | .unwindResume => .error s!"unsupported: reached unwind path in {f.name}"
    | .abort => .error s!"unsupported: reached abort in {f.name}"
    | .unsupported d => .error s!"unsupported: {d} (line {blk.termLine})"
    | .call funIdx args dest target => do
        let args := args.map (rebaseOperand offset)
        let dest := rebasePlace offset dest
        let st' ←
          match shimCall crate funIdx with
          | some shim => shim st args dest blk.termLine
          | none =>
              let (stS, argsS) := materialiseStrArgs st blk.termLine args
              inlineCall crate depth stS funIdx argsS dest blk.termLine
        -- moved arguments now belong to the callee (which drops them);
        -- the destination is written
        let st' := markInit (markMovedOps st' args) dest
        walkBlock crate depth st' f offset target (bb :: visited)
    | .callDyn fp args dest target => do
        -- indirect call: resolve the statically-tracked fn pointer
        let fp := rebasePlace offset fp
        let args := args.map (rebaseOperand offset)
        let dest := rebasePlace offset dest
        match fp with
        | { root := .local n, projs := [], .. } =>
            match st.fnPtrs.lookup n with
            | some funIdx => do
                let st' ←
                  match shimCall crate funIdx with
                  | some shim => shim st args dest blk.termLine
                  | none =>
                      let (stS, argsS) := materialiseStrArgs st blk.termLine args
                      inlineCall crate depth stS funIdx argsS dest blk.termLine
                let st' := markInit (markMovedOps st' args) dest
                walkBlock crate depth st' f offset target (bb :: visited)
            | none => .error s!"unsupported: indirect call with unknown target (line {blk.termLine})"
        | _ => .error s!"unsupported: indirect call through a projection (line {blk.termLine})"

/-- Inline a call: extend the local space with the callee's locals, bind
    arguments (with seam retags), walk the body, bind the return value. -/
partial def inlineCall (crate : UCrate) (depth : Nat) (st : LowerSt)
    (funIdx : Nat) (args : List UOperand) (dest : UPlace) (line : Nat) :
    Except String LowerSt := do
  -- bounded depth guarantees static termination of inlining
  -- (recursion is rejected, not modeled)
  if depth == 0 then
    .error "unsupported: call inlining depth exceeded (recursion?)"
  else
  match crate.funs.find? (·.defId == funIdx) with
  | none => .error s!"unsupported: call to unknown function id {funIdx} (line {line})"
  | some f =>
    if !f.hasBody then
      .error s!"unsupported: call to bodyless function {String.intercalate "::" f.path} (line {line})"
    else if args.length != f.argCount then
      .error s!"unsupported: arg count mismatch calling {f.name}"
    else do
      let offset := st.locals.length
      let mut st := { st with locals := st.locals ++ f.locals }
      -- enter the call's protector frame
      st := { st with out := .pushProt line :: st.out }
      -- open the callee's certificate frame (shims never do: they are
      -- std frames on Miri's side, which the extractor drops) BEFORE the
      -- arguments: the enum variants Miri's fn-entry retags walked are
      -- recorded in it (`CertVariant`)
      match st.cert with
      | some c =>
          let c ← c.openFrame f.name
          st := { st with cert := some c }
      | none => pure ()
      -- bind args into callee arg locals (indices 1..argCount), with
      -- protected fn-entry retags for reference-typed components
      for h : i in [0:args.length] do
        let argLocal : UPlace := { root := .local (offset + 1 + i), projs := [] }
        let ty := f.locals[1 + i]? |>.getD (.unsupported "missing arg local")
        st ← emitSeamBind st line true argLocal ty args[i] (some (1 + i))
      -- the RETURN PLACE is passed in place too (Miri: "Protect return
      -- place for in-place return value passing"): the caller's
      -- destination is deinit'd and protected for the call, and receives
      -- the value after the frame pops. A unit destination has nothing to
      -- protect. `dest := uninit` first also roots an as-yet-unbound
      -- destination, which Miri, having no lazy allocation, never sees.
      let retTy := f.locals[0]? |>.getD (.unsupported "missing return local")
      if !(isUnitTy retTy) then
        st ← emitAssign st line dest .uninit
        st ← protectInPlace st line dest retTy
      -- walk the body
      st ← walkBlock crate (depth - 1) st f offset 0 []
      if st.halted then return st
      match st.cert with
      | some c =>
          let c ← c.closeFrame f.name
          st := { st with cert := some c }
      | none => pure ()
      -- leave the call: protectors end before the return value flows back
      st := { st with out := .popProt line :: st.out }
      -- bind the return value (callee local 0) into dest
      let retTy := f.locals[0]? |>.getD (.unsupported "missing return local")
      if isUnitTy retTy then
        return st
      else
        let retLocal : UPlace := { root := .local offset, projs := [] }
        if containsRef retTy then
          emitSeamCopy st line false dest retTy retLocal
        else
          emitAssign st line dest (.use (.copy retLocal))

end

/-- Rewrite hoisted-global place roots to their assigned locals. -/
def resolveGlobalRoot (gmap : List (Nat × Nat)) (p : UPlace) : Except String UPlace :=
  match p.root with
  | .local _ => .ok p
  | .global gid =>
      match gmap.lookup gid with
      | some idx => .ok { p with root := .local idx }
      | none => .error s!"unsupported: reference to unhoisted global {gid}"

def resolveGlobalsOp (gmap : List (Nat × Nat)) : UOperand → Except String UOperand
  | .copy p => do return .copy (← resolveGlobalRoot gmap p)
  | .move p => do return .move (← resolveGlobalRoot gmap p)
  | op => .ok op

def resolveGlobalsRv (gmap : List (Nat × Nat)) : URvalue → Except String URvalue
  | .use op => do return .use (← resolveGlobalsOp gmap op)
  | .move p => do return .move (← resolveGlobalRoot gmap p)
  | .ref kind prot p => do return .ref kind prot (← resolveGlobalRoot gmap p)
  | .aggregate v ops => do return .aggregate v (← ops.mapM (resolveGlobalsOp gmap))
  | .exposeAddr p => do return .exposeAddr (← resolveGlobalRoot gmap p)
  | .addr p => do return .addr (← resolveGlobalRoot gmap p)
  | .fromExposed p => do return .fromExposed (← resolveGlobalRoot gmap p)
  | .ptrOffset p d ib => do return .ptrOffset (← resolveGlobalRoot gmap p) d ib
  | .ptrOffsetBy p i ib => do
      return .ptrOffsetBy (← resolveGlobalRoot gmap p) (← resolveGlobalRoot gmap i) ib
  | .addrOf p => do return .addrOf (← resolveGlobalRoot gmap p)
  | .rawField p steps => do return .rawField (← resolveGlobalRoot gmap p) steps
  | .refSlice kind prot p => do return .refSlice kind prot (← resolveGlobalRoot gmap p)
  | .discriminant p => do return .discriminant (← resolveGlobalRoot gmap p)
  | .sliceLen p => do return .sliceLen (← resolveGlobalRoot gmap p)
  | .subSlice p lo hi => do
      return .subSlice (← resolveGlobalRoot gmap p) (← resolveGlobalsOp gmap lo)
        (← resolveGlobalsOp gmap hi)
  | .binOp op t a b => do
      return .binOp op t (← resolveGlobalsOp gmap a) (← resolveGlobalsOp gmap b)
  | rv => .ok rv

def resolveGlobalsStmt (gmap : List (Nat × Nat)) : LStmt → Except String LStmt
  | .assign dst rv line => do
      return .assign (← resolveGlobalRoot gmap dst) (← resolveGlobalsRv gmap rv) line
  | .assignIf discr v dst rv line => do
      return .assignIf (← resolveGlobalRoot gmap discr) v
        (← resolveGlobalRoot gmap dst) (← resolveGlobalsRv gmap rv) line
  | .alloc dst sz line => do
      let sz ← match sz with
        | some op => pure (some (← resolveGlobalsOp gmap op))
        | none => pure none
      return .alloc (← resolveGlobalRoot gmap dst) sz line
  | .check discr vs m line => do
      return .check (← resolveGlobalRoot gmap discr) vs m line
  | .dealloc p line => do
      return .dealloc (← resolveGlobalRoot gmap p) line
  | s => .ok s

/-- Lower a crate's `main` into a flat program.

    Globals hoisting: every global becomes a fresh local appended after
    main's locals, materialized `uninit` at pc 0 and then given its value
    by inlining its initializer (Charon's `value` call) before `main`
    runs, outside any certificate frame (Miri evaluates consts and
    statics before the program starts, so it records no frames for
    them). `Global` place roots are rewritten to those locals. A const
    whose initializer does not lower is unsupported (it is only ever
    read); a static whose initializer does not lower keeps starting
    `uninit` (documented divergence: the program must write it before a
    value-dependent use). -/
def lowerCrate (crate : UCrate) (cert? : Option Cert := none) : Except String LProg := do
  match crate.funs.find? (·.name == "main") with
  | none => .error "no main function in crate"
  | some main =>
    if !main.hasBody then .error "main has no body"
    else do
      let base := main.locals.length
      let gmap := crate.globals.zipIdx.map (fun (g, i) => (g.gid, base + i))
      let hoistInit : List LStmt :=
        (crate.globals.zipIdx.map (fun (_, i) =>
          LStmt.assign { root := .local (base + i), projs := [] } .uninit 0)).reverse
      -- with a certificate: two scratch words for the checks, and main's
      -- frame opened
      let nGlob := crate.globals.length
      let st0 : LowerSt ← match cert? with
        | none => pure { locals := main.locals ++ crate.globals.map (·.ty), out := hoistInit }
        | some cert => do
            let c ← ({ cert, checkDrops := true } : CertCursor).openFrame main.name
            pure { locals := main.locals ++ crate.globals.map (·.ty) ++ [.nat, .nat],
                   out := hoistInit, cert := some c,
                   certBad := base + nGlob, certTmp := base + nGlob + 1 }
      let st0 ← crate.globals.zipIdx.foldlM (fun st (g, i) => do
        match g.init with
        | none => pure st
        | some fid =>
          -- the call's return-place protection lands on a scratch local;
          -- the global itself gets one plain store, so its stack is just
          -- its base item, as for Miri's pre-evaluated allocation
          let g' : UPlace := { root := .local (base + i), projs := [], ty := g.ty }
          let tmp : UPlace := { root := .local st.locals.length, projs := [], ty := g.ty }
          let st1 := { st with locals := st.locals ++ [g.ty], cert := none }
          match inlineCall crate 8 st1 fid [] tmp 0 with
          | .ok st' => pure { pushOut st' (.assign g' (.use (.copy tmp)) 0) with cert := st.cert }
          | .error e =>
              if g.isStatic then pure st
              else throw s!"unsupported: initializer of const {g.name}: {e}") st0
      let st ← walkBlock crate 8 st0 main 0 0 []
      let st ← match st.cert with
        | some c => if st.halted then pure st else do
            let c ← c.closeFrame main.name
            pure { st with cert := some c }
        | none => pure st
      let stmts ← st.out.reverse.mapM (resolveGlobalsStmt gmap)
      let stats : CertStats := match st.cert with
        | some c => { used := true, checked := c.checked, runtime := c.runtime, pinned := c.pinned }
        | none => {}
      return { locals := st.locals, stmts, stats }

end conformance
