import conformance.ullbc_ast

/-!
ULLBC → flat statement list, in the obseq3-expressible fragment.

Passes (fused into one walk):
1. **Inline** all calls in `main` (callee locals renumbered into one global
   local space; recursion/indirect calls rejected).
2. **Linearize**: follow `goto`/call-target edges from bb0; a revisited
   block means a loop → unsupported. Unwind edges are never followed.
3. **Drop** StorageLive/Dead, Borrowck/FakeRead, Nop, PlaceMention, and
   unit-aggregate assignments (no memory access in Miri either).
4. **Desugar** non-empty tuple aggregates into per-field assignments.
5. **Seam retags**: reference-typed arguments and return values are
   re-tagged at inline seams (`arg := &mut *callerPtr`), mirroring Miri's
   Retag-on-function-entry/exit. Raw-typed args are copied untagged.

Any construct outside the fragment yields `.error "unsupported: …"`,
which the harness reports as the test's unsupported-reason.
-/

namespace conformance

/-- A lowered program: one global local space, straight-line statements.
    `pushProt`/`popProt` bracket an inlined call's protector frame. -/
inductive LStmt
| assign (dst : UPlace) (rv : URvalue) (line : Nat)
| pushProt (line : Nat)
| popProt (line : Nat)
deriving Repr, BEq, Inhabited

def LStmt.line : LStmt → Nat
  | .assign _ _ l => l
  | .pushProt l => l
  | .popProt l => l

structure LProg where
  locals : List UTy
  stmts : List LStmt
deriving Repr, Inhabited

structure LowerSt where
  locals : List UTy
  out : List LStmt   -- reversed

def rebasePlace (off : Nat) (p : UPlace) : UPlace :=
  match p.root with
  | .local n => { p with root := .local (n + off) }
  | .global _ => p

def rebaseOperand (off : Nat) : UOperand → UOperand
  | .copy p => .copy (rebasePlace off p)
  | .move p => .move (rebasePlace off p)
  | op => op

def rebaseRvalue (off : Nat) : URvalue → URvalue
  | .use op => .use (rebaseOperand off op)
  | .ref kind prot p => .ref kind prot (rebasePlace off p)
  | .aggregate ops => .aggregate (ops.map (rebaseOperand off))
  | .uninit => .uninit
  | .unsupported d => .unsupported d

/-- The pointee place of a pointer-holding place. -/
def pointee (p : UPlace) : UPlace :=
  { p with projs := p.projs ++ [.deref] }

def checkOperand (line : Nat) : UOperand → Except String Unit
  | .unsupported d => .error s!"unsupported: {d} (line {line})"
  | _ => .ok ()

/-- Append one lowered assignment, desugaring aggregates and rejecting
    unsupported payloads. Places/rvalues must already be rebased. -/
def emitAssign (st : LowerSt) (line : Nat) (dst : UPlace) (rv : URvalue) :
    Except String LowerSt := do
  match rv with
  | .unsupported d => .error s!"unsupported: {d} (line {line})"
  | .use .constUnit =>
      return st  -- unit value: no memory access
  | .use op => do
      checkOperand line op
      return { st with out := .assign dst rv line :: st.out }
  | .ref _ _ _ | .uninit =>
      return { st with out := .assign dst rv line :: st.out }
  | .aggregate [] =>
      return st  -- unit value: no memory access
  | .aggregate ops => do
      let mut st := st
      for h : i in [0:ops.length] do
        let op := ops[i]
        checkOperand line op
        let fdst := { dst with projs := dst.projs ++ [.field i] }
        st := { st with out := .assign fdst (.use op) line :: st.out }
      return st

/-- Retag kind for a reference-typed seam binding. -/
def seamRefKind : UTy → Option URefKind
  | .ref true _ => some .mut
  | .ref false _ => some .shared
  | _ => none

def isUnitTy : UTy → Bool
  | .tup [] => true
  | _ => false

/-- Does this type contain a reference (transitively through tuples)?
    Raw pointers don't count — they are not retagged at seams. -/
partial def containsRef : UTy → Bool
  | .ref _ _ => true
  | .tup tys => tys.any containsRef
  | _ => false

/-- Copy `src` into `dst` at an inline seam, retagging every reference
    (including refs inside tuples, mirroring Miri's field retagging).
    Non-ref components are plain copies. `prot` marks the retags as
    protected (fn-entry retags: true for arguments, false for returns). -/
partial def emitSeamCopy (st : LowerSt) (line : Nat) (prot : Bool) (dst : UPlace)
    (ty : UTy) (src : UPlace) : Except String LowerSt := do
  match ty with
  | .ref mutbl _ =>
      emitAssign st line dst (.ref (if mutbl then .mut else .shared) prot (pointee src))
  | .tup tys => do
      let mut st := st
      for h : i in [0:tys.length] do
        let fdst := { dst with projs := dst.projs ++ [.field i] }
        let fsrc := { src with projs := src.projs ++ [.field i] }
        st ← emitSeamCopy st line prot fdst tys[i] fsrc
      return st
  | _ => emitAssign st line dst (.use (.copy src))

/-- Bind one value into a fresh local at an inline seam, retagging if the
    type contains references. -/
def emitSeamBind (st : LowerSt) (line : Nat) (prot : Bool) (dstLocal : UPlace)
    (ty : UTy) (op : UOperand) : Except String LowerSt := do
  if containsRef ty then
    match op with
    | .copy p | .move p => emitSeamCopy st line prot dstLocal ty p
    | _ => .error s!"unsupported: reference-typed argument is not a place (line {line})"
  else
    emitAssign st line dstLocal (.use op)

mutual

/-- Walk fn body blocks from `bb`, appending lowered statements.
    Returns the state at the fn's `Return`. -/
partial def walkBlock (crate : UCrate) (depth : Nat) (st : LowerSt)
    (f : UFun) (offset : Nat) (bb : Nat) (visited : List Nat) :
    Except String LowerSt := do
  if visited.contains bb then
    .error s!"unsupported: control-flow loop in {f.name}"
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
          st ← emitAssign st s.line (rebasePlace offset dst) (rebaseRvalue offset rv)
    match blk.term with
    | .ret => return st
    | .goto t => walkBlock crate depth st f offset t (bb :: visited)
    | .unwindResume => .error s!"unsupported: reached unwind path in {f.name}"
    | .abort => .error s!"unsupported: reached abort in {f.name}"
    | .unsupported d => .error s!"unsupported: {d} (line {blk.termLine})"
    | .call funIdx args dest target => do
        let args := args.map (rebaseOperand offset)
        let dest := rebasePlace offset dest
        let st' ← inlineCall crate depth st funIdx args dest blk.termLine
        walkBlock crate depth st' f offset target (bb :: visited)

/-- Inline a call: extend the local space with the callee's locals, bind
    arguments (with seam retags), walk the body, bind the return value. -/
partial def inlineCall (crate : UCrate) (depth : Nat) (st : LowerSt)
    (funIdx : Nat) (args : List UOperand) (dest : UPlace) (line : Nat) :
    Except String LowerSt := do
  if depth == 0 then
    .error "unsupported: call inlining depth exceeded (recursion?)"
  else
  match crate.funs.find? (·.defId == funIdx) with
  | none => .error s!"unsupported: call to unknown function id {funIdx} (line {line})"
  | some f =>
    if !f.hasBody then
      .error s!"unsupported: call to bodyless function {f.name} (line {line})"
    else if args.length != f.argCount then
      .error s!"unsupported: arg count mismatch calling {f.name}"
    else do
      let offset := st.locals.length
      let mut st := { st with locals := st.locals ++ f.locals }
      -- enter the call's protector frame
      st := { st with out := .pushProt line :: st.out }
      -- bind args into callee arg locals (indices 1..argCount), with
      -- protected fn-entry retags for reference-typed components
      for h : i in [0:args.length] do
        let argLocal : UPlace := { root := .local (offset + 1 + i), projs := [] }
        let ty := f.locals[1 + i]? |>.getD (.unsupported "missing arg local")
        st ← emitSeamBind st line true argLocal ty args[i]
      -- walk the body
      st ← walkBlock crate (depth - 1) st f offset 0 []
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
  | .ref kind prot p => do return .ref kind prot (← resolveGlobalRoot gmap p)
  | .aggregate ops => do return .aggregate (← ops.mapM (resolveGlobalsOp gmap))
  | rv => .ok rv

def resolveGlobalsStmt (gmap : List (Nat × Nat)) : LStmt → Except String LStmt
  | .assign dst rv line => do
      return .assign (← resolveGlobalRoot gmap dst) (← resolveGlobalsRv gmap rv) line
  | s => .ok s

/-- Lower a crate's `main` into a flat program.

    Statics hoisting: every global becomes a fresh local appended after
    main's locals, materialized `uninit` at pc 0; `Global` place roots are
    rewritten to those locals. Initializer bodies are NOT run — hoisted
    statics start undef, which is fine for SB purposes as long as the
    program writes them before any value-dependent use (documented
    divergence: real statics have interned, initialized allocations). -/
def lowerCrate (crate : UCrate) : Except String LProg := do
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
      let st0 : LowerSt :=
        { locals := main.locals ++ crate.globals.map (·.ty), out := hoistInit }
      let st ← walkBlock crate 8 st0 main 0 0 []
      let stmts ← st.out.reverse.mapM (resolveGlobalsStmt gmap)
      return { locals := st.locals, stmts }

end conformance
