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

/-- A lowered program: one global local space, straight-line assigns. -/
structure LStmt where
  dst : UPlace
  rv : URvalue
  line : Nat
deriving Repr, BEq, Inhabited

structure LProg where
  locals : List UTy
  stmts : List LStmt
deriving Repr, Inhabited

structure LowerSt where
  locals : List UTy
  out : List LStmt   -- reversed

def rebasePlace (off : Nat) (p : UPlace) : UPlace :=
  { p with root := p.root + off }

def rebaseOperand (off : Nat) : UOperand → UOperand
  | .copy p => .copy (rebasePlace off p)
  | .move p => .move (rebasePlace off p)
  | op => op

def rebaseRvalue (off : Nat) : URvalue → URvalue
  | .use op => .use (rebaseOperand off op)
  | .ref kind p => .ref kind (rebasePlace off p)
  | .aggregate ops => .aggregate (ops.map (rebaseOperand off))
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
      return { st with out := { dst, rv, line } :: st.out }
  | .ref _ _ =>
      return { st with out := { dst, rv, line } :: st.out }
  | .aggregate [] =>
      return st  -- unit value: no memory access
  | .aggregate ops => do
      let mut st := st
      for h : i in [0:ops.length] do
        let op := ops[i]
        checkOperand line op
        let fdst := { dst with projs := dst.projs ++ [.field i] }
        st := { st with out := { dst := fdst, rv := .use op, line } :: st.out }
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
    Non-ref components are plain copies. -/
partial def emitSeamCopy (st : LowerSt) (line : Nat) (dst : UPlace) (ty : UTy)
    (src : UPlace) : Except String LowerSt := do
  match ty with
  | .ref mutbl _ =>
      emitAssign st line dst (.ref (if mutbl then .mut else .shared) (pointee src))
  | .tup tys => do
      let mut st := st
      for h : i in [0:tys.length] do
        let fdst := { dst with projs := dst.projs ++ [.field i] }
        let fsrc := { src with projs := src.projs ++ [.field i] }
        st ← emitSeamCopy st line fdst tys[i] fsrc
      return st
  | _ => emitAssign st line dst (.use (.copy src))

/-- Bind one value into a fresh local at an inline seam, retagging if the
    type contains references. -/
def emitSeamBind (st : LowerSt) (line : Nat) (dstLocal : UPlace) (ty : UTy)
    (op : UOperand) : Except String LowerSt := do
  if containsRef ty then
    match op with
    | .copy p | .move p => emitSeamCopy st line dstLocal ty p
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
      -- bind args into callee arg locals (indices 1..argCount)
      for h : i in [0:args.length] do
        let argLocal : UPlace := { root := offset + 1 + i, projs := [] }
        let ty := f.locals[1 + i]? |>.getD (.unsupported "missing arg local")
        st ← emitSeamBind st line argLocal ty args[i]
      -- walk the body
      st ← walkBlock crate (depth - 1) st f offset 0 []
      -- bind the return value (callee local 0) into dest
      let retTy := f.locals[0]? |>.getD (.unsupported "missing return local")
      if isUnitTy retTy then
        return st
      else
        let retLocal : UPlace := { root := offset, projs := [] }
        if containsRef retTy then
          emitSeamCopy st line dest retTy retLocal
        else
          emitAssign st line dest (.use (.copy retLocal))

end

/-- Lower a crate's `main` into a flat program. -/
def lowerCrate (crate : UCrate) : Except String LProg := do
  match crate.funs.find? (·.name == "main") with
  | none => .error "no main function in crate"
  | some main =>
    if !main.hasBody then .error "main has no body"
    else do
      let st ← walkBlock crate 8 { locals := main.locals, out := [] } main 0 0 []
      return { locals := st.locals, stmts := st.out.reverse }

end conformance
