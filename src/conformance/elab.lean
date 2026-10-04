import conformance.lowering
import obseq3.values

/-!
Elaborate a lowered untyped program (`LProg`) into obseq3's intrinsically
typed syntax: `(Γ : Ctx) × Prog Γ`. Type agreement is established with
`DecidableEq LayoutTy` and transported along the resulting equalities, so
runtime-parsed programs need no hand-written proofs.
-/

namespace conformance

open obseq3

/-- Merge enum variants' field layouts into one payload: every variant's
    fields must be a prefix of the longest variant's (Option-style). -/
def mergeVariantLayouts (variants : List (List LayoutTy)) :
    Except String (List LayoutTy) :=
  variants.foldlM
    (fun acc fields =>
      if acc.isPrefixOf fields then .ok fields
      else if fields.isPrefixOf acc then .ok acc
      else .error "unsupported: incompatible enum variant layouts")
    []

partial def toLayout : UTy → Except String LayoutTy
  | .nat => .ok .usize
  | .int t => .ok (.IntL t.toIntTy)
  | .ref _ inner => do return .PtrL (← toLayout inner)
  | .raw _ inner => do return .PtrL (← toLayout inner)
  | .tup tys => do return .TupL (← tys.mapM toLayout)
  | .structT tys _ => do return .TupL (← tys.mapM toLayout)
  | .cell inner => toLayout inner   -- interior-mutable wrapper is layout-transparent
  | .boxT inner => do return .PtrL (← toLayout inner)
  | .vecT elem => toLayout (vecHeader elem)
  | .slice _ _ elem => do return .PtrL (← toLayout elem)  -- one-cell fat value
  | .sliceData _ => .error "unsupported: unsized slice value position"
  | .enum variants => do
      let vls ← variants.mapM (·.mapM toLayout)
      -- the tag is an `isize`, the type MIR's `discriminant()` has for an
      -- enum without a `repr`
      return .TupL (.IntL ⟨64, true⟩ :: (← mergeVariantLayouts vls))
  | .unsupported d => .error s!"unsupported: type {d}"

def toRefKind : URefKind → obseq3.RefKind
  | .shared => .Shared
  | .mut => .Mut
  | .twoPhase => .TwoPhase
  | .rawMut => .Raw true
  | .rawConst => .Raw false
  | .boxMut => .BoxMut

def elabRoot (Γ : Ctx) : URoot → Except String ((τ : LayoutTy) × Place Γ τ)
  | .local n =>
      if h : n < Γ.length then
        .ok ⟨Γ.get ⟨n, h⟩, .local ⟨⟨n, h⟩, rfl⟩⟩
      else .error s!"local _{n} out of range"
  | .global gid => .error s!"global {gid} not hoisted by lowering"

def elabPlaceAux (Γ : Ctx) :
    (τ : LayoutTy) → Place Γ τ → List UProj →
    Except String ((σ : LayoutTy) × Place Γ σ)
  | τ, pl, [] => .ok ⟨τ, pl⟩
  | .PtrL inner, pl, .deref :: rest =>
      elabPlaceAux Γ inner (.deref pl) rest
  | _, _, .deref :: _ => .error "deref of non-pointer place"
  | .TupL tys, pl, .field i :: rest =>
      if h : i < tys.length then
        elabPlaceAux Γ (tys.get ⟨i, h⟩) (.proj pl (.field ⟨i, h⟩ .nil)) rest
      else .error s!"field index {i} out of range"
  | _, _, .field _ :: _ => .error "field projection on non-tuple place"
  | _, _, .index _ :: _ => .error "array index not resolved by lowering"
  | _, _, .ptrMetadata :: _ => .error "pointer metadata not turned into `sliceLen` by lowering"

def elabPlace (Γ : Ctx) (p : UPlace) : Except String ((τ : LayoutTy) × Place Γ τ) := do
  let ⟨τ, pl⟩ ← elabRoot Γ p.root
  elabPlaceAux Γ τ pl p.projs

/-- Elaborate a place that must be integer-typed, at any width
    (discriminants, allocation sizes, operands). -/
def elabIntPlace (Γ : Ctx) (p : UPlace) (what : String) :
    Except String ((t : IntTy) × Place Γ (.IntL t)) := do
  let ⟨τ, pl⟩ ← elabPlace Γ p
  match τ, pl with
  | .IntL t, pl => return ⟨t, pl⟩
  | _, _ => .error s!"{what} is not an integer-typed place"

/-- The integer type an integer-valued rvalue is elaborated at: the
    destination's, or `usize` when the destination is not an integer (the
    assignment then reports the mismatch). -/
def intTyOf : LayoutTy → IntTy
  | .IntL t => t
  | _ => IntTy.u64

def elabRvalue (Γ : Ctx) (expected : LayoutTy) :
    URvalue → Except String ((τ : LayoutTy) × RExpr Γ τ)
  | .use (.const v) => .ok ⟨.IntL (intTyOf expected), .constInit v⟩
  | .use .constUnit => .error "unit constant not dropped by lowering"
  | .use (.str _) => .error "string literal not materialised by lowering"
  | .use (.copy p) | .use (.move p) => do
      -- an assignment `Move` operand is a COPY, as Miri evaluates it (rustc
      -- FIXME: "do some more logic on `move` to invalidate the old
      -- location"); the in-place protection Miri applies to a moved CALL
      -- argument is emitted by the seam (`emitSeamBind`), 2026-09-21
      let ⟨τ, pl⟩ ← elabPlace Γ p
      return ⟨τ, .copy pl⟩
  | .move p => do
      let ⟨τ, pl⟩ ← elabPlace Γ p
      return ⟨τ, .move pl⟩
  | .use (.unsupported d) => .error s!"unsupported: {d}"
  | .ref kind prot p => do
      let ⟨τ, pl⟩ ← elabPlace Γ p
      return ⟨.PtrL τ, .ref (toRefKind kind) prot (freezeMask p.ty) pl⟩
  | .exposeAddr p => do
      let ⟨τ, pl⟩ ← elabPlace Γ p
      match τ, pl with
      | .PtrL _, pl => return ⟨.IntL (intTyOf expected), .exposeAddr pl⟩
      | _, _ => .error "ptr-to-int cast of a non-pointer place"
  | .addr p => do
      let ⟨τ, pl⟩ ← elabPlace Γ p
      match τ, pl with
      | .PtrL _, pl => return ⟨.IntL (intTyOf expected), .addr pl⟩
      | _, _ => .error "ptr-to-int transmute of a non-pointer place"
  | .use (.constNeg _ _) => .error "negative constant not encoded by lowering"
  | .fromExposed _ => .error "fromExposed is elaborated against the destination type"
  | .rawField _ _ => .error "rawField is expanded at emission"
  | .ptrOffset _ _ _ => .error "ptrOffset is elaborated against the destination type"
  | .sliceLen p => do
      -- slice metadata: the fat pointer's extent, in elements
      let ⟨τ, pl⟩ ← elabPlace Γ p
      match τ, pl with
      | .PtrL _, pl => return ⟨.IntL (intTyOf expected), .sliceLen pl⟩
      | _, _ => .error "slice length of a non-pointer place"
  | .subSlice _ _ _ => .error "subSlice is elaborated against the destination type"
  | .binOp op ity a b => do
      -- a runtime word: two integer operand PLACES (the seam materialised
      -- any constant operand) and the mirlite `BinOp` the string names
      let pa ← match a with
        | .copy p | .move p => elabIntPlace Γ p "binOp operand"
        | _ => .error "binOp operand not materialised by lowering"
      let pb ← match b with
        | .copy p | .move p => elabIntPlace Γ p "binOp operand"
        | _ => .error "binOp operand not materialised by lowering"
      let some bop := binOpOf op ity.toIntTy
        | .error s!"unsupported: binary op {op}"
      return ⟨.IntL (intTyOf expected), .binOp bop pa.2 pb.2⟩
  | .refSlice _ _ _ => .error "refSlice is elaborated against the destination type"
  | .fnRef _ => .error "fn reference not consumed by lowering"
  | .uninit => .error "uninit is elaborated against the destination type"
  | .aggregate _ _ => .error "aggregate not desugared by lowering"
  | .discriminant _ => .error "discriminant not desugared by lowering"
  | .unsupported d => .error s!"unsupported: {d}"

def elabStmt (Γ : Ctx) : LStmt → Except String (Stmt Γ)
  | .pushProt _ => return .pushProtectors
  | .popProt _ => return .popProtectors
  | .assign dst rv line => do
      let ⟨τd, pd⟩ ← elabPlace Γ dst
      match rv with
      | .uninit => return .assign pd .uninit
      | .fromExposed p =>
          let np ← elabIntPlace Γ p "int-to-ptr cast source"
          match τd, pd with
          | .PtrL _, pd => return .assign pd (.fromExposed np.2)
          | _, _ => .error s!"int-to-ptr cast into a non-pointer place (line {line})"
      | .ptrOffset p delta inb =>
          let ⟨τp, pp⟩ ← elabPlace Γ p
          match τp, pp, τd, pd with
          | .PtrL _, pp, .PtrL _, pd => return .assign pd (.ptrOffset pp delta inb)
          | _, _, _, _ => .error s!"pointer offset on a non-pointer place (line {line})"
      | .refSlice kind prot p =>
          let ⟨τp, pp⟩ ← elabPlace Γ p
          match τp, pp, τd, pd with
          | .PtrL _, pp, .PtrL _, pd =>
              return .assign pd (.refSlice (toRefKind kind) prot pp)
          | _, _, _, _ => .error s!"slice retag on a non-pointer place (line {line})"
      | .subSlice p lo hi =>
          -- the ELEMENT type is the destination's pointee: the narrowing
          -- scales its bounds by that block size
          let ⟨τp, pp⟩ ← elabPlace Γ p
          let ploOp ← match lo with
            | .copy q | .move q => elabIntPlace Γ q "sub-slice bound"
            | _ => .error "sub-slice bound not materialised by lowering"
          let phiOp ← match hi with
            | .copy q | .move q => elabIntPlace Γ q "sub-slice bound"
            | _ => .error "sub-slice bound not materialised by lowering"
          match τd, pd with
          | .PtrL τe, pd =>
              -- source and destination are the same slice type: the
              -- narrowing neither changes the element nor the pointee
              if h : τp = obseq3.LayoutTy.PtrL τe then
                return .assign pd (.subSlice (h ▸ pp) ploOp.2 phiOp.2)
              else
                .error s!"sub-slice element type mismatch (line {line})"
          | _, _ => .error s!"sub-slice into a non-pointer place (line {line})"
      | _ =>
        let ⟨τr, er⟩ ← elabRvalue Γ τd rv
        if h : τr = τd then
          return .assign pd (h ▸ er)
        else
          -- pointer casts that change the pointee type are tag-preserving
          -- reinterprets (`p as *mut U`)
          match τd, pd, τr, er with
          | .PtrL _, pd, .PtrL _, .copy pl => return .assign pd (.ptrCast pl)
          | _, _, _, _ =>
            .error s!"type mismatch at line {line}: dst {reprStr τd} vs rhs {reprStr τr}"
  | .assignIf discr val dst rv line => do
      let discrP ← elabIntPlace Γ discr "assignIf discriminant"
      let ⟨τd, pd⟩ ← elabPlace Γ dst
      let ⟨τr, er⟩ ← elabRvalue Γ τd rv
      if h : τr = τd then
        return .assignIf discrP.2 val pd (h ▸ er)
      else
        .error s!"assignIf type mismatch at line {line}: dst {reprStr τd} vs rhs {reprStr τr}"
  | .alloc dst szOp _line => do
      let ⟨τd, pd⟩ ← elabPlace Γ dst
      match τd, pd with
      | .PtrL _, pd => do
          let len ← match szOp with
            | none => pure (AllocLen.const 1)
            | some (.const v) => pure (AllocLen.const v)
            | some (.copy p) | some (.move p) =>
                pure (AllocLen.fromPlace (← elabIntPlace Γ p "allocation size").2)
            | some _ => .error "unsupported allocation size operand"
          return .assign pd (.alloc len)
      | _, _ => .error "alloc destination is not pointer-typed"
  | .dealloc ptr _line => do
      let ⟨τp, pp⟩ ← elabPlace Γ ptr
      match τp, pp with
      | .PtrL _, pp => return .dealloc pp
      | _, _ => .error "dealloc argument is not pointer-typed"

/-- A loaded, runnable conformance program. `lines` is parallel to `prog`
    (source line per statement, for locating UB verdicts). -/
structure Loaded where
  Γ : Ctx
  prog : Prog Γ
  lines : List Nat
  stats : CertStats := {}
  /-- Each local's BYTE layout (widths, offsets, padding), for the byte
      machines; the typed program itself is on cell layouts. -/
  blay : List obseq3.bytes.BLayout := []

/-- The places a lowered statement mentions (for the opaque-local check). -/
def operandPlaces : UOperand → List UPlace
  | .copy p | .move p => [p]
  | _ => []

def rvaluePlaces : URvalue → List UPlace
  | .use op => operandPlaces op
  | .move p | .ref _ _ p | .exposeAddr p | .addr p | .fromExposed p | .ptrOffset p _ _ | .rawField p _
  | .refSlice _ _ p | .discriminant p | .sliceLen p => [p]
  | .subSlice p lo hi => p :: (operandPlaces lo ++ operandPlaces hi)
  | .aggregate _ ops => ops.flatMap operandPlaces
  | .binOp _ _ a b => operandPlaces a ++ operandPlaces b
  | .fnRef _ | .uninit | .unsupported _ => []

def stmtPlaces : LStmt → List UPlace
  | .assign dst rv _ => dst :: rvaluePlaces rv
  | .assignIf discr _ dst rv _ => discr :: dst :: rvaluePlaces rv
  | .alloc dst sz _ => dst :: (sz.map operandPlaces).getD []
  | .dealloc p _ => [p]
  | .pushProt _ | .popProt _ => []

def elabProg (lp : LProg) : Except String Loaded := do
  -- a local of a type the loader cannot lay out is tolerated as long as no
  -- statement touches it: `assert_eq!`'s never-walked panic arm declares
  -- `core::fmt::Arguments` locals in the same function body. Such a local
  -- gets a placeholder word layout; a USE of it is still an error.
  let layouts := lp.locals.map fun ty =>
    match toLayout ty with
    | .ok l => (l, none)
    | .error e => (obseq3.LayoutTy.usize, some e)
  let Γ := layouts.map (·.1)
  for s in lp.stmts do
    for p in stmtPlaces s do
      match p.root with
      | .local n =>
          match layouts[n]? with
          | some (_, some e) => throw s!"{e} (local _{n} used at line {s.line})"
          | _ => pure ()
      | .global _ => pure ()
  let stmts ← lp.stmts.mapM (elabStmt Γ)
  return { Γ, prog := stmts ++ [.halt], lines := lp.stmts.map (·.line) ++ [0], stats := lp.stats,
           -- a placeholder local (never used, checked above) gets the
           -- placeholder's layout, so every local's layout has its type's
           -- shape (`bytes.Agrees`, the byte proof's layout conditions)
           blay := (lp.locals.zip layouts).map fun (ty, _, err?) =>
             if err?.isSome then obseq3.bytes.ofLayoutTy .usize else toBLayout ty }

/-- Full pipeline: ULLBC JSON → parsed crate → lowered (along the
    certificate, if any) → elaborated. -/
def loadCrate (json : Lean.Json) (cert? : Option Cert := none) : Except String Loaded := do
  let crate ← parseCrate json
  let lp ← lowerCrate crate cert?
  elabProg lp

end conformance
