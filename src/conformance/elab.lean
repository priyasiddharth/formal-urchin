import conformance.lowering
import obseq3.mirlite_semantics

/-!
Elaborate a lowered untyped program (`LProg`) into obseq3's intrinsically
typed syntax: `(Γ : Ctx) × Prog Γ`. Type agreement is established with
`DecidableEq LayoutTy` and transported along the resulting equalities, so
runtime-parsed programs need no hand-written proofs.
-/

namespace conformance

open obseq3

def toLayout : UTy → Except String LayoutTy
  | .nat => .ok .NatL
  | .ref _ inner => do return .PtrL (← toLayout inner)
  | .raw _ inner => do return .PtrL (← toLayout inner)
  | .tup tys => do return .TupL (← tys.mapM toLayout)
  | .unsupported d => .error s!"unsupported: type {d}"

def toRefKind : URefKind → obseq3.RefKind
  | .shared => .Shared
  | .mut => .Mut
  | .twoPhase => .TwoPhase
  | .rawMut => .Raw true
  | .rawConst => .Raw false

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

def elabPlace (Γ : Ctx) (p : UPlace) : Except String ((τ : LayoutTy) × Place Γ τ) := do
  let ⟨τ, pl⟩ ← elabRoot Γ p.root
  elabPlaceAux Γ τ pl p.projs

def elabRvalue (Γ : Ctx) : URvalue → Except String ((τ : LayoutTy) × RExpr Γ τ)
  | .use (.const v) => .ok ⟨.NatL, .constInit v⟩
  | .use .constUnit => .error "unit constant not dropped by lowering"
  | .use (.copy p) | .use (.move p) => do
      let ⟨τ, pl⟩ ← elabPlace Γ p
      return ⟨τ, .copy pl⟩
  | .use (.unsupported d) => .error s!"unsupported: {d}"
  | .ref kind prot p => do
      let ⟨τ, pl⟩ ← elabPlace Γ p
      return ⟨.PtrL τ, .ref (toRefKind kind) prot pl⟩
  | .uninit => .error "uninit is elaborated against the destination type"
  | .aggregate _ => .error "aggregate not desugared by lowering"
  | .unsupported d => .error s!"unsupported: {d}"

def elabStmt (Γ : Ctx) : LStmt → Except String (Stmt Γ)
  | .pushProt _ => return .pushProtectors
  | .popProt _ => return .popProtectors
  | .assign dst rv line => do
      let ⟨τd, pd⟩ ← elabPlace Γ dst
      match rv with
      | .uninit => return .assign pd .uninit
      | _ =>
        let ⟨τr, er⟩ ← elabRvalue Γ rv
        if h : τr = τd then
          return .assign pd (h ▸ er)
        else
          .error s!"type mismatch at line {line}: dst {reprStr τd} vs rhs {reprStr τr}"

/-- A loaded, runnable conformance program. `lines` is parallel to `prog`
    (source line per statement, for locating UB verdicts). -/
structure Loaded where
  Γ : Ctx
  prog : Prog Γ
  lines : List Nat

def elabProg (lp : LProg) : Except String Loaded := do
  let Γ ← lp.locals.mapM toLayout
  let stmts ← lp.stmts.mapM (elabStmt Γ)
  return { Γ, prog := stmts ++ [.halt], lines := lp.stmts.map (·.line) ++ [0] }

/-- Full pipeline: ULLBC JSON → parsed crate → lowered → elaborated. -/
def loadCrate (json : Lean.Json) : Except String Loaded := do
  let crate ← parseCrate json
  let lp ← lowerCrate crate
  elabProg lp

end conformance
