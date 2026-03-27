import obseq.mirlite

namespace obseq.notation

open obseq

/-- Proof-facing notation helper for the base place with no projection path. -/
def basePlace (base : Word) : mirlite.LExpr :=
  mirlite.LExpr.Place { base := base, path := [] }

/-- Proof-facing notation helper for constant RHS expressions. -/
def constRhs (n : Word) : mirlite.RExpr :=
  mirlite.RExpr.ConstOp n

/-- Proof-facing notation helper for base-place copy RHS expressions. -/
def copyRhs (base : Word) : mirlite.RExpr :=
  mirlite.RExpr.CopyOp { base := base, path := [] }

/--
Proof-facing notation helper for the supported binary-op fragment:
the sum of two base-place copies.
-/
def binCopyRhs (lhs rhs : Word) : mirlite.RExpr :=
  mirlite.RExpr.BinaryOp (copyRhs lhs) (copyRhs rhs)

scoped syntax "place(" term ")" : term
scoped syntax "const " term : term
scoped syntax "copy " term : term
scoped syntax:60 term " ::= " term : term

scoped macro_rules
  | `(place($b)) => `(obseq.notation.basePlace $b)
  | `(const $n) => `(obseq.notation.constRhs $n)
  | `(copy $b) => `(obseq.notation.copyRhs $b)
  | `($lhs ::= $rhs) => `(obseq.mirlite.Stmt.Assgn $lhs $rhs)

open scoped obseq.notation

example (base : Word) :
    place(base) = mirlite.LExpr.Place { base := base, path := [] } := by
  rfl

example (n : Word) :
    (const n) = mirlite.RExpr.ConstOp n := by
  rfl

example (base : Word) :
    (copy base) = mirlite.RExpr.CopyOp { base := base, path := [] } := by
  rfl

example (lhs rhs : Word) :
    binCopyRhs lhs rhs =
      mirlite.RExpr.BinaryOp
        (mirlite.RExpr.CopyOp { base := lhs, path := [] })
        (mirlite.RExpr.CopyOp { base := rhs, path := [] }) := by
  rfl

example (base n : Word) :
    (place(base) ::= const n) =
      mirlite.Stmt.Assgn
        (mirlite.LExpr.Place { base := base, path := [] })
        (mirlite.RExpr.ConstOp n) := by
  rfl

end obseq.notation
