import obseq3.oseair

/-!
# Route brackets

The compiler's `Die`s close ROUTE BRACKETS: a borrow it mints for its own
use, one access through it, and the `Die`:

    l     r := Borrow k false [] (some n) base off    -- k pushes on top
    l+1   one access THROUGH r (Load/ExposeAddr/FromExposed/PtrOffset of r,
          or RStore/CStore at r)
    l+2   Die r n

`bracketIssues` checks that every `Die` of a program closes such a
bracket, that the bracket's register appears nowhere else in the program,
and that no `SkipIf` jumps into a bracket. Then the route tag never
leaves its register, the `Die` finds it on top, and after the `Die` no
instruction holds it: this is what makes OSEA-IR and OSEA-IR_B (`Die`
elided) agree on compiled code. The check is decidable and per program,
like the layout check.
-/

namespace obseq3.oseair

open obseq3

/-- Every register an `Rhs` mentions. -/
def Rhs.regs : Rhs → List Register
  | .Load _ r | .AllocDyn _ r | .ExposeAddr _ r | .FromExposed _ r
  | .PtrOffset _ r _ _ | .PlaceAddr r _ _ | .SliceLen _ r => [r]
  | .Alloc _ | .AllocN _ _ => []
  | .Borrow _ _ _ _ r _ => [r]
  | .PtrOffsetBy _ _ r1 r2 _ | .BinOp _ r1 r2 => [r1, r2]
  | .SubSlice _ r1 r2 r3 => [r1, r2, r3]

/-- Every register an instruction mentions, read or written. -/
def Instr.regs : Instr → List Register
  | .Assgn r rhs => r :: rhs.regs
  | .RStore _ s p => [s, p]
  | .CStore _ _ p => [p]
  | .Die r _ => [r]
  | .Dealloc p => [p]
  | .SkipIf d _ _ => [d]
  | .PushProt | .PopProt | .Halt => []

/-- A route borrow: no protector, no mask, a static length, and a kind
    that PUSHES its item on top (not an insert-above). -/
def Instr.routeBorrow? : Instr → Option (Register × Nat)
  | .Assgn r (.Borrow k false [] (some n) _ _) =>
      match k with
      | .Mut | .BoxMut | .Shared | .Raw false => some (r, n)
      | _ => none
  | _ => none

/-- An access THROUGH `r` that writes no register but a fresh one and
    copies nothing out of `r`. -/
def Instr.through (r : Register) : Instr → Bool
  | .Assgn d (.Load _ p) | .Assgn d (.ExposeAddr _ p) | .Assgn d (.FromExposed _ p)
  | .Assgn d (.PtrOffset _ p _ _) => p == r && d != r
  | .RStore _ s p => p == r && s != r
  | .CStore _ _ p => p == r
  | _ => false

/-- The problems with a program's route brackets (empty: all good). -/
def bracketIssues (code : List (Option Instr)) : List String := Id.run do
  let mut issues : List String := []
  let at? (l : Nat) : Option Instr := (code[l]?).getD none
  -- the labels of the brackets' three instructions
  let mut inBracket : List (Nat × Nat) := []   -- (borrow label, die label)
  for l in List.range code.length do
    match at? l with
    | some (.Die r n) =>
        if l < 2 then
          issues := issues ++ [s!"label {l}: Die with no bracket"]
        else
          match (at? (l - 2)).bind Instr.routeBorrow?, at? (l - 1) with
          | some (r', n'), some acc =>
              if r' != r then
                issues := issues ++ [s!"label {l}: Die {reprStr r} closes a borrow of {reprStr r'}"]
              else if n' != n then
                issues := issues ++ [s!"label {l}: Die length {n}, borrow length {n'}"]
              else if !acc.through r then
                issues := issues ++ [s!"label {l}: the bracket's middle is not an access through {reprStr r}: {reprStr acc}"]
              else
                inBracket := inBracket ++ [(l - 2, l)]
          | _, _ => issues := issues ++ [s!"label {l}: Die not preceded by a route borrow and an access"]
    | _ => pure ()
  -- a bracket's register appears in its three instructions only
  for (b, d) in inBracket do
    match at? d with
    | some (.Die r _) =>
        for l in List.range code.length do
          if l < b || d < l then
            match at? l with
            | some i =>
                if i.regs.contains r then
                  issues := issues ++ [s!"label {l}: mentions {reprStr r}, the register of the bracket at {b}"]
            | none => pure ()
    | _ => pure ()
  -- no jump lands inside a bracket
  for l in List.range code.length do
    match at? l with
    | some (.SkipIf _ _ skip) =>
        let t := l + 1 + skip
        for (b, d) in inBracket do
          if b < t && t ≤ d then
            issues := issues ++ [s!"label {l}: SkipIf lands at {t}, inside the bracket at {b}"]
    | _ => pure ()
  return issues

end obseq3.oseair
