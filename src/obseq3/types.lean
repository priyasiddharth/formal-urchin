import obseq3.sb

namespace obseq3

/-- An integer type: width in bits and signedness. A word of this type
    holds the type's BIT PATTERN, below `2 ^ bits` (two's complement when
    signed), as rustc's interpreter stores it. -/
structure IntTy where
  bits : Nat
  signed : Bool
deriving Repr, BEq, DecidableEq, Inhabited

namespace IntTy

def u64 : IntTy := ⟨64, false⟩

def modulus (t : IntTy) : Nat := 2 ^ t.bits

/-- The width in bytes (at least one: `bool` is a byte). -/
def sizeB (t : IntTy) : Nat := max 1 (t.bits / 8)

/-- The mathematical value of a bit pattern. -/
def toInt (t : IntTy) (w : Word) : Int :=
  let w := w % t.modulus
  if t.signed && 2 * w ≥ t.modulus then (w : Int) - t.modulus else w

/-- The bit pattern of a mathematical value, wrapping at the width. -/
def ofInt (t : IntTy) (i : Int) : Word := (i % (t.modulus : Int)).toNat

/-- Is `i` representable in `t`? -/
def inRange (t : IntTy) (i : Int) : Bool :=
  if t.signed then -(t.modulus : Int) ≤ 2 * i && 2 * i < t.modulus
  else 0 ≤ i && i < t.modulus

end IntTy

/-- A layout type: what a place holds. `IntL t` is an integer of type `t`
    (width and signedness — the static half of MiniRust's
    `Type::Int(IntType)`); `PtrL τ` a pointer to a `τ`; `TupL` a tuple.
    Byte offsets and padding are not here: the byte model takes them from a
    per-local byte layout (`mirlite.LayEnv`). -/
inductive LayoutTy where
  | IntL (t : IntTy)
  | PtrL (inner : LayoutTy)
  | TupL (tys : List LayoutTy)
deriving Repr, BEq, Inhabited

instance : ToString LayoutTy where
  toString t := reprStr t

/-- The pointer-sized unsigned integer (`usize`): sizes, addresses, and the
    loader's model words. -/
abbrev LayoutTy.usize : LayoutTy := .IntL IntTy.u64


/-- Integer binary operations, as MIR has them (rustc
    `interpret/operator.rs`, `binary_int_op`), each at an integer type:
    - `add`/`sub`/`mul`: MIR `Add`/`Sub`/`Mul` — WRAP at the width;
    - `addOv`/`subOv`/`mulOv`: the overflow FLAG of `AddWithOverflow` etc.
      (0/1); the loader pairs it with the wrapped result, and the panic of
      a debug-build overflow is a separate `Assert` on it;
    - `addUB`/`subUB`/`mulUB`: `AddUnchecked` etc. — UB on overflow;
    - `div`/`rem`: truncating; UB on a zero divisor and on signed
      `MIN / -1` (rustc inserts an `Assert` before them);
    - `bitAnd`/`bitOr`/`bitXor` on bit patterns;
    - `shl`/`shr`: amount taken modulo the width; `shr` is arithmetic when
      signed; `shlUB`/`shrUB` (`ShlUnchecked`…) are UB when the amount is
      not below the width;
    - comparisons by the type's signedness; `eq`/`ne` on bit patterns.
    UB is not computed by `evalBinOp` (which stays total, so a proof can
    treat it as opaque) but decided by `binOpUB`, which both machines
    consult first. -/
inductive BinOp where
| add (t : IntTy) | sub (t : IntTy) | mul (t : IntTy)
| addOv (t : IntTy) | subOv (t : IntTy) | mulOv (t : IntTy)
| addUB (t : IntTy) | subUB (t : IntTy) | mulUB (t : IntTy)
| div (t : IntTy) | rem (t : IntTy)
| bitAnd (t : IntTy) | bitOr (t : IntTy) | bitXor (t : IntTy)
| shl (t : IntTy) | shr (t : IntTy) | shlUB (t : IntTy) | shrUB (t : IntTy)
| lt (t : IntTy) | le (t : IntTy) | gt (t : IntTy) | ge (t : IntTy)
| eq | ne
deriving Repr, BEq, DecidableEq, Inhabited

def flag (b : Bool) : Word := if b then 1 else 0

def evalBinOp : BinOp → Word → Word → Word
  | .add t, x, y | .addUB t, x, y => t.ofInt (t.toInt x + t.toInt y)
  | .sub t, x, y | .subUB t, x, y => t.ofInt (t.toInt x - t.toInt y)
  | .mul t, x, y | .mulUB t, x, y => t.ofInt (t.toInt x * t.toInt y)
  | .addOv t, x, y => flag !(t.inRange (t.toInt x + t.toInt y))
  | .subOv t, x, y => flag !(t.inRange (t.toInt x - t.toInt y))
  | .mulOv t, x, y => flag !(t.inRange (t.toInt x * t.toInt y))
  | .div t, x, y => t.ofInt (Int.tdiv (t.toInt x) (t.toInt y))
  | .rem t, x, y => t.ofInt (Int.tmod (t.toInt x) (t.toInt y))
  | .bitAnd t, x, y => (x % t.modulus) &&& (y % t.modulus)
  | .bitOr t, x, y => (x % t.modulus) ||| (y % t.modulus)
  | .bitXor t, x, y => (x % t.modulus) ^^^ (y % t.modulus)
  | .shl t, x, y | .shlUB t, x, y => t.ofInt (t.toInt x * 2 ^ (y % t.bits))
  | .shr t, x, y | .shrUB t, x, y => t.ofInt (Int.ediv (t.toInt x) (2 ^ (y % t.bits)))
  | .lt t, x, y => flag (decide (t.toInt x < t.toInt y))
  | .le t, x, y => flag (decide (t.toInt x ≤ t.toInt y))
  | .gt t, x, y => flag (decide (t.toInt x > t.toInt y))
  | .ge t, x, y => flag (decide (t.toInt x ≥ t.toInt y))
  | .eq, x, y => flag (x == y)
  | .ne, x, y => flag (x != y)

/-- The undefined behaviour of an operation on these operands, if any
    (rustc: `throw_ub!` in `binary_int_op`). -/
def binOpUB : BinOp → Word → Word → Option String
  | .addUB t, x, y =>
      if t.inRange (t.toInt x + t.toInt y) then none else some "arithmetic overflow in unchecked_add"
  | .subUB t, x, y =>
      if t.inRange (t.toInt x - t.toInt y) then none else some "arithmetic overflow in unchecked_sub"
  | .mulUB t, x, y =>
      if t.inRange (t.toInt x * t.toInt y) then none else some "arithmetic overflow in unchecked_mul"
  | .div t, x, y | .rem t, x, y =>
      if t.toInt y == 0 then some "division by zero"
      else if !(t.inRange (Int.tdiv (t.toInt x) (t.toInt y))) then some "overflow in signed division"
      else none
  | .shlUB t, _, y | .shrUB t, _, y =>
      if y % t.modulus < t.bits then none else some "shift amount out of range"
  | _, _, _ => none

/- Decidable equality for `LayoutTy`.
   Needed by the conformance elaborator to produce `Local`/`Place`
   type-equality proofs from runtime-parsed programs. -/
mutual
  def layoutDecEq : (a b : LayoutTy) → Decidable (a = b)
    | .IntL s, .IntL t =>
        if h : s = t then .isTrue (by rw [h]) else .isFalse (by intro hc; cases hc; exact h rfl)
    | .IntL _, .PtrL _ | .IntL _, .TupL _ => .isFalse (by intro h; cases h)
    | .PtrL _, .IntL _ | .PtrL _, .TupL _ => .isFalse (by intro h; cases h)
    | .TupL _, .IntL _ | .TupL _, .PtrL _ => .isFalse (by intro h; cases h)
    | .PtrL a, .PtrL b =>
        match layoutDecEq a b with
        | .isTrue h => .isTrue (by rw [h])
        | .isFalse h => .isFalse (by intro hc; cases hc; exact h rfl)
    | .TupL as, .TupL bs =>
        match layoutListDecEq as bs with
        | .isTrue h => .isTrue (by rw [h])
        | .isFalse h => .isFalse (by intro hc; cases hc; exact h rfl)

  def layoutListDecEq : (as bs : List LayoutTy) → Decidable (as = bs)
    | [], [] => .isTrue rfl
    | [], _ :: _ => .isFalse (by intro h; cases h)
    | _ :: _, [] => .isFalse (by intro h; cases h)
    | a :: as, b :: bs =>
        match layoutDecEq a b, layoutListDecEq as bs with
        | .isTrue h₁, .isTrue h₂ => .isTrue (by rw [h₁, h₂])
        | .isFalse h₁, _ => .isFalse (by intro hc; cases hc; exact h₁ rfl)
        | _, .isFalse h₂ => .isFalse (by intro hc; cases hc; exact h₂ rfl)
end

instance : DecidableEq LayoutTy := layoutDecEq

end obseq3
