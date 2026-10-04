import obseq3.syntax
import obseq3.permission

/-!
# Values, bindings and registers

The data both machines share:
- mirlite's environment (`Binding`, `Env`), the value of one leaf
  (`MemValue`) and a resolved place (`PlaceRes`);
- OSEA-IR's registers and the value a register holds (`Val`), with the
  one-to-one translation between the two value types.
-/

namespace obseq3.mirlite

open obseq3

structure Binding where
  addr : Word
  tag : Tag
deriving Repr, Inhabited

abbrev Env (Γ : Ctx) := Fin Γ.length → Option Binding

namespace Env

def empty : Env Γ := fun _ => none

def lookup (env : Env Γ) (loc : Local Γ τ) : Option Binding :=
  env loc.idx

def set (env : Env Γ) (loc : Local Γ τ) (binding : Binding) : Env Γ :=
  fun idx => if idx = loc.idx then some binding else env idx

end Env

/-- The value of one leaf (an integer or a pointer). -/
inductive MemValue where
| undef
| word  (value : Word)
-- `base`/`sizeB` are the ALLOCATION the pointer has provenance over;
-- `offsetB` is where it points inside it; `extentB` is how many bytes the
-- pointer claims from there — the pointee's size for a thin pointer,
-- `len · elemSizeB` for a slice.
| ptrVal (base : Word) (offsetB : Word) (extentB : Word) (sizeB : Word) (tag : Tag)
deriving Repr, BEq, Inhabited

/-- A resolved place: its address, the tag it is accessed with, and the
    allocation it lies in. -/
structure PlaceRes where
  addr      : Word
  tag       : Tag
  allocBase : Word
  allocSizeB : Word

end obseq3.mirlite

namespace obseq3.oseair

open obseq3

inductive Register
| R (idx : Nat)
deriving Repr, Inhabited, DecidableEq, BEq

/-- A register's value: mirlite's `MemValue`, constructor for constructor. -/
inductive Val
| Undef
| Dat (value : Word)
| Ptr (base : Word) (offsetB : Word) (extentB : Word) (sizeB : Word) (tag : Tag)
deriving Repr, BEq, Inhabited

open obseq3.mirlite (MemValue)

def Val.toMem : Val → MemValue
  | .Undef => .undef
  | .Dat w => .word w
  | .Ptr b o e s t => .ptrVal b o e s t

def ofMem : MemValue → Val
  | .undef => .Undef
  | .word w => .Dat w
  | .ptrVal b o e s t => .Ptr b o e s t

end obseq3.oseair
