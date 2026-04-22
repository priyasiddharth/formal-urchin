import obseq2.types

namespace obseq2

def blockSize (layout : LayoutTy) : Nat :=
  layoutSize layout

inductive RefKind
| Shared
| Mut
| Raw
deriving Repr, BEq, Inhabited, DecidableEq

abbrev AddrRenameMap := Word → Option Word
abbrev TagRenameMap := Tag → Option Tag

end obseq2
