import obseq3.bytelayout

/-!
# A byte layout has its type's shape

`Agrees τ l`: the byte layout `l` has the shape of the cell layout `τ` —
an integer of any width for `NatL`, a pointer to an agreeing pointee for
`PtrL`, a tuple of agreeing fields (offsets, size and alignment free) for
`TupL`. Decidable per local, it implies the byte proof's two layout
conditions for EVERY place (`byteproof/layoutagree.lean`), so the
conformance harness can check the loader's layouts program by program.
-/

namespace obseq3.bytes

mutual
def Agrees : obseq.LayoutTy → BLayout → Bool
  | .NatL, .int _ => true
  | .PtrL τ, .ptr q => Agrees τ q
  | .TupL ts, .tup fs _ _ _ => AgreesList ts fs
  | _, _ => false

def AgreesList : List obseq.LayoutTy → List BLayout → Bool
  | [], [] => true
  | t :: ts, f :: fs => Agrees t f && AgreesList ts fs
  | _, _ => false
end

end obseq3.bytes
