import obseq3.compile_tests
open obseq3 obseq3.CompileTests

namespace obseq3.OrderProbe
open obseq3.mirlite

-- x : Nat, p : *mut Nat, q : *mut *mut Nat, q2 : *mut *mut Nat, r : *mut Nat
abbrev natL := obseq.LayoutTy.NatL
abbrev pN := obseq.LayoutTy.PtrL natL
abbrev ppN := obseq.LayoutTy.PtrL pN

def Γp : Ctx := [natL, pN, ppN, ppN, pN]
def x : Place Γp natL := .local ⟨⟨0, by decide⟩, rfl⟩
def p : Place Γp pN := .local ⟨⟨1, by decide⟩, rfl⟩
def q : Place Γp ppN := .local ⟨⟨2, by decide⟩, rfl⟩
def q2 : Place Γp ppN := .local ⟨⟨3, by decide⟩, rfl⟩
def r : Place Γp pN := .local ⟨⟨4, by decide⟩, rfl⟩

/-- The copy's range read and the destination chain's pointer-cell read
    land on the SAME cell (p's storage), through tags where the source's
    is a Unique reborrow ABOVE the destination chain's. -/
def prog : List (Stmt Γp) :=
  [.assign x (.constInit 5),
   .assign p (.ref .Mut false [] x),
   .assign q (.ref .Mut false [] p),
   .assign q2 (.ref .Mut false [] (.deref q)),
   .assign r (.ptrCast q2),
   .assign (.deref (.deref q)) (.copy (.deref r))]

#eval expectDiff Γp prog .ok "order probe"

end obseq3.OrderProbe
