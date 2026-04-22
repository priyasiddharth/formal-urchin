import obseq2.syntax

namespace obseq2.examples

open obseq2

abbrev NatL : LayoutTy := obseq.LayoutTy.NatL
abbrev PairNat : LayoutTy := obseq.LayoutTy.TupL [NatL, NatL]
abbrev PtrNat : LayoutTy := obseq.LayoutTy.PtrL NatL

abbrev Γcopy : Ctx := [NatL, NatL]

def copyDst : Local Γcopy NatL := {
  idx := ⟨0, by simp [Γcopy]⟩
  hTy := by simp [Γcopy]
}

def copySrc : Local Γcopy NatL := {
  idx := ⟨1, by simp [Γcopy]⟩
  hTy := by simp [Γcopy]
}

def typedCopy : Stmt Γcopy :=
  copyAssign (.local copyDst) (.local copySrc)

abbrev Γconst : Ctx := [NatL]

def constDst : Local Γconst NatL := {
  idx := ⟨0, by simp [Γconst]⟩
  hTy := by simp [Γconst]
}

def typedConstInit : Stmt Γconst :=
  .assign (.local constDst) (.constInit 7)

abbrev Γref : Ctx := [PtrNat, PairNat]

def refDst : Local Γref PtrNat := {
  idx := ⟨0, by simp [Γref]⟩
  hTy := by simp [Γref]
}

def refSrcBase : Local Γref PairNat := {
  idx := ⟨1, by simp [Γref]⟩
  hTy := by simp [Γref]
}

def fstPath : PathTo PairNat NatL :=
  .field (idx := ⟨0, by simp⟩) .nil

def projectedSrc : Place Γref NatL :=
  .proj (.local refSrcBase) fstPath

def typedRef : Stmt Γref :=
  refAssign (.local refDst) .Shared projectedSrc

abbrev Γderef : Ctx := [NatL, PtrNat]

def derefDst : Local Γderef NatL := {
  idx := ⟨0, by simp [Γderef]⟩
  hTy := by simp [Γderef]
}

def derefSrc : Local Γderef PtrNat := {
  idx := ⟨1, by simp [Γderef]⟩
  hTy := by simp [Γderef]
}

def typedDeref : Stmt Γderef :=
  derefAssign (.local derefDst) (.local derefSrc)

end obseq2.examples
