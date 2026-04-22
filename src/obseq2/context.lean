import obseq2.common

namespace obseq2

abbrev Ctx := List LayoutTy

structure Local (Γ : Ctx) (τ : LayoutTy) where
  idx : Fin Γ.length
  hTy : Γ.get idx = τ

namespace Local

variable {Γ : Ctx} {τ τ' : LayoutTy}

end Local

end obseq2
