import obseq3.types

namespace obseq3

abbrev Ctx := List LayoutTy

structure Local (Γ : Ctx) (τ : LayoutTy) where
  idx : Fin Γ.length
  hTy : Γ.get idx = τ

end obseq3
