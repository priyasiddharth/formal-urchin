import obseq.types
import obseq.sb

namespace obseq2

abbrev Word := obseq.Word
abbrev Tag := obseq.Tag

abbrev TyVal := obseq.TyVal
abbrev LayoutTy := obseq.LayoutTy

abbrev typeSize : TyVal → Nat := obseq.typeSize
abbrev typeSizeList : List TyVal → Nat := obseq.typeSizeList

abbrev layoutSize : LayoutTy → Nat := obseq.layoutSize
abbrev layoutSizeList : List LayoutTy → Nat := obseq.layoutSizeList

abbrev layoutToTyVal : LayoutTy → TyVal := obseq.layoutToTyVal
abbrev layoutToTyValList : List LayoutTy → List TyVal := obseq.layoutToTyValList

end obseq2
