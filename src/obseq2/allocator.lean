import obseq2.types

namespace obseq2

structure AllocatorSpec (Mem : Type) where
  alloc : Mem → Nat → Word × Mem

end obseq2
