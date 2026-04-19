import obseq.sb

namespace obseq

structure AllocatorSpec
  (Mem : Type) where
  alloc : Mem → Nat → Word × Mem

end obseq
