import obseq3.types

namespace obseq3

/-- v3 permission model: every operation is range-based (`len` cells) and
    returns `Except String` so error messages reach the conformance
    harness. Compare `obseq2.PermissionModel` (single-address, `Option`). -/
structure PermissionModel where
  State : Type
  init : State
  own : State → Word → Nat → Except String (State × Tag)
  read : State → Word → Nat → Tag → Except String State
  useMut : State → Word → Nat → Tag → Except String State
  ref : State → Word → Nat → Tag → RefKind → Except String (State × Tag)
  die : State → Word → Nat → Tag → Except String State

namespace PermissionModel

def stackedBorrows : PermissionModel where
  State := AccessPerms
  init := AccessPerms.init
  own := sb_own
  read := sb_read
  useMut := sb_write
  ref := sb_ref
  die := sb_die

end PermissionModel

end obseq3
