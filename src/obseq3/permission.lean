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
  ref : State → Word → Nat → Tag → RefKind → Bool → List Bool → Except String (State × Tag)
  die : State → Word → Nat → Tag → Except String State
  dealloc : State → Word → Nat → Tag → Except String State
  expose : State → Tag → Except String State
  pushFrame : State → State
  popFrame : State → Except String State

namespace PermissionModel

def stackedBorrows : PermissionModel where
  State := AccessPerms
  init := AccessPerms.init
  own := sb_own
  read := sb_read
  useMut := sb_write
  ref := fun s addr len tag kind prot mask => sb_ref s addr len tag kind prot mask
  die := sb_die
  dealloc := sb_dealloc
  expose := sb_expose
  pushFrame := sb_push_frame
  popFrame := sb_pop_frame

/-- OSEA-IR_B's model: Stacked Borrows with `Die` a no-op — die elision
    (`proof.die_elision`). -/
def stackedBorrowsNoDie : PermissionModel :=
  { stackedBorrows with die := fun s _ _ _ => .ok s }

end PermissionModel

end obseq3
