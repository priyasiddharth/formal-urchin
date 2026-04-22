import obseq2.common

namespace obseq2

def RefKind.toSbRefOpKind : RefKind → obseq.RefOpKind
| .Shared => .Shared
| .Mut => .Mut
| .Raw => .Raw

structure PermissionModel where
  State : Type
  WellFormed : State → Prop
  own : State → Word → Option (State × Tag)
  read : State → Word → Tag → Option State
  useMut : State → Word → Tag → Option State
  ref : State → Word → Tag → RefKind → Option (State × Tag)
  die : State → Word → Tag → Option State

namespace PermissionModel

def stackedBorrows : PermissionModel where
  State := obseq.AccessPerms
  WellFormed := obseq.SBValid
  own := fun s addr =>
    match obseq.sb_own s addr with
    | (.Ok s', freshTag) => some (s', freshTag)
    | (.Err _, _) => none
  read := fun s addr tag =>
    match obseq.sb_read s addr tag with
    | .Ok s' => some s'
    | .Err _ => none
  useMut := fun s addr tag =>
    match obseq.sb_use_mb s addr tag with
    | .Ok s' => some s'
    | .Err _ => none
  ref := fun s addr tag kind =>
    match obseq.sb_ref s addr tag kind.toSbRefOpKind with
    | (.Ok s', freshTag) => some (s', freshTag)
    | (.Err _, _) => none
  die := fun s addr tag =>
    match obseq.sb_die s addr tag with
    | .Ok s' => some s'
    | .Err _ => none

end PermissionModel

end obseq2
