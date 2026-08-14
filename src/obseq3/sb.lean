import obseq.types

/-!
# obseq3 Stacked Borrows model

v3 of the SB permission model, forked from `obseq.sb` (v1) for the Miri
conformance suite (see plans/sb_conformance_obseq3.md). Differences from v1:

- **Per-cell stacks**: every operation takes a length and acts on each cell
  of `[addr, addr+len)`. `sb_own` initializes a stack at every cell of the
  allocation (v1 only ever created a stack at the allocation base, so any
  access at offset > 0 failed).
- **Writable raw pointers**: stack items for raw pointers carry mutability.
  `RawPtr true` behaves like Miri's SharedReadWrite (grants writes, survives
  reads); `RawPtr false` behaves like a shared item. v1 rejected all writes
  through raws and performed a mutable parent access even for const raws.
- Results are `Except String` so error messages (with cell offsets) reach
  the conformance harness.

Known divergence from Miri (documented, tests affected are xfail-model):
no SharedReadWrite *grouping* — sibling `RawPtr true` items invalidate each
other the way Unique items do.

Executable only; preservation lemmas are reconstructed on demand later.
-/

namespace obseq3

abbrev Word := Nat
abbrev Tag := Nat

/-- Surface kinds for reference-creating operations (retags).
    `TwoPhase` is a reserved two-phase `&mut`: like Miri's SB treatment it
    performs only a *read* parent access and pushes a SharedReadWrite-like
    item (writable, survives reads). -/
inductive RefKind
| Shared
| Mut
| Raw (mutbl : Bool)
| TwoPhase
deriving Inhabited, Repr, BEq, DecidableEq

/-- Borrow-stack items. -/
inductive Item
| Own (tag : Tag)
| MutRef (tag : Tag)
| Ref (tag : Tag)
| RawPtr (mutbl : Bool) (tag : Tag)
deriving Inhabited, Repr, BEq

namespace Item

def tag : Item → Tag
| Own t => t
| MutRef t => t
| Ref t => t
| RawPtr _ t => t

/-- Items popped by a read access performed through an item below them.
    Miri: Unique items get disabled on foreign reads; shared and
    SharedReadWrite items survive. -/
def poppedByRead : Item → Bool
| MutRef _ => true
| _ => false

/-- Items that grant write access. -/
def grantsWrite : Item → Bool
| Own _ => true
| MutRef _ => true
| RawPtr true _ => true
| _ => false

end Item

def RefKind.toItem : RefKind → Tag → Item
| .Shared => .Ref
| .Mut => .MutRef
| .Raw mutbl => .RawPtr mutbl
| .TwoPhase => .RawPtr true

abbrev BorrowStack := List Item

/-- Per-address map of borrow stacks (top of stack = list head). -/
abbrev SB := List (Word × BorrowStack)

def SB.find? (sb : SB) (addr : Word) : Option BorrowStack :=
  match sb with
  | [] => none
  | (a, stack) :: rest => if a == addr then some stack else SB.find? rest addr

def SB.set (sb : SB) (addr : Word) (stack : BorrowStack) : SB :=
  (addr, stack) :: sb.filter (fun (a, _) => a != addr)

/-- `protFrames` models Miri's call-frame protectors: a stack of tag sets,
    one frame per active (inlined) call. A tag in any active frame is
    *protected*: any access that would pop or disable its items is UB.
    Frames are pushed/popped by the `pushProtectors`/`popProtectors`
    pseudo-statements the loader emits at inline seams. -/
structure AccessPerms where
  StackMap : SB
  NextTag : Tag
  protFrames : List (List Tag) := []
deriving Inhabited, Repr, BEq

def AccessPerms.init : AccessPerms := { StackMap := [], NextTag := 0 }

def AccessPerms.isProtected (ap : AccessPerms) (tag : Tag) : Bool :=
  ap.protFrames.any (·.contains tag)

/-- First protected item in a list of items about to be popped/disabled. -/
def firstProtected (ap : AccessPerms) (items : List Item) : Option Item :=
  items.find? (fun k => ap.isProtected k.tag)

def freshTag (ap : AccessPerms) : Tag × AccessPerms :=
  (ap.NextTag, { ap with NextTag := ap.NextTag + 1 })

/-- Split a stack at the item with the given tag:
    `(itemsAbove, item, itemsBelow)` where `itemsAbove` are closer to the top. -/
def splitStack : BorrowStack → Tag → Option (BorrowStack × Item × BorrowStack)
  | [], _ => none
  | item :: rest, tag =>
      if item.tag == tag then some ([], item, rest)
      else match splitStack rest tag with
        | some (above, found, below) => some (item :: above, found, below)
        | none => none

/-! ## Single-cell primitives -/

/-- Read access at one cell through `tag`: the granting item may be any
    kind; items above it that are `poppedByRead` (Unique) are removed —
    unless one of them is protected, which is UB. -/
def readCell (ap : AccessPerms) (addr : Word) (tag : Tag) : Except String AccessPerms :=
  match ap.StackMap.find? addr with
  | none => .error s!"sb-read: no borrow stack at address {addr}"
  | some stack =>
    match splitStack stack tag with
    | none => .error s!"sb-read: tag {tag} does not exist in the borrow stack at {addr}"
    | some (above, item, below) =>
      let popped := above.filter (·.poppedByRead)
      match firstProtected ap popped with
      | some p =>
          .error s!"sb-read: not granting read access to tag {tag} at {addr} because that would remove item for tag {p.tag} which is strongly protected"
      | none =>
        let above' := above.filter (fun k => !k.poppedByRead)
        .ok { ap with StackMap := ap.StackMap.set addr (above' ++ item :: below) }

/-- Write access at one cell through `tag`: the granting item must grant
    writes; everything above it is popped — unless one of the popped
    items is protected, which is UB. -/
def writeCell (ap : AccessPerms) (addr : Word) (tag : Tag) : Except String AccessPerms :=
  match ap.StackMap.find? addr with
  | none => .error s!"sb-write: no borrow stack at address {addr}"
  | some stack =>
    match splitStack stack tag with
    | none => .error s!"sb-write: tag {tag} does not exist in the borrow stack at {addr}"
    | some (above, item, below) =>
      if item.grantsWrite then
        match firstProtected ap above with
        | some p =>
            .error s!"sb-write: not granting write access to tag {tag} at {addr} because that would remove item for tag {p.tag} which is strongly protected"
        | none =>
            .ok { ap with StackMap := ap.StackMap.set addr (item :: below) }
      else
        .error s!"sb-write: tag {tag} (a read-only item) does not grant write access at {addr}"

/-- Initialize one cell with a root `Own` item. The cell must not already
    have a (nonempty) stack. -/
def ownCell (ap : AccessPerms) (addr : Word) (tag : Tag) : Except String AccessPerms :=
  match ap.StackMap.find? addr with
  | some [] | none =>
      .ok { ap with StackMap := ap.StackMap.set addr [.Own tag] }
  | some _ => .error s!"sb-own: borrow stack at {addr} is not empty"

/-- Push a new item on one cell's stack. -/
def pushCell (ap : AccessPerms) (addr : Word) (item : Item) : Except String AccessPerms :=
  match ap.StackMap.find? addr with
  | none => .error s!"sb-push: no borrow stack at address {addr}"
  | some stack => .ok { ap with StackMap := ap.StackMap.set addr (item :: stack) }

/-- Insert a new item directly above the granting item (Miri's placement
    for SharedReadWrite: adjacent to the parent, not on top — this is what
    makes sibling raw pointers coexist). No access is performed. -/
def insertAboveCell (ap : AccessPerms) (addr : Word) (tag : Tag) (item : Item) :
    Except String AccessPerms :=
  match ap.StackMap.find? addr with
  | none => .error s!"sb-insert: no borrow stack at address {addr}"
  | some stack =>
    match splitStack stack tag with
    | none => .error s!"sb-insert: tag {tag} does not exist in the borrow stack at {addr}"
    | some (above, granting, below) =>
        .ok { ap with StackMap := ap.StackMap.set addr (above ++ item :: granting :: below) }

/-- Fold an `Except`-producing per-cell operation over `[addr, addr+len)`,
    decorating errors with the failing offset. -/
def foldCells (op : AccessPerms → Word → Except String AccessPerms)
    (ap : AccessPerms) (addr : Word) : Nat → Except String AccessPerms
  | 0 => .ok ap
  | n + 1 =>
      match op ap addr with
      | .error e => .error s!"{e} (cell offset {addr})"
      | .ok ap' => foldCells op ap' (addr + 1) n

/-! ## Range operations (the `PermissionModel` surface) -/

/-- Allocate: one fresh tag rooted at every cell of `[addr, addr+len)`. -/
def sb_own (ap : AccessPerms) (addr : Word) (len : Nat) :
    Except String (AccessPerms × Tag) := do
  let (tag, ap) := freshTag ap
  let ap ← foldCells (fun ap a => ownCell ap a tag) ap addr len
  return (ap, tag)

/-- Read access over a range through `tag`. -/
def sb_read (ap : AccessPerms) (addr : Word) (len : Nat) (tag : Tag) :
    Except String AccessPerms :=
  foldCells (fun ap a => readCell ap a tag) ap addr len

/-- Write access over a range through `tag`. -/
def sb_write (ap : AccessPerms) (addr : Word) (len : Nat) (tag : Tag) :
    Except String AccessPerms :=
  foldCells (fun ap a => writeCell ap a tag) ap addr len

/-- Retag: create a child reference of `kind` from parent `tag` over a range.
    One fresh child tag. Per cell, following Miri's SB:
    - `Mut`: write access via the parent, push the Unique item on top;
    - `Shared` / `Raw false`: read access via the parent, push on top;
    - `Raw true`: **no access**, insert the SharedReadWrite-like item
      directly above the granting item (sibling raws coexist);
    - `TwoPhase`: read access via the parent, insert above the granting
      item (reserved borrow behaves like SharedReadWrite until activation).
    With `prot := true` (function-entry retags at inline seams), the fresh
    tag is registered in the innermost protector frame. -/
def sb_ref (ap : AccessPerms) (addr : Word) (len : Nat) (tag : Tag) (kind : RefKind)
    (prot : Bool := false) : Except String (AccessPerms × Tag) := do
  let (newTag, ap) := freshTag ap
  let newItem := kind.toItem newTag
  let cellOp : AccessPerms → Word → Except String AccessPerms :=
    match kind with
    | .Mut => fun ap a => do pushCell (← writeCell ap a tag) a newItem
    | .Shared | .Raw false => fun ap a => do pushCell (← readCell ap a tag) a newItem
    | .Raw true => fun ap a => insertAboveCell ap a tag newItem
    | .TwoPhase => fun ap a => do insertAboveCell (← readCell ap a tag) a tag newItem
  let ap ← foldCells cellOp ap addr len
  if prot then
    match ap.protFrames with
    | [] => .error "sb-ref: protected retag outside any protector frame"
    | frame :: rest => return ({ ap with protFrames := (newTag :: frame) :: rest }, newTag)
  else
    return (ap, newTag)

/-- Enter a call: push an empty protector frame. -/
def sb_push_frame (ap : AccessPerms) : AccessPerms :=
  { ap with protFrames := [] :: ap.protFrames }

/-- Leave a call: drop the innermost protector frame, ending the
    protection of every tag registered in it. -/
def sb_pop_frame (ap : AccessPerms) : Except String AccessPerms :=
  match ap.protFrames with
  | [] => .error "sb-pop-frame: no active protector frame"
  | _ :: rest => .ok { ap with protFrames := rest }

/-- Deallocate a range through `tag`: at each cell the tag must exist and
    grant write access, no item anywhere in the stack may be protected,
    and the whole stack is then removed (later accesses at these cells
    fail with "no borrow stack"). -/
def sb_dealloc (ap : AccessPerms) (addr : Word) (len : Nat) (tag : Tag) :
    Except String AccessPerms :=
  foldCells
    (fun ap a =>
      match ap.StackMap.find? a with
      | none => .error s!"sb-dealloc: no borrow stack at address {a}"
      | some stack =>
        match splitStack stack tag with
        | none => .error s!"deallocation through tag {tag}: that tag does not exist in the borrow stack at {a}"
        | some (_, item, _) =>
          if !item.grantsWrite then
            .error s!"sb-dealloc: tag {tag} (a read-only item) does not grant deallocation at {a}"
          else
            match firstProtected ap stack with
            | some p =>
                .error s!"deallocating while item for tag {p.tag} is strongly protected"
            | none =>
                .ok { ap with StackMap := ap.StackMap.filter (fun (x, _) => x != a) })
    ap addr len

/-- Kill a reference over a range: pop the item with `tag` if it is on top
    of each cell's stack (and is not the root `Own`). -/
def sb_die (ap : AccessPerms) (addr : Word) (len : Nat) (tag : Tag) :
    Except String AccessPerms :=
  foldCells
    (fun ap a =>
      match ap.StackMap.find? a with
      | none => .error s!"sb-die: no borrow stack at address {a}"
      | some [] => .error "sb-die: stack empty"
      | some (item :: below) =>
          if item.tag == tag then
            match item with
            | .Own _ => .error s!"sb-die: tag {tag} is the allocation root"
            | _ =>
                if ap.isProtected item.tag then
                  .error s!"sb-die: tag {tag} is strongly protected"
                else .ok { ap with StackMap := ap.StackMap.set a below }
          else .error s!"sb-die: top of stack is {item.tag}, expected {tag}")
    ap addr len

end obseq3
