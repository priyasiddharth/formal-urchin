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

SharedReadWrite items are grouped: writes through an SRW item pop only
items above its contiguous SRW run (see `writeCell`), and SRW placement
is insert-above-granting (see `insertAboveCell`) — together these
reproduce Miri's SRW-group behavior.

Executable only; preservation lemmas are reconstructed on demand later.
-/

namespace obseq3

abbrev Word := Nat
abbrev Tag := Nat

/-- Surface kinds for reference-creating operations (retags).

    A retag (`sb_ref`) derives a child pointer with one fresh tag from a
    parent tag over a range of cells. The kind decides, per cell:
    - which access (if any) is performed through the PARENT — this is
      what invalidates siblings (a write pops items above the parent, a
      read disables Unique items above it);
    - which `Item` the child contributes (`RefKind.toItem`);
    - where that item is placed: pushed on TOP of the stack, or inserted
      directly ABOVE the granting item (Miri's SharedReadWrite placement,
      which is what lets sibling raw pointers coexist in one group).

    Orthogonal parameters of `sb_ref`, independent of the kind: with
    `prot := true` (fn-entry retags at inline call seams) the fresh tag
    is registered in the innermost protector frame; the freeze `mask`
    marks `UnsafeCell` cells and changes only the `Shared`/`Raw false`
    behavior (see below).

    Kinds originate in the conformance lowering (`toRefKind`, from ULLBC
    `Rvalue::Ref`/`Rvalue::RawPtr` and seam retags) and are carried
    verbatim into the target IR's `Rhs.Borrow`/`Rhs.BorrowRest`; the
    compiler's own internal place-lowering borrows use only `Shared` and
    `Mut`. -/
inductive RefKind
/-- `&T`, a shared reference. Per cell: read access via the parent, then
    push the frozen `Item.Ref` on top (read-only; killed by any writer
    below). Cells the freeze mask marks interior-mutable instead get a
    SharedReadWrite `RawPtr true` inserted above the granting item with
    NO access — `UnsafeCell` contents stay writable behind `&`. -/
| Shared
/-- `&mut T`, a unique reference. Per cell: write access via the parent
    (pops everything above it), then push `Item.MutRef` (Unique) on top.
    Also the kind used for Box retags and for every compiler-internal
    borrow minted while lowering assignment destinations. -/
| Mut
/-- Raw pointers. `Raw true` (`*mut T`, `&raw mut`): NO parent access —
    the SharedReadWrite `RawPtr true` item is inserted directly above the
    granting item, so sibling mutable raws join one group instead of
    invalidating each other. `Raw false` (`*const T`): like `Shared` —
    read access plus a read-only `RawPtr false` pushed on top, with
    masked (`UnsafeCell`) cells getting the access-free SharedReadWrite
    insertion instead. -/
| Raw (mutbl : Bool)
/-- A reserved two-phase `&mut` (ULLBC `TwoPhaseMut`, from `&mut` in
    autoref positions). Per cell: only a READ parent access, then a
    SharedReadWrite-like `RawPtr true` inserted above the granting item —
    writable and read-surviving until activation, matching Miri's SB
    treatment of reservations (`two_phase_aliasing_violation` is the
    conformance witness). -/
| TwoPhase
deriving Inhabited, Repr, BEq, DecidableEq

/-- Borrow-stack items. `Disabled` is a Unique that was invalidated by a
    read: it grants nothing but KEEPS ITS PLACE in the stack — removing
    it would merge the SharedReadWrite groups on either side (miri's
    disable_mut_does_not_merge_srw tests exactly this). -/
inductive Item
| Own (tag : Tag)
| MutRef (tag : Tag)
| Ref (tag : Tag)
| RawPtr (mutbl : Bool) (tag : Tag)
| Disabled (tag : Tag)
deriving Inhabited, Repr, BEq

namespace Item

def tag : Item → Tag
| Own t => t
| MutRef t => t
| Ref t => t
| RawPtr _ t => t
| Disabled t => t

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

/-- SharedReadWrite items (the write-grouping class). -/
def isSrw : Item → Bool
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

/-- The reserved wildcard tag: pointers produced by int-to-ptr casts.
    Accesses through it resolve to the topmost *exposed* granting item.
    `freshTag` starts at 1 so real tags never collide with it. -/
def wildcardTag : Tag := 0

/-- `protFrames` models Miri's call-frame protectors: a stack of tag sets,
    one frame per active (inlined) call. A tag in any active frame is
    *protected*: any access that would pop or disable its items is UB
    (weakly for SharedReadWrite items). Frames are pushed/popped by the
    `pushProtectors`/`popProtectors` pseudo-statements the loader emits
    at inline seams. `exposed` is the set of tags leaked by ptr-to-int
    casts — the candidates for wildcard accesses. -/
structure AccessPerms where
  StackMap : SB
  NextTag : Tag
  protFrames : List (List Tag) := []
  exposed : List Tag := []
deriving Inhabited, Repr, BEq

def AccessPerms.init : AccessPerms := { StackMap := [], NextTag := 1 }

/-- Expose a tag (ptr-to-int cast). Exposing the wildcard is a no-op. -/
def sb_expose (ap : AccessPerms) (tag : Tag) : AccessPerms :=
  if tag == wildcardTag then ap
  else { ap with exposed := tag :: ap.exposed }

/-- Resolve a wildcard access at one cell: the topmost exposed item that
    grants the access (Miri's optimistic wildcard resolution). Takes the
    exposed-tag set directly so per-cell content functions can be stated
    over `(protFrames, exposed)` instead of a full `AccessPerms`. -/
def resolveWildcardIn (exposed : List Tag) (stack : BorrowStack) (needWrite : Bool) :
    Option Tag :=
  (stack.find? (fun k =>
    match k with
    | .Disabled _ => false
    | _ => exposed.contains k.tag && (!needWrite || k.grantsWrite))).map (·.tag)

def resolveWildcard (ap : AccessPerms) : BorrowStack → Bool → Option Tag :=
  resolveWildcardIn ap.exposed

def isProtectedIn (pf : List (List Tag)) (tag : Tag) : Bool :=
  pf.any (·.contains tag)

def AccessPerms.isProtected (ap : AccessPerms) (tag : Tag) : Bool :=
  isProtectedIn ap.protFrames tag

/-- First item whose protection blocks a pop. Protection is *weak* on
    SharedReadWrite items (`RawPtr true`): Miri allows popping and even
    deallocating protected interior-mutable/raw items — only Unique and
    frozen protected items make a pop UB. -/
def firstProtectedIn (pf : List (List Tag)) (items : List Item) : Option Item :=
  items.find? (fun k =>
    match k with
    | .RawPtr true _ => false
    | _ => isProtectedIn pf k.tag)

def firstProtected (ap : AccessPerms) : List Item → Option Item :=
  firstProtectedIn ap.protFrames

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

/-- The stack-level content of a read access (factored out of `readCell`
    for the compiler-correctness proofs): the granting item may be any
    kind; items above it that are `poppedByRead` (Unique) are DISABLED in
    place — unless one of them is protected, which is UB. -/
def readCellContent (pf : List (List Tag)) (ex : List Tag) (addr : Word) (tag : Tag)
    (stack : BorrowStack) : Except String BorrowStack :=
  match (if tag == wildcardTag
         then (resolveWildcardIn ex stack false).elim
                (Except.error s!"read access using <wildcard>: no exposed tags have suitable permission in the borrow stack at {addr}")
                Except.ok
         else .ok tag) with
  | .error e => .error e
  | .ok tag =>
  match splitStack stack tag with
  | none => .error s!"sb-read: tag {tag} does not exist in the borrow stack at {addr}"
  | some (above, item, below) =>
    match item with
    | .Disabled _ =>
        .error s!"sb-read: tag {tag} does not exist in the borrow stack at {addr} (disabled)"
    | _ =>
    let hit := above.filter (·.poppedByRead)
    match firstProtectedIn pf hit with
    | some p =>
        .error s!"sb-read: not granting read access to tag {tag} at {addr} because that would remove item for tag {p.tag} which is strongly protected"
    | none =>
      -- DISABLE invalidated Uniques (do not remove): removal would
      -- merge adjacent SharedReadWrite groups
      let above' := above.map (fun k => if k.poppedByRead then .Disabled k.tag else k)
      .ok (above' ++ item :: below)

/-- Read access at one cell through `tag`. -/
def readCell (ap : AccessPerms) (addr : Word) (tag : Tag) : Except String AccessPerms :=
  match ap.StackMap.find? addr with
  | none => .error s!"sb-read: no borrow stack at address {addr}"
  | some stack =>
    match readCellContent ap.protFrames ap.exposed addr tag stack with
    | .error e => .error e
    | .ok v => .ok { ap with StackMap := ap.StackMap.set addr v }

/-- The stack-level content of a write access (factored out of `writeCell`
    so the compiler-correctness proofs can characterize per-cell folds):
    the granting item must grant writes; everything above it is popped —
    unless one of the popped items is protected, which is UB. -/
def writeCellContent (pf : List (List Tag)) (ex : List Tag) (addr : Word) (tag : Tag)
    (stack : BorrowStack) : Except String BorrowStack :=
  match (if tag == wildcardTag
         then (resolveWildcardIn ex stack true).elim
                (Except.error s!"write access using <wildcard>: no exposed tags have suitable permission in the borrow stack at {addr}")
                Except.ok
         else .ok tag) with
  | .error e => .error e
  | .ok tag =>
  match splitStack stack tag with
  | none => .error s!"sb-write: tag {tag} does not exist in the borrow stack at {addr}"
  | some (above, item, below) =>
    match item with
    | .Disabled _ =>
        .error s!"sb-write: tag {tag} does not exist in the borrow stack at {addr} (disabled)"
    | _ =>
    if item.grantsWrite then
      -- SharedReadWrite grouping: a write through an SRW item stays
      -- within its contiguous SRW run — only items above the whole
      -- group are popped (miri's disable_mut_does_not_merge_srw is
      -- the negative test: SRWs separated by a Unique are distinct
      -- groups and still invalidate each other)
      let (srwRun, rest) :=
        if item.isSrw then
          let grp := above.reverse.takeWhile Item.isSrw
          (grp.reverse, above.take (above.length - grp.length))
        else ([], above)
      match firstProtectedIn pf rest with
      | some p =>
          .error s!"sb-write: not granting write access to tag {tag} at {addr} because that would remove item for tag {p.tag} which is strongly protected"
      | none =>
          .ok (srwRun ++ item :: below)
    else
      .error s!"sb-write: tag {tag} (a read-only item) does not grant write access at {addr}"

/-- Write access at one cell through `tag`. -/
def writeCell (ap : AccessPerms) (addr : Word) (tag : Tag) : Except String AccessPerms :=
  match ap.StackMap.find? addr with
  | none => .error s!"sb-write: no borrow stack at address {addr}"
  | some stack =>
    match writeCellContent ap.protFrames ap.exposed addr tag stack with
    | .error e => .error e
    | .ok v => .ok { ap with StackMap := ap.StackMap.set addr v }

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
    match (if tag == wildcardTag
           then (resolveWildcard ap stack false).elim
                  (Except.error s!"retag using <wildcard>: no exposed tags have suitable permission in the borrow stack at {addr}")
                  Except.ok
           else .ok tag) with
    | .error e => .error e
    | .ok tag =>
    match splitStack stack tag with
    | none => .error s!"sb-insert: tag {tag} does not exist in the borrow stack at {addr}"
    | some (_, .Disabled _, _) =>
        .error s!"sb-insert: tag {tag} does not exist in the borrow stack at {addr} (disabled)"
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

/-- Index-carrying variant of `foldCells` (the cell op sees its offset,
    needed by masked retags). Top-level rather than a nested `let rec` so
    the compiler-correctness proofs can reason about it. -/
def foldCellsIdx (op : AccessPerms → Word → Nat → Except String AccessPerms)
    (ap : AccessPerms) (addr : Word) (i len : Nat) : Except String AccessPerms :=
  if i < len then
    match op ap (addr + i) i with
    | .error e => .error s!"{e} (cell offset {i})"
    | .ok ap' => foldCellsIdx op ap' addr (i + 1) len
  else .ok ap
  termination_by len - i

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
    `mask` marks the cells inside `UnsafeCell` ranges (type-directed, from
    the pointee type): for `Shared` and `Raw false` retags, masked cells
    get a SharedReadWrite item inserted above the granting item with NO
    access (interior mutability), instead of the frozen item + read.
    With `prot := true` (function-entry retags at inline seams), the fresh
    tag is registered in the innermost protector frame. -/
def sb_ref (ap : AccessPerms) (addr : Word) (len : Nat) (tag : Tag) (kind : RefKind)
    (prot : Bool := false) (mask : List Bool := []) :
    Except String (AccessPerms × Tag) := do
  let (newTag, ap) := freshTag ap
  let newItem := kind.toItem newTag
  let cellOp : AccessPerms → Word → Nat → Except String AccessPerms :=
    match kind with
    | .Mut => fun ap a _ => do pushCell (← writeCell ap a tag) a newItem
    | .Shared | .Raw false => fun ap a i =>
        if mask.getD i false then
          insertAboveCell ap a tag (.RawPtr true newTag)
        else do
          pushCell (← readCell ap a tag) a newItem
    | .Raw true => fun ap a _ => insertAboveCell ap a tag newItem
    | .TwoPhase => fun ap a _ => do insertAboveCell (← readCell ap a tag) a tag newItem
  let ap ← foldCellsIdx cellOp ap addr 0 len
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

/-- The stack-level content of a `die` at one cell (factored for the
    compiler-correctness proofs): pop the item with `tag` if it is on top
    and is neither the allocation root nor protected. -/
def dieCellContent (pf : List (List Tag)) (tag : Tag) : BorrowStack → Except String BorrowStack
  | [] => .error "sb-die: stack empty"
  | item :: below =>
      if item.tag == tag then
        match item with
        | .Own _ => .error s!"sb-die: tag {tag} is the allocation root"
        | _ =>
            if isProtectedIn pf item.tag then
              .error s!"sb-die: tag {tag} is strongly protected"
            else .ok below
      else .error s!"sb-die: top of stack is {item.tag}, expected {tag}"

/-- Kill a reference over a range: pop the item with `tag` if it is on top
    of each cell's stack (and is not the root `Own`). -/
def sb_die (ap : AccessPerms) (addr : Word) (len : Nat) (tag : Tag) :
    Except String AccessPerms :=
  foldCells
    (fun ap a =>
      match ap.StackMap.find? a with
      | none => .error s!"sb-die: no borrow stack at address {a}"
      | some stack =>
          match dieCellContent ap.protFrames tag stack with
          | .error e => .error e
          | .ok below => .ok { ap with StackMap := ap.StackMap.set a below })
    ap addr len

end obseq3
