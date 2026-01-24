namespace obseq

abbrev Word := Nat
abbrev Tag := Nat

inductive RefKind
| Own (tag: Tag)
| MutRef (tag: Tag)
| Ref (tag: Tag)
| RawPtr (tag: Tag)
deriving Inhabited, Repr, BEq

def RefKind.tag : RefKind → Tag
| Own t => t
| MutRef t => t
| Ref t => t
| RawPtr t => t

def RefKind.isMb : RefKind → Bool
| MutRef _ => true
| _ => false

def RefKind.isRaw : RefKind → Bool
| RawPtr _ => true
| _ => false

abbrev BorrowStack := List RefKind

/--
A StackedMap (SB) maps a memory location (Addr) to a permission stack.
--/
abbrev SB := List (Word × BorrowStack)

def SB.find? (sb : SB) (addr : Word) : Option BorrowStack :=
  match sb with
  | [] => none
  | (a, stack) :: rest => if a == addr then some stack else SB.find? rest addr

def SB.insert (sb : SB) (addr : Word) (stack : BorrowStack) : SB :=
  (addr, stack) :: sb.filter (fun (a, _) => a != addr)

structure AccessPerms where
  StackMap: SB
  NextTag: Tag
deriving Inhabited, Repr, BEq

def freshTag (ap : AccessPerms) : Tag × AccessPerms :=
  (ap.NextTag, { ap with NextTag := ap.NextTag + 1 })

inductive SBResult
| Ok (ap : AccessPerms)
| Err (msg : String)
deriving Inhabited, Repr

open SBResult

-- Rule: sb-own
-- Premise: sb[a] = [], g is fresh
-- Conclusion: sb[a] = [(g, o)]
def sb_own (ap : AccessPerms) (addr : Word) : SBResult × Tag :=
  match ap.StackMap.find? addr with
  | some [] | none => -- Treat none as empty for initialization or explicit empty check?
    -- Paper says sb[a] = [], but in implementation usually we allocate and init.
    -- Assuming alloc calls this.
    let (tag, ap') := freshTag ap
    let stack := [RefKind.Own tag]
    let newSB := ap'.StackMap.insert addr stack
    (Ok { ap' with StackMap := newSB }, tag)
  | some _ => (Err s!"sb-own: stack at {addr} not empty", 0)

-- Helper to find item in stack and split it: returns (above, item, below)
def splitStack (stack : BorrowStack) (tag : Tag) : Option (BorrowStack × RefKind × BorrowStack) :=
  let rec aux (acc : BorrowStack) (rem : BorrowStack) : Option (BorrowStack × RefKind × BorrowStack) :=
    match rem with
    | [] => none
    | item :: rest =>
      if item.tag == tag then some (acc.reverse, item, rest)
      else aux (item :: acc) rest
  aux [] stack

-- Rule: sb-read-safe
-- Premise: sb[a] = x ++ (g, k) :: y, k \in {o, mb, b}
-- Conclusion: sb[a] = filter(x, ¬mb) ++ (g, k) :: y
def sb_read_safe (ap : AccessPerms) (addr : Word) (tag : Tag) : SBResult :=
  match ap.StackMap.find? addr with
  | none => Err s!"sb-read-safe: address {addr} not found"
  | some stack =>
    match splitStack stack tag with
    | none => Err s!"sb-read-safe: tag {tag} not found in stack at {addr}"
    | some (x, item, y) =>
      match item with
      | RefKind.Own _ | RefKind.MutRef _ | RefKind.Ref _ =>
        let x' := x.filter (fun k => !k.isMb)
        let newStack := x' ++ item :: y
        let newSB := ap.StackMap.insert addr newStack
        Ok { ap with StackMap := newSB }
      | RefKind.RawPtr _ => Err s!"sb-read-safe: tag {tag} is RawPtr, expected o, mb, or b"

-- Rule: sb-read-use-raw
-- Premise: sb[a] = x ++ (g, r) :: y, ∀ kx \in x. kx = r
-- Conclusion: sb[a] unchanged
def sb_read_use_raw (ap : AccessPerms) (addr : Word) (tag : Tag) : SBResult :=
  match ap.StackMap.find? addr with
  | none => Err s!"sb-read-use-raw: address {addr} not found"
  | some stack =>
    match splitStack stack tag with
    | none => Err s!"sb-read-use-raw: tag {tag} not found in stack at {addr}"
    | some (x, item, _y) =>
      match item with
      | RefKind.RawPtr _ =>
        if x.all (fun k => k.isRaw) then Ok ap
        else Err s!"sb-read-use-raw: items above raw pointer {tag} are not all raw"
      | _ => Err s!"sb-read-use-raw: tag {tag} is not RawPtr"

-- Rule: sb-use-mb
-- Premise: sb[a] = x ++ (g, k) :: y, k \in {o, mb}
-- Conclusion: sb[a] = (g, k) :: y
def sb_use_mb (ap : AccessPerms) (addr : Word) (tag : Tag) : SBResult :=
  match ap.StackMap.find? addr with
  | none => Err s!"sb-use-mb: address {addr} not found"
  | some stack =>
    match splitStack stack tag with
    | none => Err s!"sb-use-mb: tag {tag} not found in stack at {addr}"
    | some (_x, item, y) =>
      match item with
      | RefKind.Own _ | RefKind.MutRef _ =>
        let newStack := item :: y
        let newSB := ap.StackMap.insert addr newStack
        Ok { ap with StackMap := newSB }
      | _ => Err s!"sb-use-mb: tag {tag} is not Own or MutRef"

-- Rule: sb-mv
-- Premise: sb[a] = x ++ [(g, o)], k \in {o}
-- Conclusion: sb[a] = []
def sb_mv (ap : AccessPerms) (addr : Word) (tag : Tag) : SBResult :=
  match ap.StackMap.find? addr with
  | none => Err s!"sb-mv: address {addr} not found"
  | some stack =>
    -- Check if (g, o) is at the bottom. The paper says x ++ [(g, o)].
    -- Since our list is top-first (stack), "bottom" is the last element.
    -- Wait, stacks usually grow at the head.
    -- If `stack = x ++ (g, k) :: y` usually means `x` is top.
    -- So `x ++ [(g, o)]` means `(g, o)` is at the bottom (end of list).
    match stack.reverse with
    | item :: _rest => -- item is the bottom
      if item.tag == tag then
        match item with
        | RefKind.Own _ =>
           let newSB := ap.StackMap.insert addr []
           Ok { ap with StackMap := newSB }
        | _ => Err s!"sb-mv: tag {tag} is not Own"
      else Err s!"sb-mv: tag {tag} is not at the bottom of the stack"
    | [] => Err s!"sb-mv: stack empty"


-- Rule: sb-new-mut-ref
-- Premise: use(a, g) -> sb', g' fresh, rf \in {mb, r} -- Wait, table says {mb, r}.
-- The rule name is `sb-new-mut-ref` but it seems to cover raw too?
-- "ref(rf, a, g) ... rf \in {mb, r}"
-- Conclusion: sb[a] = (g', rf) :: sb'[a]
def sb_new_mut_ref (ap : AccessPerms) (addr : Word) (tag : Tag) (kind : RefKind -> Bool) : SBResult × Tag :=
  -- First perform use(a, g). Note: `use` corresponds to `sb-use-mb`.
  -- Wait, if creating a Raw pointer, do we use `sb-use-mb`?
  -- Table says: `<use(a, g), sb> -> sb'`.
  -- If `use` invokes `sb-use-mb`, then yes.
  -- But `sb-use-mb` requires `k \in {o, mb}`.
  -- What if I create a raw pointer from a shared ref? That shouldn't be allowed by `sb-use-mb`.
  -- The paper says `ref(rf, a, g)` premise is `use(a, g)`.
  -- This implies you need write access to create a mutable ref or raw pointer.
  match sb_use_mb ap addr tag with
  | Ok ap' =>
    let (newTag, ap'') := freshTag ap'
    match ap''.StackMap.find? addr with
    | some stack =>
       -- kind is a constructor function? No, let's just pass the kind constructor.
       -- But I need to construct it with newTag.
       -- Let's make this function take a constructor.
       -- Ideally I should pass `RefKind.MutRef` or `RefKind.RawPtr`.
       -- But those are constructors.
       -- I'll define specialized functions or take a sum type.
       (Ok ap'', newTag) -- Placeholder return
    | none => (Err "sb-new-mut-ref: stack gone?", 0)
  | Err msg => (Err msg, 0)

-- Helper for specific kinds
def sb_new_mut_ref_kind (ap : AccessPerms) (addr : Word) (tag : Tag) (mkKind : Tag -> RefKind) : SBResult × Tag :=
  match sb_use_mb ap addr tag with
  | Ok ap' =>
    let (newTag, ap'') := freshTag ap'
    match ap''.StackMap.find? addr with
    | some stack =>
       let newItem := mkKind newTag
       let newStack := newItem :: stack
       let newSB := ap''.StackMap.insert addr newStack
       (Ok { ap'' with StackMap := newSB }, newTag)
    | none => (Err "sb-new-mut-ref: stack gone?", 0)
  | Err msg => (Err msg, 0)

-- Rule: sb-new-ref
-- Premise: read(a, g) -> sb', g' fresh
-- Conclusion: sb[a] = (g', b) :: sb'[a]
def sb_new_ref (ap : AccessPerms) (addr : Word) (tag : Tag) : SBResult × Tag :=
  match sb_read_safe ap addr tag with
  | Ok ap' =>
    let (newTag, ap'') := freshTag ap'
    match ap''.StackMap.find? addr with
    | some stack =>
       let newItem := RefKind.Ref newTag
       let newStack := newItem :: stack
       let newSB := ap''.StackMap.insert addr newStack
       (Ok { ap'' with StackMap := newSB }, newTag)
    | none => (Err "sb-new-ref: stack gone?", 0)
  | Err msg => (Err msg, 0)

-- Rule: sb-die
-- Premise: sb[a] = (g, k) :: y
-- Conclusion: sb[a] = y
def sb_die (ap : AccessPerms) (addr : Word) (tag : Tag) : SBResult :=
  match ap.StackMap.find? addr with
  | none => Err s!"sb-die: address {addr} not found"
  | some stack =>
    match stack with
    | item :: y =>
      if item.tag == tag then
        let newSB := ap.StackMap.insert addr y
        Ok { ap with StackMap := newSB }
      else Err s!"sb-die: top of stack is {item.tag}, expected {tag}"
    | [] => Err "sb-die: stack empty"

end obseq
