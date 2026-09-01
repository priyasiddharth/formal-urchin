# protectors, and where they come from: the Charon inlining seam

Written 2026-09-01, from reading `syntax.lean`, both semantics,
`sb.lean`, `compile.lean` and `src/conformance/lowering.lean`. Answers
the recurring question "who decides which tags are protected?".

## [FACT] mirlite has NO function calls

    inductive Stmt (Γ : Ctx)
    | assign | assignIf | alloc | dealloc
    | pushProtectors | popProtectors | halt

A program is a flat `List (Stmt Γ)`. No call, no return, no function
table. Protector frames are the ONLY call-shaped structure in the
machine, and they are pushed by explicit statements.

## [FACT] protection is a MEMBERSHIP SET, not a field on an item

`Item` is a kind plus a bare `Tag` (`Own`/`MutRef`/`Ref`/`RawPtr`/
`Disabled`); `Tag` is a `Nat`. Nothing on a stack item says
"protected". The set lives beside the stacks:

    AccessPerms.protFrames : List (List Tag)     -- one frame per active inlined call
    isProtectedIn pf tag := pf.any (·.contains tag)

Consequences:

* every check (`dieCellContent`, `firstProtectedIn`, `sb_dealloc`)
  takes `pf` and looks the tag up — which is why the per-cell content
  functions are stated over `(protFrames, exposed)` rather than a whole
  `AccessPerms`;
* `popProtectors` un-protects a whole batch at once by dropping the head
  frame, touching no stack and no item;
* where the item KIND matters is the WEAKNESS of protection, not its
  presence: `firstProtectedIn` returns `false` for `RawPtr true`
  (SharedReadWrite), so those may still be popped — Miri's rule,
  encoded as kind-dispatch at the check site.

## [FACT] exactly three writes touch `protFrames`

    sb_push_frame ap := { ap with protFrames := [] :: ap.protFrames }
    sb_pop_frame  ap := match ap.protFrames with
                        | []          => .error "no active protector frame"
                        | _ :: rest   => .ok { ap with protFrames := rest }
    sb_ref ... prot ... := ... if prot then
                             match ap.protFrames with
                             | [] => .error "protected retag outside any protector frame"
                             | frame :: rest => ({ ap with protFrames := (newTag :: frame) :: rest }, newTag)

So a tag enters a frame in ONE place, and:

1. it is the FRESHLY MINTED child (`newTag`), never the parent;
2. it goes into the INNERMOST frame only — a retag can never register
   into an enclosing call's frame;
3. it happens AFTER the per-cell retag fold, as a separate step;
4. no active frame is an ERROR, not a no-op: a protected retag outside a
   bracket is UB on both machines by construction.

`push` registers nothing — it conses an EMPTY frame.

## [FACT] the frames and the `prot` flags are produced by the LOADER

`src/conformance/lowering.lean`'s `inlineCall` emits them, wrapped
around the spliced callee body:

    st := pushProt line                                  -- enter the frame
    for each arg: emitSeamBind st line prot:=TRUE ...    -- fn-entry retags
    walkBlock (depth - 1) ... f ...                      -- the callee, INLINED
    st := popProt line                                   -- leave; protection ends
    ... emitSeamCopy st line prot:=FALSE dest retTy ...  -- return value, unprotected

So the tags in a frame are exactly the fresh tags of that call's
ARGUMENT retags, one per reference-typed component — `emitSeamCopy`
recurses through the type, so refs inside tuples and enum payloads each
get their own (enum payloads guarded on the discriminant with
`assignIf`). The RETURN value is retagged after `popProt`, unprotected,
matching Miri.

## [FACT] the pipeline, and what it cannot express

Rust -> Charon -> ULLBC JSON -> untyped AST (`ullbc_ast.lean`) ->
lowering -> mirlite `Prog`. Calls do not survive. Constraints that bound
what the conformance corpus can even state:

* inlining is bounded at DEPTH 8; recursion is rejected
  (`"call inlining depth exceeded (recursion?)"`), not modeled —
  termination is static;
* indirect/unresolved calls and bodyless functions are rejected, except
  a few allocator shims (`Box::new`, `alloc`, `dealloc`,
  `Layout::from_size_align_unchecked`) lowered to dedicated statements;
* boxes retag as a `Unique` reborrow with the same protector machinery.
  KNOWN DIVERGENCE, flagged in the source: Miri's box protection is WEAK
  (dealloc allowed during the call) while the model's protector blocks
  pops identically. The comment says the dealloc difference is
  unexercised.

## [FACT] none of this is verified — it is upstream of `compile_correct`

Charon's extraction, the inlining, and the choice of where to put
`pushProt` / `prot := true` are all OUTSIDE the theorem.
`compile_correct` starts from whatever `Prog` comes out and proves
mirlite = oseair; it does not prove Rust = mirlite. The conformance
suite is what tests that upper edge, by running real Charon artifacts.

See also [[what-compile-correct-actually-says]].

## [OBS] why the two protector statements are the CHEAPEST widening left

Both compile by pure pass-through — one instruction each — and the two
executions are LITERALLY the same expression, since `M = MSB` on both
sides:

    .ok    { state with perms := M.pushFrame state.perms, pc := state.pc + 1 }   -- mirlite
    Ok     { state with perms := M.pushFrame state.perms, pc := state.pc + 1 }   -- oseair

And `PermSim`'s frame conjunct is `ListRel (TagListSim ρt) src.protFrames
tgt.protFrames`, with `ListRel R (a::as) (b::bs) = R a b ∧ ListRel R as bs`:

* PUSH: both cons `[]`, and the new obligation is
  `TagListSim ρt [] []` = `True`. Rebuild `PermSim` with `⟨trivial, h⟩`
  — no tag reasoning at all.
* POP: both drop the head; the tail relation is the second component of
  the existing conjunction. The error case matches too, because
  `ListRel` forces equal lengths, so one machine's `protFrames` is `[]`
  exactly when the other's is.

No memory, no registers, no renames, no `placeRegMap` change. Far below
the cost of any rvalue, and unlike `uninit` nothing needs generalizing
first. `CoreStmt` currently excludes both.
