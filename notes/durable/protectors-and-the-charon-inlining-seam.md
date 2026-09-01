# the Charon lowering: protectors, inlining, and every other non-trivial conversion

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

## [FACT] the "passes" are CONCERNS, not stages — it is ONE walk

The header docstring of `lowering.lean` numbers five passes and says, in
parentheses, "fused into one walk". Take that literally. There is a
single `mutual` block (`walkBlock` / `walkCall`, :627-734) entered once
at :796 as `walkBlock crate 8 st0 main 0 0 []`, and every concern —
dropping StorageLive, linearizing gotos, desugaring aggregates,
inlining, seam retags — happens in that one recursive descent,
appending to `st.out`. There is no intermediate IR.

This matters because pass 1 (inline) and pass 5 (seam retags) are
otherwise a paradox: inlining DESTROYS the call boundary, and seam
retags must PRESERVE the only part of it Stacked Borrows can see. If
they were sequential, pass 5 would run over an already-flattened
statement list — call boundaries gone, callee locals renumbered into one
global space — and would have to reconstruct the seams from exactly the
information inlining just erased.

Fusion sidesteps it. When `walkCall` runs it still holds the argument
operands, the callee signature and local types, and the destination, so
it emits the seam AROUND the recursion that does the inlining:

    pushProt                                    :712
    emitSeamBind ... prot := true   (per arg)   :718   <- "pass 5"
    walkBlock crate (depth-1) ... f offset 0 [] :720   <- "pass 1"
    popProt                                     :722
    emitSeamCopy ... prot := false  (return)    :730   <- "pass 5"

The inlined body is nested INSIDE the seam; the retags are emitted
before the callee's statements exist in the output, never recovered
afterwards. Each call node is consumed exactly once and both concerns
are served from it at that moment.

Read off the ordering while it is in front of you: arg retags are
protected (`true`), the return retag is NOT (`false`), and the return
retag is emitted AFTER `popProt` — protectors end before the return
value flows back. That asymmetry is real Miri behaviour and is only
expressible because the retags are a separate thing you can place
relative to the frame.

## [FACT] seam retags are keyed on TYPES, not on calls

`emitSeamCopy` (:222-264) recurses over `UTy`, not over the call graph:
`.ref` -> a `ref` retag, `.boxT` -> a Unique reborrow, `.slice` -> a
runtime-length `refSlice`, `.tup` -> field by field, `.enum` -> write
the discriminant then guard each payload field with `assignIf` on it.
Its own unsupported case is nested references in an enum payload.

So it is not call machinery that happens to be used at calls. It has
three call sites and only two are seams: the third is :303-307, where a
plain `x := *p` needs a retag because Miri retags reference-typed values
loaded through an indirection (`load_invalid_mut` / `load_invalid_shr`).

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


## [FACT] the other non-trivial conversions the lowering performs

All in `src/conformance/lowering.lean`; line numbers as of 2026-09-01.
The header docstring enumerates the passes, but these are the ones that
CHANGE MEANING rather than reshape syntax.

**Linearization — the CFG is erased** (`walkBlock`, :631). Follows
`goto`/call-target edges from `bb0` and emits straight-line code; a
revisited block is `"unsupported: control-flow loop"` (:637). Unwind
edges are never followed; reaching one is
`"unsupported: reached unwind path"` (:663). Real branches (`switchInt`)
are rejected — the target has only forward-only `SkipIf`.

**Asserts are discharged at lowering time, not compiled** (:652-661).
`assert cond expected` is constant-folded: statically true -> dropped,
statically false -> `"unsupported: statically failing assert"`, not
foldable -> `"unsupported: dynamic assert condition"`. So bounds checks
on constant indices vanish INTO the lowering and no bounds-check
machinery ever reaches mirlite.

**A small constant-propagation pass rides along.** `constOf` (:172)
reads literals and const-tracked plain locals from `st.constVals`;
`foldBinOp` (:179) folds Add/Sub/Mul — plain, `Checked` and `Wrapping`
variants ALL to plain `Int` arithmetic — and the six comparisons to 0/1.
DIVERGENCE worth knowing: no overflow or wrapping semantics, so an
overflowing constant expression would silently disagree with Rust
rather than be rejected. Unexercised while every folded value is small.

**Array indices become field projections** (`resolveIdxPlace`, :153;
`resolveIdxOperand` :165, `resolveIdxRvalue` :192, applied from
`emitAssign` :271-272). Arrays are homogeneous tuples, so
`.index (.const n)` and `.index (.fromLocal l)` with `l` const-tracked
both become `UProj.field n`; anything else is
`"unsupported: runtime array index"`. Indices MUST be static — the
model has no dynamic value analysis and needs them to compute layouts.

**Statics are hoisted but their initializers are NOT run**
(`lowerCrate`, :783-793). Each global gets a local after `main`'s, the
prologue materializes it with `uninit` (`hoistInit`), and
`resolveGlobalsStmt` (:760) / `resolveGlobalRoot` (:737) rewrite
`.global gid` roots to those locals. A program reading a static
therefore sees undef where Rust would see the initializer. DOCUMENTED
DIVERGENCE, listed in the header's coverage table.

**Unit aggregates become access-free `uninit`** (`emitAssign`, :330).
Deliberate, and the comment records why: Miri performs no memory access
either, but the assignment still ALLOCATES its destination, and a ZST
local is a real zero-sized allocation that can be borrowed. Before
2026-08-22 this was dropped outright and `&mut z` for `z : ()` failed at
resolution (`local/zst_ref`). This is the interaction that makes ZST
locals and `uninit` load-bearing rather than hypothetical — cf. the
`extendBlock` fix in the `uninit` widening.

**Aggregates are desugared structurally** (:339, :345), because
mirlite HAS NO AGGREGATE RVALUE. `RExpr` (`obseq3/syntax.lean`:95-104)
is nine constructors — `constInit`, `copy`, `ref`, `ptrCast`,
`ptrOffset`, `refSlice`, `exposeAddr`, `fromExposed`, `uninit` — and
every one writes a single value to a single place, so there is nothing
for `(a, b)` to lower INTO.

That is a deliberate choice, not an omission. Under Stacked Borrows the
desugaring is free: Miri builds a tuple by writing each field in turn
and has no distinct "aggregate write" event, and the fields are disjoint
cell ranges so the writes cannot invalidate each other. But an aggregate
rvalue would be expensive in the PROOF — every member of `CoreRhs` costs
a family of simulation leaves, one per destination place shape (the
~1000-line-per-family structure of `const_write.lean` and `ref.lean`) —
and it would prove nothing new, since each desugared field assignment is
already exactly a `copy` or a `constInit`. `fld dst i` just extends the
destination's projection path, which the mother lemma already reasons
about.

Non-empty tuples become per-field assignments; an enum variant writes the
discriminant to payload slot 0 and field `i` to slot `1+i`. Seam retags
into enum payloads are guarded on the discriminant with `assignIf` —
which is where `assignIf` comes from. It exists for enum payload
retags, NOT for general branching.

**Fn pointers are tracked statically** (:309, :324, :445). A flat
local -> defId map (`st.fnPtrs`), propagated through plain copies and
through `transmute`, so a statically-resolvable indirect call can be
inlined (:675). A fn pointer stored into a PROJECTION is rejected —
the map is flat, not per-place.

**Heap and interior mutability are shimmed, not modeled**
(`shimCall`, :375). `Box::new` / `alloc::alloc` / `dealloc` become
dedicated `LStmt.alloc`/`.dealloc`; `Layout` is modeled as its size
word; `UnsafeCell`/`Cell`/`RefCell` become type-directed freeze masks,
with RefCell's borrow flag elided as SB-irrelevant.

**Bookkeeping dropped:** `StorageLive`/`Dead`, `Borrowck`/`FakeRead`,
`Nop`, `PlaceMention`.

## [OBS] the pattern: everything dynamic is resolved statically or rejected

Branches, indices, offsets, arithmetic, asserts, call targets — the
lowering either settles them at compile time or refuses the program.
That is exactly what lets mirlite be a flat straight-line machine with
no value analysis, and it is why the rejected list in the header is
about LANGUAGE complexity rather than missing SB rules.

It also means several of these are SEMANTIC choices the theorem never
sees: uninitialized statics and unchecked constant arithmetic in
particular are divergences from Rust that live entirely above
`compile_correct`.
