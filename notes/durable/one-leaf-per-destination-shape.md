# One leaf per DESTINATION shape: `ValuePkg` and `StoreStep`

Load this before writing any new simulation leaf, or when adding an
rvalue to `CoreRhs`. The short version: do not write a leaf. Write a
value package.

[FACT, 2026-09-14] **A leaf depends on its rvalue only through
`ValuePkg`.** The package names the rvalue's whole compiled contribution
abstractly — as `run (compileRExprPreChecked rhs) csA` and nothing else —
with the store instruction, the destination register and the tag renaming
all existential. Once a leaf refers to the pre-phase only by that name,
the rvalue's SOURCE shape disappears from the leaf too: one
code-inclusion obligation covers a chain source, a projection's
`Borrow`/`Die` bracket, and a retag alike.
→ src/obseq3/proof/spine.lean, `def ValuePkg`

[FACT, 2026-09-14] **So there are five leaves and two recursions in the
whole development**, keyed on the destination and shared by copy, both
integer-pointer casts, ref, `constInit` and `uninit`:

    storereg_local_simulation        bound local
    storereg_localfresh_simulation   unbound local (allocates the root)
    storereg_chaindst_simulation     `*chain :=`
    storereg_projdst_simulation      `chain.f :=`, EITHER offset
    storereg_projlocalfresh_…        `loc.f :=`, `loc` unbound
    storereg_projdst_recursion       peels nesting, flattens a deref root

`copy.lean`, `ref.lean` and `const_write.lean` contain zero leaves.
→ src/obseq3/proof/spine.lean

[FACT, 2026-09-14] **The store instruction is abstract too.** Seams take
`mkStore : Register → Instr` and

    StoreStep compProg sR bound mkStore vals

— "executing this instruction performs the write, at any state whose
registers agree with `sR`'s below `bound`". `bound` is the only subtle
field: it is what carries a REGISTER store's operand across a destination
lowering that allocates registers of its own. `StoreStep.rstore` builds
the predicate from the operand's lookup plus that frame;
`StoreStep.cstore` needs only the value list's length. The two stores are
otherwise identical — both reduce to the same `writeThroughPtr`, and even
the invalid-pointer string they hand it is unobservable once the write
succeeds (`writeThroughPtr_msg_irrel`).
→ src/obseq3/proof/common.lean, `def StoreStep`

[FACT, 2026-09-14] **`ValuePkg` carries one conjunct OUTSIDE its
code-inclusion gate**: the place map of the post-rvalue state. A
non-local destination is lowered AFTER the rvalue's code, so its
`PlaceInputsMapped` has to transfer before any code fact exists. The
gated copy cannot do it, and this is the one place where the abstraction
had to give.

## Why this matters

A new rvalue costs a value package and nothing else — no leaf, no
fragment lemma, no dispatcher. Mirror `ValuePkg.of_readPkgLowered` for a
register-store rvalue, `ValuePkg.of_pureCStore` for a constant-store one.
The collapse that established this took the proof directory from 27,604
to 15,277 lines; re-introducing a per-rvalue leaf would undo it.

`ptrCast` is the rvalue this does NOT cover, and the reason is precise —
see ptrcast-is-a-memcpy-not-a-store.md.

## See also

- ptrcast-is-a-memcpy-not-a-store.md
- lowering-sim-as-a-package.md
- raw-pointer-provenance-is-the-wildcard-tag.md
