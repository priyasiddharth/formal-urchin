# Already-rejected design alternatives — don't re-litigate

Load this when a "wouldn't it be simpler if we..." question comes up.
Each rejection has recorded reasoning; revisit only if the cited
bottleneck changes.

[FACT] **CompCert-style `Block × Z` addresses** — rejected 2026-04-30.
Would only remove the cross-allocation freshness arithmetic
(`AllocatorProofSpec.alloc_fresh` plays the block-separation role);
does NOT touch the actual bottleneck, stacked-borrows frame lemmas for
intra-allocation aliasing, which are orthogonal to address
representation. Migration cost across `Val.Ptr` matches and all of
`sb.lean` is high. → obseq2-comparison.md 2026-04-30. (Note: the
2026-06-17 identity-on-domain decision strengthened the flat-address
choice — lockstep bump allocators make ρa/ρt identity, which a block
model would have obscured.)

[FACT] **Iris / separation logic for non-interference** — rejected in
the v2 plan. Explicit CompCert-like footprint + frame-invariant record
instead; Iris worth revisiting only if the permission-module boundary
needs abstract ownership/ghost state/modular client specs.
→ src/obseq/obseq2.md §2

[FACT] **Fully typed (intrinsic) OSEA-IR** — rejected 2026-04-25 in
favor of a proof-side WF layer (`RegValWF`/`InstrWF`/`CompiledWF`).
Typed target IR only pays off if type preservation is a goal; for
behavioral simulation it is unnecessary. Caveat: the WF layer was
never actually built (only a comment at common.lean:284), so its
intended static discharge of write-bounds obligations is instead done
directly (identity conjunct + affine arithmetic).
→ obseq2-comparison.md 2026-04-25 + 2026-06-17 correction

[FACT] **8th "slice" conjunct on CompilerInv for fragment placement** —
rejected 2026-04-28 in favor of the code-map representation
(`Prog = Nat → Option Instr`), which closes placement goals by `simp`
by construction and supports future branch backpatching. The invariant
grows only for *semantic* facts (the 2026-06-17 identity conjuncts are
in that category, hence not a violation). → obseq2-comparison.md 2026-04-28

[FACT] **`PermSim` renamed-permission relation / deriving ρ-identity
on the fly** — both rejected 2026-06-17 in favor of the
identity-on-domain conjunct. PermSim is CompCert-`inject`-faithful but
heavier and touches permission.lean; on-the-fly derivation gets stuck
(identity is not derivable without a global fact).
→ rho-maps-are-identity-on-domain.md

[FACT] **MIR's `Operand` layer in `RExpr`** — rejected 2026-09-14.
mirlite has no `Operand` type: MIR's `Rvalue::Use(Operand)` is inlined as
two rvalue constructors (`copy p`, `constInit v`), `Move` is folded into
`copy` (nothing deinitializes a source), and every other rvalue takes a
`Place` rather than an operand — so a constant cannot be cast, which the
ingestion admits with `unsupported "ptr/int cast of a non-place"`
(src/conformance/ullbc_ast.lean:665).

Copying MIR faithfully was considered and rejected on measurement: of the
41 unsupported ULLBC tests, ZERO are blocked by the operand restriction.
The manifest's reasons are heap containers and trait objects (Box, Rc,
String, Vec, custom allocators, vtables — ~12), protectors (~8), threads
(3), slices (3), interior mutability (3), named ADTs, transmute,
closures, fn pointers, two-phase, MaybeUninit, unions. The binding
constraint is the type/feature frontier, not the rvalue grammar.

    python3 -c "import json,collections; m=json.load(open('conformance/manifest.json')); \
      c=collections.Counter(t['reason'] for t in m if t.get('status')=='unsupported'); \
      [print(n,r) for r,n in c.most_common()]"

The cost side is the reason not to do it anyway: the FLAT, place-only
grammar is what makes `ValuePkg` work — one non-recursive dispatch in
`compileRExprPreChecked`, and the source shape vanishing behind the
package (see one-leaf-per-destination-shape.md). Operands would multiply
the packages per rvalue (a cast of a constant is not the package a cast
of a place is) and re-open the compiler to materialize constants into
registers before casting, adding instructions and fragment lemmas under
both audit roots.

**Revisit if:** an `unsupported "…non-place"` ever becomes a binding
constraint. Even then the cheap fix is in the INGESTION — hoist the
constant into a temporary local and emit two statements — which keeps
mirlite's grammar and the whole proof surface fixed.
