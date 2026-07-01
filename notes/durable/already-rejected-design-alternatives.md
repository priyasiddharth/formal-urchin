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
