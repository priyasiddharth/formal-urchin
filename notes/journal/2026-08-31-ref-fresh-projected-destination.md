# ref: a projected destination over an unbound root

Date: 2026-08-31
Tags: obseq3, ref, regime-B, unbound-root, extendBlock, tooling

## [FACT] the σ-sized root changes the ρa extension, and little else

`ref_projzero_fresh_simulation` proves `dst.g := &kind s` at zero field
offset with `dst`'s root UNBOUND. Derived from
`ref_fresh_dst_simulation` by a blanket substitution of the ROOT's
layout — `PtrL τ` becomes `σ` at every `Alloc`, `typeSize`,
`setPlaceInfo`, `PtrRegisterEntry` and `allocSize` — with exactly one
exception, `writeThroughPtr_sim (τ := PtrL τ)`, where the layout names
the VALUE being stored rather than the block receiving it. Protecting
that one occurrence before the blanket replace and restoring it after
is the whole trick.

Two genuine (non-substitution) changes:

1. ρa extends over the WHOLE root block, not one cell.
   `AddrRenameMap.extend a a` becomes `extendBlock a (blockSize σ)`,
   with `extendBlock`/`extendBlock_base`/`extendBlock_mem` replacing
   `extend_id`/`extend_self`. The pointer-local case got away with a
   single address because `blockSize (PtrL τ) = 1`.
2. The destination's block-domain conjunct in `LocalBindingSim` was
   discharged by `simp [blockSize]; omega` (one cell); now it is
   `fun k hk => ⟨addrStart + k, h_ra_dom k hk⟩`.

The `mirlite.preparePlaceAssign` inversion needed NO change — the
fresh-local leaf already had `mirlite.allocateRoot` in its simp set.

## [FACT] a path cannot reach `PtrL τ` from `τ`

The none/none dispatcher branch (both destination root and source
unbound) needs `srcLoc.idx ≠ dstLoc.idx`, and here neither the types
(`σ` vs `τ`, unrelated) nor the env facts (both `none`) give it. Shared
indices would force `σ = τ` and hence `g : PathTo τ (PtrL τ)`.

That is impossible for a SIZE reason, and `cases` cannot see it — a
path may descend through arbitrarily many tuple fields. The lemma:

```lean
theorem PathTo.sizeOf_le (p : PathTo σ ρ) : sizeOf ρ ≤ sizeOf σ
```

by induction, with `List.sizeOf_lt_of_mem (List.get_mem tys idx)` for
the field case. Then `sizeOf (PtrL τ) = 1 + sizeOf τ` closes it by
`omega`. Lean's derived `SizeOf` and its `sizeOf_spec` simp lemmas do
all the work; no bespoke measure needed.

Compare `ref_proj_dst_src_idx_ne` (same day), where the path ran the
other way — out of a `PtrL`, which has no fields — and `cases f` alone
sufficed. Direction decides which technique applies.

## [OBS] `induction ... with | @field ...` binds the AUTO-BOUND index first

`PathTo`'s constructors carry an auto-bound `{τ}` from the inductive's
signature ahead of `field`'s own `{tys}`. So `| @field tys idx rest ih`
silently binds the TARGET LAYOUT to the name `tys`, and the error
surfaces far away as "invalid field `get` ... of type LayoutTy". The
correct pattern names it: `| @field ρ' tys idx rest ih`.

## [OBS] a Python trap that truncated the file

`open(p, 'w').write(f(...))` evaluates `open(p, 'w')` — which TRUNCATES
— before evaluating the argument. When `f` raised (a missing scratch
file), `ref.lean` was left at zero bytes. It was recoverable from HEAD,
costing only the uncommitted fragment pair.

Rule for scripted edits from now on: compute the full output string
into a variable, assert it is longer than the input, and only then
open the file for writing. Never let a call that can raise sit inside
the `write(...)` argument.

## [FACT] d77's teeth

`t.0 := &mut x` with `t` fresh, followed by `t.1 := &mut y` — the
second field is in bounds only if the root really was allocated at the
tuple's size. Control: retarget the first borrow to `y`, so the two
fields alias; `*(t.0) := 9` then reads a popped tag and mirlite reports
`ub` at statement 4.

## state

Build green; 17/17 + 90/90; audit exact at ONE sorry. Residual call
sites 11 -> 10. Two unbound-root sites left: a deref source under a
fresh destination, and a projected destination over an unbound root at
NONZERO offset (that one adds the interior `Borrow(Mut)` and its
cleanup `Die`, i.e. BRIDGE 1 on top of this leaf).
