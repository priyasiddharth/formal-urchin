# 2026-08-29 (cont. 4) — L→P: the two-mint leaf

## What closed
`ref_local_projoffset_simulation`: `dst.g := &src` at NONZERO offset,
both roots bound. Fragment `[Borrow(kind,src); Borrow(Mut,dst field);
RStore; Die]` — the first leaf where the target mints TWO tags in one
statement:
- the rhs reference pairs with the source's mint; ρt extends there
  (`sb_ref_respects_PermSim`, as L→L);
- the dst field borrow is a compiler phantom; BRIDGE 1
  (`sb_ref_use_die_cancels`) cancels its ref;use;die to the parent
  write — run UNDER the extended rename, with its suppliers
  (`freshTag_not_protected`, the wildcard bound) fed by the rhs
  member's own outputs `h_tbd'`/`h_psim'`. The composition the audit
  once called "interleaved-keystone commutation — a new pattern"
  turned out, post-lowering-order-fix, to be plain sequencing.

Built on the FIRST try — the L→L + C1 templates compose without
friction now. d41 pins it differentially, including a write THROUGH
the stored field reference (54/54).

## Bookkeeping notes
- Two fresh registers; LBS = rename_mono + insert_fresh ×2 +
  pointwise placeRegMap through 4 emits + 2 setNextRegs.
- TagRenameBounded final: source +1 (rhs mint), target +2 (both
  mints, one died — the counter never rewinds); `mono h_tbd'` with
  the keystone's `h_ntle` through `sb_write_NextTag`.
- Address spellings normalized eagerly (`Nat.add_zero/zero_add` at
  the run facts) — the discipline from copy P-offset pays off.

## State
All targets green; units 17/17 + 54/54; suite 82/123; axiom audit
exact; leaf axioms standard; audit at 4. Ref's residual: nested/deref
dst bases, non-local srcs under non-local dsts, and the prior src
classes.
