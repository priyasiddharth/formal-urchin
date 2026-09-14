# `Die` does nothing when its tag is no longer on top

Load this when reasoning about the `Borrow; use; Die` bracket a projected
place lowering emits, or when tempted to treat `Die` as a Stacked Borrows
operation.

[FACT, 2026-09-14] **`Die` has no Rust counterpart.** Stacked Borrows
never ends a borrow actively; items are popped by the next conflicting
access. The instruction exists only to retire the COMPILER's own
scaffolding — the temporary that `placeToRegChecked` borrows at a nonzero
field offset. Its old "must be on top" branch was a self-check that
brackets nest, not a semantic requirement.
→ src/obseq3/sb.lean, `dieCellContent`

[FACT, 2026-09-14] **So the not-on-top branch is a no-op.** `.ok (item ::
below)`, not an error. When an intervening access has already popped the
temporary, SB has ended the borrow itself and the cleanup has nothing to
do. The `Own`-root and protected branches stay errors: a compiler
temporary is never either, so they are dead for the proof and kept as
sanity checks.

[FACT, 2026-09-14] **This makes the bracket collapse UNCONDITIONAL.**
`Borrow; use; Die` equals `use through the parent` in every case, not
only when nothing intervenes — which is what `sb_ref_use_die_cancels` and
`sb_ref_read_die_cancels` always asserted and what the strict branch
broke on. Within a bracket only the rvalue's own instruction accesses
through the temporary, so at the `Die` the temporary is either on top or
already gone:

    Mut mint inside the bracket   write access pops the temp; Die no-ops
    Raw / Shared mint             item inserted directly ABOVE THE
                                  GRANTING ITEM, below the temp, which
                                  stays on top; Die pops as before

[FACT, 2026-09-14] **Mis-nesting is still caught, and caught better.**
`Die` only ever removes its OWN tag, and only from the top, so the sole
way a bad bracket differs is a STALE ITEM left on the target's stack.
`PermSim` relates stacks positionally (`StackSim` is `ListRel ItemSim`
over the whole stack), so a stale item is unrelatable to mirlite's and
the simulation step fails to typecheck — a build failure over all inputs,
rather than a runtime error on whichever inputs a test happens to
exercise. The runtime check only ever guarded the UNPROVED fragment,
where `--osea` still catches a verdict divergence.

[FACT, 2026-09-14] **The whole proof library built unchanged.** The
keystones only ever used the on-top case. One split was needed:
`dieCellContent_top_ref`, because `.Ref` and `.MutRef` no longer unify
through the error branch.

## Why this matters

Any future minting rvalue inherits the collapse for free. Before this,
each one would have had to prove that nothing it did could disturb the
projection's temporary — which for `refSlice` was false.

## See also

- refslice-projsrc-mut-pops-the-projection-borrow.md
- one-leaf-per-destination-shape.md
