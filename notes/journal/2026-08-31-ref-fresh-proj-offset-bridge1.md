# ref: BRIDGE 1 over a freshly allocated root

Date: 2026-08-31
Tags: obseq3, ref, regime-B, bridge-1, merge

## [FACT] this one was a MERGE, not a substitution

Every ref leaf so far this session came from ONE donor plus local
substitutions. `ref_projoffset_fresh_simulation` could not:

- diff(`ref_local_projzero_simulation`, `ref_local_projoffset_simulation`)
  = 405 lines — the bound zero-to-offset delta is a rewrite;
- diff(`ref_local_projzero_simulation`, `ref_projzero_fresh_simulation`)
  = 560 lines — so is the bound-to-fresh delta;
- copy's own zero-to-offset delta was 433 lines.

The two axes (fresh root, nonzero offset) are independent and each
costs a full proof, so the leaf is the CROSS of two donors. It was
assembled as: `ref_projzero_fresh_simulation`'s §1-§6 (allocation, both
ρt extensions, ρa `extendBlock`) verbatim, then
`ref_local_projoffset_simulation`'s write phase (BRIDGE 1) with the
fresh spellings, then a rebuild combining both.

Cost: the assembly compiled with ONE error (a TagRenameBounded
weakening, below), after one intermediate build that stopped at
`trace_state` to confirm the first nine sections. Splicing whole
sections at their natural boundaries turned out far cheaper than
patching either donor toward the other.

## [FACT] where the section boundary has to fall

The two donors order their phases differently:
`ref_projzero_fresh_simulation` does the fragment and execution first,
then the mirlite write; `ref_local_projoffset_simulation` inverts the
mirlite write FIRST. The offset version needs po's order, because the
interior `Borrow`'s bounds check (`h_off_le`) comes from `h_nb`, the
destination fit condition produced by splitting `writeResolvedPlace` —
and `q1`/`q2`/`q3` from BRIDGE 1 are arguments to the execution steps.

So the splice point is: mirlite write inversion + BRIDGE 1 BEFORE the
fragment. Get that wrong and the execution steps have no tags to
mention.

## [OBS] the one real error: bounding the tag rename past BRIDGE 1

`TagRenameBounded ρt' perms''.NextTag q3.NextTag` — the oseair bound is
now `q3`, three permission states past the one `h_tbd2` knows about.
`sb_write_NextTag h_useMut_src` fixes the mirlite side; the oseair side
needs `h_ntle : qAcc'.NextTag ≤ q3.NextTag` transported through
`sb_write_NextTag h_useMut_tgt : qAcc'.NextTag = tgtP2.NextTag`:

```lean
exact TagRenameBounded.mono h_tbd2 (Nat.le_refl _)
  (by rw [← sb_write_NextTag h_useMut_tgt]; exact h_ntle)
```

In the zero-offset leaf `h_useMut_tgt` WAS the final state, so the
bound was an equality and `exact h_tbd2` sufficed. BRIDGE 1 turns that
equality into an inequality — the only place in the whole leaf where
the extra two instructions leak into the invariant.

## [FACT] peel arithmetic for five instructions

The fragment nests as
`emit(emit(emit({emit({setPlaceInfo(emit cs' [Alloc])} with nR) [Borrow]} with nR) [Borrow2]) [RStore]) [Die]`,
so `getPlaceInfo` peels are
`emit, emit, emit, setNextReg, emit, setNextReg` before reaching the
`setPlaceInfo`, and `emit_code_lt_nextLabel` peels run 4, 3, 2, 1, 0
for the five code facts. Getting these counts right up front is what
kept the error count at one.

## [FACT] d78's teeth

`t.1 := &mut x` with `t` fresh, then `t.0 := &mut y` — the second field
is in bounds only if the root was allocated at the tuple's size.
Control: retarget the first borrow to `y` so the fields alias;
`*(t.1) := 9` then reads a popped tag and mirlite reports `ub` at
statement 4.

## state

Build green; 17/17 + 91/91; audit exact at ONE sorry. Residual call
sites 10 -> 9. THREE of the four unbound-root sites are closed; the
last is a deref SOURCE under a fresh destination, which crosses the
fresh machinery with the spine mother lemma instead of with BRIDGE 1.
