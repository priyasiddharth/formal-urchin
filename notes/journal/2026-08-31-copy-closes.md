# copy_place_residual is closed

[OBS 2026-08-31] The copy dispatcher is TOTAL. `copy_place_residual` is
deleted and `scripts/axiom_whitelist.txt` pins ONE sorry,
`ref_place_residual`.

**The last class** was a PROJ-TOPPED source under a PROJECTED
destination, and it split on the SOURCE offset:

- at ZERO source offset the source supplies a `LoweringSim` PACKAGE
  (`LoweringSimAny.projZero`, ~35 lines), and the existing
  projected-destination leaves accepted it with no new proof — d70/d71;
- at NONZERO source offset it cannot, because its lowering emits a
  `Borrow(Shared)` and leaves a cleanup `Die`, breaking the package's
  `cleanup = []` promise. That needed four leaves, one per
  (destination offset × bound/fresh root), each carrying BRIDGE 1S
  around the READ — d72/d73/d74.

[FACT] The two bridges never interleave. The SOURCE projection's borrow
is taken and retired inside the rhs pre-phase, before the destination
lowering starts; the DESTINATION projection's borrow is taken after.
So `sb_ref_read_die_cancels` and `sb_ref_use_die_cancels` each apply to
a contiguous window and no commutation argument is needed anywhere.

## What made the last two leaves tractable

[EMP] Rewrite the source phase STRUCTURALLY, never by patching `rw`
chains. Tokenize the post-alloc source state, turn the `Load`-only
state into the `Borrow`/`Load`/`Die` tower, and remap every standalone
`Register.R CS0.nextReg` to the LOAD target `Register.R PS.nextReg`,
splitting the leaf at `subst h_sOut_eq` (`sOut0` before it, `sOut`
after). Patching site-by-site made the error count go UP; the
structural rewrite took it 9 → 1. Verified against 11bf68c..HEAD.

[EMP] Then write the write phase FRESH rather than editing it, and
expect exactly three classes of follow-up error:
1. ARITIES — every `StateIncr` tower and every `emit_code_lt_nextLabel`
   peel count changes when a projection adds instructions. The
   destination projection adds three (Borrow/RStore/Die), so the
   SOURCE code facts need two more peels each, and the towers a
   `freshReg` plus an `emit`.
2. SPELLING — `csnorm at h1 h_eq'` for every `omega` that compares two
   `emit`-laden atoms; the record-update sugar `{ X with … }` on a huge
   term must become an explicit four-field literal, and multi-line
   `{ s_mid with … }` records must be collapsed to one line or their
   fields will not align.
3. CONTENT — the destination borrow mints at `q3.NextTag` (the state
   AFTER the source's `Die`), not at `s_mid.perms.NextTag`. This is the
   one that is not mechanical, and it is the one worth thinking about
   before writing.

[OBS] `csnorm` does NOT cover `getPlaceInfo`; those peels stay explicit,
and the count grows with the tower. Extending `csnorm` to include them
was tried and rejected — see
durable/csnorm-a-normal-form-for-compiler-states.md.

**Validation:** full build green; 17/17 + 87/87; corpus 82 pass / 0 fail
/ 123, osea matched 82; `scripts/audit_axioms.sh` exact at ONE sorry,
`[axioms]` untouched.
