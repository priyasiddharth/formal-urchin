# 2026-10-05 — Die elision: OSEA-IR → OSEA-IR_B

Goal (user): a forward simulation showing that eliding `Die` never makes
a valid OSEA-IR program invalid. OSEA-IR_B is OSEA-IR whose `Die` is a
no-op, represented as the permission model `stackedBorrowsNoDie`
(`{ stackedBorrows with die := fun s _ _ _ => .ok s }`). Plan:
~/.claude/plans/can-we-move-to-stateless-lemur.md.

## The counterexample (why the semantics had to change)

[OBS] Under the old rules the theorem is false. Take one byte, stacks
written top first; A is OSEA-IR, B is OSEA-IR_B:

1. `Alloc` → `[Own t0]`.
2. `Borrow Shared` → `[Ref t1, t0]`.
3. Store `r1`, then `ExposeAddr` → `exposed = [t1]`.
4. `Die r1` → A `[t0]`, B `[Ref t1, t0]`.
5. `Borrow Raw-mut r0` (inserted above `t0`) → A `[t2, t0]`,
   B `[t1, t2, t0]`.
6. Expose `t2`.
7. `Borrow Raw-mut r2` → A `[t3, t2, t0]`, B `[t1, t3, t2, t0]`.
8. A `FromExposed` wildcard, then a `Borrow Raw-mut` through it.
   `resolveWildcardIn` takes the TOPMOST exposed item: A picks `t2`,
   B picks the dead `t1`.
9. `CStore` via `r3` (SRW): B's SRW run stops at `Ref t1`, so B pops
   `[t5, t1]`.
10. `CStore` via `r5`: A ok, B "tag does not exist".

The point is step 8: an exposed, died item is still resolvable in B.

[DEC] (user) The rule set, chosen after several rounds:
- `AccessPerms.retired`.
- `sb_die` errors if the tag is exposed, and records the tag as retired.
- `sb_expose` errors if the tag is retired (no stack check; the user
  rejected "expose only if in SB" because expose-then-die stays valid
  under it).

So `retired ∩ exposed = ∅` in every valid run, and B exposes exactly
what A exposes. Both checks are stricter than Miri. Neither fires on
compiled programs: only route tags and move's temporary are died, and
those never reach memory, so they are never exposed.

## Group A — semantics + compile_correct repair

- sb.lean: the `retired` field; `sb_expose : … → Except String
  AccessPerms`; `sb_die` with the exposed check and `retired := tag ::`.
  The fold's per-cell op is now the named `dieCellOp`.
- permission.lean: `expose` returns `Except`; `stackedBorrowsNoDie`.
- oseair/mirlite `ExposeAddr` propagate the error.

[OBS] No verdict moved: 33 + 145, 188/0/0/18, `--osea` 188,
`--layouts` 188; the running-example trace is unchanged.

`expectDiff` now also runs every compiled differential program on
OSEA-IR_B and requires the same verdict. All 145 agree; that equality
is stronger than the theorem, which gives only ok ⇒ ok.

[OBS] Proof. `RetiredSim` is needed in ONE direction only:
- a renamed target tag is retired ⇒ its source tag is retired;
- every target-retired tag is below the target counter (route tags
  are outside ρt's range).
The pieces:
- `PermSim` gains it as a 6th conjunct.
- `rename_mono` takes a side condition. `rename_extend` covers the
  fresh pair; `RetiredSim.of_eq` covers steps that do not retire.
- Keystones: new `h_unexp` (`freshTag_not_exposed`). Their
  conclusions add `s3.retired = t' :: sAcc.retired` and
  `t' < s3.NextTag`. The six callers use `PermSim.of_cancel`.
- `sb_die_respects_PermSim` takes `h_bd` and transports the exposed
  check (`TagListSim.contains_eq`).
- Expose: `exposeBody`, `sb_expose_ok_iff`,
  `sb_expose_respects_PermSim` (`Except`).
  `sb_die_exposeBody_comm` needs the exposed tag ≠ the died tag.
- `projoff_bracket`'s op now gets `sA.NextTag ≤ T` and
  `RetiredSim ρt perms' pmid`, and its die-commutation is specialised
  to the bracket's own route tag `T`. exposefield uses both: the
  exposed tag is a renamed tag, below `T`, and the target expose
  succeeds.
- Audit: 3 axioms, 0 sorries, 802 declarations.

## Group B: the per-state layer

[OBS] `stacksub.lean` (397 lines): the spike held. `srwSplit_sub` and
`splitStack_sub` go through with the `same`-only SRW side condition.
`cellsub.lean` (491): `CellRel E N` = StackSub + B-tags distinct + below
`N` + A's bottom is `Own`. That replaces the separate `PermWF` file the
plan had: the well-formedness travels inside the cell relation.

[OBS] `permsub.lean` (541): `PermSub` and the range transports — read,
write, ref, own, dealloc, die, expose, push/pop frame. All sorry-free.
- One generic lifter (`foldCells_sub`) turns a cell transport into a
  fold transport; read and write are ten lines each.
- Retag: a ZERO-LENGTH `Die` retires any tag, including one not yet
  minted. So the fresh tag `N` may already be "retired", and a protected
  retag of it would break `Extra` for a B-item tagged `N`. Fix: restrict
  the extras to `t < N` before the fold (`CellRel.restrict`, free from
  the bound in `CellRel`), then `regProt_prot` only protects `N`.
- `sb_ref_eq` factors the registration (`regProt`) out of `sb_ref`, so
  A and B finish with the same function of equal frames.
- Die: B unchanged; per cell `dieCellContent_cell` with `Extra A'`; the
  unprotectedness of the died tag comes from the cell op itself, so a
  zero-length die of a protected tag creates no extra and needs nothing.

## Group B: the machine level

[OBS] `die_elision.lean` (≈390 lines) is model-GENERIC. `ModelSim M1 M2 R`
asks each permission op of `M1` that succeeds to be matched by `M2`'s with
the same returned tag and `R`-related states; `runN_msim` then gives
lockstep simulation for any program. The machine never inspects a
permission state, so the proof is pure case analysis on `step`/`evalRhs`
(`split at h` also rewrites the goal's identical discriminants; the
`rw [hl]` I first wrote after each split was redundant and failed).
`modelSim_noDie : ModelSim MSB MSB_B PermSub` is nine one-liners over
`permsub.lean`. No separate `PermWF` file was needed (it lives in `CellRel`).

[OBS] Name clash caught only by the audit scripts (they import every
proof module together): `readCellThrough_sim`/`allocPtr_sim` already
exist in leafops/alloc. The generic lemmas are now `*_msim`.

[OBS] Audit: roots now include `die_elision`; 3 axioms, 0 sorries;
`proof_axioms.lean` 945 declarations (was 802). Suites unchanged:
33 + 145, 188/0/0/18 of 206, `--osea` 188, `--layouts` 188.

## Group C: tests and harness

[OBS] Four OSEA-IR witnesses in `compile_tests` (149 now), each run on
both machines (`expectOseaAB`):
- w1: die of an exposed tag. A: "sb-die: tag 3 is exposed"; B ok.
- w2: expose of a retired tag. A: "sb-expose: tag 3 is retired"; B ok.
- w3: use after die. A: tag does not exist; B ok. This is the direction
  the theorem allows: B may succeed where A fails.
- w4: the counterexample from the plan. A now stops at the `Die`. B
  runs on and fails at the last store ("sb-write: tag 7 does not
  exist"). Checked by running a prefix: B is ok through instruction 15,
  so its failure is the dead-`Ref 3` wildcard resolution, as claimed.

[OBS] `--osea` also runs every compiled corpus program on OSEA-IR_B and
requires the same outcome at the same label (`mismatchB`, which fails
the suite). 188 matched, 0 mismatches, 0 OSEA-IR_B mismatches.
