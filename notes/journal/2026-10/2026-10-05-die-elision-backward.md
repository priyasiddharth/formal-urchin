# 2026-10-05 — Die elision, backward: same verdict on compiled code

## Context
`die_elision` is OK(A) ⇒ OK(B). The user asked for the other direction
(UB in OSEA-IR ⇒ UB in OSEA-IR_B), equivalently OK(B) ⇒ OK(A). False for
arbitrary OSEA-IR (w1–w3). For compiled code it needs two COMPILER
properties: every `Die` succeeds, and nothing acts through a died tag.
Neither involves the source program (an earlier answer of mine said it
did; corrected).

## The compiler check
[OBS] Reading compile.lean: `Die`s come only from `cleanupInstrs`, and
every cleanup list is a singleton in practice — `projOffset`'s base and
`placeToBorrowRegChecked`'s base are never `.proj` (nested projections
are reassociated first), so their cleanup is `[]`. `.ref` never dies its
borrow (postCleanup `[]`); `addrOf` uses the local's own register. Hence
the expected shape of every bracket:

    r := Borrow k false [] (some n) base off   -- k ∈ Mut/BoxMut/Shared/Raw false
    one access THROUGH r                        -- Load/ExposeAddr/FromExposed/PtrOffset, RStore/CStore at r
    Die r n

and `r` (a fresh register) appears nowhere else. `SkipIf` jumps over a
whole compiled assignment, never into a bracket.

[OBS] `oseair.bracketIssues` (src/obseq3/brackets.lean) checks exactly
that, per program, decidably. Wired into `expectDiff` (all compiled
witnesses) and `--osea` (all compiled corpus programs; new status
`brackets`, fails the suite). Result: 0 issues; the corpus has 771 `Die`s,
all checked. Sanity: the checker rejects w1/w3's shapes and a reuse of a
bracket register, accepts a good bracket.

## Plan from here
1. General lemma: a program whose brackets check out reaches the same
   verdict on OSEA-IR and OSEA-IR_B (OK(B) ⇒ OK(A) at each step).
2. Compiled code passes the check: either prove it for `compile.lean`, or
   keep it as a per-program decidable hypothesis (as `LocalsAgree`).

## The proof (same day)

[OBS] Done, sorry-free, 3 axioms. Files (≈2,500 lines):
- `permsub_rev.lean`: B succeeds through a tag A has not retired ⇒ A
  succeeds (read, write, ref, own, dealloc, expose, pop-frame). Key:
  `splitStack_rev` (splitting B at a non-extra tag finds an A-item); A
  pops/disables a subset of what B does. The `*_back` lemmas reuse the
  forward ones for the relation (determinism gives B's result).
- `tagsin.lean`: `MemOK P m` (every pointer tag in memory satisfies P)
  defined as `ByteMemSim (keepMap P) m m`, `keepMap P` the partial identity
  on P. Reads and stores then come free from `decodeV_sim`/`writeL_sim`.
- `die_back.lean`: `RouteProg` (Prop form of the check), `Inv`: PermSub +
  `PInv` (retired/exposed/protected tags < NextTag, wildcard never
  retired) + memory tags good + register tags < NextTag and retired only
  in DEAD bracket registers + `Pending` inside a bracket (route tag on top
  of every byte, unexposed, unprotected, held by its register alone).
- `die_back_ops.lean`: `evalRhs_back`, `writeThroughPtr_back`.
- `die_back_step.lean`: push-kind retag leaves its item on top; access
  through the top item is the identity; `sb_die_of_top`.
- `die_back_run.lean`: `step_back`, `runN_back`, `die_elision_back`,
  `die_elision_iff` (for RouteProg programs).
- `die_back_check.lean`: `routeOK_sound` (Bool check ⇒ RouteProg, given
  nothing beyond the emitted labels), `compileProg_code_none`,
  `compiled_die_elision_iff` — an audit root.

[DEC] The compiler-side fact is a DECIDABLE PER-PROGRAM check
(`oseair.routeOK`, run on every compiled witness and corpus program,
771 Dies), not a theorem about `compile.lean`, like the layout check.
Proving it for all programs needs a dataflow invariant over every compile
function (a route register is used once and never again); parked.

[OBS] `StateIncr` gained a field `code_none` (nothing emitted beyond
`nextLabel`), so a compiled program is exactly its emitted labels. Prop
field, no behaviour change; `StateIncr.patchLabel` takes `label <
cs'.nextLabel` (its one caller, `emitSkipIfAround`, has it).

[OBS] Found while designing the invariant: `RouteProg` also needs "no
`CStore` stores a pointer literal" (a literal could carry any tag, a
retired one included). Compiled code stores only data/uninit literals;
`routeOK` checks it.

Audit: 5 roots; 1109 declarations. Suites unchanged.

## The compiler always passes the check (same day, later)

[OBS] `compiled_routeProg : compileProg L P = .ok Q → RouteProg Q`, hence
`compiled_die_elision` (audit root): every compiled program reaches the
same verdict on OSEA-IR and OSEA-IR_B — no per-program hypothesis.
`route_seg.lean` (269) + `route_compile.lean` (2030), sorry-free, 3 axioms.

[OBS] Method: each compile function's emitted code is a SEGMENT (`Emits`)
with a spec (`Seg`): every register it mentions is a local's, passed in,
or created in its register window; every `Die` closes a bracket inside the
segment on a window register; no pointer literal; no `SkipIf`. A place
lowering may end in an OPEN bracket (`PlaceOut`), which the caller closes
with one access and the `Die` (`close_access`, the one lemma every
consumer uses: readToReg, readRhsPre, move, deref, the assignment's store).
Statement level: `Code` (allows the guard's `SkipIf`, jump target within
the segment and never inside a bracket) composes by concatenation; the
program is one `Code` segment from label 0, hence `RouteProg`
(`Code.routeProg`).

[OBS] Two facts about the compiler that the spec needed and that held:
nested projections are reassociated before lowering, so a projection's
base never has a cleanup (every cleanup list has ≤ 1 entry); and the
assignment's store immediately follows the destination's route borrow.
`assignIf`'s guard register is created before the body — handled by
`Code.append_guard` (treat it as live inside, then drop).

[OBS] The audit caught one more name clash (`emitSkipIfAround_ok`, in
assignif.lean); renamed `skipIfAround_ok`. Audit: 6 roots, 1265
declarations. Suites unchanged. Paper: the theorem is now unconditional;
the check's definition is gone from the paper (not needed to state it); the
check still runs in the tests as a regression guard.
