# Proj-topped copy sources at nonzero offset: the deref-dst arm goes total

[OBS 2026-08-30] `*p := copy s.f` with the field OFF ZERO is closed by
`copy_chaindst_projsrc_offset_simulation` (d65). With it,
`copy_place_residual` no longer names any deref destination: the whole
deref-dst arm of `CompilerInv_step_copy` is total, and the only
remaining class is a projected destination over a LOCAL base.

**Why it was easy in principle.** The parked note called it a merge of
two ~600-line proofs, and that is exactly what it is: §1–§5 and §8–§11
come from `copy_chaindst_projsrc_zero_simulation` (d64) unchanged apart
from carrying `PathTo.offset spath` through the source address, and
§6–§7 are `copy_projchain_offset_simulation`'s BRIDGE 1S phase spliced
in where the zero leaf had a bare `Load`.

The splice is clean because of an ORDERING accident worth naming: the
projection's `Borrow(Shared)` and its cleanup `Die` both sit inside the
rhs pre-phase, so they bracket the READ *contiguously* — the
destination lowering has not started yet. `sb_ref_read_die_cancels`
therefore applies with nothing interleaved, and its output
`PermSim ρt perms₂ q3` slots into exactly the argument position where
the zero leaf passes `h_psim2`. The destination mother lemma then runs
at the post-`Die` states and needs no commutation argument at all.

## Potholes (three new, all about term SHAPE not mathematics)

[OBS] **Record-update sugar elaborates to a `let`.** Writing a
compiled state as `{ X with nextReg := … }` in a *hypothesis* elaborates
to `let __src := X; { nextReg := …, nextLabel := __src.nextLabel, … }`,
while the same state in the *goal* appears as a flat four-field
literal. `rw [h_dval]` and `h_dval ▸ h_d` then both fail to fire. The
fix is not to align the spellings but to stop matching syntactically:
transport by DEFEQ instead —

    have h_d' : CheckedCompilerM.value … <my spelling> = Except.ok o := h_d
    have h_oeq : dOut = o := Except.ok.inj (h_dval.symm.trans h_d')

and close the residual shape difference with a trailing `rfl`. This is
the fifth manifestation of the record-sugar problem in copy.lean and
the first with a general remedy. See
[[transport-compiled-states-by-defeq]].

[OBS] **Structure-instance fields must line up.** Lean's
`sepByIndent` wants every field of a `{ x with … }` that starts a new
line to sit at the SAME column. `{ s with a := 1,` then a next line
indented differently is a parse error ("unexpected identifier; expected
'}'"), which reads nothing like an indentation complaint. Generated or
reflowed proof text must either keep all fields on one line or align
them exactly.

[OBS] **Long `StateIncr` chains defeat the unifier.** The source tower
here is FIVE steps (freshReg, `Borrow`, freshReg, `Load`, cleanup
`Die`) before the destination lowering. A single `StateIncr.trans`
chain of `emit_state_incr _ _` across all five leaves the intermediate
instruction lists as metavariables; the unifier then has to reconcile
`emit (emit (freshReg …).snd ?l₁) ?l₂` with a record literal and gives
up with an "application type mismatch" (or burns the heartbeat budget
on `isDefEq`). The remedy is to SPLIT the chain at a state you can
name: prove a ground prefix `StateIncr CS0 CS2V` from explicit terms,
then reuse the short dst-side chain the other leaves already use, and
compose with one `StateIncr.trans`. Both halves are then
ground-vs-ground defeq checks, which succeed instantly.

[EMP] Raising `maxHeartbeats` masks this but does not fix it: with the
un-split chain the declaration compiles at 1000000 heartbeats, and once
the chain is split it compiles at the DEFAULT 200000. The heartbeat
budget was measuring the doomed unification, not the size of the proof.
Verified against 5cc3854+.

## Teeth

`expectDiff` compares VERDICTS, not values, so a wrong-value mutation
does not bite — the tooth has to induce a UB divergence. Oversizing the
projection's `Borrow` by one word does it, and restricting the mutation
to `RefKind.Shared` makes it DISCRIMINATING: d64 (source projection at
offset 0, which takes the no-borrow branch) still passes, while d65
flips to `target verdict ub 4, source agrees ok`. That is precisely the
`h_le1` obligation the leaf discharges from the copy's own fit check.

**Validation:** full build green; 17/17 + 78/78; corpus 82 pass / 0 fail
/ 123, osea matched 82; `scripts/audit_axioms.sh` exact at 2 sorries,
`[axioms]` block untouched.

**References:** the parked entry this closes (removed from
notes/loose-ends/parked.md), journal/2026-08-30-projected-dst-recursion.md,
durable/flatten-one-place-at-a-time.md.
