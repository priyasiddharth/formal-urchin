# obseq2 research notes

Agent-maintained knowledge base for the obseq2 compiler-correctness
proof effort (mirlite → oseair, Lean 4). Conventions per the
better-than-fish skill: confidence markers, three durability tiers,
supersede-never-delete.

## Layout

```
durable/    [FACT] — source/paper/design-grounded, time-invariant
empirical/  [EMP]  — repeated observations, version-stamped
            (first entry 2026-08-21: grind's `.eq_def` rule)
journal/    [OBS] [HYP] — dated single events, YYYY-MM dirs
weekly/ monthly/     — digests
loose-ends/parked.md — parked work with resume context
sessions.md          — index of significant sessions (read latest
                       entry first when starting a session)
```

## Project-stable conventions

- The human-facing dev log is `obseq2-comparison.md` at the repo root
  (newest-first dated entries; subtitle "obseq2 Development Log").
  Design narrative goes THERE; agent working state goes HERE.
  Cross-link, don't duplicate.
- v2 (live) proofs: `src/obseq2/proof/`. v1 (reference only):
  `src/obseq/proof/` — see durable/dont-port-v1-proofs-reconstruct-in-v2.md
  before reusing anything from v1.
- Build check: **`lake build Obseq3Proof`** (and `Obseq2Proof` for v2).
  Plain `lake build` builds only the `Core` default target
  (`obseq`/`obseq2`/`interp`) — **it does not compile the proof
  libraries at all**, so a proof file can be broken while `lake build`
  reports success. Healthy means all jobs green with only the expected
  `sorry` warnings (count tracked in the latest journal state snapshot).
  Corrected 2026-08-21; see journal/2026-08/2026-08-21-regime-c.md.
- **Before committing a proof leg, retry its SMALL lemmas with `grind`.**
  A green build is not a reason to skip this — the failure mode observed
  twice on 2026-08-21 was writing a lemma by hand, seeing it compile, and
  never trying grind at all. Applies to: constructor case-bashes,
  tag/bound/beq algebra, induction LEAVES (grind does no induction
  itself, but `induction … <;> grind [...]` works), and any goal where
  `omega` fails on something visibly true. Pass `foo.eq_def` rather than
  `foo` for match-bodied definitions. Do NOT bother for ∃-witness
  assembly, monadic `bind`/`pure` unfolding, or the big fragment/
  execution proofs — grind cannot do those. Typical saving is 10–25
  lines per lemma; see empirical/grind-needs-eq-def-for-match-defs.md
  and journal/2026-08/2026-08-21-grind-assessment.md.
- `[EMP]` notes stamp "Verified against" with this repo's commit
  (`git rev-parse --short HEAD`), since the Lean code is the moving
  target.
