# grind: pass `foo.eq_def`, not `foo`, for definitions that match

**Verified against:** `a0dda43` (Lean 4.28, toolchain
`leanprover/lean4:v4.28.0`)

[EMP] When a goal turns on a definition whose body is a `match` — and
especially one matching on a `Bool` or a constructor field nested inside
another constructor — passing the definition *itself* to `grind` often
stalls, while passing its **`.eq_def`** closes the goal:

```lean
grind [Item.grantsWrite]        -- stalls: un-split Bool inside RawPtr
grind [Item.grantsWrite.eq_def] -- closes
```

**Why:** with the bare name, grind receives the *conditional equation
lemmas* (one per branch, each guarded), and it will not split the
scrutinee to discharge the guards. `.eq_def` hands it the single
unconditional equation whose RHS *is* the `match` term, and grind's
case-splitting then fires on that term.

**Where this has paid off so far** (all Lean 4.28, this repo):
- `Item.grantsWrite` / `Item.poppedByRead` (Bool inside `RawPtr m t`)
- `refCellContent` (the `Raw` arm's mask Bool) — with `.eq_def` the
  `cases kind` disappears too: `grind [refCellContent.eq_def]` alone
  proves `refCellContent … none ≠ .ok w`
- `writeCell` / `readCell` in the `NextTag`-preservation lemmas:
  `foldCells_NextTag (fun _ _ _ h => by grind [writeCell.eq_def]) …`

**Rule of thumb:** reach for `.eq_def` whenever the definition's body is
a `match` and grind's first attempt fails. It costs nothing to try and
is the difference between a one-line proof and a hand-rolled
`cases … <;> simp only […]` bash of 10–25 lines.

**Related (2026-08-21, same toolchain): grind beats omega on some
arithmetic.** Twice this session `omega` failed on trivial goals
(`addr + (k+1) = addr + 1 + k`, `a + 0 + n ≤ a + n`) reporting
counterexamples over atoms that do not appear in the goal — the
metavariable-leak pattern. `grind` closed the first outright where omega
needed a hand-written `rw [Nat.add_assoc, Nat.add_comm 1 k]`. When omega
fails on a goal you can see is true, try `grind` before hand-rolling
rewrites.

**Scope:** this is about GOAL-side reduction only. It does not help
grind with ∃-witness assembly or monadic `bind`/`pure` unfolding — see
`journal/2026-08/2026-08-21-grind-assessment.md` for the full
pass/fail map of what grind can and cannot do in this codebase.
