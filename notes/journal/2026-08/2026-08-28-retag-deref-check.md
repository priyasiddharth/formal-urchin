# The event fix lands: mirlite's `.ref` checks retag dereferenceability

[FACT] mirlite's `evalRExpr .ref` now errs when the retag range exceeds
the resolved place's allocation
(`resolved.addr + blockSize σ > resolved.allocBase + resolved.allocSize`)
— Miri's requirement, the retag-side mirror of `writeResolvedPlace`'s
check, in the range form that admits zero-sized referents at
one-past-the-end. Behaviour on every reachable state is UNCHANGED (suite
82/123, differential 82/0/0, all units) because every mint site stores
the allocation's size and no construct can shrink it — which is exactly
why this was an invariant gap and not a bug.

[FACT] The three closed ref regimes each gained one `if_neg` at their
`evalRExpr` unfolding, and the discharge pattern is telling: L→L and F→L
close by `Nat.lt_irrefl` (a whole local's range against itself), P→L by
`PathTo.offset_add_size_le` — the typing lemma now doing SOURCE-side
duty as well as target-side. Whole repair: three lines-of-thought,
~15 minutes.

[FACT] The gap example is now PINNED as tests, all three corners:
- t16 (`tests.lean`): the junk state itself, encoded as DATA — run a
  legitimate prefix (`p := &mut x`), then forge the stored pointer's
  size to 0, then step `L := &mut *p`: must err with "out-of-bounds
  range". Teeth verified: with the check reverted, t16 fails with
  "expected err, got ok" — the literal pre-fix behaviour. This is the
  suite's first STATE-level test (a state no program reaches, expressible
  because `mirlite.State` is just data); the technique generalizes to any
  future invariant-gap finding.
- d30: the reachable reborrow `L := &mut *p`, write through it — the
  check must NOT fire (differential ok on both machines).
- d31: the ZST twist — reborrow through a zero-sized pointee, where the
  SAME numeric shape (`size 0`) is legitimate: the bound is typed, and
  only the event has the type.

[OPEN] The deref-source ref regime (`L := &kind *p`) is now UNBLOCKED at
the model level: source success at the retag event implies the target
`Borrow`'s bound via `MemValSim`'s `o' = o ∧ s' = s`. The leaf remains to
be proved (spine prelude + P→L-style endgame with loaded-pointer facts).
`refSlice`'s analogous check is deferred with the non-core constructs
(its range is within the fat value's own extent by construction; the
allocation-level question recurs one level up).

Validation: units 16/16 + 44/44, suite pass 82 | fail 0 (123),
differential matched 82 | mismatch 0. Ref regimes re-verified
axiom-clean.

**References:** mirlite_semantics.lean (`.ref`),
2026-08-27-ref-proj-closed.md (the finding), loose-ends/parked.md
(entry now resolved), tests.lean t16, compile_tests d30/d31.
