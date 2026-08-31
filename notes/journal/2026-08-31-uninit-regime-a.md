# `uninit`, regime A — and what the generalization actually costs

Started 2026-08-31, after the last sorry closed. Goal: widen `CoreRhs`
from three rvalues to four by admitting `uninit`.

## [FACT] `uninit` is `constInit` at a general width

    | .uninit => .ok { values := List.replicate (blockSize τ) MemValue.undef
                       values_len := List.length_replicate
                       state := state }

No place to resolve, no `read`/`ref`, `state := state`. The only memory
effect is the surrounding `doAssign`'s `writeResolvedPlace`. Compiled,
it is one `CStore (layoutToTyVal τ) (replicate (blockSize τ) Val.Undef)`
with an EMPTY rhs pre-phase — the same statement shape as `constInit`,
differing only in (a) the value list, (b) `τ` arbitrary rather than
`NatL`, (c) width `blockSize τ` rather than 1.

## [FACT] the one new obligation is free

`MemValSim`'s first clause is `| .undef, _ => True` — an undef source
cell refines ANY target value. So the cell-by-cell relation between the
stored lists is `ListRel_replicate_undef`, four lines by induction.
There is no value agreement to establish at all, which is the part that
costs work in `copy`.

## [OBS] the plumbing was already width-general; only the LEAVES were not

Checked before starting, and it is what makes this cheap:

- `writeThroughPtr_sim` already takes `values`, `vals`,
  `h_vl : values.length = blockSize τ` and
  `h_rel : ListRel (MemValSim ρa ρt) values vals`.
- `runN_CStore_step` already takes `vals` and
  `h_size : vals.length = obseq.typeSize ty`.
- `LocalBindingSim`'s block-domain conjunct
  (`∀ k, k < blockSize τ → ∃ a', ρa (binding.addr + k) = some a'`)
  is exactly `writeThroughPtr_sim`'s `h_dom` at general width. In the
  single-cell `constInit` leaf it was bound and UNUSED.

const_write.lean hardcodes the width only in its own leaves: 114 `NatL`,
56 `Val.Dat`, 20 `MemValue.word`, 39 `NatTy` across 3194 lines.

## [FACT] the shape that generalizes a leaf

Parameterize by the rvalue and its value pair, and thread the compiled
shape as hypotheses — the `h_run0`/`h_val0` pattern ref.lean already
uses everywhere:

    (rhs : RExpr Γ τ) (vs : List MemValue) (vs' : List Val)
    (h_len  : vs.length = blockSize τ)
    (h_rel  : ListRel (MemValSim ρa ρt) vs vs')
    (h_size : vs'.length = obseq.typeSize (layoutToTyVal τ))
    (h_run0 : ∀ cs reg, getPlaceInfo cs loc.idx.1 = some (reg, τ) →
        run (compileStmtChecked (.assign (.local loc) rhs)) cs
          = emit cs [Instr.CStore (layoutToTyVal τ) vs' reg])
    (h_val0 : ∀ cs, ∃ so, value (compileStmtChecked (.assign (.local loc) rhs)) cs = ok so)

`RhsPre` carries a DEPENDENT evidence field (`ev : (dstPtr : Register) →
RExprToEvidence dstPtr expr`), so "the rhs lowers to a single CStore"
cannot be stated as an equation on `compileRExprPreChecked`. Threading
the STATEMENT's run/value instead sidesteps the dependency entirely.

## [OBS] measured cost of regime A

`const_store_local_existing_simulation` (generic) + `constInit`
re-derived as a 12-line instantiation + `uninit`'s run lemma and leaf:
about 170 lines net, four build iterations. Three of the four failures
were mechanical and already in the notes:

- multi-line structure-instance fields must share a column (twice: the
  `{ s_osea with perms := …, mem := …, pc := … }` and the evidence
  record) — flatten records onto one line;
- `ListRel` is a DEF, not an inductive, so `⟨rfl, trivial⟩` cannot
  elaborate against it while the lists are metavariables. Pass
  `(vs := …) (vs' := …)` explicitly, or wrap in `by exact`.

Only one was a real thinking error: `h_useMut_tgt` speaks of
`vs.length`, so the rewrite to `vs'.length` is
`← ListRel.length_eq h_rel` ALONE — adding `h_len` overshoots to
`blockSize τ`.

## estimate for the rest

Nine leaves in the const-write taxonomy; regime A is two of them. What
remains: regime B (fresh local), the five projected-destination leaves
(zero/offset/fresh x local-base, plus the two deref-base ones), regime D
(deref chain), then the three dispatchers and the flatten transfers,
then `CoreRhs`/`CoreStmt` and `compile_correct`'s case split. The leaves
are longer than regime A but the substitution is the same one.

NOTE: `CoreRhs` must NOT be widened until the whole dispatcher is total.
Until then this work changes no theorem statement — the audit and the
scope note are unaffected.
