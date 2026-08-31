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


## progress log (appended as leaves land)

| leaf family | generic name | instances | notes |
|---|---|---|---|
| A, bound local | `const_store_local_existing_simulation` | `const_write_local_existing_simulation`, `uninit_local_existing_simulation` | done |
| B, fresh local | `const_store_fresh_local_simulation` | `const_write_fresh_local_simulation`, `uninit_fresh_local_simulation` | done; ρa extends by `extendBlock`, not `extend` |
| C0, proj at offset 0 over a bound local | `const_store_proj_zero_simulation` | `const_write_proj_zero_simulation`, `uninit_proj_zero_simulation` | done |
| C1, proj at nonzero offset | `const_store_proj_offset_simulation` | both | done (BRIDGE 1) |
| C-fresh, proj over an unbound root | `const_store_proj_fresh_simulation` | both | done; `extendBlock` correction |
| C-deref0 / C-deref | `const_store_proj_deref_{zero,}_simulation` | both | done |
| D, deref chain dst | `const_store_deref_chain_simulation` | both | done |
| dispatchers + flatten transfers | `const_store_{proj,deref,resolved}_simulation`, `ConstStoreFrags` | both | done |
| `CoreRhs`/`CoreStmt` + `compile_correct` | — | — | DONE — `uninit` is a core rvalue |

## [FACT] the width-generalization checklist, per leaf

Every leaf needs the same six edits. Recording them so the remaining
ones are transcription, not thought:

1. `{loc/path at NatL}` -> add `{τ : LayoutTy}`, retype.
2. drop `(v : Word)`; add `{vs} {vs'}` and
   `h_len : vs.length = blockSize τ`,
   `h_rel : ListRel (MemValSim ρa ρt) vs vs'` (rename-POLYMORPHIC in any
   leaf that extends a rename before the store),
   `h_size : vs'.length = obseq.typeSize (layoutToTyVal τ)`.
3. thread the compiled fragment as `h_frag`/`h_fragval` keyed on
   `getPlaceInfo cs loc.idx.1 = some (reg, σ)` — the rhs-specific run
   lemma cannot be shared, because `compileRExprPreChecked rhs` does not
   reduce for a variable rhs. Generate its uninit twin by substitution.
4. `h_useMut_tgt` speaks of `vs.length`; `writeThroughPtr_sim` wants
   `vs'.length`. Bridge with `rw [← ListRel.length_eq h_rel]` ALONE.
5. `writeThroughPtr_sim`'s `h_dom` was `Nat.lt_one_iff` + the base fact
   at width one. At general width it is `LocalBindingSim`'s block-domain
   conjunct (bound local) or `AddrRenameMap.extendBlock_mem` (fresh
   root). For a PROJECTED destination it additionally needs
   `PathTo.offset_add_size_le path` to get `k < blockSize σ` from
   `k < blockSize τ`.
6. `runN_CStore_step`'s `rfl` becomes `h_size`.

## [OBS] insert ABOVE the docstring, always

Inserting the two instances at anchor `\ntheorem const_write_proj_offset_simulation`
landed them between that theorem's docstring and the theorem, giving
"unexpected token '/--'". Already in the notes from an earlier session;
hit it again. When inserting before a documented theorem, anchor on the
docstring's opening `/--`, not on `theorem`.


## [FACT] the dispatchers needed a BUNDLE, not more threading

Three dispatcher levels each route to several leaves, and each leaf now
takes two or three rvalue-specific fragment hypotheses. Threading them
individually would have put ~20 arguments on every dispatcher.

`ConstStoreFrags rhs vs'` is the bundle: nineteen fields, one per
(destination shape x run/value/StateIncr), each universally quantified
over the place so a dispatcher can instantiate it at
`flattenPlace ptrPlace` and friends. `constInit_frags` and
`uninit_frags` prove it once each, every field a one-liner over the
existing fragment lemmas.

**Why a bundle and not a generic proof:** for a variable `rhs`,
`compileRExprPreChecked rhs` does not reduce, so NO fragment lemma can
be proved generically. The bundle does not avoid that — it just stops
the un-provable-generically part from infecting every signature.

## [OBS] reading undef is NOT ub — only OBSERVING it is

The first teeth for d91 dropped a re-initialisation so the program read
an undef cell, expecting ub. It came back `.ok`: `readWordSeq` returns
`MemValue.undef` for a missing cell and a `copy` is happy to move it.
Only the operations that INTERPRET a word err — a deref (`deref of a
non-pointer value`), a branch discriminant, an alloc length.

This is exactly what makes `MemValSim`'s `| .undef, _ => True` sound,
and it is the reason `uninit` costs almost nothing to admit: an undef
source cell imposes no obligation on the target cell at all.

The teeth that DO bite: make the pointer itself undef
(`p := uninit` in place of `p := &mut s.0`) and then deref it — ub at
that statement on both machines.

## [FACT] `uninit` is now a core rvalue

`CoreRhs` admits `constInit`, `copy`, `ref`, `uninit`;
`compile_correct`'s case split routes `.uninit` to
`CompilerInv_step_uninit`. The audit is unchanged (two roots, zero
sorries) — what changed is the SCOPE of the theorem, which now covers
undef-fill of any place at any layout type.
