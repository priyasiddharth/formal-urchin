# [FACT] ref_place_residual: the eight sites, and one class that never existed

Tags: obseq3, ref, residual, site-map

`obseq3.proof.ref_place_residual` is the ONLY `sorry` left in
`src/obseq3` (verified 2026-08-31 by `grep -rn sorry src/obseq3` and by
`scripts/audit_axioms.sh`). ONE call site.

The count is NOT monotone and is not the metric. It went 12 -> 6 as
whole classes closed, then 6 -> 8 when the projected-destination source
recursion split one coarse residual arm into three narrow ones while
CLOSING `t.g := &kind s.f` and `t.g := &kind (s.f).h`, then back to 6
when the same-unbound-root leaves closed two of those. Read the class
table, not the count.

## the map

Enumerated by walking the `cases` arms enclosing each
`exact ref_place_residual` in `src/obseq3/proof/ref.lean`.

| statement shape | sites |
|---|---|
| PROJECTED dst over a DEREF base — `(*p).g := &_`, any src | 1 |

The destination is itself a chain (`derefProj`), so this is the
destination-spine mirror of the two-mother leaf — with the extra twist
that the projection at NONZERO offset also mints an interior
`Borrow(Mut)` whose `Die` BRIDGE 1 must collapse. Donors:
`ref_derefdst_derefprojsrc_simulation` for the two mothers,
`ref_proj{zero,offset}_derefsrc_simulation` for the projection over a
spine-free base.

## [FACT] two mothers is cheap when both cleanups are empty

Closing `*chain := &kind (*p).f` took 453 lines FIRST TRY, against
copy's two-mother leaves which are far longer. The difference is that
both `placeToRegChecked (.deref _)` calls return `cleanup := []`, so the
statement's whole emitted shape is known BEFORE either mother runs, and
each code-inclusion obligation is one `StateIncr` step off `h_stmtRun`
instead of a hand-assembled tower. See
journal/2026-08-31-ref-two-mothers.md.

## [FACT] the nil-projection eta relates `*P` and `(*P).nil`

`flattenPlace` never introduces an empty projection, so it cannot
relate the two spellings — but `resolvePlaceAcc` adds `PathTo.offset
.nil = 0`, and the two compiled lowerings emit the same instructions
from the same register counter (`placeToRegChecked`'s deref arm returns
`cleanup := []`, so the projection arm's `[] ++ [tmp]` is `[tmp]`).
`stepStmt_assign_refsrc_nil` + `placeToBorrowRegChecked_nil_agree`.
Under a projected destination it CLOSES the plain-deref-source site;
under a deref destination it MERGES that site into the projected one.
See journal/2026-08-31-ref-nil-projection-eta.md.

Class 1 needs TWO mother-lemma applications in one statement (`copy`'s
two-mother skeleton is the donor); class 2 needs the spine mother lemma
on the DESTINATION side, which no ref leaf does yet.

A deref-rooted source under a plain LOCAL destination is CLOSED
(2026-08-31) — that half of class 1 needed only one mother lemma.

## [FACT] "non-spine deref sources" is not a class

Earlier docstrings (and the commits of 2026-08-31 that copied them)
listed "non-spine deref srcs" among the remaining work. There is no
such thing:

```lean
theorem PtrChain_flatten_deref {Γ : Ctx} {τ : LayoutTy}
    (p : Place Γ (obseq.LayoutTy.PtrL τ)) :
    PtrChain (Place.deref (flattenPlace p))     -- spine.lean:420
```

holds for an ARBITRARY `p`. Flattening normalizes any deref place into
the `PtrChain` grammar, so every deref source is a spine and the mother
lemma always applies to it. The residual's deref-source sites (classes
1 and 4) are blocked by their DESTINATIONS, not by their sources.

Corrected in `ref_place_residual`'s docstring and in the SORRY AUDIT
block of `obseq3/proof/compiler.lean`.

## [HYP] what the classes are likely to cost

- Class 3's `(s.f).h` half looks like a src-flattening transfer away
  from the already-closed proj-over-local leaves — the ref analogue of
  `compileStmt_assign_derefdst_flatten_run`, generalized over the src
  rather than the rhs. Cheap if it goes through.
- Class 2 is the one the dst-flattening recursion structurally cannot
  reach: flattening keeps the `deref`, so `(*p).g` never becomes a
  projection over a local. It needs the spine mother lemma on the
  DESTINATION side, which no ref leaf does yet.
- Classes 1, 4 and the `(*p).f` half of 3 all pair a spine-lowered src
  with a non-local dst, i.e. two mother-lemma applications in one
  statement. `copy` already does that (its two-mother skeleton), so
  that is the donor to look at, not another ref leaf.

## [FACT] the source-flattening transfer (2026-08-31)

`placeToBorrowRegChecked` has its OWN reassociating arm:

```lean
  | .proj (.proj b q) p => do
      let out ← placeToBorrowRegChecked kind prot mask (.proj b (q.append p))
      ...
```

with the comment "REASSOCIATE nested projections ... `&mut s.1.0` must
not route through a wide Mut borrow of `s.1`". So the compiler already
flattens nested projection borrows, and the transfer is a theorem about
code the compiler was written to produce, not a new normalization.

Probed before proving anything: for `(s.1).1` with offsets 2 and 1, and
for a three-layer `((s.1).1).1` with offsets 4, 2, 1, both spellings
emit ONE `Borrow` at the summed offset (3, then 7), with the same result
register and cleanup. `#eval` on `.nextLabel` and on `.code 0` settled
in one run what would otherwise have been a guess.

Landed:
- `placeToBorrowRegChecked_flatten_agree` — the borrow mirror of
  `placeToRegChecked_flatten_agree`, same case structure.
- `stepStmt_assign_refsrc_anyflatten` — generalizes
  `stepStmt_assign_refsrc_flatten` from a deref src to ANY src.
- `compileStmt_ref_src_congr_local_run/_value` — the CONGRUENCE both
  statement-level transfers factor through, plus the flatten and
  reassoc instantiations.
- `ref_proj_src_local_simulation` — the recursion, mirroring
  `ref_proj_dst_simulation`.

## [OBS] why the congruence, and not a rewrite

The obvious proof of the reassociation transfer is to rewrite the source
place with `flattenPlace_srcproj_assoc` inside
`CheckedCompilerM.value (compileStmtChecked (.assign dst (.ref .. src)))`.
That fails with "motive is not type correct": the value's type is
`Except String (ResultWithEvidence Unit (fun _ => StmtEvidence stmt))`,
so the RESULT TYPE mentions the statement, and changing the place
changes the type of the `so` being produced.

Factoring through a congruence lemma whose hypotheses are the two
agreement facts about the BORROW lowering avoids touching the place
under `compileStmtChecked` at all. Worth reaching for whenever a
transfer is about a subterm of an evidence-carrying compiled statement.

## [FACT] the recursion generalizes by destination shape, not by source

Extending the source-flattening recursion from a local destination to a
DEREF destination (2026-08-31) took only:

- `compileStmt_ref_src_congr_deref_run/_value` — the same congruence
  with `CompilerM.run (ensurePlaceRoot (Place.deref P)) cs` as the base
  state instead of `(ensureLocalRegE dstLoc).run cs`;
- the two reassociation instantiations;
- `ref_proj_src_deref_simulation`, textually the local recursion with
  the base case additionally flattening the DESTINATION chain and
  composing both transfers into the threaded `stmt0`.

Everything source-side — `placeToBorrowRegChecked_flatten_agree`,
`stepStmt_assign_refsrc_anyflatten`, `flattenPlace_srcproj_assoc`,
`placeToBorrowRegChecked_projassoc_agree` — was reused unchanged. The
per-destination cost is the congruence plus the recursion skeleton; the
source theory is written once.

One difference worth noting: the deref congruence's VALUE direction
needs an extra case split that the local one does not. With a local
destination, once the borrow lowering succeeds the rest of the
compilation cannot fail; with a deref destination the destination's own
`placeToRegChecked` can still fail, so its success has to be extracted
from the hypothesis before concluding.

## [FACT] the one shape index disjointness does not reach (2026-08-31)

Every fresh-destination leaf so far discharged the "both roots unbound"
branch by showing the two locals cannot share an index:

- `ref_dst_src_idx_ne` — types: `τ ≠ PtrL τ`;
- `ref_proj_dst_src_idx_ne` — `cases f` on an impossible `PathTo`;
- `ref_dst_src_idx_ne_of_proj` — `PathTo.sizeOf_le`.

For a PROJECTED destination with a PROJECTED source there is no such
argument, and none is possible: `g : PathTo σ (PtrL τ)` and
`f : PathTo σ τ` can both leave the same layout, so `t.g := &kind t.f`
with `t` fresh is well-typed and REACHABLE. The allocation binds the
source root, the borrow reads nothing (only `&mut` of uninitialized
memory), and the step succeeds.

So this is not a vacuous branch to be discharged — it is a real
behaviour. CLOSED 2026-08-31 by
`ref_proj{zero,offset}_fresh_selfsrc_simulation`: the source binding is
the one `allocateRoot` just made, its register is the root register the
`Alloc` produced (`getPlaceInfo_setPlaceInfo_self`, not a survival
argument), and every source fact — address, tag, non-wildcard, block
domain — comes from the extended renames instead of `h_lbs` on the
pre-state.

Two mechanical notes from that derivation:

- `h_rtS1` and the non-wildcard fact are needed at `sb_ref_respects_PermSim`,
  which sits EARLIER than where the distinct-root leaves define them.
  Hoist `h0`/`h_nwD` above §5.
- `induction sbase` gives the source base's layout an INACCESSIBLE name,
  so `σb` from the theorem binders is not the one in scope. Bind it in
  the case pattern — `| @«local» σ' srcLoc =>` — or the layout-equality
  step cannot even be stated.

## [FACT] a deref-rooted source costs nothing extra over a plain deref

`placeToRegChecked`'s DEREF arm ignores its `kind` argument entirely —
it lowers the pointer place at `Shared`, `Load`s, and emits the
cleanup:

```lean
  | .deref ptrPlace => do
      let ptrOut ← placeToRegChecked RefKind.Shared ptrPlace
      ...
```

So `placeToBorrowRegChecked kind prot mask (.proj (.deref P) f)` — which
lowers its base with `placeToRegChecked kind (.deref P)` — emits exactly
the chain code a plain `&kind *P` emits, and differs only in the
`Borrow`'s offset operand. That is why the mother lemma can be invoked
at `kind` rather than `Shared` and consumed unchanged, and why
`ref_derefprojsrc_local_simulation` is `ref_deref_local_simulation`
under the same offset substitution used five times before.

One arithmetic wrinkle: the two machines spell the stored pointer's
offset differently — mirlite as `addr + off - allocBase`, oseair as
`addr - allocBase + off`. They agree only given `allocBase ≤ addr`,
which the mother lemma supplies as `h_dle`; `Nat.sub_add_comm h_dle`
is the bridge. `omega` reports a spurious counterexample over
compiler-state atoms if handed the goal without that hypothesis
threaded, so name the equation rather than inlining a tactic.

## [FACT] a projected destination over a LOCAL base has no spine

Recorded 2026-08-31 while closing `t.g := &kind (*p).f`. The
destination's lowering at zero offset IS the root register, and at
nonzero offset is one `Borrow` from it — no `ptrChain_lowering_sim`
involved. So a chain SOURCE under such a destination needs only ONE
mother lemma, and the four leaves are the destination's four quadrants
(offset zero/nonzero x root bound/fresh) with the source spine spliced
in.

That halved what looked like a uniform four-site class. Only the two
DEREF-destination sites genuinely need two mother lemmas.

## [OBS] the destination-side package does NOT collapse the quadrants

Considered and rejected 2026-08-31, having first claimed it would work.
`LoweringSim` — the named conclusion of `ptrChain_lowering_sim` — is
already the destination package for the shapes that supply it, and a
projected destination at ZERO offset does
(`LoweringSim.projZero`). But it demands `placeOut.result.cleanup = []`
(spine.lean), and `placeToRegChecked`'s projection arm at NONZERO offset
returns `cleanup := baseRes.cleanup ++ [(tmpReg, blockSize τ)]`
(compile.lean). So the package covers exactly the two zero-offset
quadrants — the ones that were already cheap — and covering the other
two would mean restating it WITH the cleanup and packaging BRIDGE 1,
whose proof is the very assembly the package was meant to avoid.

Check the `cleanup = []` conjunct before proposing a package for any
lowering that mints a temporary.
