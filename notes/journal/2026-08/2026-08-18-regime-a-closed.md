# Regime A closed: the first end-to-end statement simulation (audit 4 → 5-but-narrower)

[OBS 2026-08-18] Second increment of the day. Two leaf-layer closures:

**`const_write_stmt_evidence` is total** — the fresh-root branch closed
via the new `ensurePlaceRoot_maps_root` (§D): `ensurePlaceRoot`
establishes its own postcondition, so lowering succeeds whether the
root was pre-mapped or freshly allocated (aggregate desugar).

**REGIME A of the const-write leaf is CLOSED** —
`const_write_local_existing_simulation` proves, end to end, the
simulation of a constant write to a bound local: locate the compiled
fragment (one `CStore`, via `compileStmt_local_existing_run` computing
the compile monad and `compileStmt_emitted_in_compProg` placing it at
the runtime pc), execute it (BRIDGE 2 with its new concrete-conclusion
interface), transport the permission step (BRIDGE 3 — the first real
consumer of the non-wildcard binding-tag fact added to
`LocalBindingSim`), and rebuild every invariant conjunct.
`const_write_resolved_simulation` is now a fully-proved delegation over
destination regimes. This is obseq2's long-parked "Step 4 regime-A
milestone", finally done — and against the corrected PermSim invariant
rather than the false equality.

**Enabling surgery** (this is why the leaf could close):
- `CompilerInv` dropped the never-consumed `CompilerStateWF` conjunct
  (returns strengthened — with a placeRegMap bound — when the proj
  regime needs temp-register collision freedom);
- `LocalBindingSim` now records `(binding.tag == wildcardTag) = false`
  (bound locals are minted by `sb_own`), which is what lets BRIDGE 3
  fire on local writes;
- BRIDGE 2's conclusion became CONCRETE (the exact result state with
  perms from the given `useMut`) so leaves can connect it to BRIDGE 3's
  output without a determinism detour.

[FACT] The remaining 5 sorries (3 const-write regimes + copy + ref) are
each blocked on a NAMED invariant extension — the honest finding of the
attempt: (B) lockstep-allocation conjunct + `sb_own` transport;
(C) strengthened WF + BRIDGE 1∘3 composition; (D) SB-env coherence
(bound locals\' cells carry granting stacks) for read-through-own;
(copy) `sb_read` transport + a bidirectional memory relation
(one-directional `SourceMemSim` does not constrain target cells where
the source is uninitialized); (ref) `sb_ref` transport + tag-bound WF
(mapped/stack tags < NextTag) for extension injectivity. Each is an
invariant-design increment, not a proof-grinding one — exactly the
pattern obseq2\'s comments predicted ("blocking factors for stronger
invariants").

**References:** proof/compiler.lean audit, 2026-08-18-bridges-closed.md,
loose-ends/parked.md.
