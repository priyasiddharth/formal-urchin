# mirlite deref resolution is now a real SB read (risk item (a) resolved)

[FACT] `resolvePlaceAcc` added to mirlite: place resolution FOR AN ACCESS
performs an `M.read` of each dereferenced pointer cell — Miri's behavior
(evaluating `*p` reads `p` as an operand) and what the compiled code
already did (`Rhs.Load`). The pure `resolvePlace?` remains only for
genuine raw peeks (`assignIf` discriminants, matching `SkipIf`).
`doAssign` restructured to resolve the destination once, WITH accesses,
BEFORE the rhs — the compiled fragment's order; `alloc`/`dealloc`/
`readAllocLen`/all `evalRExpr` resolutions likewise;
`finishPlaceAssign`/`allocateBaseAndWrite` deleted (dead: prepare
guarantees resolution).

[FACT] This closes the plan's original risk-register item (a): the deref
`Load` was the target's signature extra event, and the divergence was
REAL — `q := &mut p; *p := v; use **q` was source-ok/target-UB before
(no corpus test had the shape). Miri sides with the target. Now both
machines read, and regime D's two walls (Load success, post-Load
PermSim) collapse: the source read's success transports via
`sb_read_respects_PermSim`, no SB-env coherence invariant needed for
deref.

Validation, all green on first run after the change:
- conformance suite UNCHANGED (pass 76 of the Miri corpus — Miri's
  recorded verdicts already assume these reads);
- differential UNCHANGED then extended: matched 77 | mismatch 0;
- t14 (mirlite unit) and d24 (differential) pin the witness — d24 is
  the program that mismatched before the change;
- NEW `conformance/local/` sibling directory for project-authored Rust
  witnesses through the identical charon pipeline, provenance-marked
  "local-model-reasoned" in the manifest (README section added):
  `local/deref_read_disables_sibling` runs end-to-end and errs at the
  reasoned line 13 with the disabled-tag message. Suite is now
  pass 77 / total 117.

Proof impact: const_write proofs re-plumbed to the new `doAssign` shape
(resolveAcc-based hypotheses; regime A delegation intact; same 5
sorries). Regime D's blocker list shrinks to fragment execution only.

[OPEN] Run the pinned Miri on conformance/local/*.rs and upgrade the
provenance from model-reasoned to Miri-verified (needs a Miri build;
parked).
