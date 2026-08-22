# `AllocLockstep` wired: `CompilerInv` at nine conjuncts, regime B fully unblocked

[FACT] `CompilerInv` (proof/common.lean) carries a ninth conjunct,
`AllocLockstep s_mir.mem s_osea.mem`, defined as
`mem_osea.addrStart = mem_mir.addrStart`. Both machines use the same bump
allocator (`mirlite.allocate` and `oseair.allocate` are the same function
over their own `Mem`), so equal watermarks means corresponding fresh
allocations return the SAME base address. `AllocLockstep.allocate_eq` is
the consumer-facing form: the two allocations agree AND the property
survives them.

[FACT] Why the invariant needs it rather than the leaf: `IdentityOnDomain
ρa` is already a conjunct, and it is FALSE the moment the two machines
hand out different addresses for corresponding allocations. So a fresh
local can only extend ρa by `.refl` if the allocators are in lockstep, and
that has to be an invariant because it is a property of the whole
execution history, not of the statement being simulated.

[OBS 2026-08-22] Cheaper than the `TagRenameBounded` wiring, which was
itself cheap. Two construction sites got one bullet each — a store moves
no watermark, so `AllocLockstep.writeWordSeq` plus the two
`*_writeWordSeq_addrStart` inductions discharge both — and
`loadSpine_lowering_sim` needed NO change at all, because the spine never
touches memory on either machine (its `s_osea'.mem = s_osea.mem`
conclusion already existed, and source resolution does not write). Total
diff: two files, ~70 lines, most of it the new definitions.

[EMP] Two invariant-conjunct increments in one afternoon, both landing in
about an hour, both with the same shape: define the fact, prove that the
ops the closed regimes actually perform do not disturb it, add one bullet
per construction site. The reason it stays cheap is structural —
`CompilerInv` is CONSTRUCTED in only two places (regime A and the deref
spine); every other theorem that mentions it either takes it as a
hypothesis or passes it through a delegation. Expect the same for any
further conjunct until a third construction site appears (regime B will
be the third).

[OPEN] `const_write_fresh_local_simulation` (regime B) has no machinery
blockers left. Its remaining work is all leaf-local: invert mirlite's
`allocateBase` (allocate, then `M.own`, then bind the local), execute the
target's `Alloc` fragment, and extend `SourceMemSim`/`LocalBindingSim` at
the new cell. The `sb_own` member supplies the permission step and the ρt
extension; `AllocLockstep.allocate_eq` supplies the address agreement.

Validation: units 15/15 + 38/38, suite pass 77 | fail 0 (117),
differential matched 77 | mismatch 0 | skipped 0, obseq2 green. Proof
layer only. Audit stays at 5 sorries; closed leaves stay axiom-clean.

**References:** proof/compiler.lean (audit),
2026-08-22-tagrenamebounded-wired.md, 2026-08-22-sb-own-member.md.
