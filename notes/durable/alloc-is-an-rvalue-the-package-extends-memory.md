# `alloc` is an rvalue; its value package extends memory

[FACT, as of 2026-09-21] `RExpr.alloc len : RExpr Γ (PtrL τ)` with
`AllocLen := const n | fromPlace (p : Place Γ NatL)`. mirlite
(`evalAllocLen`, then `allocate` + `M.own` of `n * blockSize τ` units at
the watermark; the value is `ptrVal base 0 units tag`); compiler
(`compileAllocLenChecked`: `AllocN ty n`, or `guardRead p` — copy's read
of `p` with its register exposed — then `AllocDyn ty lenReg`, which
reads the VALUE register, never memory). The statement form
`dst := alloc len` is an ordinary `assign`, so `Box::new` and
`std::alloc::alloc` are evaluated BEFORE their destination is written,
as calls are. Source: src/obseq3/{syntax,mirlite_semantics,compile}.lean,
src/conformance/elab.lean (`.alloc dst szOp ↦ .assign pd (.alloc len)`).

[FACT] Why it is in the theorem: `ValuePkg` (proof/spine.lean) hands back
a GROWN address renaming `ρa'` (`AddrRenameIncr ρa ρa'`,
`IdentityOnDomain ρa'`) and the source memory the rvalue left, `memO`,
with `output.state = { sM with mem := memO, perms := perms₂ }`,
`SourceMemSim ρa' ρt' memO sR.mem`, `AllocLockstep ρa' memO sR.mem`.
Before 2026-09-21 it promised `sR.mem = sA.mem` and an unchanged source
memory. Every destination leaf consumes the new form by instantiating
its write seam at `(s_mir := { s_mir with mem := memO })` under `ρa'`;
no seam gained a new proof. Every leaf returns `∃ ρa'`. The other
packages (constant store, the read packages, ref, move) supply
`ρa' := ρa`, `memO := sM.mem` via `SourceMemSim.of_mem_eq` /
`AllocLockstep.of_mem_eq` (common.lean).

[FACT] The package (proof/alloc.lean): `alloc_step_bundle` is the
shared closing over any related pair of states and a one-step target
allocation into `R cs1.nextReg`; `alloc_const_valuePkg` establishes the
step from the start states (`runN_Assgn_AllocN_step`),
`alloc_fromPlace_valuePkg` from the post-read states of
`copy_readRegPkg_flat` (`runN_Assgn_AllocDyn_step` with the read's
exposed register). `ρa` grows by `extendBlock` at the SHARED watermark
— `AllocLockstep` is what makes the two bases equal — exactly as a
fresh-root destination grows it. Dispatch: `CompilerInv_step_constStore`
/ `assignStep_constStore`, which are generic over any `ValuePkg`.

[FACT] What `dealloc` would need, by contrast: memory SHRINKS
(`Mem.removeRange`), so `SourceMemSim` must be shown on the cells that
remain and `AllocLockstep`'s table must drop the entry on both sides; a
die-like transport of `M.dealloc` along `PermSim`. It is the one
statement left outside `CoreStmt`. See
[[what-compile-correct-actually-says]].
