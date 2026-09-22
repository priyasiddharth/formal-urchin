# `dealloc` is copy's read of the pointer, then a free

[FACT, as of 2026-09-22] `Stmt.dealloc dst` (`dst : Place Γ (PtrL τ)`),
mirlite: `evalCopy` of `dst` (bounds, SB read, initialisation — the one
typed-access discipline every read has), the value must be
`[ptrVal base 0 size tag]`, then `M.dealloc perms base size tag`
(`sb_dealloc`: at every cell the tag exists and grants writes, no item is
protected, the stack is removed) and `Mem.removeRange base size`.
Before 2026-09-22 the pointer read was a bespoke one-cell `M.read` with
no bounds check. Compiler: `readToReg dst` — copy's read with its VALUE
register exposed (`guardRead` is `readToReg` at `NatL`) — then
`Instr.Dealloc reg`, which checks offset 0 against the loaded value and
does the same free. Source: src/obseq3/{mirlite_semantics,compile}.lean.

[FACT] Proof (proof/dealloc.lean): the read is `copy_readRegPkg_flat` at
`PtrL τ` (as `alloc`'s runtime length, proof/alloc.lean); `ListRel_ptr_inv`
turns the related value into a target pointer at the SAME base
(`IdentityOnDomain`) and the renamed tag; `runN_Dealloc_step` is the one
target step. Transports: `sb_dealloc_respects_PermSim` — induction on
the length with the per-cell op named (`deallocCellOp`,
`deallocCellOp_ok_inv`/`_ok_eq`); per cell `SB.find?_transport`,
`splitStack_some_transport`, `ItemSim.grantsWrite_eq`,
`firstProtectedIn_none_transport`, and `StackMapSim.filter_cell`
(removing a cell on both sides; `SB.find?_filter_self` /
`SB.find?_filter_ne`). `SourceMemSim.removeRange` via
`List.lookup_filter_key` on both memories. `AllocLockstep`,
`LocalBindingSim`, both renamings and the counters are untouched.
Dispatch: `CompilerInv_step_dealloc`, a statement leaf in the shape of
the protector frames'.

[FACT] The gate is GONE (same day, later): `CoreRhs`/`CoreStmt`/
`CoreProg` deleted, the roots take no scope hypothesis. See
[[what-compile-correct-actually-says]].
