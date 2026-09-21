# `alloc` becomes an rvalue; the value package learns to extend memory

[FACT 2026-09-21, verified against 3c69dda+] `RExpr.alloc len : RExpr Γ
(PtrL τ)` replaces `Stmt.alloc dst len`. Semantics: `evalAllocLen`
(static, or `evalCopy` of the `NatL` place yielding one word), then
`allocate` + `M.own` of `n * blockSize τ` units at the watermark; the
value is the pointer. Compiler: `compileAllocLenChecked` — `AllocN`, or
`guardRead p` (the guard's exposed copy read) then `AllocDyn` on the
VALUE register; oseair's `AllocDyn` reads a register, not memory. The
elaborator emits `.assign pd (.alloc len)`. Goldens g8/g9 and d13
unchanged: a local destination lowers in the same order either way.

[FACT 2026-09-21] Why the order mattered: `Box::new`/`std::alloc::alloc`
are calls; the destination is written AFTER they run. The old statement
resolved its destination (deref levels included) BEFORE the length read
and the allocation — the one construct with the other order.

[FACT 2026-09-21] `ValuePkg` generalised (commit 3c69dda): the tail
returns `ρa'` with `AddrRenameIncr ρa ρa'`, `IdentityOnDomain ρa'`, and
`memO` with `output.state = { sM with mem := memO, perms := perms₂ }`,
`SourceMemSim ρa' ρt' memO sR.mem`, `AllocLockstep ρa' memO sR.mem`, in
place of `sR.mem = sA.mem` and `output.state = { sM with perms := perms₂ }`.
The leaves absorb it by INSTANTIATION: each bound seam is called at
`(s_mir := { s_mir with mem := memO })` and `ρa'`; the chain seams take
`SourceMemSim`/`AllocLockstep` against `sR.mem` instead of the start
memory plus `sR.mem = s_osea.mem`; the three fresh-root seams take
`(h_sms1, h_alloc1)` at `memO` in place of the seven start-memory facts
they rebuilt them from. Existing constructors supply `ρa' := ρa`,
`memO := sM.mem` through `SourceMemSim.of_mem_eq`/`AllocLockstep.of_mem_eq`.
Built first try; the whole edit was mechanical. Our reading: the seams
were already parametric in the source state and the renaming, so
"memory the rvalue left" is a free parameter, not a new proof.

[FACT 2026-09-21] The alloc package (proof/alloc.lean): `alloc_step_bundle`
is the shared closing — from `(memS, permsS, env)`/`sR1` related at
`(ρa, ρt, cs1)`, a source `own` and the target's one-step allocation
into `R cs1.nextReg`, everything the tail asks for: `ρa.extendBlock`
at the shared watermark (`AllocLockstep` makes the bases equal),
`ρt.extend` from `sb_own_respects_PermSim`, `AllocLockstep.of_alloc`,
`SourceMemSim.rename_mono` (neither allocation touches a cell),
`LocalBindingSim.insert_fresh_reg`, `StoreStep.rstore`. Constructors:
`AllocN` from the start states (`runN_Assgn_AllocN_step`); `AllocDyn`
from the post-read states of `copy_readRegPkg_flat` with the read's
exposed register as the length (`runN_Assgn_AllocDyn_step`,
`ListRel_word_inv`). The four guard-read lemmas moved from assign_if
into alloc.lean, which sits between copy and assign_if.

[OBS 2026-09-21] Two Lean idioms that bit: `split at h` on a nested
`match (match … with …) with …` splits the OUTER match and leaves the
inner one in `heq`; `simp only at heq` then reduces the constructor
case and a second `split at heq` finishes. And `swap` is Mathlib, not
core — use `case h_2 => …` on `split`'s tags.

[FACT 2026-09-21] Gate: `CoreRhs` is total; `CoreStmt` excludes exactly
`dealloc`. Audit 3 axioms / 0 sorries; units 17/17 + 116/116; corpus
93/0/43; differential 93 matched.
