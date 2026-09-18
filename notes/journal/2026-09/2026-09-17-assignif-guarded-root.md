# A guard rooted its destination only on the taken path

[OBS 2026-09-17] **The compiler had a real bug at `assignIf`, found by a
differential probe, not by the corpus.** `rs_guarded_fresh_root_then_write`
(compile_tests.lean): `d := 0; if d == 1 { x := 5 }; x := 7; halt` with
`x` never written before the guard. mirlite: the guard is skipped, `x`
stays unbound, the third statement allocates it — `.ok`. The target
said `.ub 2`: `compileAssignChecked` inside the guarded block called
`ensurePlaceRoot x`, which emitted `x`'s root `Alloc` INSIDE the block
and recorded `x ↦ R1` in `placeRegMap` at compile time; the skip jumped
over the `Alloc`, and statement 2 compiled as a store through `R1`,
which nothing had assigned. A compile-time map with a run-time
precondition that only one path establishes.

[OBS 2026-09-17] **The corpus cannot reach it.** `emitSeamCopy`
(lowering.lean, the `.enum` arm) emits `dst.0 := copy src.0` before
every `assignIf` on `dst.(1+i)`, so a guarded destination's root is
always already written. That is why 82/0/41 and 82 matched said
nothing; the probe was written while planning the proof's skipped arm,
where "the body changed no `placeRegMap` entry" was the fact the arm
needed and could not have had.

[FACT 2026-09-17, verified against 64d5c78+ (the fix commit)] **Fix: both machines allocate the destination's root
local before the discriminant read, on both paths.** mirlite gains
`ensureRoot` (allocate the root local if unbound; recurse through proj
and deref, as the compiler's `ensurePlaceRoot` does) and the `.assignIf`
arm runs it first; the compiler's arm calls `ensurePlaceRoot dst` before
`guardRead discr`. The guarded body's own `ensurePlaceRoot` then finds
the root mapped and is silent. Verdict-neutral: units 108/108 (g11's
stream unchanged; the new golden g12 shows `Alloc; Load; SkipIf`),
corpus 82/0/41, differential 82 matched, and the probe passes with
`.ok` on both machines.

*Why this and not a compile-time rejection.* A compiler that rejects a
guarded write to a never-written local would keep `compile_correct`
honest (it quantifies over programs that compile) and is corpus-safe,
but it is a scope cut where the model is what is wrong: a MIR local's
storage exists whether or not a branch writes it; mirlite's lazy
first-write allocation is an abstraction of `StorageLive`, and a guard
is exactly where it becomes path-dependent. Allocating the root at the
statement, as `assign` already does before evaluating its rvalue, makes
it path-independent again. A target-only hoist was never an option —
`AllocLockstep` is in the invariant. Recorded in
durable/already-rejected-design-alternatives.md.

[FACT 2026-09-17] **The arm's proof is the sum of existing parts plus
one new step.** proof/assign_if.lean: `ensureRoot_simulation` (the root
step — `copy_freshroot_prologue` + `runN_Assgn_Alloc_step` when unbound,
nothing when bound), `copy_readRegPkg_flat` (copy's read package with
its register exposed, from the previous session), two `SkipIf` step
lemmas, and then either the plain assign leaf from the fall-through
state (`AssignLeaf`, one `assignStep_*` per rvalue) or, on the skip,
`CompilerInv.ofInvAt` at the statement's end, where
`compileAssignChecked_placeRegMap_of_mapped` — the never-run body kept
the place map BECAUSE its root was already mapped — is exactly the
bug's negation. `assignIf` is in `CoreStmt` with `CoreRhs rhs` and no
shape condition. Net: +900 lines of proof, one new compiler definition
(`guardRead`, no code change), audit unchanged.

[HYP 2026-09-17] **`compileStmtChecked`'s `.assign (.local loc)` fast
path could go.** It is not `rfl`-equal to `compileAssignChecked (.local
loc) rhs` (commit dc164ad's "by rfl" holds only for non-local
destinations); the arm proof bridges them with
`compileAssignChecked_local_run/_value` (an `emit cs []` and a lookup).
Deleting the arm would make the bridge `rfl` at the cost of re-proving
~15 local-destination compile lemmas through `placeToRegChecked Mut
(.local loc)`. Parked.

[OBS 2026-09-18] **Confirmed and done the next day, at the user's
request ("delete the local fast path then").** The cost estimate was
wrong in the right direction: not ~15 lemmas re-proved, but ten sites
each repaired by one rewrite, because the general path can be restated
in the fast path's SHAPE once (`compileStmt_local_run`,
`compileStmt_local_value_iff`, common.lean) — the destination lookup
returns the register the root step recorded because the rvalue
lowering kept the place map, which is the same lemma family the
guard's skipped arm needed. The user's question that led here —
*why does the root step discard the register?* — has the answer that
made the deletion obviously safe: `ensurePlaceRoot` is a side effect
on the place map, not a destination computation; the store register
comes from lowering the whole place, and a local is the one shape
where the two coincide, so the fast path was an optimization of
nothing. Net −90 lines; audit unchanged.

## See also

- assignif-reads-its-discriminant.md
- protectors-and-the-charon-inlining-seam.md
- one-leaf-per-destination-shape.md
- already-rejected-design-alternatives.md
