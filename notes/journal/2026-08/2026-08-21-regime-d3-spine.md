# Regime D closed for all load-spine depths: the spine mother lemma

[FACT] `const_write_deref_spine_simulation` replaces the depth-1 D1
proof and the D2/D3 residuals: a constant write through ANY all-deref
pointer chain over a bound local (`*p := v`, `**q := v`, deeper) now
simulates end-to-end. The engine is `loadSpine_lowering_sim`
(proof/spine.lean, new file): an induction over `LoadSpine` places
(local | deref of spine) showing the compiled `Load` chain executes,
ending with a register holding the ρ-renamed resolved pointer, the
threaded permission state `PermSim`-related, memory untouched,
`LocalBindingSim` intact, `placeRegMap` unchanged, counters monotone.
Regime D's residual is now a single named sorry
(`const_write_deref_nonspine_simulation`): a projection anywhere in the
chain, whose `Borrow` lowering shares regime C's `sb_ref`-transport
blocker. Audit: 6 → 5 sorries, with strictly more closed than before.

[FACT] The proof needed one more mirlite semantics alignment (found by
attempting the induction, not by testing): the target `Load` bounds-
checks a loaded pointer (`offset < size`) before reading through it,
but mirlite's deref resolution read through intermediate pointers
unchecked — SB alone as the oracle. Unprovable as stated: a stored
out-of-slice pointer with a surviving stack would make the source
succeed where the target errs; excluding it needs a perms↔mem coherence
invariant (heavy) or the mirrored check (small, Miri's dereferenceable
requirement, and the read-side mirror of `writeResolvedPlace`'s
existing write bounds check). Took the check: `resolvePlaceAcc`'s deref
now errors on out-of-bounds pointers before the SB read. Validated:
Miri corpus unchanged (pass 77/117), differential 77/0/0, new unit t15
+ differential d25 pin the OOB-deref alignment (ptrOffset out of
bounds, then nested deref: UB at the same statement on both machines).

[FACT] New reusable pieces beyond the mother lemma:
`placeInputsMapped_of_resolveAcc` (resolution success → root mapped),
`LocalBindingSim.placeRegMap_congr` (binding sim transfers across
equal-map compiler states — needed because fragment-run states are
opaque, so the D1-era defeq transfer trick fails), and the
`StateIncr`-based fragment-installation threading: sub-fragment code
containment follows from `CheckedCompilerM.incr` + bind decomposition,
with no need to know the sub-run's closed form — this is the pattern
every multi-fragment statement proof (copy, ref, dealloc) will reuse.

[EMP] (Lean 4.28) new potholes: `induction` on an inductive-Prop family
fails when the target's type index is not a variable — index the
predicate by the pointer shape (`Place Γ (PtrL τ)`) instead of a bare
type so the indices stay variables; `split at` on deeply nested
match-chains leaves generalized scrutinees (`x✝`) that orphan
`rename_i` names — unfold with `cases h : <scrutinee>` + `simp only
[h] at` per level instead; a chain of `simp only [run_bind,
value_bind]` unfolds monadic tails past the point where
`CheckedCompilerM.incr` can unify — rewrite with single `rw
[run_bind]` steps and keep tails folded.

[OPEN] The write-consumer replays the final Load manually because the
mother lemma is stated for pointer-TYPED spines; a `.deref`-headed
variant returning write-ready facts could absorb those ~80 lines when
copy's deref regime lands.
