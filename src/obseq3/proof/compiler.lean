import obseq3.proof.const_write
import obseq3.proof.copy
import obseq3.proof.ref

/-!
Top-level compiler-correctness theorems for the proof-core fragment
(`CoreProg`: halt / assign with constInit/copy/ref), port of
`obseq2/proof/compiler.lean`. Both theorems are complete modulo the audited
sorries below.

## SORRY AUDIT (the skeleton's obligation graph)

CLOSED:
- ✔ BRIDGE 1 `sb_ref_use_die_cancels` (proof/keystone.lean, 2026-08-15):
  Borrow(Mut);use;Die ≡ the bare parent access up to NextTag, via the
  `setChain` normal form for move-to-front assoc-list folds.
- ✔ BRIDGE 2 `writeThroughPtr_sim` (proof/common.lean §G, 2026-08-18):
  range memory-write simulation via `SourceMemSim.writeWordSeq_extend`.
- ✔ BRIDGE 3 `sb_write_respects_PermSim` (proof/permsim_transport.lean,
  2026-08-18): the ρt-transport family (ListRel transports, beq/Item
  transports, splitStack/firstProtectedIn/writeCellContent transports,
  relational setChain) — non-wildcard acting tags (core programs cannot
  mint wildcards; resolveWildcardIn transport deferred with the
  non-core constructs).
- ✔ `placeToRegChecked_emits_preserves_mem` (common.lean §E, 2026-08-18).

- ✔ BRIDGE 3 family COMPLETE — all five range ops. The minting side is
  `sb_ref_respects_PermSim` and `sb_own_respects_PermSim`
  (proof/permsim_transport.lean, 2026-08-22): the two ops that GROW ρt.
  Both machines mint at their own counter, so the statements conclude for
  `ρt.extend srcFresh tgtFresh`; well-formedness of that extension is
  exactly `TagRenameBounded` (common.lean), the tag half of the
  strengthened WF this audit has been naming: the range bound puts the
  target's fresh tag outside ρt's range (injectivity) and the domain
  bound puts the source's outside its domain (so the extension is a
  growth). Supporting machinery: `insertAboveContent` factored out of
  `insertAboveCell` and `refCellOp` factored out of `sb_ref` (both in
  sb.lean, behavior-preserving — suite 77/117, differential 77/0/0, units
  15/15 + 38/38 unchanged), `refCellContent`/`refCellStep` collapsing each
  retag variant to one stack rewrite, `insertAboveContent_transport`,
  `refCellContent_transport`, and `foldCellsIdx_ok_of_cells` (the
  construction counterpart of `foldCellsIdx_ok_inv`, in keystone.lean).
  `sb_own` reuses all of the ρt-extension algebra and adds only
  `ownCellStep` + `foldCells_ok_iff_foldCellsIdx_ok` (keystone.lean):
  `ownCell` is the one cell op that succeeds on a MISSING stack, so it
  needs the indexed fold's `Option`-shaped characterizations, which the
  index-free `foldCells_ok_inv` does not provide.

`LocalBindingSim` gained a referent-range conjunct 2026-08-22 (every
bound local's WHOLE block is in ρa's domain, not just its base) —
`MemValSim`'s own range obligation is what forces it, for a `&local`
whose pointer is stored.

Invariant extensions landed 2026-08-21 (with regime D1): the
`PlaceRegMapBound` conjunct (mapped registers < nextReg — the register
half of the once-planned strengthened `CompilerStateWF`; fresh temps
cannot clobber bound locals' registers) and the strengthened `MemValSim`
pointer case (stored tags are non-wildcard; the referent range is in
ρa's domain). These also discharge part of regime C's blocker list.

WIRED (2026-08-22): `CompilerInv` grew from seven conjuncts to nine —
the two facts the minting members need.

- `TagRenameBounded ρt s_mir.perms.NextTag s_osea.perms.NextTag`
  (eighth): the hypothesis every consumer of `sb_ref`/`sb_own` needs.
  Free at the closed sites — the three access ops leave `NextTag` alone
  (`sb_write_NextTag`/`sb_read_NextTag`/`sb_die_NextTag`), so regime A
  and the deref spine rewrite the bound through unchanged.
  `ptrChain_lowering_sim` (né loadSpine) gained two counter-framing conjuncts for the
  same reason (the spine only reads).
- `AllocLockstep s_mir.mem s_osea.mem` (ninth): the two bump allocators
  sit at the same watermark, so corresponding fresh allocations return
  the SAME base address — which is what lets ρa extend by `.refl` at a
  fresh local without breaking `IdentityOnDomain`. Free at the closed
  sites too: stores do not move a watermark
  (`AllocLockstep.writeWordSeq`), and the spine needed NO change at all,
  since it never touches memory on either machine.
  `AllocLockstep.allocate_eq` is the consumer-facing form: corresponding
  allocations agree, and the property survives them.

Remaining (2): every remaining sorry is blocked on a NAMED obligation.
1. ✔ `const_write_deref_deep_residual` — RETIRED 2026-09-01, the first
   residual to die. The pending-cleanup generalization landed as
   `ptrChain_lowering_sim`; `flattenPlace` + its congruence family
   (spine.lean) then normalized EVERY deref dst into the chain grammar
   (`PtrChain_flatten_deref`), so regime D's dispatcher routes every
   shape through `const_write_deref_chain_simulation` and never falls
   back. The residual and its nonspine dispatcher were deleted; the
   axiom whitelist dropped to THREE sorries.
2. ✔ `const_write_proj_nonlocal_residual` — RETIRED 2026-09-03, the
   second residual to die. The two C-deref leaves COLLAPSED onto the
   mother lemma at `Mut (.deref P)` (gate `PtrChain (.deref P)` — any
   depth, proj-interiors included); the proj-dst dispatcher's deref arm
   went TOTAL via the flatten transfer
   (`compileStmt_const_projderef_flatten_run/_value` +
   `PtrChain_flatten_deref`); and the last class — UNBOUND roots —
   closed as `const_write_proj_fresh_simulation` (regime B-proj:
   `allocateRoot`/`ensurePlaceRoot` allocate the σ-sized root in
   lockstep, ρa extends by the IDENTITY over the whole fresh block via
   `AddrRenameMap.extendIdRange`, then the C0/C1 endgames land inside
   it). The axiom whitelist dropped to TWO sorries.
3. `copy_place_residual` — NARROWED 2026-08-29 (later): regimes L→L,
   P0→L, P→L (nonzero offset) and D→L (deref src through a load spine)
   are CLOSED (`copy_local_local_simulation`, `copy_proj_zero_simulation`,
   `copy_proj_offset_simulation`, `copy_deref_local_simulation`). D→L is
   `[spine; Load; Memcpy]` — no Borrow, no Die, no keystone — with the
   `Memcpy`'s source bound supplied by the copy-range dereferenceability
   check (the read-side event fix, t17-pinned) through `MemValSim`'s
   `o' = o ∧ s' = s`, and its nonoverlapping check by the overlap guard
   via `resolvePlace?_of_resolveAcc`. Remaining: proj-of-proj and mixed
   chains (reassociation transfer), unbound dst (regime-B), non-local
   dst (contiguous BRIDGE 1 shape — composition, no blocker).
4. `ref_place_residual` — NARROWED 2026-08-30: P→L, D→L, both field-dst
   regimes (L→P0/L→P — the TWO-MINT leaf, BRIDGE 1 under the extended
   rename), and the DST-FLATTENING RECURSION are CLOSED: nested
   projection destinations of any depth reassociate on both machines
   (`stepStmt_assign_proj_assoc` source-side, the transfer lemmas —
   now in common.lean — compiled-side) and `ref_proj_dst_simulation`
   recurses into the leaves, stmt0-threaded. The residual's h_stmt is
   stmt0-loosened. Remaining: deref dst bases (spine composition),
   non-local srcs under non-local dsts, non-spine deref srcs,
   proj-of-proj srcs, unbound roots.

- ✔ REGIME P→L of ref — `ref_proj_local_simulation` (2026-08-27):
  `dst := &kind s.f`, any kind/offset/mask, dst and src-root both bound
  locals. Two instructions, as L→L, with the field's offset in the
  `Borrow`. The bounds check comes from TYPING alone
  (`PathTo.offset_add_size_le`: a field's range fits its layout) — the
  source's `sb_ref` checks nothing, so nothing semantic could supply it.
  The stored pointer covers the WHOLE base allocation (mirlite stores
  `allocBase/allocSize`), which is what `LocalBindingSim`'s block-domain
  conjunct was made for.
- ✔ REGIME C-deref of const_write — `const_write_proj_deref_simulation`
  (2026-08-27): `(*p).f := v` over ANY load spine, nonzero offset. Spine
  mother lemma for the prelude; then the C1 endgame with the parent tag
  coming from the LOADED pointer via `MemValSim` instead of a local
  binding. Fragment `[spine; Load; Borrow(Mut); CStore; Die]`.
- ✔ REGIME D-proj of const_write — `const_write_deref_proj_simulation`
  (2026-08-27): `*(s.f) := v`, the pointer FIELD of a bound tuple local.
  Fragment `[Borrow(Shared); Load; Die; CStore]` — the first consumer of
  BRIDGE 1S (`sb_ref_read_die_cancels`, keystone.lean): the Shared
  triple's net stack effect is exactly the parent read mirlite's
  `resolvePlaceAcc` performs at the deref. Its success supplier is
  `sb_ref_Shared_ok_of_sb_read_ok` (a shared retag with an empty mask
  succeeds wherever the read does). The (since-retired) nonspine dispatcher
  is now a PROVED dispatcher over this and the deep residual.

- ✔ REGIME C of const_write — `const_write_proj_simulation`
  (2026-08-27), split by the projection's OFFSET, which is what decides
  the lowering's shape. C0 (offset zero) is `const_write_proj_zero_run`'s
  bare `CStore`: regime A with a wider `allocSize`, since a projected
  place's bounds come from the BASE's layout. C1 (nonzero) is
  `Borrow(Mut); CStore; Die` — the FIRST closed regime that mints a tag,
  uses it and kills it, and therefore the first consumer of BRIDGE 1
  (`sb_ref_use_die_cancels`), which says that triple equals the bare
  parent write on the stacks. Both of BRIDGE 1's side conditions are
  DERIVED, not assumed: `sb_ref_Mut_ok_of_sb_write_ok` (a mutable retag
  succeeds wherever the write does — per cell `writeCell` then
  `pushCell`) supplies the retag's success, which the source cannot
  provide since it performs a bare write; and `freshTag_not_protected`
  supplies `h_unprot` from `TagRenameBounded` + `PermSim`. New
  execution lemma: `runN_Die_step`.
- ✔ REGIME F→L of `ref` — `ref_fresh_dst_simulation` (proof/ref.lean,
  2026-08-23): `&src` into an UNBOUND local. Fragment `Alloc; Borrow;
  RStore`; the only statement so far in which ρt extends TWICE (`sb_own`
  for the destination's root tag, then `sb_ref` for the reference), which
  works because each minting member returns the `TagRenameBounded` at the
  intermediate counters that the next one takes as hypothesis — the
  payoff for making that an invariant rather than a per-leaf side
  condition. ρa extends once, at the identity pair. New pieces:
  `compileStmt_ref_fresh_local_run`/`_value`, `prepare_lookup_ne`
  (preparing one local leaves other bindings alone — needed because
  `doAssign` resolves the SOURCE against the post-allocation state),
  `layout_ne_ptrL`/`ref_dst_src_idx_ne` (a `PtrL τ` destination and a `τ`
  source are necessarily distinct locals, since `Local` carries its type
  proof), `getPlaceInfo_setNextReg`.
- ✔ REGIME L→L of `ref` — `ref_local_local_simulation` (proof/ref.lean,
  2026-08-22): `dstLocal := &srcLocal`, both bound, ANY referent size
  (the `0 < blockSize τ` side condition and its `ref_zst_residual` went
  away the same day when the target's `Rhs.Borrow` bounds check became
  the range form `addr + len > base + size` — `local/zst_ref`).
  The fragment is `Borrow; RStore` with NO `Die` (a stored reference's
  cleanup is never emitted), so the ref leaf does not need BRIDGE 1.
  First leaf to grow ρt at a USER-visible tag: the two machines' fresh
  reference tags are paired by `sb_ref_respects_PermSim`, and the stored
  pointer's `MemValSim` holds under the extension with its referent
  range from `LocalBindingSim`'s block-domain conjunct. Executes via
  `runN_Assgn_Borrow_step` + `runN_RStore_step`; the latter was
  UNPROVABLE until `BEq TyVal` was hand-written (obseq/types.lean,
  2026-08-22 — the derived instance for the nested inductive was an
  opaque `partial def`, invisible to the logic).

- ✔ REGIME B (fresh local) `const_write_fresh_local_simulation`
  (2026-08-22): the only regime that grows BOTH renames. The fragment is
  two instructions — the root `Alloc` that `ensureLocalRegE` emits when
  the local is unmapped, then the `CStore`. ρa extends by the IDENTITY
  pair (`AllocLockstep` makes both allocators hand out the same address;
  `AddrRenameIncr.extend_id` needs no freshness side condition, because
  `IdentityOnDomain` already forces any prior mapping of that address to
  be the identity one) and ρt extends at the fresh pair via
  `sb_own_respects_PermSim`. Knowing the fragment BEGINS with the `Alloc`
  is exactly what the `UnboundLocalsUnmapped` conjunct supplies. New
  pieces: `runN_Assgn_Alloc_step`, `ensureLocalRegE_fresh`,
  `compileStmt_local_fresh_run`, `getPlaceInfo_setPlaceInfo_self`/`_ne`,
  `getPlaceInfo_emit`, `AddrRenameMap.extend` + its two lemmas,
  `SourceMemSim.rename_mono`.

CLOSED in the leaf layer (2026-08-18):
- ✔ `const_write_stmt_evidence` — total (fresh-root branch via
  `ensurePlaceRoot_maps_root`).
- ✔ `const_write_resolved_simulation` — proved delegation over regimes;
  REGIME A (bound local) closed end-to-end by
  `const_write_local_existing_simulation`: fragment located via
  `compileStmt_emitted_in_compProg` + `compileStmt_local_existing_run`,
  executed via BRIDGE 2, permissions transported via BRIDGE 3, invariant
  rebuilt (this is obseq2's long-parked "Step 4 regime-A milestone").
- ✔ REGIME D (load spines) `const_write_deref_spine_simulation`
  (2026-08-21, subsuming the same-day depth-1 proof): `*p := v`,
  `**q := v` and every deeper all-deref shape, via the spine mother
  lemma `ptrChain_lowering_sim` (proof/spine.lean) — an induction over
  `LoadSpine` places showing the compiled `Load` chain executes and
  ends with a register holding the ρ-renamed resolved pointer, with the
  threaded perms `PermSim`-related and everything else framed. Each
  level's `Load` bounds check is matched by mirlite's dereferenceable
  check (added 2026-08-21 to `resolvePlaceAcc` — the read-side mirror
  of `writeResolvedPlace`'s bounds check; validated: suite 77/117,
  differential 77/0/0, t15/d25 pin the OOB-deref alignment). Reusable
  pieces: `ptrChain_lowering_sim`, `placeInputsMapped_of_resolveAcc`,
  `LocalBindingSim.placeRegMap_congr`, `runN_Assgn_Load_ptr_step`,
  `resolvePlaceAcc_deref_local_inversion`,
  `LocalBindingSim.insert_fresh_reg`, `RegMap.lookup_insert_self`/`_ne`
  (+ `LawfulBEq Register`), `placeToRegChecked_local_existing`,
  `emit_nil`; the fresh-root case is vacuous (`preparePlaceAssign`
  cannot allocate under a deref).
-/

namespace obseq3.proof

open obseq3
open obseq3.compile
open obseq3.oseair (Instr Register Rhs Val)

/-- One source step is simulated by finitely many target steps and
    `CompilerInv` is re-established, for programs in the proof-core
    fragment. -/
theorem CompilerInv_step
    {Γ : Ctx}
    {cs0 : CompilerState}
    {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    (compProg : oseair.Prog)
    (h_core : CoreProg prog)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    (h_step : srcStep s_mir prog = .ok s_mir') :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' := by
  simp only [srcStep] at h_step
  split at h_step
  · -- halt: fixed point on both sides; zero target steps.
    simp at h_step; subst h_step
    exact ⟨ρa, ρt, s_osea, 0,
      AddrRenameIncr.refl ρa, TagRenameIncr.refl ρt,
      by simp [oseair.runN], h_inv⟩
  · -- off the end: source is stuck-ok; zero target steps.
    simp at h_step; subst h_step
    exact ⟨ρa, ρt, s_osea, 0,
      AddrRenameIncr.refl ρa, TagRenameIncr.refl ρt,
      by simp [oseair.runN], h_inv⟩
  · rename_i stmt h_ne h_get
    have h_stmt_core : CoreStmt stmt := h_core _ _ h_get
    cases stmt with
    | halt =>
        simp only [mirlite.stepStmt] at h_step
        cases h_step
        exact ⟨ρa, ρt, s_osea, 0,
          AddrRenameIncr.refl ρa, TagRenameIncr.refl ρt,
          by simp [oseair.runN], h_inv⟩
    | assign dst rhs =>
        cases rhs with
        | constInit v =>
            exact CompilerInv_step_constWrite compProg v h_comp h_inv h_get h_step
        | copy src =>
            exact CompilerInv_step_copy compProg h_comp h_inv h_get h_step
        | ref kind prot mask src =>
            exact CompilerInv_step_ref kind prot mask compProg h_comp h_inv h_get h_step
        | ptrCast src => exact absurd h_stmt_core (by simp [CoreStmt, CoreRhs])
        | ptrOffset src d => exact absurd h_stmt_core (by simp [CoreStmt, CoreRhs])
        | refSlice k p src => exact absurd h_stmt_core (by simp [CoreStmt, CoreRhs])
        | exposeAddr src => exact absurd h_stmt_core (by simp [CoreStmt, CoreRhs])
        | fromExposed src => exact absurd h_stmt_core (by simp [CoreStmt, CoreRhs])
        | uninit => exact absurd h_stmt_core (by simp [CoreStmt, CoreRhs])
    | assignIf discr val dst rhs => exact absurd h_stmt_core (by simp [CoreStmt])
    | alloc dst len => exact absurd h_stmt_core (by simp [CoreStmt])
    | dealloc p => exact absurd h_stmt_core (by simp [CoreStmt])
    | pushProtectors => exact absurd h_stmt_core (by simp [CoreStmt])
    | popProtectors => exact absurd h_stmt_core (by simp [CoreStmt])

/-- Main compiler-correctness theorem (forward simulation of successful
    source runs): every n-step source execution of a proof-core program is
    matched by a finite target execution, and `CompilerInv` relates the
    final states. The observable consequence lives in the invariant:
    `SourceMemSim` at renamed addresses and `PermSim` at renamed tags. -/
theorem compile_correct
    {Γ : Ctx}
    {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    (compProg : oseair.Prog)
    (n : Nat)
    (h_core : CoreProg prog)
    (h_comp : compileProg prog = Except.ok compProg)
    (h_run : mirlite.runN MSB n s_mir prog = mirlite.Result.ok s_mir')
    (h_inv : CompilerInv (initialState Γ) prog ρa ρt s_mir s_osea) :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (m : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB m s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv (initialState Γ) prog ρa' ρt' s_mir' s_osea' := by
  induction n generalizing ρa ρt s_mir s_osea with
  | zero =>
      simp [mirlite.runN] at h_run
      exact ⟨ρa, ρt, s_osea, 0,
        AddrRenameIncr.refl ρa, TagRenameIncr.refl ρt,
        by simp [oseair.runN], h_run ▸ h_inv⟩
  | succ n ih =>
      simp only [mirlite.runN] at h_run
      split at h_run
      · -- halt: runN short-circuits.
        simp at h_run; subst h_run
        exact ⟨ρa, ρt, s_osea, 0,
          AddrRenameIncr.refl ρa, TagRenameIncr.refl ρt,
          by simp [oseair.runN], h_inv⟩
      · -- none: runN short-circuits.
        simp at h_run; subst h_run
        exact ⟨ρa, ρt, s_osea, 0,
          AddrRenameIncr.refl ρa, TagRenameIncr.refl ρt,
          by simp [oseair.runN], h_inv⟩
      · -- real step: CompilerInv_step then the induction hypothesis.
        rename_i stmt h_ne h_get
        split at h_run
        · rename_i s_mid h_step_eq
          have h_step : srcStep s_mir prog = .ok s_mid := by
            unfold srcStep
            rw [h_get]
            cases stmt with
            | halt => exact (h_ne rfl).elim
            | assign dst rhs => exact h_step_eq
            | assignIf a b c d => exact h_step_eq
            | alloc a b => exact h_step_eq
            | dealloc a => exact h_step_eq
            | pushProtectors => exact h_step_eq
            | popProtectors => exact h_step_eq
          obtain ⟨ρa_mid, ρt_mid, s_osea_mid, k,
            hρa_step, hρt_step, h_target_k, h_inv_mid⟩ :=
            CompilerInv_step compProg h_core (by simpa [compileProg] using h_comp) h_inv h_step
          obtain ⟨ρa', ρt', s_osea', m,
            hρa_tail, hρt_tail, h_target_m, h_inv'⟩ :=
            ih h_run h_inv_mid
          exact ⟨ρa', ρt', s_osea', k + m,
            AddrRenameIncr.trans hρa_step hρa_tail,
            TagRenameIncr.trans hρt_step hρt_tail,
            (oseair_runN_add k m s_osea compProg s_osea_mid h_target_k).trans
              h_target_m,
            h_inv'⟩
        · simp at h_run

end obseq3.proof
