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
  `loadSpine_lowering_sim` gained two counter-framing conjuncts for the
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

Remaining (5): every remaining sorry is blocked on a NAMED obligation:
1. `const_write_fresh_local_simulation` — FULLY UNBLOCKED as of
   2026-08-22: the `sb_own` member mints the root tag and extends ρt,
   and `AllocLockstep` (now a `CompilerInv` conjunct) makes the two
   machines' fresh allocations land at the same address so ρa extends by
   `.refl`. What remains is the leaf's own work: mirlite's
   `allocateBase` inversion, the target `Alloc` fragment's execution, and
   `SourceMemSim`/`LocalBindingSim` extension at the new cell.
2. `const_write_proj_simulation` — every SB-side obligation is now
   available (`sb_ref` member + `TagRenameBounded` in the invariant +
   `PlaceRegMapBound`); what remains is proof work, not machinery:
   compose the member with BRIDGE 1 and BRIDGE 3 over the internal
   `Borrow`, and execute the proj fragment.
3. `const_write_deref_nonspine_simulation` — a projection somewhere in
   the dereferenced pointer place: its lowering emits a `Borrow` with
   cleanup — same position as regime C above, and unblocked by the same
   landed member (the former D2/D3 split is gone: all-deref spines of
   EVERY depth closed 2026-08-21 via `loadSpine_lowering_sim`).
4. `CompilerInv_step_copy` — the `sb_read` transport member EXISTS
   (`sb_read_respects_PermSim`, 2026-08-19); still needs a bidirectional
   memory relation (source-absent cells read as undef; one-directional
   `SourceMemSim` does not constrain the target there) plus the Memcpy
   execution lemma.
5. `CompilerInv_step_ref` — fully unblocked as of 2026-08-22: the
   `sb_ref` member extends ρt and hands back the extended
   `TagRenameBounded`, which the invariant now carries. What remains is
   the leaf's own work — the `Borrow` fragment's execution, the
   `MemValSim` for the stored `ptrVal` under the extended ρt, and
   BRIDGE 2 for the `RStore`. Its `Die` cleanup transport exists
   (`sb_die_respects_PermSim`).

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
  lemma `loadSpine_lowering_sim` (proof/spine.lean) — an induction over
  `LoadSpine` places showing the compiled `Load` chain executes and
  ends with a register holding the ρ-renamed resolved pointer, with the
  threaded perms `PermSim`-related and everything else framed. Each
  level's `Load` bounds check is matched by mirlite's dereferenceable
  check (added 2026-08-21 to `resolvePlaceAcc` — the read-side mirror
  of `writeResolvedPlace`'s bounds check; validated: suite 77/117,
  differential 77/0/0, t15/d25 pin the OOB-deref alignment). Reusable
  pieces: `loadSpine_lowering_sim`, `placeInputsMapped_of_resolveAcc`,
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
