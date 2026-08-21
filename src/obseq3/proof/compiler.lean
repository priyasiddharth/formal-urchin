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

Invariant extensions landed 2026-08-21 (with regime D1): the
`PlaceRegMapBound` conjunct (mapped registers < nextReg — the register
half of the once-planned strengthened `CompilerStateWF`; fresh temps
cannot clobber bound locals' registers) and the strengthened `MemValSim`
pointer case (stored tags are non-wildcard; the referent range is in
ρa's domain). These also discharge part of regime C's blocker list.

- ✔ BRIDGE 3, `sb_ref` member `sb_ref_respects_PermSim`
  (proof/permsim_transport.lean, 2026-08-21): the ρt-GROWING transport —
  fresh tags are the two (differing) counters, results related under
  `TagRenameMap.extend ρt src.NextTag tgt.NextTag`; injectivity of the
  extension from the new `TagRenameBound` hypothesis (mapped pairs
  strictly below both counters), which the lemma re-establishes at the
  bumped counters. Engine: `refCellOp`/`refCellContent` content forms
  over `foldCellsIdx` (per-`RefKind` cell ops incl. freeze-mask
  `insertAboveCell` placements), `foldCellsIdx_ok_of_cells`
  (keystone.lean), `insertAboveContent_transport`, and
  `PermSim.rename_mono` for the untouched parts. Handles both protector
  registration (`prot = true`) and the plain case. All four transport
  members (write/read/die/ref) are now theorems.

Invariant extension landed 2026-08-21 (with the `sb_ref` transport): the
`TagRenameBound ρt s_mir.perms.NextTag s_osea.perms.NextTag` conjunct —
every mapped tag pair sits strictly below both machines' counters, which
is what makes the fresh-pair ρt extension injective. It holds at init
(only the wildcard, tag 0, is mapped and counters start at 1) and is
preserved by every event: `sb_write`/`sb_read`/`sb_die` keep both
counters (`sb_*_NextTag` in common.lean, as does `resolvePlaceAcc`),
and `sb_ref_respects_PermSim` returns it re-established at the bumped
counters.

Target-machine provability fix (2026-08-21): `deriving BEq` on the
NESTED inductives `TyVal`/`LayoutTy` compiled to `partial` — hence
OPAQUE — functions, so `ty != ty` was not reducible and NO proof about
`Instr.RStore` (which guards on `srcTy != ty`) could get past the type
check. Both `BEq`s are now hand-written structurally in obseq/types.lean
with `beq_self`/`bne_self` simp lemmas. Behavior-neutral: suite 77/117
pass, differential 77/0/0, unit tests green.

Remaining (5 declarations): every remaining sorry is blocked on a NAMED
obligation:
1. `const_write_fresh_local_simulation` — needs the lockstep-allocation
   conjunct (`s_osea.mem.addrStart = s_mir.mem.addrStart`) so ρa extends
   at the equal fresh address, plus the `sb_own` transport member.
2. `const_write_proj_simulation` — REGIME C's CORE CLOSED 2026-08-21:
   `const_write_proj_local_simulation` proves `loc.field := v` at a
   nonzero offset over a bound root local. This is THE BORROW
   COMPOSITION: the source's single parent write is matched by the
   target's `Borrow(Mut) ; CStore ; Die`, cancelled by BRIDGE 1, with
   the internal borrow's SUCCESS supplied by `sb_ref_Mut_ok_of_sb_write`
   (no source event to transport) and BRIDGE 1's side conditions derived
   from `PermSim` + `TagRenameBound` (`isProtectedIn_NextTag_false`,
   `NextTag_ne_wildcard`). ρt does not grow — internal fresh tags are
   never mapped. Four named residuals remain in the delegation:
   PROJ-FRESH-ROOT (regime-B blocker), PROJ-ZERO-OFFSET (no `Borrow` is
   emitted at all — regime A's shape at a projected place, needs only
   its fragment lemma), PROJ-NESTED and PROJ-OVER-DEREF (both need this
   proof generalized over an OPAQUE base run, the way
   `loadSpine_lowering_sim` is stated).
3. `const_write_deref_nonspine_simulation` — a projection somewhere in
   the dereferenced pointer place. The borrow composition it needs now
   EXISTS (item 2); what remains is the generalization over an opaque
   base run, shared with PROJ-NESTED/PROJ-OVER-DEREF and with the ref
   leaf's REF-NONLOCAL regimes — one piece of work unblocking all five.
4. `CompilerInv_step_copy` — the `sb_read` transport member EXISTS
   (`sb_read_respects_PermSim`, 2026-08-19); still needs a bidirectional
   memory relation (source-absent cells read as undef; one-directional
   `SourceMemSim` does not constrain the target there) plus the Memcpy
   execution lemma.
5. `CompilerInv_step_ref` — CORE REGIME CLOSED 2026-08-21:
   `ref_local_local_existing_simulation` (proof/ref.lean) proves
   `dl = &sl` for bound one-cell locals end-to-end, and it is the FIRST
   ρt-GROWING statement simulation: `sb_ref_respects_PermSim` extends ρt
   at the fresh tag pair, `sb_write_respects_PermSim` fires at the
   extended map, BRIDGE 2 stores the pointer, and the invariant is
   rebuilt with `SourceMemSim`/`LocalBindingSim`/`MemValSim` transported
   along `TagRenameIncr`. Four named residual regimes remain as inline
   sorries in the delegation: REF-FRESH-DST (unbound destination —
   the regime-B `sb_own`/lockstep-allocation blocker), REF-NONLOCAL-DST
   (projected/deref'd destination — regime-C borrow composition),
   REF-NONLOCAL-SRC (projected/deref'd source place), REF-WIDE-SRC
   (multi-cell referent — needs an allocation-domain invariant for
   `MemValSim`'s range conjunct).

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
