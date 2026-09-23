import obseq3.proof.alloc

/-!
# `dealloc`: copy's read of the pointer, then the block is freed

`dealloc dst` reads the pointer stored at `dst` exactly as `copy` reads
a place (bounds, the SB read, initialisation — `evalCopy` since
2026-09-22), then frees the block it names: the permission model's
`dealloc` through the pointer's tag at every cell (the tag must exist
and grant writes, no item may be protected, the stack is removed) and
the cells leave memory. The compiler emits copy's read with its register
exposed (`readToReg`) and one `Dealloc` on that register, which does the
same two things.

So the proof is the read package with the register exposed
(`copy_readRegPkg_flat`, as `alloc`'s runtime length and `assignIf`'s
guard use it), one target step, and two transports: `sb_dealloc` along
`PermSim` — per cell, `splitStack`/`grantsWrite`/`firstProtectedIn` all
transport, and removing a cell on both sides keeps `StackMapSim` — and
`removeRange` along `SourceMemSim` (the renaming is the identity on its
domain, so a surviving source cell's image survives too). Memory SHRINKS
but the allocation table and the watermark do not move, so
`AllocLockstep` is untouched; env, registers and both renamings are
untouched too.
-/

namespace obseq3.proof

open obseq3
open obseq3.compile
open obseq3.oseair (Instr Register Rhs Val)

variable {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
variable {ρa : AddrRenameMap} {ρt : TagRenameMap}
variable {s_mir s_mir' : mirlite.State MSB Γ}
variable {s_osea : oseair.State MSB}

/-! ## The target step -/

theorem runN_Dealloc_step
    (compProg : oseair.Prog) (s : oseair.State MSB) (r : Register)
    {b sz : Word} {t : Tag} {p2 : AccessPerms}
    (h_instr : compProg s.pc = some (Instr.Dealloc r))
    (h_entry : PtrRegisterEntry s.reg r b 0 sz t)
    (h_dealloc : MSB.dealloc s.perms b sz t = .ok p2) :
    oseair.runN MSB 1 s compProg = oseair.Result.Ok
      { s with perms := p2, mem := s.mem.removeRange b sz, pc := s.pc + 1 } := by
  obtain ⟨e, h_lookup⟩ := h_entry
  have h_step : oseair.step MSB s compProg = oseair.Result.Ok
      { s with perms := p2, mem := s.mem.removeRange b sz, pc := s.pc + 1 } := by
    simp only [oseair.step, oseair.stepWith, h_instr, h_lookup, bne_self_eq_false,
      Bool.false_eq_true, if_false, h_dealloc]
  simp [oseair.runN_succ, oseair.runN_zero, h_step]

/-! ## `sb_dealloc` along `PermSim` -/

/-- The per-cell op of `sb_dealloc`, named so the fold's steps can be
    rewritten by name. -/
def deallocCellOp (tag : Tag) (ap : AccessPerms) (a : Word) : Except String AccessPerms :=
  match ap.StackMap.find? a with
  | none => .error s!"sb-dealloc: no borrow stack at address {a}"
  | some stack =>
    match splitStack stack tag with
    | none => .error s!"deallocation through tag {tag}: that tag does not exist in the borrow stack at {a}"
    | some (_, item, _) =>
      if !item.grantsWrite then
        .error s!"sb-dealloc: tag {tag} (a read-only item) does not grant deallocation at {a}"
      else
        match firstProtected ap stack with
        | some p =>
            .error s!"deallocating while item for tag {p.tag} is strongly protected"
        | none =>
            .ok { ap with StackMap := ap.StackMap.filter (fun (x, _) => x != a) }

theorem sb_dealloc_eq (ap : AccessPerms) (addr : Word) (len : Nat) (tag : Tag) :
    sb_dealloc ap addr len tag = foldCells (deallocCellOp tag) ap addr len := rfl

/-- One cell of `sb_dealloc`, inverted: the stack is there, the tag
    splits it at a write-granting item, nothing is protected, and the
    cell is removed. -/
theorem deallocCellOp_ok_inv {ap ap' : AccessPerms} {a : Word} {tag : Tag}
    (h : deallocCellOp tag ap a = .ok ap') :
    ∃ stack ab item bl,
      ap.StackMap.find? a = some stack ∧
      splitStack stack tag = some (ab, item, bl) ∧
      item.grantsWrite = true ∧
      firstProtectedIn ap.protFrames stack = none ∧
      ap' = { ap with StackMap := ap.StackMap.filter (fun (x, _) => x != a) } := by
  simp only [deallocCellOp] at h
  split at h
  · simp at h
  rename_i stack h_find
  split at h
  · simp at h
  rename_i ab item bl h_split
  by_cases h_gw : item.grantsWrite = true
  · rw [if_neg (by simp [h_gw])] at h
    split at h
    · simp at h
    rename_i h_fp
    cases h
    exact ⟨stack, ab, item, bl, h_find, h_split, h_gw, h_fp, rfl⟩
  · rw [if_pos (by simpa using h_gw)] at h
    simp at h

/-- The converse. -/
theorem deallocCellOp_ok_eq (ap : AccessPerms) (a : Word) (tag : Tag)
    {stack ab bl : BorrowStack} {item : Item}
    (h_find : ap.StackMap.find? a = some stack)
    (h_split : splitStack stack tag = some (ab, item, bl))
    (h_gw : item.grantsWrite = true)
    (h_fp : firstProtectedIn ap.protFrames stack = none) :
    deallocCellOp tag ap a
      = .ok { ap with StackMap := ap.StackMap.filter (fun (x, _) => x != a) } := by
  simp only [deallocCellOp, h_find, h_split, firstProtected, h_fp]
  rw [if_neg (by simp [h_gw])]

/-- The cell removed is gone. -/
theorem SB.find?_filter_self (a : Word) :
    ∀ (sb : SB), SB.find? (sb.filter (fun (e : Word × BorrowStack) => e.1 != a)) a = none
  | [] => rfl
  | (k, s) :: rest => by
      by_cases hk : k = a
      · rw [List.filter_cons_of_neg (by simp [hk])]
        exact SB.find?_filter_self a rest
      · rw [List.filter_cons_of_pos (by simp [hk])]
        simp only [SB.find?, show (k == a) = false by simp [hk]]
        exact SB.find?_filter_self a rest

/-- Removing the same cell on both sides keeps the maps related. -/
theorem StackMapSim.filter_cell {x y : SB} (h : StackMapSim ρt x y) (a : Word) :
    StackMapSim ρt (x.filter (fun (e : Word × BorrowStack) => e.1 != a))
      (y.filter (fun (e : Word × BorrowStack) => e.1 != a)) := by
  intro b
  by_cases hb : b = a
  · subst hb
    rw [SB.find?_filter_self, SB.find?_filter_self]
    trivial
  · rw [SB.find?_filter_ne hb, SB.find?_filter_ne hb]
    exact h b

/-- `sb_dealloc` transports along `PermSim`: the source freeing a block
    through a tag means the target frees it through the tag's image, and
    the results are related. Neither counter moves. -/
theorem sb_dealloc_respects_PermSim
    {ρt : TagRenameMap} {tagS tagT : Tag}
    (h_wf : TagRenameWF ρt) (h_tag : ρt tagS = some tagT) :
    ∀ (len : Nat) (addr : Word) {src tgt src' : AccessPerms},
      PermSim ρt src tgt →
      sb_dealloc src addr len tagS = .ok src' →
      ∃ tgt', sb_dealloc tgt addr len tagT = .ok tgt' ∧ PermSim ρt src' tgt' ∧
        src'.NextTag = src.NextTag ∧ tgt'.NextTag = tgt.NextTag := by
  intro len
  induction len with
  | zero =>
      intro addr src tgt src' h_sim h_src
      rw [sb_dealloc_eq] at h_src
      simp only [foldCells] at h_src
      cases h_src
      exact ⟨tgt, rfl, h_sim, rfl, rfl⟩
  | succ n ih =>
      intro addr src tgt src' h_sim h_src
      obtain ⟨h_stacks, h_prot, h_exp, h_next⟩ := h_sim
      rw [sb_dealloc_eq] at h_src ⊢
      simp only [foldCells] at h_src
      split at h_src
      · simp at h_src
      rename_i src1 h_cell
      obtain ⟨stack, ab, item, bl, h_find, h_split, h_gw, h_fp, rfl⟩ :=
        deallocCellOp_ok_inv h_cell
      obtain ⟨stack', h_find', h_ss⟩ := SB.find?_transport h_stacks h_find
      obtain ⟨ab', item', bl', h_split', -, h_item, -⟩ :=
        splitStack_some_transport h_wf h_tag h_ss h_split
      have h_gw' : item'.grantsWrite = true := by
        rw [ItemSim.grantsWrite_eq h_item]; exact h_gw
      have h_fp' : firstProtectedIn tgt.protFrames stack' = none :=
        firstProtectedIn_none_transport h_wf h_prot h_ss h_fp
      have h_sim1 : PermSim ρt
          { src with StackMap := src.StackMap.filter (fun (x, _) => x != addr) }
          { tgt with StackMap := tgt.StackMap.filter (fun (x, _) => x != addr) } :=
        ⟨StackMapSim.filter_cell h_stacks addr, h_prot, h_exp, h_next⟩
      obtain ⟨tgt', h_tgt, h_sim', h_ns, h_nt⟩ := ih (addr + 1) h_sim1 h_src
      refine ⟨tgt', ?_, h_sim', h_ns, h_nt⟩
      simp only [foldCells]
      rw [deallocCellOp_ok_eq tgt addr tagT h_find' h_split' h_gw' h_fp']
      rw [sb_dealloc_eq] at h_tgt
      exact h_tgt

/-! ## `removeRange` along `SourceMemSim` -/

/-- `List.lookup` through a key filter. -/
theorem List.lookup_filter_key {β : Type} (p : Word → Bool) (a : Word) :
    ∀ (l : List (Word × β)),
      List.lookup a (l.filter (fun e => p e.1)) = if p a then List.lookup a l else none
  | [] => by simp
  | (k, v) :: rest => by
      by_cases hk : p k = true
      · rw [List.filter_cons_of_pos (by simpa using hk)]
        by_cases hka : a = k
        · subst hka
          simp [List.lookup, hk]
        · have h1 : (a == k) = false := by simp [hka]
          simp only [List.lookup, h1]
          exact List.lookup_filter_key p a rest
      · rw [List.filter_cons_of_neg (by simpa using hk)]
        by_cases hka : a = k
        · subst hka
          simp only [List.lookup, beq_self_eq_true]
          rw [List.lookup_filter_key p a rest]
          simp [hk]
        · have h1 : (a == k) = false := by simp [hka]
          simp only [List.lookup, h1]
          exact List.lookup_filter_key p a rest

theorem mirlite_find?_removeRange (m : mirlite.Mem) (base : Word) (sz : Nat) (a : Word) :
    mirlite.Mem.find? (m.removeRange base sz) a
      = if (decide (a < base) || decide (base + sz ≤ a)) then mirlite.Mem.find? m a
        else none := by
  simp only [mirlite.Mem.find?, mirlite.Mem.removeRange]
  exact List.lookup_filter_key (fun x => decide (x < base) || decide (base + sz ≤ x)) a m.mMap

theorem oseair_find?_removeRange (m : oseair.Mem) (base : Word) (sz : Nat) (a : Word) :
    oseair.Mem.find? (m.removeRange base sz) a
      = if (decide (a < base) || decide (base + sz ≤ a)) then oseair.Mem.find? m a
        else none := by
  simp only [oseair.Mem.find?, oseair.Mem.removeRange]
  exact List.lookup_filter_key (fun x => decide (x < base) || decide (base + sz ≤ x)) a m.mMap

/-- Removing the same range on both sides keeps the memories related:
    the renaming is the identity on its domain, so a surviving source
    cell's image is at the same address, outside the range too. -/
theorem SourceMemSim.removeRange
    (h_id : IdentityOnDomain ρa) {m : mirlite.Mem} {m' : oseair.Mem}
    (h : SourceMemSim ρa ρt m m') (base : Word) (sz : Nat) :
    SourceMemSim ρa ρt (m.removeRange base sz) (m'.removeRange base sz) := by
  intro a v h_find
  rw [mirlite_find?_removeRange] at h_find
  split at h_find
  · rename_i h_out
    obtain ⟨a', v', h_ra, h_find', h_mvs⟩ := h a v h_find
    have h_aa : a' = a := (h_id _ _ h_ra).symm
    subst h_aa
    refine ⟨a', v', h_ra, ?_, h_mvs⟩
    rw [oseair_find?_removeRange, if_pos h_out]
    exact h_find'
  · simp at h_find

/-- A single pointer cell related to `[.ptrVal b o e s t]` is a target
    pointer at the renamed base and tag, same offset and size. -/
theorem ListRel_ptr_inv {b o e s : Word} {t : Tag} {vals : List Val}
    (h : ListRel (MemValSim ρa ρt) [mirlite.MemValue.ptrVal b o e s t] vals) :
    ∃ b' t', vals = [Val.Ptr b' o e s t'] ∧ ρa b = some b' ∧ ρt t = some t' := by
  cases vals with
  | nil => exact absurd h (by simp [ListRel])
  | cons x xs =>
      cases xs with
      | cons y ys => exact absurd h.2 (by simp [ListRel])
      | nil =>
          cases x with
          | Ptr b' o' e' s' t' =>
              obtain ⟨⟨h_b, h_o, h_e, h_s, h_t, -⟩, -⟩ := h
              subst h_o h_e h_s
              exact ⟨b', t', rfl, h_b, h_t⟩
          | Dat v' => exact absurd h.1 (by simp [MemValSim])
          | Undef => exact absurd h.1 (by simp [MemValSim])

/-! ## The statement -/

/-- The `dealloc` step: copy's read of the pointer place through its
    exposed-register package, then one `Dealloc`, with the two
    transports above closing the invariant. Neither renaming grows. -/
theorem CompilerInv_step_dealloc {τ : LayoutTy}
    {dst : Place Γ (obseq.LayoutTy.PtrL τ)}
    (compProg : oseair.Prog)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    (h_stmt : prog.get? s_mir.pc = some (.dealloc dst))
    (h_step : mirlite.stepStmt MSB s_mir (.dealloc dst) = .ok s_mir') :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' := by
  obtain ⟨csPrefix, h_csAt, h_invAt⟩ := h_inv.invAt
  obtain ⟨h_pc, h_lbs, h_sms, h_psim, h_id_a, h_wf_t, h_tbd, h_alloc, h_unmap, h_prb⟩ :=
    h_invAt
  -- §1 the source step: the read gave a pointer at offset zero, the free succeeded
  simp only [mirlite.stepStmt] at h_step
  cases h_copy : mirlite.evalCopy MSB s_mir dst with
  | err e => rw [h_copy] at h_step; simp at h_step
  | ok out =>
  rw [h_copy] at h_step
  simp only at h_step
  split at h_step
  case h_2 => simp at h_step
  rename_i base offset ext size tag h_vals
  by_cases h_off : offset = 0
  case neg => rw [if_pos (by simpa using h_off)] at h_step; simp at h_step
  subst h_off
  rw [if_neg (by simp)] at h_step
  cases h_de : MSB.dealloc out.state.perms base size tag with
  | error e => rw [h_de] at h_step; simp at h_step
  | ok permsD =>
  rw [h_de] at h_step
  injection h_step with h_s'
  subst h_s'
  -- §2 the read, through copy's package with the register exposed
  have h_evalC : mirlite.evalRExpr MSB s_mir (.copy (flattenPlace dst)) = .ok out := by
    rw [evalRExpr_copy_flatten]
    simp only [mirlite.evalRExpr]
    exact h_copy
  obtain ⟨pOutC, h_pvalC, h_prmC, h_restC⟩ :=
    copy_readRegPkg_flat compProg dst ρa ρt s_mir s_osea csPrefix h_id_a h_wf_t h_tbd h_lbs
      h_prb h_sms h_alloc h_psim h_pc out h_evalC
  have h_sres : ∃ rs permsS, mirlite.resolvePlaceAcc MSB s_mir dst = .ok (rs, permsS) := by
    simp only [mirlite.evalCopy] at h_copy
    cases h : mirlite.resolvePlaceAcc MSB s_mir dst with
    | error e => rw [h] at h_copy; simp at h_copy
    | ok pr => exact ⟨pr.1, pr.2, rfl⟩
  obtain ⟨rs, permsS, h_sres⟩ := h_sres
  obtain ⟨dOut, hD⟩ := placeToRegChecked_ok_of_placeInputsMapped
    (cs := csPrefix) (kind := RefKind.Shared)
    (placeInputsMapped_of_localBindingSim_resolvePlace h_lbs
      (resolvePlace?_of_resolveAcc h_sres))
  obtain ⟨h_rfr, h_rfv⟩ := readToReg_flat hD
  -- §3 the statement's compiled shape: the read, then the `Dealloc`
  have h_stmtVal : CheckedCompilerM.value (compileStmtChecked (.dealloc dst)) csPrefix
      = Except.ok ⟨(), StmtEvidence.dealloc dst⟩ := by
    simp only [compileStmtChecked, csMonad, csRun, h_rfv]
  have h_stmtRun : CheckedCompilerM.run (compileStmtChecked (.dealloc dst)) csPrefix
      = emit (CheckedCompilerM.run (readToReg dst) csPrefix)
        [Instr.Dealloc (Register.R (CheckedCompilerM.run
          (placeToRegChecked RefKind.Shared (flattenPlace dst)) csPrefix).nextReg)] := by
    simp only [compileStmtChecked, csMonad, csRun, h_rfv]
  have F : StmtFrame compProg cs0 prog s_mir.pc
      (CheckedCompilerM.run (compileStmtChecked (.dealloc dst)) csPrefix) :=
    StmtFrame.ofStmt h_comp h_csAt h_stmt h_stmtVal
  rw [h_stmtRun, h_rfr] at F
  -- §4 the read's run
  have h_codeR : CodeIncluded compProg
      (CheckedCompilerM.run (compileRExprPreChecked (.copy (flattenPlace dst))) csPrefix) :=
    F.code.mono (emit_state_incr _ _)
  obtain ⟨ρt2, nR, sR, perms₂, vals, h_incrT2, h_wfT2, h_ost, -, h_runR, h_regmono,
    h_lbsR, h_psimR, h_tbdR, h_smem, h_pcR, h_vreg, h_valsRel⟩ := h_restC h_codeR
  rw [h_vals] at h_valsRel
  obtain ⟨base', tag', h_valsE, h_rb, h_rt⟩ := ListRel_ptr_inv h_valsRel
  have h_bb : base' = base := (h_id_a _ _ h_rb).symm
  subst h_bb h_valsE
  have h_entry : PtrRegisterEntry sR.reg
      (Register.R (CheckedCompilerM.run
        (placeToRegChecked RefKind.Shared (flattenPlace dst)) csPrefix).nextReg)
      base' 0 size tag' := ⟨_, h_vreg⟩
  -- §5 the free, transported, and the `Dealloc` executed
  rw [h_ost] at h_de
  obtain ⟨tgtD, h_deT, h_psimD, h_nsD, h_ntD⟩ :=
    sb_dealloc_respects_PermSim h_wfT2 h_rt size base' h_psimR h_de
  have h_codeD : compProg sR.pc = some (Instr.Dealloc (Register.R (CheckedCompilerM.run
      (placeToRegChecked RefKind.Shared (flattenPlace dst)) csPrefix).nextReg)) := by
    rw [h_pcR]
    refine F.code _ _ ?_ ?_
    · simp [emit]
    · simpa using emit_code_at_new
        (CheckedCompilerM.run (compileRExprPreChecked (.copy (flattenPlace dst))) csPrefix)
        [Instr.Dealloc (Register.R (CheckedCompilerM.run
          (placeToRegChecked RefKind.Shared (flattenPlace dst)) csPrefix).nextReg)]
        (k := 0) (by simp)
  have h_runD := runN_Dealloc_step compProg sR _ h_codeD h_entry h_deT
  -- §6 the invariant at the post-free states
  refine ⟨ρa, ρt2, _, nR + 1, AddrRenameIncr.refl ρa, h_incrT2,
    oseair_runN_trans h_runR h_runD, ?_⟩
  obtain ⟨csNext, h_next, h_nl, h_nr, h_np⟩ := F.next
  rw [h_ost]
  refine CompilerInv.ofInvAt h_next rfl h_nl h_nr h_np ⟨?_, ?_, ?_, h_psimD, h_id_a, h_wfT2,
    ?_, ?_, ?_, ?_⟩
  · show sR.pc + 1 = _
    rw [h_pcR]; simp [emit]
  · intro τ' loc' b h_env
    obtain ⟨reg, base, tag, h_pi, h_entry', h_ra, h_rt', h_nw, h_dom⟩ := h_lbsR loc' b h_env
    exact ⟨reg, base, tag, by rw [getPlaceInfo_emit]; exact h_pi, h_entry', h_ra, h_rt', h_nw,
      h_dom⟩
  · show SourceMemSim ρa ρt2 (s_mir.mem.removeRange base' size) (sR.mem.removeRange base' size)
    refine SourceMemSim.removeRange h_id_a ?_ base' size
    rw [h_smem]
    exact SourceMemSim.rename_mono (AddrRenameIncr.refl ρa) h_incrT2 h_sms
  · show TagRenameBounded ρt2 permsD.NextTag tgtD.NextTag
    rw [h_nsD, h_ntD]
    exact h_tbdR
  · show AllocLockstep ρa (s_mir.mem.removeRange base' size) (sR.mem.removeRange base' size)
    rw [h_smem]
    exact ⟨h_alloc.1, h_alloc.2.1, h_alloc.2.2⟩
  · intro τ' loc' h_none
    rw [getPlaceInfo_emit, getPlaceInfo_congr' h_prmC]
    exact h_unmap loc' h_none
  · intro idx reg τ'' h_look
    rw [getPlaceInfo_emit, getPlaceInfo_congr' h_prmC] at h_look
    show RegisterBelow (emit _ _).nextReg reg
    simp only [emit]
    exact RegisterBelow.mono h_regmono (h_prb idx reg τ'' h_look)

end obseq3.proof
