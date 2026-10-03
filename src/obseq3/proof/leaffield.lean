import obseq3.proof.readsrc

/-!
# One-leaf rvalues with a field operand

`ptrCast`, `ptrOffset` and `fromExposed` read ONE leaf of
their operand. When the operand is a field `b.f`:
- at byte offset zero (and for nested fields, after flattening) the field
  lowers as its base, so the chain skeletons apply through the lowering
  contract (`proj_nested_lowers`/`proj_nested_compiles` add nesting);
- at a nonzero offset the compiled read is `Borrow(Shared); op; Die`
  through the borrow temporary, and keystone's `sb_ref_read_die_cancels`
  closes it — provided the op reads exactly the field's bytes, which
  `LeafWF` (integer- and pointer-typed places have a one-leaf layout)
  guarantees. `refSlice` (a retag after the bracket) and `exposeAddr`
  (an exposure inside it) are in `refslicefield.lean`/`exposefield.lean`.
-/

namespace obseq3.proof

open obseq3 obseq3.bytes obseq3.proof
open obseq3.mirlite (MemValue Binding Env PlaceRes)
open obseq3.oseair (Val Register)
open obseq3.compile

/-! ## Nested fields lower as the flattened field -/

theorem proj_nested_lowers {Γ : Ctx} {L : mirlite.LayEnv Γ} {compProg : oseair.Prog}
    {ρ σ τ : LayoutTy} {b : Place Γ ρ} {q : PathTo ρ σ} {p : PathTo σ τ}
    (h : LowersB L compProg (.proj b (q.append p))) : LowersB L compProg (.proj (.proj b q) p) := by
  intro ρt sM kind cs sA resolved permsD hwf h_res h_tbd h_lbs h_prb h_mem h_lock h_psim h_pc h_inc
  obtain ⟨h_run, h_val⟩ := placeToReg_assoc (L := L) kind b q p cs
  rw [resolvePlaceAcc_assoc] at h_res
  rw [h_run] at h_inc
  obtain ⟨o2, n, s', t, h2⟩ :=
    h ρt sM kind cs sA resolved permsD hwf h_res h_tbd h_lbs h_prb h_mem h_lock h_psim h_pc h_inc
  rw [h2.val] at h_val
  cases h_v1 : CheckedCompilerM.value (placeToRegChecked L kind (.proj (.proj b q) p)) cs with
  | error e => rw [h_v1] at h_val; cases h_val
  | ok o1 =>
      rw [h_v1] at h_val
      simp only [Except.map, Except.ok.injEq] at h_val
      exact ⟨o1, n, s', t, h2.congr h_v1 h_val h_run⟩

theorem proj_nested_compiles {Γ : Ctx} {L : mirlite.LayEnv Γ}
    {ρ σ τ : LayoutTy} {b : Place Γ ρ} {q : PathTo ρ σ} {p : PathTo σ τ}
    (h : CompilesB L (.proj b (q.append p))) : CompilesB L (.proj (.proj b q) p) := by
  intro s cs kind r h_map h_res
  obtain ⟨h_run, h_val⟩ := placeToReg_assoc (L := L) kind b q p cs
  rw [resolvePlaceAcc_assoc] at h_res
  obtain ⟨o2, h_v2, h_c2, h_p2⟩ := h s cs kind r h_map h_res
  rw [h_v2] at h_val
  cases h_v1 : CheckedCompilerM.value (placeToRegChecked L kind (.proj (.proj b q) p)) cs with
  | error e => rw [h_v1] at h_val; cases h_val
  | ok o1 =>
      rw [h_v1] at h_val
      simp only [Except.map, Except.ok.injEq] at h_val
      exact ⟨o1, rfl, by rw [h_val]; exact h_c2, by rw [h_run]; exact h_p2⟩

/-! ## The one-leaf layout condition -/

/-- Integer- and pointer-typed places have a one-leaf layout: the leaf a
    one-leaf read decodes spans the whole place. -/
def LeafWF {Γ : Ctx} (L : mirlite.LayEnv Γ) : Prop :=
  (∀ {σ : LayoutTy} (p : Place Γ (LayoutTy.PtrL σ)),
    (mirlite.leafKind (mirlite.placeLayout L p)).size = (mirlite.placeLayout L p).size) ∧
  (∀ {t : IntTy} (p : Place Γ (LayoutTy.IntL t)),
    (mirlite.leafKind (mirlite.placeLayout L p)).size = (mirlite.placeLayout L p).size)

/-! ## Read-only one-leaf ops -/

/-- An rvalue that reads one leaf through `src` and changes no permission
    beyond that read: its source evaluation is a checked read, and its
    target instruction, given the target read's outcome, yields related
    values. -/
structure ReadOnlyOpB {Γ : Ctx} (L : mirlite.LayEnv Γ) (dstL : BLayout) {σ τ : LayoutTy}
    (rhs : RExpr Γ τ) (src : Place Γ σ) (mk : Register → oseair.Rhs) : Prop where
  source : ∀ (sM : mirlite.State MSB Γ) output,
    mirlite.evalRExpr MSB L sM dstL rhs = .ok output →
    ∃ resolved permsR perms', mirlite.resolvePlaceAcc MSB L sM src = .ok (resolved, permsR) ∧
      ¬ sM.mem.isFreed resolved.allocBase = true ∧
      ¬ (resolved.addr + (mirlite.leafKind (mirlite.placeLayout L src)).size
          > resolved.allocBase + resolved.allocSize) ∧
      sb_read permsR resolved.addr (mirlite.leafKind (mirlite.placeLayout L src)).size
        resolved.tag = .ok perms' ∧
      output.state = { sM with perms := perms' }
  target : ∀ (ρt : TagRenameMap) (sM : mirlite.State MSB Γ) (s1 : oseair.State MSB) (reg : Register)
      (resolved : PlaceRes) (permsR : MSB.State) (ext : Nat) (T : Tag) output (pmid : AccessPerms),
    mirlite.evalRExpr MSB L sM dstL rhs = .ok output →
    mirlite.resolvePlaceAcc MSB L sM src = .ok (resolved, permsR) →
    TagRenameWF ρt → ByteMemSim ρt sM.mem s1.mem → ByteAllocLockstep sM.mem s1.mem →
    s1.reg.lookup reg = some [Val.Ptr resolved.allocBase (resolved.addr - resolved.allocBase) ext
      resolved.allocSize T] →
    resolved.allocBase ≤ resolved.addr →
    sb_read s1.perms resolved.addr (mirlite.leafKind (mirlite.placeLayout L src)).size T = .ok pmid →
    ∃ vals, oseair.evalRhs MSB s1 (mk reg) = .Ok vals { s1 with perms := pmid } ∧
      ListRel (StoreSim ρt) output.values (vals.map oseair.Val.toMem)

/-- The target's one-leaf read, given the SB read's outcome. -/
theorem readCellThrough_ro {ρt : TagRenameMap} (hwf : TagRenameWF ρt)
    {s1 : oseair.State MSB} {reg : Register} {resolved : PlaceRes} {ext : Nat} {T : Tag}
    {mS : bytes.Mem} {k : Scalar} {pmid : AccessPerms}
    (h_reg : s1.reg.lookup reg = some [Val.Ptr resolved.allocBase
      (resolved.addr - resolved.allocBase) ext resolved.allocSize T])
    (h_le : resolved.allocBase ≤ resolved.addr) (h_mem : ByteMemSim ρt mS s1.mem)
    (h_lock : ByteAllocLockstep mS s1.mem) (h_free : ¬ mS.isFreed resolved.allocBase = true)
    (h_bnd : ¬ (resolved.addr + k.size > resolved.allocBase + resolved.allocSize))
    (h_rd : sb_read s1.perms resolved.addr k.size T = .ok pmid) :
    oseair.readCellThrough MSB s1 reg k
        = .ok (oseair.ofMem (mirlite.decodeV k (s1.mem.read resolved.addr k.size)), pmid) ∧
      ValSim ρt (mirlite.decodeV k (mS.read resolved.addr k.size))
        (mirlite.decodeV k (s1.mem.read resolved.addr k.size)) := by
  have hA : resolved.allocBase + (resolved.addr - resolved.allocBase) = resolved.addr :=
    Nat.add_sub_cancel' h_le
  have h_freeT : s1.mem.isFreed resolved.allocBase = false := by
    simp only [bytes.Mem.isFreed, ← h_lock.2.2] at h_free ⊢
    simpa using h_free
  refine ⟨?_, decodeV_sim hwf k (h_mem.read _ _)⟩
  simp only [oseair.readCellThrough, h_reg, hA, h_freeT, Bool.false_eq_true, if_false, h_bnd,
    PermissionModel.stackedBorrows, h_rd]

theorem ptrOffset_ro {Γ : Ctx} {L : mirlite.LayEnv Γ} (dstL : BLayout) {σ τ : LayoutTy}
    (src : Place Γ (LayoutTy.PtrL σ)) (delta : Int) :
    ReadOnlyOpB L dstL (RExpr.ptrOffset (τ := τ) src delta) src
      (fun r => oseair.Rhs.PtrOffset (mirlite.leafKind (mirlite.placeLayout L src)) r
        (delta * ((mirlite.pointeeLayout L src).size : Int))) where
  source sM output h := by
    simp only [mirlite.evalRExpr] at h
    split at h
    · cases h
    · rename_i base offset e sz tag perms' h_rc
      split at h
      · cases h
      simp only [mirlite.EvalResult.ok.injEq] at h
      subst h
      obtain ⟨r, p, h_r, h_free, h_bnd, h_rd, -⟩ := readCell_inv h_rc
      exact ⟨r, p, perms', h_r, h_free, h_bnd, h_rd, rfl⟩
    · cases h
  target ρt sM s1 reg resolved permsR ext T output pmid h h_res hwf h_mem h_lock h_reg h_le h_rdT := by
    simp only [mirlite.evalRExpr] at h
    split at h
    · cases h
    · rename_i base offset e sz tag perms' h_rc
      split at h
      · cases h
      rename_i h_neg
      simp only [mirlite.EvalResult.ok.injEq] at h
      subst h
      obtain ⟨r', p', h_r', h_free, h_bnd, h_rd, h_v⟩ := readCell_inv h_rc
      obtain ⟨rfl, rfl⟩ := resolve_eq h_res h_r'
      obtain ⟨h_rct, h_vs⟩ := readCellThrough_ro hwf h_reg h_le h_mem h_lock h_free h_bnd h_rdT
      rw [← h_v] at h_vs
      obtain ⟨t', h_w, h_t⟩ := valSim_ptr h_vs
      refine ⟨[Val.Ptr base (((offset : Int) + delta * ((mirlite.pointeeLayout L src).size : Int)).toNat)
          e sz t'], ?_, ?_⟩
      · simp only [oseair.evalRhs]
        rw [h_rct, h_w]
        simp only [oseair.ofMem, h_neg, if_false]
      · refine ⟨Or.inr ⟨by simp, ?_⟩, trivial⟩
        simp only [ValSim, oseair.Val.toMem, oseair.ofMem, MemValSim, idA]
        exact ⟨trivial, trivial, trivial, trivial, h_t, fun _ _ => ⟨_, rfl⟩⟩
    · cases h

theorem fromExposed_ro {Γ : Ctx} {L : mirlite.LayEnv Γ} (dstL : BLayout) {τ : LayoutTy}
    (src : Place Γ (LayoutTy.IntL tN)) :
    ReadOnlyOpB L dstL (RExpr.fromExposed (τ := τ) src) src
      (oseair.Rhs.FromExposed (mirlite.leafKind (mirlite.placeLayout L src))) where
  source sM output h := by
    simp only [mirlite.evalRExpr] at h
    split at h
    · cases h
    · rename_i n perms' h_rc
      simp only [mirlite.EvalResult.ok.injEq] at h
      subst h
      obtain ⟨r, p, h_r, h_free, h_bnd, h_rd, -⟩ := readCell_inv h_rc
      exact ⟨r, p, perms', h_r, h_free, h_bnd, h_rd, rfl⟩
    · cases h
  target ρt sM s1 reg resolved permsR ext T output pmid h h_res hwf h_mem h_lock h_reg h_le h_rdT := by
    simp only [mirlite.evalRExpr] at h
    split at h
    · cases h
    · rename_i n perms' h_rc
      simp only [mirlite.EvalResult.ok.injEq] at h
      subst h
      obtain ⟨r', p', h_r', h_free, h_bnd, h_rd, h_v⟩ := readCell_inv h_rc
      obtain ⟨rfl, rfl⟩ := resolve_eq h_res h_r'
      obtain ⟨h_rct, h_vs⟩ := readCellThrough_ro hwf h_reg h_le h_mem h_lock h_free h_bnd h_rdT
      rw [← h_v] at h_vs
      have h_w := valSim_word h_vs
      have h_ao : s1.mem.allocOf n = sM.mem.allocOf n := by
        simp only [bytes.Mem.allocOf, h_lock.1]
      refine ⟨[Val.Ptr ((sM.mem.allocOf n).getD (n, 0)).1 (n - ((sM.mem.allocOf n).getD (n, 0)).1)
          (((sM.mem.allocOf n).getD (n, 0)).2 - (n - ((sM.mem.allocOf n).getD (n, 0)).1))
          ((sM.mem.allocOf n).getD (n, 0)).2 wildcardTag], ?_, ?_⟩
      · simp only [oseair.evalRhs]
        rw [h_rct, h_w]
        simp only [oseair.ofMem, h_ao]
      · refine ⟨Or.inr ⟨by simp, ?_⟩, trivial⟩
        simp only [ValSim, oseair.Val.toMem, oseair.ofMem, MemValSim, idA]
        exact ⟨trivial, trivial, trivial, trivial, hwf.2, fun _ _ => ⟨_, rfl⟩⟩
    · cases h

theorem ptrCast_ro {Γ : Ctx} {L : mirlite.LayEnv Γ} (dstL : BLayout) {σ τ : LayoutTy}
    (src : Place Γ (LayoutTy.PtrL σ)) :
    ReadOnlyOpB L dstL (RExpr.ptrCast (τ := τ) src) src
      (oseair.Rhs.Load (leafLayout (mirlite.leafKind (mirlite.placeLayout L src)))) where
  source sM output h := by
    simp only [mirlite.evalRExpr] at h
    split at h
    · cases h
    · rename_i v perms' h_rc
      split at h
      · cases h
      simp only [mirlite.EvalResult.ok.injEq] at h
      subst h
      obtain ⟨r, p, h_r, h_free, h_bnd, h_rd, -⟩ := readCell_inv h_rc
      exact ⟨r, p, perms', h_r, h_free, h_bnd, h_rd, rfl⟩
  target ρt sM s1 reg resolved permsR ext T output pmid h h_res hwf h_mem h_lock h_reg h_le h_rdT := by
    simp only [mirlite.evalRExpr] at h
    split at h
    · cases h
    · rename_i v perms' h_rc
      split at h
      · cases h
      rename_i h_def
      simp only [mirlite.EvalResult.ok.injEq] at h
      subst h
      obtain ⟨r', p', h_r', h_free, h_bnd, h_rd, h_v⟩ := readCell_inv h_rc
      obtain ⟨rfl, rfl⟩ := resolve_eq h_res h_r'
      have hv : v ≠ .undef := fun h' => h_def (by rw [h']; rfl)
      have h_vs := decodeV_sim hwf (mirlite.leafKind (mirlite.placeLayout L src))
        (h_mem.read resolved.addr (mirlite.leafKind (mirlite.placeLayout L src)).size)
      rw [← h_v] at h_vs
      obtain ⟨h_defT, h_relS⟩ := readL_rel (vs := [v])
        (ws := [mirlite.decodeV (mirlite.leafKind (mirlite.placeLayout L src))
          (s1.mem.read resolved.addr (mirlite.leafKind (mirlite.placeLayout L src)).size)])
        (show ListRel _ [v] [_] from ⟨h_vs, trivial⟩)
        (by simp only [List.any_cons, List.any_nil, Bool.or_false]
            exact Bool.eq_false_iff.mpr h_def)
      have hA : resolved.allocBase + (resolved.addr - resolved.allocBase) = resolved.addr :=
        Nat.add_sub_cancel' h_le
      have h_freeT : s1.mem.isFreed resolved.allocBase = false := by
        simp only [bytes.Mem.isFreed, ← h_lock.2.2] at h_free ⊢
        simpa using h_free
      refine ⟨_, ?_, h_relS⟩
      simp only [oseair.evalRhs, h_reg, hA, h_freeT, Bool.false_eq_true, if_false,
        leafLayout_size, h_bnd, PermissionModel.stackedBorrows, h_rdT, readL_leafLayout,
        List.map_cons, List.map_nil]
      have h_defT' : ([oseair.ofMem (mirlite.decodeV (mirlite.leafKind (mirlite.placeLayout L src))
          (s1.mem.read resolved.addr (mirlite.leafKind (mirlite.placeLayout L src)).size))].any
          fun v => v == Val.Undef) = false := h_defT
      rw [h_defT']
      rfl

/-! ## The bracket skeleton -/

theorem readRhsPre_shapeG {Γ : Ctx} {L : mirlite.LayEnv Γ} {dstL : BLayout}
    {σ τ : LayoutTy} {rhs : RExpr Γ τ} {src : Place Γ σ} {mk : Register → oseair.Rhs}
    {post : Register → List oseair.Instr}
    {ev : (srcRes : PtrResult) → PlaceToRegEvidence L RefKind.Shared src srcRes →
      (dstPtr : Register) → RExprToEvidence L dstPtr rhs}
    {cs : CompilerState}
    {sOut : ResultWithEvidence PtrResult (PlaceToRegEvidence L RefKind.Shared src)}
    (h_sval : CheckedCompilerM.value (placeToRegChecked L RefKind.Shared src) cs = .ok sOut) :
    CheckedCompilerM.run (readRhsPre L dstL rhs src mk post ev) cs
      = emit (bumpReg (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared src) cs))
          ([oseair.Instr.Assgn
            (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared src) cs).nextReg)
            (mk sOut.result.reg)] ++ cleanupInstrs sOut.result.cleanup ++
            post (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared src) cs).nextReg)) ∧
    ∃ pOut, CheckedCompilerM.value (readRhsPre L dstL rhs src mk post ev) cs = Except.ok pOut ∧
      (∀ d, pOut.store d = [oseair.Instr.RStore dstL
        (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared src) cs).nextReg) d]) ∧
      pOut.postCleanup = [] := by
  simp only [readRhsPre, CheckedCompilerM.run_bind, CheckedCompilerM.value_bind,
    CheckedCompilerM.run_lift, CheckedCompilerM.value_lift, CheckedCompilerM.run_pure,
    CheckedCompilerM.value_pure, h_sval]
  exact ⟨rfl, _, rfl, fun _ => rfl, rfl⟩

/-- The compile-time half of a nonzero-offset field read: the projection
    lowers to one route borrow with one cleanup entry, and its lowering
    leaves the place map alone. -/
theorem projoff_compile {Γ : Ctx} {L : mirlite.LayEnv Γ} {ρ τ : LayoutTy} {b : Place Γ ρ}
    {f : PathTo ρ τ} {ρt : TagRenameMap} {sM : mirlite.State MSB Γ} {sA : oseair.State MSB}
    {csA : CompilerState} {r : PlaceRes × MSB.State}
    (h_np : ∀ (σ' : LayoutTy) (bb : Place Γ σ') (q : PathTo σ' ρ), b = bb.proj q → False)
    (h0 : pathOffset L b f ≠ 0) (hcb : CompilesB L b)
    (h_lbs : LocalBindingSimB L ρt sM.env sA csA)
    (h_res : mirlite.resolvePlaceAcc MSB L sM (.proj b f) = .ok r) :
    ∃ outP, CheckedCompilerM.value (placeToRegChecked L RefKind.Shared (.proj b f)) csA = .ok outP ∧
      outP.result.cleanup.length = 1 ∧
      (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared (.proj b f)) csA).placeRegMap
        = csA.placeRegMap := by
  obtain ⟨_, h_rb, -⟩ := borrow_proj_res (L := L) f sM _ h_res
  obtain ⟨bOut, h_bval, h_bclean, h_bprm⟩ := hcb sM csA RefKind.Shared _ (fun loc bnd h => by
    obtain ⟨r, t, hpi, -⟩ := h_lbs loc bnd h
    exact ⟨r, _, hpi⟩) h_rb
  obtain ⟨h_runP, outP, h_valP, h_resP⟩ :=
    (proj_lowering (kind := RefKind.Shared) f h_np h_bval).2 h0
  refine ⟨outP, h_valP, by rw [h_resP, h_bclean]; rfl, by rw [h_runP]; exact h_bprm⟩

/-- The one-leaf bracket at a nonzero field offset, `Borrow(Shared); op;
    Die`, for any op whose target effect, given the read through the fresh
    tag, is that read followed by a permission transform `g` that commutes
    with `Die` (the identity for a plain read, the exposure for
    `exposeAddr`). The source's one read of the field is matched: the
    bracket ends in `g q3` with `q3` related to the source's post-read
    state, the op's values in the load register, and memory unchanged.
    `post` (code after the bracket, e.g. `refSlice`'s retag) is not run. -/
theorem projoff_bracket {Γ : Ctx} {L : mirlite.LayEnv Γ} {compProg : oseair.Prog}
    {dstL : BLayout} {ρ τ τr : LayoutTy} {b : Place Γ ρ} {f : PathTo ρ τ} {rhs : RExpr Γ τr}
    {mk : Register → oseair.Rhs} {post : Register → List oseair.Instr}
    {ev : (srcRes : PtrResult) → PlaceToRegEvidence L RefKind.Shared (.proj b f) srcRes →
      (dstPtr : Register) → RExprToEvidence L dstPtr rhs}
    {P : List Val → (AccessPerms → AccessPerms) → Prop}
    (h_np : ∀ (σ' : LayoutTy) (bb : Place Γ σ') (q : PathTo σ' ρ), b = bb.proj q → False)
    (h0 : pathOffset L b f ≠ 0) (hb : LowersB L compProg b) (hcb : CompilesB L b)
    (h_len : (mirlite.leafKind (mirlite.placeLayout L (.proj b f))).size = placeSize L (.proj b f))
    {ρt : TagRenameMap} {sM : mirlite.State MSB Γ} {sA : oseair.State MSB} {csA : CompilerState}
    (h_wf : TagRenameWF ρt) (h_tbd : TagRenameBounded ρt sM.perms.NextTag sA.perms.NextTag)
    (h_lbs : LocalBindingSimB L ρt sM.env sA csA) (h_prb : PlaceRegMapBoundB csA)
    (h_mem : ByteMemSim ρt sM.mem sA.mem) (h_alloc : ByteAllocLockstep sM.mem sA.mem)
    (h_psim : PermSim ρt sM.perms sA.perms) (h_pc : sA.pc = csA.nextLabel)
    {resolved : PlaceRes} {permsR perms' : MSB.State}
    (h_res : mirlite.resolvePlaceAcc MSB L sM (.proj b f) = .ok (resolved, permsR))
    (h_free : ¬ sM.mem.isFreed resolved.allocBase = true)
    (h_bnd : ¬ (resolved.addr + (mirlite.leafKind (mirlite.placeLayout L (.proj b f))).size
        > resolved.allocBase + resolved.allocSize))
    (h_rd : sb_read permsR resolved.addr (mirlite.leafKind (mirlite.placeLayout L (.proj b f))).size
        resolved.tag = .ok perms')
    (h_op : ∀ (S1 : oseair.State MSB) (reg : Register) (ext : Nat) (T : Tag) (pmid : AccessPerms),
      ByteMemSim ρt sM.mem S1.mem → ByteAllocLockstep sM.mem S1.mem →
      S1.reg.lookup reg = some [Val.Ptr resolved.allocBase (resolved.addr - resolved.allocBase) ext
        resolved.allocSize T] →
      resolved.allocBase ≤ resolved.addr →
      sb_read S1.perms resolved.addr (mirlite.leafKind (mirlite.placeLayout L (.proj b f))).size T
        = .ok pmid →
      ∃ vals g, oseair.evalRhs MSB S1 (mk reg) = .Ok vals { S1 with perms := g pmid } ∧
        (∀ (p p' : AccessPerms) a n t, sb_die p a n t = .ok p' → sb_die (g p) a n t = .ok (g p')) ∧
        P vals g)
    (h_code : CodeIncludedB compProg
      (CheckedCompilerM.run (readRhsPre L dstL rhs (.proj b f) mk post ev) csA)) :
    ∃ (n : Nat) (s3 : oseair.State MSB) (q3 : AccessPerms) (vals : List Val)
      (g : AccessPerms → AccessPerms),
      oseair.runN MSB n sA compProg = .Ok s3 ∧
      s3.pc = (CheckedCompilerM.run (readRhsPre L dstL rhs (.proj b f) mk (fun _ => []) ev) csA).nextLabel ∧
      s3.mem = sA.mem ∧ s3.perms = g q3 ∧
      PermSim ρt perms' q3 ∧ TagRenameBounded ρt perms'.NextTag q3.NextTag ∧
      s3.reg.lookup
        (Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared (.proj b f)) csA).nextReg)
        = some vals ∧
      (∀ r, RegisterBelow csA.nextReg r → s3.reg.lookup r = sA.reg.lookup r) ∧
      csA.nextReg ≤ (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared (.proj b f)) csA).nextReg ∧
      P vals g := by
  obtain ⟨⟨bRes, permsB⟩, h_rb, h_addr, h_tag, h_ab, h_as, h_pb⟩ :=
    borrow_proj_res (L := L) f sM _ h_res
  simp only at h_addr h_tag h_ab h_as h_pb
  subst h_pb
  -- compile-time
  obtain ⟨bOut, h_bval, h_bclean, h_bprm⟩ := hcb sM csA RefKind.Shared _ (fun loc bnd h => by
    obtain ⟨r, t, hpi, -⟩ := h_lbs loc bnd h
    exact ⟨r, _, hpi⟩) h_rb
  obtain ⟨h_runP, outP, h_valP, h_resP⟩ :=
    (proj_lowering (kind := RefKind.Shared) f h_np h_bval).2 h0
  obtain ⟨h_run0, -⟩ :=
    readRhsPre_shapeG (dstL := dstL) (rhs := rhs) (mk := mk) (post := fun _ => []) (ev := ev) h_valP
  obtain ⟨h_runG, -⟩ :=
    readRhsPre_shapeG (dstL := dstL) (rhs := rhs) (mk := mk) (post := post) (ev := ev) h_valP
  rw [h_resP, h_bclean, h_runP] at h_run0 h_runG
  simp only [List.nil_append, cleanupInstrs, List.reverse_cons, List.reverse_nil,
    List.map_cons, List.map_nil, List.append_nil] at h_run0 h_runG
  rw [h_runG] at h_code
  have h_code3 := h_code.mono (emit_append_state_incr _ _ _)
  rw [h_runP]
  rw [h_run0]
  -- the base's lowering
  obtain ⟨bOut', n1, s1, tres, hB⟩ :=
    hb ρt sM RefKind.Shared csA sA bRes permsR h_wf h_rb h_tbd h_lbs h_prb h_mem h_alloc h_psim h_pc
      (h_code3.mono (((bumpReg_state_incr' _).trans (emit_state_incr _ _)).trans
        ((bumpReg_state_incr' _).trans (emit_state_incr _ _))))
  have h_same : bOut' = bOut := by
    have := hB.val
    rw [h_bval] at this
    exact (Except.ok.inj this).symm
  subst h_same
  obtain ⟨ext, h_bentry⟩ := hB.entry
  have hA : bRes.allocBase + (bRes.addr - bRes.allocBase) = bRes.addr :=
    Nat.add_sub_cancel' hB.le
  have h_mem1 : ByteMemSim ρt sM.mem s1.mem := by rw [hB.mem]; exact h_mem
  have h_lock1 : ByteAllocLockstep sM.mem s1.mem := by rw [hB.mem]; exact h_alloc
  have h_freeT : s1.mem.isFreed bRes.allocBase = false := by
    rw [h_ab] at h_free
    simp only [bytes.Mem.isFreed, ← h_lock1.2.2] at h_free ⊢
    simpa using h_free
  have h_bnd' : bRes.addr + pathOffset L b f + placeSize L (.proj b f)
      ≤ bRes.allocBase + bRes.allocSize := by
    rw [← h_ab, ← h_as, ← h_len]
    have := Nat.le_of_not_gt h_bnd
    rw [h_addr] at this
    exact this
  -- the read, transported; the target's Shared retag; the cancellation
  have h_rd0 := h_rd
  rw [h_addr, h_tag, h_len] at h_rd0
  obtain ⟨p2, h_rd', h_psim2⟩ := sb_read_respects_PermSim hB.psim h_wf hB.rt h_rd0
  obtain ⟨q1, h_ref⟩ := sb_ref_Shared_ok_of_sb_read_ok h_rd'
  have h_tbd_mid : TagRenameBounded ρt permsR.NextTag s1.perms.NextTag := by
    rw [hB.srcNT]; exact TagRenameBounded.mono h_tbd (Nat.le_refl _) hB.tgtNT
  have h_unprot := freshTag_not_protected hB.psim h_tbd_mid
  have h0w : wildcardTag < s1.perms.NextTag := (h_tbd_mid _ _ h_wf.2).2
  have h_ntw : (s1.perms.NextTag == wildcardTag) = false := by
    simp only [beq_eq_false_iff_ne]; exact (Nat.ne_of_lt h0w).symm
  obtain ⟨q2, q3, sAcc, h_rd1, h_die1, h_rd2, h_sm, h_ex, h_pf, h_ntle, h_wk⟩ :=
    sb_ref_read_die_cancels h_ntw h_unprot h_ref
  have h_acc : sAcc = p2 := Except.ok.inj (h_rd2.symm.trans h_rd')
  subst h_acc
  -- the code
  have hct := code_borrow_load_die (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared b) csA)
  let tmp := Register.R (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared b) csA).nextReg
  let ld := Register.R ((CheckedCompilerM.run (placeToRegChecked L RefKind.Shared b) csA).nextReg + 1)
  have h_at : ∀ k i, k < 3 →
      (emit (bumpReg (emit (bumpReg (CheckedCompilerM.run (placeToRegChecked L RefKind.Shared b) csA))
        [oseair.Instr.Assgn tmp
          (borrowRhs RefKind.Shared (placeSize L (.proj b f)) bOut'.result.reg (pathOffset L b f))]))
        ([oseair.Instr.Assgn ld (mk tmp)] ++ [oseair.Instr.Die tmp (placeSize L (.proj b f))])).code
          (s1.pc + k) = some i →
      compProg (s1.pc + k) = some i := by
    intro k i hk hc
    refine h_code3 _ i ?_ hc
    rw [(hct _ _ _).2.2.2, hB.pc]; omega
  -- §1 Borrow
  have h1 := runN_Borrow (s := s1) (h_at 0 _ (by omega) (by rw [hB.pc]; exact (hct _ _ _).1))
    h_bentry h_freeT (by rw [hA]; exact h_bnd') (by rw [hA]; exact h_ref)
  -- §2 the op, through the fresh tag
  let S1 : oseair.State MSB :=
    { s1 with
        perms := q1,
        reg := s1.reg.insert tmp
          [Val.Ptr bRes.allocBase (bRes.addr - bRes.allocBase + pathOffset L b f)
            (placeSize L (.proj b f)) bRes.allocSize s1.perms.NextTag],
        pc := s1.pc + 1 }
  have h_le : resolved.allocBase ≤ resolved.addr := by
    rw [h_ab, h_addr]; exact Nat.le_trans hB.le (Nat.le_add_right _ _)
  have h_regS1 : S1.reg.lookup tmp = some [Val.Ptr resolved.allocBase
      (resolved.addr - resolved.allocBase) (placeSize L (.proj b f)) resolved.allocSize
      s1.perms.NextTag] := by
    rw [h_ab, h_as, h_addr]
    show (s1.reg.insert tmp _).lookup tmp = _
    rw [RegMap.lookup_insert_self, Nat.sub_add_comm hB.le]
  obtain ⟨vals, g, h_evT, h_gdie, hP⟩ := h_op S1 tmp _ _ q2 h_mem1 h_lock1 h_regS1 h_le
    (by rw [h_len, h_addr]; exact h_rd1)
  have h2 := runN_Assgn (h_at 1 _ (by omega) (by rw [hB.pc]; exact (hct _ _ _).2.1)) h_evT
  -- §3 Die
  let S2 : oseair.State MSB := { S1 with perms := g q2, reg := S1.reg.insert ld vals, pc := S1.pc + 1 }
  have hne : tmp ≠ ld := by simp [tmp, ld]
  have h3 := runN_Die (s := S2) (h_at 2 _ (by omega) (by rw [hB.pc]; exact (hct _ _ _).2.2.1))
    (by
      show (S1.reg.insert ld vals).lookup tmp = _
      rw [RegMap.lookup_insert_ne _ _ hne]
      exact RegMap.lookup_insert_self _ _ _)
    (by rw [← Nat.add_assoc, hA]; exact h_gdie _ _ _ _ _ h_die1)
  refine ⟨n1 + 1 + 1 + 1, { S2 with perms := g q3, pc := S2.pc + 1 }, q3, vals, g,
    runN_trans (runN_trans (runN_trans hB.run h1) h2) h3, ?_, hB.mem, rfl, ?_, ?_, ?_, ?_, ?_, hP⟩
  · show s1.pc + 1 + 1 + 1 = _
    rw [(hct _ _ _).2.2.2, hB.pc]
  · exact ⟨by rw [h_sm]; exact h_psim2.1, by rw [h_pf]; exact h_psim2.2.1,
      by rw [h_ex]; exact h_psim2.2.2.1, Nat.le_trans h_psim2.2.2.2.1 h_ntle,
      by rw [h_wk]; exact h_psim2.2.2.2.2⟩
  · rw [sb_read_NextTag h_rd, hB.srcNT]
    refine TagRenameBounded.mono h_tbd (Nat.le_refl _) (Nat.le_trans hB.tgtNT ?_)
    rw [← sb_read_NextTag h_rd']; exact h_ntle
  · show (S1.reg.insert ld vals).lookup ld = _
    exact RegMap.lookup_insert_self _ _ _
  · intro r hr
    have hr' := RegisterBelow.mono hB.regmono hr
    have hne1 : r ≠ tmp := RegisterBelow.ne_fresh hr'
    have hne2 : r ≠ ld := RegisterBelow.ne_fresh (RegisterBelow.mono (Nat.le_succ _) hr')
    show ((s1.reg.insert tmp _).insert ld vals).lookup r = _
    rw [RegMap.lookup_insert_ne _ _ hne2, RegMap.lookup_insert_ne _ _ hne1]
    exact hB.frame r hr
  · show csA.nextReg ≤ _ + 1
    have := hB.regmono
    omega

theorem leaf_pkg_projoff {Γ : Ctx} {L : mirlite.LayEnv Γ} {compProg : oseair.Prog}
    {dstL : BLayout} {ρ τ τr : LayoutTy} {b : Place Γ ρ} {f : PathTo ρ τ} {rhs : RExpr Γ τr}
    {mk : Register → oseair.Rhs}
    {ev : (srcRes : PtrResult) → PlaceToRegEvidence L RefKind.Shared (.proj b f) srcRes →
      (dstPtr : Register) → RExprToEvidence L dstPtr rhs}
    (h_np : ∀ (σ' : LayoutTy) (bb : Place Γ σ') (q : PathTo σ' ρ), b = bb.proj q → False)
    (h0 : pathOffset L b f ≠ 0) (hb : LowersB L compProg b) (hcb : CompilesB L b)
    (h_len : (mirlite.leafKind (mirlite.placeLayout L (.proj b f))).size = placeSize L (.proj b f))
    (h_op : ReadOnlyOpB L dstL rhs (.proj b f) mk)
    (h_pre : compileRExprPreChecked L dstL rhs = readRhsPre L dstL rhs (.proj b f) mk (fun _ => []) ev) :
    ValuePkgB compProg L dstL rhs := by
  intro ρt sM sA csA h_wf h_tbd h_lbs h_prb h_mem h_alloc h_psim h_pc _h_unmap output h_ev
  obtain ⟨resolved, permsR, perms', h_res, h_free, h_bnd, h_rd, h_ost⟩ := h_op.source sM output h_ev
  obtain ⟨outP, h_valP, -, h_prmP⟩ := projoff_compile h_np h0 hcb h_lbs h_res
  obtain ⟨h_run, pOut, h_val, h_store, h_post⟩ :=
    readRhsPre_shapeG (dstL := dstL) (rhs := rhs) (mk := mk) (post := fun _ => []) (ev := ev) h_valP
  have h_prmR : (CheckedCompilerM.run (readRhsPre L dstL rhs (.proj b f) mk (fun _ => []) ev)
      csA).placeRegMap = csA.placeRegMap := by rw [h_run]; exact h_prmP
  rw [h_pre]
  refine ⟨_, pOut, h_val, h_store, h_post, h_prmR, fun h_code => ?_⟩
  obtain ⟨n, s3, q3, vals, g, h_runT, h_pc3, h_mem3, h_g, h_ps, h_tb, h_ld, h_fr, h_nr, rfl, h_rel⟩ :=
    projoff_bracket (P := fun vals g => g = id ∧
        ListRel (StoreSim ρt) output.values (vals.map oseair.Val.toMem))
      h_np h0 hb hcb h_len h_wf h_tbd h_lbs h_prb h_mem h_alloc h_psim h_pc h_res h_free h_bnd h_rd
      (fun S1 reg ext T pmid hm hl hr hle hrd => by
        obtain ⟨vals, h_ev', h_rel⟩ :=
          h_op.target ρt sM S1 reg resolved permsR ext T output pmid h_ev h_res h_wf hm hl hr hle hrd
        exact ⟨vals, id, h_ev', fun _ _ _ _ _ h => h, rfl, h_rel⟩)
      h_code
  refine ⟨ρt, n, s3, sM.mem, perms', vals, TagRenameIncr.refl ρt, h_wf, h_ost, h_runT,
    ?_, ?_, by rw [h_g]; exact h_ps, by rw [h_g]; exact h_tb, by rw [h_mem3]; exact h_mem,
    by rw [h_mem3]; exact h_alloc, h_pc3, ?_, h_rel⟩
  · rw [h_run]; show csA.nextReg ≤ _ + 1; omega
  · exact LocalBindingSimB.prm_congr (LocalBindingSimB.of_frame h_lbs h_prb h_fr) h_prmR
  · rw [h_run]
    exact StoreStepB.rstore compProg _ _ dstL _ vals h_ld (show _ < _ + 1 by omega)

/-! ## Nested fields: congruence -/

theorem ValuePkgB.congr {Γ : Ctx} {L : mirlite.LayEnv Γ} {compProg : oseair.Prog}
    {dstL : BLayout} {τ : LayoutTy} {r1 r2 : RExpr Γ τ}
    (h_eval : ∀ sM, mirlite.evalRExpr MSB L sM dstL r1 = mirlite.evalRExpr MSB L sM dstL r2)
    (h_run : ∀ cs, CheckedCompilerM.run (compileRExprPreChecked L dstL r1) cs
      = CheckedCompilerM.run (compileRExprPreChecked L dstL r2) cs)
    (h_val : ∀ cs p2, CheckedCompilerM.value (compileRExprPreChecked L dstL r2) cs = .ok p2 →
      ∃ p1, CheckedCompilerM.value (compileRExprPreChecked L dstL r1) cs = .ok p1 ∧
        (∀ d, p1.store d = p2.store d) ∧ p1.postCleanup = p2.postCleanup)
    (h : ValuePkgB compProg L dstL r2) : ValuePkgB compProg L dstL r1 := by
  intro ρt sM sA csA h_wf h_tbd h_lbs h_prb h_mem h_alloc h_psim h_pc h_unmap output h_ev
  rw [h_eval] at h_ev
  obtain ⟨mkStore, p2, h_v2, h_st2, h_po2, h_prm2, h_rest⟩ :=
    h ρt sM sA csA h_wf h_tbd h_lbs h_prb h_mem h_alloc h_psim h_pc h_unmap output h_ev
  obtain ⟨p1, h_v1, h_st, h_po⟩ := h_val csA p2 h_v2
  refine ⟨mkStore, p1, h_v1, fun d => (h_st d).trans (h_st2 d), h_po.trans h_po2,
    by rw [h_run]; exact h_prm2, fun hc => ?_⟩
  rw [h_run] at hc ⊢
  exact h_rest hc



theorem readRhsPre_assoc {Γ : Ctx} {L : mirlite.LayEnv Γ} {dstL : BLayout} {ρ σ τ τr : LayoutTy}
    {rhs1 rhs2 : RExpr Γ τr} (b : Place Γ ρ) (q : PathTo ρ σ) (p : PathTo σ τ)
    (mk : Register → oseair.Rhs) (post : Register → List oseair.Instr)
    (ev1 : (srcRes : PtrResult) → PlaceToRegEvidence L RefKind.Shared (.proj (.proj b q) p) srcRes →
      (dstPtr : Register) → RExprToEvidence L dstPtr rhs1)
    (ev2 : (srcRes : PtrResult) → PlaceToRegEvidence L RefKind.Shared (.proj b (q.append p)) srcRes →
      (dstPtr : Register) → RExprToEvidence L dstPtr rhs2) (cs : CompilerState) :
    CheckedCompilerM.run (readRhsPre L dstL rhs1 (.proj (.proj b q) p) mk post ev1) cs
      = CheckedCompilerM.run (readRhsPre L dstL rhs2 (.proj b (q.append p)) mk post ev2) cs ∧
    ∀ p2, CheckedCompilerM.value (readRhsPre L dstL rhs2 (.proj b (q.append p)) mk post ev2) cs = .ok p2 →
      ∃ p1, CheckedCompilerM.value (readRhsPre L dstL rhs1 (.proj (.proj b q) p) mk post ev1) cs = .ok p1 ∧
        (∀ d, p1.store d = p2.store d) ∧ p1.postCleanup = p2.postCleanup := by
  obtain ⟨h_run, h_val⟩ := placeToReg_assoc (L := L) RefKind.Shared b q p cs
  cases h1 : CheckedCompilerM.value (placeToRegChecked L RefKind.Shared (.proj (.proj b q) p)) cs with
  | ok o1 =>
      cases h2 : CheckedCompilerM.value (placeToRegChecked L RefKind.Shared (.proj b (q.append p))) cs with
      | ok o2 =>
          rw [h1, h2] at h_val
          simp only [Except.map, Except.ok.injEq] at h_val
          obtain ⟨r1, p1, v1, s1, c1⟩ := readRhsPre_shapeG (dstL := dstL) (rhs := rhs1) (mk := mk)
            (post := post) (ev := ev1) h1
          obtain ⟨r2, p2, v2, s2, c2⟩ := readRhsPre_shapeG (dstL := dstL) (rhs := rhs2) (mk := mk)
            (post := post) (ev := ev2) h2
          rw [r1, r2, h_run, h_val]
          refine ⟨rfl, fun p2' h2' => ?_⟩
          rw [v2] at h2'
          cases h2'
          exact ⟨p1, v1, fun d => by rw [s1, s2, h_run], by rw [c1, c2]⟩
      | error e => rw [h1, h2] at h_val; simp [Except.map] at h_val
  | error e =>
      cases h2 : CheckedCompilerM.value (placeToRegChecked L RefKind.Shared (.proj b (q.append p))) cs with
      | ok o2 => rw [h1, h2] at h_val; simp [Except.map] at h_val
      | error e' =>
          rw [h1, h2] at h_val
          simp only [Except.map, Except.error.injEq] at h_val
          subst h_val
          simp only [readRhsPre, CheckedCompilerM.run_bind, CheckedCompilerM.value_bind, h1, h2, h_run]
          exact ⟨by first | rfl | trivial, fun p2 h => by cases h⟩

/-! ## Operands: a chain, a field of one, a nested field -/

inductive LeafSrcB {Γ : Ctx} : {τ : LayoutTy} → Place Γ τ → Prop
  | chain {τ : LayoutTy} {p : Place Γ τ} : ChainB p → LeafSrcB p
  | field {ρ τ : LayoutTy} {b : Place Γ ρ} (f : PathTo ρ τ) : ChainB b → LeafSrcB (.proj b f)
  | nested {ρ σ τ : LayoutTy} {b : Place Γ ρ} {q : PathTo ρ σ} {p : PathTo σ τ} :
      LeafSrcB (.proj b (q.append p)) → LeafSrcB (.proj (.proj b q) p)

/-- One wrapper for every one-leaf rvalue `F p` compiled as
    `readRhsPre … (mk p) post`: a chain operand by its core package, a field
    of a chain at offset zero by the same core (the field lowers as its
    base), at a nonzero offset by the op's bracket package, and a nested
    field by reassociation. -/
theorem leaf_pkgL {Γ : Ctx} {L : mirlite.LayEnv Γ} {compProg : oseair.Prog} {dstL : BLayout}
    {σ τr : LayoutTy} (F : Place Γ σ → RExpr Γ τr) (mk : Place Γ σ → Register → oseair.Rhs)
    (post : Register → List oseair.Instr)
    (ev : (p : Place Γ σ) → (srcRes : PtrResult) → PlaceToRegEvidence L RefKind.Shared p srcRes →
      (dstPtr : Register) → RExprToEvidence L dstPtr (F p))
    (h_pre : ∀ p, compileRExprPreChecked L dstL (F p) = readRhsPre L dstL (F p) p (mk p) post (ev p))
    (h_mk : ∀ {ρ σ' : LayoutTy} (b : Place Γ ρ) (q : PathTo ρ σ') (p : PathTo σ' σ),
      mk (.proj (.proj b q) p) = mk (.proj b (q.append p)))
    (h_eval : ∀ {ρ σ' : LayoutTy} (b : Place Γ ρ) (q : PathTo ρ σ') (p : PathTo σ' σ) sM,
      mirlite.evalRExpr MSB L sM dstL (F (.proj (.proj b q) p))
        = mirlite.evalRExpr MSB L sM dstL (F (.proj b (q.append p))))
    (h_core : ∀ p, LowersB L compProg p → CompilesB L p → ValuePkgB compProg L dstL (F p))
    (h_off : ∀ {ρ : LayoutTy} (b : Place Γ ρ) (f : PathTo ρ σ),
      (∀ (σ' : LayoutTy) (bb : Place Γ σ') (q : PathTo σ' ρ), b = bb.proj q → False) →
      pathOffset L b f ≠ 0 → LowersB L compProg b → CompilesB L b →
      (mirlite.leafKind (mirlite.placeLayout L (.proj b f))).size = placeSize L (.proj b f) →
      ValuePkgB compProg L dstL (F (.proj b f)))
    (hWF : PtrPlacesWF L)
    (h_len : ∀ p : Place Γ σ,
      (mirlite.leafKind (mirlite.placeLayout L p)).size = (mirlite.placeLayout L p).size)
    (src : Place Γ σ) (h : LeafSrcB src) : ValuePkgB compProg L dstL (F src) := by
  cases h with
  | chain hc => exact h_core _ (chainB_lowers hWF hc) (chainB_compilesB hc)
  | field f hb =>
      rename_i ρ b
      have h_np := ChainB.not_proj hb
      by_cases h0 : pathOffset L b f = 0
      · exact h_core _ (proj_zero_lowers f h_np h0 (chainB_lowers hWF hb))
          (proj_zero_compiles f h_np h0 (chainB_compilesB hb))
      · exact h_off b f h_np h0 (chainB_lowers hWF hb) (chainB_compilesB hb) (h_len _)
  | nested hn =>
      rename_i ρ' σ' b q p
      have ih := leaf_pkgL F mk post ev h_pre h_mk h_eval h_core h_off hWF h_len
        (.proj b (q.append p)) hn
      have h_as := readRhsPre_assoc (L := L) (dstL := dstL) (rhs1 := F (.proj (.proj b q) p))
        (rhs2 := F (.proj b (q.append p))) b q p (mk (.proj b (q.append p))) post (ev _) (ev _)
      refine ValuePkgB.congr (fun sM => h_eval b q p sM) (fun cs => ?_) (fun cs => ?_) ih
      · rw [h_pre, h_pre, h_mk]; exact (h_as cs).1
      · rw [h_pre, h_pre, h_mk]; exact (h_as cs).2
termination_by src.depth
decreasing_by all_goals (subst_vars; simp_all [Place.depth]; try omega)

/-- A read-only one-leaf op: its core package and its bracket package. -/
theorem ro_pkgL {Γ : Ctx} {L : mirlite.LayEnv Γ} {compProg : oseair.Prog} {dstL : BLayout}
    {σ τr : LayoutTy} (F : Place Γ σ → RExpr Γ τr) (mk : Place Γ σ → Register → oseair.Rhs)
    (ev : (p : Place Γ σ) → (srcRes : PtrResult) → PlaceToRegEvidence L RefKind.Shared p srcRes →
      (dstPtr : Register) → RExprToEvidence L dstPtr (F p))
    (h_pre : ∀ p, compileRExprPreChecked L dstL (F p)
      = readRhsPre L dstL (F p) p (mk p) (fun _ => []) (ev p))
    (h_mk : ∀ {ρ σ' : LayoutTy} (b : Place Γ ρ) (q : PathTo ρ σ') (p : PathTo σ' σ),
      mk (.proj (.proj b q) p) = mk (.proj b (q.append p)))
    (h_eval : ∀ {ρ σ' : LayoutTy} (b : Place Γ ρ) (q : PathTo ρ σ') (p : PathTo σ' σ) sM,
      mirlite.evalRExpr MSB L sM dstL (F (.proj (.proj b q) p))
        = mirlite.evalRExpr MSB L sM dstL (F (.proj b (q.append p))))
    (h_leafop : ∀ p, LeafOpB L dstL (F p) p (mk p)) (h_ro : ∀ p, ReadOnlyOpB L dstL (F p) p (mk p))
    (hWF : PtrPlacesWF L)
    (h_len : ∀ p : Place Γ σ,
      (mirlite.leafKind (mirlite.placeLayout L p)).size = (mirlite.placeLayout L p).size)
    (src : Place Γ σ) (h : LeafSrcB src) : ValuePkgB compProg L dstL (F src) :=
  leaf_pkgL F mk (fun _ => []) ev h_pre h_mk h_eval
    (fun p hl hc => leaf_pkg_core (ev := ev p) hl hc (h_leafop p) (h_pre p))
    (fun _ _ h_np h0 hl hc h_l => leaf_pkg_projoff (ev := ev _) h_np h0 hl hc h_l (h_ro _) (h_pre _))
    hWF h_len src h

theorem ptrCast_pkgL {Γ : Ctx} {L : mirlite.LayEnv Γ} {compProg : oseair.Prog}
    (hWF : PtrPlacesWF L) (hLeaf : LeafWF L) (dstL : BLayout) {σ τ : LayoutTy}
    (src : Place Γ (LayoutTy.PtrL σ)) (h : LeafSrcB src) :
    ValuePkgB compProg L dstL (RExpr.ptrCast (τ := τ) src) :=
  ro_pkgL (fun p => RExpr.ptrCast (τ := τ) p)
    (fun p => oseair.Rhs.Load (leafLayout (mirlite.leafKind (mirlite.placeLayout L p))))
    (fun p srcRes evd _ => RExprToEvidence.ptrCast p srcRes evd) (fun _ => rfl)
    (fun _ _ _ => by simp only [placeLayout_assoc])
    (fun _ _ _ _ => by simp only [mirlite.evalRExpr, mirlite.readCell, placeLayout_assoc,
      resolvePlaceAcc_assoc])
    (fun p => ptrCast_leafop dstL p) (fun p => ptrCast_ro dstL p) hWF (fun p => hLeaf.1 p) src h

theorem ptrOffset_pkgL {Γ : Ctx} {L : mirlite.LayEnv Γ} {compProg : oseair.Prog}
    (hWF : PtrPlacesWF L) (hLeaf : LeafWF L) (dstL : BLayout) {σ τ : LayoutTy}
    (src : Place Γ (LayoutTy.PtrL σ)) (h : LeafSrcB src) (delta : Int) :
    ValuePkgB compProg L dstL (RExpr.ptrOffset (τ := τ) src delta) :=
  ro_pkgL (fun p => RExpr.ptrOffset (τ := τ) p delta)
    (fun p r => oseair.Rhs.PtrOffset (mirlite.leafKind (mirlite.placeLayout L p)) r
      (delta * ((mirlite.pointeeLayout L p).size : Int)))
    (fun p srcRes evd _ => RExprToEvidence.ptrOffset p delta srcRes evd) (fun _ => rfl)
    (fun _ _ _ => by simp only [mirlite.pointeeLayout, placeLayout_assoc])
    (fun _ _ _ _ => by simp only [mirlite.evalRExpr, mirlite.readCell, placeLayout_assoc,
      resolvePlaceAcc_assoc, mirlite.pointeeLayout])
    (fun p => ptrOffset_leafop dstL p delta) (fun p => ptrOffset_ro dstL p delta) hWF
    (fun p => hLeaf.1 p) src h

theorem fromExposed_pkgL {Γ : Ctx} {L : mirlite.LayEnv Γ} {compProg : oseair.Prog}
    (hWF : PtrPlacesWF L) (hLeaf : LeafWF L) (dstL : BLayout) {τ : LayoutTy}
    (src : Place Γ (LayoutTy.IntL tN)) (h : LeafSrcB src) :
    ValuePkgB compProg L dstL (RExpr.fromExposed (τ := τ) src) :=
  ro_pkgL (fun p => RExpr.fromExposed (τ := τ) p)
    (fun p => oseair.Rhs.FromExposed (mirlite.leafKind (mirlite.placeLayout L p)))
    (fun p srcRes evd _ => RExprToEvidence.fromExposed p srcRes evd) (fun _ => rfl)
    (fun _ _ _ => by simp only [placeLayout_assoc])
    (fun _ _ _ _ => by simp only [mirlite.evalRExpr, mirlite.readCell, placeLayout_assoc,
      resolvePlaceAcc_assoc])
    (fun p => fromExposed_leafop dstL p) (fun p => fromExposed_ro dstL p) hWF
    (fun p => hLeaf.2 p) src h

end obseq3.proof
