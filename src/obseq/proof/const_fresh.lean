import obseq.proof.state_helpers
import obseq.proof.struct_init_common

/-!
# `obseq.proof.const_fresh`

Local compiler-correctness lemmas for the fresh-destination word-constant
fragment.

As in `const_existing`, this is the paper-level `ConstOp(n)` case. The only
freshness-specific work is extending the source environment and the compiler
place map with the newly allocated base/register pair. Fresh allocation into a
proper projection path is still intentionally out of scope: this fragment
remains base-only because the runtime/compiler semantics still reject fresh
sub-path writes.
-/

namespace obseq.proof

open obseq
open obseq.mirlite
open obseq.oseair hiding State Result
open obseq.compile
open scoped obseq.notation

structure ConstFreshCtx where
  base : Word
  n : Word
  cs : CompilerState
  h_instrs : CompilerEmpty cs
  h_absent : BaseAbsent cs base

namespace ConstFreshCtx

def reg (ctx : ConstFreshCtx) : Register :=
  Register.R ctx.cs.nextReg

def postPlaceMap (ctx : ConstFreshCtx) : PlaceMap :=
  (ctx.base, (ctx.reg, LayoutTy.NatL)) :: ctx.cs.placeMap

def stmt (ctx : ConstFreshCtx) : mirlite.Stmt :=
  place(ctx.base) ::= const ctx.n

def compiled (ctx : ConstFreshCtx) : oseair.Prog :=
  (compileStmt ctx.cs ctx.stmt).instrs

theorem instrs_nil (ctx : ConstFreshCtx) : ctx.cs.instrs = [] :=
  ctx.h_instrs

end ConstFreshCtx

namespace ConstFresh

@[simp] theorem compiled_eq
  (ctx : ConstFreshCtx) :
  ctx.compiled =
    [oseair.Instr.Assgn ctx.reg (oseair.Rhs.Alloc TyVal.NatTy),
     oseair.Instr.CStore TyVal.NatTy [oseair.Val.Dat ctx.n] ctx.reg] := by
  have h_place :
      placeToReg ctx.cs { base := ctx.base, path := [] } mirlite.RefKind.Mut (some LayoutTy.NatL) =
        { reg := ctx.reg, layout := LayoutTy.NatL, cleanup := [],
          cs :=
            { nextReg := ctx.cs.nextReg + 1,
              placeMap := (ctx.base, (ctx.reg, LayoutTy.NatL)) :: ctx.cs.placeMap,
              instrs := ctx.cs.instrs ++ [oseair.Instr.Assgn ctx.reg (oseair.Rhs.Alloc TyVal.NatTy)] } } := by
    unfold placeToReg ConstFreshCtx.reg
    rw [ctx.h_absent]
    simp [freshReg, emit, setPlace, layoutToTyVal, typeSize]
  unfold ConstFreshCtx.compiled ConstFreshCtx.stmt
  simp [compileStmt, obseq.notation.basePlace, obseq.notation.placeExpr,
    obseq.notation.mkPlace, obseq.notation.constRhs,
    h_place, emit, cleanupInstrs, List.map, ctx.instrs_nil, layoutToTyVal, typeSize]

theorem osea_run_ok
  (ctx : ConstFreshCtx)
  (s_osea : oseair.State)
  (prog_osea : oseair.Prog)
  (tag : Word)
  (ap2 ap3 : AccessPerms)
  (h_start : StartsAt prog_osea s_osea.pc ctx.compiled)
  (h_own : sb_own s_osea.ap s_osea.mem.addrStart = (SBResult.Ok ap2, tag))
  (h_use : sb_use_mb ap2 s_osea.mem.addrStart tag = SBResult.Ok ap3) :
  oseair.runN 2 s_osea prog_osea =
    oseair.Result.Ok
      { s_osea with
        reg := s_osea.reg.insert ctx.reg
          (TyVal.PTy, [oseair.Val.Ptr s_osea.mem.addrStart 0 (blockSize LayoutTy.NatL) tag]),
        mem := oseair.writeWordSeq
          { s_osea.mem with addrStart := s_osea.mem.addrStart + blockSize LayoutTy.NatL }
          s_osea.mem.addrStart [oseair.Val.Dat ctx.n],
        ap := ap3,
        pc := s_osea.pc + 2 } := by
  rw [compiled_eq ctx] at h_start
  simpa using
    osea_run_alloc_cstore_embedded_ok
      s_osea prog_osea LayoutTy.NatL [oseair.Val.Dat ctx.n] ctx.reg tag ap2 ap3 h_start
      (by decide : 0 < blockSize LayoutTy.NatL) h_own h_use

theorem mirlite_step_inv
  (ctx : ConstFreshCtx)
  (s_mir : mirlite.State)
  (s_mir_next : mirlite.State)
  (prog_mir : mirlite.Prog)
  (h_env : s_mir.env.lookup ctx.base = none)
  (h_start : StartsAt prog_mir s_mir.pc [ctx.stmt])
  (h_step : mirlite.step s_mir prog_mir = mirlite.Result.Ok s_mir_next) :
  ∃ tag ap2 ap3,
    sb_own s_mir.ap s_mir.mem.addrStart = (SBResult.Ok ap2, tag) ∧
    sb_use_mb ap2 s_mir.mem.addrStart tag = SBResult.Ok ap3 ∧
    s_mir_next =
      { s_mir with
        env := s_mir.env.insert ctx.base (s_mir.mem.addrStart, TyVal.NatTy, tag),
        mem := mirlite.writeWordSeq
          { s_mir.mem with addrStart := s_mir.mem.addrStart + blockSize LayoutTy.NatL }
          s_mir.mem.addrStart [mirlite.MemValue.Val ctx.n],
        ap := ap3,
        pc := s_mir.pc + 1 } := by
  have h_stmt_mir : prog_mir.get? s_mir.pc = some ctx.stmt := StartsAt.singleton h_start
  rcases List.get?_eq_some_iff.mp h_stmt_mir with ⟨h_pc_mir, h_get_mir⟩
  unfold mirlite.step at h_step
  rw [dif_pos h_pc_mir, h_get_mir] at h_step
  cases h_own : sb_own s_mir.ap s_mir.mem.addrStart with
  | mk ownRes tag =>
      cases ownRes with
      | Err _ =>
          simp [ConstFreshCtx.stmt, obseq.notation.basePlace, obseq.notation.placeExpr,
            obseq.notation.mkPlace, obseq.notation.constRhs,
            mirlite.stepAssignConst, mirlite.finishPlaceAssign, mirlite.allocateBaseAndWrite,
            h_env, h_own, mirlite.allocate, blockSize, mirlite.writeWordSeq, layoutToTyVal] at h_step
      | Ok ap2 =>
          cases h_use : sb_use_mb ap2 s_mir.mem.addrStart tag with
          | Err _ =>
              simp [ConstFreshCtx.stmt, obseq.notation.basePlace, obseq.notation.placeExpr,
                obseq.notation.mkPlace, obseq.notation.constRhs,
                mirlite.stepAssignConst, mirlite.finishPlaceAssign, mirlite.allocateBaseAndWrite,
                h_env, h_own, h_use, mirlite.allocate, blockSize, mirlite.writeWordSeq, layoutToTyVal] at h_step
          | Ok ap3 =>
              refine ⟨tag, ap2, ap3, rfl, h_use, ?_⟩
              simpa [ConstFreshCtx.stmt, obseq.notation.basePlace, obseq.notation.placeExpr,
                obseq.notation.mkPlace, obseq.notation.constRhs,
                mirlite.stepAssignConst, mirlite.finishPlaceAssign, mirlite.allocateBaseAndWrite,
                h_env, h_own, h_use, mirlite.allocate, blockSize, mirlite.writeWordSeq, layoutToTyVal]
                using h_step.symm

variable (ctx : ConstFreshCtx)
variable (s_mir : mirlite.State)
variable (s_osea : oseair.State)
variable (s_mir_next : mirlite.State)
variable (ρa : AddrRenaming)
variable (ρt : TagRenaming)

theorem simulation
  (prog_mir : mirlite.Prog)
  (prog_osea : oseair.Prog)
  (h_sim : StateSim ctx.cs.placeMap ρa ρt s_mir s_osea)
  (h_env : s_mir.env.lookup ctx.base = none)
  (h_mir_start : StartsAt prog_mir s_mir.pc [ctx.stmt])
  (h_osea_start : StartsAt prog_osea s_osea.pc ctx.compiled)
  (h_mir_step : mirlite.step s_mir prog_mir = mirlite.Result.Ok s_mir_next) :
  ∃ ρa' ρt' s_osea_next,
    StepStar s_osea prog_osea s_osea_next ∧
    StateSim ctx.postPlaceMap ρa' ρt' s_mir_next s_osea_next := by
  let ⟨tag_m, ap2_m, ap3_m, h_own, h_use, h_next_full⟩ :=
    mirlite_step_inv
      ctx s_mir s_mir_next prog_mir h_env h_mir_start h_mir_step
  let ρa' := extendAddrRenameMap ρa s_mir.mem.addrStart s_osea.mem.addrStart
  let ⟨tag_o, ap2_o, h_target_own, h_sb2⟩ :=
    sb_own_sim_extend
      (addr_o := s_osea.mem.addrStart)
      (h_sim := StateSim.sb h_sim)
      h_own
  let ρt' := extendTagRenameMap ρt tag_m tag_o
  have h_new_addr : ρa' s_mir.mem.addrStart = some s_osea.mem.addrStart := by
    simp [ρa']
  have h_new_tag : ρt' tag_m = some tag_o := by
    simp [ρt']
  let ⟨ap3_o, h_target_use, h_sb3⟩ :=
    sb_use_mb_sim_ok
      (ρa := ρa')
      (ρt := ρt')
      (h_sim := h_sb2)
      h_new_addr h_new_tag h_use
  let s_osea_post :=
    { s_osea with
      reg := s_osea.reg.insert ctx.reg
        (TyVal.PTy, [oseair.Val.Ptr s_osea.mem.addrStart 0 (blockSize LayoutTy.NatL) tag_o]),
      mem := oseair.writeWordSeq
        { s_osea.mem with addrStart := s_osea.mem.addrStart + blockSize LayoutTy.NatL }
        s_osea.mem.addrStart [oseair.Val.Dat ctx.n],
      ap := ap3_o,
      pc := s_osea.pc + 2 }
  have h_target_run :
      oseair.runN 2 s_osea prog_osea = oseair.Result.Ok s_osea_post := by
    simpa [s_osea_post] using
      osea_run_ok
        ctx s_osea prog_osea tag_o ap2_o ap3_o h_osea_start h_target_own h_target_use
  refine ⟨ρa', ρt', s_osea_post, StepStar.of_runN_ok h_target_run, ?_⟩
  rw [h_next_full]
  simpa [ConstFreshCtx.postPlaceMap, ConstFreshCtx.reg, s_osea_post] using
    state_sim_alloc_write
      (π := ctx.cs.placeMap)
      (ρa := ρa)
      (ρa' := ρa')
      (ρt := ρt)
      (ρt' := ρt')
      (base := ctx.base)
      (reg := ctx.reg)
      (layout := LayoutTy.NatL)
      (freshAddr_m := s_mir.mem.addrStart)
      (freshAddr_o := s_osea.mem.addrStart)
      (tag_m := tag_m)
      (tag_o := tag_o)
      (ap_m' := ap3_m)
      (ap_o' := ap3_o)
      (pc_mir := s_mir.pc + 1)
      (pc_osea := s_osea.pc + 2)
      (vals_mir := [mirlite.MemValue.Val ctx.n])
      (vals_osea := [oseair.Val.Dat ctx.n])
      h_sim
      rfl
      rfl
      (by
        simpa [ConstFreshCtx.reg] using (alloc_fresh_reg (cs := ctx.cs)))
      h_sb3
      (mem_vals_eq_word ctx.n)
      rfl

end ConstFresh

end obseq.proof
