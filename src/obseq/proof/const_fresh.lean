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

variable {A_m : mirlite.AllocatorSpec} {A_o : oseair.AllocatorSpec}

structure ConstFreshCtx where
  base : Word
  n : Word
  cs : CompilerState
  h_regs_below : PlaceMapRegsBelowNextReg cs
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
    simp [freshReg, emit, setPlace, layoutToTyVal]
  unfold ConstFreshCtx.compiled ConstFreshCtx.stmt
  simp [compileStmt, obseq.notation.basePlace, obseq.notation.placeExpr,
    obseq.notation.mkPlace, obseq.notation.constRhs,
    h_place, emit, cleanupInstrs, ctx.instrs_nil]

theorem osea_run_ok
  (ctx : ConstFreshCtx)
  (s_osea : oseair.State)
  (prog_osea : oseair.Prog)
  (allocBase : Word)
  (allocMem : oseair.Mem)
  (tag : Word)
  (ap2 ap3 : AccessPerms)
  (h_start : StartsAt prog_osea s_osea.pc ctx.compiled)
  (h_alloc_pair : A_o.alloc s_osea.mem (blockSize LayoutTy.NatL) = (allocBase, allocMem))
  (h_own : sb_own s_osea.ap allocBase = (SBResult.Ok ap2, tag))
  (h_use : sb_use_mb ap2 allocBase tag = SBResult.Ok ap3) :
  oseair.runNWith A_o 2 s_osea prog_osea =
    oseair.Result.Ok
      { s_osea with
        reg := s_osea.reg.insert ctx.reg
          (TyVal.PTy, [oseair.Val.Ptr allocBase 0 (blockSize LayoutTy.NatL) tag]),
        mem := oseair.writeWordSeq allocMem allocBase [oseair.Val.Dat ctx.n],
        ap := ap3,
        pc := s_osea.pc + 2 } := by
  rw [compiled_eq ctx] at h_start
  simpa using
    osea_run_alloc_cstore_embedded_ok
      s_osea prog_osea LayoutTy.NatL [oseair.Val.Dat ctx.n] ctx.reg allocBase allocMem tag ap2 ap3 h_start
      (by decide : 0 < blockSize LayoutTy.NatL) h_alloc_pair h_own h_use

theorem mirlite_step_inv
  (ctx : ConstFreshCtx)
  (s_mir : mirlite.State)
  (s_mir_next : mirlite.State)
  (prog_mir : mirlite.Prog)
  (h_env : s_mir.env.lookup ctx.base = none)
  (h_start : StartsAt prog_mir s_mir.pc [ctx.stmt])
  (h_step : mirlite.stepWith A_m s_mir prog_mir = mirlite.Result.Ok s_mir_next) :
  ∃ freshAddr allocMem tag ap2 ap3,
    A_m.alloc s_mir.mem (typeSize TyVal.NatTy) = (freshAddr, allocMem) ∧
    allocMem.mMap = s_mir.mem.mMap ∧
    sb_own s_mir.ap freshAddr = (SBResult.Ok ap2, tag) ∧
    sb_use_mb ap2 freshAddr tag = SBResult.Ok ap3 ∧
    s_mir_next =
      { s_mir with
        env := s_mir.env.insert ctx.base (freshAddr, TyVal.NatTy, tag),
        mem := mirlite.writeWordSeq allocMem freshAddr [mirlite.MemValue.Val ctx.n],
        ap := ap3,
        pc := s_mir.pc + 1 } := by
  have h_stmt_mir : prog_mir.get? s_mir.pc = some ctx.stmt := StartsAt.singleton h_start
  rcases List.get?_eq_some_iff.mp h_stmt_mir with ⟨h_pc_mir, h_get_mir⟩
  let freshAddr := (A_m.alloc s_mir.mem (typeSize TyVal.NatTy)).1
  let allocMem := (A_m.alloc s_mir.mem (typeSize TyVal.NatTy)).2
  have h_alloc_pair :
      A_m.alloc s_mir.mem (typeSize TyVal.NatTy) = (freshAddr, allocMem) := by
    simp [freshAddr, allocMem]
  have h_alloc_mMap : allocMem.mMap = s_mir.mem.mMap := by
    simpa [h_alloc_pair] using A_m.alloc_mMap_eq s_mir.mem (typeSize TyVal.NatTy)
  unfold mirlite.stepWith at h_step
  rw [dif_pos h_pc_mir, h_get_mir] at h_step
  cases h_own : sb_own s_mir.ap freshAddr with
  | mk ownRes tag =>
      cases ownRes with
      | Err _ =>
          simp [ConstFreshCtx.stmt, obseq.notation.basePlace, obseq.notation.placeExpr,
            obseq.notation.mkPlace, obseq.notation.constRhs,
            mirlite.stepAssignConstWith, mirlite.finishPlaceAssignWith, mirlite.allocateBaseAndWriteWith,
            h_env, h_alloc_pair, h_own] at h_step
      | Ok ap2 =>
          cases h_use : sb_use_mb ap2 freshAddr tag with
          | Err _ =>
              simp [ConstFreshCtx.stmt, obseq.notation.basePlace, obseq.notation.placeExpr,
                obseq.notation.mkPlace, obseq.notation.constRhs,
                mirlite.stepAssignConstWith, mirlite.finishPlaceAssignWith, mirlite.allocateBaseAndWriteWith,
                h_env, h_alloc_pair, h_own, h_use] at h_step
          | Ok ap3 =>
              refine ⟨freshAddr, allocMem, tag, ap2, ap3, h_alloc_pair, h_alloc_mMap, h_own, h_use, ?_⟩
              simpa [ConstFreshCtx.stmt, obseq.notation.basePlace, obseq.notation.placeExpr,
                obseq.notation.mkPlace, obseq.notation.constRhs,
                mirlite.stepAssignConstWith, mirlite.finishPlaceAssignWith, mirlite.allocateBaseAndWriteWith,
                h_env, h_alloc_pair, h_own, h_use]
                using h_step.symm

variable (ctx : ConstFreshCtx)
variable (s_mir : mirlite.State)
variable (s_osea : oseair.State)
variable (s_mir_next : mirlite.State)
variable (ρa : AddrRenameMap)
variable (ρt : TagRenameMap)
variable {ptr_sim : PtrSimPred}

theorem simulation
  (prog_mir : mirlite.Prog)
  (prog_osea : oseair.Prog)
  (h_sim : StateSim ctx.cs.placeMap ρa ρt s_mir s_osea ptr_sim)
  (h_noninterference : TargetNonInterference ρa s_osea)
  (h_source_below : SourceBlocksBelowAddrStart ctx.cs.placeMap s_mir)
  (h_tag_fresh : ∀ tag, s_mir.ap.NextTag ≤ tag → ρt tag = none)
  (h_source_alloc_base :
    (A_m.alloc s_mir.mem (typeSize TyVal.NatTy)).1 = s_mir.mem.addrStart)
  (h_env : s_mir.env.lookup ctx.base = none)
  (h_mir_start : StartsAt prog_mir s_mir.pc [ctx.stmt])
  (h_osea_start : StartsAt prog_osea s_osea.pc ctx.compiled)
  (h_mir_step : mirlite.stepWith A_m s_mir prog_mir = mirlite.Result.Ok s_mir_next) :
  ∃ ρa' ρt' s_osea_next,
    StepStarWith oseair.bumpAllocator s_osea prog_osea s_osea_next ∧
    StateSim ctx.postPlaceMap ρa' ρt' s_mir_next s_osea_next ptr_sim ∧
    TargetNonInterference ρa' s_osea_next ∧
    s_osea_next.pc = s_osea.pc + ctx.compiled.length := by
  let ⟨freshAddr_m, allocMem_m, tag_m, ap2_m, ap3_m, h_alloc_pair_m, h_alloc_mMap_m, h_own, h_use, h_next_full⟩ :=
    mirlite_step_inv
      ctx s_mir s_mir_next prog_mir h_env h_mir_start h_mir_step
  have h_alloc_base_m : freshAddr_m = s_mir.mem.addrStart := by
    have h_fst := congrArg Prod.fst h_alloc_pair_m
    exact h_fst.symm.trans h_source_alloc_base
  have h_tag_fresh' : ∀ tag, tag_m ≤ tag → ρt tag = none := by
    have h_tag_eq : tag_m = s_mir.ap.NextTag := sb_own_tag_eq_nextTag h_own
    simpa [h_tag_eq] using h_tag_fresh
  let allocBase_o := (oseair.bumpAllocator.alloc s_osea.mem (blockSize LayoutTy.NatL)).1
  let allocMem_o := (oseair.bumpAllocator.alloc s_osea.mem (blockSize LayoutTy.NatL)).2
  have h_alloc_pair :
      oseair.bumpAllocator.alloc s_osea.mem (blockSize LayoutTy.NatL) =
        (allocBase_o, allocMem_o) := by
    simp [allocBase_o, allocMem_o]
  have h_alloc_mMap_o : allocMem_o.mMap = s_osea.mem.mMap := by
    simpa [h_alloc_pair] using
      oseair.AllocatorSpec.alloc_mMap_eq
        (A := oseair.bumpAllocator) s_osea.mem (blockSize LayoutTy.NatL)
  have h_alloc_base : allocBase_o = s_osea.mem.addrStart := by
    simp [allocBase_o, oseair.bumpAllocator, oseair.allocate]
  have h_alloc_addrStart' :
      allocMem_o.addrStart = s_osea.mem.addrStart + blockSize LayoutTy.NatL := by
    simp [allocMem_o, oseair.bumpAllocator, oseair.allocate]
  obtain ⟨ρa', ρt', s_osea_next, h_steps, h_rest⟩ :=
    fresh_write_simulation (A_o := oseair.bumpAllocator) (freshAddr_m := freshAddr_m)
      h_sim h_noninterference h_source_below
      (by
        simpa [ConstFreshCtx.reg] using
          (alloc_fresh_reg_of_ge (cs := ctx.cs) ctx.h_regs_below (Nat.le_refl _)))
      h_tag_fresh' h_own h_use h_alloc_mMap_m h_alloc_base_m
      h_alloc_mMap_o h_alloc_base h_alloc_addrStart' (by decide)
      (fun tag_o ap2_o ap3_o h_target_own h_target_use => by
        simpa [allocBase_o, allocMem_o, ConstFreshCtx.reg] using
          osea_run_ok (A_o := oseair.bumpAllocator)
            ctx s_osea prog_osea allocBase_o allocMem_o tag_o ap2_o ap3_o
            h_osea_start h_alloc_pair h_target_own h_target_use)
      h_next_full (mem_vals_eq_word ctx.n) rfl
  rcases h_rest with ⟨h_sim_next, h_noninterference_next, h_pc⟩
  refine ⟨ρa', ρt', s_osea_next, h_steps, ?_, h_noninterference_next, ?_⟩
  · simpa [ConstFreshCtx.postPlaceMap, ConstFreshCtx.reg] using h_sim_next
  · simpa [compiled_eq] using h_pc

theorem simulation_structured
  (prog_mir : mirlite.Prog)
  (prog_osea : oseair.Prog)
  (h_sim : StateSim ctx.cs.placeMap ρa ρt s_mir s_osea ptr_sim)
  (h_noninterference : TargetNonInterference ρa s_osea)
  (h_source_below : SourceBlocksBelowAddrStart ctx.cs.placeMap s_mir)
  (h_tag_fresh : ∀ tag, s_mir.ap.NextTag ≤ tag → ρt tag = none)
  (h_source_alloc_base :
    (A_m.alloc s_mir.mem (typeSize TyVal.NatTy)).1 = s_mir.mem.addrStart)
  (h_env : s_mir.env.lookup ctx.base = none)
  (h_mir_start : StartsAt prog_mir s_mir.pc [ctx.stmt])
  (h_osea_start : StartsAt prog_osea s_osea.pc ctx.compiled)
  (h_mir_step : mirlite.stepWith A_m s_mir prog_mir = mirlite.Result.Ok s_mir_next) :
  ∃ freshAddr_m allocBase_o tag_m tag_o ρa' ρt' s_osea_next,
    tag_m = s_mir.ap.NextTag ∧
    ρa' = extendAddrRenameMap ρa freshAddr_m allocBase_o ∧
    ρt' = extendTagRenameMap ρt tag_m tag_o ∧
    StepStarWith oseair.bumpAllocator s_osea prog_osea s_osea_next ∧
    StateSim ctx.postPlaceMap ρa' ρt' s_mir_next s_osea_next ptr_sim ∧
    TargetNonInterference ρa' s_osea_next ∧
    s_mir_next.env = s_mir.env.insert ctx.base (freshAddr_m, TyVal.NatTy, tag_m) ∧
    s_mir_next.ap.NextTag = s_mir.ap.NextTag + 1 ∧
    s_osea_next.pc = s_osea.pc + ctx.compiled.length := by
  let ⟨freshAddr_m, allocMem_m, tag_m, ap2_m, ap3_m, h_alloc_pair_m, h_alloc_mMap_m, h_own, h_use, h_next_full⟩ :=
    mirlite_step_inv
      ctx s_mir s_mir_next prog_mir h_env h_mir_start h_mir_step
  have h_alloc_base_m : freshAddr_m = s_mir.mem.addrStart := by
    have h_fst := congrArg Prod.fst h_alloc_pair_m
    exact h_fst.symm.trans h_source_alloc_base
  have h_tag_fresh' : ∀ tag, tag_m ≤ tag → ρt tag = none := by
    have h_tag_eq : tag_m = s_mir.ap.NextTag := sb_own_tag_eq_nextTag h_own
    simpa [h_tag_eq] using h_tag_fresh
  let allocBase_o := (oseair.bumpAllocator.alloc s_osea.mem (blockSize LayoutTy.NatL)).1
  let allocMem_o := (oseair.bumpAllocator.alloc s_osea.mem (blockSize LayoutTy.NatL)).2
  have h_alloc_pair :
      oseair.bumpAllocator.alloc s_osea.mem (blockSize LayoutTy.NatL) =
        (allocBase_o, allocMem_o) := by
    simp [allocBase_o, allocMem_o]
  have h_alloc_mMap_o : allocMem_o.mMap = s_osea.mem.mMap := by
    simpa [allocBase_o, allocMem_o] using
      oseair.AllocatorSpec.alloc_mMap_eq
        (A := oseair.bumpAllocator) s_osea.mem (blockSize LayoutTy.NatL)
  have h_alloc_base : allocBase_o = s_osea.mem.addrStart := by
    simp [allocBase_o, oseair.bumpAllocator, oseair.allocate]
  have h_alloc_addrStart' :
      allocMem_o.addrStart = s_osea.mem.addrStart + blockSize LayoutTy.NatL := by
    simp [allocMem_o, oseair.bumpAllocator, oseair.allocate]
  obtain ⟨tag_o, ρa', ρt', s_osea_next, h_ρa', h_ρt', h_steps, h_sim_next,
      h_noninterference_next, h_pc⟩ :=
    fresh_write_simulation_structured
      (A_o := oseair.bumpAllocator) (freshAddr_m := freshAddr_m)
      h_sim h_noninterference h_source_below
      (by
        simpa [ConstFreshCtx.reg] using
          (alloc_fresh_reg_of_ge (cs := ctx.cs) ctx.h_regs_below (Nat.le_refl _)))
      h_tag_fresh' h_own h_use h_alloc_mMap_m h_alloc_base_m
      h_alloc_mMap_o h_alloc_base h_alloc_addrStart' (by decide)
      (fun tag_o ap2_o ap3_o h_target_own h_target_use => by
        simpa [allocBase_o, allocMem_o, ConstFreshCtx.reg] using
          osea_run_ok (A_o := oseair.bumpAllocator)
            ctx s_osea prog_osea allocBase_o allocMem_o tag_o ap2_o ap3_o
            h_osea_start h_alloc_pair h_target_own h_target_use)
      h_next_full (mem_vals_eq_word ctx.n) rfl
  have h_tag_eq : tag_m = s_mir.ap.NextTag :=
    obseq.sb_own_tag_eq_nextTag h_own
  have h_ap2_next : ap2_m.NextTag = s_mir.ap.NextTag + 1 :=
    obseq.sb_own_nextTag_succ h_own
  have h_ap3_next : ap3_m.NextTag = s_mir.ap.NextTag + 1 := by
    rw [obseq.sb_use_mb_nextTag_eq h_use]
    exact h_ap2_next
  have h_env_next :
      s_mir_next.env = s_mir.env.insert ctx.base (freshAddr_m, TyVal.NatTy, tag_m) := by
    simpa [h_next_full]
  have h_nextTag_post : s_mir_next.ap.NextTag = s_mir.ap.NextTag + 1 := by
    simpa [h_next_full] using h_ap3_next
  refine ⟨freshAddr_m, allocBase_o, tag_m, tag_o, ρa', ρt', s_osea_next,
    h_tag_eq, h_ρa', h_ρt', h_steps, h_sim_next, h_noninterference_next,
    h_env_next, h_nextTag_post, ?_⟩
  simpa [compiled_eq] using h_pc

end ConstFresh

end obseq.proof
