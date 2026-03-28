import obseq.proof.state_helpers
import obseq.proof.struct_init_common

/-!
# `obseq.proof.const_existing`

Local compiler-correctness lemmas for the existing-destination word-constant
fragment.

This cluster follows the paper grammar again: `ConstOp` is word-only, so the
proved fragment here is exactly `place(base) ::= const n`.
-/

namespace obseq.proof

open obseq
open obseq.mirlite
open obseq.oseair hiding State Result
open obseq.compile
open scoped obseq.notation

structure ConstExistingCtx where
  base : Word
  reg : Register
  n : Word
  cs : CompilerState
  h_instrs : CompilerEmpty cs
  h_lookup : BaseReady cs base reg LayoutTy.NatL

namespace ConstExistingCtx

def stmt (ctx : ConstExistingCtx) : mirlite.Stmt :=
  place(ctx.base) ::= const ctx.n

def compiled (ctx : ConstExistingCtx) : oseair.Prog :=
  (compileStmt ctx.cs ctx.stmt).instrs

def mirStart (_ctx : ConstExistingCtx) (s_mir : mirlite.State) : mirlite.State :=
  { s_mir with pc := 0 }

def oseaStart (_ctx : ConstExistingCtx) (s_osea : oseair.State) : oseair.State :=
  { s_osea with pc := 0 }

def oseaPost (ctx : ConstExistingCtx)
  (s_osea : oseair.State)
  (ap' : AccessPerms)
  (addr : Word) : oseair.State :=
  { s_osea with
    ap := ap',
    mem := oseair.writeWordSeq s_osea.mem addr [oseair.Val.Dat ctx.n],
    pc := 1 }

theorem instrs_nil (ctx : ConstExistingCtx) : ctx.cs.instrs = [] :=
  ctx.h_instrs

end ConstExistingCtx

theorem ConstExistingCtx.compiled_eq
  (ctx : ConstExistingCtx) :
  ctx.compiled = [oseair.Instr.CStore TyVal.NatTy [oseair.Val.Dat ctx.n] ctx.reg] := by
  have h_place :
      placeToReg ctx.cs { base := ctx.base, path := [] } mirlite.RefKind.Mut (some LayoutTy.NatL) =
        { reg := ctx.reg, layout := LayoutTy.NatL, cleanup := [], cs := ctx.cs } := by
    unfold placeToReg
    rw [ctx.h_lookup]
    simp [layoutResolvePath]
  unfold ConstExistingCtx.compiled
  unfold ConstExistingCtx.stmt compileStmt
  simp [obseq.notation.basePlace, obseq.notation.constRhs, h_place, emit, cleanupInstrs,
    ctx.instrs_nil]

namespace ConstExisting

abbrev LocalSim
  (ctx : ConstExistingCtx)
  (ρa : AddrRenaming)
  (ρt : TagRenaming)
  (s_mir : mirlite.State)
  (s_osea : oseair.State) : Prop :=
  StateSim ctx.cs.placeMap ρa ρt s_mir s_osea

theorem osea_run_ok
  (ctx : ConstExistingCtx)
  (s_osea : oseair.State)
  (prog_osea : oseair.Prog)
  (addr tag : Word)
  (ap' : AccessPerms)
  (h_start : StartsAt prog_osea s_osea.pc ctx.compiled)
  (h_reg :
    s_osea.reg.lookup ctx.reg =
      some (TyVal.PTy, [oseair.Val.Ptr addr 0 (blockSize LayoutTy.NatL) tag]))
  (h_use : sb_use_mb s_osea.ap addr tag = SBResult.Ok ap') :
  oseair.runN 1 s_osea prog_osea =
    oseair.Result.Ok
      { s_osea with
        ap := ap',
        mem := oseair.writeWordSeq s_osea.mem addr [oseair.Val.Dat ctx.n],
        pc := s_osea.pc + 1 } := by
  rw [ctx.compiled_eq] at h_start
  simpa using
    osea_run_cstore_embedded_ok s_osea prog_osea LayoutTy.NatL [oseair.Val.Dat ctx.n]
      addr tag ctx.reg ap' h_start (by decide : 0 < blockSize LayoutTy.NatL) h_reg h_use

/--
Paper step 1 for the existing-destination constant case: invert a successful
MIR step to recover the unique successful `sb_use_mb` and the exact source
post-state.
-/
theorem mirlite_step_inv
  (ctx : ConstExistingCtx)
  (s_mir : mirlite.State)
  (s_mir_next : mirlite.State)
  (prog_mir : mirlite.Prog)
  (addr tag : Word)
  (h_env : s_mir.env.lookup ctx.base = some (addr, TyVal.NatTy, tag))
  (h_start : StartsAt prog_mir s_mir.pc [ctx.stmt])
  (h_step : mirlite.step s_mir prog_mir = mirlite.Result.Ok s_mir_next) :
  ∃ ap',
    sb_use_mb s_mir.ap addr tag = SBResult.Ok ap' ∧
    s_mir_next =
      { s_mir with
        ap := ap',
        mem := mirlite.writeWordSeq s_mir.mem addr [mirlite.MemValue.Val ctx.n],
        pc := s_mir.pc + 1 } := by
  have h_stmt_mir : prog_mir.get? s_mir.pc = some ctx.stmt := StartsAt.singleton h_start
  rcases List.get?_eq_some_iff.mp h_stmt_mir with ⟨h_pc_mir, h_get_mir⟩
  unfold mirlite.step at h_step
  rw [dif_pos h_pc_mir, h_get_mir] at h_step
  cases h_use : sb_use_mb s_mir.ap addr tag with
  | Err _ =>
      simp [ConstExistingCtx.stmt, obseq.notation.basePlace, obseq.notation.constRhs,
        mirlite.stepAssignConst, mirlite.finishPlaceAssign, mirlite.writeResolvedPlace,
        h_env, h_use] at h_step
  | Ok ap' =>
      refine ⟨ap', rfl, ?_⟩
      simpa [ConstExistingCtx.stmt, obseq.notation.basePlace, obseq.notation.constRhs,
        mirlite.stepAssignConst, mirlite.finishPlaceAssign, mirlite.writeResolvedPlace,
        h_env, h_use, mirlite.writeWordSeq] using h_step.symm

variable (ctx : ConstExistingCtx)
variable (s_mir : mirlite.State)
variable (s_osea : oseair.State)
variable (s_mir_next : mirlite.State)
variable (ρa : AddrRenaming)
variable (ρt : TagRenaming)

/--
Paper-style embedded simulation for `place(base) ::= const n` with an existing
destination:

1. recover the tracked runtime pointer/register pair from `StateSim`,
2. invert the MIR step,
3. transport the successful SB use to the target and execute the singleton
   `CStore`, and
4. rebuild `StateSim` after the matching writes.
-/
theorem simulation
  (prog_mir : mirlite.Prog)
  (prog_osea : oseair.Prog)
  (h_sim : LocalSim ctx ρa ρt s_mir s_osea)
  (h_mir_start : StartsAt prog_mir s_mir.pc [ctx.stmt])
  (h_osea_start : StartsAt prog_osea s_osea.pc ctx.compiled)
  (h_mir_step : mirlite.step s_mir prog_mir = mirlite.Result.Ok s_mir_next) :
  ∃ s_osea_next,
    StepStar s_osea prog_osea s_osea_next ∧
    LocalSim ctx ρa ρt s_mir_next s_osea_next := by
  -- Step 1: recover the runtime pointer/register witnesses tracked by `StateSim`.
  let ⟨addr_m, addr_o, tag_m, tag_o, h_ptr, _h_mem⟩ := StateSim.place h_sim ctx.h_lookup
  have h_env : s_mir.env.lookup ctx.base = some (addr_m, TyVal.NatTy, tag_m) :=
    place_runtime_sim.env h_ptr
  have h_reg :
      s_osea.reg.lookup ctx.reg =
        some (TyVal.PTy, [oseair.Val.Ptr addr_o 0 (blockSize LayoutTy.NatL) tag_o]) :=
    place_runtime_sim.reg h_ptr
  have h_addr : ρa addr_m = some addr_o := place_runtime_sim.addr h_ptr
  have h_tag : ρt tag_m = some tag_o := place_runtime_sim.tag h_ptr

  -- Step 2: invert the MIR step and expose the successful source-side SB use.
  let ⟨ap_m', h_use, h_next_full⟩ :=
    mirlite_step_inv
      ctx s_mir s_mir_next prog_mir addr_m tag_m h_env h_mir_start h_mir_step
  let ⟨ap_o', h_target_use, h_sb_next⟩ :=
    sb_use_mb_sim_ok (StateSim.sb h_sim) h_addr h_tag h_use

  -- Step 3: run the singleton compiled fragment on the target side.
  let s_osea_post :=
    { s_osea with
      ap := ap_o',
      mem := oseair.writeWordSeq s_osea.mem addr_o [oseair.Val.Dat ctx.n],
      pc := s_osea.pc + 1 }
  have h_target_run :
      oseair.runN 1 s_osea prog_osea = oseair.Result.Ok s_osea_post := by
    simpa [s_osea_post] using
      osea_run_ok
        ctx s_osea prog_osea addr_o tag_o ap_o' h_osea_start h_reg h_target_use

  -- Step 4: rebuild the simulation relation on the post-states.
  refine ⟨s_osea_post, StepStar.of_runN_ok h_target_run, ?_⟩
  rw [h_next_full]
  simpa [s_osea_post] using
    state_sim_write
      (π := ctx.cs.placeMap)
      (ρa := ρa)
      (ρt := ρt)
      (dst_mir := addr_m)
      (dst_osea := addr_o)
      (ap_m' := ap_m')
      (ap_o' := ap_o')
      (pc_mir := s_mir.pc + 1)
      (pc_osea := s_osea.pc + 1)
      (vals_mir := [mirlite.MemValue.Val ctx.n])
      (vals_osea := [oseair.Val.Dat ctx.n])
      h_sim h_sb_next (mem_vals_eq_word ctx.n)

end ConstExisting

end obseq.proof
