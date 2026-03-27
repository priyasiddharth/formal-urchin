import obseq.mirlite
import obseq.oseair
import obseq.compile
import obseq.notation
import obseq.sb

/-!
# `obseq.proof.core`

Shared proof infrastructure for the currently supported `obseq` fragment.

The active fragment is still intentionally small:

- base places only (`path = []`)
- block-sized layouts carried explicitly through the simulation relation
- word constants through `ConstOp`
- tuple construction through `StructInitOp`
- copies and later binary operations over copies

The proof pattern used by the statement-specific files is simulation-based:

1. invert the MIR step to recover the exact source-side SB action and post-state,
2. expose the shape of the compiled OSEA fragment,
3. execute that compiled fragment on the target side, and
4. rebuild the simulation relation on the post-states.

The intended layering above this core is:

- local fragment theorem,
- embedded arbitrary-PC wrapper, and then
- later whole-program induction.

This file contains the fragment predicates, the simulation relations, and the
generic multi-step target execution relation shared by all proof clusters.
-/

namespace obseq.proof

open obseq
open obseq.mirlite
open obseq.oseair hiding State Result
open obseq.compile
open scoped obseq.notation

/--
`StartsAt prog pc frag` says that `frag` is the slice of `prog` beginning at
`pc`.

This is the fragment-embedding relation used by the arbitrary-PC wrappers:
the local theorem proves correctness for the standalone fragment, and
`StartsAt` records where that fragment sits inside a larger program.
-/
def StartsAt (prog : List α) (pc : Nat) (frag : List α) : Prop :=
  ∀ i, frag.get? i = prog.get? (pc + i)

namespace StartsAt

theorem singleton
  {prog : List α}
  {pc : Nat}
  {x : α}
  (h : StartsAt prog pc [x]) :
  prog.get? pc = some x := by
  simpa [StartsAt, Nat.zero_add] using (h 0).symm

theorem tail
  {prog : List α}
  {pc : Nat}
  {x : α}
  {frag : List α}
  (h : StartsAt prog pc (x :: frag)) :
  StartsAt prog (pc + 1) frag := by
  intro i
  have h_i := h (i + 1)
  simpa [StartsAt, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h_i

end StartsAt

def shiftMirPc (basePc : Nat) (s : mirlite.State) : mirlite.State :=
  { s with pc := basePc + s.pc }

def shiftOseaPc (basePc : Nat) (s : oseair.State) : oseair.State :=
  { s with pc := basePc + s.pc }

def shiftMirResultPc (basePc : Nat) : mirlite.Result → mirlite.Result
  | mirlite.Result.Ok s => mirlite.Result.Ok (shiftMirPc basePc s)
  | mirlite.Result.Err msg => mirlite.Result.Err msg

def shiftOseaResultPc (basePc : Nat) : oseair.Result → oseair.Result
  | oseair.Result.Ok s => oseair.Result.Ok (shiftOseaPc basePc s)
  | oseair.Result.Err msg => oseair.Result.Err msg

def shiftOseaRhsResultPc (basePc : Nat) : oseair.RhsResult → oseair.RhsResult
  | oseair.RhsResult.Ok vals ty s => oseair.RhsResult.Ok vals ty (shiftOseaPc basePc s)
  | oseair.RhsResult.Err msg => oseair.RhsResult.Err msg

def CompilerEmpty (cs : CompilerState) : Prop :=
  cs.instrs = []

def BaseReady (cs : CompilerState) (base : Word) (reg : Register) (layout : LayoutTy) : Prop :=
  getPlaceInfo cs base = some (reg, layout)

def BaseAbsent (cs : CompilerState) (base : Word) : Prop :=
  getPlaceInfo cs base = none

def regIdx : Register → Nat
  | Register.R n => n

def MappedRegsBelowNext (cs : CompilerState) : Prop :=
  ∀ base reg layout,
    cs.placeMap.lookup base = some (reg, layout) →
    regIdx reg < cs.nextReg

/-- Proof-facing symbolic block size for a layout. -/
def blockSize (layout : LayoutTy) : Nat :=
  typeSize (layoutToTyVal layout)

def mem_val_eq (v1 : mirlite.MemValue) (v2 : oseair.Val) : Prop :=
  match v1, v2 with
  | mirlite.MemValue.Undef, oseair.Val.Undef => True
  | mirlite.MemValue.Val n1, oseair.Val.Dat n2 => n1 = n2
  | _, _ => False

def mem_val_eq_opt (v1 : Option mirlite.MemValue) (v2 : Option oseair.Val) : Prop :=
  match v1, v2 with
  | some val1, some val2 => mem_val_eq val1 val2
  | none, none => True
  | _, _ => False

inductive mem_vals_eq : List mirlite.MemValue → List oseair.Val → Prop
| nil : mem_vals_eq [] []
| cons :
    mem_val_eq v_mir v_osea →
    mem_vals_eq vals_mir vals_osea →
    mem_vals_eq (v_mir :: vals_mir) (v_osea :: vals_osea)

abbrev AddrRenaming := obseq.AddrRenaming
abbrev TagRenaming := obseq.TagRenaming

/-- Global stacked-borrows agreement for the current proof fragment. -/
def sb_eq
  (s_mir : mirlite.State)
  (s_osea : oseair.State) : Prop :=
  s_mir.ap = s_osea.ap

/--
`base_ptr_sim` is the exact per-base simulation relation for one entry of the
compiler's place-to-register map `π`.

Unlike the earlier version of this relation, the static compiler fact
`π[base] = (reg, layout)` is part of the definition rather than carried as a
separate side hypothesis. The relation still uses exact address/tag equality;
the more general renaming-based interface is `place_runtime_sim`.
-/
def base_ptr_sim
  (π : PlaceMap)
  (s_mir : mirlite.State)
  (s_osea : oseair.State)
  (base : Word)
  (reg : Register)
  (addr tag : Word)
  (layout : LayoutTy) : Prop :=
  π.lookup base = some (reg, layout) ∧
  s_mir.env.lookup base = some (addr, layoutToTyVal layout, tag) ∧
  s_osea.reg.lookup reg = some (TyVal.PTy, [oseair.Val.Ptr addr 0 (blockSize layout) tag])

/--
`sim_mem_at` is the memory-side relation for one tracked allocation block.

For the current base-place fragment we only need:

- equal allocation fronts (`addrStart`), and
- pointwise value agreement across the tracked block starting at `addr`.
-/
def sim_mem_at
  (s_mir : mirlite.State)
  (s_osea : oseair.State)
  (addr : Word)
  (layout : LayoutTy) : Prop :=
  s_mir.mem.addrStart = s_osea.mem.addrStart ∧
  ∀ i, i < blockSize layout →
    mem_val_eq_opt (s_mir.mem.find? (addr + i)) (s_osea.mem.find? (addr + i))

/--
`block_sim_at` is the renaming-friendly memory relation for one tracked block.

Unlike `sim_mem_at`, it compares a source block at `addr` against a target
block at `addr'`, so the theorem interface no longer needs exact address
equality between the two machines.
-/
def block_sim_at
  (s_mir : mirlite.State)
  (s_osea : oseair.State)
  (addr addr' : Word)
  (layout : LayoutTy) : Prop :=
  ∀ i, i < blockSize layout →
    mem_val_eq_opt (s_mir.mem.find? (addr + i)) (s_osea.mem.find? (addr' + i))

/--
`interval_disjoint base1 size1 base2 size2` says the half-open intervals
`[base1, base1 + size1)` and `[base2, base2 + size2)` do not overlap.
-/
def interval_disjoint
  (base1 size1 base2 size2 : Word) : Prop :=
  base1 + size1 ≤ base2 ∨ base2 + size2 ≤ base1

/--
All `π`-tracked runtime blocks are disjoint from the current fresh-allocation
interval.

This packages the proof-only non-overlap fact needed in fresh-allocation
proofs: when both machines allocate `[addrStart, addrStart + freshSize)`,
that fresh block cannot shadow any previously mapped base.
-/
def mapped_blocks_fresh_interval
  (π : PlaceMap)
  (s_mir : mirlite.State)
  (s_osea : oseair.State)
  (freshSize : Word) : Prop :=
  ∀ base reg layout addr addr' tag tag',
    π.lookup base = some (reg, layout) →
    s_mir.env.lookup base = some (addr, layoutToTyVal layout, tag) →
    s_osea.reg.lookup reg = some (TyVal.PTy, [oseair.Val.Ptr addr' 0 (blockSize layout) tag']) →
    interval_disjoint addr (blockSize layout) s_mir.mem.addrStart freshSize ∧
    interval_disjoint addr' (blockSize layout) s_osea.mem.addrStart freshSize

/--
`StateSim π` is the theorem-facing exact simulation interface for the currently
proved fragment.

For every entry of the compiler place map `π`, the two machines agree on:

- the runtime base/register correspondence,
- the concrete tracked address and tag,
- the pointed-to block contents, and
- the global stacked-borrows state.

This is still a fragment-local relation: it only constrains the `π`-tracked
places plus the validity side conditions. The tracked-block fresh-interval fact
is treated separately as a proof axiom via `StateSim.fresh_interval`.
-/
def StateSim
  (π : PlaceMap)
  (s_mir : mirlite.State)
  (s_osea : oseair.State) : Prop :=
  SBValid s_mir.ap ∧
  SBValid s_osea.ap ∧
  s_mir.ap = s_osea.ap ∧
  s_mir.mem.addrStart = s_osea.mem.addrStart ∧
  (∀ base reg layout,
    π.lookup base = some (reg, layout) →
    ∃ addr tag,
      base_ptr_sim π s_mir s_osea base reg addr tag layout ∧
      sim_mem_at s_mir s_osea addr layout)

namespace StateSim

theorem ap_eq
  {π : PlaceMap}
  {s_mir : mirlite.State}
  {s_osea : oseair.State}
  (h : StateSim π s_mir s_osea) :
  s_mir.ap = s_osea.ap := h.2.2.1

theorem addrStart_eq
  {π : PlaceMap}
  {s_mir : mirlite.State}
  {s_osea : oseair.State}
  (h : StateSim π s_mir s_osea) :
  s_mir.mem.addrStart = s_osea.mem.addrStart := h.2.2.2.1

theorem place
  {π : PlaceMap}
  {s_mir : mirlite.State}
  {s_osea : oseair.State}
  (h : StateSim π s_mir s_osea)
  {base : Word} {reg : Register} {layout : LayoutTy}
  (h_lookup : π.lookup base = some (reg, layout)) :
  ∃ addr tag,
    base_ptr_sim π s_mir s_osea base reg addr tag layout ∧
    sim_mem_at s_mir s_osea addr layout := by
  exact h.2.2.2.2 base reg layout h_lookup

theorem valid_mir
  {π : PlaceMap}
  {s_mir : mirlite.State}
  {s_osea : oseair.State}
  (h : StateSim π s_mir s_osea) :
  SBValid s_mir.ap := h.1

theorem valid_osea
  {π : PlaceMap}
  {s_mir : mirlite.State}
  {s_osea : oseair.State}
  (h : StateSim π s_mir s_osea) :
  SBValid s_osea.ap := h.2.1

/-- Proof-only interval-disjointness axiom for tracked blocks vs fresh allocation. -/
axiom fresh_interval
  {π : PlaceMap}
  {s_mir : mirlite.State}
  {s_osea : oseair.State}
  (h : StateSim π s_mir s_osea)
  {freshSize : Word}
  {base : Word} {reg : Register} {layout : LayoutTy}
  {addr addr' tag tag' : Word}
  (h_lookup : π.lookup base = some (reg, layout))
  (h_env : s_mir.env.lookup base = some (addr, layoutToTyVal layout, tag))
  (h_reg :
    s_osea.reg.lookup reg =
      some (TyVal.PTy, [oseair.Val.Ptr addr' 0 (blockSize layout) tag'])) :
  interval_disjoint addr (blockSize layout) s_mir.mem.addrStart freshSize ∧
  interval_disjoint addr' (blockSize layout) s_osea.mem.addrStart freshSize

end StateSim

inductive StepStar : oseair.State → oseair.Prog → oseair.State → Prop
| refl (s : oseair.State) (prog : oseair.Prog) : StepStar s prog s
| tail (s1 s2 s3 : oseair.State) (prog : oseair.Prog) :
    oseair.step s1 prog = oseair.Result.Ok s2 →
    StepStar s2 prog s3 →
    StepStar s1 prog s3

theorem StepStar.single
  {s1 s2 : oseair.State} {prog : oseair.Prog}
  (h : oseair.step s1 prog = oseair.Result.Ok s2) :
  StepStar s1 prog s2 :=
  StepStar.tail s1 s2 s2 prog h (StepStar.refl s2 prog)

theorem StepStar.trans
  {s1 s2 s3 : oseair.State}
  {prog : oseair.Prog}
  (h12 : StepStar s1 prog s2)
  (h23 : StepStar s2 prog s3) :
  StepStar s1 prog s3 := by
  induction h12 with
  | refl _ _ =>
      exact h23
  | tail s1 s2 sMid prog h_step _h_rest ih =>
      exact StepStar.tail s1 s2 s3 prog h_step (ih h23)

end obseq.proof
