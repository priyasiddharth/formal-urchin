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

abbrev AddrRenaming := AddrRenameMap
abbrev TagRenaming := TagRenameMap

/--
`place_runtime_sim` is the renaming-aware per-base simulation relation for one
entry of the compiler's place-to-register map `π`.

The static compiler fact `π[base] = (reg, layout)` is packaged together with
the runtime source environment entry, the runtime target register entry, and
the address/tag renaming witnesses that relate the two pointers.
-/
def place_runtime_sim
  (π : PlaceMap)
  (ρa : AddrRenaming)
  (ρt : TagRenaming)
  (s_mir : mirlite.State)
  (s_osea : oseair.State)
  (base : Word)
  (reg : Register)
  (addr_m addr_o tag_m tag_o : Word)
  (layout : LayoutTy) : Prop :=
  π.lookup base = some (reg, layout) ∧
  s_mir.env.lookup base = some (addr_m, layoutToTyVal layout, tag_m) ∧
  s_osea.reg.lookup reg = some (TyVal.PTy, [oseair.Val.Ptr addr_o 0 (blockSize layout) tag_o]) ∧
  ρa addr_m = some addr_o ∧
  ρt tag_m = some tag_o

namespace place_runtime_sim

theorem env
  {π : PlaceMap} {ρa : AddrRenaming} {ρt : TagRenaming}
  {s_mir : mirlite.State} {s_osea : oseair.State}
  {base : Word} {reg : Register}
  {addr_m addr_o tag_m tag_o : Word} {layout : LayoutTy}
  (h :
    place_runtime_sim π ρa ρt s_mir s_osea base reg addr_m addr_o tag_m tag_o layout) :
  s_mir.env.lookup base = some (addr_m, layoutToTyVal layout, tag_m) := h.2.1

theorem reg
  {π : PlaceMap} {ρa : AddrRenaming} {ρt : TagRenaming}
  {s_mir : mirlite.State} {s_osea : oseair.State}
  {base : Word} {reg : Register}
  {addr_m addr_o tag_m tag_o : Word} {layout : LayoutTy}
  (h :
    place_runtime_sim π ρa ρt s_mir s_osea base reg addr_m addr_o tag_m tag_o layout) :
  s_osea.reg.lookup reg = some (TyVal.PTy, [oseair.Val.Ptr addr_o 0 (blockSize layout) tag_o]) :=
  h.2.2.1

theorem addr
  {π : PlaceMap} {ρa : AddrRenaming} {ρt : TagRenaming}
  {s_mir : mirlite.State} {s_osea : oseair.State}
  {base : Word} {reg : Register}
  {addr_m addr_o tag_m tag_o : Word} {layout : LayoutTy}
  (h :
    place_runtime_sim π ρa ρt s_mir s_osea base reg addr_m addr_o tag_m tag_o layout) :
  ρa addr_m = some addr_o := h.2.2.2.1

theorem tag
  {π : PlaceMap} {ρa : AddrRenaming} {ρt : TagRenaming}
  {s_mir : mirlite.State} {s_osea : oseair.State}
  {base : Word} {reg : Register}
  {addr_m addr_o tag_m tag_o : Word} {layout : LayoutTy}
  (h :
    place_runtime_sim π ρa ρt s_mir s_osea base reg addr_m addr_o tag_m tag_o layout) :
  ρt tag_m = some tag_o := h.2.2.2.2

end place_runtime_sim

/--
`block_sim_at` is the renaming-friendly memory relation for one tracked block.

It compares a source block at `addr` against a target block at `addr'`, so the
theorem interface no longer needs exact address equality between the two
machines.
-/
def block_sim_at
  (s_mir : mirlite.State)
  (s_osea : oseair.State)
  (addr addr' : Word)
  (layout : LayoutTy) : Prop :=
  ∀ i, i < blockSize layout →
    mem_val_eq_opt (s_mir.mem.find? (addr + i)) (s_osea.mem.find? (addr' + i))

/--
`StateSim π` is the theorem-facing exact simulation interface for the currently
proved fragment.

For every entry of the compiler place map `π`, the two machines agree on:

- the runtime base/register correspondence,
- the concrete tracked address and tag,
- the pointed-to block contents, and
- the global stacked-borrows state.

This is still a fragment-local relation: it only constrains the `π`-tracked
places, with SB well-formedness bundled inside `sb_sim`.
-/
def StateSim
  (π : PlaceMap)
  (ρa : AddrRenaming)
  (ρt : TagRenaming)
  (s_mir : mirlite.State)
  (s_osea : oseair.State) : Prop :=
  sb_sim ρa ρt s_mir.ap s_osea.ap ∧
  (∀ base reg layout,
    π.lookup base = some (reg, layout) →
    ∃ addr_m addr_o tag_m tag_o,
      place_runtime_sim π ρa ρt s_mir s_osea base reg addr_m addr_o tag_m tag_o layout ∧
      block_sim_at s_mir s_osea addr_m addr_o layout)

namespace StateSim

theorem sb
  {π : PlaceMap} {ρa : AddrRenaming} {ρt : TagRenaming}
  {s_mir : mirlite.State} {s_osea : oseair.State}
  (h : StateSim π ρa ρt s_mir s_osea) :
  sb_sim ρa ρt s_mir.ap s_osea.ap := h.1

theorem place
  {π : PlaceMap} {ρa : AddrRenaming} {ρt : TagRenaming}
  {s_mir : mirlite.State} {s_osea : oseair.State}
  (h : StateSim π ρa ρt s_mir s_osea)
  {base : Word} {reg : Register} {layout : LayoutTy}
  (h_lookup : π.lookup base = some (reg, layout)) :
  ∃ addr_m addr_o tag_m tag_o,
    place_runtime_sim π ρa ρt s_mir s_osea base reg addr_m addr_o tag_m tag_o layout ∧
    block_sim_at s_mir s_osea addr_m addr_o layout := by
  exact h.2 base reg layout h_lookup

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

theorem StepStar.of_runN_ok
  {n : Nat}
  {s s' : oseair.State}
  {prog : oseair.Prog}
  (h : oseair.runN n s prog = oseair.Result.Ok s') :
  StepStar s prog s' := by
  induction n generalizing s with
  | zero =>
      simp at h
      subst s'
      exact StepStar.refl s prog
  | succ n ih =>
      cases h_step : oseair.step s prog with
      | Err _ =>
          simp [oseair.runN, h_step] at h
      | Ok s1 =>
          simp [oseair.runN, h_step] at h
          exact StepStar.tail s s1 s' prog h_step (ih h)

end obseq.proof
