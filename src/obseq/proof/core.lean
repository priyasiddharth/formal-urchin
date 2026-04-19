import obseq.mirlite
import obseq.oseair
import obseq.compile
import obseq.notation
import obseq.sb

/-!
# `obseq.proof.core`

Shared proof infrastructure for the currently supported `obseq` fragment.

The active fragment is still intentionally small:

- existing places may use arbitrary tuple projection paths
- fresh-place allocation is still base-only (`path = []`)
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

/-! ## Axioms -/

axiom alloc_fresh_reg
  {cs : CompilerState} :
  ∀ base layout,
    cs.placeMap.lookup base = some (Register.R cs.nextReg, layout) →
    False

axiom addr_rename_offset
  {ρa : AddrRenameMap} :
  ∀ {addr_m addr_o off},
    ρa addr_m = some addr_o →
    ρa (addr_m + off) = some (addr_o + off)

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
  unfold StartsAt at h
  simpa [Nat.zero_add, List.get?] using (h 0).symm

theorem tail
  {prog : List α}
  {pc : Nat}
  {x : α}
  {frag : List α}
  (h : StartsAt prog pc (x :: frag)) :
  StartsAt prog (pc + 1) frag := by
  unfold StartsAt at h ⊢
  intro i
  have h_i := h (i + 1)
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h_i

theorem get_instr
  {prog : List α}
  {pc : Nat}
  {instr : α}
  (h_start : StartsAt prog pc [instr]) :
  ∃ h_pc : pc < prog.length, prog.get ⟨pc, h_pc⟩ = instr := by
  have h_stmt : prog.get? pc = some instr := StartsAt.singleton h_start
  exact (List.get?_eq_some_iff.mp h_stmt)

end StartsAt

def CompilerEmpty (cs : CompilerState) : Prop :=
  cs.instrs = []

def BaseReady (cs : CompilerState) (base : Word) (reg : Register) (layout : LayoutTy) : Prop :=
  getPlaceInfo cs base = some (reg, layout)

def BaseAbsent (cs : CompilerState) (base : Word) : Prop :=
  getPlaceInfo cs base = none

/-- Proof-facing symbolic block size for a layout. -/
def blockSize (layout : LayoutTy) : Nat :=
  typeSize (layoutToTyVal layout)

@[simp] theorem blockSize_eq_layoutSize
  (layout : LayoutTy) :
  blockSize layout = layoutSize layout := by
  simp [blockSize]

theorem layoutResolvePath_blockSize_le
  {baseLayout subLayout : LayoutTy}
  {path : List Nat}
  {off : Word}
  (h_path : layoutResolvePath baseLayout path = some (off, subLayout)) :
  off + blockSize subLayout ≤ blockSize baseLayout := by
  simpa [blockSize_eq_layoutSize] using
    layoutResolvePath_layoutSize_le baseLayout path off subLayout h_path

/-- Predicate for pointer-cell simulation.  Receives MIR Place, MIR tag, and
    the four OSEA Ptr fields (base, off, size, tag). -/
abbrev PtrSimPred := mirlite.Place → Tag → Word → Word → Word → Tag → Prop

/-- Default pointer predicate: reject all PlaceTag↔Ptr pairs. -/
def defaultPtrSim : PtrSimPred := fun _ _ _ _ _ _ => False

/-- Renaming-aware pointer predicate built from ρa, ρt and the MIR env.
    A PlaceTag↔Ptr cell is accepted when the place resolves via the
    environment to the OSEA pointer's base plus offset under the address and
    tag renamings. -/
def ptrSimOfCtx (ρa : AddrRenameMap) (ρt : TagRenameMap) (env : mirlite.Env)
    : PtrSimPred :=
  fun p tag_m base off size tag_o =>
    ∃ (addr_m : Word) (baseLayout subLayout : LayoutTy)
      (pathOff : Word) (baseTag : Tag),
      env.lookup p.base = some (addr_m, layoutToTyVal baseLayout, baseTag) ∧
      layoutResolvePath baseLayout p.path = some (pathOff, subLayout) ∧
      ρa addr_m = some base ∧
      off = pathOff ∧
      ρt tag_m = some tag_o ∧
      size = blockSize baseLayout

/-- Given a `ptrSimOfCtx` witness together with a known env-lookup and
    path-resolution for the same place, extract the OSEA-side equalities
    (base, offset, size, tag) directly.  Avoids repeating the equating
    chain in every simulation proof that consumes a stored pointer. -/
theorem ptrSimOfCtx_elim
  {ρa : AddrRenameMap} {ρt : TagRenameMap} {env : mirlite.Env}
  {q : mirlite.Place} {gq : Tag}
  {base off size tag_o : Word}
  {targetBaseAddr targetBaseTag : Word}
  {targetBaseLayout innerLayout : LayoutTy}
  {targetOff : Word}
  (h_ptr : ptrSimOfCtx ρa ρt env q gq base off size tag_o)
  (h_env : env.lookup q.base =
    some (targetBaseAddr, layoutToTyVal targetBaseLayout, targetBaseTag))
  (h_path : layoutResolvePath targetBaseLayout q.path = some (targetOff, innerLayout)) :
  ρa targetBaseAddr = some base ∧
  off = targetOff ∧
  ρt gq = some tag_o ∧
  size = blockSize targetBaseLayout := by
  rcases h_ptr with
    ⟨addr_m, baseLayout, subLayout, pathOff, baseTag,
      h_env', h_path', h_addr, h_off, h_tag, h_size⟩
  have h_env_eq :
      (addr_m, layoutToTyVal baseLayout, baseTag) =
        (targetBaseAddr, layoutToTyVal targetBaseLayout, targetBaseTag) :=
    Option.some.inj (h_env'.symm.trans h_env)
  have h_addr_eq : addr_m = targetBaseAddr := congrArg Prod.fst h_env_eq
  have h_ty_eq : layoutToTyVal baseLayout = layoutToTyVal targetBaseLayout :=
    congrArg (fun t => t.2.1) h_env_eq
  cases h_addr_eq
  have h_tyRes1 :=
    tyResolvePath_layoutToTyVal baseLayout q.path pathOff subLayout h_path'
  have h_tyRes2 :=
    tyResolvePath_layoutToTyVal targetBaseLayout q.path targetOff innerLayout h_path
  rw [h_ty_eq] at h_tyRes1
  have h_pair_eq :
      (pathOff, layoutToTyVal subLayout) = (targetOff, layoutToTyVal innerLayout) :=
    Option.some.inj (h_tyRes1.symm.trans h_tyRes2)
  have h_pathOff_eq : pathOff = targetOff := congrArg Prod.fst h_pair_eq
  cases h_pathOff_eq
  have h_size_eq : blockSize baseLayout = blockSize targetBaseLayout := by
    simp [blockSize, h_ty_eq]
  exact ⟨by simpa using h_addr, h_off, h_tag, by rw [h_size, h_size_eq]⟩

def mem_val_eq (v1 : mirlite.MemValue) (v2 : oseair.Val)
    (ptr_sim : PtrSimPred := defaultPtrSim) : Prop :=
  match v1, v2 with
  | mirlite.MemValue.Undef, oseair.Val.Undef => True
  | mirlite.MemValue.Val n1, oseair.Val.Dat n2 => n1 = n2
  | mirlite.MemValue.PlaceTag p tag_m, oseair.Val.Ptr base off size tag_o =>
      ptr_sim p tag_m base off size tag_o
  | _, _ => False

def mem_val_eq_opt (v1 : Option mirlite.MemValue) (v2 : Option oseair.Val)
    (ptr_sim : PtrSimPred := defaultPtrSim) : Prop :=
  match v1, v2 with
  | some val1, some val2 => mem_val_eq val1 val2 ptr_sim
  | none, none => True
  | _, _ => False

inductive mem_vals_eq (ptr_sim : PtrSimPred)
    : List mirlite.MemValue → List oseair.Val → Prop
| nil : mem_vals_eq ptr_sim [] []
| cons :
    mem_val_eq v_mir v_osea ptr_sim →
    mem_vals_eq ptr_sim vals_mir vals_osea →
    mem_vals_eq ptr_sim (v_mir :: vals_mir) (v_osea :: vals_osea)


/--
`place_runtime_sim` is the renaming-aware per-base simulation relation for one
entry of the compiler's place-to-register map `π`.

The static compiler fact `π[base] = (reg, layout)` is packaged together with
the runtime source environment entry, the runtime target register entry, and
the address/tag renaming witnesses that relate the two pointers.
-/
def place_runtime_sim
  (π : PlaceMap)
  (ρa : AddrRenameMap)
  (ρt : TagRenameMap)
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
  {π : PlaceMap} {ρa : AddrRenameMap} {ρt : TagRenameMap}
  {s_mir : mirlite.State} {s_osea : oseair.State}
  {base : Word} {reg : Register}
  {addr_m addr_o tag_m tag_o : Word} {layout : LayoutTy}
  (h :
    place_runtime_sim π ρa ρt s_mir s_osea base reg addr_m addr_o tag_m tag_o layout) :
  s_mir.env.lookup base = some (addr_m, layoutToTyVal layout, tag_m) := h.2.1

theorem reg
  {π : PlaceMap} {ρa : AddrRenameMap} {ρt : TagRenameMap}
  {s_mir : mirlite.State} {s_osea : oseair.State}
  {base : Word} {reg : Register}
  {addr_m addr_o tag_m tag_o : Word} {layout : LayoutTy}
  (h :
    place_runtime_sim π ρa ρt s_mir s_osea base reg addr_m addr_o tag_m tag_o layout) :
  s_osea.reg.lookup reg = some (TyVal.PTy, [oseair.Val.Ptr addr_o 0 (blockSize layout) tag_o]) :=
  h.2.2.1

theorem addr
  {π : PlaceMap} {ρa : AddrRenameMap} {ρt : TagRenameMap}
  {s_mir : mirlite.State} {s_osea : oseair.State}
  {base : Word} {reg : Register}
  {addr_m addr_o tag_m tag_o : Word} {layout : LayoutTy}
  (h :
    place_runtime_sim π ρa ρt s_mir s_osea base reg addr_m addr_o tag_m tag_o layout) :
  ρa addr_m = some addr_o := h.2.2.2.1

theorem tag
  {π : PlaceMap} {ρa : AddrRenameMap} {ρt : TagRenameMap}
  {s_mir : mirlite.State} {s_osea : oseair.State}
  {base : Word} {reg : Register}
  {addr_m addr_o tag_m tag_o : Word} {layout : LayoutTy}
  (h :
    place_runtime_sim π ρa ρt s_mir s_osea base reg addr_m addr_o tag_m tag_o layout) :
  ρt tag_m = some tag_o := h.2.2.2.2

theorem eq
  {π : PlaceMap} {ρa : AddrRenameMap} {ρt : TagRenameMap}
  {s_mir : mirlite.State} {s_osea : oseair.State}
  {base : Word} {reg : Register}
  {addr₁_m addr₁_o tag₁_m tag₁_o : Word}
  {addr₂_m addr₂_o tag₂_m tag₂_o : Word}
  {layout : LayoutTy}
  (h₁ :
    place_runtime_sim π ρa ρt s_mir s_osea
      base reg addr₁_m addr₁_o tag₁_m tag₁_o layout)
  (h₂ :
    place_runtime_sim π ρa ρt s_mir s_osea
      base reg addr₂_m addr₂_o tag₂_m tag₂_o layout) :
  addr₁_m = addr₂_m ∧ addr₁_o = addr₂_o ∧ tag₁_m = tag₂_m ∧ tag₁_o = tag₂_o := by
  have h_env_eq :
      some (addr₁_m, layoutToTyVal layout, tag₁_m) =
        some (addr₂_m, layoutToTyVal layout, tag₂_m) := by
    exact (place_runtime_sim.env h₁).symm.trans (place_runtime_sim.env h₂)
  have h_reg_eq :
      some (TyVal.PTy, [oseair.Val.Ptr addr₁_o 0 (blockSize layout) tag₁_o]) =
        some (TyVal.PTy, [oseair.Val.Ptr addr₂_o 0 (blockSize layout) tag₂_o]) := by
    exact (place_runtime_sim.reg h₁).symm.trans (place_runtime_sim.reg h₂)
  cases h_env_eq
  cases h_reg_eq
  exact ⟨rfl, rfl, rfl, rfl⟩

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
  (layout : LayoutTy)
  (ptr_sim : PtrSimPred := defaultPtrSim) : Prop :=
  ∀ i, i < blockSize layout →
    mem_val_eq_opt (s_mir.mem.find? (addr + i)) (s_osea.mem.find? (addr' + i)) ptr_sim

theorem block_sim_at_offset
  {s_mir : mirlite.State}
  {s_osea : oseair.State}
  {addr_m addr_o : Word}
  {baseLayout subLayout : LayoutTy}
  {off : Word}
  {ptr_sim : PtrSimPred}
  (h_block : block_sim_at s_mir s_osea addr_m addr_o baseLayout ptr_sim)
  (h_fit : off + blockSize subLayout ≤ blockSize baseLayout) :
  block_sim_at s_mir s_osea (addr_m + off) (addr_o + off) subLayout ptr_sim := by
  intro i hi
  have h_within : off + i < blockSize baseLayout := by
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hi off) h_fit
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h_block (off + i) h_within

/--
`blocks_disjoint addr₁ sz₁ addr₂ sz₂` says that the concrete cells of the two
tracked blocks do not overlap.
-/
def blocks_disjoint
  (addr₁ : Word)
  (sz₁ : Nat)
  (addr₂ : Word)
  (sz₂ : Nat) : Prop :=
  ∀ i, i < sz₁ → ∀ j, j < sz₂ → addr₁ + i ≠ addr₂ + j

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
  (ρa : AddrRenameMap)
  (ρt : TagRenameMap)
  (s_mir : mirlite.State)
  (s_osea : oseair.State)
  (ptr_sim : PtrSimPred := defaultPtrSim) : Prop :=
  sb_sim ρa ρt s_mir.ap s_osea.ap ∧
  (∀ base reg layout,
    π.lookup base = some (reg, layout) →
    ∃ addr_m addr_o tag_m tag_o,
      place_runtime_sim π ρa ρt s_mir s_osea base reg addr_m addr_o tag_m tag_o layout ∧
      block_sim_at s_mir s_osea addr_m addr_o layout ptr_sim) ∧
  (∀ base₁ reg₁ layout₁ base₂ reg₂ layout₂,
    π.lookup base₁ = some (reg₁, layout₁) →
    π.lookup base₂ = some (reg₂, layout₂) →
    base₁ ≠ base₂ →
    ∀ addr₁_m addr₁_o tag₁_m tag₁_o addr₂_m addr₂_o tag₂_m tag₂_o,
      place_runtime_sim π ρa ρt s_mir s_osea base₁ reg₁ addr₁_m addr₁_o tag₁_m tag₁_o layout₁ →
      place_runtime_sim π ρa ρt s_mir s_osea base₂ reg₂ addr₂_m addr₂_o tag₂_m tag₂_o layout₂ →
      blocks_disjoint addr₁_m (blockSize layout₁) addr₂_m (blockSize layout₂) ∧
      blocks_disjoint addr₁_o (blockSize layout₁) addr₂_o (blockSize layout₂))

namespace StateSim

theorem sb
  {π : PlaceMap} {ρa : AddrRenameMap} {ρt : TagRenameMap}
  {s_mir : mirlite.State} {s_osea : oseair.State}
  {ptr_sim : PtrSimPred}
  (h : StateSim π ρa ρt s_mir s_osea ptr_sim) :
  sb_sim ρa ρt s_mir.ap s_osea.ap := h.1

theorem place
  {π : PlaceMap} {ρa : AddrRenameMap} {ρt : TagRenameMap}
  {s_mir : mirlite.State} {s_osea : oseair.State}
  {ptr_sim : PtrSimPred}
  (h : StateSim π ρa ρt s_mir s_osea ptr_sim)
  {base : Word} {reg : Register} {layout : LayoutTy}
  (h_lookup : π.lookup base = some (reg, layout)) :
  ∃ addr_m addr_o tag_m tag_o,
    place_runtime_sim π ρa ρt s_mir s_osea base reg addr_m addr_o tag_m tag_o layout ∧
    block_sim_at s_mir s_osea addr_m addr_o layout ptr_sim := by
  exact h.2.1 base reg layout h_lookup

theorem place_projected
  {π : PlaceMap} {ρa : AddrRenameMap} {ρt : TagRenameMap}
  {s_mir : mirlite.State} {s_osea : oseair.State}
  {ptr_sim : PtrSimPred}
  (h : StateSim π ρa ρt s_mir s_osea ptr_sim)
  {p : mirlite.Place}
  {reg : Register}
  {baseLayout subLayout : LayoutTy}
  {off : Word}
  (h_lookup : π.lookup p.base = some (reg, baseLayout))
  (h_path : layoutResolvePath baseLayout p.path = some (off, subLayout)) :
  ∃ addr_m addr_o tag_m tag_o,
    place_runtime_sim π ρa ρt s_mir s_osea
      p.base reg addr_m addr_o tag_m tag_o baseLayout ∧
    block_sim_at s_mir s_osea (addr_m + off) (addr_o + off) subLayout ptr_sim := by
  let ⟨addr_m, addr_o, tag_m, tag_o, h_ptr, h_block⟩ := StateSim.place h h_lookup
  refine ⟨addr_m, addr_o, tag_m, tag_o, h_ptr, ?_⟩
  exact block_sim_at_offset h_block (layoutResolvePath_blockSize_le h_path)

theorem disjoint
  {π : PlaceMap} {ρa : AddrRenameMap} {ρt : TagRenameMap}
  {s_mir : mirlite.State} {s_osea : oseair.State}
  {ptr_sim : PtrSimPred}
  (h : StateSim π ρa ρt s_mir s_osea ptr_sim)
  {base₁ base₂ : Word}
  {reg₁ reg₂ : Register}
  {layout₁ layout₂ : LayoutTy}
  (h_lookup₁ : π.lookup base₁ = some (reg₁, layout₁))
  (h_lookup₂ : π.lookup base₂ = some (reg₂, layout₂))
  (h_ne : base₁ ≠ base₂)
  {addr₁_m addr₁_o tag₁_m tag₁_o addr₂_m addr₂_o tag₂_m tag₂_o : Word}
  (h_ptr₁ :
    place_runtime_sim π ρa ρt s_mir s_osea
      base₁ reg₁ addr₁_m addr₁_o tag₁_m tag₁_o layout₁)
  (h_ptr₂ :
    place_runtime_sim π ρa ρt s_mir s_osea
      base₂ reg₂ addr₂_m addr₂_o tag₂_m tag₂_o layout₂) :
  blocks_disjoint addr₁_m (blockSize layout₁) addr₂_m (blockSize layout₂) ∧
  blocks_disjoint addr₁_o (blockSize layout₁) addr₂_o (blockSize layout₂) := by
  exact h.2.2 base₁ reg₁ layout₁ base₂ reg₂ layout₂ h_lookup₁ h_lookup₂ h_ne
    addr₁_m addr₁_o tag₁_m tag₁_o addr₂_m addr₂_o tag₂_m tag₂_o h_ptr₁ h_ptr₂

end StateSim

theorem resolveDirectPlace_eq_of_env_lookup
  {state : mirlite.State}
  {p : mirlite.Place}
  {addr tag off : Word}
  {baseLayout subLayout : LayoutTy}
  (h_env : state.env.lookup p.base = some (addr, layoutToTyVal baseLayout, tag))
  (h_path : layoutResolvePath baseLayout p.path = some (off, subLayout)) :
  mirlite.resolveDirectPlace state p =
    (mirlite.Result.Ok state,
      { addr := addr + off, tag := tag, ty := layoutToTyVal subLayout, state := state }) := by
  cases p with
  | mk base path =>
      simp at h_env h_path
      have h_path' :
          tyResolvePath (layoutToTyVal baseLayout) path =
            some (off, layoutToTyVal subLayout) :=
        tyResolvePath_layoutToTyVal baseLayout path off subLayout h_path
      simp [mirlite.resolveDirectPlace, mirlite.resolvePath, h_env, h_path']

theorem finishPlaceAssign_existing_eq
  {pc0 : Nat}
  {state : mirlite.State}
  {p : mirlite.Place}
  {vals : List mirlite.MemValue}
  {ty : TyVal}
  {addr tag off : Word}
  {baseLayout subLayout : LayoutTy}
  (h_env : state.env.lookup p.base = some (addr, layoutToTyVal baseLayout, tag))
  (h_path : layoutResolvePath baseLayout p.path = some (off, subLayout)) :
  mirlite.finishPlaceAssign pc0 state p vals ty =
    match sb_use_mb state.ap (addr + off) tag with
    | SBResult.Ok ap' =>
        mirlite.Result.Ok
          { state with
            ap := ap',
            mem := mirlite.writeWordSeq state.mem (addr + off) vals,
            pc := pc0 + 1 }
    | SBResult.Err msg => mirlite.Result.Err msg := by
  unfold mirlite.finishPlaceAssign mirlite.finishPlaceAssignWith
  rw [h_env]
  by_cases h_empty : p.path = []
  · have h_path' : layoutResolvePath baseLayout [] = some (off, subLayout) := by
      simpa [h_empty] using h_path
    simp [layoutResolvePath] at h_path'
    rcases h_path' with ⟨rfl, rfl⟩
    cases h_use : sb_use_mb state.ap addr tag <;>
      simp [h_empty, h_use, mirlite.writeResolvedPlace]
  · rw [resolveDirectPlace_eq_of_env_lookup h_env h_path]
    cases h_use : sb_use_mb state.ap (addr + off) tag <;>
      simp [h_empty, h_use, mirlite.writeResolvedPlace]

theorem finishPlaceAssignWith_existing_eq
  {A : mirlite.AllocatorSpec}
  {pc0 : Nat}
  {state : mirlite.State}
  {p : mirlite.Place}
  {vals : List mirlite.MemValue}
  {ty : TyVal}
  {addr tag off : Word}
  {baseLayout subLayout : LayoutTy}
  (h_env : state.env.lookup p.base = some (addr, layoutToTyVal baseLayout, tag))
  (h_path : layoutResolvePath baseLayout p.path = some (off, subLayout)) :
  mirlite.finishPlaceAssignWith A pc0 state p vals ty =
    match sb_use_mb state.ap (addr + off) tag with
    | SBResult.Ok ap' =>
        mirlite.Result.Ok
          { state with
            ap := ap',
            mem := mirlite.writeWordSeq state.mem (addr + off) vals,
            pc := pc0 + 1 }
    | SBResult.Err msg => mirlite.Result.Err msg := by
  unfold mirlite.finishPlaceAssignWith
  rw [h_env]
  by_cases h_empty : p.path = []
  · have h_path' : layoutResolvePath baseLayout [] = some (off, subLayout) := by
      simpa [h_empty] using h_path
    simp [layoutResolvePath] at h_path'
    rcases h_path' with ⟨rfl, rfl⟩
    cases h_use : sb_use_mb state.ap addr tag <;>
      simp [h_empty, h_use, mirlite.writeResolvedPlace]
  · rw [resolveDirectPlace_eq_of_env_lookup h_env h_path]
    cases h_use : sb_use_mb state.ap (addr + off) tag <;>
      simp [h_empty, h_use, mirlite.writeResolvedPlace]

inductive StepStarWith (A : oseair.AllocatorSpec) : oseair.State → oseair.Prog → oseair.State → Prop
| refl (s : oseair.State) (prog : oseair.Prog) : StepStarWith A s prog s
| tail (s1 s2 s3 : oseair.State) (prog : oseair.Prog) :
    oseair.stepWith A s1 prog = oseair.Result.Ok s2 →
    StepStarWith A s2 prog s3 →
    StepStarWith A s1 prog s3

abbrev StepStar : oseair.State → oseair.Prog → oseair.State → Prop :=
  StepStarWith oseair.bumpAllocator

theorem StepStarWith.single
  {A : oseair.AllocatorSpec}
  {s1 s2 : oseair.State} {prog : oseair.Prog}
  (h : oseair.stepWith A s1 prog = oseair.Result.Ok s2) :
  StepStarWith A s1 prog s2 :=
  StepStarWith.tail s1 s2 s2 prog h (StepStarWith.refl s2 prog)

theorem StepStar.single
  {s1 s2 : oseair.State} {prog : oseair.Prog}
  (h : oseair.step s1 prog = oseair.Result.Ok s2) :
  StepStar s1 prog s2 :=
  StepStarWith.single h

theorem StepStarWith.trans
  {A : oseair.AllocatorSpec}
  {s1 s2 s3 : oseair.State}
  {prog : oseair.Prog}
  (h12 : StepStarWith A s1 prog s2)
  (h23 : StepStarWith A s2 prog s3) :
  StepStarWith A s1 prog s3 := by
  induction h12 with
  | refl _ _ =>
      exact h23
  | tail s1 s2 sMid prog h_step _h_rest ih =>
      exact StepStarWith.tail s1 s2 s3 prog h_step (ih h23)

theorem StepStar.trans
  {s1 s2 s3 : oseair.State}
  {prog : oseair.Prog}
  (h12 : StepStar s1 prog s2)
  (h23 : StepStar s2 prog s3) :
  StepStar s1 prog s3 := by
  exact StepStarWith.trans h12 h23

theorem StepStarWith.of_runN_ok
  {A : oseair.AllocatorSpec}
  {n : Nat}
  {s s' : oseair.State}
  {prog : oseair.Prog}
  (h : oseair.runNWith A n s prog = oseair.Result.Ok s') :
  StepStarWith A s prog s' := by
  induction n generalizing s with
  | zero =>
      simp at h
      subst s'
      exact StepStarWith.refl s prog
  | succ n ih =>
      cases h_step : oseair.stepWith A s prog with
      | Err _ =>
          simp [oseair.runNWith, h_step] at h
      | Ok s1 =>
          simp [oseair.runNWith, h_step] at h
          exact StepStarWith.tail s s1 s' prog h_step (ih h)

theorem StepStar.of_runN_ok
  {n : Nat}
  {s s' : oseair.State}
  {prog : oseair.Prog}
  (h : oseair.runN n s prog = oseair.Result.Ok s') :
  StepStar s prog s' := by
  exact StepStarWith.of_runN_ok h

end obseq.proof
