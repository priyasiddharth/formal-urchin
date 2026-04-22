# Plan for Obseq v2


## Goal
Design obseq v2 so compiler-correctness proofs are shorter, more uniform, and easier to extend than the current version.
The main strategy is to make typing, framing, and permission interfaces explicit first, then add instruction families in phases.

## Changes
1. Move to a typed MIR AST.
	Use a phased typed MIR rather than a fully intrinsic encoding all at once.
	Concretely, the goal is to move from statements that are only checked externally, such as `_0 = copy _1`, to statements whose operands already carry the layout they are supposed to have, such as `_0 : <ty> = copy (_1 : <ty>)`.
	The goal is not to move to proof-carrying syntax or to encode every well-formedness condition in the term itself.
	The goal is to make the type and layout information that is currently implicit and recovered later by side conditions explicit in the AST.
	That is already stronger than the current syntax: the AST records the layout of each place and expression, so ill-typed combinations such as assigning a pointer-valued expression to a word-typed place are not even representable.
	This matters because the compiler and local simulation lemmas can read the expected layout directly from the term, instead of re-deriving it later from separate typing judgments.
	A representative shape is:
	```lean
	inductive Place (Γ : Ctx) : LayoutTy → Type
	| local : Γ.HasType x τ → Place Γ τ
	| proj  : Place Γ τ -> PathTo τ τ' -> Place Γ τ'

	inductive RExpr (Γ : Ctx) : LayoutTy → Type
	| constInit : Word -> RExpr Γ (.WordL)
	| ref   : RefKind -> Place Γ τ -> RExpr Γ (.PtrL τ)
	| deref : Place Γ (.PtrL τ) -> RExpr Γ τ

	inductive Stmt (Γ : Ctx) : Type
	| assign : Place Γ τ -> RExpr Γ τ -> Stmt Γ
	```
	The exact details may change, but the important point is that the layout index is part of the AST, not recovered later by side conditions.
	Places should be path-aware from day one so projections are not a later retrofit.

2. Represent non-interference as a bundled invariant.
	Replace ad hoc non-interference threading with one invariant package, likely a refinement of `TargetNonInterference`, with named fields for:
	- frame preservation of untouched tracked blocks
	- allocator freshness and next-allocation safety
	- temp-region disjointness
	- address and tag rename stability
	Every local simulation theorem should take this invariant as input and return its post-state version.
	`CompilerInv` should store this package directly.
	The intended style is closer to explicit CompCert-like disjointness than to a full separation-logic layer: package concrete footprint and freshness facts in one record, rather than introducing a general separating conjunction.
	A reasonable sketch is:
	```lean
	structure Footprint where
	  base : Word
	  size : Nat

	def Footprint.contains (fp : Footprint) (a : Word) : Prop :=
	  ∃ i, i < fp.size ∧ a = fp.base + i

	def Footprint.disjoint (fp₁ fp₂ : Footprint) : Prop :=
	  ∀ a, fp₁.contains a -> fp₂.contains a -> False

	def PlaceFootprint
	  (addr : Word)
	  (layout : LayoutTy) : Footprint :=
	  { base := addr, size := blockSize layout }

	structure FrameInv
	  (π : PlaceMap)
	  (ρa : AddrRenameMap)
	  (ρt : TagRenameMap)
	  (s_mir : mirlite.State)
	  (s_osea : oseair.State) : Prop where
	  tracked_blocks_disjoint :
	    ∀ base₁ reg₁ layout₁ base₂ reg₂ layout₂,
	      π.lookup base₁ = some (reg₁, layout₁) ->
	      π.lookup base₂ = some (reg₂, layout₂) ->
	      base₁ ≠ base₂ ->
	      ∀ addr₁_m addr₁_o tag₁_m tag₁_o addr₂_m addr₂_o tag₂_m tag₂_o,
	        place_runtime_sim π ρa ρt s_mir s_osea base₁ reg₁ addr₁_m addr₁_o tag₁_m tag₁_o layout₁ ->
	        place_runtime_sim π ρa ρt s_mir s_osea base₂ reg₂ addr₂_m addr₂_o tag₂_m tag₂_o layout₂ ->
	        Footprint.disjoint (PlaceFootprint addr₁_m layout₁) (PlaceFootprint addr₂_m layout₂) ∧
	        Footprint.disjoint (PlaceFootprint addr₁_o layout₁) (PlaceFootprint addr₂_o layout₂)
	  next_alloc_fresh :
	    ∀ sz, NextAllocClear (A_o := oseair.bumpAllocator) ρa s_osea sz
	  rename_below_frontier :
	    TargetAddrRenameBelowAddrStart ρa s_osea
	  nonempty_stacks_below_frontier :
	    TargetNonemptyStacksBelowAddrStart s_osea
	```
	This is only a repackaging of what the current proof development already uses.
	The point is to move from scattered lemmas such as `blocks_disjoint`, `StateSim.disjoint`, `NextAllocClear`, and `TargetNonInterference` to one theorem-facing frame package with named fields.
	If this works well, `blocks_disjoint` can either remain the primitive notion and `Footprint.disjoint` can be a thin wrapper around it, or v2 can switch entirely to footprints and prove the current lemmas as compatibility lemmas.
	The expected benefit is not more abstraction for its own sake. It is that local preservation theorems can say they preserve one `FrameInv` package, instead of manually reconstructing disjointness, freshness, and frontier facts each time.
	For the initial v2 design, prefer this explicit footprint and frame-invariant style over introducing Iris.
	Iris is worth revisiting only if the permission-module boundary starts needing substantially more abstract ownership reasoning, ghost state, or modular client-style specifications than the current compiler-correctness argument requires.

3. Keep stacked borrows as a module.
	Stacked borrows should remain the first backend, but the compiler and proofs should depend only on a permission-module interface exposing the operations and laws they need.
	That keeps the permission model swappable without forcing a redesign of the compiler proof.

4. Additional areas to prioritize.
	- Support projected places from day one, using the path-aware pattern already visible in `StructInitExistingCtx`, instead of repeating the current base-only shape in ref and deref proofs.
	- Keep phase 1 intentionally narrow: support projections, but do not take on structs yet.
	- Refactor proof helpers so alloc, memcpy, writeback, and frame-preservation lemmas are reused systematically.
	- Add symbolic execution support for short OSEA fragments early, so target-execution proofs stop being bespoke scripts.
	- Make cleanup and temporary lifetime explicit in the design, so v2 does not repeat the current deref mismatch between the compiler and proof.
	- Keep allocator reasoning abstract instead of baking in bump-allocator-specific behavior.
	- Do not add new axioms without explicit review.

## Phases
0. Freeze interfaces.
	Define the v2 typed syntax, the permission-module interface, the bundled non-interference invariant, and the standard return shape for local simulation theorems.

1. Build the typed core around `constinit`, `ref`, and `deref`.
	Implement typed, path-aware versions of `constinit`, `ref`, and `deref` first.
	Phase 1 should already support projected places, but it should explicitly defer structs and other aggregates.
	This keeps the syntax and proofs focused on the core permission-sensitive operations that motivated obseq in the first place.
	Deliverable: one uniform compiler/simulation theorem family for typed `constinit`, `ref`, and `deref`, including projected-place cases.

2. Rebuild shared proof infrastructure.
	Simplify `StateSim` and split helper lemmas into reusable pieces for alloc, load, memcpy, writeback, and frame preservation.
	At this stage, decide whether `blocks_disjoint` remains the primitive relation or whether v2 moves to an explicit `Footprint.disjoint` wrapper and derives the current lemmas from it.
	Add symbolic execution support for short OSEA fragments so `osea_run_ok` style proofs become routine.

3. Lift local theorems to compiler composition.
	Rebuild `CompilerInv` around the new invariant package and make every supported instruction theorem return the same kind of result package.
	Only after phases 1 and 2 are stable should v2 restate and prove the whole-program step theorem for the supported typed core.

4. Expand coverage iteratively.
	Add copy, fresh-destination variants, and richer aggregate operations next.
	Structs should enter here rather than in phase 1.
	Defer loops, branches, methods, and separate compilation until the straight-line permission-sensitive fragment is stable.

## Success Criteria
- Each phase should expose one standard theorem shape rather than a new bespoke proof interface.
- Phase 1 should include at least one projected-place example in each of `constinit`, `ref`, and `deref`, so path-aware from day one is tested rather than only claimed.
- The dereference compiler fragment and dereference execution proof should be literally the same instruction sequence, including `Die`.
- Fresh-allocation proofs should stay abstract over allocator results.
- The whole-program theorem should no longer need ad hoc temp-safety recovery lemmas outside the uniform local result package.

## Starting Points
- `mirlite.lean` for the current source syntax and semantics
- `compile.lean` for lowering hooks that should survive the redesign
- `proof/core.lean` and `proof/state_helpers.lean` for the simulation and invariant layer that need to be simplified
- `proof/struct_init_existing.lean` as the best current template for path-aware contexts
- `proof/compiler.lean` as the integration target, not the starting point


