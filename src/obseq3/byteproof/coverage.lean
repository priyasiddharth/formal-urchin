import obseq3.byteproof.correct

/-!
# Coverage: every program is in the fragment

The place predicates of the fragment are total: every place that is not
a projection is a `ChainB` (a deref of a deref recurses, a deref of a field
flattens nested fields by `derefNested`), and every projection is a field
of one, possibly nested. Every rvalue has an `RhsB` case and every
non-`halt` statement a `StmtB` case, so `StmtB` holds of every statement
and the fragment hypothesis of `compileB_correct_fragment` is discharged:
`compileB_correct_all` assumes only the two layout conditions.
-/

namespace obseq3.byteproof

open obseq3 obseq3.bytes obseq3.proof
open obseq3.compileB

theorem ChainB.deref_all {Γ : Ctx} :
    ∀ {τ : LayoutTy} (P : Place Γ (obseq.LayoutTy.PtrL τ)), ChainB (.deref P)
  | _, .local loc => .deref (.base loc)
  | _, .deref P => .deref (ChainB.deref_all P)
  | _, .proj (.local loc) f => .derefProj f (.base loc)
  | _, .proj (.deref P) f => .derefProj f (ChainB.deref_all P)
  | _, .proj (.proj b q) f => .derefNested (ChainB.deref_all (.proj b (q.append f)))
termination_by _ P => P.depth
decreasing_by all_goals (simp only [Place.depth]; omega)

theorem LeafSrcB.all {Γ : Ctx} : ∀ {τ : LayoutTy} (p : Place Γ τ), LeafSrcB p
  | _, .local loc => .chain (.base loc)
  | _, .deref P => .chain (ChainB.deref_all P)
  | _, .proj (.local loc) f => .field f (.base loc)
  | _, .proj (.deref P) f => .field f (ChainB.deref_all P)
  | _, .proj (.proj b q) f => .nested (LeafSrcB.all (.proj b (q.append f)))
termination_by _ p => p.depth
decreasing_by simp only [Place.depth]; omega

theorem ReadSrcB.all {Γ : Ctx} : ∀ {τ : LayoutTy} (p : Place Γ τ), ReadSrcB p
  | _, .local loc => .base (.chain (.base loc))
  | _, .deref P => .base (.chain (ChainB.deref_all P))
  | _, .proj (.local loc) f => .base (.field f (.base loc))
  | _, .proj (.deref P) f => .base (.field f (ChainB.deref_all P))
  | _, .proj (.proj b q) f => .nested (ReadSrcB.all (.proj b (q.append f)))
termination_by _ p => p.depth
decreasing_by simp only [Place.depth]; omega

theorem BorrowSrcB.all {Γ : Ctx} : ∀ {τ : LayoutTy} (p : Place Γ τ), BorrowSrcB p
  | _, .local loc => .local loc
  | _, .deref P => .deref (ChainB.deref_all P)
  | _, .proj (.local loc) f => .field f (.base loc)
  | _, .proj (.deref P) f => .field f (ChainB.deref_all P)
  | _, .proj (.proj b q) f => .nested (BorrowSrcB.all (.proj b (q.append f)))
termination_by _ p => p.depth
decreasing_by simp only [Place.depth]; omega

theorem RhsB.all {Γ : Ctx} {τ : LayoutTy} (rhs : RExpr Γ τ) : RhsB rhs := by
  cases rhs with
  | constInit v => exact .constInit v
  | copy p => exact .copy (ReadSrcB.all p)
  | move p => exact .move (BorrowSrcB.all p)
  | ref kind prot mask p => exact .ref kind prot mask (BorrowSrcB.all p)
  | ptrCast p => exact .ptrCast (LeafSrcB.all p)
  | ptrOffset p delta => exact .ptrOffset delta (LeafSrcB.all p)
  | refSlice kind prot p => exact .refSlice kind prot (LeafSrcB.all p)
  | sliceLen p => exact .sliceLen (ReadSrcB.all p)
  | subSlice p lo hi => exact .subSlice (ReadSrcB.all p) (ReadSrcB.all lo) (ReadSrcB.all hi)
  | exposeAddr p => exact .exposeAddr (LeafSrcB.all p)
  | fromExposed p => exact .fromExposed (LeafSrcB.all p)
  | uninit => exact .uninit
  | alloc len =>
      cases len with
      | const n => exact .allocConst n
      | fromPlace p => exact .allocDyn (ReadSrcB.all p)
  | binOp op a b => exact .binOp op (ReadSrcB.all a) (ReadSrcB.all b)

theorem StmtB0.assign_all {Γ : Ctx} :
    ∀ {τ : LayoutTy} (dst : Place Γ τ) (rhs : RExpr Γ τ), StmtB0 (.assign dst rhs)
  | _, .local loc, rhs => .assign (.local loc) (RhsB.all rhs)
  | _, .deref P, rhs => .assign (.deref (ChainB.deref_all P)) (RhsB.all rhs)
  | _, .proj (.local loc) f, rhs => .assign (.projLocal loc f) (RhsB.all rhs)
  | _, .proj (.deref P) f, rhs => .assign (.projDeref f (ChainB.deref_all P)) (RhsB.all rhs)
  | _, .proj (.proj b q) f, rhs => .nested (StmtB0.assign_all (.proj b (q.append f)) rhs)
termination_by _ dst => dst.depth
decreasing_by simp only [Place.depth]; omega

theorem StmtB.all {Γ : Ctx} (stmt : Stmt Γ) (h : stmt ≠ .halt) : StmtB stmt := by
  cases stmt with
  | assign dst rhs => exact .base (StmtB0.assign_all dst rhs)
  | assignIf discr val dst rhs => exact .assignIf (ReadSrcB.all discr) (StmtB0.assign_all dst rhs)
  | dealloc p => exact .base (.dealloc (ReadSrcB.all p))
  | pushProtectors => exact .base .pushProtectors
  | popProtectors => exact .base .popProtectors
  | halt => exact absurd rfl h

/-- **Byte-level compiler correctness.** If every pointer-typed place has
    a pointer-sized layout and every integer- or pointer-typed place a
    one-leaf layout, and `prog` compiles, then every successful source run
    from the initial state is matched by a successful target run from the
    initial state, the two related by the byte invariant at the
    statement-prefix compile state. -/
theorem compileB_correct_all {Γ : Ctx} (L : mirliteB.LayEnv Γ) (hWF : PtrPlacesWF L)
    (hLeaf : LeafWF L)
    (prog : Prog Γ) (compProg : oseairL.Prog) (h_comp : compileProg L prog = .ok compProg)
    (n : Nat) {s_mir' : mirliteB.State MSB Γ}
    (h_run : mirliteB.runN MSB L n (mirliteB.State.initial MSB Γ) prog = .ok s_mir') :
    ∃ (ρt : TagRenameMap) (s_osea' : oseairL.State MSB) (m : Nat),
      oseairL.runN MSB m (oseairL.State.initial MSB) compProg = .Ok s_osea' ∧
      InvAtB L ρt s_mir' s_osea' (csAtB L (initialState Γ) prog s_mir'.pc) :=
  compileB_correct_fragment L hWF hLeaf prog compProg h_comp
    (fun stmt _ h_nh => StmtB.all stmt h_nh) n h_run

/-! ## The conditions hold for the uniform layout -/

theorem ofLayoutTyList_getD : ∀ (ts : List LayoutTy) (i : Fin ts.length),
    (ofLayoutTyList ts).getD i.1 default = ofLayoutTy (ts.get i)
  | _ :: _, ⟨0, _⟩ => rfl
  | _ :: ts, ⟨i + 1, h⟩ => ofLayoutTyList_getD ts ⟨i, Nat.lt_of_succ_lt_succ h⟩

theorem fieldLayout_ofLayoutTy {ρ τ : LayoutTy} (path : PathTo ρ τ) :
    mirliteB.fieldLayout (ofLayoutTy ρ) path.indices = ofLayoutTy τ := by
  induction path with
  | nil => rfl
  | field idx tail ih =>
      simp only [PathTo.indices, ofLayoutTy, reprC, mirliteB.fieldLayout, ofLayoutTyList_getD]
      exact ih

theorem placeLayout_uniform {Γ : Ctx} {τ : LayoutTy} (p : Place Γ τ) :
    mirliteB.placeLayout (mirliteB.uniformEnv Γ) p = ofLayoutTy τ := by
  induction p with
  | «local» loc => simp only [mirliteB.placeLayout, mirliteB.uniformEnv, loc.hTy]
  | proj b path ih => simp only [mirliteB.placeLayout, ih, fieldLayout_ofLayoutTy]
  | deref p ih => simp only [mirliteB.placeLayout, ih, ofLayoutTy]

theorem uniformEnv_ptrWF (Γ : Ctx) : PtrPlacesWF (mirliteB.uniformEnv Γ) := fun p => by
  rw [placeLayout_uniform]; rfl

theorem uniformEnv_leafWF (Γ : Ctx) : LeafWF (mirliteB.uniformEnv Γ) :=
  ⟨fun p => by rw [placeLayout_uniform]; rfl, fun p => by rw [placeLayout_uniform]; rfl⟩

/-- **Byte-level compiler correctness, at the uniform layout** (every
    scalar and pointer an 8-byte leaf): no hypotheses beyond compilation. -/
theorem compileB_correct_uniform {Γ : Ctx} (prog : Prog Γ) (compProg : oseairL.Prog)
    (h_comp : compileProg (mirliteB.uniformEnv Γ) prog = .ok compProg)
    (n : Nat) {s_mir' : mirliteB.State MSB Γ}
    (h_run : mirliteB.runN MSB (mirliteB.uniformEnv Γ) n (mirliteB.State.initial MSB Γ) prog
      = .ok s_mir') :
    ∃ (ρt : TagRenameMap) (s_osea' : oseairL.State MSB) (m : Nat),
      oseairL.runN MSB m (oseairL.State.initial MSB) compProg = .Ok s_osea' ∧
      InvAtB (mirliteB.uniformEnv Γ) ρt s_mir' s_osea'
        (csAtB (mirliteB.uniformEnv Γ) (initialState Γ) prog s_mir'.pc) :=
  compileB_correct_all _ (uniformEnv_ptrWF Γ) (uniformEnv_leafWF Γ) prog compProg h_comp n h_run

end obseq3.byteproof
