import obseq3.byteproof.program
import obseq3.byteproof.const_write

/-!
# The proved fragment

Which statements the byte-level proof covers, as predicates, and the
lemma turning each into a `StmtSimB` — so `compileB_correct_fragment` is
the program theorem for every program in the fragment. Not yet covered:
`assignIf`, nested projections (`x.f.g`), derefs of non-chain places, and
the one-leaf rvalues / `refSlice` with a FIELD operand.
-/

namespace obseq3.byteproof

open obseq3 obseq3.bytes obseq3.proof
open obseq3.mirlite (MemValue Binding Env PlaceRes)
open obseq3.oseair (Val Register)
open obseq3.compileB

/-- Places that can be borrowed (`ref`, `move`): a local, a deref chain,
    a field of a chain. -/
inductive BorrowSrcB {Γ : Ctx} : {τ : LayoutTy} → Place Γ τ → Prop
  | local {τ : LayoutTy} (loc : Local Γ τ) : BorrowSrcB (.local loc)
  | deref {σ : LayoutTy} {q : Place Γ (obseq.LayoutTy.PtrL σ)} :
      PtrChain (.deref q) → BorrowSrcB (.deref q)
  | field {ρ τ : LayoutTy} {b : Place Γ ρ} (f : PathTo ρ τ) : PtrChain b → BorrowSrcB (.proj b f)

/-- The rvalues covered, with their operand shapes. -/
inductive RhsB {Γ : Ctx} : {τ : LayoutTy} → RExpr Γ τ → Prop
  | constInit (v : Word) : RhsB (.constInit v)
  | uninit {τ : LayoutTy} : RhsB (τ := τ) .uninit
  | copy {τ : LayoutTy} {src : Place Γ τ} : ReadSrcB src → RhsB (.copy src)
  | move {τ : LayoutTy} {src : Place Γ τ} : BorrowSrcB src → RhsB (.move src)
  | ref {τ : LayoutTy} {src : Place Γ τ} (kind : RefKind) (prot : Bool) (mask : List Bool) :
      BorrowSrcB src → RhsB (.ref kind prot mask src)
  | ptrCast {σ τ : LayoutTy} {src : Place Γ (obseq.LayoutTy.PtrL σ)} :
      PtrChain src → RhsB (.ptrCast (τ := τ) src)
  | ptrOffset {σ τ : LayoutTy} {src : Place Γ (obseq.LayoutTy.PtrL σ)} (delta : Int) :
      PtrChain src → RhsB (.ptrOffset (τ := τ) src delta)
  | refSlice {σ τ : LayoutTy} {src : Place Γ (obseq.LayoutTy.PtrL σ)} (kind : RefKind)
      (prot : Bool) : PtrChain src → RhsB (.refSlice (τ := τ) kind prot src)
  | exposeAddr {σ : LayoutTy} {src : Place Γ (obseq.LayoutTy.PtrL σ)} :
      PtrChain src → RhsB (.exposeAddr src)
  | fromExposed {τ : LayoutTy} {src : Place Γ obseq.LayoutTy.NatL} :
      PtrChain src → RhsB (.fromExposed (τ := τ) src)
  | sliceLen {σ : LayoutTy} {src : Place Γ (obseq.LayoutTy.PtrL σ)} :
      ReadSrcB src → RhsB (.sliceLen src)
  | subSlice {σ : LayoutTy} {src : Place Γ (obseq.LayoutTy.PtrL σ)}
      {lo hi : Place Γ obseq.LayoutTy.NatL} :
      ReadSrcB src → ReadSrcB lo → ReadSrcB hi → RhsB (.subSlice src lo hi)
  | allocConst {τ : LayoutTy} (n : Nat) : RhsB (.alloc (τ := τ) (.const n))
  | allocDyn {τ : LayoutTy} {p : Place Γ obseq.LayoutTy.NatL} :
      ReadSrcB p → RhsB (.alloc (τ := τ) (.fromPlace p))
  | binOp (op : BinOp) {a b : Place Γ obseq.LayoutTy.NatL} :
      ReadSrcB a → ReadSrcB b → RhsB (.binOp op a b)

theorem RhsB.pkg {Γ : Ctx} {L : mirliteB.LayEnv Γ} {compProg : oseairL.Prog}
    (hWF : PtrPlacesWF L) {τ : LayoutTy} {rhs : RExpr Γ τ} (h : RhsB rhs) (dstL : BLayout) :
    ValuePkgB compProg L dstL rhs := by
  cases h with
  | constInit v => exact constInit_pkg dstL v
  | uninit => exact uninit_pkg dstL
  | copy h => exact copy_pkgR hWF dstL h
  | move h =>
      cases h with
      | «local» loc => exact move_local_pkg hWF loc dstL
      | deref hc => exact move_deref_pkg hWF hc dstL
      | field f hc => exact move_proj_pkg hWF f hc dstL
  | ref kind prot mask h =>
      cases h with
      | «local» loc => exact ref_local_pkg hWF loc dstL kind prot mask
      | deref hc => exact ref_deref_pkg hWF hc dstL kind prot mask
      | field f hc => exact ref_proj_pkg hWF f hc dstL kind prot mask
  | ptrCast h => exact ptrCast_pkg hWF dstL h
  | ptrOffset delta h => exact ptrOffset_pkg hWF dstL h delta
  | refSlice kind prot h => exact refSlice_pkg hWF dstL kind prot h
  | exposeAddr h => exact exposeAddr_pkg hWF dstL h
  | fromExposed h => exact fromExposed_pkg hWF dstL h
  | sliceLen h => exact sliceLen_pkg hWF dstL h
  | subSlice h1 h2 h3 => exact subSlice_pkg hWF dstL h1 h2 h3
  | allocConst n => exact alloc_const_pkg dstL n
  | allocDyn h => exact alloc_dyn_pkg hWF dstL h
  | binOp op ha hb => exact binOp_pkg hWF dstL op ha hb

/-- The destinations covered. -/
inductive DstB {Γ : Ctx} : {τ : LayoutTy} → Place Γ τ → Prop
  | local {τ : LayoutTy} (loc : Local Γ τ) : DstB (.local loc)
  | deref {τ : LayoutTy} {P : Place Γ (obseq.LayoutTy.PtrL τ)} :
      PtrChain (.deref P) → DstB (.deref P)
  | projLocal {ρ τ : LayoutTy} (loc : Local Γ ρ) (f : PathTo ρ τ) : DstB (.proj (.local loc) f)
  | projDeref {ρ τ : LayoutTy} {P : Place Γ (obseq.LayoutTy.PtrL ρ)} (f : PathTo ρ τ) :
      PtrChain (.deref P) → DstB (.proj (.deref P) f)

/-- The statements covered. -/
inductive StmtB {Γ : Ctx} : Stmt Γ → Prop
  | assign {τ : LayoutTy} {dst : Place Γ τ} {rhs : RExpr Γ τ} :
      DstB dst → RhsB rhs → StmtB (.assign dst rhs)
  | pushProtectors : StmtB .pushProtectors
  | popProtectors : StmtB .popProtectors
  | dealloc {σ : LayoutTy} {dst : Place Γ (obseq.LayoutTy.PtrL σ)} :
      ReadSrcB dst → StmtB (.dealloc dst)

theorem StmtB.sim {Γ : Ctx} {L : mirliteB.LayEnv Γ} {compProg : oseairL.Prog}
    (hWF : PtrPlacesWF L) {stmt : Stmt Γ} (h : StmtB stmt) : StmtSimB L compProg stmt := by
  intro ρt s_mir s_mir' s_osea cs h_inv h_code h_step
  cases h with
  | assign hd hr =>
      cases hd with
      | «local» loc =>
          cases h_env : s_mir.env.lookup loc with
          | none =>
              exact storereg_localfresh_simB compProg (hr.pkg hWF _) h_inv h_code h_env h_step
          | some b =>
              exact storereg_local_simB compProg (hr.pkg hWF _) h_inv h_code h_env h_step
      | deref hc =>
          exact storereg_chaindst_simB compProg hWF hc (hr.pkg hWF _) h_inv h_code h_step
      | projLocal loc f =>
          cases h_env : s_mir.env.lookup loc with
          | none =>
              exact storereg_projlocalfresh_simB compProg hWF (hr.pkg hWF _) h_inv h_code h_env
                h_step
          | some b =>
              exact storereg_projlocal_simB compProg hWF h_env (hr.pkg hWF _) h_inv h_code h_step
      | projDeref f hc =>
          exact storereg_projchain_simB compProg hWF hc (hr.pkg hWF _) h_inv h_code h_step
  | pushProtectors => exact pushProt_simB compProg h_inv h_code h_step
  | popProtectors => exact popProt_simB compProg h_inv h_code h_step
  | dealloc hd => exact dealloc_simB compProg hWF hd h_inv h_code h_step

/-- **Byte-level compiler correctness, for the proved fragment.** If every
    pointer-typed place has a pointer-sized layout, `prog` compiles, and
    every non-halt statement of `prog` is in the fragment, then every
    successful source run from the initial state is matched by a
    successful target run from the initial state, the two related by the
    byte invariant at the statement-prefix compile state. -/
theorem compileB_correct_fragment {Γ : Ctx} (L : mirliteB.LayEnv Γ) (hWF : PtrPlacesWF L)
    (prog : Prog Γ) (compProg : oseairL.Prog) (h_comp : compileProg L prog = .ok compProg)
    (h_frag : ∀ stmt, stmt ∈ prog → stmt ≠ .halt → StmtB stmt)
    (n : Nat) {s_mir' : mirliteB.State MSB Γ}
    (h_run : mirliteB.runN MSB L n (mirliteB.State.initial MSB Γ) prog = .ok s_mir') :
    ∃ (ρt : TagRenameMap) (s_osea' : oseairL.State MSB) (m : Nat),
      oseairL.runN MSB m (oseairL.State.initial MSB) compProg = .Ok s_osea' ∧
      InvAtB L ρt s_mir' s_osea' (csAtB L (initialState Γ) prog s_mir'.pc) :=
  compileB_correct L prog compProg h_comp
    (fun stmt h_mem h_nh => (h_frag stmt h_mem h_nh).sim hWF) n h_run

end obseq3.byteproof
