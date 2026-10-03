import obseq3.byteproof.assignif

/-!
# Byte-level compiler correctness, for the proved fragment

The statements covered (`StmtB`): every `StmtB0` statement (assignments to
locals, fields at any depth and pointer chains of the covered rvalues;
dealloc; protector push/pop), and the guarded assignment `assignIf` whose
discriminant is a read source and whose body is a covered assignment.
-/

namespace obseq3.byteproof

open obseq3 obseq3.bytes obseq3.proof
open obseq3.mirlite (MemValue Binding Env PlaceRes)
open obseq3.oseair (Val Register)
open obseq3.compileB

inductive StmtB {Γ : Ctx} : Stmt Γ → Prop
  | base {stmt : Stmt Γ} : StmtB0 stmt → StmtB stmt
  | assignIf {τ : LayoutTy} {discr : Place Γ obseq.LayoutTy.NatL} {val : Word}
      {dst : Place Γ τ} {rhs : RExpr Γ τ} :
      ReadSrcB discr → StmtB0 (.assign dst rhs) → StmtB (.assignIf discr val dst rhs)

theorem StmtB.sim {Γ : Ctx} {L : mirliteB.LayEnv Γ} {compProg : oseairL.Prog}
    (hWF : PtrPlacesWF L) (hLeaf : LeafWF L) {stmt : Stmt Γ} (h : StmtB stmt) :
    StmtSimBc L compProg stmt := by
  cases h with
  | base h0 => exact (h0.sim hWF hLeaf).toC
  | assignIf hd hb =>
      intro ρt s_mir s_mir' s_osea cs h_inv h_ok h_code h_step
      obtain ⟨v, hv⟩ := h_ok
      exact assignIf_simB hWF hd (hb.sim hWF hLeaf) h_inv hv h_code h_step

/-- **Byte-level compiler correctness, for the proved fragment.** If every
    pointer-typed place has a pointer-sized layout, `prog` compiles, and
    every non-halt statement of `prog` is in the fragment, then every
    successful source run from the initial state is matched by a
    successful target run from the initial state, the two related by the
    byte invariant at the statement-prefix compile state. -/
theorem compileB_correct_fragment {Γ : Ctx} (L : mirliteB.LayEnv Γ) (hWF : PtrPlacesWF L)
    (hLeaf : LeafWF L)
    (prog : Prog Γ) (compProg : oseairL.Prog) (h_comp : compileProg L prog = .ok compProg)
    (h_frag : ∀ stmt, stmt ∈ prog → stmt ≠ .halt → StmtB stmt)
    (n : Nat) {s_mir' : mirliteB.State MSB Γ}
    (h_run : mirliteB.runN MSB L n (mirliteB.State.initial MSB Γ) prog = .ok s_mir') :
    ∃ (ρt : TagRenameMap) (s_osea' : oseairL.State MSB) (m : Nat),
      oseairL.runN MSB m (oseairL.State.initial MSB) compProg = .Ok s_osea' ∧
      InvAtB L ρt s_mir' s_osea' (csAtB L (initialState Γ) prog s_mir'.pc) :=
  compileB_correct L prog compProg h_comp
    (fun stmt h_mem h_nh => (h_frag stmt h_mem h_nh).sim hWF hLeaf) n h_run

end obseq3.byteproof
