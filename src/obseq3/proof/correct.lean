import obseq3.proof.check

/-!
# Compiler correctness, for the proved fragment

The statements covered (`StmtB`): every `StmtB0` statement (assignments to
locals, fields at any depth and pointer chains of the covered rvalues;
dealloc; protector push/pop), and `check` of a read source.
-/

namespace obseq3.proof

open obseq3 obseq3.bytes obseq3.proof
open obseq3.mirlite (MemValue Binding Env PlaceRes)
open obseq3.oseair (Val Register)
open obseq3.compile

inductive StmtB {Γ : Ctx} : Stmt Γ → Prop
  | base {stmt : Stmt Γ} : StmtB0 stmt → StmtB stmt
  | check {discr : Place Γ (LayoutTy.IntL tN)} {vals : List Word} {member : Bool} :
      ReadSrcB discr → StmtB (.check discr vals member)

theorem StmtB.sim {Γ : Ctx} {L : mirlite.LayEnv Γ} {compProg : oseair.Prog}
    (hWF : PtrPlacesWF L) (hLeaf : LeafWF L) {stmt : Stmt Γ} (h : StmtB stmt) :
    StmtSimB L compProg stmt := by
  cases h with
  | base h0 => exact h0.sim hWF hLeaf
  | check hd => exact check_simB hWF hd

/-- **Compiler correctness, for the proved fragment.** If every
    pointer-typed place has a pointer-sized layout, `prog` compiles, and
    every non-halt statement of `prog` is in the fragment, then every
    successful source run from the initial state is matched by a
    successful target run from the initial state, the two related by the
    byte invariant at the statement-prefix compile state. -/
theorem compile_correct_fragment {Γ : Ctx} (L : mirlite.LayEnv Γ) (hWF : PtrPlacesWF L)
    (hLeaf : LeafWF L)
    (prog : Prog Γ) (compProg : oseair.Prog) (h_comp : compileProg L prog = .ok compProg)
    (h_frag : ∀ stmt, stmt ∈ prog → stmt ≠ .halt → StmtB stmt)
    (n : Nat) {s_mir' : mirlite.State MSB Γ}
    (h_run : mirlite.runN MSB L n (mirlite.State.initial MSB Γ) prog = .ok s_mir') :
    ∃ (ρt : TagRenameMap) (s_osea' : oseair.State MSB) (m : Nat),
      oseair.runN MSB m (oseair.State.initial MSB) compProg = .Ok s_osea' ∧
      InvAtB L ρt s_mir' s_osea' (csAtB L (initialState Γ) prog s_mir'.pc) :=
  compile_correct L prog compProg h_comp
    (fun stmt h_mem h_nh => (h_frag stmt h_mem h_nh).sim hWF hLeaf) n h_run

end obseq3.proof
