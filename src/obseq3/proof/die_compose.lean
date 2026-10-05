import obseq3.proof.coverage
import obseq3.proof.layoutagree
import obseq3.proof.die_elision

/-!
# Compiler correctness into OSEA-IR_B

`compile_correct_*` composed with `die_elision`: a successful mirlite run
is matched by a successful run of the compiled program on OSEA-IR_B (every
`Die` a no-op), in the same number of target steps, ending at the same pc,
registers and memory as the OSEA-IR run that the boundary invariant
`InvAtB` relates to the source.
-/

namespace obseq3.proof

open obseq3 obseq3.compile

theorem compile_correct_noDie_all {Γ : Ctx} (L : mirlite.LayEnv Γ) (hWF : PtrPlacesWF L)
    (hLeaf : LeafWF L)
    (prog : Prog Γ) (compProg : oseair.Prog) (h_comp : compileProg L prog = .ok compProg)
    (n : Nat) {s_mir' : mirlite.State MSB Γ}
    (h_run : mirlite.runN MSB L n (mirlite.State.initial MSB Γ) prog = .ok s_mir') :
    ∃ (ρt : TagRenameMap) (s_osea' : oseair.State MSB) (s_b : oseair.State MSB_B) (m : Nat),
      oseair.runN MSB m (oseair.State.initial MSB) compProg = .Ok s_osea' ∧
      InvAtB L ρt s_mir' s_osea' (csAtB L (initialState Γ) prog s_mir'.pc) ∧
      oseair.runN MSB_B m (oseair.State.initial MSB_B) compProg = .Ok s_b ∧
      s_b.pc = s_osea'.pc ∧ s_b.reg = s_osea'.reg ∧ s_b.mem = s_osea'.mem := by
  obtain ⟨ρt, s_osea', m, h_t, h_inv⟩ :=
    compile_correct_all L hWF hLeaf prog compProg h_comp n h_run
  obtain ⟨s_b, h_b, h1, h2, h3⟩ := die_elision compProg m h_t
  exact ⟨ρt, s_osea', s_b, m, h_t, h_inv, h_b, h1, h2, h3⟩

theorem compile_correct_noDie_agrees {Γ : Ctx} (L : mirlite.LayEnv Γ) (hL : LocalsAgree L)
    (prog : Prog Γ) (compProg : oseair.Prog) (h_comp : compileProg L prog = .ok compProg)
    (n : Nat) {s_mir' : mirlite.State MSB Γ}
    (h_run : mirlite.runN MSB L n (mirlite.State.initial MSB Γ) prog = .ok s_mir') :
    ∃ (ρt : TagRenameMap) (s_osea' : oseair.State MSB) (s_b : oseair.State MSB_B) (m : Nat),
      oseair.runN MSB m (oseair.State.initial MSB) compProg = .Ok s_osea' ∧
      InvAtB L ρt s_mir' s_osea' (csAtB L (initialState Γ) prog s_mir'.pc) ∧
      oseair.runN MSB_B m (oseair.State.initial MSB_B) compProg = .Ok s_b ∧
      s_b.pc = s_osea'.pc ∧ s_b.reg = s_osea'.reg ∧ s_b.mem = s_osea'.mem :=
  compile_correct_noDie_all L hL.ptrWF hL.leafWF prog compProg h_comp n h_run

theorem compile_correct_noDie_uniform {Γ : Ctx} (prog : Prog Γ) (compProg : oseair.Prog)
    (h_comp : compileProg (mirlite.uniformEnv Γ) prog = .ok compProg)
    (n : Nat) {s_mir' : mirlite.State MSB Γ}
    (h_run : mirlite.runN MSB (mirlite.uniformEnv Γ) n (mirlite.State.initial MSB Γ) prog
      = .ok s_mir') :
    ∃ (ρt : TagRenameMap) (s_osea' : oseair.State MSB) (s_b : oseair.State MSB_B) (m : Nat),
      oseair.runN MSB m (oseair.State.initial MSB) compProg = .Ok s_osea' ∧
      InvAtB (mirlite.uniformEnv Γ) ρt s_mir' s_osea'
        (csAtB (mirlite.uniformEnv Γ) (initialState Γ) prog s_mir'.pc) ∧
      oseair.runN MSB_B m (oseair.State.initial MSB_B) compProg = .Ok s_b ∧
      s_b.pc = s_osea'.pc ∧ s_b.reg = s_osea'.reg ∧ s_b.mem = s_osea'.mem :=
  compile_correct_noDie_all _ (uniformEnv_ptrWF Γ) (uniformEnv_leafWF Γ) prog compProg h_comp n h_run

end obseq3.proof
