import obseq2.proof.common

namespace obseq2.proof

open obseq2
open obseq2.compile
open obseq2.oseair (Instr Register Rhs Val)

theorem CompilerInv_step_ref
    {Γ : Ctx} {τ : LayoutTy} {cs0 : CompilerState} {prog : obseq2.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_mir' : obseq2.mirlite.State PermissionModel.stackedBorrows Γ}
    {s_osea : oseair.State}
    {dst : Place Γ (obseq.LayoutTy.PtrL τ)} {src : Place Γ τ}
    (kind : RefKind)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    (h_stmt : prog.get? s_mir.pc = some (.assign dst (.ref kind src)))
    (h_step : obseq2.mirlite.stepStmt PermissionModel.stackedBorrows s_mir
                (.assign dst (.ref kind src)) = .ok s_mir') :
    ∃ (s_osea' : oseair.State) (n : Nat),
      oseair.runN n s_osea (compileProgFrom cs0 prog) = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa ρt s_mir' s_osea' := by
  sorry

end obseq2.proof
