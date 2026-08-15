import obseq3.proof.common

namespace obseq3.proof

open obseq3
open obseq3.compile
open obseq3.oseair (Instr Register Rhs Val)

/-- LEAF SORRY 2: per-statement simulation for `.assign dst (.copy src)`.
    Target fragment: `[dst lowering (Mut)] [src lowering (Shared)]
    Memcpy [src cleanup] [dst cleanup]`. Beyond the const-write obligations
    this needs: a `Memcpy` analog of BRIDGE 2 over `blockSize τ` cells
    (source: `M.read` at the src range then the `useMut` write; target:
    `Memcpy`'s read-then-useMut — the same two events); the `M.read`
    transport through `PermSim` (BRIDGE 3 family); and BRIDGE 1 for both
    lowerings' Borrow/Die pairs. Renames grow by `.refl`: copy mints no
    source tag, and all target-internal tags are died. -/
theorem CompilerInv_step_copy
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {τ : LayoutTy}
    {dst src : Place Γ τ}
    (compProg : oseair.Prog)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    (h_stmt : prog.get? s_mir.pc = some (.assign dst (.copy src)))
    (h_step : mirlite.stepStmt MSB s_mir (.assign dst (.copy src)) = .ok s_mir') :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' := by
  sorry

end obseq3.proof
