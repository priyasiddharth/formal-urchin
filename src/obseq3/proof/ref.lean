import obseq3.proof.common

namespace obseq3.proof

open obseq3
open obseq3.compile
open obseq3.oseair (Instr Register Rhs Val)

/-- LEAF SORRY 3: per-statement simulation for
    `.assign dst (.ref kind prot mask src)` (v3 signature carries the
    protector flag and freeze mask; both land verbatim in the emitted
    `Borrow`, so no separate faithfulness obligation arises).

    This is the only case that grows ρt: both machines call `M.ref` on
    `PermSim`-related states whose counters satisfy only `NextTag ≤`, so the
    fresh tags DIFFER — the case extends ρt with the pair
    `ρt' srcFresh = some tgtFresh`. `TagRenameWF` is preserved because both
    sides mint strictly above every previously mapped tag (counters are
    monotone), and the wildcard mapping is untouched (fresh tags are ≥ 1).
    Obligations: the `sb_ref` transport through `PermSim` extended at the
    fresh pair (BRIDGE 3 family, the genuinely new v3 lemma), `MemValSim`
    for the stored `ptrVal` under the extended ρt (its base is lockstep, so
    ρa grows by `.refl`), BRIDGE 2 for the `RStore` of the pointer, and
    BRIDGE 1 for the dst lowering when `dst` is projected. -/
theorem CompilerInv_step_ref
    {Γ : Ctx} {cs0 : CompilerState} {prog : obseq3.Prog Γ}
    {ρa : AddrRenameMap} {ρt : TagRenameMap}
    {s_mir s_mir' : mirlite.State MSB Γ}
    {s_osea : oseair.State MSB}
    {τ : LayoutTy}
    {dst : Place Γ (obseq.LayoutTy.PtrL τ)}
    {src : Place Γ τ}
    (kind : RefKind) (prot : Bool) (mask : List Bool)
    (compProg : oseair.Prog)
    (h_comp : compileProgFromChecked cs0 prog = Except.ok compProg)
    (h_inv  : CompilerInv cs0 prog ρa ρt s_mir s_osea)
    (h_stmt : prog.get? s_mir.pc = some (.assign dst (.ref kind prot mask src)))
    (h_step : mirlite.stepStmt MSB s_mir (.assign dst (.ref kind prot mask src)) = .ok s_mir') :
    ∃ (ρa' : AddrRenameMap) (ρt' : TagRenameMap) (s_osea' : oseair.State MSB) (n : Nat),
      AddrRenameIncr ρa ρa' ∧
      TagRenameIncr ρt ρt' ∧
      oseair.runN MSB n s_osea compProg = oseair.Result.Ok s_osea' ∧
      CompilerInv cs0 prog ρa' ρt' s_mir' s_osea' := by
  sorry

end obseq3.proof
