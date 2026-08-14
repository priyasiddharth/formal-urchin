# MIR-to-Lean ingestion landscape (for SB conformance testing)

Recorded 2026-08-14 during the SB-conformance audit. Question: does any
existing tool translate memory-level MIR into a Lean-consumable AST?

[FACT] No off-the-shelf MIR→Lean translator preserves the memory level.
- Aeneas (AeneasVerif) has a first-class Lean 4 backend but translates
  Charon's LLBC into *pure functional* code; explicitly cannot handle
  unsafe code / raw pointers / interior mutability — precisely the SB
  test fragment. (aeneasverif.github.io/projects)
- Creusot targets Why3 (Coma/WhyML), not Lean, and purifies borrows via
  prophecies; unsafe unsupported.
- Electrolysis (Ullrich 2016) was MIR→Lean 2, also purified, dead.
- RefinedRust/RustBelt/the POPL'20 SB formalization model memory but in
  Coq/Iris over their own calculi.
- stable-mir-json / KMIR (Runtime Verification) are faithful but emit
  JSON/K with no Lean consumer.

[FACT] Charon (github.com/AeneasVerif/charon) is the reusable frontend
half: a standalone rustc driver dumping MIR as ULLBC/LLBC JSON
(`charon rustc --ullbc --mir built --format json --monomorphize -- ...`).
ULLBC is a flat basic-block IR closest to raw MIR; `--mir built` is
pre-optimization MIR (optimizations can delete the borrows under test).

[FACT] Charon does NOT emit MIR Retag statements. Verified two ways:
its ULLBC `StatementKind` (charon/src/ast/ullbc_ast.rs) has no Retag
variant, and translate_bodies.rs has no match arm for
`mir::StatementKind::Retag` — Charon never passes `-Zmir-emit-retag`,
so the AddRetag pass never runs. Consequence: retag points must be
synthesized on the Lean side at `Rvalue::Ref`/`Rvalue::RawPtr` lowering
(which coincides with the eager permission model in obseq2/obseq3),
plus explicit seam retags where calls are inlined. Residual divergence
from Miri: Miri also retags on every typed copy of a reference value
(plain `let y = x;`, fn args/returns) — a test whose UB hinges on such
a retag would false-pass; audit inlined tests for this.

Related: [[v1-v2-sb-model-divergences-from-miri-sb]],
plans/sb_conformance_obseq3.md.
