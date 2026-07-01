# v1 (obseq) is axiom-backed — check before citing a v1 lemma as "proved"

Load this before treating a v1 result as a fully-discharged template or
claiming "v1 proved X".

[FACT] v1 builds with no sorrys but rests on explicit axioms
(inventory per ARISTOTLE_SUMMARY.md, "all at top of their files"):
- `sb.lean`: `sb_ref_mut_use_die_stack_eq`,
  `sb_ref_shared_read_die_stack_eq`, `sb_ref_mut_use_die_ok_of_use_ok`,
  `sb_ref_shared_read_die_ok_of_read_ok`, `freshTag_fresh`,
  `sb_read_sim_ok`, `sb_use_mb_sim_ok`, `sb_own_sim_extend`
- `proof/core.lean`: `alloc_fresh_reg`, `addr_rename_offset`
- `proof/state_helpers.lean`: `alloc_fresh_disjoint`, `alloc_fresh_tag`,
  `alloc_fresh_block`

[FACT] paper.md §7 additionally claims `compiled_eq`,
`mirlite_step_inv`, and `osea_run_ok` are axiomatized for both RefOp
and DrefOp.

[OPEN] Those two inventories disagree — the bridge-lemma axioms of
paper.md §7 do not appear in Aristotle's list, and the 2026-06-17
session treated `existing_write_simulation`/`const_existing` as fully
proved. Likely paper.md §7 predates later proof work and is stale, but
this hasn't been verified against the current v1 tree. Grep
`^axiom` under src/obseq/ before relying on either claim.

[FACT] Known v1 design debt (paper.md §4, §7): `compile.lean` lowers
deref with a cleanup `Die` on the loaded pointer (5 instructions), but
`proof/deref.lean` models a 4-instruction fragment without it. This
compiler/proof mismatch is one reason v2's design makes cleanup and
temporary lifetime explicit (src/obseq/obseq2.md, "Additional areas").

## Why this matters

The reconstruct-not-port verdict already says don't reuse v1 code; this
note adds: don't even trust v1's *conclusions* as fully grounded without
checking which axioms they stand on. v2's rule is "no new axioms
without explicit review".

## See also

- dont-port-v1-proofs-reconstruct-in-v2.md
- where-design-knowledge-lives.md
