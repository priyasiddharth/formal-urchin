# Summary of changes for run 6e61334a-ab82-4bce-a137-8f038905d5cd
Simplified the lemmas and proofs in the `obseq` directory, reducing total line count from 6,078 to 5,708 (370 lines removed). The project builds successfully with no errors and no `sorry`s. No new axioms were added.

**Key changes:**

1. **`proof/const_existing.lean` (296→166 lines, -130):** Refactored `ConstExisting.simulation` to use the shared `existing_write_simulation` theorem from `state_helpers.lean`, eliminating the duplicated manual off=0/off≠0 case split with all the verbose argument passing.

2. **`proof/struct_init_existing.lean` (335→191 lines, -144):** Same refactoring — `StructInitExisting.simulation` now delegates to `existing_write_simulation` instead of duplicating its logic.

3. **`proof/state_helpers.lean` (1730→1653 lines, -77):** 
   - Simplified `list_lookup_filter_ne` proof (replaced verbose manual BEq case analysis with cleaner `by_cases`/`simp` approach)
   - Replaced verbose explicit named-argument passing in `state_sim_write` and `existing_write_simulation` (e.g., `state_sim_write_subrange (π := π) (ρa := ρa) ... h_sim h_dst` → `state_sim_write_subrange h_sim h_dst ...`)
   - Fixed linter warnings (removed unused `Nat.add_zero` simp args)

4. **`proof/copy_existing.lean` (263→245 lines, -18):** Simplified verbose explicit named-argument passing in the `simulation` theorem and fixed all linter warnings about unused simp arguments (`blockSize`, `List.map`, `layoutToTyVal`, `mirlite.finishPlaceAssign`, `mirlite.writeResolvedPlace`, `h_dst`).

5. **`proof/const_fresh.lean` and `proof/struct_init_fresh.lean`:** Fixed multiple linter warnings about unused simp arguments (`typeSize`, `layoutToTyVal`, `List.map`, `mirlite.writeWordSeq`, `blockSize`, `wordStructTy`, `wordStructMirVals`, `mirlite.structConstWords?`).

**Existing axioms (unchanged, all at top of their files):**
- `sb.lean`: `sb_ref_mut_use_die_stack_eq`, `sb_ref_shared_read_die_stack_eq`, `sb_ref_mut_use_die_ok_of_use_ok`, `sb_ref_shared_read_die_ok_of_read_ok`, `freshTag_fresh`, `sb_read_sim_ok`, `sb_use_mb_sim_ok`, `sb_own_sim_extend`
- `proof/core.lean`: `alloc_fresh_reg`, `addr_rename_offset`
- `proof/state_helpers.lean`: `alloc_fresh_disjoint`, `alloc_fresh_tag`, `alloc_fresh_block`