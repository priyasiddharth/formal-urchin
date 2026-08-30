# Zero-sized locals share addresses with their successors — harmlessly

Load this before "fixing" the allocator, or when a proof seems to want
distinct locals to have distinct addresses.

[FACT, 2026-08-30] **The behavior.** `mirlite.allocate m sz` returns
`m.addrStart` and bumps the watermark by `sz`
(src/obseq3/mirlite_semantics.lean:86-88). With `sz = 0` the watermark
does NOT move, so a ZST local allocated at 100 is followed by the next
local — ZST or not — ALSO at 100. Both machines do this identically
(`AllocLockstep` keeps the watermarks equal), so the two-machine
refinement is undisturbed by construction: whatever coincidence the
source exhibits, the target exhibits at the same address.

[FACT, 2026-08-30] **Three independent reasons it is benign**, worth
keeping apart because they fail differently:

1. *Memory.* Addresses matter only through the cells they name, and a
   ZST names none: its block `[100, 100)` is empty, so it overlaps
   nothing. Every memory-side property is range-quantified over
   `k < blockSize τ` and is vacuously true for it.
2. *Provenance.* Locals are distinguished by TAG, not address.
   `sb_own` mints a fresh tag and THEN folds `ownCell` over the range
   (src/obseq3/sb.lean:378-382), so for `len = 0` the fold is a no-op:
   the ZST's tag is minted (the counter advances, which keeps
   `TagRenameBounded` honest) but appears in NO borrow stack. Nothing
   can be accessed through it, and an access through the other local's
   tag at 100 consults only that cell's own stack, which the ZST never
   touched.
3. *The invariant.* `LocalBindingSim` is stated per-local; there is NO
   clause anywhere asserting distinct locals have distinct addresses.
   Two locals at 100 both need `ρa 100 = some 100`, and since the
   extension is the identity they AGREE rather than conflict.

[FACT, 2026-08-30] **The one place it could have bitten, and doesn't:**
copy's overlap guard rejects `dst := copy src` when the ranges
intersect, and a ZST source and destination can sit at the same address.
But the guard is `rs.addr < d + blockSize τ ∧ d < rs.addr + blockSize τ`
— both conjuncts are FALSE at `blockSize τ = 0`. Empty ranges never
overlap, so the copy proceeds and copies zero words. Same for the write
bounds check.

[FACT, 2026-08-30] This matches the reference semantics: in Rust,
zero-sized allocations may share addresses. Compiler correctness does
not need ZSTs to have distinct addresses — it needs the two machines to
agree, and they do, cell for cell and tag for tag.

## See also

- empty-blocks-need-a-separate-base-fact.md — the proof-side hole that
  coincident/empty blocks open, and `extendBlock`
- stacked-borrows-does-not-subsume-bounds-checks.md
