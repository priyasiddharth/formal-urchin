# Pointer values carry an extent

[FACT, as of 2026-09-23] Both machines' pointer values have FIVE fields:
mirlite `ptrVal base offset extent size tag`, oseair
`Val.Ptr base offset extent size tag`. `base`/`size` are the allocation
the pointer has provenance over (bounds checks, `dealloc`,
`resolveAddr`); `offset` is where it points inside it; `extent` is how
many cells the pointer CLAIMS from there — the pointee's block size for a
thin pointer, `len · elemSize` for a slice. Who sets it: `alloc`/`Alloc*`
→ the block; `ref`/`Borrow (some n)` → `blockSize σ`/`n`; `ptrOffset` →
unchanged; `fromExposed`/`FromExposed` → `size − offset` (a thin pointer
from an integer claims the rest of its allocation); `refSlice`/`Borrow
none` → retags EXACTLY `extent` cells and keeps it. Before 2026-09-23 a
slice's length was reconstructed as `size − offset`, exact only for
whole-allocation slices (journal/2026-08/2026-08-14-slices-landed.md).
Source: src/obseq3/{mirlite_semantics,oseair}.lean.

[FACT, updated 2026-09-24] What consumes the extent: the slice mint and
`sliceLen`. `RExpr.sliceLen p` / `Rhs.SliceLen ty r` read the fat pointer
(copy's read of the cell that HOLDS it — not an access to the slice data)
and yield `extent / elemSize`, the length in elements. That is the whole
of Rust's slice metadata in this model, and it is what makes a runtime
bounds check a real check rather than a pinned branch. A zero-sized
element carries no length in the extent (`Nat` division gives 0); the
seam is where such a `.len()` should be refused. Accesses are
bounds-checked against the ALLOCATION (`allocBase + allocSize`), not the
extent, so a sub-slice pointer reaching past its extent but inside the
allocation is caught by Stacked Borrows (its tag is not on those cells'
stacks), not by a bounds check — the same verdict Miri reaches, for the
same reason.

[FACT] Proof (2026-09-23): `MemValSim`'s pointer clause adds `e' = e`;
`PtrRegisterEntry regMap reg base offset size tag` is `∃ extent, lookup
= …` — a place's register may hold a LOADED pointer whose extent is
whatever the program stored, and no destination/source lowering depends
on it (`PtrRegisterEntry.insert_self` builds one). The step lemmas thread
it; `runN_Assgn_Borrow_rest_step` takes the register's VALUE (extent
included) because the extent is what it retags. Every existing register
literal in the proof got its extent from the instruction that minted it:
a fresh root → its block; a projection `Borrow (some (blockSize τ))` →
`blockSize τ`. The whole migration was mechanical: no lemma changed its
meaning, the corpus verdicts did not move.

[FACT 2026-09-25] Sub-slices ARE produced: `RExpr.subSlice src lo hi`
(three copy reads, then `base`, `offset + lo·elem`, `(hi − lo)·elem`,
same size and tag) is the third consumer of the extent, and the seam
shims the std `Index`/`array` chain into the receiver's retag, the
narrowing, and the mint over the narrowed range. `zst_slice` passes on
it. What remains of the slice surface: `from_raw_parts_mut` (mint a fat
pointer from a thin one plus a length) and a RUNTIME `ptr::add` — the
two gaps `buggy_split_at_mut` still has, parked with a plan. See
[[what-compile-correct-actually-says]].
