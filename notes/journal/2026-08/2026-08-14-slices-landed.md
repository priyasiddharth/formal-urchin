# Slices (runtime-length retags) landed — 53/75, zero divergences

[OBS 2026-08-14] Eighth increment: slice references. Suite:
pass 73 | fail 0 | xfail 0 | xpass 0 | unsupported 43 (116 entries);
fail tests 53/75 (45 line-accurate), 20 pass scenarios. New:
fnentry_invalidation2 at miri's exact line.

[FACT] Slice model: a `&[T]`/`&mut [T]`/`*const [T]` value is ONE cell
(the ordinary ptrVal) with the convention length = rest of allocation
(size − offset). Sound for whole-allocation slices — all the corpus
exercises without subslicing. Reborrows of slice DATA (`&mut *sli`,
receiver autorefs) become `RExpr.refSlice`: read the fat value, retag
`size − offset` cells via its tag at RUNTIME — the first retag whose
length is not statically known. Unsize coercions (`&mut [T; N] → &mut
[T]`, charon `Cast Unsize`) are plain value copies.

[FACT] Two behaviors this test pins down:
1. Miri does NOT fn-entry-retag fields of NAMED STRUCTS (the
   invalidation must happen at as_mut_ptr, not at inner(&mut t)) while
   it DOES retag tuple fields (pass_invalid_shr_tuple depends on it).
   UTy now separates `structT` (seam: plain copy) from `tup` (seam:
   field retags).
2. Shims that replace whole calls must reproduce the callee's FN-ENTRY
   retag: the as_mut_ptr shim first emits a mut refSlice of its
   receiver (the write access that pops the earlier as_ptr raw — miri
   issue 2536's exact reporting scenario), then the raw data retag.
   First shim draft omitted the entry retag and silently missed the UB
   (caught by the run, verdict ok on a fail test).

[OBS 2026-08-14] Honest boundary within the slice bucket: zst_slice
(range indexing via the std Index chain), buggy_split_at_mut (runtime
len() feeding asserts), buggy_as_mut_slice (Vec) remain unsupported —
they need dynamic bounds checks or containers, not more retag rules.
