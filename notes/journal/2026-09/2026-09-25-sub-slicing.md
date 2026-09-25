# Sub-slicing, and the first slice test off the unsupported list

2026-09-25. "Do sub slicing." The second half of the slice roadmap step,
and — because the corpus came back the same day — the first corpus test
it actually unlocks.

## The rvalue: three reads, no retag

[FACT] `RExpr.subSlice p lo hi : RExpr Γ (PtrL σ)` reads the fat pointer
and both bounds (copy's read, three times, each in the state the last
left) and stores the pointer NARROWED: same allocation, same tag, offset
moved by `lo` elements, extent cut to `hi − lo`. It does NOT retag — the
`&mut s[lo..hi]` around it is a separate `refSlice` — and touches no
memory beyond the reads. An out-of-range range errs; in Rust that path
PANICS, and a panicking path is one the certificate refuses, so the
error is unreachable on any certified execution.

[FACT] The proof (`subSlice_valuePkg`, proof/slice.lean) is the `binOp`
package with one more read, and the third read is where the register
frame earns its keep twice over: the POINTER's register has to survive
two later reads and the LOW bound's one. Both are `h_frameH`/`h_frameL`
applications on registers below the watermark — the conjunct added on
2026-09-24. Nothing else was new: neither renaming grows (no tag is
minted, no address is created), so the tail is `sliceLen`'s with a
pointer in place of a word. Audit unchanged: 3 axioms, 0 sorries.

## The seam: shim the chain into the retags it performs

[FACT] `&a[0..0]` is a call to a bodyless std function —
`core::array::index` for arrays, `core::slice::index::index{,_mut}` for
slices — taking the receiver and a `Range { start, end }` aggregate. The
shim replaces the whole call with what the std body does to the borrow
stacks:

    tmp  := refSlice kind false recv     -- the receiver's own retag
    dest := copy tmp                     -- (ptrCast when recv is an ARRAY ref:
                                         --  gives the pointer the element type)
    dest := subSlice dest lo hi          -- pure arithmetic
    dest := refSlice kind false dest     -- the mint over the narrowed range

Constant bounds are materialised into fresh word locals by the same
`materialiseWord` the `binOp` arm uses, so one rvalue covers constant
and runtime ranges. A `RangeFull` has no fields, so the shim reads the
length with `sliceLen` and narrows `0 .. len` — the identity.

[FACT] The ARRAY case needs the reinterpret: `&a[0..0]`'s receiver is
`&[i32; 3]` (pointee `TupL`), while the destination is `&[i32]`
(pointee `NatL`), and `subSlice` scales its bounds by the DESTINATION's
element size. A plain copy between differing pointer types already
elaborates to `ptrCast`, which preserves base/offset/extent/size/tag —
so the fix was to route the value through the destination first.

## zst_slice passes

[EMP 2026-09-25] `fail/stacked_borrows/zst_slice` — unsupported since
the suite began — now matches Miri: both report UB at the `&*ptr` retag
after `s.as_ptr().add(1)`, because `&a[0..0]` granted a ZERO-length
range and element 1 is not in it. Miri: "trying to retag from <360> for
SharedReadOnly permission at alloc155[0x4], but that tag does not exist
in the borrow stack". Ours: "retag failed: sb-read: tag 33 does not
exist in the borrow stack at 1". Same cell (0x4 = element 1 of an i32
array), same mechanism.

[OBS] It is registered VERDICT-ONLY: our failing statement is the retag
inside the `assert_eq!` expansion, whose charon span points at the
macro's own line (44) rather than the call site (8) Miri names. Nine
other entries are verdict-only for related span reasons.

Suite: 99 pass / 0 fail / 39 unsupported (was 98/0/40), `--osea` 99
matched, certificates 25 entries / 44 checked (25 static, 19 runtime
across 7) / 0 unchecked. Units 18/18 and 129/129 (g17 plus d104–d107,
including the zst_slice shape as a Lean-level witness: narrow, retag,
then write one element past it).

[OPEN] `buggy_split_at_mut` and `buggy_as_mut_slice` need
`slice::from_raw_parts_mut` (a length-carrying pointer mint) and a
RUNTIME `ptr::add`; the latter also needs `Vec`. Those are the next two
gaps, and both are now buildable locally.
