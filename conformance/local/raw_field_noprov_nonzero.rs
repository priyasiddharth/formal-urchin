// Local witness: `&raw mut (*p).c` through a raw pointer at byte offset 8
// is in-bounds pointer arithmetic: Miri reports UB when `p` is without provenance.
// expected: ub (checked against the pinned Miri by scripts/live.py)
#[repr(C)] struct S { a: u32, b: u32, c: u32 }
fn main() {
    let p = std::ptr::without_provenance_mut::<S>(64);
    let _q = unsafe { &raw mut (*p).c };
}
