// Local witness: `&raw mut (*p).c` through a raw pointer at byte offset 8
// is in-bounds pointer arithmetic: Miri reports UB when `p` is dangling (freed).
// expected: ub (checked against the pinned Miri by scripts/live.py)
#[repr(C)] struct S { a: u32, b: u32, c: u32 }
fn main() {
    let p = Box::into_raw(Box::new(S { a: 1, b: 2, c: 3 }));
    unsafe { drop(Box::from_raw(p)); }
    let _q = unsafe { &raw mut (*p).c };
}
