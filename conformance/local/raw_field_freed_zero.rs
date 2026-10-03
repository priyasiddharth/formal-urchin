// Local witness: `&raw mut (*p).a` through a raw pointer at byte offset 0 is
// not pointer arithmetic, so Miri accepts it even when `p` is dangling (freed).
// The loader lowers it as a copy of `p` (rustc's `place_base_raw`: no retag).
// expected: ok (checked against the pinned Miri by scripts/live.py)
#[repr(C)] struct S { a: u32, b: u32, c: u32 }
fn main() {
    let p = Box::into_raw(Box::new(S { a: 1, b: 2, c: 3 }));
    unsafe { drop(Box::from_raw(p)); }
    let _q = unsafe { &raw mut (*p).a };
}
