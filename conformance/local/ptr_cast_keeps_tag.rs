// Local witness: `<*T>::cast` / `cast_mut` / `cast_const` are raw-to-raw
// casts (`self as _`), which perform NO retag and so no access (shim added
// 2026-09-29). Casting a pointer whose tag has already been popped is
// therefore fine as long as the result is not used; a shim that retagged
// would report UB at the cast. The four casts are also exercised on a live
// pointer, which must stay usable.
// expected: ok (checked against the pinned Miri by scripts/live.py)

fn main() {
    let mut x = 5i32;
    let p = &mut x as *mut i32;
    let r = &mut x; // a fresh Unique retag of `x`: pops `p`'s item
    *r = 1;
    let _dead: *mut u32 = p.cast(); // no access, so no UB
    let _ = *r;

    let mut y = 7i32;
    let a = &mut y as *mut i32;
    let b: *mut u32 = a.cast();
    let c: *const u32 = b.cast_const();
    let d: *mut u32 = c.cast_mut();
    let e: *const i32 = d.cast::<i32>().cast_const().cast();
    unsafe {
        *d = 8;
        let _v = *e;
    }
}
