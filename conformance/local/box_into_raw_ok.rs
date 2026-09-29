// Local witness: `Box::into_raw` hands back a raw pointer that may be
// written and read, then rebuilt with `Box::from_raw` (shim added
// 2026-09-29: the Box's fn-entry Unique retag, the `&mut **b` reborrow,
// then the raw retag that is the result).
// expected: ok (checked against the pinned Miri by scripts/live.py)

fn main() {
    let b = Box::new(5i32);
    let p = Box::into_raw(b);
    unsafe {
        *p = 6;
        let _v = *p;
        drop(Box::from_raw(p));
    }
}
