// Local witness: indexing slice data at a run-time index reads through the
// slice's own tag (no retag); a write through a raw pointer to the same
// element popped that tag, so the read is UB.
// expected: ub (checked against the pinned Miri by scripts/live.py)
fn main() {
    let mut v = [1u32, 2, 3];
    let p = &mut v as *mut [u32; 3];
    let s: &[u32] = unsafe { &*p };
    let i = *Box::new(2usize);
    unsafe { (*p)[2] = 9 };
    let _x = s[i];
}
