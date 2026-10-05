// Local witness: borrow stacks are per byte. A write through a raw pointer
// to element 0 pops the shared slice's tag there only, so reading element
// 2 through the slice at a run-time index is fine.
// expected: ok (checked against the pinned Miri by scripts/live.py)
fn main() {
    let mut v = [1u32, 2, 3];
    let p = &mut v as *mut [u32; 3];
    let s: &[u32] = unsafe { &*p };
    let i = *Box::new(2usize);
    unsafe { (*p)[0] = 9 };
    let _x = s[i];
}
