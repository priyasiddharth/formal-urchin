// Local witness: the references in a local array are read at a run-time
// index after a write through a raw pointer popped them: using the loaded
// reference is UB. The array is indexed by place projection (`addrOf`), so
// the only retag is the one Rust makes of the loaded reference.
// expected: ub (checked against the pinned Miri by scripts/live.py)
fn main() {
    let mut x = 1u32;
    let px = &mut x as *mut u32;
    let a = [unsafe { &*px }, unsafe { &*px }];
    let i = *Box::new(1usize);
    unsafe { *px = 2 };
    let r = a[i];
    let _v = *r;
}
