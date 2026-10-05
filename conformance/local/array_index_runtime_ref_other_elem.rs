// Local witness: `&mut (*p)[i]` at a run-time index retags element `i`
// only: a write to a different element through `p` leaves it valid
// (stacks are per byte).
// expected: ok (checked against the pinned Miri by scripts/live.py)
fn main() {
    let mut a = [1u32, 2, 3];
    let p = &mut a as *mut [u32; 3];
    let i = *Box::new(1usize);
    let r = unsafe { &mut (*p)[i] };
    unsafe { (*p)[2] = 5 };
    *r = 6;
}
