// Local witness: `&mut (*p)[i]` at a run-time index is a Unique retag of
// that element only; a write to the same element through `p` pops it.
// expected: ub (checked against the pinned Miri by scripts/live.py)
fn main() {
    let mut a = [1u32, 2, 3];
    let p = &mut a as *mut [u32; 3];
    let i = *Box::new(1usize);
    let r = unsafe { &mut (*p)[i] };
    unsafe { (*p)[1] = 5 };
    *r = 6;
}
