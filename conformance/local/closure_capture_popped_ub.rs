// Local witness: a closure captures `&mut b`; a write through a raw
// pointer to `b` made earlier pops the captured borrow, so calling the
// closure afterwards is UB at its use of the capture.
// expected: ub (checked against the pinned Miri by scripts/live.py)
fn main() {
    let mut b = 2u32;
    let p = &mut b as *mut u32;
    let pb = unsafe { &mut *p };
    let mut f = || *pb += 1;
    unsafe { *p = 5 };
    f();
}
