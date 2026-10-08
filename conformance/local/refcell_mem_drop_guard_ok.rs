// Local witness: a `RefMut` released early with `drop(guard)`; the shared
// borrow after it needs the flag back at 0 (checked at the borrow).
// expected: ok (checked against the pinned Miri by scripts/live.py)
use std::cell::RefCell;
fn main() {
    let rc = RefCell::new(1u32);
    let mut m = rc.borrow_mut();
    *m = 3;
    drop(m);
    let r = rc.borrow();
    if *r != 3 { panic!() }
}
