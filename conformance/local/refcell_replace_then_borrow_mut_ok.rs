// Local witness: `RefCell::replace` borrows mutably for its own duration and
// gives the borrow back; `borrow_mut` afterwards needs the flag at 0.
// expected: ok (checked against the pinned Miri by scripts/live.py)
use std::cell::RefCell;
fn main() {
    let rc = RefCell::new(1u32);
    let old = rc.replace(4);
    *rc.borrow_mut() += old;
    if *rc.borrow() != 5 { panic!() }
}
