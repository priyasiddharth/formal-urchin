// derived from miri tests/pass/both_borrows/interior_mutability.rs @ 34d6a7954
// scenario: ref_mut_protector — same as ref_protector for RefMut.
// expected: ok
// rewrites: scenario extracted

use std::cell::{RefCell, RefMut};

fn break_it(rc: &RefCell<i32>, r: RefMut<'_, i32>) {
    drop(r);
    *rc.borrow_mut() = 2;
}

fn main() {
    let rc = RefCell::new(0);
    break_it(&rc, rc.borrow_mut())
}
