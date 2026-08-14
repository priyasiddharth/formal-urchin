// derived from miri tests/pass/both_borrows/interior_mutability.rs @ 34d6a7954
// scenario: ref_protector — a Ref guard passed by value must NOT get a
// protector (guards are modeled as raw-layout values, unprotected at
// seams), so mutating after dropping it is fine.
// expected: ok
// rewrites: scenario extracted

use std::cell::{Ref, RefCell};

fn break_it(rc: &RefCell<i32>, r: Ref<'_, i32>) {
    drop(r);
    *rc.borrow_mut() = 2;
}

fn main() {
    let rc = RefCell::new(0);
    break_it(&rc, rc.borrow())
}
