// derived from miri tests/pass/both_borrows/interior_mutability.rs @ 34d6a7954
// scenario: box_derefer — derefer-pass copies through a Box must not be
// retagged; the RefMut stays usable across a foreign shared reborrow.
// expected: ok
// rewrites: scenario extracted; `*mutref += 1` -> read then write;
//           `b.try_borrow().unwrap_err()` -> `let _probe = &**b;`
//           (the flag probe becomes a shared reborrow of the cell region;
//           Result/unwrap_err need enums+control flow)

use std::cell::RefCell;

fn main() {
    let mut cell = RefCell::new(0);
    let b = Box::new(&mut cell);
    let mut mutref = b.borrow_mut();
    let _t = *mutref;
    *mutref = 1;
    let _probe = &**b;
    let _t = *mutref;
    *mutref = 2;
}
