// derived from miri tests/pass/both_borrows/interior_mutability.rs @ 34d6a7954
// scenario: rust_issue_68303 — a RefMut into an Option's payload stays
// usable across a shared read of the Option.
// expected: ok
// rewrites: scenario extracted (fn body -> main);
//           `optional.as_ref().unwrap()` -> `match &optional { Some(c) => c,
//           None => unreachable!() }` (the same shared reborrow of the
//           payload; Option::as_ref/unwrap are not shimmed);
//           `optional.is_some()` -> `matches!(optional, Some(_))`

use std::cell::RefCell;

fn main() {
    let optional = Some(RefCell::new(false));
    let mut handle = match &optional { Some(c) => c, None => unreachable!() }.borrow_mut();
    assert!(matches!(optional, Some(_)));
    *handle = true;
}
