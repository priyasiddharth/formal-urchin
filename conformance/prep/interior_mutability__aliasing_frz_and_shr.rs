// derived from miri tests/pass/both_borrows/interior_mutability.rs @ 34d6a7954
// scenario: aliasing_frz_and_shr — raw escapes and shared reborrows of the
// RefCell must not unfreeze the aliasing & into its interior.
// expected: ok
// rewrites: scenario extracted
//           [2026-09-23] restored upstream form under a certificate

use std::cell::RefCell;

fn inner(rc: &RefCell<i32>, aliasing: &i32) {
    let _val = *aliasing;
    let _escape_to_raw = rc as *const RefCell<i32>;
    let _val = *aliasing;
    let _shr = &*rc;
    let _val = *aliasing;
}

fn main() {
    let rc = RefCell::new(23);
    let bshr = rc.borrow();
    inner(&rc, &*bshr);
    assert_eq!(*rc.borrow(), 23);
}
