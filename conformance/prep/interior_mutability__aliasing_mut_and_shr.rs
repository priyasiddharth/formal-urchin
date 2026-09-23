// derived from miri tests/pass/both_borrows/interior_mutability.rs @ 34d6a7954
// scenario: aliasing_mut_and_shr — raw escapes and shared reborrows of the
// RefCell must not unfreeze the aliasing &mut / & into its interior.
// expected: ok
// rewrites: scenario extracted (RefCell shims are flag-elided)
//           [2026-09-23] restored upstream form under a certificate

use std::cell::RefCell;

fn inner(rc: &RefCell<i32>, aliasing: &mut i32) {
    *aliasing += 4;
    let _escape_to_raw = rc as *const RefCell<i32>;
    *aliasing += 4;
    let _shr = &*rc;
    *aliasing += 4;
    let aliasing = &*aliasing;
    let _val = *aliasing;
    let _escape_to_raw = rc as *const RefCell<i32>;
    let _val = *aliasing;
    let _shr = &*rc;
    let _val = *aliasing;
}

fn main() {
    let rc = RefCell::new(23);
    let mut bmut = rc.borrow_mut();
    inner(&rc, &mut *bmut);
    drop(bmut);
    assert_eq!(*rc.borrow(), 23 + 12);
}
