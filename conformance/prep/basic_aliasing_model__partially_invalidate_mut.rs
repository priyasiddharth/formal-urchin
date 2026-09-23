// derived from miri tests/pass/both_borrows/basic_aliasing_model.rs @ 34d6a7954
// scenario: partially_invalidate_mut — writing a disjoint field does not
// invalidate a field borrow (per-location stacks).
// expected: ok
// rewrites: scenario extracted; assert_eq!(*data, (1, 1)) dropped (the
//           tuple's PartialEq::eq is an opaque std body)
//           [2026-09-23] restored upstream form under a certificate

fn main() {
    let data = &mut (0u8, 0u8);
    let reborrow = &mut *data as *mut (u8, u8);
    let shard = unsafe { &mut (*reborrow).0 };
    data.1 += 1;
    *shard += 1;
}
