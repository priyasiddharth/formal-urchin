// derived from miri tests/pass/both_borrows/basic_aliasing_model.rs @ 34d6a7954
// scenario: partially_invalidate_mut — writing a disjoint field does not
// invalidate a field borrow (per-location stacks).
// expected: ok
// rewrites: scenario extracted; `p += 1` -> read then write (same
//           accesses, no arithmetic); assert dropped

fn main() {
    let data = &mut (0u8, 0u8);
    let reborrow = &mut *data as *mut (u8, u8);
    let shard = unsafe { &mut (*reborrow).0 };
    let _t = data.1;
    data.1 = 1;
    let _t2 = *shard;
    *shard = 1;
}
