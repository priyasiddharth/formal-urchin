// derived from miri tests/fail/stacked_borrows/illegal_write3.rs @ 34d6a7954
// expected: UB at `*ptr = 42` (raw derived from shared ref grants no write)
// rewrites: dropped error annotation
#![allow(invalid_reference_casting)]

fn main() {
    let target = 42;
    let r = &target;
    let ptr = r as *const i32 as *mut i32;
    unsafe { *ptr = 42 };
    let _val = *r;
}
