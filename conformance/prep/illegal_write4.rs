// derived from miri tests/fail/stacked_borrows/illegal_write4.rs @ 34d6a7954
// expected: UB at `*reference` (the transmute-to-&mut retag unfroze it)
// rewrites: dropped error annotation

use std::mem;

fn main() {
    let mut target = 42;
    let raw = &mut target as *mut i32;
    let reference = unsafe { &*raw };
    let _ptr = reference as *const i32 as *mut i32;
    let _mut_ref: &mut i32 = unsafe { mem::transmute(raw) };
    let _val = *reference;
}
