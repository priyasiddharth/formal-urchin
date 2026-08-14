// derived from miri tests/fail/stacked_borrows/transmute-is-no-escape.rs @ 34d6a7954
// expected: UB at `*raw = 13` (the transmuted tag exists only at cell 0
// via its own element borrow; the offset pointer's tag is not there)
// rewrites: dropped error annotation

use std::mem;

fn main() {
    let mut x: [i32; 2] = [42, 43];
    let _raw: *mut i32 = unsafe { mem::transmute(&mut x[0]) };
    let raw = (&mut x[1] as *mut i32).wrapping_offset(-1);
    unsafe { *raw = 13 };
}
