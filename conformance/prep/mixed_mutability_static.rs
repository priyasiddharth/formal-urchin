// derived from miri tests/fail/both_borrows/mixed_mutability_static.rs @ 34d6a7954
// (stack revision)
// expected: UB at the write to the non-cell part of the static
// rewrites: ptr.cast_mut().write((1, AtomicI32::new(0))) ->
//           *(ptr as *mut (i32, AtomicI32) as *mut i32) = 1
//           (write lands on the frozen first field, same verdict/line;
//           avoids AtomicI32::new and ptr::write); dropped revisions
//           and error annotations

use std::sync::atomic::*;

static X: (i32, AtomicI32) = (0, AtomicI32::new(1));

fn main() {
    let ptr = &raw const X;
    unsafe { *(ptr as *mut (i32, AtomicI32) as *mut i32) = 1 };
}
