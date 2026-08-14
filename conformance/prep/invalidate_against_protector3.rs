// derived from miri tests/fail/both_borrows/invalidate_against_protector3.rs @ 34d6a7954
// (stack revision)
// expected: UB at `*x = 0` (the write would pop the protected shared arg)
// rewrites: dropped revisions and error annotations

use std::alloc::{Layout, alloc};

fn inner(x: *mut i32, _y: &i32) {
    unsafe { *x = 0 };
}

fn main() {
    unsafe {
        let ptr = alloc(Layout::for_value(&0i32)) as *mut i32;
        inner(ptr, &*ptr);
    };
}
