// derived from miri tests/fail/both_borrows/box_exclusive_violation1.rs @ 34d6a7954
// (stack revision)
// expected: UB at `*LEAK = 7` (write via our re-asserted box popped the leak)
// rewrites: dropped revisions and error annotations

fn demo_box_advanced_unique(mut our: Box<i32>) -> i32 {
    unknown_code_1(&*our);
    *our = 5;
    unknown_code_2();
    *our
}

use std::ptr;

static mut LEAK: *mut i32 = ptr::null_mut();

fn unknown_code_1(x: &i32) {
    unsafe {
        LEAK = x as *const _ as *mut _;
    }
}

fn unknown_code_2() {
    unsafe {
        *LEAK = 7;
    }
}

fn main() {
    demo_box_advanced_unique(Box::new(0));
}
