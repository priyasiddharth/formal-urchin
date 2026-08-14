// derived from miri tests/fail/both_borrows/illegal_write1.rs @ 34d6a7954
// (stack revision)
// expected: UB at `*x = 42` (raw from shared grants no write)
// rewrites: dropped revisions and error annotations
#![allow(invalid_reference_casting)]

fn main() {
    let target = Box::new(42);
    let xref = &*target;
    {
        let x: *mut u32 = xref as *const _ as *mut _;
        unsafe { *x = 42 };
    }
    let _x = *xref;
}
