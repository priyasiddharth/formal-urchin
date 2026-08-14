// derived from miri tests/fail/stacked_borrows/shared_rw_borrows_are_weak1.rs @ 34d6a7954
// expected: UB at `y.get_mut()` (the SRW write popped the Unique above it)
// rewrites: dropped error annotation

use std::cell::Cell;
use std::mem;

fn main() {
    unsafe {
        let x = &mut Cell::new(0);
        let y: &mut Cell<i32> = mem::transmute(&mut *x);
        let shr_rw = &*x;
        shr_rw.set(1);
        y.get_mut();
    }
}
