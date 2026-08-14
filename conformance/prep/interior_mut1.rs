// derived from miri tests/fail/stacked_borrows/interior_mut1.rs @ 34d6a7954
// expected: UB at `*inner_shr.get()` (retag of popped SRW tag)
// rewrites: dropped error annotation

use std::cell::UnsafeCell;

fn main() {
    unsafe {
        let c = &UnsafeCell::new(UnsafeCell::new(0));
        let inner_uniq = &mut *c.get();
        let inner_shr = &*inner_uniq;
        *c.get() = UnsafeCell::new(1);
        let _val = *inner_shr.get();
    }
}
