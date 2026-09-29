// derived from miri tests/fail/stacked_borrows/illegal_dealloc1.rs @ 34d6a7954
// expected: UB at dealloc through ptr2 (invalidated by the ptr1 write)
// rewrites: dropped error annotation (upstream `ptr1.write(0)` restored
//           2026-09-29 with the `ptr::write` shim)

use std::alloc::{Layout, alloc, dealloc};

fn main() {
    unsafe {
        let x = alloc(Layout::from_size_align_unchecked(1, 1));
        let ptr1 = (&mut *x) as *mut u8;
        let ptr2 = (&mut *ptr1) as *mut u8;
        ptr1.write(0);
        dealloc(ptr2, Layout::from_size_align_unchecked(1, 1));
    }
}
