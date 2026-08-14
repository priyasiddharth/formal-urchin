// derived from miri tests/fail/stacked_borrows/illegal_dealloc1.rs @ 34d6a7954
// expected: UB at dealloc through ptr2 (invalidated by the ptr1 write)
// rewrites: ptr1.write(0) -> unsafe { *ptr1 = 0 } (same access, avoids
//           the core::ptr::write intrinsic); dropped error annotation

use std::alloc::{Layout, alloc, dealloc};

fn main() {
    unsafe {
        let x = alloc(Layout::from_size_align_unchecked(1, 1));
        let ptr1 = (&mut *x) as *mut u8;
        let ptr2 = (&mut *ptr1) as *mut u8;
        *ptr1 = 0;
        dealloc(ptr2, Layout::from_size_align_unchecked(1, 1));
    }
}
