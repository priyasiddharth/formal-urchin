// derived from miri tests/pass/both_borrows/interior_mutability.rs @ 34d6a7954
// scenario: unsafe_cell_invalidate — writing through a parent raw pops a
// protected &UnsafeCell argument, and that is allowed (weak protection
// on SharedReadWrite).
// expected: ok
// rewrites: scenario extracted; mem::transmute(raw2) ->
//           &*(raw2 as *const UnsafeCell<i32>) (an SRW reborrow instead
//           of a tag-preserving transmute; same pass verdict);
//           *y += 1 -> read then write

use std::cell::UnsafeCell;

fn f(_x: &UnsafeCell<i32>, y: *mut i32) {
    unsafe {
        let _t = *y;
        *y = 1;
    }
}

fn main() {
    let mut x = 0i32;
    let raw1 = &mut x as *mut i32;
    let ref1 = unsafe { &mut *raw1 };
    let raw2 = ref1 as *mut i32;
    f(unsafe { &*(raw2 as *const UnsafeCell<i32>) }, raw1);
}
