// derived from miri tests/pass/both_borrows/interior_mutability.rs @ 34d6a7954
// scenario: unsafe_cell_deallocate — memory reached through an
// `&UnsafeCell<i32>` may be turned back into a Box and freed while that
// shared reference is live (its interior-mutable item carries no
// protector), and the Box drop really frees it (Box drop glue, 2026-10-01).
// expected: ok
// rewrites: scenario extracted (fn body -> main)
use std::cell::UnsafeCell;
use std::mem;

fn main() {
    fn f(x: &UnsafeCell<i32>) {
        let b: Box<i32> = unsafe { Box::from_raw(x as *const _ as *mut i32) };
        drop(b)
    }

    let b = Box::new(0i32);
    f(unsafe { mem::transmute(Box::into_raw(b)) });
}
