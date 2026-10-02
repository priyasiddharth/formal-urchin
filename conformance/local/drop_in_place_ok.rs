// Local witness: `ptr::drop_in_place` (shim added 2026-10-01) retags `*p`
// Unique and protected for the drop, then runs the drop glue: on a place
// with no glue, a pointer derived from `&mut` keeps working afterwards and
// the owner can read again; on a `*mut Box<i32>` the inner Box is freed.
// expected: ok (checked against the pinned Miri by scripts/live.py)
use std::alloc::{dealloc, Layout};

fn main() {
    let mut pair = (1i32, 2u8);
    let p = &mut pair as *mut (i32, u8);
    unsafe {
        std::ptr::drop_in_place(p);
        (*p).0 = 3;
    }
    let _v = pair.0;
    unsafe {
        let b: *mut Box<i32> = Box::into_raw(Box::new(Box::new(5)));
        std::ptr::drop_in_place(b);
        dealloc(b as *mut u8, Layout::new::<Box<i32>>());
    }
}
