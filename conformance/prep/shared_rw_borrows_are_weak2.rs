// derived from miri tests/fail/stacked_borrows/shared_rw_borrows_are_weak2.rs @ 34d6a7954
// expected: UB at `*y` (the replace write through the later SRW popped it)
// rewrites: dropped normalize directive and error annotation

use std::cell::RefCell;
use std::mem;

fn main() {
    unsafe {
        let x = &mut RefCell::new(0);
        let y: &i32 = mem::transmute(&*x.borrow());
        let shr_rw = &*x;
        shr_rw.replace(1);
        let _val = *y;
    }
}
