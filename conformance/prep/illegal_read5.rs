// derived from miri tests/fail/stacked_borrows/illegal_read5.rs @ 34d6a7954
// expected: UB at the second `*xref` (ptr::read of the whole RefCell
// through `xshr` disables the Unique `xref` derived from borrow_mut)
// rewrites: dropped #[rustfmt::skip] and //~ ERROR annotation

use std::cell::RefCell;
use std::{mem, ptr};

fn main() {
    let rc = RefCell::new(0);
    let mut refmut = rc.borrow_mut();
    let xref: &mut i32 = &mut *refmut;
    let xshr = &rc; // creating this is ok
    let _val = *xref; // we can even still use our mutable reference
    mem::forget(unsafe { ptr::read(xshr) }); // but after reading through the shared ref
    let _val = *xref; // the mutable one is dead and gone
}
