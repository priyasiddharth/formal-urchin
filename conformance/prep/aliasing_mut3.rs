// derived from miri tests/fail/both_borrows/aliasing_mut3.rs @ 34d6a7954
// (stack revision)
// expected: UB at the inlined fn-entry seam retags (&mut then shared of
// the same location: the shared retag finds its tag popped)
// rewrites: dropped revisions and error annotations

use std::mem;

fn safe(x: &mut i32, y: &i32) {
    *x = 1;
    let _v = *y;
}

fn main() {
    let mut x = 0;
    let xref = &mut x;
    let xraw: *mut i32 = unsafe { mem::transmute_copy(&xref) };
    let xshr = &*xref;
    let safe_raw: fn(x: *mut i32, y: *const i32) =
        unsafe { mem::transmute::<fn(&mut i32, &i32), _>(safe) };
    safe_raw(xraw, xshr);
}
