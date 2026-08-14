// derived from miri tests/fail/both_borrows/aliasing_mut1.rs @ 34d6a7954
// (stack revision)
// expected: UB at the inlined fn-entry seam retag of safe's args (both
// args carry the same unique tag; the second protected retag pops the
// first). miri flags safe's signature line; we flag the call.
// rewrites: dropped revisions and error annotations

use std::mem;

fn safe(x: &mut i32, y: &mut i32) {
    *x = 1;
    *y = 2;
}

fn main() {
    let mut x = 0;
    let xraw: *mut i32 = unsafe { mem::transmute(&mut x) };
    let safe_raw: fn(x: *mut i32, y: *mut i32) =
        unsafe { mem::transmute::<fn(&mut i32, &mut i32), _>(safe) };
    safe_raw(xraw, xraw);
}
