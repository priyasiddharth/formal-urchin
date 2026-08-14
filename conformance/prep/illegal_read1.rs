// derived from miri tests/fail/stacked_borrows/illegal_read1.rs @ 34d6a7954
// expected: UB at `*xref` (read via tag popped by callee's raw read)
// rewrites: dropped #[rustfmt::skip] and //~ ERROR annotation

fn main() {
    let mut x = 15;
    let xraw = &mut x as *mut i32;
    let xref = unsafe { &mut *xraw };
    callee(xraw);
    let _val = *xref;
}

fn callee(xraw: *mut i32) {
    let _val = unsafe { *xraw };
}
