// derived from miri tests/fail/both_borrows/illegal_write5.rs @ 34d6a7954
// (stack revision)
// expected: UB at `*xref` (callee's raw write pops xref)
// rewrites: dropped revisions and error annotations

fn main() {
    let mut x = 15;
    let xraw = &mut x as *mut i32;
    let xref = unsafe { &mut *xraw };
    callee(xraw);
    let _val = *xref;
}

fn callee(xraw: *mut i32) {
    unsafe { *xraw = 15 };
}
