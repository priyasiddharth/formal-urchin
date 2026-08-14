// derived from miri tests/fail/stacked_borrows/illegal_read2.rs @ 34d6a7954
// expected: UB at `*xref` (callee's shared-from-raw read pops xref)
// rewrites: dropped rustfmt attr and error annotation

fn main() {
    let mut x = 15;
    let xraw = &mut x as *mut i32;
    let xref = unsafe { &mut *xraw };
    callee(xraw);
    let _val = *xref;
}

fn callee(xraw: *mut i32) {
    let shr = unsafe { &*xraw };
    let _val = *shr;
}
