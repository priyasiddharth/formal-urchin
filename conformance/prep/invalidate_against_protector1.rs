// derived from miri tests/fail/stacked_borrows/invalidate_against_protector1.rs @ 34d6a7954
// expected (miri): UB at `*x` read — protector violation. Our model has no
// protectors: the read merely pops the protected &mut and the program
// completes. status: xfail-model (expected ub, observed ok).
// rewrites: dropped error annotation

fn inner(x: *mut i32, _y: &mut i32) {
    let _val = unsafe { *x };
}

fn main() {
    let mut x = 0;
    let xraw = &mut x as *mut i32;
    let xref = unsafe { &mut *xraw };
    inner(xraw, xref);
}
