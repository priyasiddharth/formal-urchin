// derived from miri tests/fail/both_borrows/invalidate_against_protector2.rs @ 34d6a7954
// (stack revision)
// expected (miri): UB at `*x = 0` — protector violation. Our model has no
// protectors: the write pops the protected shared ref and the program
// completes. status: xfail-model (expected ub, observed ok).
// rewrites: dropped revisions and error annotations

fn inner(x: *mut i32, _y: &i32) {
    unsafe { *x = 0 };
}

fn main() {
    let mut x = 0;
    let xraw = &mut x as *mut i32;
    let xref = unsafe { &*xraw };
    inner(xraw, xref);
}
