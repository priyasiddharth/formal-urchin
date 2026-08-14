// derived from miri tests/fail/stacked_borrows/illegal_read4.rs @ 34d6a7954
// expected: UB at `*xref2` (raw read invalidates derived &mut)
// rewrites: dropped error annotation

fn main() {
    let mut x = 2;
    let xref1 = &mut x;
    let xraw = xref1 as *mut i32;
    let xref2 = unsafe { &mut *xraw };
    let _val = unsafe { *xraw };
    let _illegal = *xref2;
}
