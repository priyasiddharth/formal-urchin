// derived from miri tests/fail/stacked_borrows/pass_invalid_mut.rs @ 34d6a7954
// expected: UB at `foo(xref)` seam retag (raw read invalidated xref)
// rewrites: dropped error annotation

fn foo(_: &mut i32) {}

fn main() {
    let x = &mut 42;
    let xraw = x as *mut i32;
    let xref = unsafe { &mut *xraw };
    let _val = unsafe { *xraw };
    foo(xref);
}
