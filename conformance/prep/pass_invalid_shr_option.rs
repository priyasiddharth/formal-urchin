// derived from miri tests/fail/both_borrows/pass_invalid_shr_option.rs @ 34d6a7954
// (stack revision)
// expected: UB at `foo(some_xref)` seam retag of the ref inside Some
// rewrites: dropped revisions and error annotations

fn foo(_: Option<&i32>) {}

fn main() {
    let x = &mut 42;
    let xraw = x as *mut i32;
    let some_xref = unsafe { Some(&*xraw) };
    unsafe { *xraw = 42 };
    foo(some_xref);
}
