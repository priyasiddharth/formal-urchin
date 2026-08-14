// derived from miri tests/fail/both_borrows/pass_invalid_shr_tuple.rs @ 34d6a7954
// (stack revision)
// expected: UB at `foo(pair_xref)` seam retag of tuple field 0
// rewrites: dropped revisions and error annotations

fn foo(_: (&i32, &i32)) {}

fn main() {
    let x = &mut (42i32, 31i32);
    let xraw0 = &mut x.0 as *mut i32;
    let xraw1 = &mut x.1 as *mut i32;
    let pair_xref = unsafe { (&*xraw0, &*xraw1) };
    unsafe { *xraw0 = 42 };
    foo(pair_xref);
}
