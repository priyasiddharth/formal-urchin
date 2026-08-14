// derived from miri tests/fail/both_borrows/return_invalid_shr_tuple.rs @ 34d6a7954
// (stack revision)
// expected: UB at the return-seam retag of tuple field 0
// rewrites: dropped revisions and error annotations

fn foo(x: &mut (i32, i32)) -> (&i32,) {
    let xraw = x as *mut (i32, i32);
    let ret = (unsafe { &(*xraw).1 },);
    unsafe { *xraw = (42, 23) };
    ret
}

fn main() {
    foo(&mut (1, 2)).0;
}
