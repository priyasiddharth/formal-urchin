// derived from miri tests/fail/stacked_borrows/return_invalid_mut_tuple.rs @ 34d6a7954
// expected: UB at the return-seam retag of tuple field 0
// rewrites: dropped error annotation

fn foo(x: &mut (i32, i32)) -> (&mut i32,) {
    let xraw = x as *mut (i32, i32);
    let ret = (unsafe { &mut (*xraw).1 },);
    let _val = unsafe { *xraw };
    ret
}

fn main() {
    foo(&mut (1, 2)).0;
}
