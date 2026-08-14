// derived from miri tests/fail/both_borrows/return_invalid_shr_option.rs @ 34d6a7954
// (stack revision)
// expected: UB at the return-seam retag of the ref inside Some
// rewrites: main's match on the result -> let _ = foo(..); dropped
//           revisions and error annotations

fn foo(x: &mut (i32, i32)) -> Option<&i32> {
    let xraw = x as *mut (i32, i32);
    let ret = Some(unsafe { &(*xraw).1 });
    unsafe { *xraw = (42, 23) };
    ret
}

fn main() {
    let _ = foo(&mut (1, 2));
}
