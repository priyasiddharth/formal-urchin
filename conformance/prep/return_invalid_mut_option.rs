// derived from miri tests/fail/stacked_borrows/return_invalid_mut_option.rs @ 34d6a7954
// expected: UB at the return-seam retag of the ref inside Some
// rewrites: main's match on the result -> let _ = foo(..) (UB fires at
//           the return; the match arms were empty); dropped error annotation

fn foo(x: &mut (i32, i32)) -> Option<&mut i32> {
    let xraw = x as *mut (i32, i32);
    let ret = unsafe { &mut (*xraw).1 };
    let ret = Some(ret);
    let _val = unsafe { *xraw };
    ret
}

fn main() {
    let _ = foo(&mut (1, 2));
}
