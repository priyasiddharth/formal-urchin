// derived from miri tests/fail/stacked_borrows/return_invalid_mut_option.rs @ 34d6a7954
// expected: UB at the return-seam retag of the ref inside Some
// rewrites: dropped error annotation
//           [2026-09-23] restored upstream form under a certificate

fn foo(x: &mut (i32, i32)) -> Option<&mut i32> {
    let xraw = x as *mut (i32, i32);
    let ret = unsafe { &mut (*xraw).1 };
    let ret = Some(ret);
    let _val = unsafe { *xraw };
    ret
}

fn main() {
    match foo(&mut (1, 2)) {
        Some(_x) => {}
        None => {}
    }
}
