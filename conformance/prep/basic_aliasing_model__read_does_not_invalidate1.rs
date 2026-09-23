// derived from miri tests/pass/both_borrows/basic_aliasing_model.rs @ 34d6a7954
// scenario: read_does_not_invalidate1 — reading from &mut does not
// invalidate raw-derived reborrows.
// expected: ok
// rewrites: scenario extracted
//           [2026-09-23] restored upstream form under a certificate

fn foo(x: &mut (i32, i32)) -> &i32 {
    let xraw = x as *mut (i32, i32);
    let ret = unsafe { &(*xraw).1 };
    let _val = x.1;
    ret
}

fn main() {
    assert_eq!(*foo(&mut (1, 2)), 2);
}
