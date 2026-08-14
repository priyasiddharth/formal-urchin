// derived from miri tests/pass/both_borrows/basic_aliasing_model.rs @ 34d6a7954
// scenario: read_does_not_invalidate2 — reading from &mut does not
// invalidate a raw reborrow created earlier.
// expected: ok
// rewrites: scenario extracted; assert_eq!(*foo(..), 2) -> plain deref read; explicit binding for the temp

fn foo(x: &mut (i32, i32)) -> &i32 {
    let xraw = x as *mut (i32, i32);
    let _val = x.1;
    let ret = unsafe { &(*xraw).1 };
    ret
}

fn main() {
    let mut pair = (1, 2);
    let r = foo(&mut pair);
    let _v = *r;
}
