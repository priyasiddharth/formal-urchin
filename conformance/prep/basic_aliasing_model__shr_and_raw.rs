// derived from miri tests/pass/both_borrows/basic_aliasing_model.rs @ 34d6a7954
// scenario: shr_and_raw — creating a *mut does not invalidate an existing
// laundered shared reference.
// expected: ok
// rewrites: scenario extracted; `*y2 += 1` -> read then write

fn main() {
    unsafe {
        use std::mem;
        let x = &mut 0;
        let y1: &i32 = mem::transmute(&*x);
        let y2 = x as *mut i32;
        let _val = *y1;
        let _t = *y2;
        *y2 = 1;
    }
}
