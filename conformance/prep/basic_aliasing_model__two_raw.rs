// derived from miri tests/pass/both_borrows/basic_aliasing_model.rs @ 34d6a7954
// scenario: two_raw — two raw pointers from the same &mut coexist
// (SharedReadWrite items are inserted adjacent to the parent, no access).
// expected: ok
// rewrites: scenario extracted; `p += n` -> read then write

fn main() {
    unsafe {
        let x = &mut 0;
        let y1 = x as *mut i32;
        let y2 = x as *mut i32;
        let _t1 = *y1;
        *y1 = 2;
        let _t2 = *y2;
        *y2 = 1;
    }
}
