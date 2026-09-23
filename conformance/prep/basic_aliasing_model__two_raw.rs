// derived from miri tests/pass/both_borrows/basic_aliasing_model.rs @ 34d6a7954
// scenario: two_raw — two raw pointers from the same &mut coexist
// (SharedReadWrite items are inserted adjacent to the parent, no access).
// expected: ok
// rewrites: scenario extracted
//           [2026-09-23] restored upstream form under a certificate

fn main() {
    unsafe {
        let x = &mut 0;
        let y1 = x as *mut i32;
        let y2 = x as *mut i32;
        *y1 += 2;
        *y2 += 1;
    }
}
