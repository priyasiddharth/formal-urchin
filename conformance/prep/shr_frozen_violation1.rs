// derived from miri tests/fail/both_borrows/shr_frozen_violation1.rs @ 34d6a7954
// (stack revision)
// expected: UB at the write through the shared-derived raw
// rewrites: println!("{}", foo(..)) -> let _ = foo(..); dropped revisions
//           and error annotations
#![allow(invalid_reference_casting)]

fn foo(x: &mut i32) -> i32 {
    *x = 5;
    unknown_code(&*x);
    *x
}

fn main() {
    let _ = foo(&mut 0);
}

fn unknown_code(x: &i32) {
    unsafe {
        *(x as *const i32 as *mut i32) = 7;
    }
}
