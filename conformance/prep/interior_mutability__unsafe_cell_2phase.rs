// derived from miri tests/pass/both_borrows/interior_mutability.rs @ 34d6a7954
// scenario: unsafe_cell_2phase — a two-phase `&mut` of the Vec behind
// `UnsafeCell::get()` for `push` does not invalidate the alias `x2`, which
// then reads the pushed element.
// expected: ok
// rewrites: scenario extracted (fn body -> main)
#![allow(dangerous_implicit_autorefs)]

use std::cell::UnsafeCell;

fn main() {
    unsafe {
        let x = &UnsafeCell::new(vec![]);
        let x2 = &*x;
        (*x.get()).push(0);
        let _val = (*x2.get()).get(0);
    }
}
