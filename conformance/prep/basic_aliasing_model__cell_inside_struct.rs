// derived from miri tests/pass/both_borrows/basic_aliasing_model.rs @ 34d6a7954
// scenario: cell_inside_struct — writing the interior-mutable field via a
// shared-derived pointer and the reserved field via the &mut both work.
// expected: ok
// rewrites: scenario extracted; field2.set(10) -> (allow attr added)
//           *(&(*a).field2 as *const Cell<u32> as *mut u32) = 10
//           (the same cell-range write, avoids Cell::set's body)

#![allow(invalid_reference_casting)]
use std::cell::Cell;

struct Foo {
    field1: u32,
    field2: Cell<u32>,
}

fn main() {
    let mut root = Foo { field1: 42, field2: Cell::new(88) };
    let a = &mut root;
    unsafe { *(&(*a).field2 as *const Cell<u32> as *mut u32) = 10 };
    (*a).field1 = 88;
}
