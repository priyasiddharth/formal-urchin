// derived from miri tests/pass/both_borrows/basic_aliasing_model.rs @ 34d6a7954
// scenario: box_into_raw_allows_interior_mutable_alias — a raw pointer from
// Box::into_raw and a shared reference to the Cell behind it alias freely.
// expected: ok
// rewrites: scenario extracted
use std::cell::Cell;

fn main() {
    unsafe {
        let b = Box::new(Cell::new(42));
        let raw = Box::into_raw(b);
        let c = &*raw;
        let d = raw.cast::<i32>(); // bypassing `Cell` -- only okay in Miri tests
        // `c` and `d` should permit arbitrary aliasing with each other now.
        *d = 1;
        c.set(2);
        drop(Box::from_raw(raw));
    }
}
