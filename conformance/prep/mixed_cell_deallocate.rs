// derived from miri tests/fail/both_borrows/mixed_cell_deallocate.rs @ 34d6a7954
// expected: UB at the dealloc (the plain i32 half of `*x` is
// SharedReadOnly under the shared retag, which does not grant dealloc)
// rewrites: dropped revisions and error annotation; `Box::new` +
// `Box::into_raw` replaced by `alloc` + a store (both hand `foo` a raw
// pointer carrying the allocation's root permission);
// `Layout::new::<T>()` -> `Layout::for_value(x)` (same layout; dealloc's
// layout argument is not modelled)

use std::alloc;
use std::cell::Cell;

type T = (Cell<i32>, i32);

// Deallocating `x` is UB because not all bytes are in an `UnsafeCell`.
fn foo(x: &T) {
    let layout = alloc::Layout::for_value(x);
    unsafe { alloc::dealloc(x as *const _ as *mut T as *mut u8, layout) };
}

fn main() {
    unsafe {
        let b = alloc::alloc(alloc::Layout::for_value(&(Cell::new(0i32), 0i32))) as *mut T;
        *b = (Cell::new(0), 0);
        foo(std::mem::transmute(b));
    }
}
