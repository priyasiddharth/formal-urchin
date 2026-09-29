// derived from miri tests/fail/both_borrows/mixed_cell_deallocate.rs @ 34d6a7954
// expected: UB at the dealloc (the plain i32 half of `*x` is
// SharedReadOnly under the shared retag, which does not grant dealloc)
// rewrites: dropped revisions and error annotation;
// `Layout::new::<T>()` -> `Layout::for_value(x)` (same layout; dealloc's
// layout argument is not modelled). The upstream `Box::new` +
// `Box::into_raw` are restored (2026-09-29, `Box::into_raw` shim).


use std::alloc;
use std::cell::Cell;

type T = (Cell<i32>, i32);

// Deallocating `x` is UB because not all bytes are in an `UnsafeCell`.
fn foo(x: &T) {
    let layout = alloc::Layout::for_value(x);
    unsafe { alloc::dealloc(x as *const _ as *mut T as *mut u8, layout) };
}

fn main() {
    let b: Box<T> = Box::new((Cell::new(0), 0));
    foo(unsafe { std::mem::transmute(Box::into_raw(b)) });
}
