// derived from miri tests/fail/both_borrows/deallocate_against_protector2.rs @ 34d6a7954
// expected: UB at the dealloc inside `f` (Miri, stacked borrows: the tag
// derived from the zero-sized `x` does not exist in the borrow stack for
// the i32's bytes)
// rewrites: dropped //@ headers and error annotations;
//           the closure -> the named fn `free_it` (closures are not modelled);
//           `raw.cast()` -> `raw as *mut u8`;
//           `Layout::new::<i32>()` -> `Layout::from_size_align_unchecked(4, 4)`
// (upstream `Box::leak(Box::new(0i32))` restored 2026-09-29)
use std::alloc::{dealloc, Layout};

fn inner(x: &mut (), f: fn(&mut ())) {
    // `f` may mutate, but it may not deallocate!
    f(x)
}

fn free_it(x: &mut ()) {
    unsafe {
        let raw = x as *mut _ as *mut i32;
        // Avoid ever creating a `Box`, we don't want any implicit accesses.
        dealloc(raw as *mut u8, Layout::from_size_align_unchecked(4, 4));
    }
}

fn main() {
    let ptr = Box::leak(Box::new(0i32)) as *mut i32;
    inner(unsafe { &mut *(ptr as *mut ()) }, free_it);
}
