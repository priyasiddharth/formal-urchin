// derived from miri tests/fail/both_borrows/deallocate_against_protector1.rs @ 34d6a7954
// expected: UB — `f` deallocates the allocation `x` points to while `x` is
// protected by `inner`'s fn-entry retag (Miri: "deallocating while item
// [Unique for …] is strongly protected", raised inside std's dealloc)
// rewrites: dropped //@ headers and error annotations;
//           the closure -> the named fn `free_it` (closures are not modelled);
//           `Box::leak(Box::new(0))` -> `alloc` + a store of 0;
//           `drop(Box::from_raw(raw))` -> `dealloc(raw, layout)` (Box drop
//           is not a dealloc in the model yet — parked.md § A′ item p)
use std::alloc::{alloc, dealloc, Layout};

fn inner(x: &mut i32, f: fn(&mut i32)) {
    // `f` may mutate, but it may not deallocate!
    f(x)
}

fn free_it(x: &mut i32) {
    let raw = x as *mut i32;
    unsafe { dealloc(raw as *mut u8, Layout::from_size_align_unchecked(4, 4)) };
}

fn main() {
    unsafe {
        let p = alloc(Layout::from_size_align_unchecked(4, 4)) as *mut i32;
        *p = 0;
        inner(&mut *p, free_it);
    }
}
