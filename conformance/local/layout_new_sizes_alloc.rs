// Local witness: `Layout::new::<T>()` is `T`'s size (shim added
// 2026-09-29, from the call's monomorphised type argument). The model
// sizes `alloc` from the layout word, so allocating a pair and writing
// BOTH fields is in bounds only if the size is right.
// expected: ok (checked against the pinned Miri by scripts/live.py)
use std::alloc::{alloc, dealloc, Layout};

fn main() {
    unsafe {
        let layout = Layout::new::<(i32, i32)>();
        let p = alloc(layout) as *mut (i32, i32);
        (*p).0 = 1;
        (*p).1 = 2;
        let _v = (*p).1;
        dealloc(p as *mut u8, layout);
    }
}
