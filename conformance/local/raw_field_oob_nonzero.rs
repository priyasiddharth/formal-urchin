// Local witness: `&raw mut (*p).c` through a raw pointer at byte offset 8
// is in-bounds pointer arithmetic: Miri reports UB when `p` is in a 4-byte allocation.
// expected: ub (checked against the pinned Miri by scripts/live.py)
use std::alloc::{alloc, dealloc, Layout};
#[repr(C)] struct S { a: u32, b: u32, c: u32 }
fn main() {
    unsafe {
        let l = Layout::from_size_align_unchecked(4, 4);
        let p = alloc(l) as *mut S;
        let _q = &raw mut (*p).c;
        dealloc(p as *mut u8, l);
    }
}
