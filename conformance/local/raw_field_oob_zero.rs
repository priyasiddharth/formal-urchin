// Local witness: `&raw mut (*p).a` through a raw pointer at byte offset 0 is
// not pointer arithmetic, so Miri accepts it even when `p` is too small for the struct.
// The loader lowers it as a copy of `p` (rustc's `place_base_raw`: no retag).
// expected: ok (checked against the pinned Miri by scripts/live.py)
use std::alloc::{alloc, dealloc, Layout};
#[repr(C)] struct S { a: u32, b: u32, c: u32 }
fn main() {
    unsafe {
        let l = Layout::from_size_align_unchecked(4, 4);
        let p = alloc(l) as *mut S;
        let _q = &raw mut (*p).a;
        dealloc(p as *mut u8, l);
    }
}
