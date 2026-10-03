// Local witness: `&raw mut (*p).f` through a raw pointer at a nonzero byte
// offset is in-bounds pointer arithmetic: fine when the field lies in the
// allocation (`c` at 8 of 12), and when it ends exactly at the end (the
// zero-sized `z` at 4 of 4, one past the end). The loader lowers it as `p`
// cast to `*u8` and moved in bounds (rustc's `place_base_raw`: no retag).
// expected: ok (checked against the pinned Miri by scripts/live.py)
use std::alloc::{alloc, dealloc, Layout};
#[repr(C)] struct S { a: u32, b: u32, c: u32 }
#[repr(C)] struct T { a: u32, z: () }
fn main() {
    unsafe {
        let l = Layout::from_size_align_unchecked(12, 4);
        let p = alloc(l) as *mut S;
        let q = &raw mut (*p).c;
        *q = 5;
        let _v = *q;
        dealloc(p as *mut u8, l);
        let m = Layout::from_size_align_unchecked(4, 4);
        let t = alloc(m) as *mut T;
        let _z = &raw mut (*t).z;
        dealloc(t as *mut u8, m);
    }
}
