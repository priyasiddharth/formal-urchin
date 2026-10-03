// Local witness: `p.wrapping_add(k)` is plain arithmetic: an offset past the
// end of the allocation is fine as long as nothing is accessed through it.
// expected: ok (checked against the pinned Miri by scripts/live.py)
use std::alloc::{alloc, dealloc, Layout};
fn main() {
    unsafe {
        let l = Layout::from_size_align_unchecked(4, 4);
        let p = alloc(l) as *mut u32;
        let _q = p.wrapping_add(2);
        dealloc(p as *mut u8, l);
    }
}
