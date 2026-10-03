// Local witness: `p.add(k)` is in-bounds pointer arithmetic: an offset past
// the end of the allocation is UB in Miri, even without an access.
// expected: ub (checked against the pinned Miri by scripts/live.py)
use std::alloc::{alloc, dealloc, Layout};
fn main() {
    unsafe {
        let l = Layout::from_size_align_unchecked(4, 4);
        let p = alloc(l) as *mut u32;
        let _q = p.add(2);
        dealloc(p as *mut u8, l);
    }
}
