// Local witness: `ptr::write` and `<*mut T>::write` store through a raw
// pointer without reading or dropping the old value (shim added
// 2026-09-29), including into freshly allocated, uninitialised memory.
// expected: ok (checked against the pinned Miri by scripts/live.py)
use std::alloc::{alloc, dealloc, Layout};

fn main() {
    unsafe {
        let layout = Layout::from_size_align_unchecked(4, 4);
        let p = alloc(layout) as *mut i32;
        p.write(7);
        std::ptr::write(p, 8);
        let _v = *p;
        dealloc(p as *mut u8, layout);
    }
    let mut pair = (1i32, 2i32);
    let q = &mut pair as *mut (i32, i32);
    unsafe { q.write((3, 4)) };
    let _w = pair.1;
}
