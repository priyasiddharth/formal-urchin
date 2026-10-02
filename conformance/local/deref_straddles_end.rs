// Local witness: a pointer READ that starts inside its allocation but runs
// past its end is out of bounds. The allocation is 12 bytes at alignment
// 8, so the pointer slot at offset 8 is aligned but only 4 of its 8 bytes
// are in bounds; `**q` must read that slot to find the pointer. The byte
// model once checked only the slot's first byte here (fixed 2026-10-02).
// expected: ub at `let _v = **q;` (checked against the pinned Miri by
// scripts/live.py)
use std::alloc::{alloc, dealloc, Layout};

fn main() {
    unsafe {
        let layout = Layout::from_size_align_unchecked(12, 8);
        let p = alloc(layout);
        let q = p.add(8) as *mut *mut u8;
        let _v = **q;
        dealloc(p, layout);
    }
}
