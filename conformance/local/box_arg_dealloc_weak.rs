// Local witness: a Box passed to a function gets a WEAK protector
// (Miri's `from_box_ty`), so the callee may deallocate it — here through
// `Box::into_raw` and `dealloc`, the memory Box drop will free once drop
// glue lands. A protected `&mut` would forbid this (strong protector,
// cf. deallocate_against_protector1). Before 2026-10-01 every protector
// in the model was strong, and this was a false UB.
// expected: ok (checked against the pinned Miri by scripts/live.py)
use std::alloc::{dealloc, Layout};

fn consume(b: Box<i32>) {
    let p = Box::into_raw(b);
    unsafe { dealloc(p as *mut u8, Layout::new::<i32>()) };
}

fn main() {
    consume(Box::new(5));
}
