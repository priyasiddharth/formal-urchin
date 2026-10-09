// Local witness: a `Ref`'s value pointer is std's `self.value.get()`, a raw
// pointer from a SharedReadWrite `&UnsafeCell<T>`, NOT a frozen `&T`. A
// write through a sibling raw pointer to the value (offset 8, after the
// isize flag) keeps it, so the deref after the write is fine. A model
// that froze the guard's pointer would report UB at line 11.
// expected: ok (checked against the pinned Miri by scripts/live.py)
use std::cell::RefCell;
fn main() {
    let rc = RefCell::new(1u32);
    let g = rc.borrow();
    let p = (&rc as *const RefCell<u32> as *mut u8).wrapping_add(8) as *mut u32;
    unsafe { *p = 2; }
    if *g != 2 { panic!() }
}
