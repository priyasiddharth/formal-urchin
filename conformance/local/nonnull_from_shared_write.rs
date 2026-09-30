// Local witness: `NonNull::from(&T)` carries the shared reference's
// SharedReadOnly permission (std: `from_ref` = `r as *const T`), so writing
// through it is UB. Pins the shared branch of the `NonNull::from` shim
// (both From impls render as the same path).
// expected: UB at the write (checked against the pinned Miri by
// scripts/live.py)
use std::ptr::NonNull;

fn main() {
    let y = 5i32;
    let s = NonNull::from(&y);
    unsafe { *s.as_ptr() = 6 };
}
