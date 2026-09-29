// Local witness: `<*mut T>::write` is a write ACCESS through its pointer:
// writing through a pointer whose tag a later `&mut` popped is UB, as a
// plain `*p = v` would be.
// expected: UB at the write (checked against the pinned Miri by
// scripts/live.py)

fn main() {
    let mut x = 5i32;
    let p = &mut x as *mut i32;
    let r = &mut x; // pops `p`'s item
    *r = 1;
    unsafe { p.write(2) };
    let _ = *r;
}
