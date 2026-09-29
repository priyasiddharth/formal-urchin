// Local witness: a raw pointer taken from a Box BEFORE `Box::leak` does
// not survive it: `leak` takes the Box by value, and the fn-entry Unique
// retag of the Box writes through the Box's tag, popping `q`'s item.
// expected: UB at the write through `q` (checked against the pinned Miri
// by scripts/live.py)

fn main() {
    let mut b = Box::new(5i32);
    let q = &mut *b as *mut i32;
    let r: &mut i32 = Box::leak(b);
    unsafe { *q = 1 };
    unsafe { drop(Box::from_raw(r as *mut i32)) };
}
